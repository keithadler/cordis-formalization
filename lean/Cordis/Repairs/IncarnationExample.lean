import Cordis.Repairs.CommandBarrier
import Cordis.Repairs.HistoryProvenance
import Cordis.Repairs.ReplayTransport

/-! A reachable child is retired and removed while its parent retains the
birth inverse. A root is subsequently installed under the former child name.
The two retire commands in the extended history have the same payload and
different provenance. -/
namespace Cordis.Repairs.IncarnationExample
open Calculus Stages CommandBarrier LegalHistory Incarnation IncarnationReplay

def reissueCommand : OrchestrationSorting.Command Nat Unit Bool := .insert 1 providerComponent
def reissued : R := put middle 1 (fresh providerComponent none)
def retireAgain : OrchestrationSorting.Command Nat Unit Bool := .retire 1
def retiredRoot : R := Calculus.retire reissued 1

theorem reuse_enabled : Insertable middle 1 providerComponent none :=
  ⟨rfl, insertion_enabled_after.2⟩

def states : Nat → R
  | 0 => empty
  | 1 => inserted
  | 2 => begun
  | 3 => finished
  | 4 => before
  | 5 => middle
  | 6 => reissued
  | _ => retiredRoot

def rules : Nat → Labeled.Rule
  | 0 => .insert
  | 1 => .begin
  | 2 => .finish
  | 3 => .retire
  | 4 => .remove
  | 5 => .insert
  | _ => .retire

def actors : Nat → Nat
  | 0 | 1 | 2 => 0
  | _ => 1

def trace : Indexed.Trace program empty 7 where
  state := states
  rule := rules
  actor := actors
  start := rfl
  step time bounded := by
    have range : time = 0 ∨ time = 1 ∨ time = 2 ∨ time = 3 ∨ time = 4 ∨ time = 5 ∨ time = 6 := by omega
    rcases range with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact inserted_step
    · exact begin_step
    · exact finish_step
    · exact retire_step
    · exact .remove before 1 removal_enabled
    · exact .insert middle 1 providerComponent none reuse_enabled
    · exact .retire reissued 1 (by change some _ ≠ none; simp)

def insertParent : OrchestrationSorting.Command Nat Unit Bool := .insert 0 parentComponent
def events : List (Event Nat Unit Bool) :=
  [.command insertParent, .lifecycle .begin 0, .lifecycle .finish 0,
   .command retireAgain, .command removeChild, .command reissueCommand, .command retireAgain]

theorem recorded : RootExec program events empty retiredRoot [insertParent, reissueCommand, retireAgain] := by
  exact .cons (event := .command insertParent) ⟨⟨rfl, by simp, fun _ _ => trivial⟩, rfl⟩
    (.cons (event := .lifecycle .begin 0) begin_step
      (.cons (event := .lifecycle .finish 0) finish_step
        (.cons (event := .command retireAgain) ⟨by change some _ ≠ none; simp, rfl⟩
          (.cons (event := .command removeChild) ⟨removal_enabled, rfl⟩
            (.cons (event := .command reissueCommand) ⟨reuse_enabled, rfl⟩
              (.cons (event := .command retireAgain) ⟨by change some _ ≠ none; simp, rfl⟩
                (.nil retiredRoot)))))))

theorem child_and_root_births :
    birthAt trace.state 1 3 = some 3 ∧ birthAt trace.state 1 6 = some 6 := ⟨rfl, rfl⟩

theorem old_capture_still_saved :
    ((reissued 0).map (fun row => row.phase)) = some (.active [.retire 1] view) := rfl

theorem raw_inverse_retires_replacement :
    ((Stages.undo (.retire 1) reissued) 1).map Fiber.retired = some true := rfl

theorem captured_inverse_preserves_replacement :
    retireCaptured trace.state 1 3 6 = reissued :=
  retireCaptured_after_removal (gap := 5) (by decide) (by decide) rfl

/-- The annotation is obtained from the actual trace. The parent has one
token, and its provenance forces the birth at 3. The insertion at 6 was
performed by the orchestrator at 1 and never pushed a token at the parent. -/
theorem replay_saved_word :
    ∃ stacks, StackAt trace 6 stacks ∧
      stacks 0 = [⟨.retire 1, 3⟩] ∧ replayAt trace.state 6 (stacks 0) = reissued := by
  exact ⟨_, tracked_stack trace 6 (by decide), rfl, rfl⟩

/-- The same stale-token behavior holds in an actual renamed trace. Both
the old child and the reissued root move, while their birth indices differ. -/
theorem replay_renamed_saved_word (p : Renaming.Permutation Nat) :
    let moved := Renaming.trace p trace
    ∃ stacks, StackAt moved 6 stacks ∧
      stacks (p.toFun 0) = [⟨.retire (p.toFun 1), 3⟩] ∧
      replayAt moved.state 6 (stacks (p.toFun 0)) = Renaming.registry p reissued := by
  let moved := Renaming.trace p trace
  let stacks := track moved.state moved.actor 6
  refine ⟨stacks, tracked_stack moved 6 (by decide), ?_, ?_⟩
  · change track (fun index => Renaming.registry p (trace.state index))
      (fun index => p.toFun (trace.actor index)) 6 (p.toFun 0) = _
    rw [track_renamed]
    rfl
  · change replayAt (fun index => Renaming.registry p (trace.state index)) 6
      (track (fun index => Renaming.registry p (trace.state index))
        (fun index => p.toFun (trace.actor index)) 6 (p.toFun 0)) = _
    rw [replay_tracked_renamed]
    rfl

def retiredParent : R := Calculus.retire reissued 0
def leavingParent : R := mark retiredParent 0 (.unloading [.retire 1] view)
def unloadedParent : R := mark (discharge Stages.undo [.retire 1] leavingParent) 0 .inactive

private theorem retire_parent_step : Labeled.Step program .retire 0 reissued retiredParent :=
  .retire _ _ (by change some _ ≠ none; simp)

private theorem leave_parent_step : Labeled.Step program .leave 0 retiredParent leavingParent :=
  .leave retiredParent 0
    {(fresh parentComponent none : F) with retired := true, phase := .active [.retire 1] view}
    [.retire 1] view rfl rfl (retirement_has_no_target reissued 0 view)

private theorem unload_parent_step : Labeled.Step program .unload 0 leavingParent unloadedParent := by
  have free : ¬ Relied leavingParent 0 := by
    rintro ⟨consumer, different, relied⟩
    by_cases same : consumer = 1
    · subst consumer
      exact relied
    · simp [leavingParent, retiredParent, reissued, middle, before, finished, born,
        begun, inserted, empty, erase, mark, Calculus.retire, Calculus.modify, put,
        different, same] at relied
  exact .unload leavingParent 0
    {(fresh parentComponent none : F) with retired := true, phase := .unloading [.retire 1] view}
    [.retire 1] view rfl rfl free

/-- The stale write happens on a native L-Unload, with no request to retire
the new root. The prefix ends at state 6, before the separate command used
in the provenance example. -/
theorem stale_unload :
    WellFormed.Run program empty unloadedParent ∧
      (reissued 1).map Fiber.retired = some false ∧
      (unloadedParent 1).map Fiber.retired = some true :=
  ⟨.step (.step (.step (trace.prefixRun 6 (by decide)) retire_parent_step.toCalculus)
    leave_parent_step.toCalculus) unload_parent_step.toCalculus, rfl, rfl⟩

theorem remove_reissued_root : Removable unloadedParent 1 := by
  refine ⟨rfl, rfl, fun _ => rfl, ?_⟩
  intro name
  by_cases owner : name = 0
  · subst name
    change (none : Option Nat) ≠ some 1
    decide
  · by_cases replacement : name = 1
    · subst name
      change (none : Option Nat) ≠ some 1
      decide
    · simp [unloadedParent, leavingParent, retiredParent, reissued, middle, before, finished, born,
        begun, inserted, empty, erase, mark, discharge, Stages.undo, Calculus.retire, Calculus.modify, put,
        owner, replacement]

private def closingStates (time : Nat) : R :=
  if time ≤ 6 then states time else if time = 7 then retiredParent else if time = 8 then leavingParent
  else if time = 9 then unloadedParent else erase unloadedParent 1

private def closingRules (time : Nat) : Labeled.Rule :=
  if time < 6 then rules time else if time = 6 then .retire else if time = 7 then .leave
  else if time = 8 then .unload else .remove

private def closingActors (time : Nat) : Nat :=
  if time < 6 then actors time else if time < 9 then 0 else 1

def staleClosingTrace : Indexed.Trace program empty 10 where
  state := closingStates
  rule := closingRules
  actor := closingActors
  start := rfl
  step time bounded := by
    by_cases earlier : time < 6
    · simpa [closingStates, closingRules, closingActors, earlier, show time ≤ 6 by omega, show time + 1 ≤ 6 by omega]
        using trace.step time (by omega)
    · have remaining : time = 6 ∨ time = 7 ∨ time = 8 ∨ time = 9 := by omega
      rcases remaining with rfl | rfl | rfl | rfl
      · exact retire_parent_step
      · exact leave_parent_step
      · exact unload_parent_step
      · exact .remove _ _ remove_reissued_root

/-- The same textual command occurs twice with different classifications, so
a single Boolean function of its target name cannot record this history. -/
theorem no_static_classification :
    ¬ ∃ roots : Nat → Bool, rootCommands roots events = [insertParent, reissueCommand, retireAgain] := by
  rintro ⟨roots, recorded⟩
  cases parent : roots 0 <;> cases reused : roots 1 <;>
    simp_all [rootCommands, Event.rootCommand, events, insertParent, reissueCommand, retireAgain,
      removeChild, OrchestrationSorting.Command.actor]

end Cordis.Repairs.IncarnationExample
