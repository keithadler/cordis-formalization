import Cordis.Repairs.VestigialSuffix
import Cordis.DeletionAdmissionBoundary

/-!
The corrected episode deletion selection. The opening Begin is at b-1.
Only lifecycle events of the selected actor are removed by the interval
test. A withdrawn child is identified by the birth of its live incarnation.
The suffix replay theorem supplies legal replay once the withdrawn children
are vestigial at the closure boundary.
-/
namespace Cordis.Repairs.EpisodeSelection
open Calculus Stages LegalHistory Incarnation
universe u
variable {Name Key Value Code Error : Type u} [DecidableEq Name] [DecidableEq Key]
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "Program" => Code → Instruction Name Key Value Code Error
variable {program : Code → Instruction Name Key Value Code Error}
variable {initial : Registry Name Key Value Code (Inverse Name Key Value) Error} {last : Nat}

def lifecycle : Labeled.Rule → Bool
  | .insert | .retire | .remove => false
  | _ => true

def canBirth : Labeled.Rule → Bool
  | .iter | .finish | .divert => true
  | _ => false

def withdrawn (trace : Indexed.Trace program initial last) (parent : Name) (b u time : Nat) : Bool :=
  let name := trace.actor time
  match birthAt trace.state name time with
  | none => false
  | some birth =>
    decide (0 < birth ∧ b ≤ birth - 1 ∧ birth - 1 ≤ u ∧ trace.actor (birth - 1) = parent) &&
      canBirth (trace.rule (birth - 1)) &&
      (trace.state birth name).any (fun row => row.parent == some parent)

def keeps (trace : Indexed.Trace program initial last) (actor : Name) (b u time : Nat) : Bool :=
  !withdrawn trace actor b u time &&
    !(lifecycle (trace.rule time) && decide (b - 1 ≤ time ∧ time ≤ u ∧ trace.actor time = actor))

def retained (trace : Indexed.Trace program initial last) (actor : Name) (b u : Nat) : List Nat :=
  (List.range last).filter (keeps trace actor b u)

theorem mem_retained (trace : Indexed.Trace program initial last) (actor : Name) (b u time : Nat) :
    time ∈ retained trace actor b u ↔ time < last ∧ keeps trace actor b u time = true := by
  simp [retained]

/-- A selected child command identifies a birth during this episode and
the corresponding continuous lifetime. The earlier boundary is vacant. -/
theorem withdrawn_birth (trace : Indexed.Trace program initial last) (parent : Name) (b u time : Nat)
    (selected : withdrawn trace parent b u time = true) :
    ∃ birth, 0 < birth ∧ b ≤ birth - 1 ∧ birth - 1 ≤ u ∧ trace.actor (birth - 1) = parent ∧
      canBirth (trace.rule (birth - 1)) = true ∧
      trace.state (birth - 1) (trace.actor time) = none ∧
      Residency trace.state (trace.actor time) birth time ∧
      ∃ row, trace.state birth (trace.actor time) = some row ∧ row.parent = some parent := by
  cases tagged : birthAt trace.state (trace.actor time) time with
  | none => simp [withdrawn, tagged] at selected
  | some birth =>
    simp only [withdrawn, tagged, Bool.and_eq_true, decide_eq_true_eq] at selected
    obtain ⟨⟨⟨positive, lower, upper, owner⟩, instantiation⟩, child⟩ := selected
    have resident := resident_of_birthAt tagged
    refine ⟨birth, positive, lower, upper, owner, instantiation,
      resident.boundary.resolve_left (by omega), resident, ?_⟩
    cases rowAt : trace.state birth (trace.actor time) with
    | none => simp [rowAt] at child
    | some row => exact ⟨row, rfl, by simpa [rowAt] using child⟩

private theorem birth_after_landing {before middle : R} {actor child : Name} {code : Code}
    {token : Inverse Name Key Value} {next : Option Code}
    (landed : Land program actor code before middle token next)
    (phase : Phase Name Key Code (Inverse Name Key Value))
    {fiber : Fiber Name Key Value Code (Inverse Name Key Value) Error}
    (actorPresent : before actor = some fiber)
    (stack : phase.accumulator = token :: fiber.phase.accumulator) (vacant : before child = none)
    (existsAfter : mark middle actor phase child ≠ none) :
    Transposition.CreatesChild program actor before (mark middle actor phase) child ∧
      ∀ name, PartialReplayRegistry.saved (mark middle actor phase) name =
        if name = actor then .retire child :: PartialReplayRegistry.saved before name
        else PartialReplayRegistry.saved before name := by
  have distinct : child ≠ actor := fun same => by
    have absent : before actor = none := same ▸ vacant
    simp [actorPresent] at absent
  have landedPresent : middle child ≠ none := by
    simpa [mark, Calculus.modify, distinct] using existsAfter
  obtain ⟨actual, component, action, ready, same⟩ :=
    Transposition.land_new_name_with_token program landed child vacant landedPresent
  refine ⟨⟨code, component, phase, action, ready, congrArg (fun state => mark state actor phase) same⟩, ?_⟩
  simpa only [actual] using PartialReplayRegistry.saved_after_landing program landed fiber actorPresent phase stack

/-- A new child from an actual lifecycle landing pushes its own raw
retirement token on the creator's saved stack. -/
theorem actual_child_birth {before after : R} {actor child : Name} {rule : Labeled.Rule}
    (step : Labeled.Step program rule actor before after) (birthRule : canBirth rule = true)
    (vacant : before child = none) (existsAfter : after child ≠ none) :
    Transposition.CreatesChild program actor before after child ∧
      ∀ name, PartialReplayRegistry.saved after name =
        if name = actor then .retire child :: PartialReplayRegistry.saved before name
        else PartialReplayRegistry.saved before name := by
  cases step with
  | iter _ _ _ _ _ _ _ _ _ found reloading _ landed =>
    exact birth_after_landing landed _ found (by simp [reloading, Phase.accumulator]) vacant existsAfter
  | finish _ _ _ _ _ _ _ _ found reloading _ landed =>
    exact birth_after_landing landed _ found (by simp [reloading, Phase.accumulator]) vacant existsAfter
  | divert _ _ _ _ _ _ _ _ found reloading _ branch =>
    rcases branch with ⟨rfl, _⟩ | ⟨inverse, next, landed, _⟩
    · simp [mark, Calculus.modify, vacant] at existsAfter
    · subst_vars
      exact birth_after_landing landed _ found (by simp [reloading, Phase.accumulator]) vacant existsAfter
  | _ => simp [canBirth] at birthRule

/-- The filter's birth test implies a native instantiation landing at the
selected earlier step, including when Divert accounts for that landing. -/
theorem withdrawn_created (trace : Indexed.Trace program initial last) (parent : Name) (b u time : Nat)
    (bounded : time ≤ last) (selected : withdrawn trace parent b u time = true) :
    ∃ birth, 0 < birth ∧ b ≤ birth - 1 ∧ birth - 1 ≤ u ∧
      Residency trace.state (trace.actor time) birth time ∧
      Transposition.CreatesChild program parent (trace.state (birth - 1))
        (trace.state birth) (trace.actor time) := by
  obtain ⟨birth, positive, lower, upper, owner, rule, vacant, resident, row, found, _⟩ :=
    withdrawn_birth trace parent b u time selected
  have order := resident.ordered
  have next : birth - 1 + 1 = birth := by omega
  have stepped := trace.step (birth - 1) (by omega)
  rw [owner, next] at stepped
  exact ⟨birth, positive, lower, upper, resident,
    (actual_child_birth stepped rule vacant (by simp [found])).1⟩

/-- A later incarnation cannot be withdrawn by an earlier episode even if
it uses the same name and has the same parent and component. -/
theorem keeps_later_birth (trace : Indexed.Trace program initial last) (parent : Name) (b u time birth : Nat)
    (tagged : birthAt trace.state (trace.actor time) time = some birth)
    (later : u < birth - 1) : keeps trace parent b u time = true := by
  have present := resident_of_birthAt tagged
  have bounded := present.ordered
  have outside : ¬time ≤ u := by omega
  have notBorn : ¬birth - 1 ≤ u := by omega
  simp [keeps, withdrawn, tagged, outside, notBorn]

/-- No retirement or removal of an external root is selected for deletion.
A committed lifetime preserves its parent field from its birth. -/
theorem keeps_root (trace : Indexed.Trace program initial last) (owner : Name) (b u time : Nat)
    (bounded : time ≤ last) (root : rootAt (trace.state time) (trace.actor time) = true)
    (external : lifecycle (trace.rule time) = false) :
    keeps trace owner b u time = true := by
  have noWithdrawal : withdrawn trace owner b u time = false := by
    cases tagged : birthAt trace.state (trace.actor time) time with
    | none => simp [withdrawn, tagged]
    | some birth =>
      cases current : trace.state time (trace.actor time) with
      | none => simp [rootAt, current] at root
      | some row =>
        have rootParent : row.parent = none := by simpa [rootAt, current, Option.isNone_iff_eq_none] using root
        have interval := resident_of_birthAt tagged
        cases original : trace.state birth (trace.actor time) with
        | none => exact False.elim (interval.present birth (Nat.le_refl _) interval.ordered original)
        | some first =>
          have sameParent := (interval.metadata trace bounded original current).2
          simp [withdrawn, tagged, original, sameParent, rootParent]
  simp [keeps, noWithdrawal, external]

theorem keeps_insert (trace : Indexed.Trace program initial last) (owner : Name) (b u time : Nat)
    (bounded : time < last) (rule : trace.rule time = .insert) :
    keeps trace owner b u time = true := by
  have step := trace.step time bounded
  rw [rule] at step
  generalize trace.state (time + 1) = after at step
  have absent : trace.state time (trace.actor time) = none := by
    cases step with
    | insert _ _ _ _ ready => exact ready.1
  simp [keeps, withdrawn, birthAt_none.mpr absent, rule, lifecycle]

/-- The selected parent's lifecycle events are removed from the opening
Begin through Unload, including Begin at the left boundary. -/
theorem drops_episode_lifecycle (trace : Indexed.Trace program initial last)
    (actor : Name) (b u time : Nat) (lower : b - 1 ≤ time) (upper : time ≤ u)
    (subject : trace.actor time = actor) (active : lifecycle (trace.rule time) = true) :
    keeps trace actor b u time = false := by
  simp [keeps, active, lower, upper, subject]

end Cordis.Repairs.EpisodeSelection

namespace Cordis.Repairs.EpisodeSelection
open Calculus Stages RenamingLiteral LegalHistory
open ResolutionClosureBoundary (component program)
open DeletionAdmissionBoundary (trace s0 s1 s6)

def insertCommand : OrchestrationSorting.Command Name Empty Code := .insert 0 component
def retireCommand : OrchestrationSorting.Command Name Empty Code := .retire 0

/-- The audited six-step example retains the original Insert and Retire,
which reach the exact original endpoint with the episode omitted. -/
theorem corrected_unit_episode :
    retained trace 0 2 5 = [0, 3] ∧
    RootExec program [.command insertCommand, .command retireCommand] s0 s6
      [insertCommand, retireCommand] := by
  have endpoint : s6 = retireCommand.apply s1 := by
    funext name
    by_cases same : name = 0
    · subst name
      rfl
    · simp [DeletionAdmissionBoundary.s6, DeletionAdmissionBoundary.s5, DeletionAdmissionBoundary.s4,
        DeletionAdmissionBoundary.s3, DeletionAdmissionBoundary.s2, s1, retireCommand,
        OrchestrationSorting.Command.apply, discharge, Stages.undo, mark, Calculus.retire,
        Calculus.modify, put, same]
  exact ⟨rfl, .cons (event := .command insertCommand)
    ⟨⟨rfl, by simp, fun _ key => nomatch key⟩, rfl⟩
    (.cons (event := .command retireCommand)
      ⟨by change some _ ≠ none; simp, endpoint⟩ (.nil _))⟩

end Cordis.Repairs.EpisodeSelection
