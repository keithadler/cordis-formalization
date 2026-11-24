import Cordis.Repairs.LegalHistory
import Cordis.Repairs.ExchangeReplay
import Cordis.Results.CanonicalOrderCounterexample

/-! The audited seven-step counterexample, repaired by the proved command
and activation diamonds. This constructs the reordered history from the old
one, retains both component payloads, and reaches the identical endpoint. -/
namespace Cordis.Repairs.CausalOrderExample
open Calculus Stages OrchestrationSorting CausalCommands LegalHistory
open CanonicalOrderCounterexample

abbrev Ev := Event Nat Empty Bool
def insertP : Command Nat Empty Bool := .insert P parentComponent
def insertQ : Command Nat Empty Bool := .insert Q unitComponent
def retireC : Command Nat Empty Bool := .retire C
def roots (name : Nat) : Bool := name == P || name == Q

def original : List Ev :=
  [.command insertP, .lifecycle .begin P, .lifecycle .finish P,
    .command retireC, .command insertQ, .lifecycle .begin Q, .lifecycle .finish Q]

def repaired : List Ev :=
  [.command insertP, .command insertQ, .lifecycle .begin P,
    .lifecycle .finish P, .command retireC, .lifecycle .begin Q, .lifecycle .finish Q]

private theorem first_insert : insertP.Step s0 s1 :=
  ⟨⟨rfl, by simp, fun _ key => nomatch key⟩, rfl⟩

private theorem retire_child : retireC.Step s3 s4 :=
  ⟨by change some _ ≠ none; simp, rfl⟩

private theorem last_insert : insertQ.Step s4 s5 :=
  ⟨⟨rfl, by simp, fun _ key => nomatch key⟩, rfl⟩

theorem original_legal : Exec program original s0 s7 :=
  .cons first_insert (.cons (trace.step 1 (by decide)) (.cons (trace.step 2 (by decide))
    (.cons retire_child (.cons last_insert (.cons (trace.step 5 (by decide))
      (.cons (trace.step 6 (by decide)) (.nil s7)))))))

/-- Move Q's insertion across the child retirement and then across the two
parent activation steps. Every earlier applicability fact is proved. -/
theorem repaired_by_exchanges : Exec program repaired s0 s7 := by
  have earlier : insertQ.Enabled s3 := ⟨rfl, by simp, fun _ key => nomatch key⟩
  obtain ⟨swapped, first, second⟩ := command_diamond retireC insertQ retire_child last_insert
    (by decide) earlier
  obtain ⟨_, rfl⟩ := first
  obtain ⟨beforeFinish, finishLater⟩ := activation_command_diamond program insertQ
    (trace.step 2 (by decide)) (.inr (.inr rfl)) earlier (by decide) (fun _ => rfl)
  obtain ⟨beforeBegin, beginLater⟩ := activation_command_diamond program insertQ
    (trace.step 1 (by decide)) (.inl rfl) beforeFinish (by decide) (fun _ => rfl)
  exact .cons first_insert (.cons ⟨beforeBegin, rfl⟩ (.cons beginLater (.cons finishLater
    (.cons second (.cons (trace.step 5 (by decide)) (.cons (trace.step 6 (by decide)) (.nil s7)))))))

theorem root_payloads_in_order :
    rootCommands roots original = [insertP, insertQ] ∧
      rootCommands roots repaired = [insertP, insertQ] := ⟨rfl, rfl⟩

/-- The repaired event history is a run of the original calculus, not a
relaxed scheduler or a replacement transition relation. -/
theorem repaired_native : WellFormed.Run program s0 s7 := repaired_by_exchanges.toRun

open Incarnation (birthAt)
open IncarnationReplay (Capture replayAt track)

/-- Move the unrelated root insertion past the child's Retire and its
parent's Finish. The retained retirement token follows the actual child
birth from index 3 to 4, while the root birth moves from index 5 to 3. -/
theorem exchanges_reindex_birth_and_capture :
    ∃ moved : Indexed.Trace program s0 7,
      moved.state 7 = trace.state 7 ∧
      birthAt moved.state C 5 = some 4 ∧ birthAt moved.state Q 5 = some 3 ∧
      track moved.state moved.actor 5 P = [⟨.retire C, 4⟩] ∧
      replayAt moved.state 5 (track moved.state moved.actor 5 P) =
        replayAt trace.state 5 (track trace.state trace.actor 5 P) := by
  have ready : insertQ.Enabled s3 := ⟨rfl, by simp, fun _ key => nomatch key⟩
  obtain ⟨middle, commands⟩ := ExchangeReplay.commands (point := 3) trace (by decide)
    retireC insertQ rfl rfl ⟨rfl, rfl⟩ retire_child last_insert (by decide) ready
  have earlier : insertQ.Step (middle.state 3) (middle.state 4) := by
    rw [commands.state 3 (by decide), commands.middle]
    exact ⟨ready, rfl⟩
  obtain ⟨finishRule, parentActor⟩ := commands.label 2 (by decide) (by decide)
  have activation : Transposition.Activation (middle.rule 2) := by
    rw [finishRule]
    exact .inr (.inr rfl)
  have unrelated : middle.actor 2 ≠ insertQ.actor := by
    rw [parentActor]
    decide
  have absentAfter : middle.state 3 insertQ.actor = none := by
    rw [commands.state 3 (by decide)]
    rfl
  obtain ⟨moved, exchange⟩ := ExchangeReplay.activation_command (point := 2) middle (by decide)
    insertQ activation commands.first earlier unrelated (fun _ => absentAfter)
  refine ⟨moved, (exchange.state 7 (by decide)).trans (commands.state 7 (by decide)), ?_, ?_, ?_, ?_⟩
  · rw [exchange.birth 5 (by decide), commands.birth 5 (by decide)]
    rfl
  · rw [exchange.birth 5 (by decide), commands.birth 5 (by decide)]
    rfl
  · rw [exchange.word 5 (by decide), commands.word 5 (by decide)]
    rfl
  · exact (exchange.replayAt 5 (by decide) P).trans (commands.replayAt 5 (by decide) P)

end Cordis.Repairs.CausalOrderExample
