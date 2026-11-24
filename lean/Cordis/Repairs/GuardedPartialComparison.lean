import Cordis.Repairs.GuardedPartialApplications
import Cordis.Repairs.GuardedSuffixTransport

/-! A guarded, component-compatible form of Lemma 60 at reachable cuts.
The state comparison carries the rule's control fields and actual captures.
Every resulting step has its partial Definition 58 application. -/
namespace Cordis.Repairs.GuardedPartialComparison
open LegalHistory GuardedHistory GuardedPartialApplications
open EpisodeAnnotations (NotesRelated)
open TypedRegistry (Scalar RawRegistry encodeProgram)
open PartialReplayRegistry (Coeffects)
open PaperEffectEquations (CoeffectOperations)
open PaperObservationEquations (OperationRespects)
open Vestigial (CutNotes)

universe u
variable {Name Key Code : Type u} {V : Key → Type u} {ops : CoeffectOperations V}
variable [DecidableEq Name] [DecidableEq Key]
local notation "A" => Scalar ops
local notation "R" => RawRegistry Name ops Code
local notation "Notes" => CutNotes Name Key A
local notation "Ev" => Event Name Key Code
variable (observe : ∀ key, Setoid (V key))
local notation "Related" => @StageSimulation.Related Name Key A Code _ (TypedCoeffectReplay.setoid observe) Eq
local notation "Paired" => @NotesRelated Name Key A (TypedCoeffectReplay.setoid observe)
variable {program : Code → TypedRegistry.Instruction Name ops Code} {last otherLast time : Nat}

/-- Lifting preserves the exact event label, including the command payload
or lifecycle actor. The two applications and their intermediate domains
are obtained from the actual source and extended target cuts. -/
def StepLifts (meaning : Coeffects (encodeProgram program)) (left : Trace (encodeProgram program) last)
    (right : Trace (encodeProgram program) otherLast) (time : Nat) : Prop :=
  ∀ (event : Ev) (after : R) (recorded : Notes),
    GuardedSuffix.Step (encodeProgram program) event (time + 1)
      (left.state time) (left.notes time) after recorded →
    ∃ (moved : R) (otherNotes : Notes),
      GuardedSuffix.Step (encodeProgram program) event (time + 1)
        (right.state time) (right.notes time) moved otherNotes ∧
      Related after moved ∧ Paired recorded otherNotes ∧
      Factored meaning (left.notes time) event (left.state time) after ∧
      Factored meaning (right.notes time) event (right.state time) moved

private theorem step_lifts (meaning : Coeffects (encodeProgram program))
    (respect : ∀ key, OperationRespects ops key (observe key).r)
    (left : Trace (encodeProgram program) last) (right : Trace (encodeProgram program) otherLast)
    (hi : time ≤ last) (hj : time ≤ otherLast)
    (states : Related (left.state time) (right.state time)) (notes : Paired (left.notes time) (right.notes time)) :
    StepLifts observe meaning left right time := by
  intro event after recorded step
  obtain ⟨moved, otherNotes, simulated, output, aligned, _, _⟩ :=
    GuardedSuffix.transport_step observe program respect step states notes (right.projects time hj)
  exact ⟨moved, otherNotes, simulated, output, aligned, factorization_of_step left meaning hi step,
    factorization_of_step right meaning hj simulated⟩

/-- Bidirectional guarded step comparison at actual cuts under typed
operation respect. This form of Lemma 60 compares matching controls and
annotated words while preserving the value observation on tables. -/
theorem step_bisimulation (meaning : Coeffects (encodeProgram program))
    (respect : ∀ key, OperationRespects ops key (observe key).r)
    (left : Trace (encodeProgram program) last) (right : Trace (encodeProgram program) otherLast)
    (hi : time ≤ last) (hj : time ≤ otherLast)
    (states : Related (left.state time) (right.state time)) (notes : Paired (left.notes time) (right.notes time)) :
    StepLifts observe meaning left right time ∧ StepLifts observe meaning right left time := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  exact ⟨step_lifts observe meaning respect left right hi hj states notes,
    step_lifts observe meaning respect right left hj hi (StageSimulation.Related.symm (fun _ _ eq => eq.symm) states)
      notes.symm⟩

end Cordis.Repairs.GuardedPartialComparison
