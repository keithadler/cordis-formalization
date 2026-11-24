import Cordis.Repairs.ScopedIteratorObservation
import Cordis.Repairs.ScopedReplayComparison
import Cordis.Repairs.GuardedIteratorProvenance
import Cordis.Repairs.GuardedPartialComparison

/-! The scoped comparison of stored function fields in Equation (54).
Rule guards keep their structural evidence. Entry and remaining iterators
are compared recursively on admitted head domains, and a stored accumulator
is compared as a strict partial function on its captured provider scope. -/
namespace Cordis.Repairs.ScopedEquation54
open Calculus GuardedIteratorProvenance
open PaperEffectEquations (CoeffectOperations ValueOperationWitness)
open PaperObservationEquations (OperationRespects)
open PartialCoeffectIndependenceContracts (tableSetoid)
open PartialReplayRegistry (Coeffects)
open TypedRegistry (Scalar RawRegistry RawFiber encodeProgram)
open IncarnationReplay (Capture)
open Vestigial (CutNotes)
open Iterators (OptionRel)

universe u
variable {Name Key Code : Type u} {V : Key → Type u} {ops : CoeffectOperations V}
variable [DecidableEq Name] [DecidableEq Key]
local notation "A" => Scalar ops
local notation "R" => RawRegistry Name ops Code
local notation "F" => RawFiber Name ops Code
local notation "Word" => List (Capture Name Key A)
local notation "Notes" => CutNotes Name Key A
local notation "Program" => Code → TypedRegistry.Instruction Name ops Code
variable {program : Code → TypedRegistry.Instruction Name ops Code}
variable (observe : ∀ key, Setoid (V key))
local notation "Structural" => @StageSimulation.Related Name Key A Code _ (TypedCoeffectReplay.setoid observe) Eq
local notation "Annotated" => @EpisodeAnnotations.NotesRelated Name Key A (TypedCoeffectReplay.setoid observe)
local notation "Observed" => PaperStateObservation.TablesRelatedAt (fun _ : Key => TypedCoeffectReplay.setoid observe)
  (fun _ => True)

/-- A stored code is compared through its native mediated grammar. Every
common provider route and draw specification is covered. The iterators
are compared on their respective synthesized domains. -/
def CodesCompared (lawful : MediatedAdmission.OperationsLawful ops observe) (actor : Name)
    (component : Component Key Code) (left right : Code) : Prop :=
  ∃ leftGrammar : MediatedAdmission.Mediated program component left,
  ∃ rightGrammar : MediatedAdmission.Mediated program component right,
    ∀ (choices : MediatedAdmission.Choices ops Name Code) (history : List (TypedRegistry.Outcome Name ops)),
      let leftPlan := MediatedAdmission.admit (actor := actor) choices lawful leftGrammar history
      let rightPlan := MediatedAdmission.admit (actor := actor) choices lawful rightGrammar history
      ScopedIteratorObservation.Related
        ⟨left, leftPlan.domain, leftPlan.iterator⟩ ⟨right, rightPlan.domain, rightPlan.iterator⟩

theorem CodesCompared.same (lawful : MediatedAdmission.OperationsLawful ops observe) (actor : Name)
    {component : Component Key Code} {code : Code} (grammar : MediatedAdmission.Mediated program component code) :
    CodesCompared (program := program) observe lawful actor component code code :=
  ⟨grammar, grammar, fun choices history => ScopedIteratorObservation.mediated_related actor choices lawful grammar history⟩

/-- Provider-compatible probes may vary in tables, occupancy, other
control fields, and live birth stamps. The latter only govern retirements. -/
def AccumulatorsCompared (meaning : Coeffects (encodeProgram program)) (left right : Word) : Prop :=
  ∀ live other {probe alternative : R}, ScopedReplayComparison.Scope left probe → ScopedReplayComparison.Scope right alternative →
    Observed probe alternative → OptionRel Observed (ScopedReplayComparison.run meaning live left probe)
      (ScopedReplayComparison.run meaning other right alternative)

structure StateRelated (lawful : MediatedAdmission.OperationsLawful ops observe)
    (meaning : Coeffects (encodeProgram program)) (left right : R) (first second : Notes) : Prop where
  controls : Structural left right
  stamps : Annotated first second
  leftCaptures : GuardedSuffix.SavedWordsAgree left first
  rightCaptures : GuardedSuffix.SavedWordsAgree right second
  entries : ∀ actor (a b : F), left actor = some a → right actor = some b →
    CodesCompared (program := program) observe lawful actor a.component a.component.entry b.component.entry
  remaining : ∀ actor (a b : F), left actor = some a → right actor = some b →
    ∀ code next word rest view other,
      a.phase = .reloading code word view → b.phase = .reloading next rest other →
      CodesCompared (program := program) observe lawful actor a.component code next
  accumulators : ∀ actor, AccumulatorsCompared observe meaning (first.2 actor) (second.2 actor)

theorem StateRelated.tables {lawful : MediatedAdmission.OperationsLawful ops observe}
    {meaning : Coeffects (encodeProgram program)} {left right : R} {first second : Notes}
    (related : StateRelated observe lawful meaning left right first second) : Observed left right := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  exact PaperStateObservation.tables_of_homogeneous (related.controls.tables.projected (fun _ => True)) (fun _ _ _ same => same)

private theorem StateRelated.left_codes {lawful : MediatedAdmission.OperationsLawful ops observe}
    {meaning : Coeffects (encodeProgram program)} {left right : R} {first second : Notes}
    (related : StateRelated observe lawful meaning left right first second) :
    Entries (encodeProgram program) left ∧ Remaining (encodeProgram program) left := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  constructor
  · intro actor a found
    obtain ⟨b, present, _⟩ := StageSimulation.present_related related.controls actor a found
    obtain ⟨grammar, _, _⟩ := related.entries actor a b found present
    exact grammar
  · apply Remaining.of_rows
    intro actor a code word view found phase
    obtain ⟨b, present, pair⟩ := StageSimulation.present_related related.controls actor a found
    have phases := pair.phase
    rw [phase] at phases
    generalize moved : b.phase = actual at phases
    cases phases with
    | reloading _ _ _ =>
      obtain ⟨grammar, _, _⟩ := related.remaining actor a b found present _ _ _ _ _ _ phase moved
      exact grammar

private theorem StateRelated.right_codes {lawful : MediatedAdmission.OperationsLawful ops observe}
    {meaning : Coeffects (encodeProgram program)} {left right : R} {first second : Notes}
    (related : StateRelated observe lawful meaning left right first second) :
    Entries (encodeProgram program) right ∧ Remaining (encodeProgram program) right := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  have states := related.controls.symm (fun _ _ same => same.symm)
  constructor
  · intro actor b present
    obtain ⟨a, found, pair⟩ := StageSimulation.present_related states actor b present
    obtain ⟨_, grammar, _⟩ := related.entries actor a b found present
    exact pair.component.eq_of_codes.symm ▸ grammar
  · apply Remaining.of_rows
    intro actor b code word view present phase
    obtain ⟨a, found, pair⟩ := StageSimulation.present_related states actor b present
    have phases := pair.phase
    rw [phase] at phases
    generalize moved : a.phase = actual at phases
    cases phases with
    | reloading _ _ _ =>
      obtain ⟨_, grammar, _⟩ := related.remaining actor a b found present _ _ _ _ _ _ moved phase
      exact pair.component.eq_of_codes.symm ▸ grammar

/-- Structural comparison on admitted native fields supplies the scoped
function-field clauses. The exact code is used to construct a grammar
witness on both sides, which is then checked by the recursive relation. -/
theorem of_structural (lawful : MediatedAdmission.OperationsLawful ops observe)
    (meaning : Coeffects (encodeProgram program))
    (decodes : @ScopedReplayComparison.DecodeRespects Name Key A Code _ (encodeProgram program)
      (TypedCoeffectReplay.setoid observe) meaning)
    {left right : R} {first second : Notes} (states : Structural left right) (notes : Annotated first second)
    (leftCaptures : GuardedSuffix.SavedWordsAgree left first) (rightCaptures : GuardedSuffix.SavedWordsAgree right second)
    (entries : Entries (encodeProgram program) left) (remaining : Remaining (encodeProgram program) left) :
    StateRelated observe lawful meaning left right first second := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  refine ⟨states, notes, leftCaptures, rightCaptures, ?_, ?_, ?_⟩
  · intro actor a b found present
    have pair := states actor
    rw [found, present] at pair
    change StageSimulation.FiberRelated Eq a b at pair
    rw [← pair.component.entry]
    exact CodesCompared.same observe lawful actor (entries actor a found)
  · intro actor a b found present code next word rest view other leftPhase rightPhase
    have pair := states actor
    rw [found, present] at pair
    change StageSimulation.FiberRelated Eq a b at pair
    have phases := pair.phase
    rw [leftPhase, rightPhase] at phases
    cases phases with
    | reloading _ same _ =>
      cases same
      exact CodesCompared.same observe lawful actor (remaining.at_row found leftPhase)
  · intro actor live other probe alternative firstScope secondScope observed
    exact ScopedReplayComparison.run_respects meaning decodes live other (notes.words actor) firstScope secondScope observed

theorem at_cuts (lawful : MediatedAdmission.OperationsLawful ops observe)
    (recovery : ValueOperationWitness ops)
    (laws : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    {leftLast rightLast leftCut rightCut : Nat}
    (left : GuardedHistory.Trace (encodeProgram program) leftLast) (right : GuardedHistory.Trace (encodeProgram program) rightLast)
    (hi : leftCut ≤ leftLast) (hj : rightCut ≤ rightLast) (admitted : BirthsMediated left)
    (states : Structural (left.state leftCut) (right.state rightCut)) (notes : Annotated (left.notes leftCut) (right.notes rightCut)) :
    StateRelated observe lawful (TypedReplayContracts.coeffects ops observe program recovery laws)
      (left.state leftCut) (right.state rightCut) (left.notes leftCut) (right.notes rightCut) := by
  obtain ⟨entries, remaining⟩ := codes_at_cut left admitted leftCut hi
  exact of_structural observe lawful _ (ScopedReplayComparison.typed_decode_respects ops observe program recovery laws)
    states notes (left.projects leftCut hi) (right.projects rightCut hj) entries remaining

local notation "Event" => LegalHistory.Event Name Key Code

/-- A rule with an admitted new component transfers with its payload and
its Definition 58 applications. All stored semantic fields compare again
at the two resulting cuts. -/
def StepLifts (lawful : MediatedAdmission.OperationsLawful ops observe) (meaning : Coeffects (encodeProgram program))
    {leftLast rightLast : Nat} (left : GuardedHistory.Trace (encodeProgram program) leftLast)
    (right : GuardedHistory.Trace (encodeProgram program) rightLast) (time : Nat) : Prop :=
  ∀ (event : Event) (after : R) (recorded : Notes),
    GuardedSuffix.Step (encodeProgram program) event (time + 1) (left.state time) (left.notes time) after recorded →
    NewEntries (encodeProgram program) (left.state time) after →
    ∃ (moved : R) (otherNotes : Notes),
      GuardedSuffix.Step (encodeProgram program) event (time + 1) (right.state time) (right.notes time) moved otherNotes ∧
      StateRelated observe lawful meaning after moved recorded otherNotes ∧
      GuardedPartialApplications.Factored meaning (left.notes time) event (left.state time) after ∧
      GuardedPartialApplications.Factored meaning (right.notes time) event (right.state time) moved

private theorem step_lifts (lawful : MediatedAdmission.OperationsLawful ops observe)
    (meaning : Coeffects (encodeProgram program))
    (decodes : @ScopedReplayComparison.DecodeRespects Name Key A Code _ (encodeProgram program)
      (TypedCoeffectReplay.setoid observe) meaning)
    {leftLast rightLast time : Nat} (left : GuardedHistory.Trace (encodeProgram program) leftLast)
    (right : GuardedHistory.Trace (encodeProgram program) rightLast) (hi : time ≤ leftLast) (hj : time ≤ rightLast)
    (earlier : Entries (encodeProgram program) (left.state time))
    (current : Remaining (encodeProgram program) (left.state time))
    (lift : GuardedPartialComparison.StepLifts observe meaning left right time) :
    StepLifts observe lawful meaning left right time := by
  intro event after recorded step accepted
  obtain ⟨moved, otherNotes, simulated, outputs, paired, factored, otherFactored⟩ := lift event after recorded step
  have entries := entries_after (GuardedHistory.transition_stable step.1) earlier accepted
  have remaining := remaining_after_guarded step.1 earlier current
  have resulting := of_structural observe lawful meaning decodes outputs paired
    (GuardedSuffix.step_projects step (left.projects time hi))
    (GuardedSuffix.step_projects simulated (right.projects time hj)) entries remaining
  exact ⟨moved, otherNotes, simulated, resulting, factored, otherFactored⟩

/-- Repaired Lemma 60 on guarded cuts for the native mediated program.
The paper's component-admission premise applies to an actual new entry.
The history derives the grammar of all stored remaining iterators. -/
theorem lemma60_scoped (recovery : ValueOperationWitness ops)
    (laws : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r)
    {leftLast rightLast time : Nat} (left : GuardedHistory.Trace (encodeProgram program) leftLast)
    (right : GuardedHistory.Trace (encodeProgram program) rightLast) (hi : time ≤ leftLast) (hj : time ≤ rightLast)
    (inputs : StateRelated observe (MediatedAdmission.lawful_of_contracts ops observe recovery respect)
      (TypedReplayContracts.coeffects ops observe program recovery laws)
      (left.state time) (right.state time) (left.notes time) (right.notes time)) :
    let meaning := TypedReplayContracts.coeffects ops observe program recovery laws
    let lawful := MediatedAdmission.lawful_of_contracts ops observe recovery respect
    StepLifts observe lawful meaning left right time ∧ StepLifts observe lawful meaning right left time := by
  let meaning := TypedReplayContracts.coeffects ops observe program recovery laws
  let lawful := MediatedAdmission.lawful_of_contracts ops observe recovery respect
  have decodes := ScopedReplayComparison.typed_decode_respects ops observe program recovery laws
  obtain ⟨first, second⟩ := GuardedPartialComparison.step_bisimulation observe meaning respect left right hi hj
    inputs.controls inputs.stamps
  have leftCodes := inputs.left_codes observe
  have rightCodes := inputs.right_codes observe
  exact ⟨step_lifts observe lawful meaning decodes left right hi hj leftCodes.1 leftCodes.2 first,
    step_lifts observe lawful meaning decodes right left hj hi rightCodes.1 rightCodes.2 second⟩

end Cordis.Repairs.ScopedEquation54
