import Cordis.Repairs.ScopedReplayComparison
import Cordis.Repairs.GuardedPartialApplications
import Cordis.SemanticHead

/-! The frozen application in Definition 58 has a strict evaluation on a
compatible probe. Forward applications retain their prescribed draw and
native result. The captured word is fixed, while its retirement guards
read the probe's live birth stamps. -/
namespace Cordis.Repairs.FrozenGuardedApplications
open Calculus Stages RuleEvaluation
open PartialReplayRegistry (Coeffects)
open Vestigial (CutNotes)
open IncarnationReplay (Capture)
open ScopedReplayComparison (Scope DecodeRespects)
open Iterators (OptionRel)

universe u
variable {Name Key Value Code Error : Type u} [DecidableEq Name] [DecidableEq Key]
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "C" => Capture Name Key Value
local notation "U" => Use Name Key Value Code
local notation "Program" => Code → Instruction Name Key Value Code Error

noncomputable def freeze {program : Program} (meaning : Coeffects program) (actor draw : Name)
    (use : U) (saved : List C) (live : Name → Option Nat) (state : R) : Option R := by
  classical
  exact match use with
  | .identity => some state
  | .iteration code => (SemanticHead.evaluate program actor draw code state).map Prod.fst
  | .accumulator tokens => if tokens = saved.map Capture.token then ScopedReplayComparison.run meaning live saved state else none

/-- A guarded application determines the actual successful frozen map
evaluation at its source. The primitive draw is recovered from the capture. -/
theorem freeze_of_application {program : Program} (meaning : Coeffects program) (notes : CutNotes Name Key Value)
    {actor : Name} {use : U} {before after : R}
    (applied : GuardedPartialApplications.Application meaning notes actor use before after) :
    ∃ draw, freeze meaning actor draw use (notes.2 actor) notes.1 before = some after := by
  cases use with
  | identity => cases applied; exact ⟨actor, rfl⟩
  | iteration code =>
    cases applied with
    | iteration _ _ _ inverse next landed =>
      let draw := match inverse with | .retire child => child | _ => actor
      have selected : SemanticHead.CapturedChoice draw inverse := by cases inverse <;> first | rfl | trivial
      have evaluated := SemanticHead.evaluate_complete program landed draw selected
      exact ⟨draw, by simp [freeze, evaluated]⟩
  | accumulator tokens =>
    obtain ⟨selected, defined, endpoint⟩ := applied
    refine ⟨actor, ?_⟩
    simpa only [freeze, if_pos selected] using
      (ScopedReplayComparison.success_iff meaning notes.1 (notes.2 actor) before after).mpr ⟨defined, endpoint.symm⟩

/-- Success on any probe gives the corresponding guarded application,
with the strict saved-word domain or the actual selected primitive. -/
theorem application_of_freeze {program : Program} (meaning : Coeffects program) (notes : CutNotes Name Key Value)
    {actor draw : Name} {use : U} {before after : R}
    (called : freeze meaning actor draw use (notes.2 actor) notes.1 before = some after) :
    GuardedPartialApplications.Application meaning notes actor use before after := by
  classical
  cases use with
  | identity =>
    change some before = some after at called
    cases Option.some.inj called
    exact .identity _
  | iteration code =>
    change (SemanticHead.evaluate program actor draw code before).map Prod.fst = some after at called
    obtain ⟨⟨output, inverse, next⟩, evaluated, rfl⟩ := Option.map_eq_some_iff.mp called
    exact .iteration _ _ _ _ _ (SemanticHead.evaluate_sound program actor draw code before output inverse next evaluated).1
  | accumulator tokens =>
    by_cases valid : tokens = (notes.2 actor).map Capture.token
    · simp only [freeze, if_pos valid] at called
      have defined := (ScopedReplayComparison.success_iff meaning _ _ _ _).mp called
      exact ⟨valid, defined.1, defined.2.symm⟩
    · simp [freeze, valid] at called

theorem factorization_at_cut {program : Program} {last time : Nat}
    (trace : GuardedHistory.Trace program last) (meaning : Coeffects program) (bounded : time < last) :
    ∃ (use : U) (draw : Name) (middle : R) (edit : Edit Name Key Value Code),
      freeze meaning (trace.actor time) draw use ((trace.notes time).2 (trace.actor time)) (trace.notes time).1
        (trace.state time) = some middle ∧
      use.allowed (GuardedHistory.eventRule (trace.event time)) (trace.state time) (trace.actor time) ∧
      edit.allowed (GuardedHistory.eventRule (trace.event time)) (trace.actor time) ∧
      edit.valid middle ∧ trace.state (time + 1) = edit.apply middle ∧ TablesUnchanged middle (trace.state (time + 1)) := by
  obtain ⟨use, middle, edit, applied, permitted, changes, valid, output, tables, _⟩ :=
    GuardedPartialApplications.trace_factorization trace meaning bounded
  obtain ⟨draw, frozen⟩ := freeze_of_application meaning (trace.notes time) applied
  exact ⟨use, draw, middle, edit, frozen, permitted, changes, valid, output, tables⟩

inductive UseRelated (actor : Name) (left right : CutNotes Name Key Value) : U → U → Prop where
  | identity : UseRelated actor left right .identity .identity
  | iteration (code : Code) : UseRelated actor left right (.iteration code) (.iteration code)
  | accumulator : UseRelated actor left right (.accumulator ((left.2 actor).map Capture.token))
      (.accumulator ((right.2 actor).map Capture.token))

theorem UseRelated.allowed [Setoid Value] {actor : Name} {first second : CutNotes Name Key Value}
    {firstUse secondUse : U} (uses : UseRelated actor first second firstUse secondUse)
    {left right : R} (states : StageSimulation.Related Eq left right)
    (projects : GuardedSuffix.SavedWordsAgree right second) {rule : Labeled.Rule}
    (allowed : firstUse.allowed rule left actor) : secondUse.allowed rule right actor := by
  cases uses with
  | identity => exact allowed
  | iteration code =>
    obtain ⟨ruleAllowed, row, word, view, present, phase⟩ := allowed
    obtain ⟨other, found, fields⟩ := StageSimulation.present_related states actor row present
    have phases := fields.phase
    rw [phase] at phases
    generalize otherPhase : other.phase = actual at phases
    cases phases with
    | reloading _ same words =>
      cases same
      exact ⟨ruleAllowed, other, _, _, found, otherPhase⟩
  | accumulator =>
    obtain ⟨ruleAllowed, row, view, present, phase⟩ := allowed
    obtain ⟨other, found, fields⟩ := StageSimulation.present_related states actor row present
    have phases := fields.phase
    rw [phase] at phases
    generalize otherPhase : other.phase = actual at phases
    cases phases with
    | @unloading _ word _ _ =>
      have actualWord : (second.2 actor).map Capture.token = word := by
        simpa [PartialReplayRegistry.saved, found, otherPhase, Phase.accumulator] using projects actor
      exact ⟨ruleAllowed, other, _, found, by simpa only [actualWord] using otherPhase⟩

private theorem pair_use_of_application {program : Program} (meaning : Coeffects program)
    {actor : Name} {firstUse : U} {before middle : R} {first second : CutNotes Name Key Value}
    (applied : GuardedPartialApplications.Application meaning first actor firstUse before middle) :
    ∃ otherUse, UseRelated actor first second firstUse otherUse := by
  cases firstUse with
  | identity => exact ⟨.identity, .identity⟩
  | iteration code => exact ⟨.iteration code, .iteration code⟩
  | accumulator tokens =>
    have selected := applied.1
    subst tokens
    exact ⟨_, .accumulator⟩

section Typed
open PaperEffectEquations (CoeffectOperations ValueOperationWitness)
open PaperObservationEquations (OperationRespects)
open PartialCoeffectIndependenceContracts (tableSetoid)
open TypedRegistry (Scalar RawRegistry encodeProgram)
variable {V : Key → Type u} {ops : CoeffectOperations V}
local notation "A" => Scalar ops
local notation "Raw" => RawRegistry Name ops Code
local notation "TProgram" => Code → TypedRegistry.Instruction Name ops Code
local notation "Result" => SemanticHead.Result Name Key A Code PUnit
local notation "Notes" => CutNotes Name Key A
variable (observe : ∀ key, Setoid (V key))
local notation "Related" => @StageSimulation.Related Name Key A Code _ (TypedCoeffectReplay.setoid observe) Eq
local notation "Paired" => @EpisodeAnnotations.NotesRelated Name Key A (TypedCoeffectReplay.setoid observe)

def ResultRelated (left right : Result) : Prop :=
  Related left.1 right.1 ∧
  @StageSimulation.InverseRelated Name Key A (TypedCoeffectReplay.setoid observe) left.2.1 right.2.1 ∧ left.2.2 = right.2.2

private theorem move_head {program : TProgram}
    (respect : ∀ key, OperationRespects ops key (observe key).r)
    {actor draw : Name} {code : Code} {left right : Raw} (states : Related left right)
    {result : Result} (called : SemanticHead.evaluate (encodeProgram program) actor draw code left = some result) :
    ∃ moved, SemanticHead.evaluate (encodeProgram program) actor draw code right = some moved ∧
      ResultRelated observe result moved := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  obtain ⟨output, token, next⟩ := result
  obtain ⟨landed, selected⟩ := SemanticHead.evaluate_sound (encodeProgram program) actor draw code left output token next called
  obtain ⟨newOutput, newToken, native, paired, captures⟩ :=
    TypedRegistry.encoded_land_simulation ops observe program respect states landed
  have sameDraw : SemanticHead.CapturedChoice draw newToken := by cases captures <;> exact selected
  exact ⟨(newOutput, newToken, next), SemanticHead.evaluate_complete (encodeProgram program) native draw sameDraw,
    paired, captures, rfl⟩

/-- Evaluating a stored forward head on related probes agrees on whether
it succeeds and, on success, on its native phase data and next code. -/
theorem head_respects {program : TProgram}
    (respect : ∀ key, OperationRespects ops key (observe key).r)
    (actor draw : Name) (code : Code) {left right : Raw} (states : Related left right) :
    OptionRel (ResultRelated observe)
      (SemanticHead.evaluate (encodeProgram program) actor draw code left)
      (SemanticHead.evaluate (encodeProgram program) actor draw code right) := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  cases first : SemanticHead.evaluate (encodeProgram program) actor draw code left with
  | none =>
    cases second : SemanticHead.evaluate (encodeProgram program) actor draw code right with
    | none => trivial
    | some result =>
      obtain ⟨_, found, _⟩ := move_head observe respect (states.symm (fun _ _ same => same.symm)) second
      rw [first] at found
      cases found
  | some result =>
    obtain ⟨moved, evaluated, compared⟩ := move_head observe respect states first
    rw [evaluated]
    exact compared

/-- All three frozen applications compare on structurally related
compatible probes. The accumulator's domain is tested by strict replay. -/
theorem freeze_respects {program : TProgram}
    (recovery : ValueOperationWitness ops)
    (laws : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r)
    (actor draw : Name) {firstUse secondUse : Use Name Key A Code} {first second : Notes} (notes : Paired first second)
    (uses : UseRelated actor first second firstUse secondUse)
    {left right : Raw} (states : Related left right)
    (scope : match firstUse with
      | .accumulator _ => Scope (first.2 actor) left ∧ Scope (second.2 actor) right
      | _ => True) :
    let meaning := TypedReplayContracts.coeffects ops observe program recovery laws
    OptionRel Related (freeze meaning actor draw firstUse (first.2 actor) first.1 left)
      (freeze meaning actor draw secondUse (second.2 actor) second.1 right) := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  let meaning := TypedReplayContracts.coeffects ops observe program recovery laws
  cases uses with
  | identity => exact states
  | iteration code =>
    have same := head_respects observe (program := program) respect actor draw code states
    change OptionRel Related ((SemanticHead.evaluate (encodeProgram program) actor draw code left).map Prod.fst)
      ((SemanticHead.evaluate (encodeProgram program) actor draw code right).map Prod.fst)
    cases first : SemanticHead.evaluate (encodeProgram program) actor draw code left <;>
      cases second : SemanticHead.evaluate (encodeProgram program) actor draw code right <;>
      simp only [first, second, Option.map_some, Option.map_none, OptionRel] at same ⊢
    exact same.1
  | accumulator =>
    simpa only [freeze, if_pos rfl] using ScopedReplayComparison.run_respects_states meaning
      (ScopedReplayComparison.typed_decode_respects ops observe program recovery laws) notes actor states scope.1 scope.2

/-- Actual guarded cuts supply the whole accumulator scope, including the
provider declarations and every intermediate partial inverse domain. -/
theorem freeze_respects_at_cuts {program : TProgram} {leftLast rightLast leftCut rightCut : Nat}
    (recovery : ValueOperationWitness ops)
    (laws : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r)
    (left : GuardedHistory.Trace (encodeProgram program) leftLast) (right : GuardedHistory.Trace (encodeProgram program) rightLast)
    (hi : leftCut ≤ leftLast) (hj : rightCut ≤ rightLast)
    (actor draw : Name) {firstUse secondUse : Use Name Key A Code}
    (uses : UseRelated actor (left.notes leftCut) (right.notes rightCut) firstUse secondUse)
    (notes : Paired (left.notes leftCut) (right.notes rightCut)) (states : Related (left.state leftCut) (right.state rightCut)) :
    let meaning := TypedReplayContracts.coeffects ops observe program recovery laws
    OptionRel Related
      (freeze meaning actor draw firstUse ((left.notes leftCut).2 actor) (left.notes leftCut).1 (left.state leftCut))
      (freeze meaning actor draw secondUse ((right.notes rightCut).2 actor) (right.notes rightCut).1 (right.state rightCut)) := by
  let meaning := TypedReplayContracts.coeffects ops observe program recovery laws
  apply freeze_respects observe recovery laws respect actor draw notes uses states
  cases uses with
  | identity | iteration => exact True.intro
  | accumulator => exact ⟨(ScopedReplayComparison.trace_word left leftCut hi meaning actor).1,
    (ScopedReplayComparison.trace_word right rightCut hj meaning actor).1⟩

/-- Transfer an actual Definition 58 application to the paired reachable
cut. The selected code or saved word comes from that cut's own phase. -/
theorem application_at_related_cut {program : TProgram} {leftLast rightLast leftCut rightCut : Nat}
    (recovery : ValueOperationWitness ops)
    (laws : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r)
    (left : GuardedHistory.Trace (encodeProgram program) leftLast) (right : GuardedHistory.Trace (encodeProgram program) rightLast)
    (hi : leftCut ≤ leftLast) (hj : rightCut ≤ rightLast)
    {rule : Labeled.Rule} {actor : Name} {use : Use Name Key A Code} {middle : Raw}
    (notes : Paired (left.notes leftCut) (right.notes rightCut)) (states : Related (left.state leftCut) (right.state rightCut))
    (permitted : use.allowed rule (left.state leftCut) actor)
    (actual : GuardedPartialApplications.Application (TypedReplayContracts.coeffects ops observe program recovery laws)
      (left.notes leftCut) actor use (left.state leftCut) middle) :
    let meaning := TypedReplayContracts.coeffects ops observe program recovery laws
    ∃ otherUse draw next,
      UseRelated actor (left.notes leftCut) (right.notes rightCut) use otherUse ∧
      otherUse.allowed rule (right.state rightCut) actor ∧
      freeze meaning actor draw use ((left.notes leftCut).2 actor) (left.notes leftCut).1 (left.state leftCut) = some middle ∧
      freeze meaning actor draw otherUse ((right.notes rightCut).2 actor) (right.notes rightCut).1 (right.state rightCut) = some next ∧
      GuardedPartialApplications.Application meaning (right.notes rightCut) actor otherUse (right.state rightCut) next ∧
      Related middle next := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  let meaning := TypedReplayContracts.coeffects ops observe program recovery laws
  obtain ⟨otherUse, uses⟩ := pair_use_of_application (second := right.notes rightCut) meaning actual
  obtain ⟨draw, moved⟩ := freeze_of_application meaning (left.notes leftCut) actual
  have comparison := freeze_respects_at_cuts observe recovery laws respect left right hi hj actor draw uses notes states
  change OptionRel Related
    (freeze meaning actor draw use ((left.notes leftCut).2 actor) (left.notes leftCut).1 (left.state leftCut))
    (freeze meaning actor draw otherUse ((right.notes rightCut).2 actor) (right.notes rightCut).1 (right.state rightCut)) at comparison
  rw [moved] at comparison
  cases frozen : freeze meaning actor draw otherUse ((right.notes rightCut).2 actor) (right.notes rightCut).1
      (right.state rightCut) with
  | none => simp only [frozen, OptionRel] at comparison
  | some next =>
    rw [frozen] at comparison
    exact ⟨otherUse, draw, next, uses, uses.allowed states (right.projects rightCut hj) permitted, moved, frozen,
      application_of_freeze meaning (right.notes rightCut) frozen, comparison⟩

end Typed
end Cordis.Repairs.FrozenGuardedApplications
