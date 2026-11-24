import Cordis.AccumulatorProvenance
import Cordis.DependentCoeffectExchange

/-! The shared-coeffect primitive exchange used in Lemma 78(1). -/
namespace Cordis.Transposition
open Effects AccumulatorProvenance
open PartialCoeffectLifting PartialInverseObservation
open PartialCoeffectIndependenceContracts (tableSetoid)
open Iterators (OptionRel)
universe u
variable {Key Value Error : Type u} [DecidableEq Key] [Setoid Value]
set_option linter.unusedSectionVars false

/-- Swapping two successful same-key calls preserves both observed outcomes,
compares the new captured inverses, and reaches a related resulting value. -/
def CallbackExchange
    (first second : Value → Except Error (Value × (Value → Value) × Value)) : Prop :=
  ∀ (before afterFirst finalFirstSecond : Value) (firstInverse secondInverse : Value → Value)
    (firstOutcome secondOutcome : Value),
    first before = .ok (afterFirst, firstInverse, firstOutcome) →
    second afterFirst = .ok (finalFirstSecond, secondInverse, secondOutcome) →
    ∃ afterSecond secondInverseBefore finalSecondFirst firstInverseAfter,
      second before = .ok (afterSecond, secondInverseBefore, secondOutcome) ∧
      first afterSecond = .ok (finalSecondFirst, firstInverseAfter, firstOutcome) ∧
      finalSecondFirst ≈ finalFirstSecond ∧
      Effects.Related secondInverse secondInverseBefore ∧
      Effects.Related firstInverseAfter firstInverse

/-- A captured inverse is applied on its original domain. Where it is
undefined, the completed state map leaves the input unchanged. -/
def completeValueInverse (inverse : Value → Option Value) : Value → Value :=
  fun input => (inverse input).getD input

/-- Equation (30) keeps the exact success domain, forward value and outcome.
The recorded inverse is the completed form of the actual partial inverse
returned at that input. -/
def RepresentsCallback (operation : PartialInverseObservation.Operation Value Value)
    (callback : Value → Except Error (Value × (Value → Value) × Value)) : Prop :=
  ∀ input, (operation.run input).map (fun (after, inverse, outcome) =>
    (after, completeValueInverse inverse, outcome)) = (callback input).toOption

private theorem callback_of_partial_success
    {operation : PartialInverseObservation.Operation Value Value}
    {callback : Value → Except Error (Value × (Value → Value) × Value)}
    (represented : RepresentsCallback operation callback)
    {input output : Value} {inverse : Value → Option Value} {outcome : Value}
    (actual : operation.run input = some (output, inverse, outcome)) :
    callback input = .ok (output, completeValueInverse inverse, outcome) := by
  have same := represented input
  rw [actual] at same
  cases called : callback input <;> simpa [called, Except.toOption] using same.symm

private theorem partial_success_of_callback
    {operation : PartialInverseObservation.Operation Value Value}
    {callback : Value → Except Error (Value × (Value → Value) × Value)}
    (represented : RepresentsCallback operation callback)
    {input output : Value} {inverse : Value → Value} {outcome : Value}
    (called : callback input = .ok (output, inverse, outcome)) :
    ∃ actual : Value → Option Value,
      operation.run input = some (output, actual, outcome) ∧ completeValueInverse actual = inverse := by
  have same := represented input
  rw [called] at same
  cases actual : operation.run input with
  | none => simp [actual, Except.toOption] at same
  | some triple =>
    obtain ⟨changed, saved, result⟩ := triple
    have fields : changed = output ∧ completeValueInverse saved = inverse ∧ result = outcome := by
      simpa [actual, Except.toOption, Prod.mk.injEq] using same
    obtain ⟨rfl, inverseEq, rfl⟩ := fields
    exact ⟨saved, rfl, inverseEq⟩

private theorem callback_failure_of_partial
    {operation : PartialInverseObservation.Operation Value Value}
    {callback : Value → Except Error (Value × (Value → Value) × Value)}
    (represented : RepresentsCallback operation callback) {input : Value}
    (undefined : operation.run input = none) : ∃ error, callback input = .error error := by
  have same := represented input
  rw [undefined] at same
  cases called : callback input with
  | error error => exact ⟨error, rfl⟩
  | ok triple => simp [called, Except.toOption] at same

private theorem complete_related {left right : Value → Option Value}
    (related : MapRelated (· ≈ ·) left right) :
    Effects.Related (completeValueInverse left) (completeValueInverse right) := by
  intro input output observed
  have results := related input output observed
  cases a : left input <;> cases b : right output <;>
    simp only [a, b, OptionRel, completeValueInverse, Option.getD] at results ⊢
  · exact observed
  · exact results

/-- The partial operation witness supplies recovery and respect for the
represented completed callback. Recovery uses the inverse on its actual
defined output. Respect uses identity on pairs of undefined inverse probes. -/
theorem callback_witness_of_partial
    {operation : PartialInverseObservation.Operation Value Value}
    {callback : Value → Except Error (Value × (Value → Value) × Value)}
    (represented : RepresentsCallback operation callback)
    (witness : PartialInverseObservation.Witnessed operation (· ≈ ·)) :
    Effects.Witnessed (callbackOperation callback).effect := by
  constructor
  · intro input
    cases actual : operation.run input with
    | none =>
      obtain ⟨error, called⟩ := callback_failure_of_partial represented actual
      simpa [callbackOperation, called] using (Setoid.refl input)
    | some triple =>
      obtain ⟨output, inverse, outcome⟩ := triple
      have called := callback_of_partial_success represented actual
      obtain ⟨restored, saved, related⟩ := witness.recover input output inverse outcome actual
      simpa [callbackOperation, called, completeValueInverse, saved] using related
  · intro left right related
    have probes := witness.respect left right related
    cases lcall : operation.run left <;> cases rcall : operation.run right
    all_goals simp only [lcall, rcall, OptionRel] at probes
    · obtain ⟨leftError, leftCall⟩ := callback_failure_of_partial represented lcall
      obtain ⟨rightError, rightCall⟩ := callback_failure_of_partial represented rcall
      simp only [callbackOperation, leftCall, rightCall]
      exact ⟨related, fun {_ _} observed => observed⟩
    · have leftCall := callback_of_partial_success represented
        (show operation.run left = some (_, _, _) from lcall)
      have rightCall := callback_of_partial_success represented
        (show operation.run right = some (_, _, _) from rcall)
      simp only [callbackOperation, leftCall, rightCall]
      exact ⟨probes.1, complete_related probes.2.1⟩

/-- The operation family with one common value and outcome type. -/
def callbackOperations (names : Key → Type u) (args : (key : Key) → names key → Type u)
    (operation : (key : Key) → (name : names key) → args key name → PartialInverseObservation.Operation Value Value) :
    PaperEffectEquations.CoeffectOperations (fun _ : Key => Value) :=
  ⟨names, args, fun _ _ => Value, operation⟩

/-- Definition 44's partial forward commutation, inverse-yield stability and
Equation (41) imply the primitive exchange on an occupied key. In particular
Equation (41) derives both swapped successes, so their applicability is no
extra assumption. This extracts only the laws needed by Lemma 78. -/
theorem callback_exchange_of_eq44
    {names : Key → Type u} {args : (key : Key) → names key → Type u}
    {operation : (key : Key) → (name : names key) → args key name → PartialInverseObservation.Operation Value Value}
    (key : Key) (leftName rightName : names key)
    (leftArg : args key leftName) (rightArg : args key rightName)
    (first second : Value → Except Error (Value × (Value → Value) × Value))
    (leftRep : RepresentsCallback (operation key leftName leftArg) first)
    (rightRep : RepresentsCallback (operation key rightName rightArg) second)
    (laws : PaperObservationEquations.IndependentOperations (callbackOperations names args operation)
      (tableSetoid (fun _ : Key => (inferInstance : Setoid Value)) (fun _ => True)) key key leftName rightName) :
    CallbackExchange first second := by
  intro before afterFirst finalOriginal firstInverse secondInverse firstOutcome secondOutcome firstCalled secondCalled
  obtain ⟨firstPartial, firstActual, firstComplete⟩ := partial_success_of_callback leftRep firstCalled
  obtain ⟨secondPartial, secondActual, secondComplete⟩ := partial_success_of_callback rightRep secondCalled
  obtain ⟨afterSecond, secondBefore, finalReordered, firstAfter, secondReordered, firstReordered,
    finals, secondSavedRelated, firstSavedRelated⟩ :=
    DependentCoeffectExchange.exchange_same_key (callbackOperations names args operation)
      (fun _ => inferInstance) key leftName rightName leftArg rightArg laws firstActual secondActual
  refine ⟨afterSecond, completeValueInverse secondBefore, finalReordered, completeValueInverse firstAfter,
    callback_of_partial_success rightRep secondReordered, callback_of_partial_success leftRep firstReordered,
    finals, ?_, ?_⟩
  · rw [← secondComplete]
    exact complete_related secondSavedRelated
  · rw [← firstComplete]
    exact complete_related firstSavedRelated

end Cordis.Transposition
