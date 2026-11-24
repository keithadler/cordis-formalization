import Cordis.PaperTranspositionObservation
import Cordis.TranspositionActivation

/-! Lemma 78(1) for nondeterministic name selection and successful stages.
The primitive hypotheses apply at one key at a time. The reversed execution
reuses each original fresh name. No allocator is fixed across executions. -/
namespace Cordis.Results
noncomputable section
open Calculus Stages Iterators Effects StageRecovery
universe u
variable {Name Key Value Code Error : Type u}
variable [DecidableEq Name] [DecidableEq Key] [Setoid Value]
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
local notation "I" => Inverse Name Key Value
set_option linter.unusedSectionVars false

/-- Captured inverse pairs also respect the coarser per-owner table quotient:
no domain, retirement or control-field agreement is needed at the input. This
is deliberately not a union-table quotient allowing a binding to change owner. -/
private theorem captured_inverse_tables {left right : Inverse Name Key Value}
    (related : StageSimulation.InverseRelated left right) {r s : R}
    (observed : StageRecovery.TablesRelated r s) :
    StageRecovery.TablesRelated (Stages.undo left r) (Stages.undo right s) := by
  intro owner key
  cases related with
  | unit => exact observed owner key
  | restrict n k =>
    rw [StageRecovery.tableAt_restrict, StageRecovery.tableAt_restrict]
    split
    · trivial
    · exact observed owner key
  | retire child =>
    simpa only [Stages.undo, StageRecovery.tableAt_retire] using observed owner key
  | operate n k inverses =>
    rw [StageRecovery.tableAt_operate, StageRecovery.tableAt_operate]
    split
    · have values := observed n k
      cases left : StageRecovery.tableAt r n k <;> cases right : StageRecovery.tableAt s n k <;>
        simp_all [OptionRel]
      exact inverses values
    · exact observed owner key

theorem captured_stack_tables {left right : List (Inverse Name Key Value)}
    (related : StageSimulation.StackRelated left right) {r s : R}
    (observed : StageRecovery.TablesRelated r s) :
    StageRecovery.TablesRelated (discharge Stages.undo left r) (discharge Stages.undo right s) := by
  induction related generalizing r s with
  | nil => exact observed
  | cons heads tails ih => exact ih (captured_inverse_tables heads observed)

variable (sem : PaperStateObservation.Semantics Name Key Value Code Error)
local instance : Setoid sem.Gamma := PaperStateObservation.base sem

/-- Structural pairing is used only at the SAME input. Global generator
respect supplies the distinct-input step required by Definition34. -/
private theorem stack_related {left right : List I}
    (compatible : ∀ key (v w : Value), v ≈ w → (sem.keyObservation key).r v w)
    (addressed : sem.undo = Stages.undo)
    (paired : StageSimulation.StackRelated left right)
    (generated : ∀ token ∈ right, PaperTranspositionObservation.GeneratedInverse sem token) :
    PaperStateObservation.AccumulatorRelated sem left right := by
  have respects := PaperStateObservation.accumulator_respects sem right
    (fun token member => PaperTranspositionObservation.generated_inverse_respects sem (generated token member))
  intro before after observed
  have pointwise := PaperStateObservation.tables_of_homogeneous
    ((captured_stack_tables paired (tables_refl before.val)).projected (fun _ => True)) compatible
  have crossed := respects observed
  change PaperStateObservation.TablesRelatedAt sem.keyObservation (fun _ => True)
    (PaperStateObservation.accumulator sem right before).val
    (PaperStateObservation.accumulator sem right after).val at crossed
  simp only [PaperStateObservation.accumulator_actual, addressed] at crossed
  change PaperStateObservation.TablesRelatedAt sem.keyObservation (fun _ => True)
    (PaperStateObservation.accumulator sem left before).val
    (PaperStateObservation.accumulator sem right after).val
  simpa only [PaperStateObservation.accumulator_actual, addressed] using
    (PaperStateObservation.tablesSetoid sem.keyObservation _).iseqv.trans pointwise crossed

private theorem phase_related (actor : Name) (required : Key → Bool)
    (compatible : ∀ key (v w : Value), v ≈ w → (sem.keyObservation key).r v w)
    (addressed : sem.undo = Stages.undo)
    {left right : Phase Name Key Code I}
    (paired : StageSimulation.PhaseRelated Eq left right)
    (current : ∀ code stack view, right = .reloading code stack view →
      WitnessedIterator (sem.iterator actor code))
    (generated : ∀ token ∈ right.accumulator, PaperTranspositionObservation.GeneratedInverse sem token) :
    PaperStateObservation.PhaseRelated sem actor required left right := by
  cases paired with
  | inactive => exact .inactive
  | reloading view codes stacks =>
    cases codes
    exact .reloading (current _ _ _ rfl).respect (stack_related sem compatible addressed stacks generated) (fun _ _ => rfl)
  | active view stacks => exact .active (stack_related sem compatible addressed stacks generated) (fun _ _ => rfl)
  | unloading view stacks => exact .unloading (stack_related sem compatible addressed stacks generated) (fun _ _ => rfl)

/-- The endpoint's entry and remaining iterator fields are interpreted by full
global witnesses; raw equality is not silently treated as logical reflexivity. -/
private theorem state_related {left right : R}
    (compatible : ∀ key (v w : Value), v ≈ w → (sem.keyObservation key).r v w)
    (addressed : sem.undo = Stages.undo)
    (paired : StageSimulation.Related Eq left right)
    (entries : ∀ actor fiber, right actor = some fiber →
      WitnessedIterator (sem.iterator actor fiber.component.entry))
    (current : ∀ actor fiber, right actor = some fiber → ∀ code stack view,
      fiber.phase = .reloading code stack view → WitnessedIterator (sem.iterator actor code))
    (generated : AccumulatorProvenance.Accumulators (PaperTranspositionObservation.GeneratedInverse sem) right) :
    PaperStateObservation.Related sem left right := by
  have tables : TablesRelated left right := by
    intro owner key
    have fields := paired owner
    cases first : left owner <;> cases second : right owner <;>
      simp_all only [OptionRel, tableAt, Option.bind_none, Option.bind_some]
    exact fields.table key
  refine ⟨PaperStateObservation.tables_of_homogeneous (tables.projected (fun _ => True)) compatible, ?_⟩
  intro actor
  have fields := paired actor
  cases first : left actor <;> cases second : right actor <;> simp_all only [OptionRel]
  rename_i a b
  refine ⟨fields.component.requires, fields.component.provides, ?_, fields.parent, fields.retired, ?_⟩
  · change RelatedIterator (sem.iterator actor a.component.entry) (sem.iterator actor b.component.entry)
    rw [fields.component.entry]
    exact (entries actor b second).respect
  · exact phase_related sem actor a.component.requires compatible addressed fields.phase (current actor b second)
      (generated actor b second)

/-- Concrete actual activation steps, with a literal Eq54 endpoint. The source
diamond hypotheses and the semantic representation obligations are separately
visible; no assumption states swapped applicability or endpoint equivalence. -/
theorem lemma78_nondeterministic_activation (program : Code → Instruction Name Key Value Code Error)
    (compatible : ∀ key (v w : Value), v ≈ w → (sem.keyObservation key).r v w)
    (addressed : sem.undo = Stages.undo)
    {first second : Name} {firstRule secondRule : Labeled.Rule} {before middle final : R}
    (firstStep : Labeled.Step program firstRule first before middle)
    (firstActive : Transposition.Activation firstRule)
    (secondStep : Labeled.Step program secondRule second middle final)
    (secondActive : Transposition.Activation secondRule)
    (applicable : ∃ next, Labeled.Step program secondRule second before next)
    (different : first ≠ second) (reached : WellFormed.Run program (fun _ => none) before)
    (callbacks : ∀ code, Transposition.CallbackWitness program code)
    (independent : Transposition.CurrentCallbackPair program before first second)
    (representation : AccumulatorProvenance.LandingProperty program (PaperTranspositionObservation.GeneratedInverse sem))
    (entries : ∀ actor fiber, final actor = some fiber →
      WitnessedIterator (sem.iterator actor fiber.component.entry))
    (current : ∀ actor fiber, final actor = some fiber → ∀ code stack view,
      fiber.phase = .reloading code stack view → WitnessedIterator (sem.iterator actor code)) :
    ∃ swappedMiddle swappedFinal,
      Labeled.Step program secondRule second before swappedMiddle ∧
      Labeled.Step program firstRule first swappedMiddle swappedFinal ∧
      PaperStateObservation.Related sem swappedFinal final := by
  obtain ⟨swappedMiddle, swappedFinal, swappedSecond, swappedFirst, paired⟩ :=
    Transposition.activation_diamond program firstStep firstActive secondStep secondActive
      applicable different reached callbacks independent
  have finalRun := WellFormed.Run.step (WellFormed.Run.step reached firstStep.toCalculus) secondStep.toCalculus
  exact ⟨swappedMiddle, swappedFinal, swappedSecond, swappedFirst,
    state_related sem compatible addressed paired entries current
      (AccumulatorProvenance.reachable_accumulators _ program representation finalRun)⟩

private theorem setoid_eq_of_same_relation {α : Type u} (left right : Setoid α)
    (relation : left.r = right.r) : left = right := by
  cases left
  cases right
  cases relation
  rfl

/-- Lemma 78(1) for the ordinary nondeterministic activation rules, specialized
to the homogeneous value and outcome model. Each callback denotes an
Equation (30) operation and argument. The successful forward value and
outcome are exact. The actual captured inverse is completed by identity
where its partial map is undefined. Definition 44 at the full
Equation (34) table observation supplies the local exchange law, including
success and unchanged outcomes in both orders. The witness premise uses the
strong operation-respect clause from Section 3.3.2.

The homogeneous value model requires the key tests to induce its value setoid
at every key. The last premises identify the stored program and captured
inverse fields with their semantic interpretations for Equation (54). -/
theorem lemma78_nondeterministic_activation_of_coeffects
    (program : Code → Instruction Name Key Value Code Error)
    {names : Key → Type u} {args : (key : Key) → names key → Type u}
    {operations : (key : Key) → (name : names key) → args key name →
      PartialInverseObservation.Operation Value Value}
    (operationRepresentation : ∀ code key callback, (program code).action = .operate key callback →
      ∃ name argument, Transposition.RepresentsCallback (operations key name argument) callback)
    (valueObservation : ∀ key (left right : Value),
      PaperObservationEquations.KeyEquivalent (Transposition.callbackOperations names args operations) key left right ↔
        left ≈ right)
    (witnesses : ∀ key name argument, PartialInverseObservation.Witnessed
      (operations key name argument) (· ≈ ·))
    (commutativity : ∀ key, PaperObservationEquations.CommutativeKey
      (Transposition.callbackOperations names args operations)
      (PaperObservationEquations.fullTableObservation (Transposition.callbackOperations names args operations)) key)
    (compatible : ∀ key (v w : Value), v ≈ w → (sem.keyObservation key).r v w)
    (addressed : sem.undo = Stages.undo)
    {first second : Name} {firstRule secondRule : Labeled.Rule} {before middle final : R}
    (firstStep : Labeled.Step program firstRule first before middle)
    (firstActive : Transposition.Activation firstRule)
    (secondStep : Labeled.Step program secondRule second middle final)
    (secondActive : Transposition.Activation secondRule)
    (applicable : ∃ next, Labeled.Step program secondRule second before next)
    (different : first ≠ second) (reached : WellFormed.Run program (fun _ => none) before)
    (representation : AccumulatorProvenance.LandingProperty program (PaperTranspositionObservation.GeneratedInverse sem))
    (entries : ∀ actor fiber, final actor = some fiber →
      WitnessedIterator (sem.iterator actor fiber.component.entry))
    (current : ∀ actor fiber, final actor = some fiber → ∀ code stack view,
      fiber.phase = .reloading code stack view → WitnessedIterator (sem.iterator actor code)) :
    ∃ swappedMiddle swappedFinal,
      Labeled.Step program secondRule second before swappedMiddle ∧
      Labeled.Step program firstRule first swappedMiddle swappedFinal ∧
      PaperStateObservation.Related sem swappedFinal final := by
  let coeffects := Transposition.callbackOperations names args operations
  let homogeneous := PartialCoeffectIndependenceContracts.tableSetoid
    (fun _ : Key => (inferInstance : Setoid Value)) (fun _ => True)
  have sameObservation : PaperObservationEquations.fullTableObservation coeffects = homogeneous := by
    apply setoid_eq_of_same_relation
    funext left right
    apply propext
    have values : (fun key => PaperObservationEquations.KeyEquivalent coeffects key) =
        (fun _ : Key => (inferInstance : Setoid Value).r) := by
      funext key v w
      exact propext (valueObservation key v w)
    change PartialCoeffectLifting.TableRelated
      (fun key => PaperObservationEquations.KeyEquivalent coeffects key) (fun _ => True) left right ↔
      PartialCoeffectLifting.TableRelated (fun _ : Key => (inferInstance : Setoid Value).r) (fun _ => True) left right
    rw [values]
  apply lemma78_nondeterministic_activation sem program compatible addressed firstStep firstActive secondStep
    secondActive applicable different reached _ _ representation entries current
  · intro code key callback action before after inverse outcome called
    obtain ⟨name, argument, denotes⟩ := operationRepresentation code key callback action
    have witness := Transposition.callback_witness_of_partial denotes (witnesses key name argument)
    exact ⟨by simpa only [AccumulatorProvenance.callbackOperation, called] using witness.recover before,
      by simpa only [AccumulatorProvenance.callbackOperation, called] using witness.sound.respects before⟩
  · intro _ _ leftCode rightCode _ _ _ _ _ _ _ _ key left right leftAction rightAction
    obtain ⟨leftName, leftArg, leftRep⟩ := operationRepresentation leftCode key left leftAction
    obtain ⟨rightName, rightArg, rightRep⟩ := operationRepresentation rightCode key right rightAction
    have laws := commutativity key leftName rightName
    change PaperObservationEquations.IndependentOperations coeffects
      (PaperObservationEquations.fullTableObservation coeffects) key key leftName rightName at laws
    rw [sameObservation] at laws
    exact Transposition.callback_exchange_of_eq44 key leftName rightName leftArg rightArg left right leftRep rightRep laws


end
end Cordis.Results
