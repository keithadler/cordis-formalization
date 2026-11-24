import Cordis.Repairs.AllocationBoundary

/-!
The local allocation repair uses explicit input and output domains. Native
Insertable is the input predicate; a present child with the captured component
and parent is the output predicate. Observation remains the same table-only
relation across both domains. The captured retirement is closed on the output
domain and recovers the input's observation, not its registry domain.

These are primitive laws, not yet a replacement for the paper's recursive
iterator semantics. Composition, varying name draws, and name reuse still
require their own transport/provenance arguments.
-/
namespace Cordis.Repairs.AllocationDomains
open TypedRegistry
open PaperEffectEquations (CoeffectOperations)
open TypedStateObservation (TablesRelatedAt)
universe u
variable {Name Key Code : Type u} {V : Key → Type u}
variable [DecidableEq Name] [DecidableEq Key]
variable (ops : CoeffectOperations V) (actor newborn : Name)
variable (acting child : Calculus.Component Key Code)
local notation "R" => Registry Name V Code

def Before := {state : R // CompatibleProvision.Compatible ops actor acting state ∧
  Insertable state newborn child (some actor)}
def After := {state : R // CompatibleProvision.Compatible ops actor acting state ∧
  ∃ fiber, state newborn = some fiber ∧ fiber.component = child ∧ fiber.parent = some actor}

variable {ops actor newborn acting child}

omit [DecidableEq Name] in
theorem distinct (state : Before ops actor newborn acting child) : actor ≠ newborn := by
  intro same
  obtain ⟨fiber, present, _⟩ := state.property.1.2
  have absent := state.property.2.1
  have compared := congrArg state.val same
  rw [present, absent] at compared
  cases compared

def allocate (state : Before ops actor newborn acting child) : After ops actor newborn acting child := by
  refine ⟨put state.val newborn (fresh child (some actor)), ?_, ?_⟩
  · apply CompatibleProvision.step_compatible
      (Step.insert (program := fun _ => ⟨.unit, fun _ => none⟩) state.val newborn child (some actor)
        state.property.2) state.property.1
    obtain ⟨fiber, present, _⟩ := state.property.1.2
    simp [put, distinct state, present]
  · exact ⟨fresh child (some actor), by simp [put], rfl, rfl⟩

def inverse (state : After ops actor newborn acting child) : After ops actor newborn acting child := by
  refine ⟨retire state.val newborn, ?_⟩
  obtain ⟨fiber, present, component, parent⟩ := state.property.2
  have step : Step (ops := ops) (fun _ => ⟨.unit, fun _ => none⟩) .retire newborn
      state.val (retire state.val newborn) := .retire _ _ (by simp [present])
  constructor
  · apply CompatibleProvision.step_compatible step state.property.1
    obtain ⟨old, found, _⟩ := state.property.1.2
    by_cases same : actor = newborn
    · subst actor; simp [retire, TypedRegistry.modify, present]
    · simp [retire, TypedRegistry.modify, same, found]
  · exact ⟨{fiber with retired := true}, by simp [retire, TypedRegistry.modify, present], component, parent⟩

@[simp] theorem allocate_value (state : Before ops actor newborn acting child) :
    (allocate state).val = put state.val newborn (fresh child (some actor)) := rfl
@[simp] theorem inverse_value (state : After ops actor newborn acting child) :
    (inverse state).val = retire state.val newborn := rfl

theorem allocate_tables (state : Before ops actor newborn acting child) (name : Name) (key : Key) :
    tableAt (allocate state).val name key = tableAt state.val name key := by
  by_cases same : name = newborn
  · subst name
    simp [tableAt, allocate_value, put, fresh, state.property.2.1]
  · simp [tableAt, allocate_value, put, same]

theorem inverse_tables (state : After ops actor newborn acting child) (name : Name) (key : Key) :
    tableAt (inverse state).val name key = tableAt state.val name key := by
  by_cases same : name = newborn
  · subst name
    obtain ⟨fiber, present, _⟩ := state.property.2
    simp [inverse_value, tableAt, retire, TypedRegistry.modify, present]
  · simp [inverse_value, tableAt, retire, TypedRegistry.modify, same]

omit [DecidableEq Name] [DecidableEq Key] in
theorem tables_transfer (observe : ∀ key, Setoid (V key)) (keys : Key → Prop)
    {left right changedLeft changedRight : R}
    (leftTables : ∀ name key, tableAt changedLeft name key = tableAt left name key)
    (rightTables : ∀ name key, tableAt changedRight name key = tableAt right name key)
    (related : TablesRelatedAt observe keys left right) :
    TablesRelatedAt observe keys changedLeft changedRight := by
  intro key selected
  constructor
  · intro name value found
    rw [leftTables] at found
    obtain ⟨other, result, bound, values⟩ := (related key selected).1 name value found
    exact ⟨other, result, (rightTables other key).trans bound, values⟩
  · intro name value found
    rw [rightTables] at found
    obtain ⟨other, result, bound, values⟩ := (related key selected).2 name value found
    exact ⟨other, result, (leftTables other key).trans bound, values⟩

theorem allocate_respects (observe : ∀ key, Setoid (V key)) (keys : Key → Prop)
    {left right : Before ops actor newborn acting child}
    (related : TablesRelatedAt observe keys left.val right.val) :
    TablesRelatedAt observe keys (allocate left).val (allocate right).val :=
  tables_transfer observe keys (allocate_tables left) (allocate_tables right) related

/-- This compares the captured inverse on every related output-domain probe,
not only the particular state at which it was first yielded. -/
theorem inverse_respects (observe : ∀ key, Setoid (V key)) (keys : Key → Prop)
    {left right : After ops actor newborn acting child}
    (related : TablesRelatedAt observe keys left.val right.val) :
    TablesRelatedAt observe keys (inverse left).val (inverse right).val :=
  tables_transfer observe keys (inverse_tables left) (inverse_tables right) related

theorem observational_recovery (observe : ∀ key, Setoid (V key)) (keys : Key → Prop)
    (state : Before ops actor newborn acting child) :
    TablesRelatedAt observe keys (inverse (allocate state)).val state.val := by
  apply tables_transfer observe keys
    (fun name key => (inverse_tables (allocate state) name key).trans (allocate_tables state name key))
    (fun _ _ => rfl)
  intro key _
  exact ⟨fun name value found => ⟨name, value, found, (observe key).refl value⟩,
    fun name value found => ⟨name, value, found, (observe key).refl value⟩⟩

theorem native_landing (program : Code → Instruction Name ops Code) (code : Code)
    (action : (program code).action = .instantiate child)
    (state : Before ops actor newborn acting child) :
    Land program actor code state.val (allocate state).val (.retire newborn)
      ((program code).next (.child newborn)) :=
  .instantiate state.val actor code child newborn action state.property.2

theorem native_inverse (state : After ops actor newborn acting child) :
    (inverse state).val = undo (.retire newborn) state.val := inverse_value state

/-- Recovery intentionally keeps the retired empty record. Claiming literal
equality with the input would contradict the native retirement semantics. -/
theorem recovery_not_registry_equality (state : Before ops actor newborn acting child) :
    (inverse (allocate state)).val ≠ state.val := by
  intro equal
  have atChild := congrFun equal newborn
  have absent := state.property.2.1
  simp [inverse_value, allocate_value, retire, TypedRegistry.modify, put, absent] at atChild

namespace Example
open AllocationBoundary
def input : Before operations 0 2 parent AllocationBoundary.child :=
  ⟨cleared, clearInput.property, allocation_enabled⟩
theorem blocked_excluded : ¬ ∃ admitted : Before operations 0 2 parent AllocationBoundary.child,
    admitted.val = blocked := by
  rintro ⟨admitted, same⟩
  exact allocation_blocked 2 (same ▸ admitted.property.2)
theorem child_present : (allocate input).val 2 = some (fresh AllocationBoundary.child (some 0)) := rfl
theorem inverse_retires_child : (inverse (allocate input)).val 2 =
    some { (fresh AllocationBoundary.child (some 0) : Row) with retired := true } := rfl
theorem recovers_tables : TablesRelatedAt observation (fun _ => True)
    (inverse (allocate input)).val input.val := observational_recovery observation (fun _ => True) input
end Example

end Cordis.Repairs.AllocationDomains
