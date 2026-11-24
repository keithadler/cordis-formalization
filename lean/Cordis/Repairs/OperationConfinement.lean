import Cordis.Repairs.BoundOperation
import Cordis.Repairs.ProvisionConfinement

/-! Definition 55 for the native scoped operation. The route is fixed by the
interface. Within that domain, running both the forward and the returned
inverse depends only on the permitted tables. -/
namespace Cordis.Repairs.BoundOperation
open TypedRegistry Iterators PartialInverseObservation
open PaperEffectEquations (CoeffectOperations)
universe u
variable {Name Key Code : Type u} {V : Key → Type u}
variable [DecidableEq Name] [DecidableEq Key]
variable {ops : CoeffectOperations V} {actor owner : Name}
variable {acting providing : Calculus.Component Key Code} {key : Key}
local notation "G" => Gamma ops actor acting owner providing key

omit [DecidableEq Name] in
/-- A successful route has a declared key. A foreign slot must be in the
actor's dependency interface. -/
theorem route_authorized (input : G) :
    (acting.provides key = true ∨ acting.requires key = true) ∧
      (owner = actor ∨ acting.requires key = true) := by
  obtain ⟨fiber, present, component⟩ := input.property.1.2
  have route := input.property.2.2
  by_cases provided : acting.provides key = true
  · have same : actor = owner := by simpa [bindingOwner, present, component, provided] using route
    exact ⟨.inl provided, .inl same.symm⟩
  · by_cases required : acting.requires key = true
    · exact ⟨.inr required, .inr required⟩
    · simp [bindingOwner, present, component, provided, required] at route

def OperationReadEqual (left right : G) : Prop :=
  ∀ name query, name = actor ∨ acting.requires query = true →
    tableAt left.val name query = tableAt right.val name query

theorem setSlot_reads (provided : providing.provides key = true)
    (value : Option (V key)) {left right : G} (related : OperationReadEqual left right) :
    OperationReadEqual (setSlot provided value left) (setSlot provided value right) := by
  intro name query selected
  by_cases sameKey : key = query
  · subst query
    by_cases sameOwner : name = owner
    · subst name
      rw [slot_self, slot_self]
    · rw [show tableAt (setSlot provided value left).val name key = tableAt left.val name key from
          CompatibleProvision.slot_foreign key provided value (providerState left) name sameOwner key,
        show tableAt (setSlot provided value right).val name key = tableAt right.val name key from
          CompatibleProvision.slot_foreign key provided value (providerState right) name sameOwner key]
      exact related name key selected
  · rw [show tableAt (setSlot provided value left).val name query = tableAt left.val name query from
          CompatibleProvision.slot_other key query sameKey provided value (providerState left) name,
        show tableAt (setSlot provided value right).val name query = tableAt right.val name query from
          CompatibleProvision.slot_other key query sameKey provided value (providerState right) name]
    exact related name query selected

theorem inverse_reads (provided : providing.provides key = true)
    (inverse : V key → Option (V key)) :
    MapRelated (OperationReadEqual (ops := ops) (actor := actor) (acting := acting) (owner := owner))
      (liftMap provided inverse) (liftMap provided inverse) := by
  intro left right related
  have same := related owner key (route_authorized left).2
  cases binding : tableAt left.val owner key with
  | none =>
    have other := same.symm.trans binding
    simp [liftMap, binding, other, OptionRel]
  | some value =>
    have other := same.symm.trans binding
    cases recovered : inverse value with
    | none => simp [liftMap, binding, other, recovered, OptionRel]
    | some changed =>
      simpa [liftMap, binding, other, recovered, OptionRel] using
        setSlot_reads provided (some changed) related

/-- With exactly equal permitted input tables, the two calls select the
same scalar result and saved inverse, with their permitted output tables equal. -/
theorem operation_reads {Outcome : Type u} (provided : providing.provides key = true)
    (operation : Operation (V key) Outcome) (left right : G) (related : OperationReadEqual left right) :
    OptionRel (fun a b => OperationReadEqual a.1 b.1 ∧ a.2.1 = b.2.1 ∧ a.2.2 = b.2.2)
      ((liftOperation provided operation).run left) ((liftOperation provided operation).run right) := by
  have same := related owner key (route_authorized left).2
  cases binding : tableAt left.val owner key with
  | none =>
    have other := same.symm.trans binding
    simp [liftOperation, binding, other, OptionRel]
  | some value =>
    have other := same.symm.trans binding
    cases applied : operation.run value with
    | none => simp [liftOperation, binding, other, applied, OptionRel]
    | some result =>
      obtain ⟨changed, inverse, outcome⟩ := result
      simpa [liftOperation, binding, other, applied, OptionRel] using
        setSlot_reads provided (some changed) related

theorem setSlot_domain (provided : providing.provides key = true) (value : Option (V key))
    (input : G) (name : Name) :
    (setSlot provided value input).val name = none ↔ input.val name = none :=
  CompatibleProvision.setSlot_domain key provided value (providerState input) name

/-- Apart from the selected slot, all table coordinates remain unchanged.
If that slot is foreign, it belongs to a declared dependency. -/
theorem setSlot_changes_only_declared (provided : providing.provides key = true) (value : Option (V key))
    (input : G) (name : Name) (query : Key)
    (outside : name ≠ owner ∨ query ≠ key) :
    tableAt (setSlot provided value input).val name query = tableAt input.val name query := by
  rcases outside with different | different
  · exact CompatibleProvision.slot_foreign key provided value (providerState input) name different query
  · exact CompatibleProvision.slot_other key query (Ne.symm different) provided value (providerState input) name

end Cordis.Repairs.BoundOperation
