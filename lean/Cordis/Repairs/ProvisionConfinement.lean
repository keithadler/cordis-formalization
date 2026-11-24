import Cordis.Repairs.CompatibleProvision

/-! Definition 55's read/write discipline for the repaired provision and its
actual restriction inverse. The domain fixes a component, but observing or
executing the primitive does not inspect lifecycle state or foreign control. -/
namespace Cordis.Repairs.CompatibleProvision
open TypedRegistry Iterators PartialInverseObservation
open PaperEffectEquations (CoeffectOperations)
universe u
variable {Name Key Code : Type u} {V : Key → Type u}
variable [DecidableEq Name] [DecidableEq Key]
variable {ops : CoeffectOperations V} {actor : Name} {component : Calculus.Component Key Code}

def ReadEqual (left right : Gamma ops actor component) : Prop :=
  ∀ owner key, owner = actor ∨ component.requires key = true →
    tableAt left.val owner key = tableAt right.val owner key

theorem slot_foreign (key : Key) (provided : component.provides key = true)
    (value : Option (V key)) (state : Gamma ops actor component) (owner : Name)
    (different : owner ≠ actor) (other : Key) :
    tableAt (setSlot key provided value state).val owner other = tableAt state.val owner other := by
  simp [setSlot_value, tableAt, write, TypedRegistry.modify, different]

theorem setSlot_domain (key : Key) (provided : component.provides key = true)
    (value : Option (V key)) (state : Gamma ops actor component) (owner : Name) :
    (setSlot key provided value state).val owner = none ↔ state.val owner = none := by
  by_cases same : owner = actor
  · subst owner
    obtain ⟨fiber, present, _⟩ := state.property.2
    simp [setSlot_value, write, TypedRegistry.modify, present]
  · simp [setSlot_value, write, TypedRegistry.modify, same]

theorem setSlot_reads (key : Key) (provided : component.provides key = true)
    (value : Option (V key)) {left right : Gamma ops actor component} (same : ReadEqual left right) :
    ReadEqual (setSlot key provided value left) (setSlot key provided value right) := by
  intro owner other selected
  by_cases atActor : owner = actor
  · subst owner
    by_cases atKey : key = other
    · subst other; rw [slot_self, slot_self]
    · rw [slot_other key other atKey, slot_other key other atKey]
      exact same actor other selected
  · rw [slot_foreign key provided value left owner atActor,
      slot_foreign key provided value right owner atActor]
    exact same owner other selected

def forward (key : Key) (provided : component.provides key = true) (value : V key)
    (state : Gamma ops actor component) : Option (Gamma ops actor component) :=
  ((provision key provided value).run state).map Prod.fst

/-- Both success/failure and the observable table outputs depend only on the
tables permitted by Definition 55(2). -/
theorem provision_reads (key : Key) (provided : component.provides key = true) (value : V key) :
    MapRelated (ReadEqual (ops := ops) (actor := actor)) (forward key provided value) (forward key provided value) := by
  intro left right related
  have same := related actor key (.inl rfl)
  cases bound : tableAt left.val actor key with
  | none =>
    have other := same.symm.trans bound
    simpa only [forward, provision, bound, other, Option.map_some, OptionRel] using
      setSlot_reads key provided (some value) related
  | some old =>
    have other := same.symm.trans bound
    simp [forward, provision, bound, other, OptionRel]

theorem restriction_reads (key : Key) (provided : component.provides key = true) :
    MapRelated (ReadEqual (ops := ops) (actor := actor)) (restrict key provided) (restrict key provided) := by
  intro left right related
  have same := related actor key (.inl rfl)
  cases bound : tableAt left.val actor key with
  | none =>
    have other := same.symm.trans bound
    simp [restrict, bound, other, OptionRel]
  | some old =>
    have other := same.symm.trans bound
    simpa only [restrict, bound, other, OptionRel] using setSlot_reads key provided none related

end Cordis.Repairs.CompatibleProvision
