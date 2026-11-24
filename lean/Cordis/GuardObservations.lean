import Cordis.StageRecovery
import Cordis.WellFormed

/-! The guard-congruence part of Lemma60. The observations retain exactly the
control facts used by rule guards and compare table values observationally.
No equivalence of arbitrary program callbacks or accumulator functions is
assumed to imply preservation of control effects. -/
namespace Cordis.GuardObservations
open Calculus Stages Iterators StageRecovery
universe u
variable {Name Key Value Code Error : Type u}
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
variable [DecidableEq Name] [DecidableEq Key] [Setoid Value]
set_option linter.unusedSectionVars false

def phaseKind : Phase Name Key Code (Inverse Name Key Value) → Nat
  | .inactive => 0
  | .reloading _ _ _ => 1
  | .active _ _ => 2
  | .unloading _ _ => 3

omit [DecidableEq Name] [DecidableEq Key] [Setoid Value] in
theorem phase_inactive_iff {a b : Phase Name Key Code (Inverse Name Key Value)}
    (same : phaseKind a = phaseKind b) : a = .inactive ↔ b = .inactive := by
  cases a <;> cases b <;> simp_all [phaseKind]

omit [DecidableEq Name] [DecidableEq Key] [Setoid Value] in
theorem phase_available_iff {a b : Phase Name Key Code (Inverse Name Key Value)}
    (same : phaseKind a = phaseKind b) : a.available ↔ b.available := by
  cases a <;> cases b <;> simp_all [phaseKind, Phase.available]

structure ControlFields (f g : F) : Prop where
  requires : f.component.requires = g.component.requires
  provides : f.component.provides = g.component.provides
  parent : f.parent = g.parent
  retired : f.retired = g.retired
  phase : phaseKind f.phase = phaseKind g.phase
  committed : f.phase.committed = g.phase.committed

structure FiberRelated (f g : F) : Prop extends ControlFields f g where
  table : ∀ k, OptionRel (fun v w : Value => v ≈ w) (f.table k) (g.table k)

def Related (r s : R) : Prop := ∀ n, OptionRel FiberRelated (r n) (s n)

theorem fiber_symm {f g : F} (h : FiberRelated f g) : FiberRelated g f := by
  refine ⟨⟨h.requires.symm, h.provides.symm, h.parent.symm, h.retired.symm,
    h.phase.symm, h.committed.symm⟩, ?_⟩
  intro k
  exact @OptionRel.mono Value Value (fun x y => y ≈ x) (fun x y => x ≈ y)
    (fun _ _ related => Setoid.symm related) _ _ (OptionRel.symm (h.table k))

theorem related_symm {r s : R} (h : Related r s) : Related s r := by
  intro n
  have observed := h n
  cases hr : r n <;> cases hs : s n <;> simp_all [OptionRel]
  exact fiber_symm observed

theorem none_iff {r s : R} (h : Related r s) (n : Name) : r n = none ↔ s n = none := by
  have observed := h n
  cases hr : r n <;> cases hs : s n <;> simp_all [OptionRel]

theorem present_related {r s : R} (h : Related r s) (n : Name) (f : F) (present : r n = some f) :
    ∃ g, s n = some g ∧ FiberRelated f g := by
  have observed := h n
  rw [present] at observed
  cases found : s n with
  | none => simp [found, OptionRel] at observed
  | some g => exact ⟨g, rfl, by simpa [found, OptionRel] using observed⟩

theorem table_none_iff {f g : F} (h : FiberRelated f g) (k : Key) : f.table k = none ↔ g.table k = none := by
  have observed := h.table k
  cases hf : f.table k <;> cases hg : g.table k <;> simp_all [OptionRel]

theorem target_forward {r s : R} (h : Related r s) (n : Name) (view : View Name Key)
    (target : Target r n view) : Target s n view := by
  cases present : r n with
  | none => simp [Target, present] at target
  | some f =>
    obtain ⟨g, found, fg⟩ := present_related h n f present
    simp only [Target, present] at target
    simp only [Target, found]
    refine ⟨fg.retired ▸ target.1, ?_⟩
    intro k required
    have ready := target.2 k (by simpa [fg.requires] using required)
    cases provider : r (view k) with
    | none => simp [provider] at ready
    | some p =>
      obtain ⟨q, counterpart, pq⟩ := present_related h (view k) p provider
      simp only [provider] at ready
      simp only [counterpart]
      exact ⟨(phase_available_iff pq.phase).mp ready.1,
        fun absent => ready.2 ((table_none_iff pq k).mpr absent)⟩

theorem target_iff {r s : R} (h : Related r s) (n : Name) (view : View Name Key) :
    Target r n view ↔ Target s n view :=
  ⟨target_forward h n view, target_forward (related_symm h) n view⟩

theorem relied_forward {r s : R} (h : Related r s) (n : Name) (relied : Relied r n) : Relied s n := by
  obtain ⟨consumer, different, depends⟩ := relied
  refine ⟨consumer, different, ?_⟩
  cases present : r consumer with
  | none => simp [present] at depends
  | some f =>
    obtain ⟨g, found, fg⟩ := present_related h consumer f present
    simp only [present] at depends
    simp only [found, ← fg.committed, ← fg.requires]
    exact depends

theorem relied_iff {r s : R} (h : Related r s) (n : Name) : Relied r n ↔ Relied s n :=
  ⟨relied_forward h n, relied_forward (related_symm h) n⟩

theorem insertable_forward {r s : R} (h : Related r s) (n : Name) (component : Component Key Code)
    (parent : Option Name) (ready : Insertable r n component parent) : Insertable s n component parent := by
  refine ⟨(none_iff h n).mp ready.1, ?_, ?_⟩
  · intro p hp absent
    exact ready.2.1 p hp ((none_iff h p).mpr absent)
  · intro other key
    cases found : s other with
    | none => trivial
    | some g =>
      obtain ⟨f, present, gf⟩ := present_related (related_symm h) other g found
      have separate := ready.2.2 other key
      simpa [present, gf.provides] using separate

theorem insertable_iff {r s : R} (h : Related r s) (n : Name) (component : Component Key Code)
    (parent : Option Name) : Insertable r n component parent ↔ Insertable s n component parent :=
  ⟨insertable_forward h n component parent, insertable_forward (related_symm h) n component parent⟩

theorem removable_forward {r s : R} (h : Related r s) (n : Name) (ready : Removable r n) : Removable s n := by
  cases present : r n with
  | none => simp [Removable, present] at ready
  | some f =>
    obtain ⟨g, found, fg⟩ := present_related h n f present
    simp only [Removable, present] at ready
    simp only [Removable, found]
    refine ⟨fg.retired ▸ ready.1, (phase_inactive_iff fg.phase).mp ready.2.1,
      fun k => (table_none_iff fg k).mp (ready.2.2.1 k), ?_⟩
    intro child
    cases counterpart : s child with
    | none => trivial
    | some q =>
      obtain ⟨p, old, qp⟩ := present_related (related_symm h) child q counterpart
      have noChild := ready.2.2.2 child
      simpa [old, qp.parent] using noChild

theorem removable_iff {r s : R} (h : Related r s) (n : Name) : Removable r n ↔ Removable s n :=
  ⟨removable_forward h n, removable_forward (related_symm h) n⟩

theorem errorFree_iff {r s : R} (h : Related r s) (n : Name) : ErrorFree r n ↔ ErrorFree s n := by
  exact not_congr (none_iff h n)

def LocatedRelated (a b : Name × Value) : Prop := a.1 = b.1 ∧ a.2 ≈ b.2

theorem owner_pair_related (owner : Name) {a b : Option Value}
    (related : OptionRel (fun v w : Value => v ≈ w) a b) :
    OptionRel LocatedRelated (a.map (fun v => (owner, v))) (b.map (fun v => (owner, v))) := by
  cases a <;> cases b <;> simp_all [OptionRel, LocatedRelated]

theorem bindingOwner_related {r s : R} (h : Related r s) (n : Name) (key : Key) :
    Stages.bindingOwner r n key = Stages.bindingOwner s n key := by
  cases present : r n with
  | none => simp [Stages.bindingOwner, present, (none_iff h n).mp present]
  | some f =>
    obtain ⟨g, found, fg⟩ := present_related h n f present
    simp [Stages.bindingOwner, present, found, fg.provides, fg.requires, fg.committed]

/-- The same retained owner is resolved, and its current values are related.
Missing/unauthorized accesses match too, not merely successful reads. -/
theorem location_related {r s : R} (h : Related r s) (n : Name) (key : Key) :
    OptionRel LocatedRelated (location r n key) (location s n key) := by
  simp only [location, ← bindingOwner_related h n key]
  cases Stages.bindingOwner r n key with
  | none => trivial
  | some owner =>
    cases present : r owner with
    | none => simp [present, (none_iff h owner).mp present, OptionRel]
    | some f =>
      obtain ⟨g, found, fg⟩ := present_related h owner f present
      simpa [present, found] using owner_pair_related owner (fg.table key)

theorem location_success {r s : R} (h : Related r s) (n owner : Name) (key : Key) (value : Value)
    (located : location r n key = some (owner, value)) :
    ∃ other, location s n key = some (owner, other) ∧ value ≈ other := by
  have related := location_related h n key
  rw [located] at related
  cases found : location s n key with
  | none => simp [found, OptionRel] at related
  | some pair =>
    obtain ⟨otherOwner, other⟩ := pair
    have fields : owner = otherOwner ∧ value ≈ other := by simpa [found, OptionRel, LocatedRelated] using related
    obtain ⟨same, observed⟩ := fields
    subst otherOwner
    exact ⟨other, rfl, observed⟩

end Cordis.GuardObservations
