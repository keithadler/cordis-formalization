import Cordis.WellFormed

/-! Definition53's target as a partial provider view. The base calculus stores
views as total functions but observes only declared requirements; masking avoids
counting arbitrary values at undeclared keys as target changes in Theorem73.
Uniqueness is derived from reservation disjointness and table ownership, not
assumed as a selector contract. -/
namespace Cordis.TargetView
open Calculus Stages
universe u
variable {Name Key Value Code Error : Type u}
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
variable [DecidableEq Name] [DecidableEq Key]
set_option linter.unusedSectionVars false

abbrev PartialView (Name Key : Type u) := Key → Option Name

def mask (required : Key → Bool) (view : View Name Key) : PartialView Name Key :=
  fun key => if required key then some (view key) else none

/-- Two advertised bindings of one physical key must have the same owner. -/
theorem owner_unique (r : R) (owned : Safety.Owned r) (disjoint : WellFormed.Disjoint r)
    (a b : Name) (fa fb : F) (key : Key) (ha : r a = some fa) (hb : r b = some fb)
    (ba : fa.table key ≠ none) (bb : fb.table key ≠ none) : a = b := by
  by_cases same : a = b
  · exact same
  · exact False.elim (disjoint a b fa fb ha hb same key
      ⟨owned a fa key ha ba, owned b fb key hb bb⟩)

theorem masked_targets_equal (r : R) (name : Name) (fiber : F)
    (present : r name = some fiber) (owned : Safety.Owned r) (disjoint : WellFormed.Disjoint r)
    (v w : View Name Key) (left : Target r name v) (right : Target r name w) :
    mask fiber.component.requires v = mask fiber.component.requires w := by
  funext key
  by_cases required : fiber.component.requires key = true
  · simp only [Target, present] at left right
    have vl := left.2 key required
    have wl := right.2 key required
    cases hv : r (v key) with
    | none => simp [hv] at vl
    | some vf =>
      cases hw : r (w key) with
      | none => simp [hw] at wl
      | some wf =>
        simp only [hv] at vl
        simp only [hw] at wl
        have vb : vf.table key ≠ none := vl.2
        have wb : wf.table key ≠ none := wl.2
        simp [mask, required, owner_unique r owned disjoint (v key) (w key) vf wf key hv hw vb wb]
  · simp [mask, required]

/-- Target validity depends only on the view's declared coordinates. -/
theorem target_of_mask_eq (r : R) (name : Name) (fiber : F)
    (present : r name = some fiber) (v w : View Name Key)
    (same : mask fiber.component.requires v = mask fiber.component.requires w)
    (valid : Target r name v) : Target r name w := by
  simp only [Target, present] at valid ⊢
  refine ⟨valid.1, ?_⟩
  intro key required
  have names : v key = w key := by
    have coordinate := congrFun same key
    simpa [mask, required] using coordinate
  simpa [names] using valid.2 key required

end Cordis.TargetView
