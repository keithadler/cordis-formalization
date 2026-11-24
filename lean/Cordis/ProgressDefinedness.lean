import Cordis.FiniteOrder

/-! Fresh names for Definition 52. A finite registry over natural-number
names always has a name outside its domain. -/
namespace Cordis.ProgressDefinedness
open Calculus Stages Ordering Progress
universe u
variable {Name Key Value Code Error : Type u}
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
variable [DecidableEq Name] [DecidableEq Key]
set_option linter.unusedSectionVars false

/-- A finite covering list supplies an unused natural identity. The list may
include all earlier incarnations, so allocation need not recycle removed names. -/
theorem nat_fresh_of_finite {K V C E : Type}
    (r : Registry Nat K V C (Inverse Nat K V) E) (names : List Nat)
    (finite : ∀ name fiber, r name = some fiber → name ∈ names) :
    ∃ child, r child = none := by
  let child := names.max?.getD 0 + 1
  refine ⟨child, ?_⟩
  cases present : r child with
  | none => rfl
  | some fiber =>
    have bound := List.le_max?_getD_of_mem (k := 0) (finite child fiber present)
    omega

end Cordis.ProgressDefinedness
