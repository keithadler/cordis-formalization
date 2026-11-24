import Cordis.TargetView
import Cordis.Iterators
import Cordis.Progress
import Cordis.IndexedTrace
import Cordis.Frame
import Cordis.OrderingIntervals

/-! Theorem71's control interval on actual labeled rules. Reloading occupies
an initial interval of each installed episode; it cannot restart without a new
Begin, which would require an intervening inactive state. -/
namespace Cordis.ResolutionIntervals
open Calculus Stages
universe u
variable {Name Key Value Code Error : Type u}
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
variable [DecidableEq Name] [DecidableEq Key]
set_option linter.unusedSectionVars false

def IsReloading : Phase Name Key Code (Inverse Name Key Value) → Prop
  | .reloading _ _ _ => True
  | _ => False

def Reloading (r : R) (name : Name) : Prop :=
  ∃ fiber, r name = some fiber ∧ IsReloading fiber.phase

theorem reloading_known (r : R) (name : Name) (fiber : F) (present : r name = some fiber) :
    Reloading r name ↔ IsReloading fiber.phase := by
  constructor
  · rintro ⟨entry, found, reload⟩
    have same : entry = fiber := Option.some.inj (found.symm.trans present)
    simpa [same] using reload
  · exact fun reload => ⟨fiber, present, reload⟩

end Cordis.ResolutionIntervals
