import Cordis.Ordering
import Cordis.Safety

/-! Direct dependencies and quiescence as used by Lemmas 75, 77 and 79. -/
namespace Cordis.Progress
open Calculus Stages Ordering
universe u
variable {Name Key Value Code Error : Type u}
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
variable [DecidableEq Name] [DecidableEq Key]
set_option linter.unusedSectionVars false

/-- Definition 72, with the consumer first for well-founded descent to consumers. -/
def Depends (r : R) (consumer provider : Name) : Prop :=
  ∃ c p key, r consumer = some c ∧ r provider = some p ∧
    c.component.requires key = true ∧ p.component.provides key = true

def Quiet (r : R) : Prop :=
  ∀ name fiber, r name = some fiber →
    match fiber.phase with
    | .inactive => ∀ view, ¬ Target r name view
    | .active _ view => Target r name view
    | _ => False

end Cordis.Progress
