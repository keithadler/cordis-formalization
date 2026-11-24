import Cordis.PaperTotalInvariants
import Cordis.FiniteOrder

/-! The no-deadlock argument of Theorem73 at a total triple evaluator.
The existing Calculus.Step constructors are reused, not replaced by an assumed
transition relation. The generic theorem obtains every reloading landing by
evaluating the total function. Its constructor interpretation then derives all
structural/support hypotheses from a real empty-origin prefix.

No source safety or Landable premise occurs. Conversely, this result does not
identify failed-head completions with source transitions, prove a Definition40
length bound, or settle the original theorem's unspecified completion domain.
-/
namespace Cordis.PaperTotal
noncomputable section
open Calculus Stages Ordering Progress
universe u
variable {Name Key Value Code Error : Type u}
variable [DecidableEq Name] [DecidableEq Key]
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
local notation "I" => Inverse Name Key Value
local notation "L" => Calculus.Landing (Name := Name) (Key := Key) (Value := Value)
  (Code := Code) (Undo := I) (Error := Error)
set_option linter.unusedSectionVars false

end
end Cordis.PaperTotal
