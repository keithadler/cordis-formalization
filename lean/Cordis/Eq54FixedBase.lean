import Cordis.RenamingLiteral

/-! Definition58 Eq54 with the fixed Definition33/51 base named by Definition34.
Function fields are compared by the full semantic logical relation over Gamma:
entry/remaining iterators recursively, and accumulators as whole state maps.
No code equality, list-shape equality, per-owner table surrogate, or literal
child-payload condition is substituted for that stated relation.

This is one precise reading of the paper. Rebasing the arrow's input and output
relations recursively to Eq54 itself is a different construction; it is not
silently used here. -/
namespace Cordis.Eq54FixedBase
noncomputable section
open Calculus Stages Effects Iterators RenamingLiteral

/-- Interpreting each actual inverse on all admissible finite rooted registries.
The nonexistent key constructors cannot arise when the key type is Empty. -/
def undoGamma : Inverse Name Empty Unit → Gamma → Gamma
  | .unit, state => state
  | .retire child, state => retireGamma child state
  | .restrict _ key, _ => nomatch key
  | .operate _ key _, _ => nomatch key

theorem undoGamma_actual (inverse : Inverse Name Empty Unit) (state : Gamma) :
    (undoGamma inverse state).val = Stages.undo inverse state.val := by
  cases inverse with
  | unit => rfl
  | retire => rfl
  | restrict _ key => exact nomatch key
  | operate _ key _ => exact nomatch key

/-- Every primitive here is terminal. Their global Definition37 witnesses do
not erase the control actions: the forward/inverse maps still change Gamma. -/
def childComponent : Component Empty Code := ⟨(fun _ => false), (fun _ => false), false⟩
def meaning (actor : Name) (draw : Gamma → Name) (code : Code) : Iterator Gamma :=
  if code then drawnBirthIterator actor draw childComponent else embed Effects.identity

end
end Cordis.Eq54FixedBase
