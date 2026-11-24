import Cordis.ResolutionIntervals
import Cordis.RenamingLiteral
import Cordis.Orchestration

/-! Theorem71's unconditional closure clause, read on the finite sequences
Definition58 explicitly admits. A genuine empty-origin episode can end just
after a landing Divert, with its unit inverse captured and not yet unloaded.
The sequence has no observed closing boundary. All components have the global
Definition37 unit witness over the full finite-rooted registry domain; this
example uses neither an absent-owner extension nor any Eq54 interpretation.

This does not dispute the proved initial reloading interval/target/exit-rule
clauses, or terminal recovery WHEN an Unload closes the episode. The missing
hypothesis is closure (or an execution-extension/maximality condition sufficient
to imply closure), not another local transition guard. -/
namespace Cordis.ResolutionClosureBoundary
noncomputable section
open Calculus Stages Indexed ResolutionIntervals RenamingLiteral

def component : Component Empty Code := ⟨fun _ => false, fun _ => false, false⟩
def program (_ : Code) : Instruction Name Empty Unit Code Empty :=
  { action := .unit, next := fun _ => none }
def view : View Name Empty := fun key => nomatch key

end
end Cordis.ResolutionClosureBoundary
