import Cordis.PaperTotalProgress
import Cordis.Iterators
import Cordis.Progress
import Cordis.TargetView
import Cordis.IndexedTrace
import Cordis.Frame

/-! Rule and actor labels for the total constructor interpretation. The guards
are exactly the existing Calculus.Step guards; forgetting labels and restoring
them are proved. A structural source-program witness retains BOTH labels and
is used only for program-uniform frame lemmas, not source execution equality. -/
namespace Cordis.PaperTotal
universe u
structure Model (Name Key Value Code Error : Type u) where
  program : Code → Stages.Instruction Name Key Value Code Error
  draw : Calculus.Registry Name Key Value Code (Stages.Inverse Name Key Value) Error → Name
  failed : Code → Calculus.Registry Name Key Value Code (Stages.Inverse Name Key Value) Error →
    Option (Stages.Outcome Name Value)
end Cordis.PaperTotal

namespace Cordis.PaperTotal.Labeled
open Calculus Stages
universe u
variable {Name Key Value Code Error : Type u}
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
variable [DecidableEq Name] [DecidableEq Key]

abbrev Rule := Cordis.Labeled.Rule

inductive Step (model : Model Name Key Value Code Error) : Rule → Name → R → R → Prop
  | insert (r name component parent) : Insertable r name component parent →
      Step model .insert name r (put r name (fresh component parent))
  | retire (r name) : r name ≠ none → Step model .retire name r (Calculus.retire r name)
  | remove (r name) : Removable r name → Step model .remove name r (erase r name)
  | begin (r name fiber view) : r name = some fiber → fiber.phase = .inactive →
      ErrorFree r name → Target r name view →
      Step model .begin name r (mark r name (.reloading fiber.component.entry [] view))
  | iter (r s name fiber code accumulator view inverse next) :
      r name = some fiber → fiber.phase = .reloading code accumulator view →
      Target r name view → Landing model.program model.draw model.failed name code r s inverse (some next) →
      Step model .iter name r (mark s name (.reloading next (inverse :: accumulator) view))
  | finish (r s name fiber code accumulator view inverse) :
      r name = some fiber → fiber.phase = .reloading code accumulator view →
      Target r name view → Landing model.program model.draw model.failed name code r s inverse none →
      Step model .finish name r (mark s name (.active (inverse :: accumulator) view))
  | divert (r s name fiber code accumulator view tail) :
      r name = some fiber → fiber.phase = .reloading code accumulator view →
      ¬ Target r name view →
      ((s = r ∧ tail = []) ∨ ∃ inverse next, Landing model.program model.draw model.failed name code r s inverse next ∧ tail = [inverse]) →
      Step model .divert name r (mark s name (.unloading (tail ++ accumulator) view))
  | leave (r name fiber accumulator view) :
      r name = some fiber → fiber.phase = .active accumulator view → ¬ Target r name view →
      Step model .leave name r (mark r name (.unloading accumulator view))
  | unload (r name fiber accumulator view) :
      r name = some fiber → fiber.phase = .unloading accumulator view → ¬ Relied r name →
      Step model .unload name r (mark (discharge Stages.undo accumulator r) name .inactive)

theorem Step.toCalculus {model : Model Name Key Value Code Error}
    {rule : Rule} {actor : Name} {r s : R} (h : Step model rule actor r s) :
    Calculus.Step (Landing model.program model.draw model.failed) Stages.undo r s := by
  cases h <;>
    first
    | (apply Calculus.Step.insert; assumption)
    | (apply Calculus.Step.retire; assumption)
    | (apply Calculus.Step.remove; assumption)
    | (apply Calculus.Step.begin <;> assumption)
    | (apply Calculus.Step.iter <;> assumption)
    | (apply Calculus.Step.finish <;> assumption)
    | (apply Calculus.Step.divert <;> assumption)
    | (apply Calculus.Step.leave <;> assumption)
    | (apply Calculus.Step.unload <;> assumption)

/-- The auxiliary structural program is local to THIS step. Rule and actor
labels remain exact, which permits reuse of actual target-change/frame proofs. -/
theorem Step.structural {model : Model Name Key Value Code Error}
    {rule : Rule} {actor : Name} {r s : R} (step : Step model rule actor r s) :
    ∃ structuralProgram : Code → Instruction Name Key Value Code Error,
      Cordis.Labeled.Step structuralProgram rule actor r s := by
  cases step with
  | insert r actor component parent ready => exact ⟨model.program, .insert r actor component parent ready⟩
  | retire r actor present => exact ⟨model.program, .retire r actor present⟩
  | remove r actor ready => exact ⟨model.program, .remove r actor ready⟩
  | begin r actor fiber view present phase clean target =>
    exact ⟨model.program, .begin r actor fiber view present phase clean target⟩
  | iter r middle actor fiber code stack view inverse next present phase target landed =>
    obtain ⟨localProgram, actual⟩ := landing_structural model.program model.draw model.failed landed
    exact ⟨localProgram, .iter r middle actor fiber code stack view inverse next present phase target actual⟩
  | finish r middle actor fiber code stack view inverse present phase target landed =>
    obtain ⟨localProgram, actual⟩ := landing_structural model.program model.draw model.failed landed
    exact ⟨localProgram, .finish r middle actor fiber code stack view inverse present phase target actual⟩
  | divert r middle actor fiber code stack view tail present phase changed alternative =>
    rcases alternative with abort | ⟨inverse, next, landed, tailEq⟩
    · exact ⟨model.program, .divert r middle actor fiber code stack view tail present phase changed (.inl abort)⟩
    · obtain ⟨localProgram, actual⟩ := landing_structural model.program model.draw model.failed landed
      exact ⟨localProgram, .divert r middle actor fiber code stack view tail present phase changed
        (.inr ⟨inverse, next, actual, tailEq⟩)⟩
  | leave r actor fiber stack view present phase changed =>
    exact ⟨model.program, .leave r actor fiber stack view present phase changed⟩
  | unload r actor fiber stack view present phase free =>
    exact ⟨model.program, .unload r actor fiber stack view present phase free⟩

end Cordis.PaperTotal.Labeled
