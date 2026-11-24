import Cordis.Safety
import Cordis.Ordering

/-!
The provenance convention stated after Definition74 (arXiv:2608.25512v1 p51):
externally inserted fibers have root parent; non-root fibers come from a parent's
activation (Definition 52, p. 35). The nested instantiation rule uses the
O-Insert primitive with the acting fiber as parent.
This relation distinguishes those two uses. It does not assume support, recovery,
termination, or confluence as transition premises.
-/
namespace Cordis.Orchestration
open Calculus Stages
universe u
variable {Name Key Value Code Error : Type u}
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
variable [DecidableEq Name] [DecidableEq Key]

/-- External O-Insert has root parent. Child insertion occurs only inside Land,
whose instantiate constructor fixes the actor as parent and yields its retirement.
The remaining external rules and all six lifecycle rules have unchanged premises. -/
inductive Step (program : Code → Instruction Name Key Value Code Error) : R → R → Prop
  | insert (r name component) : Insertable r name component none →
      Step program r (put r name (fresh component none))
  | retire (r name) : r name ≠ none → Step program r (Calculus.retire r name)
  | remove (r name) : Removable r name → Step program r (erase r name)
  | begin (r name fiber view) : r name = some fiber → fiber.phase = .inactive →
      ErrorFree r name → Target r name view →
      Step program r (mark r name (.reloading fiber.component.entry [] view))
  | iter (r s name fiber code accumulator view inverse next) :
      r name = some fiber → fiber.phase = .reloading code accumulator view →
      Target r name view → Land program name code r s inverse (some next) →
      Step program r (mark s name (.reloading next (inverse :: accumulator) view))
  | finish (r s name fiber code accumulator view inverse) :
      r name = some fiber → fiber.phase = .reloading code accumulator view →
      Target r name view → Land program name code r s inverse none →
      Step program r (mark s name (.active (inverse :: accumulator) view))
  | divert (r s name fiber code accumulator view tail) :
      r name = some fiber → fiber.phase = .reloading code accumulator view →
      ¬ Target r name view →
      ((s = r ∧ tail = []) ∨
        ∃ inverse next, Land program name code r s inverse next ∧ tail = [inverse]) →
      Step program r (mark s name (.unloading (tail ++ accumulator) view))
  | leave (r name fiber accumulator view) :
      r name = some fiber → fiber.phase = .active accumulator view → ¬ Target r name view →
      Step program r (mark r name (.unloading accumulator view))
  | unload (r name fiber accumulator view) :
      r name = some fiber → fiber.phase = .unloading accumulator view → ¬ Relied r name →
      Step program r (mark (discharge Stages.undo accumulator r) name .inactive)

/-- An explicit restriction of the existing calculus, not a replacement interpreter. -/
theorem Step.toCalculus {program : Code → Instruction Name Key Value Code Error}
    {r s : R} (h : Step program r s) : Calculus.Step (Land program) Stages.undo r s := by
  cases h with
  | insert name component ready => exact .insert r name component none ready
  | retire name present => exact .retire r name present
  | remove name ready => exact .remove r name ready
  | begin name fiber view present inactive errorFree target =>
    exact .begin r name fiber view present inactive errorFree target
  | iter s name fiber code accumulator view inverse next present reloading target land =>
    exact .iter r s name fiber code accumulator view inverse next present reloading target land
  | finish s name fiber code accumulator view inverse present reloading target land =>
    exact .finish r s name fiber code accumulator view inverse present reloading target land
  | divert s name fiber code accumulator view tail present reloading target land =>
    exact .divert r s name fiber code accumulator view tail present reloading target land
  | leave name fiber accumulator view present active target =>
    exact .leave r name fiber accumulator view present active target
  | unload name fiber accumulator view present unloading unrelied =>
    exact .unload r name fiber accumulator view present unloading unrelied

inductive Run (program : Code → Instruction Name Key Value Code Error) : R → R → Prop
  | refl (r) : Run program r r
  | step {r s t} : Run program r s → Step program s t → Run program r t

theorem Run.reachable_invariants {program : Code → Instruction Name Key Value Code Error}
    {r : R} (h : Run program (fun _ => none) r) :
    Safety.Tree r ∧ Safety.Owned r ∧ Ordering.Invariant r := by
  induction h with
  | refl => exact ⟨Safety.empty_tree, Safety.empty_owned, Ordering.supported_empty, Ordering.local_empty⟩
  | step _ transition ih =>
    have step := transition.toCalculus
    exact ⟨Safety.step_tree program step ih.1, Safety.step_owned program step ih.2.1,
      Ordering.step_invariant program step ih.2.2⟩

end Cordis.Orchestration
