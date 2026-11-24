import Cordis.Stages

/-! Definition58's rule/actor labels on the actual nine-rule relation. Forgetting
labels and adding them back are both proved; this is not an abstract transition
system with different guards or inverses. -/
namespace Cordis.Labeled
open Calculus Stages
universe u
variable {Name Key Value Code Error : Type u}
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
variable [DecidableEq Name] [DecidableEq Key]

inductive Rule where
  | insert | retire | remove | begin | iter | finish | divert | leave | unload
  deriving DecidableEq

inductive Step (program : Code → Instruction Name Key Value Code Error) : Rule → Name → R → R → Prop
  | insert (r name component parent) : Insertable r name component parent →
      Step program .insert name r (put r name (fresh component parent))
  | retire (r name) : r name ≠ none → Step program .retire name r (Calculus.retire r name)
  | remove (r name) : Removable r name → Step program .remove name r (erase r name)
  | begin (r name fiber view) : r name = some fiber → fiber.phase = .inactive →
      ErrorFree r name → Target r name view →
      Step program .begin name r (mark r name (.reloading fiber.component.entry [] view))
  | iter (r s name fiber code accumulator view inverse next) :
      r name = some fiber → fiber.phase = .reloading code accumulator view →
      Target r name view → Land program name code r s inverse (some next) →
      Step program .iter name r (mark s name (.reloading next (inverse :: accumulator) view))
  | finish (r s name fiber code accumulator view inverse) :
      r name = some fiber → fiber.phase = .reloading code accumulator view →
      Target r name view → Land program name code r s inverse none →
      Step program .finish name r (mark s name (.active (inverse :: accumulator) view))
  | divert (r s name fiber code accumulator view tail) :
      r name = some fiber → fiber.phase = .reloading code accumulator view →
      ¬ Target r name view →
      ((s = r ∧ tail = []) ∨ ∃ inverse next, Land program name code r s inverse next ∧ tail = [inverse]) →
      Step program .divert name r (mark s name (.unloading (tail ++ accumulator) view))
  | leave (r name fiber accumulator view) :
      r name = some fiber → fiber.phase = .active accumulator view → ¬ Target r name view →
      Step program .leave name r (mark r name (.unloading accumulator view))
  | unload (r name fiber accumulator view) :
      r name = some fiber → fiber.phase = .unloading accumulator view → ¬ Relied r name →
      Step program .unload name r (mark (discharge Stages.undo accumulator r) name .inactive)

theorem Step.toCalculus {program : Code → Instruction Name Key Value Code Error}
    {rule : Rule} {actor : Name} {r s : R} (h : Step program rule actor r s) :
    Calculus.Step (Land program) Stages.undo r s := by
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

theorem Step.ofCalculus {program : Code → Instruction Name Key Value Code Error}
    {r s : R} (h : Calculus.Step (Land program) Stages.undo r s) :
    ∃ rule actor, Step program rule actor r s := by
  cases h with
  | insert name component parent ready => exact ⟨_, _, .insert r name component parent ready⟩
  | retire name present => exact ⟨_, _, .retire r name present⟩
  | remove name ready => exact ⟨_, _, .remove r name ready⟩
  | begin name row view present inactive free target =>
    exact ⟨_, _, .begin r name row view present inactive free target⟩
  | iter middle name row code stack view inverse next present phase target landed =>
    exact ⟨_, _, .iter r middle name row code stack view inverse next present phase target landed⟩
  | finish middle name row code stack view inverse present phase target landed =>
    exact ⟨_, _, .finish r middle name row code stack view inverse present phase target landed⟩
  | divert middle name row code stack view tail present phase stale branch =>
    exact ⟨_, _, .divert r middle name row code stack view tail present phase stale branch⟩
  | leave name row stack view present phase stale =>
    exact ⟨_, _, .leave r name row stack view present phase stale⟩
  | unload name row stack view present phase unrelied =>
    exact ⟨_, _, .unload r name row stack view present phase unrelied⟩

end Cordis.Labeled
