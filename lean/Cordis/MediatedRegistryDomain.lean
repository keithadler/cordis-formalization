import Cordis.Iterators
import Cordis.ReplayWitnessCompatibility
import Cordis.SemanticHead
import Cordis.SupportUniqueness

/-! A structural registry domain for the table-observation part of the paper.
It contains finite rooted, declaration-owned, disjoint registries; no Eq54,
step-indexed relation, iterator congruence or recovery assertion occurs in its
definition. Actual primitive landings and every actual captured inverse preserve
this domain. Consequently the complete inverse function, including inputs other
than the state at which it was captured, has its original registry meaning.

The checked head below specifies one total extension: an undefined primitive
has identity forward/inverse maps and no continuation. The paper's p45
identity convention specifies a state map, not this entire triple. The separate
success theorem preserves the exact ordinary Land, inverse and selected tail;
it never asserts that an undefined head is an ordinary transition.
-/
namespace Cordis.MediatedRegistry
noncomputable section
open Calculus Stages Iterators StageRecovery
universe u
variable {Name Key Value Code Error : Type u}
variable [DecidableEq Name] [DecidableEq Key]
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "I" => Inverse Name Key Value
set_option linter.unusedSectionVars false

def Allowed (state : R) : Prop :=
  Safety.Tree state ∧ SupportUniqueness.FiniteDomain state ∧
    Safety.Owned state ∧ WellFormed.Disjoint state

abbrev Gamma (Name Key Value Code Error : Type u) :=
  {state : Registry Name Key Value Code (Inverse Name Key Value) Error // Allowed state}

theorem inverse_allowed (inverse : I) {state : R} (old : Allowed state) :
    Allowed (Stages.undo inverse state) := by
  refine ⟨Safety.undo_tree state inverse old.1, ?_,
    Safety.undo_owned state inverse old.2.2.1, WellFormed.undo_disjoint state inverse old.2.2.2⟩
  cases inverse with
  | unit => exact old.2.1
  | restrict | operate | retire => exact SupportUniqueness.modify_finite _ _ _ old.2.1

theorem landing_allowed (program : Code → Instruction Name Key Value Code Error)
    {actor : Name} {code : Code} {before after : R} {inverse : I} {next : Option Code}
    (landed : Land program actor code before after inverse next) (old : Allowed before) : Allowed after :=
  ⟨Safety.landing_tree program landed old.1, SupportUniqueness.land_finite program landed old.2.1,
    Safety.landing_owned program landed old.2.2.1, WellFormed.land_disjoint program landed old.2.2.2⟩

theorem step_allowed (program : Code → Instruction Name Key Value Code Error) {before after : R}
    (step : Calculus.Step (Land program) Stages.undo before after) (old : Allowed before) : Allowed after :=
  ⟨Safety.step_tree program step old.1, SupportUniqueness.calculus_step_finite program step old.2.1,
    Safety.step_owned program step old.2.2.1, WellFormed.step_disjoint program step old.2.2.2⟩

theorem mark_allowed {state : R} (actor : Name) (phase : Phase Name Key Code I)
    (old : Allowed state) : Allowed (mark state actor phase) :=
  ⟨Safety.modify_tree _ _ _ (fun _ => rfl) old.1, SupportUniqueness.modify_finite _ _ _ old.2.1,
    Safety.mark_owned _ actor phase old.2.2.1, WellFormed.mark_disjoint _ actor phase old.2.2.2⟩

def liftInverse (inverse : I) (state : Gamma Name Key Value Code Error) : Gamma Name Key Value Code Error :=
  ⟨Stages.undo inverse state.val, inverse_allowed inverse state.property⟩

def head (program : Code → Instruction Name Key Value Code Error) (actor : Name)
    (draw : Gamma Name Key Value Code Error → Name) (code : Code) :
    Effects.Effect (Gamma Name Key Value Code Error) where
  run before := match evaluated : SemanticHead.evaluate program actor (draw before) code before.val with
    | none => (before, id)
    | some result =>
      (⟨result.1, landing_allowed program
        (SemanticHead.evaluate_sound program actor (draw before) code before.val result.1
          result.2.1 result.2.2 evaluated).1 before.property⟩, liftInverse result.2.1)

/-- The frame result is independent of the unspecified failed-head Maybe
completion. A completion may terminate, or feed a chosen outcome to the same
named continuation family. On ordinary successful inputs it uses exactly the
real primitive's produced continuation. -/
def completedSelected (program : Code → Instruction Name Key Value Code Error) (actor : Name)
    (draw : Gamma Name Key Value Code Error → Name)
    (failed : Code → Gamma Name Key Value Code Error → Option (Outcome Name Value))
    (code : Code) (before : Gamma Name Key Value Code Error) : Option Code :=
  match SemanticHead.evaluate program actor (draw before) code before.val with
  | none => (failed code before).bind (program code).next
  | some result => result.2.2

theorem head_none (program : Code → Instruction Name Key Value Code Error) (actor : Name)
    (draw : Gamma Name Key Value Code Error → Name) (code : Code) (before : Gamma Name Key Value Code Error)
    (undefined : SemanticHead.evaluate program actor (draw before) code before.val = none) :
    (head program actor draw code).run before = (before, id) := by
  unfold head
  dsimp only
  split
  · rfl
  · rename_i result found
    rw [undefined] at found
    cases found

theorem head_some (program : Code → Instruction Name Key Value Code Error) (actor : Name)
    (draw : Gamma Name Key Value Code Error → Name) (code : Code) (before : Gamma Name Key Value Code Error)
    (result : SemanticHead.Result Name Key Value Code Error)
    (evaluated : SemanticHead.evaluate program actor (draw before) code before.val = some result) :
    ((head program actor draw code).run before).1.val = result.1 ∧
      ((head program actor draw code).run before).2 = liftInverse result.2.1 := by
  unfold head
  dsimp only
  split
  · rename_i found
    rw [evaluated] at found
    cases found
  · rename_i output found
    have same := Option.some.inj (found.symm.trans evaluated)
    subst output
    exact ⟨rfl, rfl⟩

end
end Cordis.MediatedRegistry
