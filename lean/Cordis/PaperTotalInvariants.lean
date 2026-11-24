import Cordis.PaperTotalEvaluation

/-! Structural Gamma and retained-provider invariants for total completed
heads. Every preservation fact is derived from the actual four primitive
mutations or the specified identity completion. No operational simulation,
whole-step frame, support or clean-state conclusion is an input premise.
-/
namespace Cordis.PaperTotal
noncomputable section
open Calculus Stages
universe u
variable {Name Key Value Code Error : Type u}
variable [DecidableEq Name] [DecidableEq Key]
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
set_option linter.unusedSectionVars false

theorem ordinary_step_finite (program : Code → Instruction Name Key Value Code Error)
    {r s : R} (step : Step (Land program) Stages.undo r s)
    (old : SupportUniqueness.FiniteDomain r) : SupportUniqueness.FiniteDomain s := by
  cases step with
  | insert => exact SupportUniqueness.put_finite _ _ _ old
  | retire | begin | leave => exact SupportUniqueness.modify_finite _ _ _ old
  | remove actor ready =>
    obtain ⟨names, covered⟩ := old
    refine ⟨names, ?_⟩
    intro name fiber present
    by_cases same : name = actor
    · simp [erase, same] at present
    · exact covered name fiber (by simpa [erase, same] using present)
  | iter _ _ _ _ _ _ _ _ _ _ _ landed | finish _ _ _ _ _ _ _ _ _ _ landed =>
    exact SupportUniqueness.modify_finite _ _ _ (SupportUniqueness.land_finite program landed old)
  | divert _ _ _ _ _ _ _ _ _ _ alternative =>
    rcases alternative with ⟨rfl, _⟩ | ⟨inverse, next, landed, _⟩
    · exact SupportUniqueness.modify_finite _ _ _ old
    · exact SupportUniqueness.modify_finite _ _ _ (SupportUniqueness.land_finite program landed old)
  | unload =>
    exact SupportUniqueness.modify_finite _ _ _
      (SupportUniqueness.finite_of_origins old (Frame.discharge_origins r _))

def Invariant (r : R) : Prop := MediatedRegistry.Allowed r ∧ Ordering.Invariant r

theorem empty_invariant : Invariant (fun _ => none : R) := by
  refine ⟨⟨Safety.empty_tree, ⟨[], ?_⟩, Safety.empty_owned, ?_⟩,
    ⟨Ordering.supported_empty, Ordering.local_empty⟩⟩
  · intro name fiber impossible
    cases impossible
  · intro left right a b impossible
    cases impossible

theorem step_invariant (program : Code → Instruction Name Key Value Code Error)
    (draw : R → Name) (failed : Code → R → Option (Outcome Name Value))
    {r s : R} (step : Step (Landing program draw failed) Stages.undo r s)
    (old : Invariant r) : Invariant s := by
  obtain ⟨localProgram, structural⟩ := step_structural program draw failed step
  exact ⟨⟨Safety.step_tree localProgram structural old.1.1,
      ordinary_step_finite localProgram structural old.1.2.1,
      Safety.step_owned localProgram structural old.1.2.2.1,
      WellFormed.step_disjoint localProgram structural old.1.2.2.2⟩,
    Ordering.step_invariant localProgram structural old.2⟩

inductive Run (program : Code → Instruction Name Key Value Code Error)
    (draw : R → Name) (failed : Code → R → Option (Outcome Name Value)) : R → R → Prop
  | refl (r) : Run program draw failed r r
  | tail {r s t} : Run program draw failed r s → Step (Landing program draw failed) Stages.undo s t →
      Run program draw failed r t

theorem run_invariant (program : Code → Instruction Name Key Value Code Error)
    (draw : R → Name) (failed : Code → R → Option (Outcome Name Value))
    {r s : R} (run : Run program draw failed r s) (old : Invariant r) : Invariant s := by
  induction run with
  | refl => exact old
  | tail _ step ih => exact step_invariant program draw failed step ih

theorem reachable_invariant (program : Code → Instruction Name Key Value Code Error)
    (draw : R → Name) (failed : Code → R → Option (Outcome Name Value))
    {r : R} (run : Run program draw failed (fun _ => none) r) : Invariant r :=
  run_invariant program draw failed run empty_invariant

end
end Cordis.PaperTotal
