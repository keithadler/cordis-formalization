import Cordis.PairwiseBirthBoundary

/-! Actual empty-origin comparison traces for the Definition65 boundary. Both
parents perform legal births, and both resulting next stages instantiate valid,
globally witnessed components. The foreign lifecycle edit does not restore
payload stability. No raw-name reuse, missing actor, failed guard, or absent
binding occurs in this example. -/
namespace Cordis.PairwiseBirthExamples
noncomputable section
open Calculus Stages Effects Iterators PairwiseBirthSemantics PairwiseBirthBoundary

def after : Gamma := ⟨afterForeign, foreign_run.reachable_invariants.1,
  SupportUniqueness.reachable_finite program foreign_run⟩

theorem after_state : after.val =
    mark (put base.val 2 (fresh (component .unit) (some 1))) 1 (.active [.retire 2] view) := by
  change mark moved.val 1 _ = _
  rw [moved_state]

theorem after_draw : draw after ≠ 2 := by
  apply draw_other
  rw [after_state]
  simp [mark, Calculus.modify, put]

theorem after_parent : after.val 0 ≠ none := by
  rw [after_state]
  simpa [mark, Calculus.modify, put] using base_parent

theorem after_parent_row : after.val 0 = some
    { (fresh (component .parent) none : F) with phase := .reloading .parent [] view } := by
  rw [after_state]
  rfl

def shortState : R := mark
  (put base.val 2 (fresh (component .unit) (some 0))) 0
  (.reloading .tailShort [.retire 2] view)
def longState : R := mark
  (put after.val (draw after) (fresh (component .unit) (some 0))) 0
  (.reloading .tailLong [.retire (draw after)] view)

theorem before_parent_iter : Orchestration.Step program r4 shortState := by
  apply Orchestration.Step.iter r4 _ 0
    { (fresh (component .parent) none : F) with phase := .reloading .parent [] view }
    .parent [] view (.retire 2) .tailShort
  · rfl
  · rfl
  · exact target_empty_keys _ _ _ rfl rfl
  · exact parent_legal_both.1

theorem after_parent_iter : Orchestration.Step program afterForeign longState := by
  apply Orchestration.Step.iter afterForeign _ 0
    { (fresh (component .parent) none : F) with phase := .reloading .parent [] view }
    .parent [] view (.retire (draw after)) .tailLong
  · exact after_parent_row
  · rfl
  · exact target_empty_keys _ _ _ after_parent_row rfl
  · have landed := Execution.instantiate (program := program) (result := fun code => (program code).next)
      after.val 0 .parent
      (component .unit) (draw after) rfl (fresh_ready 0 (component .unit) after after_parent)
    simpa [program, after_draw] using landed

theorem short_run : Orchestration.Run program empty shortState := .step base_run before_parent_iter
theorem long_run : Orchestration.Run program empty longState := .step foreign_run after_parent_iter

def shortGamma : Gamma := ⟨shortState, short_run.reachable_invariants.1,
  SupportUniqueness.reachable_finite program short_run⟩
def longGamma : Gamma := ⟨longState, long_run.reachable_invariants.1,
  SupportUniqueness.reachable_finite program long_run⟩

theorem after_draw_not_parent : draw after ≠ 0 := by
  intro same
  exact after_parent (same ▸ draw_absent after)

theorem short_parent_row : shortGamma.val 0 = some
    { (fresh (component .parent) none : F) with phase := .reloading .tailShort [.retire 2] view } := rfl

theorem long_parent_row : longGamma.val 0 = some
    { (fresh (component .parent) none : F) with phase := .reloading .tailLong [.retire (draw after)] view } := by
  change (mark (put after.val (draw after) _) 0 _) 0 = _
  simp [mark, Calculus.modify, put, Ne.symm after_draw_not_parent, after_parent_row]

def shortFinal : R := mark
  (put shortGamma.val (draw shortGamma) (fresh (component .unit) (some 0))) 0
  (.active [.retire (draw shortGamma), .retire 2] view)
def longFinal : R := mark
  (put longGamma.val (draw longGamma) (fresh (component .twoBirths) (some 0))) 0
  (.active [.retire (draw longGamma), .retire (draw after)] view)

theorem short_finish : Orchestration.Step program shortState shortFinal := by
  apply Orchestration.Step.finish shortState _ 0
    { (fresh (component .parent) none : F) with phase := .reloading .tailShort [.retire 2] view }
    .tailShort [.retire 2] view (.retire (draw shortGamma))
  · exact short_parent_row
  · rfl
  · exact target_empty_keys _ _ _ short_parent_row rfl
  · exact Execution.instantiate shortGamma.val 0 .tailShort (component .unit)
      (draw shortGamma) rfl (fresh_ready 0 (component .unit) shortGamma (by rw [short_parent_row]; simp))

theorem long_finish : Orchestration.Step program longState longFinal := by
  apply Orchestration.Step.finish longState _ 0
    { (fresh (component .parent) none : F) with phase := .reloading .tailLong [.retire (draw after)] view }
    .tailLong [.retire (draw after)] view (.retire (draw longGamma))
  · exact long_parent_row
  · rfl
  · exact target_empty_keys _ _ _ long_parent_row rfl
  · exact Execution.instantiate longGamma.val 0 .tailLong (component .twoBirths)
      (draw longGamma) rfl (fresh_ready 0 (component .twoBirths) longGamma (by rw [long_parent_row]; simp))

/-- Both choices are realized by actual next birth stages. The named entry
iterators differ in Maybe shape for every possible pair of actor names, so
changing names or asking only for semantic agreement cannot conceal it. -/
theorem actual_payload_choices :
    Orchestration.Run program empty shortFinal ∧
    Orchestration.Run program empty longFinal ∧
    (program .tailShort).action = .instantiate (component .unit) ∧
    (program .tailLong).action = .instantiate (component .twoBirths) ∧
    ¬ ComponentsAgree (component .unit) (component .twoBirths) :=
  ⟨.step short_run short_finish, .step long_run long_finish, rfl, rfl, child_components_disagree⟩

end
end Cordis.PairwiseBirthExamples
