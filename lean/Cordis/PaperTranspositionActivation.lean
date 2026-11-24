import Cordis.PaperTranspositionTotal
import Cordis.PaperTotalLabeled

/-! Label-preserving total-activation transport and the Begin cases. These
use the exact total-model labels, preserving the rule and actor. Structural
source-program witnesses are only a device for reusing program-uniform metadata
and guard proofs; the swapped total evaluations follow from evaluate_mark. -/
namespace Cordis.PaperTransposition
noncomputable section
open Calculus Stages Iterators Effects StageRecovery
universe u
variable {Name Key Value Code Error : Type u}
variable [DecidableEq Name] [DecidableEq Key]
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
local notation "I" => Inverse Name Key Value
set_option linter.unusedSectionVars false

theorem activation_other_table {model : PaperTotal.Model Name Key Value Code Error}
    {rule : Labeled.Rule} {actor : Name} {before after : R}
    (step : PaperTotal.Labeled.Step model rule actor before after) (active : Transposition.Activation rule)
    (name : Name) (fiber : F) (different : name ≠ actor) (present : before name = some fiber) :
    ∃ table, after name = some {fiber with table := table} := by
  obtain ⟨localProgram, actual⟩ := step.structural
  exact Transposition.activation_other_table localProgram actual active name fiber different present

theorem activation_target_forward {model : PaperTotal.Model Name Key Value Code Error}
    {rule : Labeled.Rule} {actor : Name} {before after : R}
    (step : PaperTotal.Labeled.Step model rule actor before after) (active : Transposition.Activation rule)
    (name : Name) (view : View Name Key) (different : name ≠ actor) (target : Target before name view) :
    Target after name view := by
  obtain ⟨localProgram, actual⟩ := step.structural
  exact Transposition.activation_target_forward localProgram actual active name view different target

theorem activation_after_phase (model : PaperTotal.Model Name Key Value Code Error)
    (draws : DrawByPresence model.draw) (failures : FailureByTables model.failed)
    {rule : Labeled.Rule} {actor : Name} {before after : R}
    (step : PaperTotal.Labeled.Step model rule actor before after) (active : Transposition.Activation rule)
    (name : Name) (fiber : F) (phase : Phase Name Key Code I)
    (different : actor ≠ name) (present : before name = some fiber)
    (availability : phase.available ↔ fiber.phase.available) :
    PaperTotal.Labeled.Step model rule actor (mark before name phase) (mark after name phase) := by
  cases step with
  | begin _ _ entry view found inactive free target =>
    rw [← Transposition.marks_commute _ _ _ _ _ different]
    exact .begin _ actor entry view ((Transposition.mark_other before actor name phase different).trans found) inactive
      (by simpa only [ErrorFree, Transposition.mark_other before actor name phase different] using free)
      ((Transposition.mark_target before name fiber phase present availability actor view).mpr target)
  | iter _ middle _ entry code stack view inverse next found reloading target landed =>
    rw [← Transposition.marks_commute _ _ _ _ _ different]
    exact .iter _ _ actor entry code stack view inverse next
      ((Transposition.mark_other before actor name phase different).trans found) reloading
      ((Transposition.mark_target before name fiber phase present availability actor view).mpr target)
      (landing_mark model.program model.draw model.failed draws failures landed name fiber phase different present)
  | finish _ middle _ entry code stack view inverse found reloading target landed =>
    rw [← Transposition.marks_commute _ _ _ _ _ different]
    exact .finish _ _ actor entry code stack view inverse
      ((Transposition.mark_other before actor name phase different).trans found) reloading
      ((Transposition.mark_target before name fiber phase present availability actor view).mpr target)
      (landing_mark model.program model.draw model.failed draws failures landed name fiber phase different present)
  | _ => simp [Transposition.Activation] at active

/-- First-Begin needs no independence: both swapped labelled steps and the
literal same endpoint follow from control-read and target frames. -/
theorem begin_activation_diamond (model : PaperTotal.Model Name Key Value Code Error)
    (draws : DrawByPresence model.draw) (failures : FailureByTables model.failed)
    {rule : Labeled.Rule} {first second : Name} {before middle final : R}
    (opening : PaperTotal.Labeled.Step model .begin first before middle)
    (activation : PaperTotal.Labeled.Step model rule second middle final)
    (active : Transposition.Activation rule) (different : first ≠ second) :
    ∃ swapped, PaperTotal.Labeled.Step model rule second before swapped ∧
      PaperTotal.Labeled.Step model .begin first swapped final := by
  cases opening with
  | begin _ _ fiber view found inactive free target =>
    let started : F := {fiber with phase := .reloading fiber.component.entry [] view}
    have startedFound : mark before first (.reloading fiber.component.entry [] view) first = some started :=
      mark_self before first fiber _ found
    have restored : mark (mark before first (.reloading fiber.component.entry [] view)) first .inactive = before := by
      rw [Transposition.mark_twice, ← inactive]
      exact Transposition.mark_existing before first fiber found
    have swapped := activation_after_phase model draws failures activation active first started .inactive
      (Ne.symm different) startedFound (Iff.refl False)
    rw [restored] at swapped
    obtain ⟨table, finalFound⟩ := activation_other_table activation active first started different startedFound
    have firstTarget : Target (mark before first (.reloading fiber.component.entry [] view)) first view :=
      (Transposition.mark_target before first fiber _ found (by simp [inactive, Phase.available]) first view).mpr target
    have finalTarget := activation_target_forward activation active first view different firstTarget
    let current : F := {started with table := table}
    have currentFound : final first = some current := finalFound
    have earlierFound : mark final first .inactive first = some {current with phase := .inactive} :=
      mark_self final first current .inactive currentFound
    have closed : mark (mark final first .inactive) first (.reloading fiber.component.entry [] view) = final := by
      rw [Transposition.mark_twice]
      exact Transposition.mark_existing final first current currentFound
    refine ⟨mark final first .inactive, swapped, ?_⟩
    have beginning : PaperTotal.Labeled.Step model .begin first (mark final first .inactive)
        (mark (mark final first .inactive) first (.reloading fiber.component.entry [] view)) := by
      apply PaperTotal.Labeled.Step.begin (mark final first .inactive) first {current with phase := .inactive} view earlierFound rfl
      · simp [ErrorFree, earlierFound]
      · exact (Transposition.mark_target final first current .inactive currentFound (Iff.refl False) first view).mpr finalTarget
    simpa only [closed] using beginning

/-- Earlier applicability may choose another total view at undeclared keys.
The existing actual ownership/disjointness proof recovers the actual later
partial view, rather than postulating equality of total encodings. -/
theorem activation_begin_diamond (model : PaperTotal.Model Name Key Value Code Error)
    (draws : DrawByPresence model.draw) (failures : FailureByTables model.failed)
    {rule : Labeled.Rule} {actor name : Name} {before middle final : R}
    (activation : PaperTotal.Labeled.Step model rule actor before middle) (active : Transposition.Activation rule)
    (opening : PaperTotal.Labeled.Step model .begin name middle final) (different : name ≠ actor)
    (owned : Safety.Owned before) (disjoint : WellFormed.Disjoint before)
    (earlier : ∃ initial, PaperTotal.Labeled.Step model .begin name before initial) :
    ∃ swapped, PaperTotal.Labeled.Step model .begin name before swapped ∧
      PaperTotal.Labeled.Step model rule actor swapped final := by
  have earlierTarget : ∃ selected, Target before name selected := by
    obtain ⟨initial, begins⟩ := earlier
    cases begins with
    | begin _ _ entry selected present phase free target => exact ⟨selected, target⟩
  cases opening with
  | begin _ _ fiber view found inactive free target =>
    obtain ⟨localProgram, structural⟩ := activation.structural
    have selectedTarget := Transposition.earlier_target_for_selected_view localProgram structural active owned disjoint
      name fiber view different found target earlierTarget
    cases originalFound : before name with
    | none => simp [Target, originalFound] at selectedTarget
    | some original =>
      obtain ⟨table, currentFound⟩ := activation_other_table activation active name original different originalFound
      have currentEq : {original with table := table} = fiber := Option.some.inj (currentFound.symm.trans found)
      have phaseEq : original.phase = .inactive := (congrArg Fiber.phase currentEq).trans inactive
      have componentEq : original.component = fiber.component := by
        have equality := congrArg Fiber.component currentEq
        exact equality
      have earlierFree : ErrorFree before name := by simp [ErrorFree, originalFound]
      refine ⟨mark before name (.reloading original.component.entry [] view),
        .begin before name original view originalFound phaseEq earlierFree selectedTarget, ?_⟩
      have swapped := activation_after_phase model draws failures activation active name original
        (.reloading original.component.entry [] view) (Ne.symm different) originalFound
        (by simp [phaseEq, Phase.available])
      simpa only [componentEq] using swapped

theorem advance_labeled (model : PaperTotal.Model Name Key Value Code Error)
    (actor : Name) (code : Code) (stack : List I) (view : View Name Key) (before : R)
    (fiber : F) (present : before actor = some fiber)
    (phase : fiber.phase = .reloading code stack view) (target : Target before actor view) :
    PaperTotal.Labeled.Step model
      (Transposition.landedRule (PaperTotal.evaluate model.program model.draw model.failed actor code before).2.2)
      actor before (advance model.program model.draw model.failed actor code stack view before) := by
  let result := PaperTotal.evaluate model.program model.draw model.failed actor code before
  have landed : PaperTotal.Landing model.program model.draw model.failed actor code before result.1 result.2.1 result.2.2 := rfl
  change PaperTotal.Labeled.Step model (Transposition.landedRule result.2.2) actor before
    (mark result.1 actor (Transposition.landedPhase result.2.2 result.2.1 stack view))
  cases next : result.2.2 with
  | none =>
    exact .finish before result.1 actor fiber code stack view result.2.1 present phase target (by simpa only [next] using landed)
  | some following =>
    exact .iter before result.1 actor fiber code stack view result.2.1 following present phase target (by simpa only [next] using landed)

section Observation
variable [Setoid Value]
variable (sem : PaperStateObservation.Semantics Name Key Value Code Error)

/-- Exact labels accompany the computed landed exchange: a continuation may
change to a semantically related code, but its Nothing/Just shape (and therefore
Finish/Iter rule) is derived unchanged from Def42(2). -/
theorem landed_labeled_diamond (model : PaperTotal.Model Name Key Value Code Error)
    (draws : DrawByPresence model.draw) (failures : FailureByTables model.failed)
    (first second : Name) (firstCode secondCode : Code)
    (firstRoot secondRoot : Iterator sem.Gamma)
    (independent : Independent sem firstRoot secondRoot)
    (firstReached : Reach firstRoot (sem.iterator first firstCode))
    (secondReached : Reach secondRoot (sem.iterator second secondCode))
    (firstRep : EvaluationRep sem model.program model.draw model.failed first firstCode)
    (secondRep : EvaluationRep sem model.program model.draw model.failed second secondCode)
    (state : sem.Gamma) (left right : F) (firstStack secondStack : List I)
    (firstView secondView : View Name Key)
    (leftFound : state.val first = some left) (rightFound : state.val second = some right)
    (leftPhase : left.phase = .reloading firstCode firstStack firstView)
    (rightPhase : right.phase = .reloading secondCode secondStack secondView)
    (leftTarget : Target state.val first firstView) (rightTarget : Target state.val second secondView)
    (different : first ≠ second) :
    let originalMiddle := advance model.program model.draw model.failed first firstCode firstStack firstView state.val
    let originalFinal := advance model.program model.draw model.failed second secondCode secondStack secondView originalMiddle
    let firstRule := Transposition.landedRule (PaperTotal.evaluate model.program model.draw model.failed first firstCode state.val).2.2
    let secondRule := Transposition.landedRule (PaperTotal.evaluate model.program model.draw model.failed second secondCode originalMiddle).2.2
    ∃ swappedMiddle swappedFinal,
      PaperTotal.Labeled.Step model secondRule second state.val swappedMiddle ∧
      PaperTotal.Labeled.Step model firstRule first swappedMiddle swappedFinal ∧
      PaperStateObservation.Related sem swappedFinal originalFinal := by
  dsimp only
  obtain ⟨_, _, _, _, observed⟩ := landed_total_diamond sem model.program model.draw model.failed draws failures
    first second firstCode secondCode firstRoot secondRoot independent firstReached secondReached firstRep secondRep state
    left right firstStack secondStack firstView secondView leftFound rightFound leftPhase rightPhase leftTarget rightTarget different
  have swapFirst := advance_labeled model second secondCode secondStack secondView state.val right rightFound rightPhase rightTarget
  obtain ⟨table, found⟩ := advance_other model.program model.draw model.failed second secondCode secondStack secondView state.val
    first left leftFound different
  have swapSecond := advance_labeled model first firstCode firstStack firstView _ {left with table := table} found leftPhase
    (advance_target model.program model.draw model.failed second secondCode secondStack secondView state.val right rightFound rightPhase
      first firstView different leftTarget)
  let a := Tracking.forward (sem.iterator first firstCode).effect state
  let b := Tracking.forward (sem.iterator second secondCode).effect state
  have firstLand := represented_landing sem model.program model.draw model.failed first firstCode firstRep state
  have secondLand := represented_landing sem model.program model.draw model.failed second secondCode secondRep state
  obtain ⟨ta, aFirst⟩ := landing_existing_table model.program model.draw model.failed firstLand first left leftFound
  obtain ⟨tb, bSecond⟩ := landing_existing_table model.program model.draw model.failed secondLand second right rightFound
  have pair := evaluated_pair sem model.program model.draw model.failed first second firstCode secondCode firstRoot secondRoot
    independent firstReached secondReached firstRep secondRep state
  have firstRule := landed_rules_equal sem pair.2.1.2
  have secondRule := landed_rules_equal sem pair.2.2.2
  have afterFirst :
      (PaperTotal.evaluate model.program model.draw model.failed second secondCode
        (advance model.program model.draw model.failed first firstCode firstStack firstView state.val)).2.2 =
      (PaperTotal.evaluate model.program model.draw model.failed second secondCode a.val).2.2 := by
    dsimp only [advance]
    rw [← firstRep.forward state]
    rw [evaluate_mark model.program model.draw model.failed draws failures second first secondCode a.val _ _
      (Ne.symm different) aFirst]
    rfl
  have afterSecond :
      (PaperTotal.evaluate model.program model.draw model.failed first firstCode
        (advance model.program model.draw model.failed second secondCode secondStack secondView state.val)).2.2 =
      (PaperTotal.evaluate model.program model.draw model.failed first firstCode b.val).2.2 := by
    dsimp only [advance]
    rw [← secondRep.forward state]
    rw [evaluate_mark model.program model.draw model.failed draws failures first second firstCode b.val _ _
      different bSecond]
    rfl
  refine ⟨advance model.program model.draw model.failed second secondCode secondStack secondView state.val,
    advance model.program model.draw model.failed first firstCode firstStack firstView
      (advance model.program model.draw model.failed second secondCode secondStack secondView state.val),
    ?_, ?_, observed⟩
  · rw [afterFirst]
    simpa only [a, secondRule] using swapFirst
  · simpa only [afterSecond, b, firstRule] using swapSecond

end Observation

end
end Cordis.PaperTransposition
