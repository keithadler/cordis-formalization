import Cordis.PaperTranspositionSemantics

/-! Actual total-evaluator Iter/Finish exchanges from paper independence.
This composes the semantic map/yield calculation with the real target guards
and phase edits. The constructor evaluator, failed completion, no-control-read
contracts and exact global denotation are explicit; no primitive or whole-step
diamond is assumed. Begin cases and a full inherited-hypothesis audit remain
separate from this four-case landed-step result. -/
namespace Cordis.PaperTransposition
noncomputable section
open Calculus Stages Iterators Effects StageRecovery
universe u
variable {Name Key Value Code Error : Type u}
variable [DecidableEq Name] [DecidableEq Key] [Setoid Value]
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
local notation "I" => Inverse Name Key Value
set_option linter.unusedSectionVars false

def advance (program : Code → Instruction Name Key Value Code Error)
    (draw : R → Name) (failed : Code → R → Option (Outcome Name Value))
    (actor : Name) (code : Code) (stack : List I) (view : View Name Key) (before : R) : R :=
  let result := PaperTotal.evaluate program draw failed actor code before
  mark result.1 actor (Transposition.landedPhase result.2.2 result.2.1 stack view)

theorem advance_step (program : Code → Instruction Name Key Value Code Error)
    (draw : R → Name) (failed : Code → R → Option (Outcome Name Value))
    (actor : Name) (code : Code) (stack : List I) (view : View Name Key) (before : R)
    (fiber : F) (present : before actor = some fiber)
    (phase : fiber.phase = .reloading code stack view) (target : Target before actor view) :
    Calculus.Step (PaperTotal.Landing program draw failed) Stages.undo before
      (advance program draw failed actor code stack view before) := by
  let result := PaperTotal.evaluate program draw failed actor code before
  have landed : PaperTotal.Landing program draw failed actor code before result.1 result.2.1 result.2.2 := rfl
  change Calculus.Step (PaperTotal.Landing program draw failed) Stages.undo before
    (mark result.1 actor (Transposition.landedPhase result.2.2 result.2.1 stack view))
  cases next : result.2.2 with
  | none =>
    exact .finish before result.1 actor fiber code stack view result.2.1 present phase target
      (by simpa only [next] using landed)
  | some following =>
    exact .iter before result.1 actor fiber code stack view result.2.1 following present phase target
      (by simpa only [next] using landed)

theorem advance_target (program : Code → Instruction Name Key Value Code Error)
    (draw : R → Name) (failed : Code → R → Option (Outcome Name Value))
    (actor : Name) (code : Code) (stack : List I) (view : View Name Key) (before : R)
    (fiber : F) (present : before actor = some fiber) (phase : fiber.phase = .reloading code stack view)
    (other : Name) (otherView : View Name Key) (different : other ≠ actor)
    (target : Target before other otherView) :
    Target (advance program draw failed actor code stack view before) other otherView := by
  exact landing_target_forward program draw failed (by rfl) fiber present
    (by simp [phase, Phase.available]) _ other otherView different target

theorem advance_other (program : Code → Instruction Name Key Value Code Error)
    (draw : R → Name) (failed : Code → R → Option (Outcome Name Value))
    (actor : Name) (code : Code) (stack : List I) (view : View Name Key) (before : R)
    (other : Name) (fiber : F) (present : before other = some fiber) (different : other ≠ actor) :
    ∃ table, advance program draw failed actor code stack view before other = some {fiber with table := table} := by
  obtain ⟨table, found⟩ := landing_existing_table program draw failed (by rfl) other fiber present
  exact ⟨table, (Transposition.mark_other _ other actor _ different).trans found⟩

theorem advance_mark (program : Code → Instruction Name Key Value Code Error)
    (draw : R → Name) (failed : Code → R → Option (Outcome Name Value))
    (draws : DrawByPresence draw) (failures : FailureByTables failed)
    (actor : Name) (code : Code) (stack : List I) (view : View Name Key) (before : R)
    (other : Name) (fiber : F) (phase : Phase Name Key Code I)
    (different : actor ≠ other) (present : before other = some fiber) :
    advance program draw failed actor code stack view (mark before other phase) =
      mark (advance program draw failed actor code stack view before) other phase := by
  unfold advance
  rw [evaluate_mark program draw failed draws failures actor other code before fiber phase different present]
  exact Transposition.marks_commute _ actor other _ phase different

variable (sem : PaperStateObservation.Semantics Name Key Value Code Error)
local instance : Setoid sem.Gamma := PaperStateObservation.base sem

theorem represented_landing (program : Code → Instruction Name Key Value Code Error)
    (draw : R → Name) (failed : Code → R → Option (Outcome Name Value))
    (actor : Name) (code : Code) (representation : EvaluationRep sem program draw failed actor code)
    (before : sem.Gamma) :
    PaperTotal.Landing program draw failed actor code before.val
      (Tracking.forward (sem.iterator actor code).effect before).val
      (PaperTotal.evaluate program draw failed actor code before.val).2.1
      (PaperTotal.evaluate program draw failed actor code before.val).2.2 := by
  change PaperTotal.evaluate program draw failed actor code before.val = _
  rw [representation.forward]

theorem same_phase_accumulator {left right : R} (related : PaperStateObservation.Related sem left right)
    (actor : Name) (a b : F) (first : left actor = some a) (second : right actor = some b)
    (code : Code) (stack : List I) (view : View Name Key)
    (leftPhase : a.phase = .reloading code stack view) (rightPhase : b.phase = .reloading code stack view) :
    PaperStateObservation.AccumulatorRelated sem stack stack := by
  have phases := (PaperStateObservation.fields sem related actor a b first second).phase
  rw [leftPhase, rightPhase] at phases
  cases phases
  assumption

/-- The four Iter/Finish pairs. The output states are computed, and all four
actual Step derivations are conclusions. The endpoint compares whole cleanup
maps and recursively denoted selected code at the literal Eq54 field base. -/
theorem landed_total_diamond (program : Code → Instruction Name Key Value Code Error)
    (draw : R → Name) (failed : Code → R → Option (Outcome Name Value))
    (draws : DrawByPresence draw) (failures : FailureByTables failed)
    (first second : Name) (firstCode secondCode : Code)
    (firstRoot secondRoot : Iterator sem.Gamma)
    (independent : Independent sem firstRoot secondRoot)
    (firstReached : Reach firstRoot (sem.iterator first firstCode))
    (secondReached : Reach secondRoot (sem.iterator second secondCode))
    (firstRep : EvaluationRep sem program draw failed first firstCode)
    (secondRep : EvaluationRep sem program draw failed second secondCode)
    (state : sem.Gamma) (left right : F) (firstStack secondStack : List I)
    (firstView secondView : View Name Key)
    (leftFound : state.val first = some left) (rightFound : state.val second = some right)
    (leftPhase : left.phase = .reloading firstCode firstStack firstView)
    (rightPhase : right.phase = .reloading secondCode secondStack secondView)
    (leftTarget : Target state.val first firstView) (rightTarget : Target state.val second secondView)
    (different : first ≠ second) :
    let originalMiddle := advance program draw failed first firstCode firstStack firstView state.val
    let originalFinal := advance program draw failed second secondCode secondStack secondView originalMiddle
    let swappedMiddle := advance program draw failed second secondCode secondStack secondView state.val
    let swappedFinal := advance program draw failed first firstCode firstStack firstView swappedMiddle
    Calculus.Step (PaperTotal.Landing program draw failed) Stages.undo state.val originalMiddle ∧
      Calculus.Step (PaperTotal.Landing program draw failed) Stages.undo originalMiddle originalFinal ∧
      Calculus.Step (PaperTotal.Landing program draw failed) Stages.undo state.val swappedMiddle ∧
      Calculus.Step (PaperTotal.Landing program draw failed) Stages.undo swappedMiddle swappedFinal ∧
      PaperStateObservation.Related sem swappedFinal originalFinal := by
  dsimp only
  have originalFirst := advance_step program draw failed first firstCode firstStack firstView state.val
    left leftFound leftPhase leftTarget
  have swappedFirst := advance_step program draw failed second secondCode secondStack secondView state.val
    right rightFound rightPhase rightTarget
  obtain ⟨rightTable, rightAfter⟩ := advance_other program draw failed first firstCode firstStack firstView state.val
    second right rightFound (Ne.symm different)
  obtain ⟨leftTable, leftAfter⟩ := advance_other program draw failed second secondCode secondStack secondView state.val
    first left leftFound different
  have originalSecond := advance_step program draw failed second secondCode secondStack secondView _
    {right with table := rightTable} rightAfter rightPhase
    (advance_target program draw failed first firstCode firstStack firstView state.val left leftFound leftPhase
      second secondView (Ne.symm different) rightTarget)
  have swappedSecond := advance_step program draw failed first firstCode firstStack firstView _
    {left with table := leftTable} leftAfter leftPhase
    (advance_target program draw failed second secondCode secondStack secondView state.val right rightFound rightPhase
      first firstView different leftTarget)
  refine ⟨originalFirst, originalSecond, swappedFirst, swappedSecond, ?_⟩
  let a := Tracking.forward (sem.iterator first firstCode).effect state
  let b := Tracking.forward (sem.iterator second secondCode).effect state
  have firstLand := represented_landing sem program draw failed first firstCode firstRep state
  have secondLand := represented_landing sem program draw failed second secondCode secondRep state
  have abLand := represented_landing sem program draw failed second secondCode secondRep a
  have baLand := represented_landing sem program draw failed first firstCode firstRep b
  obtain ⟨rawRelated, firstYield, secondYield⟩ := evaluated_pair sem program draw failed first second firstCode secondCode
    firstRoot secondRoot independent firstReached secondReached firstRep secondRep state
  have rawRelated' : PaperStateObservation.Related sem
      (Tracking.forward (sem.iterator first firstCode).effect b).val
      (Tracking.forward (sem.iterator second secondCode).effect a).val := by
    simpa only [a, b, firstRep.forward, secondRep.forward] using rawRelated
  obtain ⟨ta1, aFirst⟩ := landing_existing_table program draw failed firstLand first left leftFound
  obtain ⟨ta2, aSecond⟩ := landing_existing_table program draw failed firstLand second right rightFound
  obtain ⟨tb1, bFirst⟩ := landing_existing_table program draw failed secondLand first left leftFound
  obtain ⟨tb2, bSecond⟩ := landing_existing_table program draw failed secondLand second right rightFound
  obtain ⟨tab1, abFirst⟩ := landing_existing_table program draw failed abLand first _ aFirst
  obtain ⟨tab2, abSecond⟩ := landing_existing_table program draw failed abLand second _ aSecond
  obtain ⟨tba1, baFirst⟩ := landing_existing_table program draw failed baLand first _ bFirst
  obtain ⟨tba2, baSecond⟩ := landing_existing_table program draw failed baLand second _ bSecond
  have firstOld := same_phase_accumulator sem rawRelated' first _ _ baFirst abFirst
    firstCode firstStack firstView leftPhase leftPhase
  have secondOld := same_phase_accumulator sem rawRelated' second _ _ baSecond abSecond
    secondCode secondStack secondView rightPhase rightPhase
  have phases1 := fun required => landed_phases_related sem first required firstYield.2 firstYield.1 firstStack firstOld firstView
  have secondNext := OptionRel.symm secondYield.2
  have phases2 := fun required => landed_phases_related sem second required
    (OptionRel.mono (fun _ _ relation => Iterators.related_symm relation) secondNext)
    (Independence.related_symm secondYield.1) secondStack secondOld secondView
  have one := PaperStateObservation.mark_related sem rawRelated first _ _ (fun fiber _ => phases1 fiber.component.requires)
  have both := PaperStateObservation.mark_related sem one second _ _ (fun fiber _ => phases2 fiber.component.requires)
  have leftTransport := advance_mark program draw failed draws failures first firstCode firstStack firstView b.val
    second _ (Transposition.landedPhase (PaperTotal.evaluate program draw failed second secondCode state.val).2.2
      (PaperTotal.evaluate program draw failed second secondCode state.val).2.1 secondStack secondView) different bSecond
  have rightTransport := advance_mark program draw failed draws failures second secondCode secondStack secondView a.val
    first _ (Transposition.landedPhase (PaperTotal.evaluate program draw failed first firstCode state.val).2.2
      (PaperTotal.evaluate program draw failed first firstCode state.val).2.1 firstStack firstView) (Ne.symm different) aFirst
  change PaperStateObservation.Related sem
    (advance program draw failed first firstCode firstStack firstView
      (mark _ second _))
    (advance program draw failed second secondCode secondStack secondView
      (mark _ first _))
  rw [← firstRep.forward state, ← secondRep.forward state]
  rw [leftTransport, rightTransport]
  simpa only [advance, Transposition.marks_commute _ second first _ _ (Ne.symm different)] using both

end
end Cordis.PaperTransposition
