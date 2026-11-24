import Cordis.PaperTranspositionActivation
import Cordis.PaperTranspositionObservation

/-! The original adjacent-pair shape of Lemma78(1), for the explicitly
represented total-constructor interpretation. All nine Begin/Iter/Finish pairs
are covered. The earlier applicability premise is used to reconstruct the
second actor's INITIAL stored phase and target, not to assume its swapped
execution. Function-field typing is stated separately from the transition
premises; it derives Eq54 reflexivity for literal-equal Begin endpoints.

This finishes the adjacent-rule assembly, not the identification of every
paper interpretation with the chosen completion family. Exact all-input code
denotation, the documented p46 finer commutation convention, no-control-read
choices, and globally typed stored function fields remain explicit. -/
namespace Cordis.PaperTransposition
noncomputable section
open Calculus Stages Iterators Effects StageRecovery
universe u
variable {Name Key Value Code Error : Type u}
variable [DecidableEq Name] [DecidableEq Key] [Setoid Value]
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
local notation "I" => Inverse Name Key Value
variable (sem : PaperStateObservation.Semantics Name Key Value Code Error)
local instance : Setoid sem.Gamma := PaperStateObservation.base sem
set_option linter.unusedSectionVars false

structure TypedFields (state : R) : Prop where
  entries : ∀ actor fiber, state actor = some fiber → WitnessedIterator (sem.iterator actor fiber.component.entry)
  current : ∀ actor fiber, state actor = some fiber → ∀ code stack view,
    fiber.phase = .reloading code stack view → WitnessedIterator (sem.iterator actor code)
  captured : AccumulatorProvenance.Accumulators (PaperTranspositionObservation.GeneratedInverse sem) state

theorem typed_fields_self {state : R} (typed : TypedFields sem state) :
    PaperStateObservation.Related sem state state :=
  PaperStateObservation.witnessed_state_self sem state typed.entries typed.current
    (fun actor fiber present token member => PaperTranspositionObservation.generated_inverse_respects sem
      (typed.captured actor fiber present token member))

def CurrentHeads (model : PaperTotal.Model Name Key Value Code Error) (state : R) : Prop :=
  ∀ actor fiber code stack view, state actor = some fiber → fiber.phase = .reloading code stack view →
    Reach (sem.iterator actor fiber.component.entry) (sem.iterator actor code) ∧
      EvaluationRep sem model.program model.draw model.failed actor code

def ComponentsIndependent (state : R) (first second : Name) : Prop :=
  ∀ left right, state first = some left → state second = some right →
    Independent sem (sem.iterator first left.component.entry) (sem.iterator second right.component.entry)

theorem landed_source_before (model : PaperTotal.Model Name Key Value Code Error)
    {first second : Name} {rule : Labeled.Rule} {before middle : R}
    (firstStep : PaperTotal.Labeled.Step model rule first before middle) (active : Transposition.Activation rule)
    (different : first ≠ second) (current : F) (found : middle second = some current)
    (code : Code) (stack : List I) (view : View Name Key) (phase : current.phase = .reloading code stack view)
    (applicable : ∃ otherRule initial, Transposition.Activation otherRule ∧ PaperTotal.Labeled.Step model otherRule second before initial) :
    ∃ original : F, before second = some original ∧ original.phase = .reloading code stack view ∧ Target before second view := by
  obtain ⟨otherRule, initial, otherActive, otherStep⟩ := applicable
  obtain ⟨localProgram, structural⟩ := otherStep.structural
  obtain ⟨original, originalView, originalFound, unavailable, target⟩ := Transposition.activation_source localProgram structural otherActive
  obtain ⟨table, afterFound⟩ := activation_other_table firstStep active second original (Ne.symm different) originalFound
  have same : {original with table := table} = current := Option.some.inj (afterFound.symm.trans found)
  have originalPhase : original.phase = .reloading code stack view := (congrArg Fiber.phase same).trans phase
  refine ⟨original, originalFound, originalPhase, ?_⟩
  cases otherStep with
  | begin _ _ fiber selected present inactive free ownTarget =>
    have equal : fiber = original := Option.some.inj (present.symm.trans originalFound)
    subst fiber
    rw [originalPhase] at inactive
    cases inactive
  | iter _ stage _ fiber c a selected inverse next present reloading ownTarget landed =>
    have equal : fiber = original := Option.some.inj (present.symm.trans originalFound)
    subst fiber
    rw [originalPhase] at reloading
    cases reloading
    exact ownTarget
  | finish _ stage _ fiber c a selected inverse present reloading ownTarget landed =>
    have equal : fiber = original := Option.some.inj (present.symm.trans originalFound)
    subst fiber
    rw [originalPhase] at reloading
    cases reloading
    exact ownTarget
  | _ => simp [Transposition.Activation] at otherActive

theorem selected_landed_diamond (model : PaperTotal.Model Name Key Value Code Error)
    (draws : DrawByPresence model.draw) (failures : FailureByTables model.failed)
    (first second : Name) (firstCode secondCode : Code)
    (state : sem.Gamma) (stage final : R) (firstInverse secondInverse : I) (firstNext secondNext : Option Code)
    (left right : F) (firstStack secondStack : List I) (firstView secondView : View Name Key)
    (leftFound : state.val first = some left) (rightFound : state.val second = some right)
    (leftPhase : left.phase = .reloading firstCode firstStack firstView)
    (rightPhase : right.phase = .reloading secondCode secondStack secondView)
    (leftTarget : Target state.val first firstView) (rightTarget : Target state.val second secondView)
    (different : first ≠ second) (heads : CurrentHeads sem model state.val)
    (independent : ComponentsIndependent sem state.val first second)
    (firstLanding : PaperTotal.Landing model.program model.draw model.failed first firstCode state.val stage firstInverse firstNext)
    (secondLanding : PaperTotal.Landing model.program model.draw model.failed second secondCode
      (mark stage first (Transposition.landedPhase firstNext firstInverse firstStack firstView)) final secondInverse secondNext) :
    ∃ swappedMiddle swappedFinal,
      PaperTotal.Labeled.Step model (Transposition.landedRule secondNext) second state.val swappedMiddle ∧
      PaperTotal.Labeled.Step model (Transposition.landedRule firstNext) first swappedMiddle swappedFinal ∧
      PaperStateObservation.Related sem swappedFinal
        (mark final second (Transposition.landedPhase secondNext secondInverse secondStack secondView)) := by
  obtain ⟨firstReach, firstRep⟩ := heads first left firstCode firstStack firstView leftFound leftPhase
  obtain ⟨secondReach, secondRep⟩ := heads second right secondCode secondStack secondView rightFound rightPhase
  have swapped := landed_labeled_diamond sem model draws failures first second firstCode secondCode
    (sem.iterator first left.component.entry) (sem.iterator second right.component.entry)
    (independent left right leftFound rightFound) firstReach secondReach firstRep secondRep state left right
    firstStack secondStack firstView secondView leftFound rightFound leftPhase rightPhase leftTarget rightTarget different
  change PaperTotal.evaluate model.program model.draw model.failed first firstCode state.val = _ at firstLanding
  change PaperTotal.evaluate model.program model.draw model.failed second secondCode _ = _ at secondLanding
  simpa only [advance, firstLanding, secondLanding] using swapped

theorem landed_against_activation (model : PaperTotal.Model Name Key Value Code Error)
    (draws : DrawByPresence model.draw) (failures : FailureByTables model.failed)
    {first second : Name} {firstCode : Code} (state : sem.Gamma) {stage final : R}
    {firstInverse : I} {firstNext : Option Code} {secondRule : Labeled.Rule}
    (firstStack : List I) (firstView : View Name Key)
    (firstLanding : PaperTotal.Landing model.program model.draw model.failed first firstCode state.val stage firstInverse firstNext)
    (left : F) (leftFound : state.val first = some left)
    (leftPhase : left.phase = .reloading firstCode firstStack firstView) (leftTarget : Target state.val first firstView)
    (secondStep : PaperTotal.Labeled.Step model secondRule second
      (mark stage first (Transposition.landedPhase firstNext firstInverse firstStack firstView)) final)
    (secondActive : Transposition.Activation secondRule)
    (applicable : ∃ initial, PaperTotal.Labeled.Step model secondRule second state.val initial)
    (different : first ≠ second) (owned : Safety.Owned state.val) (disjoint : WellFormed.Disjoint state.val)
    (heads : CurrentHeads sem model state.val) (independent : ComponentsIndependent sem state.val first second)
    (typed : TypedFields sem final) :
    ∃ swappedMiddle swappedFinal,
      PaperTotal.Labeled.Step model secondRule second state.val swappedMiddle ∧
      PaperTotal.Labeled.Step model (Transposition.landedRule firstNext) first swappedMiddle swappedFinal ∧
      PaperStateObservation.Related sem swappedFinal final := by
  have firstStep : PaperTotal.Labeled.Step model (Transposition.landedRule firstNext) first state.val
      (mark stage first (Transposition.landedPhase firstNext firstInverse firstStack firstView)) := by
    have computed := advance_labeled model first firstCode firstStack firstView state.val left leftFound leftPhase leftTarget
    change PaperTotal.evaluate model.program model.draw model.failed first firstCode state.val = _ at firstLanding
    simpa only [advance, firstLanding] using computed
  have firstActive := Transposition.landedRule_activation firstNext
  have earlier : ∃ otherRule initial, Transposition.Activation otherRule ∧ PaperTotal.Labeled.Step model otherRule second state.val initial := by
    obtain ⟨initial, step⟩ := applicable
    exact ⟨secondRule, initial, secondActive, step⟩
  cases secondStep with
  | begin _ _ fiber view found inactive free target =>
    obtain ⟨swapped, begins, follows⟩ := activation_begin_diamond model draws failures firstStep firstActive
      (.begin _ second fiber view found inactive free target) (Ne.symm different) owned disjoint applicable
    exact ⟨swapped, _, begins, follows, typed_fields_self sem typed⟩
  | iter _ finalStage _ current code stack view inverse next found phase target landed =>
    obtain ⟨right, rightFound, rightPhase, rightTarget⟩ := landed_source_before model firstStep firstActive different
      current found code stack view phase earlier
    exact selected_landed_diamond sem model draws failures first second firstCode code state stage finalStage
      firstInverse inverse firstNext (some next) left right firstStack stack firstView view leftFound rightFound
      leftPhase rightPhase leftTarget rightTarget different heads independent firstLanding landed
  | finish _ finalStage _ current code stack view inverse found phase target landed =>
    obtain ⟨right, rightFound, rightPhase, rightTarget⟩ := landed_source_before model firstStep firstActive different
      current found code stack view phase earlier
    exact selected_landed_diamond sem model draws failures first second firstCode code state stage finalStage
      firstInverse inverse firstNext none left right firstStack stack firstView view leftFound rightFound
      leftPhase rightPhase leftTarget rightTarget different heads independent firstLanding landed
  | _ => simp [Transposition.Activation] at secondActive

/-- Original adjacent-pair form, all nine activation combinations. The three
semantic packages are explicit: original component independence with the p46
clause1 convention, current-head representation/reach, and stored function
typing. Earlier applicability is the ONLY assumed swapped applicability. -/
theorem activation_diamond (model : PaperTotal.Model Name Key Value Code Error)
    (draws : DrawByPresence model.draw) (failures : FailureByTables model.failed)
    {first second : Name} {firstRule secondRule : Labeled.Rule} (state : sem.Gamma) {middle final : R}
    (firstStep : PaperTotal.Labeled.Step model firstRule first state.val middle) (firstActive : Transposition.Activation firstRule)
    (secondStep : PaperTotal.Labeled.Step model secondRule second middle final) (secondActive : Transposition.Activation secondRule)
    (applicable : ∃ initial, PaperTotal.Labeled.Step model secondRule second state.val initial)
    (different : first ≠ second) (owned : Safety.Owned state.val) (disjoint : WellFormed.Disjoint state.val)
    (heads : CurrentHeads sem model state.val) (independent : ComponentsIndependent sem state.val first second)
    (typed : TypedFields sem final) :
    ∃ swappedMiddle swappedFinal,
      PaperTotal.Labeled.Step model secondRule second state.val swappedMiddle ∧
      PaperTotal.Labeled.Step model firstRule first swappedMiddle swappedFinal ∧
      PaperStateObservation.Related sem swappedFinal final := by
  cases firstStep with
  | begin _ _ fiber view found inactive free target =>
    obtain ⟨swapped, follows, begins⟩ := begin_activation_diamond model draws failures
      (.begin _ first fiber view found inactive free target) secondStep secondActive different
    exact ⟨swapped, _, follows, begins, typed_fields_self sem typed⟩
  | iter _ stage _ fiber code stack view inverse next found phase target landed =>
    exact landed_against_activation sem model draws failures state stack view landed fiber found phase target
      secondStep secondActive applicable different owned disjoint heads independent typed
  | finish _ stage _ fiber code stack view inverse found phase target landed =>
    exact landed_against_activation sem model draws failures state stack view landed fiber found phase target
      secondStep secondActive applicable different owned disjoint heads independent typed
  | _ => simp [Transposition.Activation] at firstActive

end
end Cordis.PaperTransposition
