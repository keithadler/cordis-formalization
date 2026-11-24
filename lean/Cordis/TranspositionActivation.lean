import Cordis.TranspositionLandings

/-! Composition of primitive exchanges with the actual activation phase edits.
The callback outcome fixes the rule and next code in both orders. Old captured
stacks are related using reachable provenance; newly captured inverses come
from the primitive diamond, rather than an assumed whole-step diamond. -/
namespace Cordis.Transposition
open Calculus Stages Labeled StageRecovery AccumulatorProvenance
universe u
variable {Name Key Value Code Error : Type u}
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
variable [DecidableEq Name] [DecidableEq Key]
set_option linter.unusedSectionVars false

def landedRule : Option Code → Rule
  | none => .finish
  | some _ => .iter

def landedPhase (next : Option Code) (inverse : Inverse Name Key Value)
    (accumulator : List (Inverse Name Key Value)) (view : View Name Key) :
    Phase Name Key Code (Inverse Name Key Value) :=
  match next with
  | none => .active (inverse :: accumulator) view
  | some code => .reloading code (inverse :: accumulator) view

theorem landedRule_activation (next : Option Code) : Activation (landedRule next) := by
  cases next <;> simp [landedRule, Activation]

theorem landed_step (program : Code → Instruction Name Key Value Code Error)
    {actor : Name} {code : Code} {r s : R} {inverse next}
    (fiber : F) (accumulator : List (Inverse Name Key Value)) (view : View Name Key)
    (found : r actor = some fiber) (phase : fiber.phase = .reloading code accumulator view)
    (target : Target r actor view) (land : Land program actor code r s inverse next) :
    Labeled.Step program (landedRule next) actor r (mark s actor (landedPhase next inverse accumulator view)) := by
  cases next with
  | none => exact .finish r s actor fiber code accumulator view inverse found phase target land
  | some next => exact .iter r s actor fiber code accumulator view inverse next found phase target land

theorem targets_separate (r : R) (first second : Name) (left right : F)
    (leftFound : r first = some left) (rightFound : r second = some right)
    (different : first ≠ second) (owned : Safety.Owned r) (disjoint : WellFormed.Disjoint r)
    (leftUnavailable : ¬ left.phase.available) (rightUnavailable : ¬ right.phase.available)
    (leftView rightView : View Name Key) (leftTarget : Target r first leftView) (rightTarget : Target r second rightView) :
    Separated left.component right.component := by
  constructor
  · intro key provided
    cases other : right.component.provides key with
    | false => rfl
    | true => exact False.elim (disjoint first second left right leftFound rightFound different key ⟨provided, other⟩)
  · exact unavailable_provision_not_required r first second left right leftFound rightFound owned disjoint
      leftUnavailable rightView rightTarget
  · exact unavailable_provision_not_required r second first right left rightFound leftFound owned disjoint
      rightUnavailable leftView leftTarget

/-- An initially applicable foreign activation supplies precisely the stored
code, stack and view used by a later landed activation. A foreign activation
cannot turn an inactive actor into a reloading actor. -/
theorem landed_source_before_activation (program : Code → Instruction Name Key Value Code Error)
    {first second : Name} {rule : Rule} {r middle : R}
    (firstStep : Labeled.Step program rule first r middle) (active : Activation rule)
    (different : first ≠ second) (current : F) (found : middle second = some current)
    (code accumulator view) (phase : current.phase = .reloading code accumulator view)
    (applicable : ∃ otherRule before, Activation otherRule ∧ Labeled.Step program otherRule second r before) :
    ∃ original : F, r second = some original ∧ original.phase = .reloading code accumulator view ∧ Target r second view := by
  obtain ⟨otherRule, before, otherActive, otherStep⟩ := applicable
  obtain ⟨original, originalView, originalFound, unavailable, target⟩ := activation_source program otherStep otherActive
  obtain ⟨table, afterFound⟩ := activation_other_table program firstStep active second original (Ne.symm different) originalFound
  have same : {original with table := table} = current := Option.some.inj (afterFound.symm.trans found)
  have originalPhase : original.phase = .reloading code accumulator view := by
    have fields := congrArg Fiber.phase same
    exact fields.trans phase
  refine ⟨original, originalFound, originalPhase, ?_⟩
  cases otherStep with
  | begin _ _ fiber selected present inactive free ownTarget =>
    have equal : fiber = original := Option.some.inj (present.symm.trans originalFound)
    subst fiber
    rw [originalPhase] at inactive
    cases inactive
  | iter _ stage _ fiber c a selected inverse next present reloading ownTarget land =>
    have equal : fiber = original := Option.some.inj (present.symm.trans originalFound)
    subst fiber
    rw [originalPhase] at reloading
    cases reloading
    exact ownTarget
  | finish _ stage _ fiber c a selected inverse present reloading ownTarget land =>
    have equal : fiber = original := Option.some.inj (present.symm.trans originalFound)
    subst fiber
    rw [originalPhase] at reloading
    cases reloading
    exact ownTarget
  | _ => simp [Activation] at otherActive

section Observation
variable [Setoid Value]

/-- The coeffect contract is needed only for the two currently installed heads
and only when both actually name the same key. It says nothing about registry
maps, phase edits, or existence of either swapped transition. -/
def CurrentCallbackPair (program : Code → Instruction Name Key Value Code Error)
    (r : R) (first second : Name) : Prop :=
  ∀ left right firstCode secondCode firstAccumulator secondAccumulator firstView secondView,
    r first = some left → r second = some right →
    left.phase = .reloading firstCode firstAccumulator firstView →
    right.phase = .reloading secondCode secondAccumulator secondView →
    CallbackPair program firstCode secondCode

omit [Setoid Value] in
theorem reachable_owned (program : Code → Instruction Name Key Value Code Error)
    {r : R} (reached : WellFormed.Run program (fun _ => none) r) : Safety.Owned r := by
  have preserve : ∀ {a b : R}, WellFormed.Run program a b → Safety.Owned a → Safety.Owned b := by
    intro a b run owned
    induction run with
    | refl => exact owned
    | step _ step ih => exact Safety.step_owned program step ih
  exact preserve reached Safety.empty_owned

theorem self_reloading_stack {r : R} (self : StageSimulation.Related Eq r r)
    (actor : Name) (fiber : F) (found : r actor = some fiber) (code accumulator view)
    (phase : fiber.phase = .reloading code accumulator view) : StageSimulation.StackRelated accumulator accumulator := by
  have related : StageSimulation.FiberRelated Eq fiber fiber := by
    simpa only [found, Iterators.OptionRel] using self actor
  have phases := related.phase
  rw [phase] at phases
  cases phases
  assumption

theorem landed_phases_related (next : Option Code) {first second : Inverse Name Key Value}
    (inverse : StageSimulation.InverseRelated first second)
    (accumulator : List (Inverse Name Key Value)) (self : StageSimulation.StackRelated accumulator accumulator)
    (view : View Name Key) :
    StageSimulation.PhaseRelated Eq (landedPhase next first accumulator view) (landedPhase next second accumulator view) := by
  cases next with
  | none => exact .active view (.cons inverse self)
  | some code => exact .reloading view rfl (.cons inverse self)

/-- A primitive pair yields two actual swapped activation rules. Both phase
edits install the original outcome-selected next code and the newly captured
inverse. All four combinations of Iter/Finish are covered by `next`. -/
theorem landed_phase_diamond (program : Code → Instruction Name Key Value Code Error)
    {first second : Name} {firstCode secondCode : Code} {r middle final : R}
    {firstInverse secondInverse : Inverse Name Key Value} {firstNext secondNext : Option Code}
    (firstLanding : Land program first firstCode r middle firstInverse firstNext)
    (secondLanding : Land program second secondCode middle final secondInverse secondNext)
    (left right : F) (leftFound : r first = some left) (rightFound : r second = some right)
    (firstAccumulator secondAccumulator : List (Inverse Name Key Value)) (firstView secondView : View Name Key)
    (leftPhase : left.phase = .reloading firstCode firstAccumulator firstView)
    (rightPhase : right.phase = .reloading secondCode secondAccumulator secondView)
    (leftTarget : Target r first firstView) (rightTarget : Target r second secondView)
    (different : first ≠ second) (owned : Safety.Owned r) (disjoint : WellFormed.Disjoint r)
    (firstWitness : CallbackWitness program firstCode) (secondWitness : CallbackWitness program secondCode)
    (independent : CallbackPair program firstCode secondCode) (sourceSelf : StageSimulation.Related Eq r r) :
    ∃ swappedMiddle swappedFinal,
      Labeled.Step program (landedRule secondNext) second r swappedMiddle ∧
      Labeled.Step program (landedRule firstNext) first swappedMiddle swappedFinal ∧
      StageSimulation.Related Eq swappedFinal
        (mark (mark final first (landedPhase firstNext firstInverse firstAccumulator firstView))
          second (landedPhase secondNext secondInverse secondAccumulator secondView)) := by
  have separate := targets_separate r first second left right leftFound rightFound different owned disjoint
    (by simp [leftPhase, Phase.available]) (by simp [rightPhase, Phase.available])
    firstView secondView leftTarget rightTarget
  obtain ⟨swappedMiddle, swappedFinal, firstUndo, secondUndo, secondMove, firstMove,
    states, secondRelated, firstRelated⟩ := landings_diamond program firstLanding secondLanding
      left right leftFound rightFound different disjoint separate firstWitness secondWitness independent sourceSelf
  have secondStep := landed_step program right secondAccumulator secondView rightFound rightPhase rightTarget secondMove
  have afterTarget := activation_target_forward program secondStep (landedRule_activation secondNext)
    first firstView different leftTarget
  obtain ⟨table, currentFound⟩ := land_existing_table program secondMove first left leftFound
  have firstMarked := land_mark program firstMove second (landedPhase secondNext secondUndo secondAccumulator secondView)
    different (by obtain ⟨table, found⟩ := land_existing_table program secondMove second right rightFound; simp [found])
  have firstStep := landed_step program {left with table := table} firstAccumulator firstView
    ((mark_other _ _ _ _ different).trans currentFound) leftPhase afterTarget firstMarked
  refine ⟨_, _, secondStep, firstStep, ?_⟩
  have firstStack := self_reloading_stack sourceSelf first left leftFound firstCode firstAccumulator firstView leftPhase
  have secondStack := self_reloading_stack sourceSelf second right rightFound secondCode secondAccumulator secondView rightPhase
  have firstMarkedRelated := StageSimulation.mark_related states first
    (landed_phases_related firstNext firstRelated firstAccumulator firstStack firstView)
  have both := StageSimulation.mark_related firstMarkedRelated second
    (landed_phases_related secondNext secondRelated secondAccumulator secondStack secondView)
  simpa only [marks_commute _ first second _ _ different] using both

/-- The same diamond with the first actor's actual phase edit already present
at the second landing. That edit is stripped using the literal control frame,
then reinstalled after the primitive exchange. -/
theorem landed_activation_diamond (program : Code → Instruction Name Key Value Code Error)
    {first second : Name} {firstCode secondCode : Code} {r middle final : R}
    {firstInverse secondInverse : Inverse Name Key Value} {firstNext secondNext : Option Code}
    (firstAccumulator secondAccumulator : List (Inverse Name Key Value)) (firstView secondView : View Name Key)
    (firstLanding : Land program first firstCode r middle firstInverse firstNext)
    (secondLanding : Land program second secondCode
      (mark middle first (landedPhase firstNext firstInverse firstAccumulator firstView)) final secondInverse secondNext)
    (left right : F) (leftFound : r first = some left) (rightFound : r second = some right)
    (leftPhase : left.phase = .reloading firstCode firstAccumulator firstView)
    (rightPhase : right.phase = .reloading secondCode secondAccumulator secondView)
    (leftTarget : Target r first firstView) (rightTarget : Target r second secondView)
    (different : first ≠ second) (owned : Safety.Owned r) (disjoint : WellFormed.Disjoint r)
    (firstWitness : CallbackWitness program firstCode) (secondWitness : CallbackWitness program secondCode)
    (independent : CallbackPair program firstCode secondCode) (sourceSelf : StageSimulation.Related Eq r r) :
    ∃ swappedMiddle swappedFinal,
      Labeled.Step program (landedRule secondNext) second r swappedMiddle ∧
      Labeled.Step program (landedRule firstNext) first swappedMiddle swappedFinal ∧
      StageSimulation.Related Eq swappedFinal
        (mark final second (landedPhase secondNext secondInverse secondAccumulator secondView)) := by
  obtain ⟨table, currentFound⟩ := land_existing_table program firstLanding first left leftFound
  let current : F := {left with table := table, phase := landedPhase firstNext firstInverse firstAccumulator firstView}
  have markedFound : mark middle first (landedPhase firstNext firstInverse firstAccumulator firstView) first = some current := by
    simp [mark, Calculus.modify, currentFound, current]
  have restoreSource : mark (mark middle first (landedPhase firstNext firstInverse firstAccumulator firstView)) first left.phase = middle := by
    rw [mark_twice]
    exact mark_existing middle first {left with table := table} currentFound
  have unmarked := land_mark program secondLanding first left.phase (Ne.symm different) (by simp [markedFound])
  rw [restoreSource] at unmarked
  obtain ⟨newTable, finalFound⟩ := land_existing_table program secondLanding first current markedFound
  have restoreFinal : mark final first (landedPhase firstNext firstInverse firstAccumulator firstView) = final :=
    mark_existing final first {current with table := newTable} finalFound
  obtain ⟨swappedMiddle, swappedFinal, secondStep, firstStep, related⟩ :=
    landed_phase_diamond program firstLanding unmarked left right leftFound rightFound
      firstAccumulator secondAccumulator firstView secondView leftPhase rightPhase leftTarget rightTarget
      different owned disjoint firstWitness secondWitness independent sourceSelf
  exact ⟨swappedMiddle, swappedFinal, secondStep, firstStep,
    by simpa only [mark_twice, restoreFinal] using related⟩

/-- First activation is a landed rule; the second may be Begin, Iter, or
Finish. For a later landing only the source control fields and target are
needed. Its earlier successful call is constructed by the primitive diamond. -/
private theorem landed_against_activation_of_sources (program : Code → Instruction Name Key Value Code Error)
    {first second : Name} {firstCode : Code} {r middle final : R}
    {firstInverse : Inverse Name Key Value} {firstNext : Option Code} {secondRule : Rule}
    (firstAccumulator : List (Inverse Name Key Value)) (firstView : View Name Key)
    (firstLanding : Land program first firstCode r middle firstInverse firstNext)
    (left : F) (leftFound : r first = some left)
    (leftPhase : left.phase = .reloading firstCode firstAccumulator firstView)
    (leftTarget : Target r first firstView)
    (secondStep : Labeled.Step program secondRule second
      (mark middle first (landedPhase firstNext firstInverse firstAccumulator firstView)) final)
    (secondActive : Activation secondRule)
    (beginReady : secondRule = .begin → ∃ before, Labeled.Step program .begin second r before)
    (landedReady : secondRule ≠ .begin → ∀ current code accumulator view,
      (mark middle first (landedPhase firstNext firstInverse firstAccumulator firstView)) second = some current →
      current.phase = .reloading code accumulator view →
      Target (mark middle first (landedPhase firstNext firstInverse firstAccumulator firstView)) second view →
      ∃ original : F, r second = some original ∧
        original.phase = .reloading code accumulator view ∧ Target r second view)
    (different : first ≠ second) (owned : Safety.Owned r) (disjoint : WellFormed.Disjoint r)
    (callbacks : ∀ code, CallbackWitness program code) (independent : CurrentCallbackPair program r first second)
    (sourceSelf : StageSimulation.Related Eq r r) (finalSelf : StageSimulation.Related Eq final final) :
    ∃ swappedMiddle swappedFinal,
      Labeled.Step program secondRule second r swappedMiddle ∧
      Labeled.Step program (landedRule firstNext) first swappedMiddle swappedFinal ∧
      StageSimulation.Related Eq swappedFinal final := by
  have firstStep := landed_step program left firstAccumulator firstView leftFound leftPhase leftTarget firstLanding
  have firstActive := landedRule_activation firstNext
  cases secondStep with
  | begin _ _ fiber view found inactive free target =>
    obtain ⟨swapped, begins, follows⟩ := activation_begin_diamond_of_applicable program firstStep firstActive
      (.begin _ second fiber view found inactive free target) (Ne.symm different) owned disjoint (beginReady rfl)
    exact ⟨swapped, _, begins, follows, finalSelf⟩
  | iter _ stage _ current code accumulator view inverse next found phase target land =>
    obtain ⟨right, rightFound, rightPhase, rightTarget⟩ :=
      landedReady (by decide) current code accumulator view found phase target
    exact landed_activation_diamond program firstAccumulator accumulator firstView view firstLanding land
      left right leftFound rightFound leftPhase rightPhase leftTarget rightTarget different owned disjoint
      (callbacks firstCode) (callbacks code)
      (independent left right firstCode code firstAccumulator accumulator firstView view leftFound rightFound leftPhase rightPhase) sourceSelf
  | finish _ stage _ current code accumulator view inverse found phase target land =>
    obtain ⟨right, rightFound, rightPhase, rightTarget⟩ :=
      landedReady (by decide) current code accumulator view found phase target
    exact landed_activation_diamond program firstAccumulator accumulator firstView view firstLanding land
      left right leftFound rightFound leftPhase rightPhase leftTarget rightTarget different owned disjoint
      (callbacks firstCode) (callbacks code)
      (independent left right firstCode code firstAccumulator accumulator firstView view leftFound rightFound leftPhase rightPhase) sourceSelf
  | _ => simp [Activation] at secondActive

/-- Earlier applicability supplies the source controls for the landed
activation cases of Lemma 78. -/
theorem landed_against_activation (program : Code → Instruction Name Key Value Code Error)
    {first second : Name} {firstCode : Code} {r middle final : R}
    {firstInverse : Inverse Name Key Value} {firstNext : Option Code} {secondRule : Rule}
    (firstAccumulator : List (Inverse Name Key Value)) (firstView : View Name Key)
    (firstLanding : Land program first firstCode r middle firstInverse firstNext)
    (left : F) (leftFound : r first = some left)
    (leftPhase : left.phase = .reloading firstCode firstAccumulator firstView)
    (leftTarget : Target r first firstView)
    (secondStep : Labeled.Step program secondRule second
      (mark middle first (landedPhase firstNext firstInverse firstAccumulator firstView)) final)
    (secondActive : Activation secondRule)
    (applicable : ∃ before, Labeled.Step program secondRule second r before)
    (different : first ≠ second) (owned : Safety.Owned r) (disjoint : WellFormed.Disjoint r)
    (callbacks : ∀ code, CallbackWitness program code) (independent : CurrentCallbackPair program r first second)
    (sourceSelf : StageSimulation.Related Eq r r) (finalSelf : StageSimulation.Related Eq final final) :
    ∃ swappedMiddle swappedFinal,
      Labeled.Step program secondRule second r swappedMiddle ∧
      Labeled.Step program (landedRule firstNext) first swappedMiddle swappedFinal ∧
      StageSimulation.Related Eq swappedFinal final := by
  apply landed_against_activation_of_sources program firstAccumulator firstView firstLanding left leftFound
    leftPhase leftTarget secondStep secondActive _ _ different owned disjoint callbacks independent sourceSelf finalSelf
  · intro beginRule
    exact beginRule ▸ applicable
  · intro _ current code accumulator view found phase _
    obtain ⟨before, earlier⟩ := applicable
    exact landed_source_before_activation program
      (landed_step program left firstAccumulator firstView leftFound leftPhase leftTarget firstLanding)
      (landedRule_activation firstNext) different current found code accumulator view phase
      ⟨secondRule, before, secondActive, earlier⟩

/-- Actual activation transposition using a legal earlier Begin or only an
earlier control state and target for Iter and Finish. -/
theorem activation_diamond_of_sources (program : Code → Instruction Name Key Value Code Error)
    {first second : Name} {firstRule secondRule : Rule} {r middle final : R}
    (firstStep : Labeled.Step program firstRule first r middle) (firstActive : Activation firstRule)
    (secondStep : Labeled.Step program secondRule second middle final) (secondActive : Activation secondRule)
    (beginReady : secondRule = .begin → ∃ before, Labeled.Step program .begin second r before)
    (landedReady : secondRule ≠ .begin → ∀ current code accumulator view,
      middle second = some current → current.phase = .reloading code accumulator view →
      Target middle second view →
      ∃ original : F, r second = some original ∧
        original.phase = .reloading code accumulator view ∧ Target r second view)
    (different : first ≠ second) (reached : WellFormed.Run program (fun _ => none) r)
    (callbacks : ∀ code, CallbackWitness program code) (independent : CurrentCallbackPair program r first second) :
    ∃ swappedMiddle swappedFinal,
      Labeled.Step program secondRule second r swappedMiddle ∧
      Labeled.Step program firstRule first swappedMiddle swappedFinal ∧
      StageSimulation.Related Eq swappedFinal final := by
  have witnesses : OperationWitnesses program := callbacks
  have sourceSelf := reachable_self_related program witnesses reached
  have finalSelf := reachable_self_related program witnesses (.step (.step reached firstStep.toCalculus) secondStep.toCalculus)
  have owned := reachable_owned program reached
  have disjoint := (WellFormed.run_invariants program reached Safety.empty_parentClosed WellFormed.disjoint_empty
    ⟨Ordering.supported_empty, Ordering.local_empty⟩).2.1
  cases firstStep with
  | begin _ _ fiber view found inactive free target =>
    obtain ⟨swapped, follows, begins⟩ := begin_activation_diamond program
      (.begin _ first fiber view found inactive free target) secondStep secondActive different
    exact ⟨swapped, _, follows, begins, finalSelf⟩
  | iter _ stage _ fiber code accumulator view inverse next found phase target land =>
    exact landed_against_activation_of_sources program accumulator view land fiber found phase target secondStep secondActive
      beginReady landedReady different owned disjoint callbacks independent sourceSelf finalSelf
  | finish _ stage _ fiber code accumulator view inverse found phase target land =>
    exact landed_against_activation_of_sources program accumulator view land fiber found phase target secondStep secondActive
      beginReady landedReady different owned disjoint callbacks independent sourceSelf finalSelf
  | _ => simp [Activation] at firstActive

/-- Lemma 78(1) with earlier applicability stated as a legal earlier step. -/
theorem activation_diamond (program : Code → Instruction Name Key Value Code Error)
    {first second : Name} {firstRule secondRule : Rule} {r middle final : R}
    (firstStep : Labeled.Step program firstRule first r middle) (firstActive : Activation firstRule)
    (secondStep : Labeled.Step program secondRule second middle final) (secondActive : Activation secondRule)
    (applicable : ∃ before, Labeled.Step program secondRule second r before)
    (different : first ≠ second) (reached : WellFormed.Run program (fun _ => none) r)
    (callbacks : ∀ code, CallbackWitness program code) (independent : CurrentCallbackPair program r first second) :
    ∃ swappedMiddle swappedFinal,
      Labeled.Step program secondRule second r swappedMiddle ∧
      Labeled.Step program firstRule first swappedMiddle swappedFinal ∧
      StageSimulation.Related Eq swappedFinal final := by
  apply activation_diamond_of_sources program firstStep firstActive secondStep secondActive _ _ different reached callbacks independent
  · intro beginRule
    exact beginRule ▸ applicable
  · intro _ current code accumulator view found phase _
    obtain ⟨before, earlier⟩ := applicable
    exact landed_source_before_activation program firstStep firstActive different current found code accumulator view phase
      ⟨secondRule, before, secondActive, earlier⟩

end Observation
end Cordis.Transposition
