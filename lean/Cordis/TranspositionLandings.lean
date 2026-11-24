import Cordis.TranspositionOperations
import Cordis.TranspositionStates

/-! All sixteen pairs of actual primitive constructors. The only semantic
premises concern individual value callbacks and same-key coeffect generators.
Fresh-name, declaration, routing, success, inverse and continuation obligations
are derived case-by-case from the original actual landings. -/
namespace Cordis.Transposition
open Calculus Stages Labeled StageRecovery AccumulatorProvenance Independence Effects
universe u
variable {Name Key Value Code Error : Type u}
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
variable [DecidableEq Name] [DecidableEq Key] [Setoid Value]
set_option linter.unusedSectionVars false

/-- Recovery and respect of each inverse actually returned by a value operation. -/
def CallbackWitness (program : Code → Instruction Name Key Value Code Error) (code : Code) : Prop :=
  ∀ key run, (program code).action = .operate key run →
    ∀ before after inverse result, run before = .ok (after, inverse, result) →
      inverse after ≈ before ∧ Effects.Respects inverse

def CallbackPair (program : Code → Instruction Name Key Value Code Error) (first second : Code) : Prop :=
  ∀ key left right, (program first).action = .operate key left →
    (program second).action = .operate key right →
    CallbackExchange left right

theorem landing_inverse_refl (program : Code → Instruction Name Key Value Code Error)
    {actor : Name} {code : Code} {r s : R} {inverse next}
    (land : Land program actor code r s inverse next) (witness : CallbackWitness program code) :
    StageSimulation.InverseRelated inverse inverse := by
  cases land with
  | unit => exact .unit
  | provide _ name _ fiber key value action found declared absent => exact .restrict actor key
  | instantiate _ _ _ component child action ready => exact .retire child
  | operate _ _ _ key run owner before after inv result action located called =>
    exact .operate owner key (witness key run action before after inv result called).2

structure Separated (left right : Component Key Code) : Prop where
  provisions : ∀ key, left.provides key = true → right.provides key = false
  left_provision : ∀ key, left.provides key = true → right.requires key = false
  right_provision : ∀ key, right.provides key = true → left.requires key = false

theorem Separated.symm {left right : Component Key Code} (separate : Separated left right) : Separated right left := by
  refine ⟨?_, separate.right_provision, separate.left_provision⟩
  intro key provided
  cases leftProvides : left.provides key with
  | false => rfl
  | true => simp [separate.provisions key leftProvides] at provided

/-- Actual primitive exchange, including all provision/operation/child mixtures.
The final state retains full control observation and table observation; each
returned inverse is related constructor-for-constructor with its original
capture. Actual reachable provenance supplies the source accumulator relation.
Phase-edit composition remains a separate obligation. -/
theorem landings_diamond (program : Code → Instruction Name Key Value Code Error)
    {first second : Name} {firstCode secondCode : Code} {r middle final : R}
    {firstInverse secondInverse : Inverse Name Key Value} {firstNext secondNext : Option Code}
    (firstLanding : Land program first firstCode r middle firstInverse firstNext)
    (secondLanding : Land program second secondCode middle final secondInverse secondNext)
    (left right : F) (leftFound : r first = some left) (rightFound : r second = some right)
    (different : first ≠ second) (disjoint : WellFormed.Disjoint r)
    (separate : Separated left.component right.component)
    (firstWitness : CallbackWitness program firstCode) (secondWitness : CallbackWitness program secondCode)
    (independent : CallbackPair program firstCode secondCode)
    (sourceSelf : StageSimulation.Related Eq r r) :
    ∃ swappedMiddle swappedFinal firstUndo secondUndo,
      Land program second secondCode r swappedMiddle secondUndo secondNext ∧
      Land program first firstCode swappedMiddle swappedFinal firstUndo firstNext ∧
      StageSimulation.Related Eq swappedFinal final ∧
      StageSimulation.InverseRelated secondUndo secondInverse ∧
      StageSimulation.InverseRelated firstUndo firstInverse := by
  have originalFirst := firstLanding
  have finalSelf := landing_self_related program secondLanding (landing_self_related program firstLanding sourceSelf)
  have firstReflexive := landing_inverse_refl program firstLanding firstWitness
  have secondReflexive := landing_inverse_refl program secondLanding secondWitness
  cases firstLanding with
  | unit _ _ _ action =>
    exact ⟨final, final, .unit, secondInverse, secondLanding, .unit final first firstCode action,
      finalSelf, secondReflexive, .unit⟩
  | provide _ _ _ fiber key value action found declared absent =>
    have same : fiber = left := Option.some.inj (found.symm.trans leftFound)
    subst fiber
    obtain ⟨swapped, secondMove, firstMove⟩ := provision_landing_diamond program r first second left right
      leftFound rightFound (Ne.symm different) key value firstCode secondCode action declared absent
      (separate.provisions key declared) (separate.left_provision key declared) secondLanding
    exact ⟨swapped, final, .restrict first key, secondInverse, secondMove, firstMove,
      finalSelf, secondReflexive, .restrict first key⟩
  | instantiate _ _ _ component child action ready =>
    obtain ⟨swapped, secondMove, firstMove⟩ := instantiation_landing_diamond program r first child second component
      firstCode secondCode right rightFound action ready disjoint secondLanding
    exact ⟨swapped, final, .retire child, secondInverse, secondMove, firstMove,
      finalSelf, secondReflexive, .retire child⟩
  | operate _ _ _ key run owner before after inv result action located called =>
    cases secondLanding with
    | unit _ _ _ secondAction =>
      exact ⟨r, write r owner key (some after), .operate owner key inv, .unit,
        .unit r second secondCode secondAction, originalFirst,
        finalSelf, .unit, firstReflexive⟩
    | provide _ _ _ current query value secondAction currentFound declared absent =>
      obtain ⟨afterEntry, afterFound, component, _⟩ :=
        Ordering.land_existing_control program originalFirst second right rightFound
      have same : afterEntry = current := Option.some.inj (afterFound.symm.trans currentFound)
      subst afterEntry
      have originalDeclared : right.component.provides query = true := by simpa [component] using declared
      obtain ⟨swapped, secondMove, firstMove⟩ := landing_provision_diamond program originalFirst second left right current
        leftFound rightFound currentFound different query value secondCode secondAction declared absent
        (separate.symm.provisions query originalDeclared) (separate.right_provision query originalDeclared)
      exact ⟨swapped, _, .operate owner key inv, .restrict second query, secondMove, firstMove,
        finalSelf, .restrict second query, firstReflexive⟩
    | instantiate _ _ _ component child secondAction ready =>
      obtain ⟨swapped, secondMove, firstMove⟩ := landing_instantiation_diamond program originalFirst second child component
        secondCode left leftFound (by simp [rightFound]) secondAction ready
      exact ⟨swapped, _, .operate owner key inv, .retire child, secondMove, firstMove,
        finalSelf, .retire child, firstReflexive⟩
    | operate _ _ _ query otherRun other otherBefore finalValue otherInv otherResult secondAction secondLocated secondCalled =>
      obtain ⟨swappedMiddle, swappedFinal, firstUndo, secondUndo, secondMove, firstMove,
        tables, secondRelated, firstRelated⟩ :=
        operations_landing_diamond program r first second owner other key query firstCode secondCode run otherRun
          action secondAction (by intro keys; subst query; exact independent key run otherRun action secondAction)
          before after otherBefore finalValue inv otherInv result otherResult located called secondLocated secondCalled
          (firstWitness key run action before after inv result called).2
          (secondWitness query otherRun secondAction otherBefore finalValue otherInv otherResult secondCalled).2
      have originalControls := controls_trans (write_controls r owner key (some after))
        (write_controls (write r owner key (some after)) other query (some finalValue))
      have swappedControls := controls_trans (operation_controls program secondMove query otherRun secondAction)
        (operation_controls program firstMove key run action)
      exact ⟨swappedMiddle, swappedFinal, firstUndo, secondUndo, secondMove, firstMove,
        related_of_controls_tables (controls_trans (controls_symm swappedControls) originalControls) tables finalSelf,
        secondRelated, firstRelated⟩

end Cordis.Transposition
