import Cordis.Eq54IdentificationObstruction
import Cordis.VestigialAdmissionBoundary
import Cordis.PairwiseBirthExamples
import Cordis.PaperRemainingClaims
import Cordis.Results.Context

/-! Counterexamples to the registry lemmas of Section 4.

The examples for Lemmas 57, 60, 61, 62 and 66 run over finite rooted
registries with an unbounded name supply. Empty coeffect keys retain
all name, control, and iterator observations needed by the examples.
-/

namespace Cordis.Results
open Calculus Stages Iterators
open RenamingLiteral (Gamma FiniteDomain Name R Code)
open RenamingLiteralExamples (rootName childName program permutation r5 r6 unload_step)
noncomputable section

/-- The unrestricted recovery target refutes the full printed Lemma 38. -/
theorem lemma38_counterexample :
    ¬ PaperRemainingClaims.lemma38 (Γ := ObservationLiftingExamples.State) :=
  fun claimed => lemma38_unrestricted_refuted claimed.2.2.2.1

/-- The unit/instantiation universe interprets whole accumulator maps and
iterators over the all-key table observation of Equations (33) and (54). -/
def emptyKeySemantics : PaperStateObservation.Semantics Name Empty Unit Code Empty where
  domain state := Safety.Tree state ∧ FiniteDomain state
  iterator actor := Eq54FixedBase.meaning actor Eq54FixedBaseExamples.draw
  undo := Stages.undo
  undo_closed token state admitted := by
    rw [← Eq54FixedBase.undoGamma_actual token (⟨state, admitted⟩ : Gamma)]
    exact (Eq54FixedBase.undoGamma token ⟨state, admitted⟩).property
  undo_unit _ := rfl
  undo_retire _ _ := rfl
  keyObservation key := nomatch key

open Eq54FixedBaseExamples in
private theorem emptyKeyInputsRelated :
    PaperTraceEquations.StateEquivalent emptyKeySemantics
      Eq54FixedBaseExamples.unitGamma Eq54FixedBaseExamples.birthGamma := by
  refine ⟨(fun key => nomatch key), ?_⟩
  intro actor
  by_cases acting : actor = rootName
  · subst actor
    have anyCode (left right : Code) :
        PaperStateObservation.CodeRelated emptyKeySemantics rootName left right := by
      cases left <;> cases right <;>
        apply @related_fold _ (PaperStateObservation.base emptyKeySemantics) <;>
        exact fun left right _ =>
          ⟨(fun key => nomatch key), (fun {_ _} _ key => nomatch key), True.intro⟩
    have emptyStacks :
        PaperStateObservation.AccumulatorRelated emptyKeySemantics [] [] := fun {_ _} observed => observed
    change OptionRel (PaperStateObservation.FiberRelated emptyKeySemantics rootName)
      (unitBefore rootName) (birthBefore rootName)
    simp only [unitBefore, unitInserted, birthBefore, RenamingLiteralExamples.r2,
      RenamingLiteralExamples.r1, mark, Calculus.modify, put, OptionRel]
    exact ⟨rfl, rfl, anyCode _ _, rfl, rfl,
      .reloading (anyCode _ _) emptyStacks (fun key => nomatch key)⟩
  · change OptionRel (PaperStateObservation.FiberRelated emptyKeySemantics actor)
      (unitBefore actor) (birthBefore actor)
    simp [unitBefore, unitInserted, birthBefore, RenamingLiteralExamples.r2,
      RenamingLiteralExamples.r1, RenamingLiteralExamples.r0, mark, Calculus.modify, put, acting, OptionRel]

open Eq54FixedBaseExamples in
/-- The literal Eq. (54) matches the inputs of unit and birth Finish, while
every possible birth Finish adds a name that unit Finish leaves absent. -/
theorem lemma60_counterexample :
    ¬ PaperLifecycleClaims.lemma60 program emptyKeySemantics := by
  intro simulate
  let after : emptyKeySemantics.Gamma :=
    ⟨unitAfter, Safety.step_tree program unit_finish.toCalculus unit_before_reachable.reachable_invariants.1,
      RenamingLiteral.modify_finite unitBefore rootName _ unit_finite⟩
  obtain ⟨other, finish, related⟩ :=
    (simulate unitGamma birthGamma .finish rootName emptyKeyInputsRelated).1 after unit_finish
  obtain ⟨name, missing, present⟩ :=
    Eq54IdentificationObstruction.every_birth_finish_changes_domain other.val finish
  exact present ((PaperStateObservation.domain_agrees emptyKeySemantics related name).mp missing)

/-- The displayed name action leaves the old child in the retirement inverse. -/
theorem lemma61_counterexample :
    ¬ PaperRemainingClaims.lemma61 program emptyKeySemantics := by
  intro equivariant
  let after : emptyKeySemantics.Gamma := ⟨r6, VestigialAdmissionBoundary.endpoint_admissible⟩
  have renamed := ((equivariant permutation).2
    RenamingLiteralExamples.beforeGamma after .unload rootName).mp unload_step
  have literalAction (state : R) :
      PaperRemainingClaims.literalRename permutation state = RenamingLiteral.registry permutation state := by
    funext name
    unfold PaperRemainingClaims.literalRename RenamingLiteral.registry
    cases state (permutation.invFun name) with
    | none => rfl
    | some entry => cases phase : entry.phase <;> simp [RenamingLiteral.fiber, RenamingLiteral.phase, phase]
  rw [literalAction, literalAction] at renamed
  exact RenamingLiteralExamples.literal_unload_transport_fails renamed

/-- Removing a vestigial child enables O-Remove of its parent, without either
of the paper's stated O-Insert exceptions. -/
theorem lemma62_counterexample :
    ¬ PaperRemainingClaims.lemma62 program emptyKeySemantics := by
  intro vestigial
  let final : emptyKeySemantics.Gamma := ⟨r6, VestigialAdmissionBoundary.endpoint_admissible⟩
  have noInsertion :
      ¬ PaperRemainingClaims.insertionConflict r6 childName .remove rootName
        (erase (erase r6 childName) rootName) := by
    intro conflict
    cases conflict.1
  obtain ⟨original, remove, _⟩ :=
    (vestigial final childName VestigialAdmissionBoundary.child_vestigial).2
      rootName .remove (by decide) |>.2 _ VestigialAdmissionBoundary.remove_after_erasure noInsertion
  exact VestigialAdmissionBoundary.no_remove_before original remove

/-- Exact repair of the missing O-Remove guard for a distinct actor. The
erased entry is the only possible parent pointer restored by reversal. -/
theorem removable_after_erasing_iff
    {N K V C U E : Type} [DecidableEq N]
    (state : Registry N K V C U E) {forgotten actor : N} (distinct : actor ≠ forgotten) :
    Removable state actor ↔ Removable (erase state forgotten) actor ∧
      ∀ entry, state forgotten = some entry → entry.parent ≠ some actor := by
  cases found : state actor with
  | none =>
    simp [Removable, erase, distinct, found]
  | some actorEntry =>
    simp only [Removable, erase, if_neg distinct, found]
    constructor
    · rintro ⟨retired, inactive, empty, noChildren⟩
      refine ⟨⟨retired, inactive, empty, ?_⟩, ?_⟩
      · intro child
        by_cases erased : child = forgotten
        · simp [erased]
        · simpa only [if_neg erased] using noChildren child
      · intro entry present
        simpa only [present] using noChildren forgotten
    · rintro ⟨⟨retired, inactive, empty, noChildren⟩, forgottenIsNotChild⟩
      refine ⟨retired, inactive, empty, ?_⟩
      intro child
      by_cases erased : child = forgotten
      · subst child
        cases present : state forgotten with
        | none => trivial
        | some entry => exact forgottenIsNotChild entry present
      · simpa only [if_neg erased] using noChildren child

/-- Definition 65's extra observation of the component named by an
instantiation is incompatible with foreign-yield stability in this trace. -/
theorem lemma66_component_observation_counterexample
    (relation : PairwiseBirthSemantics.Code → PairwiseBirthSemantics.Code → Prop)
    (observes : PairwiseBirthBoundary.ObservesComponents relation) :
    ¬ PairwiseBirthBoundary.RootYieldStable relation :=
  PairwiseBirthBoundary.no_component_observing_yield_stability relation observes

namespace BirthCounterexample

local notation "BirthCode" => PairwiseBirthSemantics.Code
local notation "BirthState" => PairwiseBirthSemantics.Gamma
open PairwiseBirthSemantics (birthEffect draw component retireGamma)

private def follow (name : Nat) : BirthCode :=
  if name = 2 then .tailShort else .twoBirths

/-- The selected child name chooses between a one-birth and a two-birth tail. -/
def branchingProgram : BirthCode → Instruction Nat Empty Unit BirthCode Empty
  | .parent => ⟨.instantiate (component .unit), fun result =>
      match result with
      | .child name => some (follow name)
      | _ => none⟩
  | code => PairwiseBirthSemantics.program code

private def meaning (actor : Nat) : BirthCode → Iterator BirthState
  | .parent => .node (birthEffect actor (component .unit))
      (fun state => some (PairwiseBirthSemantics.meaning actor (follow (draw state))))
  | code => PairwiseBirthSemantics.meaning actor code

def semantics : PaperStateObservation.Semantics Nat Empty Unit BirthCode Empty where
  domain state := Safety.Tree state ∧ SupportUniqueness.FiniteDomain state
  iterator := meaning
  undo := Stages.undo
  undo_closed token state legal := by
    cases token with
    | unit => exact legal
    | retire child => exact (retireGamma child ⟨state, legal⟩).property
    | restrict _ key => exact nomatch key
    | operate _ key _ => exact nomatch key
  undo_unit _ := rfl
  undo_retire _ _ := rfl
  keyObservation key := nomatch key

private def birthComponent (head : Iterator semantics.Gamma) : Option (Component Empty BirthCode) := by
  classical
  exact if head = PairwiseBirthSemantics.unitIterator then none else some (component .unit)

/-- The exact named constructor membership for the branches of the example. -/
theorem parent_mediated :
    MediatedRegistry.Mediated branchingProgram (fun _ => False) (fun _ => False) .parent := by
  have short : MediatedRegistry.Mediated branchingProgram (fun _ => False) (fun _ => False) .tailShort :=
    .birth _ _ rfl (fun _ _ impossible => by cases impossible)
  have long : MediatedRegistry.Mediated branchingProgram (fun _ => False) (fun _ => False) .twoBirths := by
    apply MediatedRegistry.Mediated.birth _ (component .unit) rfl
    intro outcome next selected
    have same : next = .tailShort := (Option.some.inj selected).symm
    simpa only [same] using short
  apply MediatedRegistry.Mediated.birth _ (component .unit) rfl
  intro outcome next selected
  cases outcome with
  | unit | value => cases selected
  | child name =>
    change some (follow name) = some next at selected
    have same := Option.some.inj selected
    subst next
    by_cases picked : name = 2
    · simpa [follow, picked] using short
    · simpa [follow, picked] using long

/-- In any input with the actor present, the encoded head performs exactly the
birth, child-name selection, and captured retirement of Definition 52. -/
theorem branching_head_agrees (actor : Nat) (state : BirthState) (present : state.val actor ≠ none) :
    let head := semantics.iterator actor .parent
    Land branchingProgram actor .parent state.val ((head.effect.run state).1).val
      (.retire (draw state)) (some (follow (draw state))) ∧
    (∀ probe : BirthState, ((head.effect.run state).2 probe).val = Calculus.retire probe.val (draw state)) ∧
    head.next state = some (semantics.iterator actor (follow (draw state))) := by
  obtain ⟨forward, backward⟩ := PairwiseBirthSemantics.birth_actual actor (component .unit) state present
  refine ⟨?_, backward, ?_⟩
  · change Land branchingProgram actor .parent state.val ((birthEffect actor (component .unit)).run state).1.val
      (.retire (draw state)) (some (follow (draw state)))
    rw [forward]
    exact .instantiate _ _ _ _ _ rfl (PairwiseBirthSemantics.fresh_ready _ _ _ present)
  · change some (PairwiseBirthSemantics.meaning actor (follow (draw state))) =
      some (meaning actor (follow (draw state)))
    by_cases picked : draw state = 2 <;> simp [follow, picked, meaning]

/-- The global witness conjunct of the exact Lean statement of Lemma 57 fails
for Definition 56's named birth constructor. -/
theorem lemma57_counterexample :
    ¬ PaperRemainingClaims.lemma57 branchingProgram semantics 0 birthComponent
      (fun _ => False) (fun _ => False) := by
  intro claimed
  have witness := (claimed .parent parent_mediated).2
  let observation := PaperStateObservation.observation semantics (fun _ => False ∨ False)
  have related : observation.r PairwiseBirthBoundary.base PairwiseBirthBoundary.moved :=
    fun key => nomatch key
  have selected := (related_unfold witness.respect related).2.2
  change OptionRel (@RelatedIterator _ observation) ((semantics.iterator 0 .parent).next PairwiseBirthBoundary.base)
    ((semantics.iterator 0 .parent).next PairwiseBirthBoundary.moved) at selected
  rw [(branching_head_agrees 0 _ PairwiseBirthBoundary.base_parent).2.2,
    (branching_head_agrees 0 _ PairwiseBirthBoundary.moved_parent).2.2] at selected
  have tails : @RelatedIterator _ observation (semantics.iterator 0 .tailShort) (semantics.iterator 0 .twoBirths) := by
    simpa only [follow, PairwiseBirthBoundary.base_draw, if_pos rfl,
      if_neg PairwiseBirthBoundary.moved_draw, OptionRel] using selected
  have mismatch := (related_unfold tails (observation.iseqv.refl PairwiseBirthBoundary.base)).2.2
  change OptionRel (@RelatedIterator _ observation) none (some _) at mismatch
  exact mismatch

end BirthCounterexample

export BirthCounterexample (lemma57_counterexample)


namespace PairwiseCounterexample
open PairwiseBirthBoundary (empty r1 r2 r3 r4 step1 step2 step3 step4 base moved)
open PairwiseBirthSemantics (component meaning draw)

local notation "BCode" => PairwiseBirthSemantics.Code
local notation "BRow" => PairwiseBirthSemantics.F

private def semantics : PaperStateObservation.Semantics Nat Empty Unit BCode Empty :=
  { BirthCounterexample.semantics with iterator := meaning }

private def trace : PaperLifecycleClaims.Trace PairwiseBirthSemantics.program 4 where
  state
    | 0 => empty
    | 1 => r1
    | 2 => r2
    | 3 => r3
    | _ => r4
  rule
    | 0 | 1 => .insert
    | _ => .begin
  actor
    | 0 | 2 => 0
    | _ => 1
  start := rfl
  step := by
    intro index bound
    have cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    · exact .insert empty 0 (component .parent) none ⟨rfl, by simp, by intro _ key; exact nomatch key⟩
    · exact .insert r1 1 (component .foreign) none ⟨rfl, by simp, by intro _ key; exact nomatch key⟩
    · exact .begin r2 0 (fresh (component .parent) none) PairwiseBirthBoundary.view
        rfl rfl (by intro impossible; cases impossible) (PairwiseBirthBoundary.target_empty_keys _ _ _ rfl rfl)
    · exact .begin r3 1 (fresh (component .foreign) none) PairwiseBirthBoundary.view
        rfl rfl (by intro impossible; cases impossible) (PairwiseBirthBoundary.target_empty_keys _ _ _ rfl rfl)

private theorem received_prefix (t : Nat) (bound : t ≤ 4) :
    Orchestration.Run PairwiseBirthSemantics.program empty (trace.state t) := by
  have choices : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 := by omega
  have first := Orchestration.Run.step (.refl _) step1
  have second := Orchestration.Run.step first step2
  have third := Orchestration.Run.step second step3
  rcases choices with rfl | rfl | rfl | rfl | rfl
  · exact .refl _
  · exact first
  · exact second
  · exact third
  · exact .step third step4

private theorem empty_key_observation (keys : Empty → Prop) :
    PaperStateObservation.observation semantics keys = PairwiseBirthSemantics.gammaSetoid := by
  have relations : (PaperStateObservation.observation semantics keys).r =
      PairwiseBirthSemantics.gammaSetoid.r := by
    funext left right
    exact propext ⟨fun _ => PairwiseBirthSemantics.projected_all _ _, fun _ key => nomatch key⟩
  have equality (left right : Setoid PairwiseBirthSemantics.Gamma) (eq : left.r = right.r) : left = right := by
    cases left
    cases right
    cases eq
    rfl
  exact equality _ _ relations

private theorem mediated (requires provides : Empty → Prop) (code : BCode) :
    MediatedRegistry.Mediated PairwiseBirthSemantics.program requires provides code := by
  have short : MediatedRegistry.Mediated PairwiseBirthSemantics.program requires provides .tailShort :=
    .birth _ _ rfl (fun _ _ impossible => by cases impossible)
  have long : MediatedRegistry.Mediated PairwiseBirthSemantics.program requires provides .tailLong :=
    .birth _ _ rfl (fun _ _ impossible => by cases impossible)
  cases code with
  | unit => exact .unit _ rfl (fun _ => rfl)
  | foreign => exact .birth _ _ rfl (fun _ _ impossible => by cases impossible)
  | tailShort => exact short
  | tailLong => exact long
  | twoBirths =>
    apply MediatedRegistry.Mediated.birth _ _ rfl
    intro _ next chosen
    have same : next = .tailShort := (Option.some.inj chosen).symm
    simpa only [same] using short
  | parent =>
    apply MediatedRegistry.Mediated.birth _ _ rfl
    intro outcome next chosen
    cases outcome with
    | unit | value => cases chosen
    | child name =>
      by_cases selected : name = 2
      · have eq : some PairwiseBirthSemantics.Code.tailShort = some next := by simpa [PairwiseBirthSemantics.program, selected] using chosen
        rw [← Option.some.inj eq]
        exact short
      · have eq : some PairwiseBirthSemantics.Code.tailLong = some next := by simpa [PairwiseBirthSemantics.program, selected] using chosen
        rw [← Option.some.inj eq]
        exact long

private theorem continuations (actor : Nat) (code : BCode) (produced : Option BCode)
    (before after : PairwiseBirthSemantics.R) (inverse : Inverse Nat Empty Unit)
    (land : Land PairwiseBirthSemantics.program actor code before after inverse produced) :
    ∀ next, produced = some next →
    ∃ input : semantics.Gamma, (semantics.iterator actor code).next input = some (semantics.iterator actor next) := by
  cases land with
  | unit _ _ _ action =>
    intro next selected
    cases code <;> simp [PairwiseBirthSemantics.program] at action selected
  | provide _ _ _ _ key => exact nomatch key
  | operate _ _ _ key => exact nomatch key
  | instantiate _ _ _ payload child action ready =>
    intro next selected
    cases code with
    | unit => cases action
    | foreign | tailShort | tailLong => cases selected
    | twoBirths =>
      have equal : PairwiseBirthSemantics.Code.tailShort = next := Option.some.inj selected
      subst next
      exact ⟨base, rfl⟩
    | parent =>
      have equal : (if child = 2 then PairwiseBirthSemantics.Code.tailShort else
          PairwiseBirthSemantics.Code.tailLong) = next := Option.some.inj selected
      subst next
      by_cases picked : child = 2
      · exact ⟨base, by simp [semantics, meaning, picked, PairwiseBirthBoundary.base_draw, Iterator.next]⟩
      · exact ⟨moved, by simp [semantics, meaning, picked, PairwiseBirthBoundary.moved_draw, Iterator.next]⟩

private theorem all_admitted : PaperRemainingClaims.ComponentsAdmitted (sem := semantics) trace := by
  intro t bound
  have run := received_prefix t bound
  refine ⟨⟨run.reachable_invariants.1, SupportUniqueness.reachable_finite PairwiseBirthSemantics.program run⟩, ?_⟩
  intro actor fiber present
  refine ⟨mediated _ _ _, ?_, ?_⟩
  · rw [empty_key_observation]
    exact PairwiseBirthSemantics.all_components_witnessed actor fiber.component.entry
  · intro _ _ _ _ _ _ landed
    exact continuations _ _ _ _ _ _ landed _ rfl

/-- The indexed Lemma 66 fails for every continuation comparison that
enforces Definition 65's birth-component stability on the two entries of
this trace. Both entries and their selected continuations are admitted. -/
theorem lemma66_indexed_counterexample
    (operations : PaperEffectEquations.CoeffectOperations (fun _ : Empty => Unit))
    (comparison : Nat → BCode → Nat → BCode → Prop)
    (tails : BCode → BCode → Prop) (observes : PairwiseBirthBoundary.ObservesComponents tails)
    (stable : comparison 0 .parent 1 .foreign → PairwiseBirthBoundary.RootYieldStable tails) :
    ¬ PaperRemainingClaims.lemma66 (sem := semantics) trace comparison operations (fun _ _ _ => False) := by
  intro claimed
  have operationsAdmitted : PaperLifecycleClaims.AdmittedCoeffects operations :=
    ⟨(fun key => nomatch key), (fun key => nomatch key)⟩
  obtain independent | entangled :=
    claimed operationsAdmitted all_admitted 2 2 (by decide) (by decide)
      0 1 (fresh (component .parent) none) (fresh (component .foreign) none) (by decide) rfl rfl
  · exact PairwiseBirthBoundary.no_component_observing_yield_stability tails observes (stable independent.2)
  · rcases entangled.1 with ⟨key, _⟩ | ⟨key, _⟩ <;> exact nomatch key

end PairwiseCounterexample

export PairwiseCounterexample (lemma66_indexed_counterexample)

end
end Cordis.Results
