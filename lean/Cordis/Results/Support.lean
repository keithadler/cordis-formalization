import Cordis.PaperRemainingClaims
import Cordis.Metatheory
import Cordis.SupportCounterexample
import Cordis.SupportUniqueness
import Cordis.TranspositionOrchestration
import Cordis.PaperTranspositionHistoryDiamond
import Cordis.DeletionAdmissionBoundary
import Cordis.Results.SupportTransposition

/-!
Lemmas 75, 77–79 of arXiv:2608.25512v1.

For Lemma 75, the displayed O-Insert rule admits a nonroot external insertion.
Definition 74's provenance convention restricts external insertion to the root.
The support results record both readings. Lemma 78 includes
provenance-correct orchestration and two choices of activation semantics.
Lemma 79's refutation uses the literal deletion interval.
-/

namespace Cordis.Results
open Calculus Stages Effects Iterators

section Support
universe u
variable {Name Key Value Code Error : Type u}
local notation "RegistryState" => Registry Name Key Value Code (Inverse Name Key Value) Error

/-- Definition 74, equation (61), in the order predecessor then successor. -/
def SupportRelation (state : RegistryState) (predecessor name : Name) : Prop :=
  Progress.Depends state name predecessor ∨
    ∃ fiber, state name = some fiber ∧ fiber.parent = some predecessor

private theorem uniqueSupport (state : RegistryState) (relation : Name → Name → Prop)
    (wellFounded : WellFounded relation)
    (includes : ∀ predecessor name fiber, state name = some fiber → fiber.retired = false →
      SupportRelation state predecessor name → relation predecessor name) :
    ∃ set : Name → Prop, SupportAtQuiescence.Solution state set ∧
      ∀ other : Name → Prop, SupportAtQuiescence.Solution state other → other = set := by
  let body (name : Name) (previous : ∀ predecessor, relation predecessor name → Prop) : Prop :=
    ∃ fiber, ∃ present : state name = some fiber, ∃ live : fiber.retired = false,
      (fiber.parent = none ∨ ∃ parent, ∃ parentOf : fiber.parent = some parent,
        previous parent (includes parent name fiber present live (.inr ⟨fiber, present, parentOf⟩))) ∧
      ∀ key, ∀ required : fiber.component.requires key = true,
        ∃ provider entry, ∃ found : state provider = some entry, ∃ provides : entry.component.provides key = true,
          previous provider (includes provider name fiber present live
            (.inl ⟨fiber, entry, key, present, found, required, provides⟩))
  let set := wellFounded.fix body
  have solution : SupportAtQuiescence.Solution state set := by
    intro name
    change wellFounded.fix body name ↔ _
    rw [WellFounded.fix_eq]
    constructor
    · rintro ⟨fiber, present, live, parent, requirements⟩
      refine ⟨fiber, present, live, ?_, ?_⟩
      · rcases parent with root | ⟨parentName, parentOf, supported⟩
        · exact .inl root
        · exact .inr ⟨parentName, parentOf, supported⟩
      · intro key required
        obtain ⟨provider, entry, found, provides, supported⟩ := requirements key required
        exact ⟨provider, entry, found, supported, provides⟩
    · rintro ⟨fiber, present, live, parent, requirements⟩
      refine ⟨fiber, present, live, ?_, ?_⟩
      · rcases parent with root | ⟨parentName, parentOf, supported⟩
        · exact .inl root
        · exact .inr ⟨parentName, parentOf, supported⟩
      · intro key required
        obtain ⟨provider, entry, found, supported, provides⟩ := requirements key required
        exact ⟨provider, entry, found, provides, supported⟩
  refine ⟨set, solution, ?_⟩
  intro other candidate
  funext name
  apply propext
  refine wellFounded.induction (C := fun name => other name ↔ set name) name ?_
  intro name ih
  constructor
  · intro member
    obtain ⟨fiber, present, live, parent, requirements⟩ := (candidate name).mp member
    refine (solution name).mpr ⟨fiber, present, live, ?_, ?_⟩
    · rcases parent with root | ⟨parentName, parentOf, supported⟩
      · exact .inl root
      · exact .inr ⟨parentName, parentOf, (ih parentName (includes parentName name fiber present live (.inr ⟨fiber, present, parentOf⟩))).mp supported⟩
    · intro key required
      obtain ⟨provider, entry, found, supported, provides⟩ := requirements key required
      exact ⟨provider, entry, found,
        (ih provider (includes provider name fiber present live (.inl ⟨fiber, entry, key, present, found, required, provides⟩))).mp supported, provides⟩
  · intro member
    obtain ⟨fiber, present, live, parent, requirements⟩ := (solution name).mp member
    refine (candidate name).mpr ⟨fiber, present, live, ?_, ?_⟩
    · rcases parent with root | ⟨parentName, parentOf, supported⟩
      · exact .inl root
      · exact .inr ⟨parentName, parentOf, (ih parentName (includes parentName name fiber present live (.inr ⟨fiber, present, parentOf⟩))).mpr supported⟩
    · intro key required
      obtain ⟨provider, entry, found, supported, provides⟩ := requirements key required
      exact ⟨provider, entry, found,
        (ih provider (includes provider name fiber present live (.inl ⟨fiber, entry, key, present, found, required, provides⟩))).mpr supported, provides⟩

/-- Well-foundedness of the full relation in Equation (61) suffices for
existence and uniqueness of the support set in Equation (62). -/
theorem lemma75_unique_support_of_wellFounded (state : RegistryState)
    (wellFounded : WellFounded (SupportRelation state)) :
    ∃ set : Name → Prop, SupportAtQuiescence.Solution state set ∧
      ∀ other : Name → Prop, SupportAtQuiescence.Solution state other → other = set :=
  uniqueSupport state (SupportRelation state) wellFounded (fun _ _ _ _ _ edge => edge)

variable [DecidableEq Name] [DecidableEq Key]

/-- The recursive clauses consult a name's predecessors only if that name
is still live. Equation (61) itself can include edges into retired names. -/
def SupportConsults (state : RegistryState) (predecessor name : Name) : Prop :=
  (∃ fiber, state name = some fiber ∧ fiber.retired = false) ∧
    SupportRelation state predecessor name

/-- Names with an installed view are already ordered by episode rank. -/
def SupportInstalled (state : RegistryState) (name : Name) : Prop :=
  ∃ fiber view, state name = some fiber ∧ fiber.phase.committed = some view

/-- Only dependencies between uninstalled names, consulted by a live
consumer, need an external acyclicity hypothesis. -/
def UninstalledSupportDependencies (state : RegistryState) (predecessor name : Name) : Prop :=
  Progress.Depends state name predecessor ∧
    (∃ fiber, state name = some fiber ∧ fiber.retired = false) ∧
    ¬ SupportInstalled state predecessor ∧ ¬ SupportInstalled state name

/-- Equation (62) has a well-founded recursion even when the full edge set
of Equation (61) has cycles through retired names. An installed consumer's
providers are installed with smaller episode ranks, and any live child's
parent is installed. All remaining edges between uninstalled names are
provider edges, which are acyclic by hypothesis. -/
theorem supportConsults_wellFounded_of_ranked {state : RegistryState}
    (finite : SupportUniqueness.FiniteDomain state) (ranked : SupportOrder.Ranked state)
    (captures : ChildProvenance.Captured state) (owned : Safety.Owned state)
    (supported : Ordering.Supported state) (disjoint : WellFormed.Disjoint state)
    (acyclic : FiniteOrder.Acyclic (UninstalledSupportDependencies state)) :
    WellFounded (SupportConsults state) := by
  let installed := SupportInstalled state
  obtain ⟨rank, _, _, ordered⟩ := ranked
  have fromParent {name parent : Name} {fiber : Fiber Name Key Value Code (Inverse Name Key Value) Error}
      (found : state name = some fiber) (live : fiber.retired = false)
      (parentOf : fiber.parent = some parent) : installed parent := by
    obtain ⟨entry, present, captured⟩ := captures name fiber parent found parentOf live
    cases phase : entry.phase with
    | inactive => simp [phase, Phase.accumulator] at captured
    | reloading _ _ view | active _ view | unloading _ view =>
      exact ⟨entry, view, present, by simp [phase, Phase.committed]⟩
  have lower {predecessor name : Name} (edge : SupportConsults state predecessor name)
      (active : installed name) : installed predecessor ∧ rank predecessor < rank name := by
    obtain ⟨fiber, view, found, committed⟩ := active
    obtain ⟨⟨liveFiber, foundLive, live⟩, relation⟩ := edge
    have same := Option.some.inj (foundLive.symm.trans found)
    subst liveFiber
    rcases relation with ⟨consumer, provider, key, consumerFound, providerFound, requires, provides⟩ |
        ⟨child, childFound, parentOf⟩
    · have same := Option.some.inj (consumerFound.symm.trans found)
      subst consumer
      have identifies := OrderingIntervals.declared_provider_is_committed state name predecessor fiber
        provider view key supported owned disjoint found providerFound committed requires provides
      have demand : Ordering.Demand state name predecessor key :=
        ⟨fiber, view, found, requires, committed, identifies⟩
      refine ⟨?_, ordered.provider name predecessor key demand⟩
      obtain ⟨_, entry, present, retained, _⟩ := supported name predecessor key demand
      cases phase : entry.phase with
      | inactive | reloading => simp [phase, Ordering.Retained] at retained
      | active _ view | unloading _ view =>
        exact ⟨entry, view, present, by simp [phase, Phase.committed]⟩
    · have same := Option.some.inj (childFound.symm.trans found)
      subst child
      exact ⟨fromParent found live parentOf, ordered.parent name fiber predecessor view found parentOf live committed⟩
  have installedAccessible (name : Name) (active : installed name) : Acc (SupportConsults state) name := by
    revert active
    apply (measure rank).wf.induction name
    intro name ih active
    exact .intro name (fun predecessor edge =>
      let ⟨prior, decreases⟩ := lower edge active
      ih predecessor decreases prior)
  obtain ⟨names, cover⟩ := finite
  have providerOrder : WellFounded (UninstalledSupportDependencies state) := by
    apply FiniteOrder.wellFounded_of_finite_acyclic _ names _ acyclic
    intro predecessor name edge
    obtain ⟨_, provider, _, _, present, _⟩ := edge.1
    exact cover predecessor provider present
  refine ⟨fun name => providerOrder.induction name ?_⟩
  intro name ih
  by_cases current : installed name
  · exact installedAccessible name current
  refine .intro name ?_
  intro predecessor edge
  by_cases earlier : installed predecessor
  · exact installedAccessible predecessor earlier
  obtain ⟨⟨fiber, found, live⟩, relation⟩ := edge
  rcases relation with dependency | ⟨child, childFound, parentOf⟩
  · exact ih predecessor ⟨dependency, ⟨fiber, found, live⟩, earlier, current⟩
  · have same := Option.some.inj (childFound.symm.trans found)
    subst child
    exact installedAccessible predecessor (fromParent found live parentOf)

theorem lemma75_consulted_edges_wellFounded_of_uninstalled (program : Code → Instruction Name Key Value Code Error)
    {state : RegistryState} (run : Orchestration.Run program (fun _ => none) state)
    (acyclic : FiniteOrder.Acyclic (UninstalledSupportDependencies state)) :
    WellFounded (SupportConsults state) :=
  supportConsults_wellFounded_of_ranked (SupportUniqueness.reachable_finite program run)
    (SupportOrder.reachable_ranked program run) (ChildProvenance.reachable_captured program run)
    run.reachable_invariants.2.1 run.reachable_invariants.2.2.1
    (SupportUniqueness.reachable_disjoint program run) acyclic

omit [DecidableEq Name] [DecidableEq Key] in
theorem support_unique_of_consulted_wellFounded (state : RegistryState)
    (ordered : WellFounded (SupportConsults state)) :
    ∃ set : Name → Prop, SupportAtQuiescence.Solution state set ∧
      ∀ other : Name → Prop, SupportAtQuiescence.Solution state other → other = set :=
  uniqueSupport state (SupportConsults state) ordered
    (fun _ _ fiber found live edge => ⟨⟨fiber, found, live⟩, edge⟩)

/-- On reachable registries, cycles among the consulted uninstalled
dependencies are exactly the obstruction to well-founded recursion. -/
theorem lemma75_consulted_edges_wellFounded_iff (program : Code → Instruction Name Key Value Code Error)
    {state : RegistryState} (run : Orchestration.Run program (fun _ => none) state) :
    WellFounded (SupportConsults state) ↔
      FiniteOrder.Acyclic (UninstalledSupportDependencies state) := by
  refine ⟨?_, lemma75_consulted_edges_wellFounded_of_uninstalled program run⟩
  intro wf name cycle
  have lift {first last : Name}
      (chain : FiniteOrder.Chain (UninstalledSupportDependencies state) first last) :
      Relation.TransGen (SupportConsults state) first last := by
    induction chain with
    | single edge => exact .single ⟨edge.2.1, .inl edge.1⟩
    | tail _ edge ih => exact .tail ih ⟨edge.2.1, .inl edge.1⟩
  have noLoop (node : Name) (accessible : Acc (Relation.TransGen (SupportConsults state)) node) :
      ¬ Relation.TransGen (SupportConsults state) node node := by
    induction accessible with
    | intro node _ ih => exact fun loop => ih node loop loop
  exact noLoop name (wf.transGen.apply name) (lift cycle)

theorem lemma75_consulted_edges_wellFounded (program : Code → Instruction Name Key Value Code Error)
    {state : RegistryState} (run : Orchestration.Run program (fun _ => none) state)
    (acyclic : FiniteOrder.Acyclic (Progress.Depends state)) :
    WellFounded (SupportConsults state) := by
  apply lemma75_consulted_edges_wellFounded_of_uninstalled program run
  have lift {first last : Name} (chain : FiniteOrder.Chain (UninstalledSupportDependencies state) first last) :
      FiniteOrder.Chain (fun predecessor name => Progress.Depends state name predecessor) first last := by
    induction chain with
    | single edge => exact .single edge.1
    | tail _ edge ih => exact .tail ih edge.1
  exact fun name closed => FiniteActionBudget.acyclic_flip _ acyclic name (lift closed)

/-- The unique-solution conjunct of Lemma 75 on every provenance-correct
run, with the paper's acyclic precedence assumption. -/
theorem lemma75_unique_support (program : Code → Instruction Name Key Value Code Error)
    {state : RegistryState} (run : Orchestration.Run program (fun _ => none) state)
    (acyclic : FiniteOrder.Acyclic (Progress.Depends state)) :
    ∃ set : Name → Prop, SupportAtQuiescence.Solution state set ∧
      ∀ other : Name → Prop, SupportAtQuiescence.Solution state other → other = set :=
  support_unique_of_consulted_wellFounded state (lemma75_consulted_edges_wellFounded program run acyclic)

theorem lemma75_unique_support_of_uninstalled (program : Code → Instruction Name Key Value Code Error)
    {state : RegistryState} (run : Orchestration.Run program (fun _ => none) state)
    (acyclic : FiniteOrder.Acyclic (UninstalledSupportDependencies state)) :
    ∃ set : Name → Prop, SupportAtQuiescence.Solution state set ∧
      ∀ other : Name → Prop, SupportAtQuiescence.Solution state other → other = set :=
  support_unique_of_consulted_wellFounded state
    (lemma75_consulted_edges_wellFounded_of_uninstalled program run acyclic)

theorem lemma77_of_uninstalled (program : Code → Instruction Name Key Value Code Error)
    {state : RegistryState} (run : Orchestration.Run program (fun _ => none) state)
    (acyclic : FiniteOrder.Acyclic (UninstalledSupportDependencies state))
    (quiet : Progress.Quiet state) (total : SupportAtQuiescence.TotalProvision state) :
    SupportAtQuiescence.Solution state (SupportAtQuiescence.Active state) ∧
      ∀ set : Name → Prop, SupportAtQuiescence.Solution state set → set = SupportAtQuiescence.Active state := by
  have fixed := SupportAtQuiescence.active_solution_of_capture
    (ChildProvenance.reachable_captured program run) quiet total
  obtain ⟨solution, _, unique⟩ := lemma75_unique_support_of_uninstalled program run acyclic
  exact ⟨fixed, fun set solved => (unique set solved).trans (unique _ fixed).symm⟩

/-- Lemma 77 for an actual run with the parent provenance of Definition 74.
The endpoint hypothesis on available fibers follows from total provision
throughout a run. The conclusion identifies the unique solution of (62). -/
theorem lemma77 (program : Code → Instruction Name Key Value Code Error)
    {state : RegistryState} (run : Orchestration.Run program (fun _ => none) state)
    (acyclic : FiniteOrder.Acyclic (Progress.Depends state))
    (quiet : Progress.Quiet state) (total : SupportAtQuiescence.TotalProvision state) :
    SupportAtQuiescence.Solution state (SupportAtQuiescence.Active state) ∧
      ∀ set : Name → Prop, SupportAtQuiescence.Solution state set → set = SupportAtQuiescence.Active state := by
  obtain ⟨fixedPoint, unique⟩ := SupportUniqueness.support_unique_active program run acyclic quiet total
  exact ⟨fixedPoint, fun set supported => funext fun name => propext (unique set supported name)⟩
theorem rootRule (program : Code → Instruction Name Key Value Code Error)
    {rule : Labeled.Rule} {actor : Name} {before after : RegistryState}
    (step : Labeled.Step program rule actor before after)
    (root : rule = .insert → ∃ fiber, after actor = some fiber ∧ fiber.parent = none) :
    Orchestration.Step program before after := by
  cases step with
  | insert =>
    rename_i component parent ready
    obtain ⟨fiber, appears, rootParent⟩ := root rfl
    have actorEntry : put before actor (fresh component parent) actor = some (fresh component parent) :=
      put_self _ _ _
    have same := Option.some.inj (actorEntry.symm.trans appears)
    subst fiber
    change parent = none at rootParent
    subst parent
    exact .insert before actor component ready
  | retire => apply Orchestration.Step.retire; assumption
  | remove => apply Orchestration.Step.remove; assumption
  | begin => apply Orchestration.Step.begin <;> assumption
  | iter => apply Orchestration.Step.iter <;> assumption
  | finish => apply Orchestration.Step.finish <;> assumption
  | divert => apply Orchestration.Step.divert <;> assumption
  | leave => apply Orchestration.Step.leave <;> assumption
  | unload => apply Orchestration.Step.unload <;> assumption

theorem rootTrace {program : Code → Instruction Name Key Value Code Error}
    {last : Nat} (trace : PaperLifecycleClaims.Trace program last)
    (root : PaperLifecycleClaims.RootInsertions trace) (index : Nat) (bound : index ≤ last) :
    Orchestration.Run program (fun _ => none) (trace.state index) := by
  induction index with
  | zero => rw [trace.start]; exact .refl _
  | succ index ih =>
    exact .step (ih (Nat.le_of_succ_le bound))
      (rootRule program (trace.step index bound) (root index bound))

omit [DecidableEq Name] [DecidableEq Key] in
theorem depends_acyclic (state : RegistryState)
    (acyclic : FiniteOrder.Acyclic (PaperLifecycleClaims.precedence state)) :
    FiniteOrder.Acyclic (Progress.Depends state) := by
  have flip := FiniteActionBudget.acyclic_flip _ acyclic
  have translate {consumer provider : Name} :
      Progress.Depends state consumer provider → PaperLifecycleClaims.precedence state provider consumer := by
    rintro ⟨consuming, providing, key, consumerAt, providerAt, required, provided⟩
    exact ⟨key, ⟨providing, providerAt, provided⟩, ⟨consuming, consumerAt, required⟩⟩
  intro name cycle
  apply flip name
  have reverseChain {first last : Name} (chain : FiniteOrder.Chain (Progress.Depends state) first last) :
      FiniteOrder.Chain (fun a b => PaperLifecycleClaims.precedence state b a) first last := by
    induction chain with
    | single edge => exact .single (translate edge)
    | tail _ edge ih => exact .tail ih (translate edge)
  exact reverseChain cycle

/-- The exact numbered proposition for Lemma 77 on the paper's indexed trace. -/
theorem lemma77_proved [Setoid Value] (program : Code → Instruction Name Key Value Code Error)
    (semantics : PaperStateObservation.Semantics Name Key Value Code Error)
    (operations : PaperEffectEquations.CoeffectOperations (fun _ : Key => Value)) :
    PaperLifecycleClaims.lemma77 program semantics operations := by
  intro _ last trace root _ acyclic quiet total
  exact lemma77 program (rootTrace trace root last (Nat.le_refl last))
    (depends_acyclic (trace.state last) acyclic) quiet total

end Support

section DisplayedInsert
open Metatheory
abbrev InsertModel := MediatedRegistry.Gamma Bool Unit Unit Unit Empty

/-- Every installed iterator in the displayed-rule example is the unit, which
has its Definition 37 witness at any set of keys. Its stage and inverse also
agree exactly with the primitive unit on all inputs. -/
theorem lemma75_displayed_rule_admission (keys : Unit → Prop) :
    @WitnessedIterator InsertModel (MediatedRegistry.observation keys) (embed Effects.identity) ∧
    (∀ actor (input : InsertModel), Land unitProgram actor () input.val input.val .unit none) :=
  ⟨@witnessed_embed InsertModel (MediatedRegistry.observation keys) _
      (@witnessed_identity InsertModel (MediatedRegistry.observation keys)),
    fun actor input => .unit input.val actor () rfl⟩

/-- The displayed O-Insert rules admit a provider that has its consumer as
parent. Precedence is acyclic, while combined support has a two-cycle and
equation (62) has two solutions. The second insert is external and nonroot. -/
theorem lemma75_displayed_rule_counterexample :
    Reachable cyclic ∧ WellFounded (Precedes cyclic) ∧ ¬ WellFounded (Supports cyclic) ∧
      SupportAtQuiescence.Solution cyclic (fun _ => False) ∧
      SupportAtQuiescence.Solution cyclic (fun _ => True) := by
  obtain ⟨reached, acyclic, cycle⟩ := lemma75_counterexample
  have convert (set : Bool → Prop) (fixedPoint : SupportedSet cyclic set) :
      SupportAtQuiescence.Solution cyclic set := by
    intro name
    have existsFiber : ∃ fiber, cyclic name = some fiber := by
      cases name <;> exact ⟨_, rfl⟩
    obtain ⟨fiber, present⟩ := existsFiber
    constructor
    · intro member
      have ⟨live, parent, providers⟩ := (fixedPoint name fiber present).mp member
      exact ⟨fiber, present, live, parent, providers⟩
    · rintro ⟨entry, found, live, parent, providers⟩
      have same := Option.some.inj (found.symm.trans present)
      subst entry
      exact (fixedPoint name fiber present).mpr ⟨live, parent, providers⟩
  exact ⟨reached, acyclic, cycle, convert _ cyclic_support_empty, convert _ cyclic_support_full⟩
end DisplayedInsert

/-- Lemma 75's first conclusion also fails for the primitive relation with
the root-only external convention. This trace produces a binding, so its
first provision cannot satisfy the literal global map interpretation
established in GlobalSupport. -/
theorem lemma75_primitive_counterexample :
    Orchestration.Run SupportCounterexample.program SupportCounterexample.s0 SupportCounterexample.s13 ∧
      WellFounded SupportCounterexample.EverPrecedes ∧
      ¬ WellFounded (SupportRelation SupportCounterexample.s13) := by
  obtain ⟨run, _, acyclic, noOrder⟩ := SupportCounterexample.lemma75_with_provenance_counterexample
  refine ⟨run, acyclic, fun order => noOrder ?_⟩
  apply Subrelation.wf _ order
  intro predecessor name edge
  rcases edge with ⟨provider, consumer, key, providerAt, consumerAt, provides, requires⟩ | parent
  · exact .inl ⟨consumer, provider, key, consumerAt, providerAt, requires, provides⟩
  · exact .inr parent

/-- The very run that refutes the full-relation claim has a well-founded
consultation relation. Its third cut has an actual provision binding. -/
theorem lemma75_repaired_on_primitive_counterexample :
    StageRecovery.tableAt SupportCounterexample.s3 .old false = some () ∧
      WellFounded (SupportConsults SupportCounterexample.s13) ∧
      ∃ set, SupportAtQuiescence.Solution SupportCounterexample.s13 set ∧
        ∀ other, SupportAtQuiescence.Solution SupportCounterexample.s13 other → other = set := by
  have acyclic : FiniteOrder.Acyclic (UninstalledSupportDependencies SupportCounterexample.s13) := by
    have increases {first last : SupportCounterexample.Name}
        (chain : FiniteOrder.Chain (UninstalledSupportDependencies SupportCounterexample.s13) first last) :
        SupportCounterexample.rank first < SupportCounterexample.rank last := by
      have edgeRank {a b : SupportCounterexample.Name}
          (edge : UninstalledSupportDependencies SupportCounterexample.s13 a b) :
          SupportCounterexample.rank a < SupportCounterexample.rank b := by
        obtain ⟨consumer, provider, key, consumerAt, providerAt, requires, provides⟩ := edge.1
        exact SupportCounterexample.precedence_ranked a b
          ⟨provider, consumer, key, providerAt, consumerAt, provides, requires⟩
      induction chain with
      | single edge => exact edgeRank edge
      | tail _ edge ih => exact Nat.lt_trans ih (edgeRank edge)
    exact fun name closed => (Nat.lt_irrefl _) (increases closed)
  exact ⟨rfl,
    lemma75_consulted_edges_wellFounded_of_uninstalled _ SupportCounterexample.reachable acyclic,
    lemma75_unique_support_of_uninstalled _ SupportCounterexample.reachable acyclic⟩

-- Lemma 78(1), all nine activation pairs with explicit source admission.
export PaperTranspositionHistory (activation_diamond_from_history)
-- Lemma 78(2), the three root-only external rules.
export Transposition (activation_orchestration_diamond)

/-- Every replay of the surviving Begin leaves the actor unretired. -/
private theorem lemma79_no_replay_endpoint
    (sem : PaperStateObservation.Semantics Nat Empty Unit Bool Empty)
    {endpoint : RenamingLiteral.R}
    (beginStep : Labeled.Step ResolutionClosureBoundary.program .begin 0 DeletionAdmissionBoundary.s1 endpoint) :
    ¬ PaperStateObservation.Related sem DeletionAdmissionBoundary.s6 endpoint := by
  intro related
  cases beginStep with
  | begin =>
    rename_i fiber view _ present _ _
    have result := mark_self _ _ fiber (.reloading fiber.component.entry [] view) present
    have final : DeletionAdmissionBoundary.s6 0 =
        some { (fresh ResolutionClosureBoundary.component none : RenamingLiteral.F)
          with retired := true } := rfl
    have fields := PaperStateObservation.fields sem related 0 _ _ final result
    have same := Option.some.inj (present.symm.trans (show DeletionAdmissionBoundary.s1 0 =
        some (fresh ResolutionClosureBoundary.component none) from rfl))
    subst fiber
    cases fields.retired

-- Lemma 79's original admission, hypotheses, exact survivor list and failure.
export DeletionAdmissionBoundary (certified_original_scope)

section IndexedTransposition
open PaperLifecycleClaims PaperRemainingClaims
universe u
variable {Name Key Value Code Error : Type u} [DecidableEq Name] [DecidableEq Key] [Setoid Value]
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "Program" => Code → Instruction Name Key Value Code Error

omit [Setoid Value] in
private theorem transpose_command (program : Program) {actor : Name} {rule : Labeled.Rule}
    {before middle after : R}
    (activation : Labeled.Step program rule actor before middle) (active : Transposition.Activation rule)
    (command : OrchestrationSorting.Command Name Key Code)
    (external : command.Step middle after) (different : actor ≠ command.actor)
    (notCreated : ¬ Transposition.CreatesChild program actor before middle command.actor) :
    ∃ swapped, command.Step before swapped ∧ Labeled.Step program rule actor swapped after := by
  cases command with
  | insert name component =>
    obtain ⟨ready, rfl⟩ := external
    obtain ⟨inserted, activated⟩ :=
      Transposition.activation_insert_diamond program activation active name component different ready
    refine ⟨_, ⟨?_, rfl⟩, activated⟩
    generalize payload : put before name (fresh component none) = result at inserted
    cases inserted with
    | insert _ _ actual parent legal =>
      have entries : (fresh component none : Fiber Name Key Value Code (Inverse Name Key Value) Error) = fresh actual parent := by
        simpa only [put_self, Option.some.injEq] using congrFun payload name
      have sameComponent := congrArg Fiber.component entries
      have sameParent := congrArg Fiber.parent entries
      change component = actual at sameComponent
      change none = parent at sameParent
      change Insertable before name component none
      rwa [sameComponent, sameParent]
  | retire name =>
    obtain ⟨ready, rfl⟩ := external
    have present : before name ≠ none := by
      intro absent
      exact notCreated ((Transposition.activation_creates_iff program activation active name different).mpr
        ⟨absent, ready⟩)
    exact ⟨_, ⟨present, rfl⟩, Transposition.activation_after_retirement program activation active name different present⟩
  | remove name =>
    obtain ⟨ready, rfl⟩ := external
    obtain ⟨removed, activated⟩ := Transposition.activation_remove_diamond program activation active name different ready
    refine ⟨_, ⟨?_, rfl⟩, activated⟩
    cases removed with
    | remove _ _ legal => exact legal

omit [Setoid Value] in
private theorem active_rule {rule : Labeled.Rule} (active : Activates rule) :
    Transposition.Activation rule := by
  cases rule <;> simp_all [Activates, Transposition.Activation]

/-- Both indexed clauses of Lemma 78. Equation (54) compares the endpoints
of the activation exchange. The same external command, including its
insertion payload, is replayed in the orchestration exchange. -/
theorem lemma78_indexed_of_coeffects {program : Program} {last : Nat}
    (sem : PaperStateObservation.Semantics Name Key Value Code Error)
    (trace : Trace program last) (birthAgreement : Name → Code → Name → Code → Prop)
    {names : Key → Type u} {args : (key : Key) → names key → Type u}
    {operations : (key : Key) → (name : names key) → args key name →
      PartialInverseObservation.Operation Value Value}
    (operationRepresentation : ∀ code key callback, (program code).action = .operate key callback →
      ∃ name argument, Transposition.RepresentsCallback (operations key name argument) callback)
    (valueObservation : ∀ key (left right : Value),
      PaperObservationEquations.KeyEquivalent (Transposition.callbackOperations names args operations) key left right ↔
        left ≈ right)
    (witnesses : ∀ key name argument, PartialInverseObservation.Witnessed
      (operations key name argument) (· ≈ ·))
    (commutativity : ∀ key, PaperObservationEquations.CommutativeKey
      (Transposition.callbackOperations names args operations)
      (PaperObservationEquations.fullTableObservation (Transposition.callbackOperations names args operations)) key)
    (compatible : ∀ key (v w : Value), v ≈ w → (sem.keyObservation key).r v w)
    (addressed : sem.undo = Stages.undo)
    (representation : AccumulatorProvenance.LandingProperty program (PaperTranspositionObservation.GeneratedInverse sem))
    (fields : ∀ t, t ≤ last →
      (∀ actor fiber, trace.state t actor = some fiber →
        @WitnessedIterator _ (PaperStateObservation.base sem) (sem.iterator actor fiber.component.entry)) ∧
      (∀ actor fiber, trace.state t actor = some fiber → ∀ code stack view,
        fiber.phase = .reloading code stack view →
        @WitnessedIterator _ (PaperStateObservation.base sem) (sem.iterator actor code))) :
    lemma78 (sem := sem) trace birthAgreement := by
  intro t bounded before middle after m n r s _ different active
  have firstBound : t < last := by omega
  have first := trace.step t firstBound
  have second := trace.step (t + 1) bounded
  have reached := trace.prefixRun t (Nat.le_of_lt firstBound)
  constructor
  · intro activateSecond firstFiber secondFiber _ _ _ applicable
    have typed := fields (t + 2) (by omega)
    exact lemma78_nondeterministic_activation_of_coeffects sem program
      operationRepresentation valueObservation witnesses commutativity compatible addressed
      first (active_rule active) second (active_rule activateSecond) applicable different reached representation
      typed.1 typed.2
  · intro command actorLabel _ external notCreated
    exact transpose_command program first (active_rule active) command external
      (actorLabel ▸ different) (actorLabel ▸ notCreated)

end IndexedTransposition

section DeletionCounterexample
open DeletionAdmissionBoundary
open RenamingLiteral (Name R F Code)
open ResolutionClosureBoundary (program component)
open PaperRemainingClaims PaperLifecycleClaims

private def noCoeffects : PaperEffectEquations.CoeffectOperations (fun _ : Empty => Unit) where
  Name key := nomatch key
  Argument key := nomatch key
  Outcome key := nomatch key
  operation key := nomatch key

private theorem deletion_entries_admitted :
    ComponentsAdmitted (sem := semantics) trace := by
  intro t bound
  refine ⟨every_prefix_admissible t bound, ?_⟩
  intro name fiber present
  refine ⟨.unit _ rfl (fun _ => rfl), ?_, ?_⟩
  · exact @witnessed_embed _ (PaperStateObservation.observation semantics _) Effects.identity
      (@Effects.witnessed_identity _ (PaperStateObservation.observation semantics _))
  · intro code _ next before after inverse land
    cases land

private theorem no_withdrawals (child : Name) : ¬ BornDuring trace 0 2 5 child := by
  rintro ⟨_, _, _, _, _, code, payload, _, action, _, _⟩
  cases action

private theorem retained_pair {remaining : List Nat} (increases : remaining.Pairwise (· < ·))
    (members : ∀ n, n ∈ remaining ↔ n = 0 ∨ n = 1) : remaining = [0, 1] := by
  have zero : 0 ∈ remaining := (members 0).mpr (Or.inl rfl)
  have one : 1 ∈ remaining := (members 1).mpr (Or.inr rfl)
  cases remaining with
  | nil => cases zero
  | cons head tail =>
    obtain ⟨headLess, tailIncreases⟩ := List.pairwise_cons.mp increases
    have headChoice := (members head).mp List.mem_cons_self
    rcases headChoice with rfl | rfl
    · have tailOne := List.mem_of_ne_of_mem (by decide : (1 : Nat) ≠ 0) one
      have onlyOne : ∀ n ∈ tail, n = 1 := by
        intro n whereIn
        have valid := (members n).mp (List.mem_cons_of_mem _ whereIn)
        have positive := headLess _ whereIn
        omega
      cases tail with
      | nil => cases tailOne
      | cons second rest =>
        have secondOne : second = 1 := onlyOne _ List.mem_cons_self
        subst second
        cases rest with
        | nil => rfl
        | cons third later =>
          have equal : third = 1 := onlyOne _ (List.mem_cons_of_mem _ List.mem_cons_self)
          have strict : 1 < third := (List.pairwise_cons.mp tailIncreases).1 _ List.mem_cons_self
          omega
    · have zeroTail := List.mem_of_ne_of_mem (by decide : (0 : Nat) ≠ 1) zero
      have impossible := headLess 0 zeroTail
      omega

/-- Refutation of the indexed Proposition 79, including preservation of
external payloads and quantification over every replay of the retained steps. -/
theorem lemma79_counterexample :
    ¬ lemma79 (sem := semantics) trace noCoeffects := by
  intro claimed
  have operations : AdmittedCoeffects noCoeffects :=
    ⟨(fun key => nomatch key), (fun key => nomatch key)⟩
  have roots : RootInsertions trace := by
    intro t bound insertLabel
    have index : t = 0 := by
      have choices : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 := by omega
      rcases choices with rfl | rfl | rfl | rfl | rfl | rfl
      · rfl
      all_goals cases insertLabel
    subst t
    exact ⟨fresh component none, rfl, rfl⟩
  have total : TotalProvisions trace := fun _ _ _ fiber _ _ => total_provisions fiber
  obtain ⟨last, remaining, _, _, ⟨retained, increases, members, labels, commands⟩, equivalent⟩ :=
    claimed operations deletion_entries_admitted roots total quiet 0 2 5 closed_episode
      (fun _ _ _ _ ⟨_, _, key, _⟩ => nomatch key)
      (fun child born => False.elim (no_withdrawals child born))
  have selected : ∀ t, t ∈ retained ↔ t = 0 ∨ t = 1 := by
    intro t
    rw [members]
    change (t < 6 ∧ ¬ BornDuring trace 0 2 5 0 ∧ ¬ (2 ≤ t ∧ t ≤ 5 ∧ (0 : Nat) = 0)) ↔ _
    constructor
    · rintro ⟨bound, _, excluded⟩
      have outside : ¬ (2 ≤ t ∧ t ≤ 5) := fun h => excluded ⟨h.1, h.2, rfl⟩
      omega
    · rintro (rfl | rfl)
      · exact ⟨by decide, no_withdrawals 0, by decide⟩
      · exact ⟨by decide, no_withdrawals 0, by decide⟩
  have exactly := retained_pair increases selected
  subst retained
  have duration : last = 2 := by
    have lengths := congrArg List.length labels
    simpa [Labels] using lengths
  subst last
  let command : OrchestrationSorting.Command Nat Empty Bool := .insert 0 component
  have insertedReady : Insertable s0 0 component none :=
    ⟨rfl, by simp, by intro _ key; exact nomatch key⟩
  have original : CommandAt trace 0 command :=
    ⟨by decide, rfl, rfl, insertedReady, rfl⟩
  have kept := (commands 0 0 rfl command).mpr original
  have firstState : remaining.state 1 = s1 := by
    have first := kept.2.2.2.2
    change remaining.state 1 = put (remaining.state 0) 0 (fresh component none) at first
    rw [remaining.start] at first
    exact first
  have label : remaining.rule 1 = .begin ∧ remaining.actor 1 = 0 := by
    have secondLabel := congrArg (fun list : List (Labeled.Rule × Nat) => list[1]?) labels
    change some (remaining.rule 1, remaining.actor 1) = some (.begin, 0) at secondLabel
    have pair := Option.some.inj secondLabel
    exact ⟨congrArg Prod.fst pair, congrArg Prod.snd pair⟩
  have replay := remaining.step 1 (by decide)
  rw [label.1, label.2, firstState] at replay
  have whole : PaperStateObservation.Related semantics s6 (remaining.state 2) :=
    ⟨equivalent.1, fun name => equivalent.2 name (no_withdrawals name)⟩
  exact lemma79_no_replay_endpoint semantics replay whole

end DeletionCounterexample

end Cordis.Results
