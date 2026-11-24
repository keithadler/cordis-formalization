import Cordis.TypedRegistrySupport
import Cordis.Repairs.GuardedEpisodeBoundary
import Init.Data.List.Sort.Lemmas

/-!
The active part of the support relation can be linearized using the order
of installed episodes. A count of declarations or an empty-table hypothesis
is unnecessary. The order is consumed by the open-episode sorting argument.
-/
namespace Cordis.Repairs.SupportLinearization

open Calculus Stages SupportAtQuiescence SupportUniqueness
universe u
variable {Name Key Value Code Error : Type u} [DecidableEq Name] [DecidableEq Key]
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
local notation "Program" => Code → Instruction Name Key Value Code Error

structure Linearization (members : Name → Prop) (edge : Name → Name → Prop)
    (order : List Name) : Prop where
  nodup : order.Nodup
  exact_members : ∀ name, name ∈ order ↔ members name
  ordered : ∀ first later, FiniteOrder.Chain edge first later → [first, later].Sublist order

/-- Repaired Lemma 75 at any cut of a guarded history. -/
theorem guarded_support_consultations {program : Program} {last time : Nat}
    (trace : GuardedHistory.Trace program last) (bounded : time ≤ last)
    (acyclic : FiniteOrder.Acyclic (Results.UninstalledSupportDependencies (trace.state time))) :
    WellFounded (Results.SupportConsults (trace.state time)) ∧
      ∃ support, Solution (trace.state time) support ∧
        ∀ other, Solution (trace.state time) other → other = support := by
  obtain ⟨owned, disjoint⟩ := trace.ownership time bounded
  have ordered := Results.supportConsults_wellFounded_of_ranked (trace.support_finite time bounded)
    (trace.support_ranked time bounded) (trace.child_provenance time bounded)
    owned (trace.supported time bounded) disjoint acyclic
  exact ⟨ordered, Results.support_unique_of_consulted_wellFounded _ ordered⟩

/-- Repaired Lemma 77 on the guarded endpoint itself. -/
theorem guarded_support_active {program : Program} {last : Nat}
    (trace : GuardedHistory.Trace program last)
    (acyclic : FiniteOrder.Acyclic (Results.UninstalledSupportDependencies (trace.state last)))
    (quiet : Progress.Quiet (trace.state last)) (total : TotalProvision (trace.state last)) :
    WellFounded (Results.SupportConsults (trace.state last)) ∧
      Solution (trace.state last) (Active (trace.state last)) ∧
      ∀ set, Solution (trace.state last) set → set = Active (trace.state last) := by
  obtain ⟨ordered, solution, _, unique⟩ := guarded_support_consultations trace (Nat.le_refl _) acyclic
  have fixed := active_solution_of_capture (trace.child_provenance last (Nat.le_refl _)) quiet total
  exact ⟨ordered, fixed, fun set solved => (unique set solved).trans (unique _ fixed).symm⟩

private def deduplicate : List Name → List Name
  | [] => []
  | name :: tail =>
    let unique := deduplicate tail
    if name ∈ unique then unique else name :: unique

private theorem deduplicate_members (names : List Name) (name : Name) :
    name ∈ deduplicate names ↔ name ∈ names := by
  induction names generalizing name with
  | nil => rfl
  | cons first rest ih =>
    by_cases duplicate : first ∈ deduplicate rest
    · have inRest := (ih first).mp duplicate
      simp only [deduplicate, if_pos duplicate, ih name, List.mem_cons]
      exact ⟨Or.inr, fun found => found.elim (fun eq => eq.symm ▸ inRest) id⟩
    · simp [deduplicate, duplicate, ih name]

private theorem deduplicate_nodup (names : List Name) : (deduplicate names).Nodup := by
  induction names with
  | nil => simp [deduplicate]
  | cons first rest ih => by_cases duplicate : first ∈ deduplicate rest <;> simp [deduplicate, duplicate, ih]

omit [DecidableEq Name] in
private theorem ordered_pair {rank : Name → Nat} {names : List Name}
    (sorted : names.Pairwise (fun a b => rank a ≤ rank b))
    {first later : Name} (inOrder : first ∈ names) (laterIn : later ∈ names)
    (ascending : rank first < rank later) : [first, later].Sublist names := by
  induction names with
  | nil => cases inOrder
  | cons head tail ih =>
    obtain ⟨smallest, sortedTail⟩ := List.pairwise_cons.mp sorted
    by_cases firstHead : first = head
    · subst head
      have laterTail : later ∈ tail := (List.mem_cons.mp laterIn).resolve_left (fun same =>
        Nat.lt_irrefl _ (same ▸ ascending))
      exact (List.singleton_sublist.mpr laterTail).cons₂ first
    · have firstTail := (List.mem_cons.mp inOrder).resolve_left firstHead
      have laterTail : later ∈ tail := (List.mem_cons.mp laterIn).resolve_left (fun same =>
        (Nat.not_le_of_gt (same ▸ ascending)) (smallest first firstTail))
      exact (ih sortedTail firstTail laterTail).cons head

omit [DecidableEq Name] in
private theorem sublist_forces_prefix {first later : Name} {front suffix : List Name}
    (unique : (front ++ later :: suffix).Nodup)
    (ordered : [first, later].Sublist (front ++ later :: suffix)) :
    first ∈ front := by
  induction front with
  | nil =>
    have absent := (List.nodup_cons.mp unique).1
    rcases List.sublist_cons_iff.mp ordered with small | ⟨rest, eq, small⟩
    · exact False.elim (absent (small.subset (by simp)))
    · have restEq : rest = [later] := (List.cons.inj eq).2.symm
      subst rest
      exact False.elim (absent (small.subset (by simp)))
  | cons head tail ih =>
    rcases List.sublist_cons_iff.mp ordered with remaining | ⟨rest, eq, _⟩
    · exact List.mem_cons_of_mem _ (ih (List.nodup_cons.mp unique).2 remaining)
    · exact List.mem_cons.mpr (Or.inl (List.cons.inj eq).1)

omit [DecidableEq Name] in
theorem Linearization.preceding {members : Name → Prop} {edge : Name → Name → Prop}
    {front suffix : List Name} {first later : Name}
    (plan : Linearization members edge (front ++ later :: suffix))
    (before : FiniteOrder.Chain edge first later) : first ∈ front :=
  sublist_forces_prefix plan.nodup (plan.ordered first later before)

omit [DecidableEq Key] in
private theorem linearize_by_rank (members : Name → Prop) (edge : Name → Name → Prop)
    (names : List Name) (covered : ∀ name, members name → name ∈ names)
    (rank : Name → Nat) (decreases : ∀ a b, edge a b → rank a < rank b)
    (ends : ∀ a b, edge a b → members a ∧ members b) :
    ∃ order, Linearization members edge order := by
  classical
  let candidates := deduplicate (names.filter fun name => decide (members name))
  let earlier : Name → Name → Bool := fun a b => decide (rank a ≤ rank b)
  let order := candidates.mergeSort earlier
  have rankSorted : order.Pairwise (fun a b => rank a ≤ rank b) := by
    have transitive : ∀ a b c, earlier a b → earlier b c → earlier a c := by
      intro a b c ab bc
      have first : rank a ≤ rank b := by simpa only [earlier, decide_eq_true_eq] using ab
      have second : rank b ≤ rank c := by simpa only [earlier, decide_eq_true_eq] using bc
      simpa only [earlier, decide_eq_true_eq] using Nat.le_trans first second
    have total : ∀ a b, earlier a b || earlier b a := by
      intro a b
      simpa only [earlier, Bool.or_eq_true, decide_eq_true_eq] using Nat.le_total (rank a) (rank b)
    exact (List.sorted_mergeSort transitive total candidates).imp (by simp [earlier])
  have inOrder : ∀ name, name ∈ order ↔ members name := by
    intro name
    simp only [order, List.mem_mergeSort, candidates, deduplicate_members, List.mem_filter, decide_eq_true_eq]
    exact ⟨And.right, fun member => ⟨covered name member, member⟩⟩
  refine ⟨order, ⟨(List.mergeSort_perm _ _).nodup_iff.mpr (deduplicate_nodup _), inOrder, ?_⟩⟩
  intro first later chain
  have relationRank : rank first < rank later ∧ members first ∧ members later := by
    induction chain with
    | single edge => exact ⟨decreases _ _ edge, ends _ _ edge⟩
    | tail _ edge previous =>
      exact ⟨Nat.lt_trans previous.1 (decreases _ _ edge), previous.2.1, (ends _ _ edge).2⟩
  exact ordered_pair rankSorted ((inOrder first).mpr relationRank.2.1)
    ((inOrder later).mpr relationRank.2.2) relationRank.1

/-- Every quiescent reachable endpoint with total provisions admits an
enumeration of active episodes respecting the transitive support order.
The active order itself needs no acyclicity premise on inactive names. -/
theorem active_linearization (program : Program) {state : R}
    (run : Orchestration.Run program (fun _ => none) state)
    (quiet : Progress.Quiet state) (total : TotalProvision state) :
    ∃ order, Linearization (Active state) (ActivePredecessor state) order := by
  obtain ⟨names, covered⟩ := reachable_finite program run
  obtain ⟨rank, _, _, ordered⟩ := SupportOrder.reachable_ranked program run
  have invariants := run.reachable_invariants
  have fixed := active_solution_of_capture (ChildProvenance.reachable_captured program run) quiet total
  apply linearize_by_rank (Active state) (ActivePredecessor state) names ?_ rank
    (fun _ _ edge => active_edge_decreases state rank ordered invariants.2.2.1 invariants.2.1
      (reachable_disjoint program run) fixed edge) (fun _ _ edge => ⟨edge.2.1, edge.1⟩)
  rintro name ⟨fiber, found, _⟩
  exact covered name fiber found

/-- Lemmas 75 and 77 supply the unique supported set and identify it with
the active set. This packages the exact finite order needed for normalization. -/
theorem support_linearization (program : Program) {state : R}
    (run : Orchestration.Run program (fun _ => none) state)
    (acyclic : FiniteOrder.Acyclic (Progress.Depends state))
    (quiet : Progress.Quiet state) (total : TotalProvision state) :
    Solution state (Active state) ∧
      (∀ set, Solution state set → set = Active state) ∧
      ∃ order, Linearization (Active state) (ActivePredecessor state) order := by
  obtain ⟨fixed, unique⟩ := Results.lemma77 program run acyclic quiet total
  exact ⟨fixed, unique, active_linearization program run quiet total⟩

omit [DecidableEq Name] [DecidableEq Key] in
theorem parent_precedes {state : R} {front rest : List Name} {name parent : Name} {fiber : F}
    (plan : Linearization (Active state) (ActivePredecessor state) (front ++ name :: rest))
    (fixed : Solution state (Active state))
    (present : state name = some fiber) (parentOf : fiber.parent = some parent) :
    parent ∈ front := by
  have active := (plan.exact_members name).mp (by simp)
  obtain ⟨entry, found, _, ancestry, _⟩ := (fixed name).mp active
  have same := Option.some.inj (found.symm.trans present)
  subst entry
  rcases ancestry with root | ⟨ancestor, chosen, earlier⟩
  · rw [parentOf] at root
    cases root
  · have identifies := Option.some.inj (parentOf.symm.trans chosen)
    subst ancestor
    obtain ⟨parentEntry, parentFound, available⟩ := earlier
    exact plan.preceding (.single ⟨active, ⟨_, parentFound, available⟩,
      fiber, parentEntry, present, parentFound, .inl parentOf⟩)

omit [DecidableEq Name] [DecidableEq Key] in
/-- The concrete provider in the final committed view precedes its
consumer. The key is bound at the final provider as well as declared. -/
theorem provider_precedes {state : R} {front rest : List Name} {name : Name} {fiber : F}
    (plan : Linearization (Active state) (ActivePredecessor state) (front ++ name :: rest))
    (quiet : Progress.Quiet state) (owned : Safety.Owned state)
    (present : state name = some fiber) :
    ∃ view, fiber.phase.committed = some view ∧
      ∀ key, fiber.component.requires key = true → view key ∈ front ∧
        ∃ provider, state (view key) = some provider ∧ provider.phase.available ∧ provider.table key ≠ none := by
  obtain ⟨activeEntry, activeFound, available⟩ := (plan.exact_members name).mp (by simp)
  have same := Option.some.inj (activeFound.symm.trans present)
  subst activeEntry
  have condition := quiet name fiber present
  cases phase : fiber.phase with
  | inactive | reloading | unloading => simp [phase, Phase.available] at available
  | active word view =>
    refine ⟨view, rfl, ?_⟩
    have target : Target state name view := by simpa only [phase] using condition
    simp only [Target, present] at target
    intro key required
    have bound := target.2 key required
    cases providerAt : state (view key) with
    | none => simp [providerAt] at bound
    | some provider =>
      simp only [providerAt] at bound
      have provides := owned (view key) provider key providerAt bound.2
      refine ⟨plan.preceding (.single ?_), provider, rfl, bound⟩
      exact ⟨⟨fiber, present, available⟩, ⟨provider, providerAt, bound.1⟩,
        fiber, provider, present, providerAt, .inr ⟨key, required, provides⟩⟩

/-- In a replay, once the earlier providers offer their required bindings,
the next inactive actor can begin with its original committed view. The
caller supplies the replay results for the earlier episodes. -/
theorem begin_with_committed_view (program : Program) {state before : R} {front rest : List Name}
    {name : Name} {source replay : F}
    (plan : Linearization (Active state) (ActivePredecessor state) (front ++ name :: rest))
    (quiet : Progress.Quiet state) (owned : Safety.Owned state)
    (sourceAt : state name = some source) (replayAt : before name = some replay)
    (component : replay.component = source.component) (live : replay.retired = false)
    (inactive : replay.phase = .inactive)
    (completed : ∀ provider ∈ front, ∀ key entry,
      state provider = some entry → entry.table key ≠ none →
      ∃ row, before provider = some row ∧ row.phase.available ∧ row.table key ≠ none) :
    ∃ view, source.phase.committed = some view ∧
      Labeled.Step program .begin name before (mark before name (.reloading replay.component.entry [] view)) := by
  obtain ⟨view, original, requirements⟩ := provider_precedes plan quiet owned sourceAt
  refine ⟨view, original, .begin _ _ replay view replayAt inactive (by simp [replayAt]) ?_⟩
  simp only [Target, replayAt]
  refine ⟨live, ?_⟩
  intro key required
  obtain ⟨earlier, provider, providerAt, _, bound⟩ := requirements key (component ▸ required)
  obtain ⟨row, rowAt, available, offered⟩ := completed (view key) earlier key provider providerAt bound
  simp only [rowAt]
  exact ⟨available, offered⟩

end Cordis.Repairs.SupportLinearization

namespace Cordis.Repairs.SupportLinearization
open PaperEffectEquations (CoeffectOperations)
open TypedRegistry
universe u
variable {Name Key Code : Type u} {V : Key → Type u}
variable [DecidableEq Name] [DecidableEq Key]
variable {ops : CoeffectOperations V}
local notation "R" => TypedRegistry.Registry Name V Code

/-- Equation (62) only consults predecessors of live entries. A retired
entry already fails the first clause. -/
def ConsultedSupport (state : R) (prior name : Name) : Prop :=
  (∃ fiber, state name = some fiber ∧ fiber.retired = false) ∧ supportEdge state prior name

def ActiveSupport (state : R) (prior name : Name) : Prop :=
  Active state prior ∧ Active state name ∧ supportEdge state prior name

omit [DecidableEq Name] [DecidableEq Key] in
private theorem raw_support {state : RawRegistry Name ops Code} {prior name : Name}
    (edge : PaperLifecycleClaims.supportEdge state prior name) :
    Results.SupportRelation state prior name := by
  rcases edge.2.2 with dep | parent
  · obtain ⟨key, ⟨provider, providerAt, supplies⟩, ⟨consumer, consumerAt, required⟩⟩ := dep
    exact .inl ⟨consumer, provider, key, consumerAt, providerAt, required, supplies⟩
  · obtain ⟨fiber, found, parentOf⟩ := Option.bind_eq_some_iff.mp parent
    exact .inr ⟨fiber, found, parentOf⟩

/-- Repaired Lemma 75 on the heterogeneous calculus. The relation used by
the recursion is well founded and the original support equation has a
unique solution. Actual coeffect bindings can be present throughout. -/
theorem typed_support_consultations_of_uninstalled {program : Code → Instruction Name ops Code} {last : Nat}
    (trace : Trace program (fun _ => none) last) (roots : trace.RootInsertions)
    (acyclic : FiniteOrder.Acyclic (uninstalledSupportDependencies (trace.state last))) :
    WellFounded (ConsultedSupport (trace.state last)) ∧
      ∃ support, SupportSolution (trace.state last) support ∧
        ∀ other, SupportSolution (trace.state last) other → other = support := by
  have run := Results.rootTrace trace.encode (trace.encode_roots roots) last (Nat.le_refl _)
  have rawAcyclic : FiniteOrder.Acyclic (Results.UninstalledSupportDependencies (trace.encode.state last)) := by
    simpa only [Trace.encode, uninstalledSupportDependencies_encode] using acyclic
  have order := Results.lemma75_consulted_edges_wellFounded_of_uninstalled (encodeProgram program) run rawAcyclic
  refine ⟨Subrelation.wf ?_ order, lemma75_typed_unique_of_uninstalled trace roots acyclic⟩
  rintro prior name ⟨⟨row, found, live⟩, edge⟩
  have encoded : PaperLifecycleClaims.supportEdge (trace.encode.state last) prior name := by
    simpa only [Trace.encode, supportEdge_encode] using edge
  exact ⟨⟨encodeFiber ops row, encode_row found, live⟩, raw_support encoded⟩

theorem typed_support_consultations {program : Code → Instruction Name ops Code} {last : Nat}
    (trace : Trace program (fun _ => none) last) (roots : trace.RootInsertions)
    (acyclic : FiniteOrder.Acyclic (precedes (trace.state last))) :
    WellFounded (ConsultedSupport (trace.state last)) ∧
      ∃ support, SupportSolution (trace.state last) support ∧
        ∀ other, SupportSolution (trace.state last) other → other = support := by
  apply typed_support_consultations_of_uninstalled trace roots
  have lift {first lastName : Name}
      (chain : FiniteOrder.Chain (uninstalledSupportDependencies (trace.state last)) first lastName) :
      FiniteOrder.Chain (precedes (trace.state last)) first lastName := by
    induction chain with
    | single edge => exact .single edge.1
    | tail _ edge ih => exact .tail ih edge.1
  exact fun name closed => acyclic name (lift closed)

omit [DecidableEq Name] in
private theorem active_predecessor {state : R} {prior name : Name}
    (edge : ActiveSupport state prior name) :
    SupportUniqueness.ActivePredecessor (encodeRegistry ops state) prior name := by
  obtain ⟨earlier, later, support⟩ := edge
  rw [← active_encode (ops := ops) state] at earlier later
  have rawEdge : PaperLifecycleClaims.supportEdge (encodeRegistry ops state) prior name := by
    simpa only [supportEdge_encode] using support
  obtain ⟨provider, providerAt, providerActive⟩ := earlier
  obtain ⟨consumer, consumerAt, consumerActive⟩ := later
  refine ⟨⟨consumer, consumerAt, consumerActive⟩, ⟨provider, providerAt, providerActive⟩,
    consumer, provider, consumerAt, providerAt, ?_⟩
  rcases raw_support rawEdge with dependency | ⟨entry, found, same⟩
  · obtain ⟨requires, provides, key, demandAt, supplyAt, required, supplied⟩ := dependency
    have consumerEq := Option.some.inj (demandAt.symm.trans consumerAt)
    have providerEq := Option.some.inj (supplyAt.symm.trans providerAt)
    exact .inr ⟨key, consumerEq ▸ required, providerEq ▸ supplied⟩
  · exact .inl (Option.some.inj (found.symm.trans consumerAt) ▸ same)

theorem typed_active_linearization {program : Code → Instruction Name ops Code} {last : Nat}
    (trace : Trace program (fun _ => none) last) (roots : trace.RootInsertions)
    (quiet : Quiet (trace.state last)) (total : TotalProvision (trace.state last)) :
    ∃ order, Linearization (Active (trace.state last)) (ActiveSupport (trace.state last)) order := by
  have run := Results.rootTrace trace.encode (trace.encode_roots roots) last (Nat.le_refl _)
  obtain ⟨order, plan⟩ := active_linearization (encodeProgram program) run
    ((quiet_encode_iff (ops := ops) _).mpr quiet) ((totalProvision_encode_iff (ops := ops) _).mpr total)
  refine ⟨order, ⟨plan.nodup, ?_, ?_⟩⟩
  · intro name
    simpa only [Trace.encode, active_encode] using plan.exact_members name
  · intro prior name chain
    have encoded : FiniteOrder.Chain
        (SupportUniqueness.ActivePredecessor (trace.encode.state last)) prior name := by
      induction chain with
      | single atom => exact .single (active_predecessor (ops := ops) atom)
      | tail _ atom previous => exact .tail previous (active_predecessor (ops := ops) atom)
    exact plan.ordered prior name encoded

end Cordis.Repairs.SupportLinearization
