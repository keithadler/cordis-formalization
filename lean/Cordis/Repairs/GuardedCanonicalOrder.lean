import Cordis.Repairs.GuardedCausalOrder

/-! Global priority order among schedules reached by guarded exchanges.
The complete exchange path stays in the original name set. -/
namespace Cordis.Repairs.GuardedHistory
open Calculus Stages LegalHistory
open GuardedBirthAddresses (StableActorAddresses)
open SupportAtQuiescence (TotalProvision)
open PaperEffectEquations (CoeffectOperations ValueOperationWitness)
open PaperObservationEquations (OperationRespects)
open PartialCoeffectIndependenceContracts (tableSetoid)
open TypedRegistry (encodeProgram Scalar)
open ExchangeReplay (exchangedCut exchangedIndex exchanged_stamp)

universe u
variable {Name Key Value Code Error : Type u} [DecidableEq Name] [DecidableEq Key]
variable {program : Code → Instruction Name Key Value Code Error} {last : Nat}

variable {V : Key → Type u} {ops : CoeffectOperations V}
variable {typedProgram : Code → TypedRegistry.Instruction Name ops Code}
local notation "A" => Scalar ops
local notation "Source" => Trace (encodeProgram typedProgram) last

/-- The path records the source stamp of every event, including across a
move that increases priority. Each edge witnesses all guards of the swap
and preservation of the endpoint and root input. -/
inductive ExchangePath [Setoid A] (source : Source) : Source → (Nat → Nat) → Prop
  | refl : ExchangePath source source id
  | swap {before after : Source} {expand : Nat → Nat} {point : Nat} :
      ExchangePath source before expand → point + 1 < last → StageExchange before point →
      StableActorAddresses before after (exchangedIndex point) →
      (∀ cut, cut < last → eventRoots (after.state cut) (after.event cut) =
        eventRoots (before.state (exchangedCut point cut)) (before.event (exchangedCut point cut))) →
      originalRoots after = originalRoots before →
      StageSimulation.Related Eq (before.state last) (after.state last) →
      (¬ Nonempty (ClosedEpisode after)) → Progress.Quiet (after.state last) →
      ExchangePath source after (expand ∘ exchangedIndex point)

theorem ExchangePath.preserves [Setoid A] {source result : Source} {expand : Nat → Nat}
    (path : ExchangePath source result expand)
    (self : StageSimulation.Related Eq (source.state last) (source.state last))
    (opened : ¬ Nonempty (ClosedEpisode source)) (quiet : Progress.Quiet (source.state last)) :
    StableActorAddresses source result expand ∧ originalRoots result = originalRoots source ∧
      StageSimulation.Related Eq (source.state last) (result.state last) ∧
      (¬ Nonempty (ClosedEpisode result)) ∧ Progress.Quiet (result.state last) := by
  induction path with
  | refl => exact ⟨.refl source, rfl, self, opened, quiet⟩
  | swap _ _ _ stable _ roots endpoint resultOpen resultQuiet ih =>
    obtain ⟨retained, oldRoots, oldEndpoint, _, _⟩ := ih
    exact ⟨retained.trans stable, roots.trans oldRoots,
      StageSimulation.Related.trans (Q := Eq) (fun a b => a.trans b) oldEndpoint endpoint,
      resultOpen, resultQuiet⟩

theorem ExchangePath.root_classification [Setoid A] {source result : Source} {expand : Nat → Nat}
    (path : ExchangePath source result expand) (cut : Nat) (bounded : cut < last) :
    eventRoots (result.state cut) (result.event cut) =
      eventRoots (source.state (expand (cut + 1) - 1)) (source.event (expand (cut + 1) - 1)) := by
  induction path generalizing cut with
  | refl => simp
  | @swap before after expand point path pair exchange stable classified roots endpoint opened quiet ih =>
    have inside : exchangedCut point cut < last := by
      unfold exchangedCut
      split
      · exact pair
      · split <;> omega
    exact (classified cut bounded).trans (by
      simpa only [Function.comp_apply, exchanged_stamp] using ih _ inside)

/-- Use priority zero for root commands and strictly positive priorities
for all other events. Callers can order stages and child commands within
the latter group. -/
def rootFirstPriority (trace : Trace program last) (otherwise : Nat → Nat) (stamp : Nat) : Nat :=
  if (eventRoots (trace.state (stamp - 1)) (trace.event (stamp - 1))).isEmpty then otherwise stamp + 1 else 0

theorem ExchangePath.roots_at_barriers [Setoid A] {source result : Source} {expand : Nat → Nat}
    (path : ExchangePath source result expand) (otherwise : Nat → Nat)
    (ordered : ∀ cut, cut + 1 < last → StageExchange result cut →
      rootFirstPriority source otherwise (expand (cut + 1)) ≤
        rootFirstPriority source otherwise (expand (cut + 2))) : RootsAtBarriers result := by
  apply roots_at_barriers_of_no_preferred_root
  intro cut bounded first second swap
  have firstClass := path.root_classification cut (by omega)
  have secondClass := path.root_classification (cut + 1) bounded
  have priorities := ordered cut bounded swap
  unfold rootFirstPriority at priorities
  rw [← firstClass, show cut + 2 = (cut + 1) + 1 by omega, ← secondClass] at priorities
  simp [first, List.isEmpty_iff, second] at priorities

private theorem least_nat (p : Nat → Prop) (existsValue : ∃ value, p value) :
    ∃ least, p least ∧ ∀ value, p value → least ≤ value := by
  classical
  obtain ⟨value, valid⟩ := existsValue
  induction value using Nat.strongRecOn with
  | ind value ih =>
    by_cases lower : ∃ next, next < value ∧ p next
    · obtain ⟨next, lt, validNext⟩ := lower
      exact ih next lt validNext
    · exact ⟨value, valid, fun next validNext => Nat.le_of_not_gt (fun lt => lower ⟨next, lt, validNext⟩)⟩

/-- At a fixed length, lexicographic comparison of natural priority words
has a least element in every nonempty set. -/
theorem least_priority_word (length : Nat) (p : List Nat → Prop)
    (inhabited : ∃ word, word.length = length ∧ p word) :
    ∃ least, least.length = length ∧ p least ∧
      ∀ word, word.length = length → p word → least ≤ word := by
  induction length generalizing p with
  | zero =>
    obtain ⟨word, length, valid⟩ := inhabited
    have empty := List.length_eq_zero_iff.mp length
    subst word
    exact ⟨[], rfl, valid, fun word _ _ => List.nil_le word⟩
  | succ length ih =>
    have occupied : ∃ head, ∃ tail : List Nat, tail.length = length ∧ p (head :: tail) := by
      obtain ⟨word, size, valid⟩ := inhabited
      cases word with
      | nil => simp at size
      | cons head tail => exact ⟨head, tail, Nat.succ.inj size, valid⟩
    obtain ⟨head, headExists, headLeast⟩ := least_nat _ occupied
    obtain ⟨tail, tailSize, valid, tailLeast⟩ := ih (fun tail => p (head :: tail)) headExists
    refine ⟨head :: tail, congrArg Nat.succ tailSize, valid, ?_⟩
    intro word size wordValid
    cases word with
    | nil => simp at size
    | cons other rest =>
      have restSize := Nat.succ.inj size
      rcases Nat.lt_or_eq_of_le (headLeast other ⟨rest, restSize, wordValid⟩) with earlier | same
      · exact List.le_of_lt (.rel earlier)
      · subst other
        intro smaller
        rcases List.cons_lex_cons_iff.mp smaller with impossible | ⟨_, smallerTail⟩
        · exact Nat.lt_irrefl _ impossible
        · exact tailLeast rest restSize wordValid smallerTail

private def eventPriorityKey (last : Nat) (priority : Nat → Nat) (stamp : Nat) : Nat :=
  priority stamp * (last + 1) + stamp

/-- Equal priorities are resolved by the source stamps that move with events. -/
def exchangePriorityWord (last : Nat) (priority expand : Nat → Nat) : List Nat :=
  (List.range last).map fun cut => eventPriorityKey last priority (expand (cut + 1))

private theorem exchangePriorityWord_length (last : Nat) (priority expand : Nat → Nat) :
    (exchangePriorityWord last priority expand).length = last := by
  simp [exchangePriorityWord]

private theorem eventPriorityKey_lt {priority : Nat → Nat} {first second : Nat}
    (firstBound : first ≤ last) (earlier : priority first < priority second) :
    eventPriorityKey last priority first < eventPriorityKey last priority second := by
  have order : (priority first + 1) * (last + 1) ≤ priority second * (last + 1) :=
    Nat.mul_le_mul_right _ earlier
  rw [Nat.add_mul, Nat.one_mul] at order
  unfold eventPriorityKey
  omega

private theorem lex_append_prefix (initial : List Nat) {first second : List Nat} (before : first < second) :
    initial ++ first < initial ++ second := by
  induction initial with
  | nil => exact before
  | cons _ _ ih => exact .cons ih

theorem exchangePriorityWord_lt_at {priority first second : Nat → Nat} {point : Nat}
    (bounded : point + 1 < last)
    (before : ∀ cut, cut < point → first (cut + 1) = second (cut + 1))
    (bound : first (point + 1) ≤ last)
    (earlier : priority (first (point + 1)) < priority (second (point + 1))) :
    exchangePriorityWord last priority first < exchangePriorityWord last priority second := by
  unfold exchangePriorityWord
  rw [cut_range_pair bounded, List.map_append, List.map_append]
  have initial := List.map_congr_left (l := List.range point) (f := fun cut => eventPriorityKey last priority (first (cut + 1)))
    (g := fun cut => eventPriorityKey last priority (second (cut + 1)))
    (fun cut member => congrArg _ (before cut (List.mem_range.mp member)))
  rw [initial]
  apply lex_append_prefix
  exact .rel (eventPriorityKey_lt bound earlier)

private theorem exchangePriorityWord_swap_lt {priority expand : Nat → Nat} {point : Nat}
    (bounded : point + 1 < last)
    (bound : expand (point + 2) ≤ last)
    (inversion : priority (expand (point + 2)) < priority (expand (point + 1))) :
    exchangePriorityWord last priority (expand ∘ exchangedIndex point) < exchangePriorityWord last priority expand := by
  apply exchangePriorityWord_lt_at bounded _ _ _
  · intro cut earlier
    rw [Function.comp_apply, ExchangeReplay.exchangedIndex_other (by omega) (by omega)]
  · simpa only [Function.comp_apply, ExchangeReplay.exchangedIndex_first] using bound
  · simpa only [Function.comp_apply, ExchangeReplay.exchangedIndex_first] using inversion

theorem exchangePriorityWord_stamp {priority left right : Nat → Nat}
    (same : exchangePriorityWord last priority left = exchangePriorityWord last priority right)
    {cut : Nat} (bounded : cut < last) (leftBound : left (cut + 1) ≤ last)
    (rightBound : right (cut + 1) ≤ last) : left (cut + 1) = right (cut + 1) := by
  have atCut := congrArg (fun word : List Nat => word[cut]?) same
  have keys : eventPriorityKey last priority (left (cut + 1)) = eventPriorityKey last priority (right (cut + 1)) := by
    simpa [exchangePriorityWord, List.getElem?_map, List.getElem?_range, bounded] using atCut
  have residues := congrArg (fun key => key % (last + 1)) keys
  simpa [eventPriorityKey, Nat.add_mod, Nat.mod_eq_of_lt (Nat.lt_succ_of_le leftBound),
    Nat.mod_eq_of_lt (Nat.lt_succ_of_le rightBound)] using residues

/-- A representative with globally least priority word among all guarded
exchange paths from the given surviving history, with no fresh-name
assumption. The minimum ranges over paths that can increase priority. -/
theorem Trace.order_globally_by_event_priority (trace : Source) (priority : Nat → Nat)
    (openOnly : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r) :
    letI : Setoid A := TypedCoeffectReplay.setoid observe
    ∃ (result : Source) (expand : Nat → Nat), ExchangePath trace result expand ∧
      (∀ (other : Source) (embed : Nat → Nat), ExchangePath trace other embed →
        exchangePriorityWord last priority expand ≤ exchangePriorityWord last priority embed) ∧
      (∀ cut, cut + 1 < last → StageExchange result cut →
        priority (expand (cut + 1)) ≤ priority (expand (cut + 2))) := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  let realizes (word : List Nat) := ∃ (result : Source) (expand : Nat → Nat),
    ExchangePath trace result expand ∧ exchangePriorityWord last priority expand = word
  obtain ⟨least, _, ⟨result, expand, path, rfl⟩, minimal⟩ :=
    least_priority_word last realizes ⟨_, exchangePriorityWord_length _ _ _, trace, id, .refl, rfl⟩
  have best (other : Source) (embed : Nat → Nat) (reachable : ExchangePath trace other embed) :=
    minimal _ (exchangePriorityWord_length _ _ _) ⟨other, embed, reachable, rfl⟩
  refine ⟨result, expand, path, best, ?_⟩
  intro cut bounded exchange
  apply Nat.le_of_not_gt
  intro inversion
  have self := trace.self_related last (Nat.le_refl _)
    (TypedRegistry.encoded_program_callbacks ops observe typedProgram recovery commutative)
  obtain ⟨stable, _, _, opened, settled⟩ := path.preserves self openOnly quiet
  obtain ⟨moved, _, classification, roots, endpoint, movedOpen, movedQuiet, retained, _⟩ :=
    exchange.perform result bounded opened settled observe recovery commutative respect
  have next := path.swap bounded exchange (exchange.stable_addresses bounded retained)
    classification roots endpoint movedOpen movedQuiet
  exact best moved _ next (exchangePriorityWord_swap_lt bounded
    (stable.retained.stamp (cut + 1) bounded).2 inversion)

/-- All least reachable representatives place the same source event at
each cut. This includes the case of equal assigned priorities. -/
theorem ExchangePath.least_order_unique [Setoid A] {source left right : Source}
    {first second priority : Nat → Nat}
    (leftPath : ExchangePath source left first) (rightPath : ExchangePath source right second)
    (leftLeast : ∀ other embed, ExchangePath source other embed →
      exchangePriorityWord last priority first ≤ exchangePriorityWord last priority embed)
    (rightLeast : ∀ other embed, ExchangePath source other embed →
      exchangePriorityWord last priority second ≤ exchangePriorityWord last priority embed)
    (self : StageSimulation.Related Eq (source.state last) (source.state last))
    (opened : ¬ Nonempty (ClosedEpisode source)) (quiet : Progress.Quiet (source.state last))
    {cut : Nat} (bounded : cut < last) :
    first (cut + 1) = second (cut + 1) ∧ left.event cut = right.event cut := by
  have leftRetained := (leftPath.preserves self opened quiet).1.retained
  have rightRetained := (rightPath.preserves self opened quiet).1.retained
  have same := List.le_antisymm (leftLeast right second rightPath) (rightLeast left first leftPath)
  have stamp := exchangePriorityWord_stamp same bounded (leftRetained.stamp cut bounded).2
    (rightRetained.stamp cut bounded).2
  exact ⟨stamp, (leftRetained.label cut bounded).trans (by rw [stamp, ← rightRetained.label cut bounded])⟩

/-- Excise closed episodes and return an actual path to the least order
reachable from the survivors. Root priority is based on the surviving
event's original classification within that history. The retained map
uses the initial stamps through both phases. -/
theorem normalize_globally_by_event_priority (trace : Source) (priority : Nat → Nat)
    (quiet : Progress.Quiet (trace.state last))
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r) :
    letI : Setoid A := TypedCoeffectReplay.setoid observe
    ∃ (length : Nat) (reduced result : Trace (encodeProgram typedProgram) length) (before after : Nat → Nat),
      length ≤ last ∧ ExchangePath reduced result after ∧
      (∀ other embed, ExchangePath reduced other embed →
        exchangePriorityWord length (rootFirstPriority reduced (priority ∘ before)) after ≤
          exchangePriorityWord length (rootFirstPriority reduced (priority ∘ before)) embed) ∧
      RootsAtBarriers result ∧
      RetainedEvents trace result (before ∘ after) ∧ originalRoots result = originalRoots trace ∧
      (¬ Nonempty (ClosedEpisode result)) ∧ Progress.Quiet (result.state length) ∧
      (TotalProvision (trace.state last) → TotalProvision (result.state length)) ∧
      ∃ projected, VestigeErasures (trace.state last) projected ∧
        StageSimulation.Related Eq projected (result.state length) := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  obtain ⟨length, reduced, before, bound, opened, excised, roots, _, reducedQuiet, total, projected, erased, alignment⟩ :=
    eliminate_closed_episodes trace quiet observe recovery commutative respect
  obtain ⟨result, after, path, least, localOrder⟩ := reduced.order_globally_by_event_priority
    (rootFirstPriority reduced (priority ∘ before)) opened reducedQuiet observe recovery commutative respect
  have self := reduced.self_related length (Nat.le_refl _)
    (TypedRegistry.encoded_program_callbacks ops observe typedProgram recovery commutative)
  obtain ⟨stable, resultRoots, endpoint, finalOpen, finalQuiet⟩ := path.preserves self opened reducedQuiet
  exact ⟨length, reduced, result, before, after, bound, path, least,
    path.roots_at_barriers (priority ∘ before) localOrder, excised.trans stable.retained,
    resultRoots.trans roots, finalOpen, finalQuiet, fun provisions => related_total_provision endpoint (total provisions),
    projected, erased, StageSimulation.Related.trans (Q := Eq) (fun a b => a.trans b) alignment endpoint⟩

end Cordis.Repairs.GuardedHistory
