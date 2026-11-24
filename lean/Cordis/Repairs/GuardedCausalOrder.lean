import Cordis.Repairs.GuardedNormalization
import Cordis.Repairs.GuardedBirthAddresses

/-! Stage ordering across command cuts. Every move is an actual guarded
exchange; a required reservation release stays ahead of its allocation. -/
namespace Cordis.Repairs.GuardedHistory
open Calculus Stages LegalHistory
open GuardedBirthAddresses (StableActorAddresses isRootInsertion)
open SupportAtQuiescence (TotalProvision)
open OrchestrationSorting (Command)
open PaperEffectEquations (CoeffectOperations ValueOperationWitness)
open PaperObservationEquations (OperationRespects)
open PartialCoeffectIndependenceContracts (tableSetoid)
open TypedRegistry (encodeProgram Scalar RawRegistry)
open ExchangeReplay (exchangedCut exchanged_stamp)
universe u
variable {Name Key Value Code Error : Type u} [DecidableEq Name] [DecidableEq Key]
variable {program : Code → Instruction Name Key Value Code Error} {last : Nat}
local notation "Cmd" => Command Name Key Code
local notation "Ev" => Event Name Key Code

/-- The earlier move preferred by the ordering proof. Root commands move
earlier where legal. Landings are ordered by their episode's opening and can
cross child commands, subject to the actual birth and provision guards. -/
inductive EarlierStage (trace : Trace program last) (rank : Name → Nat) (time : Nat) : Prop
  | rootPastActivation {kind : Lifecycle} {actor : Name} {root : Cmd} :
      trace.event time = .lifecycle kind actor → trace.event (time + 1) = .command root →
      commandRoots (trace.state (time + 1)) root ≠ [] → EarlierStage trace rank time
  | rootPastChild {child root : Cmd} :
      trace.event time = .command child → trace.event (time + 1) = .command root →
      commandRoots (trace.state time) child = [] → commandRoots (trace.state (time + 1)) root ≠ [] →
      rootMayCrossChild child root (trace.state time) → EarlierStage trace rank time
  | landingPastActivation {firstKind secondKind : Lifecycle} {first second : Name} :
      trace.event time = .lifecycle firstKind first → trace.event (time + 1) = .lifecycle secondKind second →
      rank second < rank first → EarlierStage trace rank time
  | landingPastChild {child : Cmd} {kind : Lifecycle} {actor : Name} :
      trace.event time = .command child → trace.event (time + 1) = .lifecycle kind actor →
      commandRoots (trace.state time) child = [] → kind ≠ .begin →
      commandMayFollowActivation child actor (trace.state time) (trace.state (time + 2)) →
      EarlierStage trace rank time

/-- The four adjacent exchanges used by stage ordering. A Begin can move
earlier if its own guards already hold at the earlier cut. -/
inductive StageExchange (trace : Trace program last) (time : Nat) : Prop
  | rootPastActivation {kind : Lifecycle} {actor : Name} {root : Cmd} :
      trace.event time = .lifecycle kind actor → trace.event (time + 1) = .command root →
      commandRoots (trace.state (time + 1)) root ≠ [] → StageExchange trace time
  | rootPastChild {child root : Cmd} :
      trace.event time = .command child → trace.event (time + 1) = .command root →
      commandRoots (trace.state time) child = [] → commandRoots (trace.state (time + 1)) root ≠ [] →
      rootMayCrossChild child root (trace.state time) → StageExchange trace time
  | activationPastActivation {firstKind secondKind : Lifecycle} {first second : Name} :
      trace.event time = .lifecycle firstKind first → trace.event (time + 1) = .lifecycle secondKind second →
      first ≠ second → (secondKind = .begin → ∃ view, Target (trace.state time) second view) → StageExchange trace time
  | activationPastChild {child : Cmd} {kind : Lifecycle} {actor : Name} :
      trace.event time = .command child → trace.event (time + 1) = .lifecycle kind actor →
      commandRoots (trace.state time) child = [] →
      commandMayFollowActivation child actor (trace.state time) (trace.state (time + 2)) → StageExchange trace time

theorem StageExchange.stable_addresses {trace moved : Trace program last} {point : Nat}
    (exchange : StageExchange trace point) (bounded : point + 1 < last)
    (retained : RetainedEvents trace moved (ExchangeReplay.exchangedIndex point)) :
    StableActorAddresses trace moved (ExchangeReplay.exchangedIndex point) := by
  have commandNotStage {i : Nat} {cmd : Cmd} (command : trace.event i = .command cmd) :
      EpisodeSelection.canBirth (trace.rule i) = false := by
    cases cmd <;> simp [Trace.rule, command, eventRule, ExchangeReplay.commandRule, EpisodeSelection.canBirth]
  apply StableActorAddresses.adjacent bounded retained
  · cases exchange with
    | rootPastActivation first _ _ | activationPastActivation first _ _ _ => simp [isRootInsertion, first]
    | activationPastChild _ second _ _ => simp [isRootInsertion, second]
    | @rootPastChild child _ first _ classified _ _ =>
      cases child with
      | insert => simp [commandRoots] at classified
      | retire | remove => simp [isRootInsertion, first]
  · intro a b
    cases exchange with
    | rootPastActivation _ command _ => rw [commandNotStage command] at b; cases b
    | rootPastChild command _ _ _ _ | activationPastChild command _ _ _ =>
      rw [commandNotStage command] at a; cases a
    | activationPastActivation first second distinct _ =>
      simpa [Trace.actor, first, second, Vestigial.eventActor] using distinct

private theorem EarlierStage.admissible {trace : Trace program last} {rank : Name → Nat} {time : Nat}
    (exchange : EarlierStage trace rank time) (bounded : time + 1 < last)
    (chronological : ChronologicalOpenings trace rank)
    (openOnly : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last)) :
    StageExchange trace time ∧ ∀ actor, trace.event (time + 1) ≠ .lifecycle .begin actor := by
  cases exchange with
  | rootPastActivation early root classified =>
    exact ⟨.rootPastActivation early root classified, fun _ impossible => by rw [root] at impossible; cases impossible⟩
  | rootPastChild child root younger older ready =>
    exact ⟨.rootPastChild child root younger older ready, fun _ impossible => by rw [root] at impossible; cases impossible⟩
  | @landingPastActivation firstKind secondKind first second early late order =>
    have different : first ≠ second := fun equal => Nat.lt_irrefl _ (equal ▸ order)
    have notBegin : secondKind ≠ .begin := by
      intro begins
      subst secondKind
      obtain ⟨opens, _, firstBegin⟩ := trace.opening_of_activation openOnly quiet (by omega) early
      exact Nat.lt_asymm order (chronological (by omega : opens < time + 1) bounded firstBegin late)
    exact ⟨.activationPastActivation early late different (fun impossible => False.elim (notBegin impossible)),
      fun _ impossible => notBegin (Event.lifecycle.inj (late.symm.trans impossible)).1⟩
  | landingPastChild child activation classified notBegin ready =>
    exact ⟨.activationPastChild child activation classified ready,
      fun _ impossible => notBegin (Event.lifecycle.inj (activation.symm.trans impossible)).1⟩

def StageOrderNormal (trace : Trace program last) (rank : Name → Nat) : Prop :=
  ∀ time, time + 1 < last → ¬ EarlierStage trace rank time

theorem StageOrderNormal.activation_runs {trace : Trace program last} {rank : Name → Nat}
    (normal : StageOrderNormal trace rank) : OrderedActivationRuns trace rank := by
  intro time firstKind secondKind first second bounded a b
  exact Nat.le_of_not_gt (fun swapped => normal time bounded (.landingPastActivation a b swapped))

theorem roots_at_barriers_of_no_preferred_root {trace : Trace program last}
    (blocked : ∀ cut, cut + 1 < last → eventRoots (trace.state cut) (trace.event cut) = [] →
      eventRoots (trace.state (cut + 1)) (trace.event (cut + 1)) ≠ [] → ¬ StageExchange trace cut) :
    RootsAtBarriers trace := by
  intro time bounded root rootEvent rootClass
  have next : eventRoots (trace.state (time + 1)) (trace.event (time + 1)) ≠ [] :=
    by simpa [rootEvent, eventRoots] using rootClass
  by_cases first : eventRoots (trace.state time) (trace.event time) = []
  · right
    cases childEvent : trace.event time with
    | lifecycle kind actor =>
      exact False.elim (blocked time bounded first next (.rootPastActivation childEvent rootEvent rootClass))
    | command command =>
      have classified : commandRoots (trace.state time) command = [] := by
        simpa [childEvent, eventRoots] using first
      have childStep := (trace.step time (by omega)).1
      have rootStep := (trace.step (time + 1) bounded).1
      rw [childEvent] at childStep
      rw [rootEvent] at rootStep
      refine ⟨command, rfl, classified, (child_root_barrier_iff command root childStep rootStep classified rootClass).mp ?_⟩
      exact fun earlier => blocked time bounded first next (.rootPastChild childEvent rootEvent classified rootClass earlier)
  · exact Or.inl first

theorem StageOrderNormal.roots_at_barriers {trace : Trace program last} {rank : Name → Nat}
    (normal : StageOrderNormal trace rank) : RootsAtBarriers trace := by
  apply roots_at_barriers_of_no_preferred_root
  intro cut bounded first next exchange
  cases exchange with
  | rootPastActivation early late root => exact normal cut bounded (.rootPastActivation early late root)
  | rootPastChild early late child root ready => exact normal cut bounded (.rootPastChild early late child root ready)
  | activationPastActivation _ late _ _ | activationPastChild _ late _ _ =>
    exact next (by simp [late, eventRoots])

def scheduledEvents (trace : Trace program last) : List Ev := (List.range last).map trace.event

private theorem event_layout {trace moved : Trace program last} {point : Nat}
    (labels : ∀ cut, cut < last → moved.event cut =
      if cut = point then trace.event (point + 1) else if cut = point + 1 then trace.event point else trace.event cut) :
    ∀ cut, cut < last → moved.event cut = trace.event (exchangedCut point cut) := by
  intro cut valid
  rw [labels cut valid]
  by_cases first : cut = point <;> by_cases second : cut = point + 1 <;> simp [exchangedCut, first, second]

private theorem event_permutation {trace moved : Trace program last} {point : Nat}
    (bounded : point + 1 < last)
    (layout : ∀ cut, cut < last → moved.event cut = trace.event (exchangedCut point cut)) :
    (scheduledEvents moved).Perm (scheduledEvents trace) := by
  have sameAt (indices : List Nat) (bounds : ∀ cut ∈ indices, cut < last ∧ cut ≠ point ∧ cut ≠ point + 1) :
      indices.map moved.event = indices.map trace.event := by
    apply List.map_congr_left
    intro cut member
    obtain ⟨valid, first, second⟩ := bounds cut member
    simpa [exchangedCut, first, second] using layout cut valid
  have head := sameAt (List.range point) (by
    intro cut member
    have before := List.mem_range.mp member
    omega)
  have tail := sameAt (List.range' (point + 2) (last - (point + 2))) (by
    intro cut member
    obtain ⟨offset, range, placed⟩ := List.mem_range'.mp member
    simp at placed
    omega)
  have earlier := layout point (by omega)
  have later := layout (point + 1) bounded
  simp [exchangedCut] at earlier later
  unfold scheduledEvents
  rw [cut_range_pair bounded, List.map_append, List.map_append, head]
  simp only [List.map_cons, earlier, later, tail]
  exact (List.Perm.swap _ _ _).append_left _

private def stagePriority (trace : Trace program last) (rank : Name → Nat) (cut : Nat) : Nat :=
  match trace.event cut with
  | .lifecycle _ actor => rank actor + 1
  | .command command => if (commandRoots (trace.state cut) command).isEmpty then last + 2 else 0

private def scheduleCost (last : Nat) (priority : Nat → Nat) : Nat :=
  ((List.range last).map fun cut => (last - cut) * priority cut).sum

private theorem EarlierStage.inverted {trace : Trace program last} {rank : Name → Nat} {point : Nat}
    (move : EarlierStage trace rank point) (rankBound : ∀ actor, rank actor ≤ last) :
    stagePriority trace rank (point + 1) < stagePriority trace rank point := by
  cases move with
  | rootPastActivation first second root =>
    simp [stagePriority, first, second, List.isEmpty_iff, root]
  | rootPastChild first second child root _ =>
    simp [stagePriority, first, second, List.isEmpty_iff, child, root]
  | landingPastActivation first second inverted =>
    simpa [stagePriority, first, second] using inverted
  | @landingPastChild _ _ actor first second child _ _ =>
    have ascending : rank actor + 1 < last + 2 := by
      have bound := rankBound actor
      omega
    simpa [stagePriority, first, second, child] using ascending

private theorem scheduleCost_decreases {before after : Nat → Nat} {point : Nat}
    (bounded : point + 1 < last)
    (inverted : before (point + 1) < before point)
    (layout : ∀ cut, cut < last → after cut = before (exchangedCut point cut)) :
    scheduleCost last after < scheduleCost last before := by
  let contribution (priority : Nat → Nat) (cut : Nat) := (last - cut) * priority cut
  have sameAt (indices : List Nat) (bounds : ∀ cut ∈ indices, cut < last ∧ cut ≠ point ∧ cut ≠ point + 1) :
      indices.map (contribution after) = indices.map (contribution before) := by
    apply List.map_congr_left
    intro cut member
    obtain ⟨inside, first, second⟩ := bounds cut member
    simp [contribution, layout cut inside, exchangedCut, first, second]
  have head := sameAt (List.range point) (by
    intro cut member
    have before := List.mem_range.mp member
    omega)
  have tail := sameAt (List.range' (point + 2) (last - (point + 2))) (by
    intro cut member
    obtain ⟨offset, range, placed⟩ := List.mem_range'.mp member
    simp at placed
    omega)
  have earlier := layout point (by omega)
  have later := layout (point + 1) bounded
  simp [exchangedCut] at earlier later
  change ((List.range last).map (contribution after)).sum < ((List.range last).map (contribution before)).sum
  rw [cut_range_pair bounded]
  simp only [List.map_append, List.sum_append_nat, List.map_cons, List.sum_cons, head, tail]
  simp only [contribution, earlier, later, show last - point = (last - (point + 1)) + 1 by omega,
    Nat.add_mul, Nat.one_mul]
  omega

section Typed
variable {V : Key → Type u} {ops : CoeffectOperations V}
variable {typedProgram : Code → TypedRegistry.Instruction Name ops Code}
local notation "A" => Scalar ops
local notation "Source" => Trace (encodeProgram typedProgram) last

theorem StageExchange.perform (trace : Source) {point : Nat}
    (move : StageExchange trace point) (bounded : point + 1 < last)
    (openOnly : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r) :
    letI : Setoid A := TypedCoeffectReplay.setoid observe
    ∃ moved : Source,
      (∀ cut, cut < last → moved.event cut = trace.event (exchangedCut point cut)) ∧
      (∀ cut, cut < last → eventRoots (moved.state cut) (moved.event cut) =
        eventRoots (trace.state (exchangedCut point cut)) (trace.event (exchangedCut point cut))) ∧
      originalRoots moved = originalRoots trace ∧
      StageSimulation.Related Eq (trace.state last) (moved.state last) ∧
      (¬ Nonempty (ClosedEpisode moved)) ∧ Progress.Quiet (moved.state last) ∧
      RetainedEvents trace moved (ExchangeReplay.exchangedIndex point) ∧
      (∀ cut, cut ≤ point → moved.state cut = trace.state cut) := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  have self := trace.self_related last (Nat.le_refl _)
    (TypedRegistry.encoded_program_callbacks ops observe typedProgram recovery commutative)
  have reduceRoot {moved : Source}
      (firstEmpty : eventRoots (trace.state point) (trace.event point) = [])
      (exchange : CommandEarlierExchange trace moved point) :
      (∀ cut, cut < last → moved.event cut = trace.event (exchangedCut point cut)) ∧
      (∀ cut, cut < last → eventRoots (moved.state cut) (moved.event cut) =
        eventRoots (trace.state (exchangedCut point cut)) (trace.event (exchangedCut point cut))) ∧
      originalRoots moved = originalRoots trace ∧
      StageSimulation.Related Eq (trace.state last) (moved.state last) ∧
      (¬ Nonempty (ClosedEpisode moved)) ∧ Progress.Quiet (moved.state last) ∧
      RetainedEvents trace moved (ExchangeReplay.exchangedIndex point) ∧
      (∀ cut, cut ≤ point → moved.state cut = trace.state cut) := by
    refine ⟨event_layout (fun cut _ => congrFun exchange.event cut), ?_,
      exchange.roots, ?_, exchange.openOnly, exchange.quiet, exchange.retained,
      fun cut earlier => exchange.state cut (by omega)⟩
    · intro cut _
      by_cases first : cut = point
      · subst cut; simpa [exchangedCut] using exchange.firstRoot
      by_cases second : cut = point + 1
      · subst cut; simpa [exchangedCut, first, firstEmpty] using exchange.secondRoot
      · simpa [exchangedCut, first, second] using exchange.otherRoots cut first second
    · rw [exchange.state last (by omega)]
      exact self
  cases move with
  | rootPastActivation activation rootEvent root =>
    obtain ⟨moved, exchange⟩ := trace.root_crosses_activation openOnly quiet bounded activation _ rootEvent root
    exact ⟨moved, reduceRoot (by simp [activation, eventRoots]) exchange⟩
  | rootPastChild childEvent rootEvent child root ready =>
    obtain ⟨moved, exchange⟩ := trace.root_crosses_child openOnly quiet bounded childEvent rootEvent child root ready
    exact ⟨moved, reduceRoot (by simpa [childEvent, eventRoots] using child) exchange⟩
  | activationPastActivation firstEvent secondEvent different begins =>
    obtain ⟨moved, initial, labels, rootsAt, suffix, retained, roots, finalOpen, finalQuiet⟩ :=
      trace.swap_activations openOnly quiet bounded firstEvent secondEvent different begins observe recovery commutative respect
    refine ⟨moved, event_layout labels, ?_,
      roots, (suffix last (by omega) (Nat.le_refl _)).1, finalOpen, finalQuiet, retained,
      fun cut earlier => (initial cut earlier).1⟩
    · intro cut valid
      rw [rootsAt cut valid]
      by_cases firstCut : cut = point
      · subst cut; simp [exchangedCut, firstEvent, secondEvent, eventRoots]
      by_cases secondCut : cut = point + 1
      · subst cut; simp [exchangedCut, firstEvent, secondEvent, eventRoots]
      · simp [exchangedCut, firstCut, secondCut]
  | activationPastChild childEvent activation childClass allowed =>
    obtain ⟨moved, labels, states, _, sameChild, roots, finalOpen, finalQuiet, retained⟩ :=
      trace.swap_activation_before_command openOnly quiet bounded childEvent activation allowed
    refine ⟨moved, event_layout (fun cut _ => congrFun labels cut), ?_,
      roots, ?_, finalOpen, finalQuiet, retained, fun cut earlier => states cut (by omega)⟩
    · intro cut _
      by_cases firstCut : cut = point
      · subst cut; simp [labels, exchangedCut, activation, eventRoots]
      by_cases secondCut : cut = point + 1
      · subst cut; simpa [labels, exchangedCut, childEvent, eventRoots] using sameChild
      · simp [labels, exchangedCut, firstCut, secondCut, states cut secondCut]
    · rw [states last (by omega)]
      exact self

/-- Every quiet open history reduces to a stage order with no remaining
preferred legal exchange. This uses the provenance of every command cut
and keeps the entire root command sequence. -/
theorem Trace.order_stages_at_barriers (trace : Source) (rank : Name → Nat)
    (rankBound : ∀ actor, rank actor ≤ last) (chronological : ChronologicalOpenings trace rank)
    (openOnly : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r) :
    letI : Setoid A := TypedCoeffectReplay.setoid observe
    ∃ (moved : Source) (expand : Nat → Nat), StageOrderNormal moved rank ∧ ChronologicalOpenings moved rank ∧
      StableActorAddresses trace moved expand ∧
      (scheduledEvents moved).Perm (scheduledEvents trace) ∧
      originalRoots moved = originalRoots trace ∧ StageSimulation.Related Eq (trace.state last) (moved.state last) ∧
      (¬ Nonempty (ClosedEpisode moved)) ∧ Progress.Quiet (moved.state last) := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  classical
  generalize measured : scheduleCost last (stagePriority trace rank) = size
  induction size using Nat.strongRecOn generalizing trace with
  | ind size ih =>
    by_cases canMove : ∃ point, point + 1 < last ∧ EarlierStage trace rank point
    · obtain ⟨point, bounded, move⟩ := canMove
      obtain ⟨legal, notBegin⟩ := move.admissible bounded chronological openOnly quiet
      obtain ⟨moved, labels, classification, roots, compared, movedOpen, movedQuiet, tracked, _⟩ :=
        legal.perform trace bounded openOnly quiet observe recovery commutative respect
      have sortedOpenings : ChronologicalOpenings moved rank := by
        apply ChronologicalOpenings.swap chronological notBegin
        intro cut valid
        rw [labels cut valid]
        by_cases first : cut = point <;> by_cases second : cut = point + 1 <;> simp [exchangedCut, first, second]
      have layout (cut : Nat) (valid : cut < last) :
          stagePriority moved rank cut = stagePriority trace rank (exchangedCut point cut) := by
        unfold stagePriority
        rw [labels cut valid]
        cases found : trace.event (exchangedCut point cut) with
        | lifecycle => rfl
        | command command =>
          have same := classification cut valid
          rw [labels cut valid, found] at same
          exact congrArg (fun commands => if commands.isEmpty then last + 2 else 0) same
      have smaller := scheduleCost_decreases bounded (move.inverted rankBound) layout
      rw [measured] at smaller
      obtain ⟨result, expand, normal, order, kept, permutation, retained, endpoint, finalOpen, finalQuiet⟩ :=
        ih _ smaller moved sortedOpenings movedOpen movedQuiet rfl
      exact ⟨result, ExchangeReplay.exchangedIndex point ∘ expand, normal, order, (legal.stable_addresses bounded tracked).trans kept,
        permutation.trans (event_permutation bounded labels), retained.trans roots,
        StageSimulation.Related.trans (Q := Eq) (fun a b => a.trans b) compared endpoint, finalOpen, finalQuiet⟩
    · exact ⟨trace, id, fun point bounded move => canMove ⟨point, bounded, move⟩, chronological, .refl trace, List.Perm.refl _, rfl,
        trace.self_related last (Nat.le_refl _)
          (TypedRegistry.encoded_program_callbacks ops observe typedProgram recovery commutative),
        openOnly, quiet⟩

/-- Reduce an open trace using priorities assigned to its original events.
An opening can move earlier when its actual target is available there.
Priorities travel with event stamps, including across reused names. -/
theorem Trace.order_by_event_priority (trace : Source) (priority : Nat → Nat)
    (openOnly : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r) :
    letI : Setoid A := TypedCoeffectReplay.setoid observe
    ∃ (moved : Source) (expand : Nat → Nat),
      (∀ cut, cut + 1 < last → StageExchange moved cut → priority (expand (cut + 1)) ≤ priority (expand (cut + 2))) ∧
      StableActorAddresses trace moved expand ∧
      (∀ cut, cut < last → eventRoots (moved.state cut) (moved.event cut) =
        eventRoots (trace.state (expand (cut + 1) - 1)) (trace.event (expand (cut + 1) - 1))) ∧
      (scheduledEvents moved).Perm (scheduledEvents trace) ∧
      originalRoots moved = originalRoots trace ∧ StageSimulation.Related Eq (trace.state last) (moved.state last) ∧
      (¬ Nonempty (ClosedEpisode moved)) ∧ Progress.Quiet (moved.state last) := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  classical
  generalize measured : scheduleCost last (fun cut => priority (cut + 1)) = size
  induction size using Nat.strongRecOn generalizing trace priority with
  | ind size ih =>
    by_cases canMove : ∃ cut, cut + 1 < last ∧ StageExchange trace cut ∧ priority (cut + 2) < priority (cut + 1)
    · obtain ⟨point, bounded, exchange, inverted⟩ := canMove
      obtain ⟨moved, labels, classification, roots, compared, movedOpen, movedQuiet, tracked, _⟩ :=
        exchange.perform trace bounded openOnly quiet observe recovery commutative respect
      let swapped := ExchangeReplay.exchangedIndex point
      let nextPriority := priority ∘ swapped
      have layout (cut : Nat) (_ : cut < last) : nextPriority (cut + 1) = priority (exchangedCut point cut + 1) :=
        congrArg priority (exchanged_stamp point cut)
      have smaller := scheduleCost_decreases (before := fun cut => priority (cut + 1))
        (after := fun cut => nextPriority (cut + 1)) bounded inverted layout
      rw [measured] at smaller
      obtain ⟨result, embed, normal, retained, classified, permutation, resultRoots, endpoint, finalOpen, finalQuiet⟩ :=
        ih _ smaller moved nextPriority movedOpen movedQuiet rfl
      refine ⟨result, swapped ∘ embed, normal, (exchange.stable_addresses bounded tracked).trans retained, ?_,
        permutation.trans (event_permutation bounded labels), resultRoots.trans roots,
        StageSimulation.Related.trans (Q := Eq) (fun a b => a.trans b) compared endpoint, finalOpen, finalQuiet⟩
      intro cut valid
      have stamp := retained.retained.stamp cut valid
      have source : embed (cut + 1) - 1 < last := by omega
      have old := (classified cut valid).trans (classification _ source)
      have full : embed (cut + 1) - 1 + 1 = embed (cut + 1) := by omega
      have mapped : swapped (embed (cut + 1)) - 1 = exchangedCut point (embed (cut + 1) - 1) := by
        calc
          _ = swapped (embed (cut + 1) - 1 + 1) - 1 := congrArg (fun stamp => swapped stamp - 1) full.symm
          _ = _ := by simp only [swapped, exchanged_stamp, Nat.add_sub_cancel]
      simpa only [Function.comp_apply, mapped] using old
    · refine ⟨trace, id, ?_, .refl trace, fun _ _ => rfl, List.Perm.refl _, rfl,
        trace.self_related last (Nat.le_refl _)
          (TypedRegistry.encoded_program_callbacks ops observe typedProgram recovery commutative), openOnly, quiet⟩
      intro cut bounded exchange
      exact Nat.le_of_not_gt (fun inverse => canMove ⟨cut, bounded, exchange, inverse⟩)

/-- Excise closed episodes and order the surviving events using priorities
of their original stamps. The result carries the same source map through
both transformations. -/
theorem normalize_by_event_priority (trace : Source) (priority : Nat → Nat)
    (quiet : Progress.Quiet (trace.state last))
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r) :
    letI : Setoid A := TypedCoeffectReplay.setoid observe
    ∃ (length : Nat) (result : Trace (encodeProgram typedProgram) length) (expand : Nat → Nat),
      length ≤ last ∧ (¬ Nonempty (ClosedEpisode result)) ∧ Progress.Quiet (result.state length) ∧
      (∀ cut, cut + 1 < length → StageExchange result cut → priority (expand (cut + 1)) ≤ priority (expand (cut + 2))) ∧
      RetainedEvents trace result expand ∧ originalRoots result = originalRoots trace ∧
      (TotalProvision (trace.state last) → TotalProvision (result.state length)) ∧
      ∃ projected, VestigeErasures (trace.state last) projected ∧
        StageSimulation.Related Eq projected (result.state length) := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  obtain ⟨length, reduced, original, bounded, openOnly, excised, roots, _, reducedQuiet, total, projected, erased, alignment⟩ :=
    eliminate_closed_episodes trace quiet observe recovery commutative respect
  obtain ⟨result, moved, ordered, retained, _, _, resultRoots, related, finalOpen, finalQuiet⟩ :=
    reduced.order_by_event_priority (priority ∘ original) openOnly reducedQuiet observe recovery commutative respect
  exact ⟨length, result, original ∘ moved, bounded, finalOpen, finalQuiet, ordered, excised.trans retained.retained,
    resultRoots.trans roots, fun provisions => related_total_provision related (total provisions), projected, erased,
    StageSimulation.Related.trans (Q := Eq) (fun a b => a.trans b) alignment related⟩

/-- Eliminate closed episodes and order the remaining stages across the
command cuts up to the actual causal barriers. The endpoint comparison
allows only the justified vestige erasures and the typed relation. -/
theorem normalize_stages_at_barriers (trace : Source) (quiet : Progress.Quiet (trace.state last))
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r) :
    letI : Setoid A := TypedCoeffectReplay.setoid observe
    ∃ (length : Nat) (openTrace result : Trace (encodeProgram typedProgram) length) (rank : Name → Nat) (expand : Nat → Nat),
      length ≤ last ∧ (¬ Nonempty (ClosedEpisode result)) ∧ StageOrderNormal result rank ∧
      ChronologicalOpenings result rank ∧ (scheduledEvents result).Perm (scheduledEvents openTrace) ∧
      (∃ embed, StableActorAddresses openTrace result embed) ∧
      RetainedEvents trace result expand ∧
      originalRoots result = originalRoots trace ∧ Progress.Quiet (result.state length) ∧
      (TotalProvision (trace.state last) →
        TotalProvision (result.state length) ∧
          ∀ {a b}, SupportUniqueness.ActivePredecessor (result.state length) a b → rank a < rank b) ∧
      ∃ projected, VestigeErasures (trace.state last) projected ∧
        StageSimulation.Related Eq projected (result.state length) := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  obtain ⟨length, reduced, before, bound, openOnly, excised, roots, _, reducedQuiet, total, projected, erased, alignment⟩ :=
    eliminate_closed_episodes trace quiet observe recovery commutative respect
  obtain ⟨result, after, normal, chronological, retained, permutation, resultRoots, related, finalOpen, finalQuiet⟩ :=
    reduced.order_stages_at_barriers (openingRanks reduced length) (openingRanks_bounded reduced length)
      (reduced.chronological_openings openOnly) openOnly reducedQuiet observe recovery commutative respect
  refine ⟨length, reduced, result, openingRanks reduced length, before ∘ after, bound, finalOpen, normal, chronological,
    permutation, ⟨after, retained⟩, excised.trans retained.retained, resultRoots.trans roots, finalQuiet, ?_, projected, erased,
    StageSimulation.Related.trans (Q := Eq) (fun a b => a.trans b) alignment related⟩
  intro provisions
  have preserved := related_total_provision related (total provisions)
  exact ⟨preserved, ChronologicalOpenings.support chronological finalOpen finalQuiet preserved⟩

end Typed
end Cordis.Repairs.GuardedHistory
