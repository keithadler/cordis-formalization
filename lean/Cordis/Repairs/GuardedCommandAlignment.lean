import Cordis.Repairs.GuardedAddressSchedule
import Cordis.Repairs.GuardedReservationOrder
import Cordis.Repairs.GuardedOpenExchange

/-! Synchronizing the next orchestration command in quiet open histories. -/
namespace Cordis.Repairs.GuardedCommandAlignment
open Calculus Stages LegalHistory GuardedHistory GuardedBirthAddresses GuardedAddressSchedule
open GuardedReservationOrder (removal_at_gap)
open GuardedScheduleMatching
open GuardedLandingMatching (ChildContinuations)
open GuardedBirthMatching (recorded_birth born_unique)
open OrchestrationSorting (Command)
open ExchangeReplay (exchangedIndex exchangedCut exchanged_stamp)

universe u v
variable {Name Key Value Code Error : Type u} [DecidableEq Name] [DecidableEq Key]
variable {program : Code → Instruction Name Key Value Code Error} {last : Nat}
local notation "Cmd" => Command Name Key Code

private theorem activation_keeps_presence (trace : Trace program last) {cut : Nat} (bounded : cut < last)
    (activation : ∃ kind name, trace.event cut = .lifecycle kind name) {target : Name}
    (found : trace.state cut target ≠ none) : trace.state (cut + 1) target ≠ none := by
  intro absent
  obtain ⟨kind, name, event⟩ := activation
  have command := removal_at_gap trace bounded found absent
  rw [event] at command
  cases command

private theorem activation_interval_presence (trace : Trace program last) {start span : Nat}
    (bounded : start + span ≤ last)
    (block : ∀ cut, start ≤ cut → cut < start + span → ∃ kind name, trace.event cut = .lifecycle kind name)
    {target : Name} (found : trace.state start target ≠ none) : trace.state (start + span) target ≠ none := by
  induction span with
  | zero => exact found
  | succ span ih =>
    exact activation_keeps_presence trace (cut := start + span) (by omega) (block _ (by omega) (by omega))
      (ih (by omega) (fun cut lower upper => block cut lower (by omega)))

theorem command_exchange_addresses {source moved : Trace program last} {time : Nat}
    (exchange : CommandEarlierExchange source moved time) (bounded : time + 1 < last)
    {kind : Lifecycle} {actor : Name} {command : Cmd}
    (activation : source.event time = .lifecycle kind actor) (external : source.event (time + 1) = .command command) :
    StableActorAddresses source moved (exchangedIndex time) := by
  apply StableActorAddresses.adjacent bounded exchange.retained
  · simp [isRootInsertion, activation]
  · intro _ stage
    cases command <;> simp [Trace.rule, external, eventRule, ExchangeReplay.commandRule, EpisodeSelection.canBirth] at stage

/-- Exchanging an activation with its adjacent event preserves the exact
command word, including relative order and target components. -/
theorem command_input_of_activation_exchange {source moved : Trace program last} {time : Nat}
    (stable : StableActorAddresses source moved (exchangedIndex time)) (bounded : time + 1 < last)
    (activation : (∃ kind actor, source.event time = .lifecycle kind actor) ∨
      (∃ kind actor, source.event (time + 1) = .lifecycle kind actor)) :
    orchestrationInput moved = orchestrationInput source := by
  have earlier (i : Nat) (inside : i < last) : commandAt moved i = commandAt source (exchangedCut time i) := by
    simpa only [exchanged_stamp, Nat.add_sub_cancel] using stable_addressed_command stable inside
  have fixed (cuts : List Nat) (inside : ∀ i ∈ cuts, i < last ∧ i ≠ time ∧ i ≠ time + 1) :
      cuts.filterMap (commandAt moved) = cuts.filterMap (commandAt source) := by
    have labels : cuts.map (commandAt moved) = cuts.map (commandAt source) := by
      apply List.map_congr_left
      intro i member
      obtain ⟨valid, before, after⟩ := inside i member
      simpa [exchangedCut, before, after] using earlier i valid
    simpa only [List.filterMap_map, Function.id_comp] using congrArg (List.filterMap id) labels
  have prefixEq := fixed (List.range time) (by
    intro i member
    have prior := List.mem_range.mp member
    omega)
  have suffixEq := fixed (List.range' (time + 2) (last - (time + 2))) (by
    intro i member
    obtain ⟨offset, boundedOffset, placed⟩ := List.mem_range'.mp member
    simp at placed
    omega)
  have first : commandAt moved time = commandAt source (time + 1) := by
    simpa [exchangedCut] using earlier time (by omega)
  have second : commandAt moved (time + 1) = commandAt source time := by
    simpa [exchangedCut] using earlier (time + 1) bounded
  unfold orchestrationInput
  rw [cut_range_pair bounded, List.filterMap_append, List.filterMap_append, prefixEq]
  rcases activation with before | after
  · have noCommand := (commandAt_none source (by omega : time < last)).mpr before
    simp only [List.filterMap_cons, first, second, noCommand, suffixEq]
  · have noCommand := (commandAt_none source bounded).mpr after
    simp only [List.filterMap_cons, first, second, noCommand, suffixEq]

/-- A command preceded by a lifecycle event waits for that event to
create its actual target. Insertions can cross any preceding activation
in a quiet open history. -/
def CommandsAtBirthBarriers (trace : Trace program last) : Prop :=
  ∀ cut, cut + 1 < last → ∀ kind actor command,
    trace.event cut = .lifecycle kind actor → trace.event (cut + 1) = .command command →
    trace.state cut command.actor = none ∧ trace.state (cut + 1) command.actor ≠ none

private def commandPosition (trace : Trace program last) (cut : Nat) : Nat :=
  match trace.event cut with
  | .command _ => cut
  | .lifecycle .. => 0

private def commandPositionSum (trace : Trace program last) : Nat :=
  ((List.range last).map (commandPosition trace)).sum

private theorem command_position_decreases {source moved : Trace program last} {cut : Nat}
    (exchange : CommandEarlierExchange source moved cut) (bounded : cut + 1 < last)
    {kind : Lifecycle} {actor : Name} {command : Cmd}
    (activation : source.event cut = .lifecycle kind actor) (external : source.event (cut + 1) = .command command) :
    commandPositionSum moved < commandPositionSum source := by
  have outside (cuts : List Nat) (fixed : ∀ i ∈ cuts, i ≠ cut ∧ i ≠ cut + 1) :
      cuts.map (commandPosition moved) = cuts.map (commandPosition source) := by
    apply List.map_congr_left
    intro i member
    obtain ⟨first, second⟩ := fixed i member
    simp [commandPosition, exchange.event, first, second]
  have head := outside (List.range cut) (fun i member => by
    have before := List.mem_range.mp member
    omega)
  have tail := outside (List.range' (cut + 2) (last - (cut + 2))) (fun i member => by
    obtain ⟨offset, _, placed⟩ := List.mem_range'.mp member
    simp at placed
    omega)
  unfold commandPositionSum
  rw [cut_range_pair bounded]
  simp only [List.map_append, List.sum_append_nat, List.map_cons, List.sum_cons, head, tail]
  simp [commandPosition, exchange.event, activation, external]

/-- Record each legal adjacent command exchange and its event-stamp map. -/
inductive CommandExchangePath : Trace program last → Trace program last → (Nat → Nat) → Prop
  | refl (trace : Trace program last) : CommandExchangePath trace trace id
  | step {before middle after : Trace program last} {cut : Nat} {expand : Nat → Nat} :
      cut + 1 < last → CommandEarlierExchange before middle cut →
      (∃ kind actor, before.event cut = .lifecycle kind actor) →
      StableActorAddresses before middle (exchangedIndex cut) →
      CommandExchangePath middle after expand →
      CommandExchangePath before after (exchangedIndex cut ∘ expand)

theorem CommandExchangePath.trans {before middle after : Trace program last} {first second : Nat → Nat}
    (earlierPath : CommandExchangePath before middle first) (laterPath : CommandExchangePath middle after second) :
    CommandExchangePath before after (first ∘ second) := by
  induction earlierPath with
  | refl => exact laterPath
  | step bounded exchange activation addresses _ ih => exact .step bounded exchange activation addresses (ih laterPath)

/-- The path preserves the actual final registry, original root commands,
and recursive birth addresses. -/
theorem CommandExchangePath.preserves {before after : Trace program last} {expand : Nat → Nat}
    (path : CommandExchangePath before after expand) :
    after.state last = before.state last ∧ originalRoots after = originalRoots before ∧
      StableActorAddresses before after expand := by
  induction path with
  | refl trace => exact ⟨rfl, rfl, .refl trace⟩
  | step bounded exchange _ stable _ ih =>
    exact ⟨ih.1.trans (exchange.state last (by omega)), ih.2.1.trans exchange.roots, stable.trans ih.2.2⟩

theorem CommandExchangePath.input_eq {before after : Trace program last} {expand : Nat → Nat}
    (path : CommandExchangePath before after expand) :
    orchestrationInput after = orchestrationInput before := by
  induction path with
  | refl => rfl
  | step bounded _ activation stable _ ih =>
    exact ih.trans (command_input_of_activation_exchange stable bounded (.inl activation))

private theorem command_reflects_new_presence (command : Cmd)
    {before after : Registry Name Key Value Code (Inverse Name Key Value) Error} {name : Name}
    (vacant : command.apply before name = none) (present : command.apply after name ≠ none) :
    before name = none ∧ after name ≠ none := by
  cases command with
  | insert target component =>
    by_cases same : name = target
    · simp [Command.apply, put, same] at vacant
    · exact ⟨by simpa [Command.apply, put, same] using vacant,
        by simpa [Command.apply, put, same] using present⟩
  | retire target =>
    exact ⟨(Transposition.retire_presence _ _ _).mp vacant,
      fun absent => present ((Transposition.retire_presence _ _ _).mpr absent)⟩
  | remove target =>
    by_cases same : name = target
    · simp [Command.apply, erase, same] at present
    · exact ⟨by simpa [Command.apply, erase, same] using vacant,
        by simpa [Command.apply, erase, same] using present⟩

/-- Move a lifecycle event after a consecutive block of commands. Each
command must avoid targeting a name made present by that lifecycle event.
The same command applied on either side cannot create a new difference
in presence, so the original check suffices for every exchange. -/
theorem push_activation_through_command_block (trace : Trace program last)
    (opened : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    {pivot span : Nat} (bounded : pivot + span < last) {kind : Lifecycle} {actor : Name}
    (activation : trace.event pivot = .lifecycle kind actor)
    (block : ∀ cut, pivot < cut → cut ≤ pivot + span → ∃ command, trace.event cut = .command command)
    (ready : ∀ cut, pivot < cut → cut ≤ pivot + span → ∀ command,
      trace.event cut = .command command → trace.state pivot command.actor = none →
      trace.state (pivot + 1) command.actor = none) :
    ∃ (moved : Trace program last) (expand : Nat → Nat),
      CommandExchangePath trace moved expand ∧
      moved.event (pivot + span) = .lifecycle kind actor ∧
      expand (pivot + span + 1) = pivot + 1 ∧
      (∀ cut, cut < pivot → addressedEventAt moved cut = addressedEventAt trace cut) ∧
      (∀ cut, pivot + span < cut → cut < last → moved.event cut = trace.event cut) ∧
      (∀ stamp, stamp ≤ pivot ∨ pivot + span + 1 < stamp → expand stamp = stamp) ∧
      (¬ Nonempty (ClosedEpisode moved)) ∧ Progress.Quiet (moved.state last) ∧
      (∀ cut, cut ≤ pivot → moved.state cut = trace.state cut) ∧
      (∀ cut, cut < pivot → moved.event cut = trace.event cut) ∧
      (∀ cut, pivot ≤ cut → cut < pivot + span → moved.event cut = trace.event (cut + 1)) := by
  induction span generalizing pivot trace with
  | zero =>
    exact ⟨trace, id, .refl _, activation, rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl, opened, quiet,
      fun _ _ => rfl, fun _ _ => rfl, fun _ _ impossible => (by omega : False).elim⟩
  | succ span ih =>
    obtain ⟨command, external⟩ := block (pivot + 1) (by omega) (by omega)
    have finite : pivot + 1 < last := by omega
    obtain ⟨mid, exchange⟩ := (trace.command_crosses_activation_iff opened quiet finite activation external).mpr
      (ready (pivot + 1) (by omega) (by omega) command external)
    have addresses := command_exchange_addresses exchange finite activation external
    have middleActivation : mid.event (pivot + 1) = .lifecycle kind actor := by
      simpa [exchange.event] using activation
    have same (cut : Nat) (after : pivot + 1 < cut) : mid.event cut = trace.event cut := by
      simp [exchange.event, show cut ≠ pivot by omega, show cut ≠ pivot + 1 by omega]
    have priorState : mid.state (pivot + 1) = command.apply (trace.state pivot) := by
      have earlier : mid.event pivot = .command command := by simpa [exchange.event] using external
      have step := (mid.step pivot (by omega)).1
      rw [earlier] at step
      rw [step.2, exchange.state pivot (by omega)]
    have nextState : mid.state (pivot + 2) = command.apply (trace.state (pivot + 1)) := by
      have step := (trace.step (pivot + 1) finite).1
      rw [external] at step
      exact (exchange.state (pivot + 2) (by omega)).trans step.2
    have middleReady (cut : Nat) (after : pivot + 1 < cut) (inside : cut ≤ pivot + 1 + span)
        (next : Cmd) (event : mid.event cut = .command next) (vacant : mid.state (pivot + 1) next.actor = none) :
        mid.state (pivot + 1 + 1) next.actor = none := by
      apply Classical.byContradiction
      intro present
      have origin := command_reflects_new_presence command
        (by simpa only [priorState] using vacant)
        (by simpa only [nextState] using present)
      exact origin.2 (ready cut (by omega) (by omega) next ((same cut after).symm.trans event) origin.1)
    obtain ⟨moved, expand, path, movedActivation, activationStamp, earlierEvents, suffix, fixed, openMoved, quietMoved, cuts, labels, shifted⟩ :=
      ih mid exchange.openOnly exchange.quiet (pivot := pivot + 1) (by omega) middleActivation
        (fun cut lower upper => by rw [same cut lower]; exact block cut (by omega) (by omega)) middleReady
    refine ⟨moved, exchangedIndex pivot ∘ expand,
      .step finite exchange ⟨kind, actor, activation⟩ addresses path, ?_, ?_, ?_, ?_, ?_, openMoved, quietMoved, ?_, ?_, ?_⟩
    · rw [show pivot + (span + 1) = pivot + 1 + span by omega]
      exact movedActivation
    · rw [Function.comp_apply, show pivot + (span + 1) + 1 = pivot + 1 + span + 1 by omega,
        activationStamp, ExchangeReplay.exchangedIndex_second]
    · intro cut prior
      have matchCut := stable_addressed_event addresses (cut := cut) (by omega)
      rw [ExchangeReplay.exchangedIndex_other (by omega) (by omega), Nat.add_sub_cancel] at matchCut
      exact (earlierEvents cut (by omega)).trans matchCut
    · intro cut after inside
      exact (suffix cut (by omega) inside).trans (same cut (by omega))
    · intro stamp outside
      rw [Function.comp_apply, fixed stamp (by omega)]
      exact ExchangeReplay.exchangedIndex_other (by omega) (by omega)

    · intro cut early
      exact (cuts cut (by omega)).trans (exchange.state cut (by omega))
    · intro cut early
      rw [labels cut (by omega)]
      simp [exchange.event, show cut ≠ pivot by omega, show cut ≠ pivot + 1 by omega]
    · intro cut lower upper
      by_cases first : cut = pivot
      · subst cut
        rw [labels pivot (by omega)]
        simp [exchange.event]
      · exact (shifted cut (by omega) (by omega)).trans (same (cut + 1) (by omega))

/-- If the block fails the exchange test, its first failing command is
a retirement or removal of the actual child created at the activation.
All earlier commands in the block satisfy the test. -/
theorem first_command_block_birth_barrier (trace : Trace program last)
    {pivot span : Nat} (bounded : pivot + span < last)
    (block : ∀ cut, pivot < cut → cut ≤ pivot + span → ∃ command, trace.event cut = .command command)
    (blocked : ¬ ∀ cut, pivot < cut → cut ≤ pivot + span → ∀ command,
      trace.event cut = .command command → trace.state pivot command.actor = none →
      trace.state (pivot + 1) command.actor = none) :
    ∃ cut name address component, pivot < cut ∧ cut ≤ pivot + span ∧
      (trace.event cut = .command (.retire name) ∨ trace.event cut = .command (.remove name)) ∧
      GuardedBirthMatching.BornAt trace name (pivot + 1) ∧
      (trace.notes cut).1 name = some (pivot + 1) ∧
      targetAt trace cut name = some (address, component) ∧ Addressed trace (pivot + 1) address ∧
      (∀ i, pivot < i → i < cut → ∀ command, trace.event i = .command command →
        trace.state pivot command.actor = none → trace.state (pivot + 1) command.actor = none) ∧
      ∀ moved : Trace program last, moved.state pivot name = none →
        (∀ i, pivot ≤ i → i < cut → moved.event i = trace.event (i + 1)) → False := by
  classical
  let fails (cut : Nat) :=
    pivot < cut ∧ cut ≤ pivot + span ∧ ∃ command, trace.event cut = .command command ∧
      trace.state pivot command.actor = none ∧ trace.state (pivot + 1) command.actor ≠ none
  have witness : ∃ cut, fails cut := by
    apply Classical.byContradiction
    intro none
    apply blocked
    intro cut lower upper command event vacant
    exact Classical.byContradiction fun present => none ⟨cut, lower, upper, command, event, vacant, present⟩
  have minimal (bound : Nat) (bad : fails bound) :
      ∃ cut, fails cut ∧ ∀ i, i < cut → ¬ fails i := by
    induction bound using Nat.strongRecOn with
    | ind bound ih =>
      by_cases low : ∃ i, i < bound ∧ fails i
      · obtain ⟨i, earlier, bad⟩ := low
        exact ih i earlier bad
      · exact ⟨bound, bad, fun i earlier bad => low ⟨i, earlier, bad⟩⟩
  obtain ⟨bound, bad⟩ := witness
  obtain ⟨cut, ⟨lower, upper, command, event, vacant, present⟩, earliest⟩ := minimal bound bad
  have prior (i : Nat) (after : pivot < i) (before : i < cut) (cmd : Cmd)
      (label : trace.event i = .command cmd) (empty : trace.state pivot cmd.actor = none) :
      trace.state (pivot + 1) cmd.actor = none :=
    Classical.byContradiction fun existsRow =>
      earliest i before ⟨after, by omega, cmd, label, empty, existsRow⟩
  have holds (offset : Nat) (inside : pivot + 1 + offset ≤ cut) :
      trace.state (pivot + 1 + offset) command.actor ≠ none ∧
        (trace.notes (pivot + 1 + offset)).1 command.actor = some (pivot + 1) := by
    induction offset with
    | zero =>
      refine ⟨present, ?_⟩
      rw [trace.notes_eq _ (by omega)]
      exact Incarnation.birthAt_of_created vacant present
    | succ offset ih =>
      obtain ⟨oldPresent, oldTag⟩ := ih (by omega)
      have newPresent : trace.state (pivot + 1 + offset + 1) command.actor ≠ none := by
        intro absent
        have remove := removal_at_gap trace (by omega) oldPresent absent
        exact present (prior (pivot + 1 + offset) (by omega) (by omega) (.remove command.actor) remove vacant)
      have beforeTag := trace.notes_eq (pivot + 1 + offset) (by omega)
      have afterTag := trace.notes_eq (pivot + 1 + offset + 1) (by omega)
      refine ⟨newPresent, ?_⟩
      change (trace.notes (pivot + 1 + offset + 1)).1 command.actor = some (pivot + 1)
      rw [afterTag]
      change Incarnation.birthAt trace.state command.actor (pivot + 1 + offset + 1) = some (pivot + 1)
      rw [Incarnation.birth_stays _ _ _ oldPresent newPresent]
      simpa only [beforeTag] using oldTag
  have atCut := holds (cut - (pivot + 1)) (by omega)
  rw [show pivot + 1 + (cut - (pivot + 1)) = cut by omega] at atCut
  have born : GuardedBirthMatching.BornAt trace command.actor (pivot + 1) :=
    ⟨by omega, by omega, by simpa only [Nat.add_sub_cancel] using vacant, present⟩
  have removalOrRetirement : trace.event cut = .command (.retire command.actor) ∨
      trace.event cut = .command (.remove command.actor) := by
    cases command with
    | insert name component =>
      have step := (trace.step cut (by omega)).1
      rw [event] at step
      exact False.elim (atCut.1 step.1.1)
    | retire => exact .inl event
    | remove => exact .inr event
  obtain ⟨address, component, target⟩ := targetAt_command trace (by omega) removalOrRetirement
  obtain ⟨birth, _, stamp, addressed, _, _⟩ := (targetAt_eq_some trace).mp target
  have equal := Option.some.inj (stamp.symm.trans atCut.2)
  refine ⟨cut, command.actor, address, component, lower, upper, removalOrRetirement, born, atCut.2,
    target, equal ▸ addressed, prior, ?_⟩
  intro moved missing labels
  have absent (offset : Nat) (inside : pivot + offset < cut) :
      moved.state (pivot + offset) command.actor = none := by
    induction offset with
    | zero => exact missing
    | succ offset ih =>
      have old := ih (by omega)
      obtain ⟨previous, label⟩ := block (pivot + offset + 1) (by omega) (by omega)
      have different : command.actor ≠ previous.actor := by
        intro same
        have ready := prior (pivot + offset + 1) (by omega) (by omega) previous label
        rw [← same] at ready
        exact present (ready vacant)
      have step := (moved.step (pivot + offset) (by omega)).1
      rw [(labels (pivot + offset) (by omega) (by omega)).trans label] at step
      change moved.state (pivot + offset + 1) command.actor = none
      rw [step.2]
      cases previous with
      | insert name component =>
        have neq : command.actor ≠ name := different
        simpa [Command.apply, put, neq] using old
      | remove name =>
        have neq : command.actor ≠ name := different
        simpa [Command.apply, erase, neq] using old
      | retire => exact (Transposition.retire_presence _ _ _).mpr old
  let atCut := cut - 1
  have sameCut : pivot + (atCut - pivot) = atCut := by dsimp [atCut]; omega
  have atBarrier := absent (atCut - pivot) (by rw [sameCut]; dsimp [atCut]; omega)
  rw [sameCut] at atBarrier
  have copied := labels atCut (by dsimp [atCut]; omega) (by dsimp [atCut]; omega)
  rw [show atCut + 1 = cut by dsimp [atCut]; omega] at copied
  have step := (moved.step atCut (by dsimp [atCut]; omega)).1
  rcases removalOrRetirement with retirement | removal
  · rw [copied.trans retirement] at step
    exact step.1 atBarrier
  · rw [copied.trans removal] at step
    exact Transposition.removable_present _ _ step.1 atBarrier

/-- The readiness check exactly characterizes whether the literal
command block can execute one cut earlier from the same registry. -/
theorem command_block_can_advance_iff (trace : Trace program last)
    (opened : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    {pivot span : Nat} (bounded : pivot + span < last) {kind : Lifecycle} {actor : Name}
    (activation : trace.event pivot = .lifecycle kind actor)
    (block : ∀ cut, pivot < cut → cut ≤ pivot + span → ∃ command, trace.event cut = .command command) :
    (∀ cut, pivot < cut → cut ≤ pivot + span → ∀ command,
      trace.event cut = .command command → trace.state pivot command.actor = none →
      trace.state (pivot + 1) command.actor = none) ↔
    ∃ moved : Trace program last, moved.state pivot = trace.state pivot ∧
      ∀ cut, pivot ≤ cut → cut < pivot + span → moved.event cut = trace.event (cut + 1) := by
  constructor
  · intro ready
    obtain ⟨moved, _, _, _, _, _, _, _, _, _, cuts, _, shifted⟩ :=
      push_activation_through_command_block trace opened quiet bounded activation block ready
    exact ⟨moved, cuts pivot (Nat.le_refl _), shifted⟩
  · rintro ⟨moved, same, events⟩
    apply Classical.byContradiction
    intro blocked
    obtain ⟨cut, name, _, _, _, upper, _, born, _, _, _, _, impossible⟩ :=
      first_command_block_birth_barrier trace bounded block blocked
    have vacant : trace.state pivot name = none := by
      simpa only [Nat.add_sub_cancel] using born.2.2.1
    exact impossible moved (by rw [same]; exact vacant) (fun i lower before => events i lower (by omega))

/-- Advance the maximal initial part of a blocked command block.
The delayed activation ends immediately before the first blocked
command and still creates that command's addressed target. -/
theorem advance_commands_to_first_birth_barrier (trace : Trace program last)
    (opened : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    {pivot span : Nat} (bounded : pivot + span < last) {kind : Lifecycle} {actor : Name}
    (activation : trace.event pivot = .lifecycle kind actor)
    (block : ∀ cut, pivot < cut → cut ≤ pivot + span → ∃ command, trace.event cut = .command command)
    (blocked : ¬ ∀ cut, pivot < cut → cut ≤ pivot + span → ∀ command,
      trace.event cut = .command command → trace.state pivot command.actor = none →
      trace.state (pivot + 1) command.actor = none) :
    ∃ (moved : Trace program last) (expand : Nat → Nat) (cut : Nat) (name : Name) (address : Address),
      pivot < cut ∧ cut ≤ pivot + span ∧ CommandExchangePath trace moved expand ∧
      moved.event (cut - 1) = .lifecycle kind actor ∧
      moved.event cut = trace.event cut ∧ commandAt moved cut = commandAt trace cut ∧
      GuardedBirthMatching.BornAt moved name cut ∧ Addressed moved cut address ∧
      Addressed trace (pivot + 1) address ∧
      (∀ i, pivot ≤ i → i + 1 < cut → moved.event i = trace.event (i + 1)) ∧
      (∀ i, i < pivot → addressedEventAt moved i = addressedEventAt trace i) ∧
      (¬ Nonempty (ClosedEpisode moved)) ∧ Progress.Quiet (moved.state last) := by
  obtain ⟨cut, name, address, _, lower, upper, external, _, sourceTag, _, sourceAddress, prior, _⟩ :=
    first_command_block_birth_barrier trace bounded block blocked
  let movedSpan := cut - 1 - pivot
  have placement : pivot + movedSpan = cut - 1 := by dsimp [movedSpan]; omega
  obtain ⟨moved, expand, path, movedActivation, stamp, earlierEvents, suffix, fixed, movedOpen, movedQuiet,
      _, _, shifted⟩ :=
    push_activation_through_command_block trace opened quiet (pivot := pivot) (span := movedSpan)
      (by omega) activation (fun i lower upper => block i lower (by omega))
      (fun i after before command event empty => prior i after (by omega) command event empty)
  have cutBound : cut < last := by omega
  have nextStamp : expand (cut + 1) = cut + 1 := fixed _ (.inr (by omega))
  have exchangeStamp : expand cut = pivot + 1 := by
    rw [placement, Nat.sub_add_cancel (by omega)] at stamp
    exact stamp
  have event := suffix cut (by omega) cutBound
  have addresses := path.preserves.2.2
  have movedActor : moved.actor cut = name := by
    rcases external with retirement | removal
    · simp [Trace.actor, Vestigial.eventActor, OrchestrationSorting.Command.actor, event, retirement]
    · simp [Trace.actor, Vestigial.eventActor, OrchestrationSorting.Command.actor, event, removal]
  have traceActor : trace.actor cut = name := by
    rcases external with retirement | removal
    · simp [Trace.actor, Vestigial.eventActor, OrchestrationSorting.Command.actor, retirement]
    · simp [Trace.actor, Vestigial.eventActor, OrchestrationSorting.Command.actor, removal]
  have maps := addresses.retained.actor_birth cutBound
  rw [nextStamp, Nat.add_sub_cancel, movedActor, traceActor, sourceTag] at maps
  obtain ⟨birth, tag, mapped⟩ := Option.map_eq_some_iff.mp maps
  have sameBirth := addresses.retained.injective (mapped.trans exchangeStamp.symm)
  subst birth
  have born := (recorded_birth moved (Nat.le_of_lt cutBound) tag).1
  obtain ⟨newAddress, movedAddress⟩ := exists_address moved born
  have transported := addresses.address cutBound (movedActor.symm ▸ tag) movedAddress
  rw [exchangeStamp] at transported
  have sameAddress := transported.unique sourceAddress
  subst newAddress
  have command := stable_addressed_command addresses cutBound
  rw [nextStamp, Nat.add_sub_cancel] at command
  exact ⟨moved, expand, cut, name, address, lower, upper, path, placement ▸ movedActivation, event,
    command, born, movedAddress, sourceAddress, fun i low high => shifted i low (by omega),
    earlierEvents, movedOpen, movedQuiet⟩

/-- In the suffix, a command immediately following an activation
waits for a row that the activation creates. -/
def CommandsAtBirthBarriersFrom (trace : Trace program last) (start : Nat) : Prop :=
  ∀ cut, start ≤ cut → cut + 1 < last → ∀ kind actor command,
    trace.event cut = .lifecycle kind actor → trace.event (cut + 1) = .command command →
    trace.state cut command.actor = none ∧ trace.state (cut + 1) command.actor ≠ none

/-- Normalize commands in the unmatched suffix and preserve every
earlier event and the registry and notes at the boundary. -/
theorem push_commands_to_birth_barriers_from (trace : Trace program last) (start : Nat)
    (openOnly : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last)) :
    ∃ (moved : Trace program last) (expand : Nat → Nat),
      CommandsAtBirthBarriersFrom moved start ∧ StableActorAddresses trace moved expand ∧
      orchestrationInput moved = orchestrationInput trace ∧ originalRoots moved = originalRoots trace ∧
      moved.state last = trace.state last ∧ (¬ Nonempty (ClosedEpisode moved)) ∧ Progress.Quiet (moved.state last) ∧
      CommandExchangePath trace moved expand ∧
      (∀ cut, cut ≤ start → cut ≤ last →
        moved.state cut = trace.state cut ∧ moved.notes cut = trace.notes cut) ∧
      (∀ cut, cut < start → moved.event cut = trace.event cut) ∧
      (∀ cut, cut < start → cut < last → addressedEventAt moved cut = addressedEventAt trace cut) := by
  classical
  generalize measure : commandPositionSum trace = cost
  induction cost using Nat.strongRecOn generalizing trace with
  | ind cost ih =>
    by_cases available : ∃ cut, start ≤ cut ∧ cut + 1 < last ∧ ∃ kind actor command,
        trace.event cut = .lifecycle kind actor ∧ trace.event (cut + 1) = .command command ∧
        (trace.state cut command.actor = none → trace.state (cut + 1) command.actor = none)
    · obtain ⟨cut, lower, bounded, kind, actor, command, activation, external, allowed⟩ := available
      obtain ⟨earlier, exchange⟩ := (trace.command_crosses_activation_iff openOnly quiet bounded activation external).mpr allowed
      have smaller := command_position_decreases exchange bounded activation external
      rw [measure] at smaller
      have stable := command_exchange_addresses exchange bounded activation external
      obtain ⟨moved, expand, barriers, retained, commands, roots, endpoint, finalOpen, finalQuiet, path, cuts, events, addresses⟩ :=
        ih _ smaller earlier exchange.openOnly exchange.quiet rfl
      refine ⟨moved, exchangedIndex cut ∘ expand, barriers, stable.trans retained,
        commands.trans (command_input_of_activation_exchange stable bounded (.inl ⟨kind, actor, activation⟩)),
        roots.trans exchange.roots, endpoint.trans (exchange.state last (by omega)), finalOpen, finalQuiet,
        .step bounded exchange ⟨kind, actor, activation⟩ stable path, ?_, ?_, ?_⟩
      · intro i earlier inside
        have same := cuts i earlier inside
        have old := exchange.prefix_eq (by omega) (by omega : i ≤ cut)
        exact ⟨same.1.trans old.1, same.2.trans old.2⟩
      · intro i earlier
        rw [events i earlier]
        simp [exchange.event, show i ≠ cut by omega, show i ≠ cut + 1 by omega]
      · intro i earlier inside
        have same := stable_addressed_event stable (cut := i) inside
        rw [ExchangeReplay.exchangedIndex_other (by omega) (by omega), Nat.add_sub_cancel] at same
        exact (addresses i earlier inside).trans same
    · refine ⟨trace, id, ?_, .refl trace, rfl, rfl, rfl, openOnly, quiet, .refl trace, fun _ _ _ => ⟨rfl, rfl⟩, fun _ _ => rfl, fun _ _ _ => rfl⟩
      intro cut lower bounded kind actor command activation external
      have blocked : ¬ (trace.state cut command.actor = none → trace.state (cut + 1) command.actor = none) :=
        fun allowed => available ⟨cut, lower, bounded, kind, actor, command, activation, external, allowed⟩
      exact ⟨Classical.byContradiction (fun vacant => blocked (fun absent => False.elim (vacant absent))),
        fun absent => blocked (fun _ => absent)⟩

/-- Move every command as early as its actual birth constraints allow. -/
theorem push_commands_to_birth_barriers_with_path (trace : Trace program last)
    (openOnly : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last)) :
    ∃ (moved : Trace program last) (expand : Nat → Nat),
      CommandsAtBirthBarriers moved ∧ StableActorAddresses trace moved expand ∧
      orchestrationInput moved = orchestrationInput trace ∧ originalRoots moved = originalRoots trace ∧
      moved.state last = trace.state last ∧ (¬ Nonempty (ClosedEpisode moved)) ∧ Progress.Quiet (moved.state last) ∧
      CommandExchangePath trace moved expand := by
  obtain ⟨moved, expand, barriers, retained, input, roots, endpoint, opened, settled, path, _, _, _⟩ :=
    push_commands_to_birth_barriers_from trace 0 openOnly quiet
  exact ⟨moved, expand, fun cut => barriers cut (Nat.zero_le _), retained, input, roots, endpoint, opened, settled, path⟩

theorem push_commands_to_birth_barriers (trace : Trace program last)
    (openOnly : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last)) :
    ∃ (moved : Trace program last) (expand : Nat → Nat),
      CommandsAtBirthBarriers moved ∧ StableActorAddresses trace moved expand ∧
      orchestrationInput moved = orchestrationInput trace ∧ originalRoots moved = originalRoots trace ∧
      moved.state last = trace.state last ∧ (¬ Nonempty (ClosedEpisode moved)) ∧ Progress.Quiet (moved.state last) := by
  obtain ⟨moved, expand, barriers, retained, input, roots, endpoint, opened, settled, _⟩ :=
    push_commands_to_birth_barriers_with_path trace openOnly quiet
  exact ⟨moved, expand, barriers, retained, input, roots, endpoint, opened, settled⟩

/-- On a command-free segment of a normalized history, any delayed
command acts on the newly born row at the very end of that segment. -/
theorem CommandsAtBirthBarriersFrom.target_absent {trace : Trace program last}
    {boundary start span : Nat} (normal : CommandsAtBirthBarriersFrom trace boundary)
    (fromBoundary : boundary ≤ start) (positive : 0 < span)
    (bounded : start + span < last) {command : Cmd} (external : trace.event (start + span) = .command command)
    (block : ∀ cut, start ≤ cut → cut < start + span → ∃ kind actor, trace.event cut = .lifecycle kind actor) :
    (∀ cut, start ≤ cut → cut < start + span → trace.state cut command.actor = none) ∧
      trace.state (start + span) command.actor ≠ none := by
  let previous := start + span - 1
  have after : previous + 1 = start + span := by dsimp [previous]; omega
  obtain ⟨kind, actor, stage⟩ := block previous (by omega) (by omega)
  have barrier := normal previous (by omega) (by omega) kind actor command stage (after.symm ▸ external)
  refine ⟨?_, after ▸ barrier.2⟩
  intro cut lower earlier
  apply Classical.byContradiction
  intro present
  have through := activation_interval_presence trace (start := cut) (span := previous - cut) (by omega)
    (fun i first last => block i (by omega) (by omega)) present
  rw [show cut + (previous - cut) = previous by omega] at through
  exact through barrier.1

theorem CommandsAtBirthBarriers.target_absent {trace : Trace program last}
    (normal : CommandsAtBirthBarriers trace) {start span : Nat} (positive : 0 < span)
    (bounded : start + span < last) {command : Cmd} (external : trace.event (start + span) = .command command)
    (block : ∀ cut, start ≤ cut → cut < start + span → ∃ kind actor, trace.event cut = .lifecycle kind actor) :
    (∀ cut, start ≤ cut → cut < start + span → trace.state cut command.actor = none) ∧
      trace.state (start + span) command.actor ≠ none :=
  CommandsAtBirthBarriersFrom.target_absent (boundary := 0)
    (fun cut _ => normal cut) (Nat.zero_le _) positive bounded external block

/-- Move the first subsequent command to an earlier cut across only
lifecycle events. The command is either an insertion or targets a row
already present at that cut. The complete ordered command input is kept. -/
theorem pull_command_through_activations_with_path (trace : Trace program last)
    (openOnly : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    {start span : Nat} (bounded : start + span < last) {command : Cmd}
    (external : trace.event (start + span) = .command command)
    (block : ∀ cut, start ≤ cut → cut < start + span → ∃ kind name, trace.event cut = .lifecycle kind name)
    (ready : trace.state start command.actor = none → trace.state (start + span) command.actor = none) :
    ∃ (moved : Trace program last) (expand : Nat → Nat),
      StableActorAddresses trace moved expand ∧
      (∀ stamp, stamp ≤ start → expand stamp = stamp) ∧
      (∀ cut, cut ≤ start → moved.state cut = trace.state cut ∧ moved.notes cut = trace.notes cut) ∧
      (∀ cut, cut < start → moved.event cut = trace.event cut) ∧
      moved.event start = .command command ∧ commandAt moved start = commandAt trace (start + span) ∧
      orchestrationInput moved = orchestrationInput trace ∧ moved.state last = trace.state last ∧
      (¬ Nonempty (ClosedEpisode moved)) ∧ Progress.Quiet (moved.state last) ∧ CommandExchangePath trace moved expand := by
  induction span generalizing trace with
  | zero => exact ⟨trace, id, .refl trace, fun _ _ => rfl, fun _ _ => ⟨rfl, rfl⟩, fun _ _ => rfl,
      external, rfl, rfl, rfl, openOnly, quiet, .refl trace⟩
  | succ span ih =>
    let time := start + span
    have finite : time + 1 < last := bounded
    obtain ⟨kind, name, activation⟩ := block time (by omega) (by omega)
    have notCreated (vacant : trace.state time command.actor = none) : trace.state (time + 1) command.actor = none := by
      by_cases absent : trace.state start command.actor = none
      · exact ready absent
      · exact False.elim (activation_interval_presence trace (start := start) (span := span) (by omega)
          (fun cut lower upper => block cut lower (by omega)) absent vacant)
    obtain ⟨mid, exchange⟩ := (trace.command_crosses_activation_iff openOnly quiet finite activation external).mpr notCreated
    have stable := command_exchange_addresses exchange finite activation external
    have sameLabel (cut : Nat) (earlier : cut < time) : mid.event cut = trace.event cut := by
      simp [exchange.event, show cut ≠ time by omega, show cut ≠ time + 1 by omega]
    have sameBlock (cut : Nat) (first : start ≤ cut) (inside : cut < start + span) :
        ∃ k n, mid.event cut = .lifecycle k n := by
      rw [sameLabel cut inside]
      exact block cut first (by omega)
    have now : mid.event time = .command command := by simpa only [exchange.event, if_pos rfl] using external
    have nextReady (absent : mid.state start command.actor = none) : mid.state time command.actor = none := by
      rw [exchange.state start (by omega)] at absent
      rw [exchange.state time (by omega)]
      apply Classical.byContradiction
      intro present
      exact activation_keeps_presence trace (by omega) ⟨kind, name, activation⟩ present (ready absent)
    obtain ⟨moved, expand, retained, fixedStamps, fixed, prefixLabels, movedCommand, movedAt, input, endpoint, finalOpen, finalQuiet, path⟩ :=
      ih mid exchange.openOnly exchange.quiet (by omega) now sameBlock nextReady
    refine ⟨moved, exchangedIndex time ∘ expand, stable.trans retained, ?_, ?_, ?_, movedCommand, ?_,
      input.trans (command_input_of_activation_exchange stable finite (.inl ⟨kind, name, activation⟩)),
      endpoint.trans (exchange.state last (by omega)),
      finalOpen, finalQuiet, .step finite exchange ⟨kind, name, activation⟩ stable path⟩
    · intro stamp early
      rw [Function.comp_apply, fixedStamps stamp early]
      exact ExchangeReplay.exchangedIndex_other (by omega) (by omega)
    · intro cut earlier
      have first := fixed cut earlier
      have second := exchange.prefix_eq (by omega : time ≤ last) (by omega : cut ≤ time)
      exact ⟨first.1.trans second.1, first.2.trans second.2⟩
    · intro cut earlier
      exact (prefixLabels cut earlier).trans (sameLabel cut (by omega))
    · exact movedAt.trans (by simpa only [ExchangeReplay.exchangedIndex_first, Nat.add_sub_cancel] using
        stable_addressed_command stable (cut := time) (by omega : time < last))

theorem pull_command_through_activations (trace : Trace program last)
    (openOnly : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    {start span : Nat} (bounded : start + span < last) {command : Cmd}
    (external : trace.event (start + span) = .command command)
    (block : ∀ cut, start ≤ cut → cut < start + span → ∃ kind name, trace.event cut = .lifecycle kind name)
    (ready : trace.state start command.actor = none → trace.state (start + span) command.actor = none) :
    ∃ (moved : Trace program last) (expand : Nat → Nat),
      StableActorAddresses trace moved expand ∧
      (∀ stamp, stamp ≤ start → expand stamp = stamp) ∧
      (∀ cut, cut ≤ start → moved.state cut = trace.state cut ∧ moved.notes cut = trace.notes cut) ∧
      (∀ cut, cut < start → moved.event cut = trace.event cut) ∧
      moved.event start = .command command ∧ commandAt moved start = commandAt trace (start + span) ∧
      orchestrationInput moved = orchestrationInput trace ∧ moved.state last = trace.state last ∧
      (¬ Nonempty (ClosedEpisode moved)) ∧ Progress.Quiet (moved.state last) := by
  obtain ⟨moved, expand, addresses, stamps, cuts, events, selected, commandAt, input, endpoint, opened, settled, _⟩ :=
    pull_command_through_activations_with_path trace openOnly quiet bounded external block ready
  exact ⟨moved, expand, addresses, stamps, cuts, events, selected, commandAt, input, endpoint, opened, settled⟩

/-- The next removal can create a vacancy at the beginning of an
activation block exactly when its target is already present there.
The exchange keeps the matched prefix and the addressed command input. -/
theorem pull_removal_through_activations_iff (trace : Trace program last)
    (openOnly : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    {start span : Nat} (bounded : start + span < last) {name : Name}
    (removal : trace.event (start + span) = .command (.remove name))
    (block : ∀ cut, start ≤ cut → cut < start + span → ∃ kind actor, trace.event cut = .lifecycle kind actor) :
    trace.state start name ≠ none ↔
      ∃ (moved : Trace program last) (expand : Nat → Nat),
        CommandExchangePath trace moved expand ∧
        (∀ cut, cut ≤ start → moved.state cut = trace.state cut ∧ moved.notes cut = trace.notes cut) ∧
        (∀ cut, cut < start → moved.event cut = trace.event cut) ∧
        moved.event start = .command (.remove name) ∧ moved.state (start + 1) name = none ∧
        commandAt moved start = commandAt trace (start + span) ∧
        orchestrationInput moved = orchestrationInput trace ∧
        (¬ Nonempty (ClosedEpisode moved)) ∧ Progress.Quiet (moved.state last) := by
  have inside : start < last := by omega
  constructor
  · intro present
    obtain ⟨moved, expand, _, _, cuts, events, selected, addressed, input, _, opened, settled, path⟩ :=
      pull_command_through_activations_with_path trace openOnly quiet bounded removal block
        (fun absent => False.elim (present absent))
    have step := (moved.step start inside).1
    rw [selected] at step
    refine ⟨moved, expand, path, cuts, events, selected, ?_, addressed, input, opened, settled⟩
    rw [step.2]
    simp [Command.apply, erase]
  · rintro ⟨moved, _, _, cuts, _, selected, _, _, _, _, _⟩ absent
    have step := (moved.step start inside).1
    rw [selected] at step
    have removable : Removable (moved.state start) name := step.1
    rw [(cuts start (Nat.le_refl _)).1] at removable
    simp [Removable, absent] at removable

/-- If a removal cannot create a vacancy at the beginning of its
activation block, its actual target was born inside the block. -/
theorem birth_blocks_early_removal (trace : Trace program last)
    {start span : Nat} (bounded : start + span < last) {name : Name}
    (removal : trace.event (start + span) = .command (.remove name))
    (block : ∀ cut, start ≤ cut → cut < start + span → ∃ kind actor, trace.event cut = .lifecycle kind actor)
    (absent : trace.state start name = none) :
    ∃ cut kind actor address, start ≤ cut ∧ cut < start + span ∧
      trace.event cut = .lifecycle kind actor ∧
      GuardedBirthMatching.BornAt trace name (cut + 1) ∧
      GuardedReservationOrder.removalAddress trace (start + span) = some address ∧
      Addressed trace (cut + 1) address := by
  obtain ⟨cut, row, _, earlier, found, tag, resident, vacant, original, _, _⟩ :=
    trace.retire_remove_birth bounded (.inr removal)
  have lower : start ≤ cut := by
    apply Nat.le_of_not_gt
    intro before
    exact resident.present start (by omega) (by omega) absent
  have born : GuardedBirthMatching.BornAt trace name (cut + 1) :=
    ⟨by omega, by omega, by simpa using vacant, by rw [original]; exact Option.noConfusion⟩
  obtain ⟨address, addressed⟩ := exists_address trace born
  obtain ⟨kind, actor, event⟩ := block cut lower earlier
  exact ⟨cut, kind, actor, address, lower, earlier, event, born,
    GuardedReservationOrder.removalAddress_eq_some trace |>.mpr
      ⟨name, cut + 1, removal, tag, addressed, by rw [found]; exact Option.noConfusion⟩, addressed⟩

private def commandTarget : AddressedCommand Name Key Code → Option Address
  | .insert _ _ => none
  | .retire path _ | .remove path _ => some path

private theorem existing_key (trace : Trace program last) {cut : Nat} (bounded : cut < last) {name : Name}
    (event : trace.event cut = .command (.retire name) ∨ trace.event cut = .command (.remove name)) :
    ∃ birth path, (commandAt trace cut).bind commandTarget = some path ∧
      (trace.notes cut).1 name = some birth ∧ Addressed trace birth path := by
  obtain ⟨path, component, target⟩ := targetAt_command trace bounded event
  obtain ⟨birth, _, live, address, _, _⟩ := (targetAt_eq_some trace).mp target
  refine ⟨birth, path, ?_, live, address⟩
  rcases event with retire | remove
  · simp [commandAt, retire, commandTarget, target]
  · simp [commandAt, remove, commandTarget, target]

private theorem pending_target_present {leftLength rightLength start time : Nat}
    (left : Trace program leftLength) (right : Trace program rightLength)
    (leftBound : start < leftLength) (rightBound : time < rightLength) (before : start ≤ time)
    (current : CutAgreement left right start)
    (past : ∀ cut, cut < start → addressedEventAt left cut = addressedEventAt right cut)
    {first : Cmd} (firstEvent : left.event start = .command first) {target : Name}
    (later : right.event time = .command (.retire target) ∨ right.event time = .command (.remove target))
    (same : commandAt left start = commandAt right time) : right.state start target ≠ none := by
  obtain ⟨laterBirth, path, addressedLater, laterTag, laterPath⟩ := existing_key right rightBound later
  have firstKey := (congrArg (fun command => command.bind commandTarget) same).trans addressedLater
  have known : ∃ birth, (left.notes start).1 first.actor = some birth ∧ Addressed left birth path := by
    cases first with
    | insert => simp [commandAt, firstEvent, commandTarget] at firstKey
    | retire name =>
      obtain ⟨birth, otherPath, key, tagged, address⟩ := existing_key left leftBound (.inl firstEvent)
      exact ⟨birth, tagged, Option.some.inj (key.symm.trans firstKey) ▸ address⟩
    | remove name =>
      obtain ⟨birth, otherPath, key, tagged, address⟩ := existing_key left leftBound (.inr firstEvent)
      exact ⟨birth, tagged, Option.some.inj (key.symm.trans firstKey) ▸ address⟩
  obtain ⟨birth, leftTag, leftPath⟩ := known
  obtain ⟨p, _, live, _⟩ := current
  have earlyTag : (right.notes start).1 (p.toFun first.actor) = some birth := (live first.actor).trans leftTag
  have early := recorded_birth right (by omega : start ≤ rightLength) earlyTag
  obtain ⟨earlyPath, rightPath⟩ := exists_address right early.1
  have samePath := address_of_matched_birth left right past early.2 leftPath rightPath
  have sameBirth := rightPath.injective laterPath samePath.symm
  have sameName := born_unique right early.1 (sameBirth.symm ▸ (recorded_birth right (Nat.le_of_lt rightBound) laterTag).1)
  intro absent
  have missing := (right.births_agree start (by omega) (p.toFun first.actor)).mpr (sameName.symm ▸ absent)
  rw [earlyTag] at missing
  cases missing

private def isCommandEvent : Option (AddressedEvent Key Code) → Bool
  | none | some (.lifecycle ..) => false
  | _ => true

private theorem command_presence_from_address (trace : Trace program last) {cut : Nat} (bounded : cut < last) :
    (commandAt trace cut).isSome = isCommandEvent (addressedEventAt trace cut) := by
  cases event : trace.event cut with
  | lifecycle kind actor =>
    cases tag : actorAddress trace cut <;> simp [commandAt, addressedEventAt, event, tag, isCommandEvent]
  | command command =>
    rw [addressedEventAt_of_command trace bounded event]
    cases commandAt trace cut with
    | none => rfl
    | some entry => cases entry <;> rfl

private theorem filterMap_lengths {α : Type v} {β : Type u} (cuts : List α) (left right : α → Option β)
    (agrees : ∀ cut ∈ cuts, (left cut).isSome = (right cut).isSome) :
    (cuts.filterMap left).length = (cuts.filterMap right).length := by
  simp only [List.length_filterMap_eq_countP]
  exact List.countP_congr (fun cut member => by rw [agrees cut member])

private theorem matched_command_counts {leftLength rightLength start : Nat}
    (left : Trace program leftLength) (right : Trace program rightLength)
    (leftBound : start ≤ leftLength) (rightBound : start ≤ rightLength)
    (past : ∀ cut, cut < start → addressedEventAt left cut = addressedEventAt right cut) :
    ((List.range start).filterMap (commandAt left)).length = ((List.range start).filterMap (commandAt right)).length := by
  apply filterMap_lengths
  intro cut member
  have prior := List.mem_range.mp member
  rw [command_presence_from_address left (by omega), command_presence_from_address right (by omega), past cut prior]

/-- Equal command input and a matched prefix transfer the absence of
remaining commands to the other trace. -/
theorem command_free_of_matched_prefix {leftLength rightLength start : Nat}
    (left : Trace program leftLength) (right : Trace program rightLength)
    (leftBound : start ≤ leftLength) (rightBound : start ≤ rightLength)
    (past : ∀ cut, cut < start → addressedEventAt left cut = addressedEventAt right cut)
    (input : orchestrationInput left = orchestrationInput right)
    (leftFree : ∀ cut, start ≤ cut → cut < leftLength → ∃ kind name, left.event cut = .lifecycle kind name) :
    ∀ cut, start ≤ cut → cut < rightLength → ∃ kind name, right.event cut = .lifecycle kind name := by
  have split (length : Nat) (bound : start ≤ length) :
      List.range length = List.range start ++ List.range' start (length - start) := by
    simpa only [List.range_eq_range', Nat.zero_add, Nat.add_sub_of_le bound] using
      (List.range'_append_1 (s := 0) (m := start) (n := length - start)).symm
  have sourceTail : (List.range' start (leftLength - start)).filterMap (commandAt left) = [] := by
    apply List.filterMap_eq_nil_iff.mpr
    intro i member
    obtain ⟨offset, valid, atCut⟩ := List.mem_range'.mp member
    simp at atCut
    exact (commandAt_none left (by omega)).mpr (leftFree i (by omega) (by omega))
  have lengths := congrArg List.length input
  unfold orchestrationInput at lengths
  rw [split leftLength leftBound, split rightLength rightBound, List.filterMap_append, List.filterMap_append,
    sourceTail, List.length_append, List.length_append, List.length_nil,
    matched_command_counts left right leftBound rightBound past] at lengths
  have targetTail : (List.range' start (rightLength - start)).filterMap (commandAt right) = [] :=
    List.length_eq_zero_iff.mp (by omega)
  intro cut lower inside
  apply (commandAt_none right inside).mp
  apply List.filterMap_eq_nil_iff.mp targetTail
  apply List.mem_range'.mpr
  exact ⟨cut - start, by omega, by simp; omega⟩

private theorem next_command_at_rank (trace : Trace program last) {start span : Nat} (bounded : start + span < last)
    {command : Cmd} (event : trace.event (start + span) = .command command)
    (block : ∀ cut, start ≤ cut → cut < start + span → ∃ kind name, trace.event cut = .lifecycle kind name) :
    (orchestrationInput trace)[((List.range start).filterMap (commandAt trace)).length]? = commandAt trace (start + span) := by
  let time := start + span
  have prefixEq : List.range time = List.range start ++ List.range' start span := by
    simpa only [List.range_eq_range', Nat.zero_add] using
      (List.range'_append_1 (s := 0) (m := start) (n := span)).symm
  have split : List.range last = List.range time ++ time :: List.range' (time + 1) (last - (time + 1)) := by
    have tail : List.range last = List.range time ++ List.range' time (last - time) := by
      simpa only [List.range_eq_range', Nat.zero_add, show time + (last - time) = last by omega] using
        (List.range'_append_1 (s := 0) (m := time) (n := last - time)).symm
    rw [tail, show last - time = (last - (time + 1)) + 1 by omega, List.range'_succ]
  have noCommands : (List.range' start span).filterMap (commandAt trace) = [] := by
    apply List.filterMap_eq_nil_iff.mpr
    intro i member
    obtain ⟨offset, boundedOffset, placed⟩ := List.mem_range'.mp member
    simp at placed
    exact (commandAt_none trace (by omega)).mpr (block i (by omega) (by omega))
  unfold orchestrationInput
  rw [split, prefixEq, List.filterMap_append, List.filterMap_append, noCommands, List.append_nil,
    List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  cases read : commandAt trace time with
  | none =>
    obtain ⟨_, _, lifecycle⟩ := (commandAt_none trace bounded).mp read
    have clash := event.symm.trans lifecycle
    cases clash
  | some entry => simp [read]

/-- The shared command list and previously matched events determine the
two next addressed commands, even at different cuts. -/
theorem next_delayed_commands_agree {leftLength rightLength start leftSpan rightSpan : Nat}
    (left : Trace program leftLength) (right : Trace program rightLength)
    (leftBound : start + leftSpan < leftLength) (rightBound : start + rightSpan < rightLength)
    (past : ∀ cut, cut < start → addressedEventAt left cut = addressedEventAt right cut)
    (input : orchestrationInput left = orchestrationInput right)
    {first later : Cmd} (firstEvent : left.event (start + leftSpan) = .command first)
    (laterEvent : right.event (start + rightSpan) = .command later)
    (leftBlock : ∀ cut, start ≤ cut → cut < start + leftSpan → ∃ kind name, left.event cut = .lifecycle kind name)
    (rightBlock : ∀ cut, start ≤ cut → cut < start + rightSpan → ∃ kind name, right.event cut = .lifecycle kind name) :
    commandAt left (start + leftSpan) = commandAt right (start + rightSpan) := by
  have counts := matched_command_counts left right (by omega : start ≤ leftLength) (by omega : start ≤ rightLength) past
  have first := next_command_at_rank left leftBound firstEvent leftBlock
  have second := next_command_at_rank right rightBound laterEvent rightBlock
  rw [input, counts, second] at first
  exact first.symm

theorem next_commands_agree {leftLength rightLength start span : Nat}
    (left : Trace program leftLength) (right : Trace program rightLength)
    (leftBound : start < leftLength) (rightBound : start + span < rightLength)
    (past : ∀ cut, cut < start → addressedEventAt left cut = addressedEventAt right cut)
    (input : orchestrationInput left = orchestrationInput right)
    {first later : Cmd} (firstEvent : left.event start = .command first)
    (laterEvent : right.event (start + span) = .command later)
    (block : ∀ cut, start ≤ cut → cut < start + span → ∃ kind name, right.event cut = .lifecycle kind name) :
    commandAt left start = commandAt right (start + span) :=
  next_delayed_commands_agree left right (leftSpan := 0) leftBound rightBound past input
    firstEvent laterEvent (fun _ lower upper => by omega) block

private theorem pending_command_ready {leftLength rightLength start span : Nat}
    (left : Trace program leftLength) (right : Trace program rightLength)
    (leftBound : start < leftLength) (rightBound : start + span < rightLength)
    (current : CutAgreement left right start)
    (past : ∀ cut, cut < start → addressedEventAt left cut = addressedEventAt right cut)
    {first later : Cmd} (firstEvent : left.event start = .command first)
    (laterEvent : right.event (start + span) = .command later)
    (same : commandAt left start = commandAt right (start + span)) :
    right.state start later.actor = none → right.state (start + span) later.actor = none := by
  cases later with
  | insert name component =>
    intro _
    have step := (right.step _ rightBound).1
    rw [laterEvent] at step
    exact step.1.1
  | retire name =>
    intro absent
    exact False.elim (pending_target_present left right leftBound rightBound (by omega) current past firstEvent
      (.inl laterEvent) same absent)
  | remove name =>
    intro absent
    exact False.elim (pending_target_present left right leftBound rightBound (by omega) current past firstEvent
      (.inr laterEvent) same absent)

/-- Synchronize the next addressed command of two quiet open runs. If
one run is already at the command, its matched prefix supplies any
existing target in the other run before the remaining activations. -/
theorem align_next_command_with_path {leftLength rightLength start span : Nat}
    (left : Trace program leftLength) (right : Trace program rightLength)
    (leftBound : start < leftLength) (rightBound : start + span < rightLength)
    (rightOpen : ¬ Nonempty (ClosedEpisode right)) (rightQuiet : Progress.Quiet (right.state rightLength))
    (current : CutAgreement left right start) (stable : ChildContinuations program)
    (past : ∀ cut, cut < start → addressedEventAt left cut = addressedEventAt right cut)
    {first later : Cmd} (firstEvent : left.event start = .command first)
    (laterEvent : right.event (start + span) = .command later)
    (block : ∀ cut, start ≤ cut → cut < start + span → ∃ kind name, right.event cut = .lifecycle kind name)
    (input : orchestrationInput left = orchestrationInput right) :
    ∃ (moved : Trace program rightLength) (expand : Nat → Nat),
      StableActorAddresses right moved expand ∧
      (∀ cut, cut < start + 1 → addressedEventAt left cut = addressedEventAt moved cut) ∧
      CutAgreement left moved (start + 1) ∧ orchestrationInput moved = orchestrationInput right ∧
      moved.state rightLength = right.state rightLength ∧
      (¬ Nonempty (ClosedEpisode moved)) ∧ Progress.Quiet (moved.state rightLength) ∧ CommandExchangePath right moved expand := by
  have same := next_commands_agree left right leftBound rightBound past input firstEvent laterEvent block
  have ready := pending_command_ready left right leftBound rightBound current past firstEvent laterEvent same
  obtain ⟨moved, expand, retained, stamps, fixed, _, event, matched, commands, endpoint, opened, settled, path⟩ :=
    pull_command_through_activations_with_path right rightOpen rightQuiet rightBound laterEvent block ready
  have earlier (cut : Nat) (inside : cut < start) : addressedEventAt left cut = addressedEventAt moved cut := by
    have equality := stable_addressed_event retained (cut := cut) (by omega)
    rw [stamps _ (by omega : cut + 1 ≤ start), Nat.add_sub_cancel] at equality
    exact (past cut inside).trans equality.symm
  have movedBound : start < rightLength := by omega
  have last : addressedEventAt left start = addressedEventAt moved start := by
    rw [addressedEventAt_of_command left leftBound firstEvent, addressedEventAt_of_command moved movedBound event,
      matched, same]
  have currentMoved : CutAgreement left moved start := by
    obtain ⟨names, registry, live, words⟩ := current
    have initial := fixed start (Nat.le_refl _)
    refine ⟨names, by simpa only [initial.1] using registry, by simpa only [initial.2] using live, ?_⟩
    unfold GuardedBirthReplay.SavedMatch at words ⊢
    simpa only [initial.2] using words
  have leftCommand {kind name} (impossible : left.event start = .lifecycle kind name) : Transposition.Activation kind.rule := by
    rw [firstEvent] at impossible
    cases impossible
  have rightCommand {kind name} (impossible : moved.event start = .lifecycle kind name) : Transposition.Activation kind.rule := by
    rw [event] at impossible
    cases impossible
  refine ⟨moved, expand, retained, ?_, advance_addressed_cut left moved leftBound movedBound currentMoved stable
    leftCommand rightCommand earlier last, commands, endpoint, opened, settled, path⟩
  intro cut inside
  rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ inside) with rfl | before
  · exact last
  · exact earlier cut before

theorem least_later_command (trace : Trace program last) {start time : Nat} {command : Cmd}
    (lower : start ≤ time) (bounded : time < last) (event : trace.event time = .command command) :
    ∃ (span : Nat) (next : Cmd), start + span < last ∧ trace.event (start + span) = .command next ∧
      ∀ cut, start ≤ cut → cut < start + span → ∃ kind name, trace.event cut = .lifecycle kind name := by
  induction time using Nat.strongRecOn generalizing command with
  | ind time ih =>
    by_cases prior : ∃ (cut : Nat) (cmd : Cmd), start ≤ cut ∧ cut < time ∧ trace.event cut = .command cmd
    · obtain ⟨cut, cmd, before, earlier, found⟩ := prior
      exact ih cut earlier before (by omega) found
    · have exactCut : start + (time - start) = time := by omega
      refine ⟨time - start, command, by rw [exactCut]; exact bounded, by rw [exactCut]; exact event, ?_⟩
      intro cut first earlier
      rw [exactCut] at earlier
      cases label : trace.event cut with
      | lifecycle kind name => exact ⟨kind, name, rfl⟩
      | command cmd => exact False.elim (prior ⟨cut, cmd, first, earlier, label⟩)

/-- A command remaining after the common prefix on one side guarantees
a first remaining command on the other side. -/
theorem pending_delayed_command_occurs {leftLength rightLength start leftSpan : Nat}
    (left : Trace program leftLength) (right : Trace program rightLength)
    (leftBound : start + leftSpan < leftLength) (rightBound : start ≤ rightLength)
    (past : ∀ cut, cut < start → addressedEventAt left cut = addressedEventAt right cut)
    (input : orchestrationInput left = orchestrationInput right)
    {command : Cmd} (firstEvent : left.event (start + leftSpan) = .command command)
    (block : ∀ cut, start ≤ cut → cut < start + leftSpan → ∃ kind actor, left.event cut = .lifecycle kind actor) :
    ∃ span later, start + span < rightLength ∧ right.event (start + span) = .command later ∧
      ∀ cut, start ≤ cut → cut < start + span → ∃ kind actor, right.event cut = .lifecycle kind actor := by
  have counts := matched_command_counts left right (by omega : start ≤ leftLength) rightBound past
  have next := next_command_at_rank left leftBound firstEvent block
  have pending : commandAt left (start + leftSpan) ≠ none := by
    intro missing
    obtain ⟨kind, name, wrong⟩ := (commandAt_none left leftBound).mp missing
    rw [firstEvent] at wrong
    cases wrong
  rw [input, counts] at next
  have split : List.range rightLength = List.range start ++ List.range' start (rightLength - start) := by
    simpa only [List.range_eq_range', Nat.zero_add, Nat.add_sub_of_le rightBound] using
      (List.range'_append_1 (s := 0) (m := start) (n := rightLength - start)).symm
  unfold orchestrationInput at next
  rw [split, List.filterMap_append, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at next
  have existsLater : (List.range' start (rightLength - start)).filterMap (commandAt right) ≠ [] := by
    intro empty
    rw [empty] at next
    exact pending next.symm
  obtain ⟨entry, member⟩ := List.exists_mem_of_ne_nil _ existsLater
  obtain ⟨cut, placed, found⟩ := List.mem_filterMap.mp member
  obtain ⟨offset, inside, atCut⟩ := List.mem_range'.mp placed
  simp at atCut
  have external : ∃ cmd, right.event cut = .command cmd := by
    cases event : right.event cut with
    | command cmd => exact ⟨cmd, rfl⟩
    | lifecycle => simp [commandAt, event] at found
  obtain ⟨cmd, event⟩ := external
  exact least_later_command right (by omega : start ≤ cut) (by omega : cut < rightLength) event

private theorem pending_command_occurs {leftLength rightLength start : Nat}
    (left : Trace program leftLength) (right : Trace program rightLength)
    (leftBound : start < leftLength) (rightBound : start ≤ rightLength)
    (past : ∀ cut, cut < start → addressedEventAt left cut = addressedEventAt right cut)
    (input : orchestrationInput left = orchestrationInput right)
    {command : Cmd} (firstEvent : left.event start = .command command) :
    ∃ span later, start + span < rightLength ∧ right.event (start + span) = .command later ∧
      ∀ cut, start ≤ cut → cut < start + span → ∃ kind actor, right.event cut = .lifecycle kind actor :=
  pending_delayed_command_occurs left right (leftSpan := 0) leftBound rightBound past input firstEvent
    (fun _ lower upper => by omega)

theorem align_next_command {leftLength rightLength start span : Nat}
    (left : Trace program leftLength) (right : Trace program rightLength)
    (leftBound : start < leftLength) (rightBound : start + span < rightLength)
    (rightOpen : ¬ Nonempty (ClosedEpisode right)) (rightQuiet : Progress.Quiet (right.state rightLength))
    (current : CutAgreement left right start) (stable : ChildContinuations program)
    (past : ∀ cut, cut < start → addressedEventAt left cut = addressedEventAt right cut)
    {first later : Cmd} (firstEvent : left.event start = .command first)
    (laterEvent : right.event (start + span) = .command later)
    (block : ∀ cut, start ≤ cut → cut < start + span → ∃ kind name, right.event cut = .lifecycle kind name)
    (input : orchestrationInput left = orchestrationInput right) :
    ∃ (moved : Trace program rightLength) (expand : Nat → Nat),
      StableActorAddresses right moved expand ∧
      (∀ cut, cut < start + 1 → addressedEventAt left cut = addressedEventAt moved cut) ∧
      CutAgreement left moved (start + 1) ∧ orchestrationInput moved = orchestrationInput right ∧
      moved.state rightLength = right.state rightLength ∧
      (¬ Nonempty (ClosedEpisode moved)) ∧ Progress.Quiet (moved.state rightLength) := by
  obtain ⟨moved, expand, kept, order, cut, commands, endpoint, opened, quiet, _⟩ :=
    align_next_command_with_path left right leftBound rightBound rightOpen rightQuiet current stable past firstEvent laterEvent block input
  exact ⟨moved, expand, kept, order, cut, commands, endpoint, opened, quiet⟩

/-- A matched prefix and shared surviving command input let a command on
one side advance both traces. The right-hand cut of its counterpart is
derived from the remaining input. -/
theorem align_pending_command_with_path {leftLength rightLength start : Nat}
    (left : Trace program leftLength) (right : Trace program rightLength)
    (leftBound : start < leftLength) (rightBound : start ≤ rightLength)
    (rightOpen : ¬ Nonempty (ClosedEpisode right)) (rightQuiet : Progress.Quiet (right.state rightLength))
    (current : CutAgreement left right start) (stable : ChildContinuations program)
    (past : ∀ cut, cut < start → addressedEventAt left cut = addressedEventAt right cut)
    (input : orchestrationInput left = orchestrationInput right)
    {command : Cmd} (firstEvent : left.event start = .command command) :
    ∃ (moved : Trace program rightLength) (expand : Nat → Nat),
      start < rightLength ∧ StableActorAddresses right moved expand ∧
      (∀ cut, cut < start + 1 → addressedEventAt left cut = addressedEventAt moved cut) ∧
      CutAgreement left moved (start + 1) ∧ orchestrationInput moved = orchestrationInput right ∧
      moved.state rightLength = right.state rightLength ∧
      (¬ Nonempty (ClosedEpisode moved)) ∧ Progress.Quiet (moved.state rightLength) ∧ CommandExchangePath right moved expand := by
  obtain ⟨span, later, bounded, laterEvent, block⟩ :=
    pending_command_occurs left right leftBound rightBound past input firstEvent
  obtain ⟨moved, expand, kept, schedule, agreement, commands, endpoint, openOnly, quiet, path⟩ :=
    align_next_command_with_path left right leftBound bounded rightOpen rightQuiet current stable past
    firstEvent laterEvent block input
  exact ⟨moved, expand, by omega, kept, schedule, agreement, commands, endpoint, openOnly, quiet, path⟩

theorem align_pending_command {leftLength rightLength start : Nat}
    (left : Trace program leftLength) (right : Trace program rightLength)
    (leftBound : start < leftLength) (rightBound : start ≤ rightLength)
    (rightOpen : ¬ Nonempty (ClosedEpisode right)) (rightQuiet : Progress.Quiet (right.state rightLength))
    (current : CutAgreement left right start) (stable : ChildContinuations program)
    (past : ∀ cut, cut < start → addressedEventAt left cut = addressedEventAt right cut)
    (input : orchestrationInput left = orchestrationInput right)
    {command : Cmd} (firstEvent : left.event start = .command command) :
    ∃ (moved : Trace program rightLength) (expand : Nat → Nat),
      start < rightLength ∧ StableActorAddresses right moved expand ∧
      (∀ cut, cut < start + 1 → addressedEventAt left cut = addressedEventAt moved cut) ∧
      CutAgreement left moved (start + 1) ∧ orchestrationInput moved = orchestrationInput right ∧
      moved.state rightLength = right.state rightLength ∧
      (¬ Nonempty (ClosedEpisode moved)) ∧ Progress.Quiet (moved.state rightLength) := by
  obtain ⟨moved, expand, canAdvance, kept, order, cut, commands, endpoint, opened, quiet, _⟩ :=
    align_pending_command_with_path left right leftBound rightBound rightOpen rightQuiet current stable past input firstEvent
  exact ⟨moved, expand, canAdvance, kept, order, cut, commands, endpoint, opened, quiet⟩

/-- At a matched cut, a normalized peer is already at this same addressed
command. Any positive delay would require the actual target to be born
after the cut, which is incompatible with the matching command. -/
theorem pending_command_at_suffix_birth_frontier {leftLength rightLength start : Nat}
    (left : Trace program leftLength) (right : Trace program rightLength)
    (leftBound : start < leftLength) (rightBound : start ≤ rightLength)
    (rightNormal : CommandsAtBirthBarriersFrom right start)
    (current : CutAgreement left right start)
    (past : ∀ cut, cut < start → addressedEventAt left cut = addressedEventAt right cut)
    (input : orchestrationInput left = orchestrationInput right)
    {command : Cmd} (external : left.event start = .command command) :
    start < rightLength ∧ (∃ next, right.event start = .command next) ∧
      addressedEventAt left start = addressedEventAt right start := by
  obtain ⟨span, later, bounded, laterEvent, block⟩ :=
    pending_command_occurs left right leftBound rightBound past input external
  have same := next_commands_agree left right leftBound bounded past input external laterEvent block
  have noDelay : span = 0 := by
    apply Nat.eq_zero_of_not_pos
    intro positive
    obtain ⟨absent, present⟩ := rightNormal.target_absent (Nat.le_refl _) positive bounded laterEvent block
    have ready := pending_command_ready left right leftBound bounded current past external laterEvent same
    exact present (ready (absent start (Nat.le_refl _) (by omega)))
  subst span
  refine ⟨bounded, ⟨later, laterEvent⟩, ?_⟩
  exact (addressedEventAt_of_command left leftBound external).trans
    ((congrArg (Option.map commandEventAddress) same).trans (addressedEventAt_of_command right bounded laterEvent).symm)

theorem pending_command_at_birth_frontier {leftLength rightLength start : Nat}
    (left : Trace program leftLength) (right : Trace program rightLength)
    (leftBound : start < leftLength) (rightBound : start ≤ rightLength)
    (rightNormal : CommandsAtBirthBarriers right)
    (current : CutAgreement left right start)
    (past : ∀ cut, cut < start → addressedEventAt left cut = addressedEventAt right cut)
    (input : orchestrationInput left = orchestrationInput right)
    {command : Cmd} (external : left.event start = .command command) :
    start < rightLength ∧ (∃ next, right.event start = .command next) ∧
      addressedEventAt left start = addressedEventAt right start :=
  pending_command_at_suffix_birth_frontier left right leftBound rightBound
    (fun cut _ => rightNormal cut) current past input external

/-- A matched pending command becomes immediate in the normalized suffix,
with no further exchanges after suffix normalization. -/
theorem normalize_suffix_to_match_pending_command {leftLength rightLength start : Nat}
    (left : Trace program leftLength) (right : Trace program rightLength)
    (leftBound : start < leftLength) (rightBound : start ≤ rightLength)
    (opened : ¬ Nonempty (ClosedEpisode right)) (quiet : Progress.Quiet (right.state rightLength))
    (current : CutAgreement left right start) (stable : ChildContinuations program)
    (past : ∀ cut, cut < start → addressedEventAt left cut = addressedEventAt right cut)
    (input : orchestrationInput left = orchestrationInput right)
    {command : Cmd} (external : left.event start = .command command) :
    ∃ (moved : Trace program rightLength) (expand : Nat → Nat),
      CommandExchangePath right moved expand ∧ CommandsAtBirthBarriersFrom moved start ∧
      start < rightLength ∧ (∃ next, moved.event start = .command next) ∧
      (∀ cut, cut ≤ start → moved.state cut = right.state cut ∧ moved.notes cut = right.notes cut) ∧
      (∀ cut, cut < start → moved.event cut = right.event cut) ∧
      (∀ cut, cut < start + 1 → addressedEventAt left cut = addressedEventAt moved cut) ∧
      CutAgreement left moved (start + 1) ∧
      (¬ Nonempty (ClosedEpisode moved)) ∧ Progress.Quiet (moved.state rightLength) := by
  obtain ⟨moved, expand, barriers, _, commands, _, _, openMoved, quietMoved, path, cuts, labels, addresses⟩ :=
    push_commands_to_birth_barriers_from right start opened quiet
  have boundary := cuts start (Nat.le_refl _) rightBound
  have matched : CutAgreement left moved start := by
    obtain ⟨names, states, births, saved⟩ := current
    refine ⟨names, by rw [boundary.1]; exact states, by rw [boundary.2]; exact births, ?_⟩
    unfold GuardedBirthReplay.SavedMatch at saved ⊢
    simpa only [boundary.2] using saved
  have earlier (cut : Nat) (before : cut < start) : addressedEventAt left cut = addressedEventAt moved cut :=
    (past cut before).trans (addresses cut before (by omega)).symm
  obtain ⟨inside, selected, now⟩ := pending_command_at_suffix_birth_frontier left moved leftBound rightBound
    barriers matched earlier (input.trans commands.symm) external
  obtain ⟨next, atStart⟩ := selected
  have advance := advance_addressed_cut left moved leftBound inside matched stable
    (fun event => by rw [external] at event; cases event)
    (fun event => by rw [atStart] at event; cases event) earlier now
  refine ⟨moved, expand, path, barriers, inside, ⟨next, atStart⟩,
    fun cut bound => cuts cut bound (by omega), labels, ?_, advance, openMoved, quietMoved⟩
  intro cut before
  rcases Nat.eq_or_lt_of_le (show cut ≤ start by omega) with rfl | prior
  · exact now
  · exact earlier cut prior

/-- A command at a child's birth cut reads the stamp of that birth. -/
theorem command_target_of_birth_at_cut (trace : Trace program last)
    {cut : Nat} (bounded : cut < last) {command : Cmd}
    (external : trace.event cut = .command command)
    (born : GuardedBirthMatching.BornAt trace command.actor cut) :
    ∃ address component,
      Addressed trace cut address ∧ targetAt trace cut command.actor = some (address, component) ∧
      (command = .retire command.actor ∨ command = .remove command.actor) := by
  have target : trace.event (cut) = .command (.retire command.actor) ∨
      trace.event (cut) = .command (.remove command.actor) := by
    cases command with
    | insert name component =>
      have step := (trace.step _ bounded).1
      rw [external] at step
      exact False.elim (born.2.2.2 step.1.1)
    | retire => exact .inl external
    | remove => exact .inr external
  obtain ⟨address, component, found⟩ := targetAt_command trace bounded target
  obtain ⟨birth, _, tag, path, _, _⟩ := (targetAt_eq_some trace).mp found
  -- The birth stamp read by this command is the one at its birth cut.
  have created : (trace.notes (cut)).1 command.actor = some (cut) := by
    rw [trace.notes_eq _ (Nat.le_of_lt bounded)]
    have boundary : cut - 1 + 1 = cut := by have := born.1; omega
    rw [← boundary]
    exact Incarnation.birthAt_of_created born.2.2.1 (by rw [boundary]; exact born.2.2.2)
  have stamp := Option.some.inj (tag.symm.trans created)
  refine ⟨address, component, stamp ▸ path, found, ?_⟩
  exact target.imp (fun event => Event.command.inj (external.symm.trans event))
    (fun event => Event.command.inj (external.symm.trans event))

/-- A delayed command in a normalized suffix is a retirement or
removal of the row born at the immediately preceding activation. -/
theorem delayed_command_birth_at_suffix_frontier (trace : Trace program last)
    {start span : Nat} (positive : 0 < span) (bounded : start + span < last)
    (normal : CommandsAtBirthBarriersFrom trace start)
    {command : Cmd} (external : trace.event (start + span) = .command command)
    (block : ∀ cut, start ≤ cut → cut < start + span → ∃ kind name, trace.event cut = .lifecycle kind name) :
    ∃ address component, GuardedBirthMatching.BornAt trace command.actor (start + span) ∧
      Addressed trace (start + span) address ∧ targetAt trace (start + span) command.actor = some (address, component) ∧
      (command = .retire command.actor ∨ command = .remove command.actor) := by
  obtain ⟨absent, present⟩ := normal.target_absent (Nat.le_refl _) positive bounded external block
  have earlier : start + span - 1 < start + span := by omega
  have born : GuardedBirthMatching.BornAt trace command.actor (start + span) :=
    ⟨by omega, by omega, absent _ (by omega) earlier, present⟩
  obtain ⟨address, component, path, target, kind⟩ := command_target_of_birth_at_cut trace bounded external born
  exact ⟨address, component, born, path, target, kind⟩

/-- The first delayed command in each of two normalized suffixes waits
for the same addressed birth, even when the activations are at different
cuts or the new rows use different raw names. -/
theorem commands_at_birth_cuts_share_target {leftLength rightLength start leftSpan rightSpan : Nat}
    (left : Trace program leftLength) (right : Trace program rightLength)
    (leftBound : start + leftSpan < leftLength) (rightBound : start + rightSpan < rightLength)
    (past : ∀ cut, cut < start → addressedEventAt left cut = addressedEventAt right cut)
    (input : orchestrationInput left = orchestrationInput right)
    {first later : Cmd} (firstEvent : left.event (start + leftSpan) = .command first)
    (laterEvent : right.event (start + rightSpan) = .command later)
    (leftBorn : GuardedBirthMatching.BornAt left first.actor (start + leftSpan))
    (rightBorn : GuardedBirthMatching.BornAt right later.actor (start + rightSpan))
    (leftBlock : ∀ cut, start ≤ cut → cut < start + leftSpan → ∃ kind name, left.event cut = .lifecycle kind name)
    (rightBlock : ∀ cut, start ≤ cut → cut < start + rightSpan → ∃ kind name, right.event cut = .lifecycle kind name) :
    ∃ address component,
      GuardedBirthMatching.BornAt left first.actor (start + leftSpan) ∧
      GuardedBirthMatching.BornAt right later.actor (start + rightSpan) ∧
      Addressed left (start + leftSpan) address ∧ Addressed right (start + rightSpan) address ∧
      targetAt left (start + leftSpan) first.actor = some (address, component) ∧
      targetAt right (start + rightSpan) later.actor = some (address, component) := by
  obtain ⟨address, component, leftAddress, leftTarget, leftKind⟩ :=
    command_target_of_birth_at_cut left leftBound firstEvent leftBorn
  obtain ⟨other, otherComponent, rightAddress, rightTarget, rightKind⟩ :=
    command_target_of_birth_at_cut right rightBound laterEvent rightBorn
  have commands := next_delayed_commands_agree left right leftBound rightBound past input
    firstEvent laterEvent leftBlock rightBlock
  have targets : address = other ∧ component = otherComponent := by
    cases first <;> cases later <;>
      simp [OrchestrationSorting.Command.actor] at leftKind rightKind <;>
      simp [commandAt, firstEvent, laterEvent, OrchestrationSorting.Command.actor] at commands leftTarget rightTarget <;>
      simp_all
  obtain ⟨rfl, rfl⟩ := targets
  exact ⟨address, component, leftBorn, rightBorn, leftAddress, rightAddress, leftTarget, rightTarget⟩

/-- Normalized peers waiting for their next command allocate the same target. -/
theorem delayed_commands_wait_for_same_birth {leftLength rightLength start leftSpan rightSpan : Nat}
    (left : Trace program leftLength) (right : Trace program rightLength)
    (leftBound : start + leftSpan < leftLength) (rightBound : start + rightSpan < rightLength)
    (leftPositive : 0 < leftSpan) (rightPositive : 0 < rightSpan)
    (leftNormal : CommandsAtBirthBarriersFrom left start) (rightNormal : CommandsAtBirthBarriersFrom right start)
    (past : ∀ cut, cut < start → addressedEventAt left cut = addressedEventAt right cut)
    (input : orchestrationInput left = orchestrationInput right)
    {first later : Cmd} (firstEvent : left.event (start + leftSpan) = .command first)
    (laterEvent : right.event (start + rightSpan) = .command later)
    (leftBlock : ∀ cut, start ≤ cut → cut < start + leftSpan → ∃ kind name, left.event cut = .lifecycle kind name)
    (rightBlock : ∀ cut, start ≤ cut → cut < start + rightSpan → ∃ kind name, right.event cut = .lifecycle kind name) :
    ∃ address component,
      GuardedBirthMatching.BornAt left first.actor (start + leftSpan) ∧
      GuardedBirthMatching.BornAt right later.actor (start + rightSpan) ∧
      Addressed left (start + leftSpan) address ∧ Addressed right (start + rightSpan) address ∧
      targetAt left (start + leftSpan) first.actor = some (address, component) ∧
      targetAt right (start + rightSpan) later.actor = some (address, component) := by
  obtain ⟨_, _, leftBorn, _, _, _⟩ :=
    delayed_command_birth_at_suffix_frontier left leftPositive leftBound leftNormal firstEvent leftBlock
  obtain ⟨_, _, rightBorn, _, _, _⟩ :=
    delayed_command_birth_at_suffix_frontier right rightPositive rightBound rightNormal laterEvent rightBlock
  exact commands_at_birth_cuts_share_target left right leftBound rightBound past input
    firstEvent laterEvent leftBorn rightBorn leftBlock rightBlock

/-- A command for a row just born after the matched cut cannot be the
peer's first command at the matched cut itself. -/
theorem newborn_command_excludes_immediate_peer {leftLength rightLength start : Nat}
    (left : Trace program leftLength) (right : Trace program rightLength)
    (leftBound : start + 1 < leftLength) (rightBound : start < rightLength)
    (current : CutAgreement right left start)
    (past : ∀ cut, cut < start → addressedEventAt left cut = addressedEventAt right cut)
    (input : orchestrationInput left = orchestrationInput right)
    {kind : Lifecycle} {actor : Name} (activation : left.event start = .lifecycle kind actor)
    {first next : Cmd} (external : left.event (start + 1) = .command first)
    (immediate : right.event start = .command next)
    (born : GuardedBirthMatching.BornAt left first.actor (start + 1)) : False := by
  have same := next_delayed_commands_agree left right (leftSpan := 1) (rightSpan := 0)
    leftBound rightBound past input external immediate
    (fun cut lo hi => by
      obtain rfl : cut = start := by omega
      exact ⟨_, _, activation⟩)
    (fun _ lo hi => by omega)
  obtain ⟨_, _, _, _, kind⟩ := command_target_of_birth_at_cut left leftBound external born
  have target : left.event (start + 1) = .command (.retire first.actor) ∨
      left.event (start + 1) = .command (.remove first.actor) :=
    kind.imp (fun eq => external.trans (congrArg Event.command eq))
      (fun eq => external.trans (congrArg Event.command eq))
  have present := pending_target_present right left rightBound leftBound (by omega) current
    (fun i earlier => (past i earlier).symm) immediate target same.symm
  exact present (by simpa only [Nat.add_sub_cancel] using born.2.2.1)

/-- The dependency shared by two delayed commands identifies the same
allocating parent and stage ordinal in their normalized suffixes. -/
theorem delayed_commands_wait_for_same_allocating_stage {leftLength rightLength start leftSpan rightSpan : Nat}
    (left : Trace program leftLength) (right : Trace program rightLength)
    (leftBound : start + leftSpan < leftLength) (rightBound : start + rightSpan < rightLength)
    (leftPositive : 0 < leftSpan) (rightPositive : 0 < rightSpan)
    (leftNormal : CommandsAtBirthBarriersFrom left start) (rightNormal : CommandsAtBirthBarriersFrom right start)
    (past : ∀ cut, cut < start → addressedEventAt left cut = addressedEventAt right cut)
    (input : orchestrationInput left = orchestrationInput right)
    {first later : Cmd} (firstEvent : left.event (start + leftSpan) = .command first)
    (laterEvent : right.event (start + rightSpan) = .command later)
    (leftBlock : ∀ cut, start ≤ cut → cut < start + leftSpan → ∃ kind name, left.event cut = .lifecycle kind name)
    (rightBlock : ∀ cut, start ≤ cut → cut < start + rightSpan → ∃ kind name, right.event cut = .lifecycle kind name) :
    let leftCut := start + leftSpan - 1
    let rightCut := start + rightSpan - 1
    ∃ (parent : Address) (ordinal leftBirth rightBirth : Nat) (leftActor rightActor : Name)
      (leftKind rightKind : Lifecycle) (component : Component Key Code),
      left.event leftCut = .lifecycle leftKind leftActor ∧ right.event rightCut = .lifecycle rightKind rightActor ∧
      (left.notes leftCut).1 leftActor = some leftBirth ∧ (right.notes rightCut).1 rightActor = some rightBirth ∧
      Addressed left leftBirth parent ∧ Addressed right rightBirth parent ∧
      occurrencesBefore (isParentStage left leftBirth) leftCut = ordinal ∧
      occurrencesBefore (isParentStage right rightBirth) rightCut = ordinal ∧
      targetAt left (start + leftSpan) first.actor = some (.child parent ordinal, component) ∧
      targetAt right (start + rightSpan) later.actor = some (.child parent ordinal, component) := by
  dsimp only
  obtain ⟨address, component, _, _, leftAddress, rightAddress, leftTarget, rightTarget⟩ :=
    delayed_commands_wait_for_same_birth left right leftBound rightBound leftPositive rightPositive
      leftNormal rightNormal past input firstEvent laterEvent leftBlock rightBlock
  let leftCut := start + leftSpan - 1
  let rightCut := start + rightSpan - 1
  have leftStep : leftCut + 1 = start + leftSpan := by dsimp [leftCut]; omega
  have rightStep : rightCut + 1 = start + rightSpan := by dsimp [rightCut]; omega
  obtain ⟨leftKind, leftActor, leftEvent⟩ := leftBlock leftCut (by omega) (by omega)
  obtain ⟨rightKind, rightActor, rightEvent⟩ := rightBlock rightCut (by omega) (by omega)
  obtain ⟨leftBirth, parent, leftTag, leftParent, leftChild⟩ :=
    (show Addressed left (leftCut + 1) address from leftStep ▸ leftAddress).parent_of_lifecycle leftEvent
  obtain ⟨rightBirth, otherParent, rightTag, rightParent, rightChild⟩ :=
    (show Addressed right (rightCut + 1) address from rightStep ▸ rightAddress).parent_of_lifecycle rightEvent
  obtain ⟨rfl, ordinal⟩ := Address.child.inj (leftChild.symm.trans rightChild)
  exact ⟨parent, _, leftBirth, rightBirth, leftActor, rightActor, leftKind, rightKind, component,
    leftEvent, rightEvent, leftTag, rightTag, leftParent, rightParent, rfl, ordinal.symm,
    leftChild ▸ leftTarget, leftChild ▸ rightTarget⟩

/-- If one run takes a lifecycle step at a normalized frontier, another
run with the same prefix and input cannot pull its pending command to
that cut. For a pending removal, this forces the target to be absent
at the shared cut. The intervening command-free block must give birth to it. -/
theorem ready_command_precludes_frontier_activation {leftLength rightLength start span : Nat}
    (left : Trace program leftLength) (right : Trace program rightLength)
    (leftBound : start < leftLength) (rightBound : start + span < rightLength)
    (leftNormal : CommandsAtBirthBarriers left)
    (rightOpen : ¬ Nonempty (ClosedEpisode right)) (rightQuiet : Progress.Quiet (right.state rightLength))
    (current : CutAgreement right left start)
    (past : ∀ cut, cut < start → addressedEventAt right cut = addressedEventAt left cut)
    (input : orchestrationInput right = orchestrationInput left)
    {kind : Lifecycle} {actor : Name} (activation : left.event start = .lifecycle kind actor)
    {command : Cmd} (external : right.event (start + span) = .command command)
    (block : ∀ cut, start ≤ cut → cut < start + span → ∃ kind actor, right.event cut = .lifecycle kind actor)
    (ready : right.state start command.actor = none → right.state (start + span) command.actor = none) : False := by
  obtain ⟨earlier, expand, retained, stamps, prefixCuts, _, advanced, _, commands, _, _, _⟩ :=
    pull_command_through_activations right rightOpen rightQuiet rightBound external block ready
  have earlierPast (cut : Nat) (bounded : cut < start) : addressedEventAt earlier cut = addressedEventAt left cut := by
    have same := stable_addressed_event retained (cut := cut) (by omega)
    rw [stamps _ (by omega : cut + 1 ≤ start), Nat.add_sub_cancel] at same
    exact same.trans (past cut bounded)
  have earlierCut : CutAgreement earlier left start := by
    obtain ⟨names, states, births, saved⟩ := current
    obtain ⟨stateEq, notesEq⟩ := prefixCuts start (Nat.le_refl _)
    refine ⟨names, by rw [stateEq]; exact states, by rw [notesEq]; exact births, ?_⟩
    unfold GuardedBirthReplay.SavedMatch at saved ⊢
    simpa only [notesEq] using saved
  obtain ⟨_, ⟨next, event⟩, _⟩ := pending_command_at_birth_frontier earlier left (by omega)
    (Nat.le_of_lt leftBound) leftNormal earlierCut earlierPast (commands.trans input) advanced
  rw [activation] at event
  cases event

/-- A release that is the first pending command can block alignment with
a normalized lifecycle step only if its target was born after the common
cut. This uses the actual incarnation, even when the raw name is reused. -/
theorem first_pending_removal_requires_birth {leftLength rightLength start span : Nat}
    (left : Trace program leftLength) (right : Trace program rightLength)
    (leftBound : start < leftLength) (rightBound : start + span < rightLength)
    (leftNormal : CommandsAtBirthBarriers left)
    (rightOpen : ¬ Nonempty (ClosedEpisode right)) (rightQuiet : Progress.Quiet (right.state rightLength))
    (current : CutAgreement right left start)
    (past : ∀ cut, cut < start → addressedEventAt right cut = addressedEventAt left cut)
    (input : orchestrationInput right = orchestrationInput left)
    {kind : Lifecycle} {actor removed : Name} (activation : left.event start = .lifecycle kind actor)
    (external : right.event (start + span) = .command (.remove removed))
    (block : ∀ cut, start ≤ cut → cut < start + span → ∃ kind actor, right.event cut = .lifecycle kind actor) :
    right.state start removed = none ∧
      ∃ birth, start ≤ birth ∧ birth < start + span ∧ (right.notes (start + span)).1 removed = some (birth + 1) := by
  have vacant : right.state start removed = none := by
    apply Classical.byContradiction
    intro present
    exact ready_command_precludes_frontier_activation left right leftBound rightBound leftNormal
      rightOpen rightQuiet current past input activation external block (fun absent => False.elim (present absent))
  obtain ⟨birth, _, _, bounded, _, tag, lives, _, _, _, _⟩ := right.retire_remove_birth rightBound (.inr external)
  have after : start ≤ birth := Nat.le_of_not_gt (fun earlier => lives.present start (by omega) (by omega) vacant)
  exact ⟨vacant, birth, after, bounded, tag⟩

private theorem quiet_disables_activation {rule : Labeled.Rule} {name : Name}
    {before after : Registry Name Key Value Code (Inverse Name Key Value) Error}
    (step : Labeled.Step program rule name before after) (activation : Transposition.Activation rule)
    (quiet : Progress.Quiet before) : False := by
  cases step with
  | begin _ _ row view found phase _ target =>
    have blocked := quiet _ row found
    rw [phase] at blocked
    exact blocked view target
  | iter _ _ _ row _ _ _ _ _ found phase _ _ | finish _ _ _ row _ _ _ _ found phase _ _ =>
    have blocked := quiet _ row found
    rwa [phase] at blocked
  | _ => simp [Transposition.Activation] at activation

/-- A matched endpoint is terminal in the other quiet open run. The
matched prefix has consumed the entire shared command word. Its projected
registry is already quiet, so there is no remaining activation. -/
theorem matched_endpoint_is_terminal {leftLength rightLength : Nat}
    (left : Trace program leftLength) (right : Trace program rightLength)
    (bounded : leftLength ≤ rightLength) (current : CutAgreement left right leftLength)
    (past : ∀ cut, cut < leftLength → addressedEventAt left cut = addressedEventAt right cut)
    (input : orchestrationInput left = orchestrationInput right)
    (leftQuiet : Progress.Quiet (left.state leftLength)) (rightQuiet : Progress.Quiet (right.state rightLength))
    (rightOpen : ¬ Nonempty (ClosedEpisode right)) : leftLength = rightLength := by
  refine Nat.le_antisymm bounded (Nat.le_of_not_gt ?_)
  intro later
  cases event : right.event leftLength with
  | command command =>
    have counts := matched_command_counts left right (Nat.le_refl _) bounded past
    have next := next_command_at_rank right (start := leftLength) (span := 0) later event (fun _ lower upper => by omega)
    rw [← counts, ← input] at next
    change (orchestrationInput left)[(orchestrationInput left).length]? = commandAt right leftLength at next
    have outside : (orchestrationInput left)[(orchestrationInput left).length]? = none :=
      List.getElem?_eq_none_iff.mpr (Nat.le_refl _)
    rw [outside] at next
    obtain ⟨_, _, impossible⟩ := (commandAt_none right later).mp next.symm
    rw [event] at impossible
    cases impossible
  | lifecycle kind name =>
    obtain ⟨p, registry, _, _⟩ := current
    have projected := GuardedCutState.project_quiet_iff _ |>.mpr leftQuiet
    have renamed := GuardedRenaming.quiet_transport p projected
    rw [registry] at renamed
    have settled := (GuardedCutState.project_quiet_iff _).mp renamed
    obtain ⟨activation, step⟩ := right.activation_at rightOpen rightQuiet later event
    exact quiet_disables_activation step activation settled

end Cordis.Repairs.GuardedCommandAlignment
