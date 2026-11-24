import Cordis.Repairs.GuardedOpenHistory
import Cordis.Repairs.GuardedReindex
import Cordis.Repairs.CommandBeforeActivation
import Cordis.Repairs.VestigialRestore

/-! Preserve actual guarded event payloads and annotations across an
adjacent root command exchange in an open-only history. -/
namespace Cordis.Repairs.GuardedHistory
open Calculus Stages LegalHistory
open Vestigial (CutNotes cutNotes eventActor)
open OrchestrationSorting (Command)
universe u
variable {Name Key Value Code Error : Type u} [DecidableEq Name] [DecidableEq Key]
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "Ev" => Event Name Key Code
local notation "Notes" => CutNotes Name Key Value
variable {program : Code → Stages.Instruction Name Key Value Code Error} {last : Nat}

/-- Recording a step preserves an actor's birth and component when that
actor is absent at both cuts or has the same component at both cuts. -/
theorem Trace.actorSource_next (trace : Trace program last) {time : Nat} (bounded : time < last) (event : Ev)
    (component : (trace.state (time + 1) (eventActor event)).map Fiber.component =
      (trace.state time (eventActor event)).map Fiber.component) :
    GuardedSuffix.actorSource (trace.state (time + 1)) (trace.notes (time + 1)) event =
      GuardedSuffix.actorSource (trace.state time) (trace.notes time) event := by
  let name := eventActor event
  have births := trace.births_agree time (Nat.le_of_lt bounded) name
  unfold GuardedSuffix.actorSource
  refine Prod.ext ?_ component
  change (trace.notes (time + 1)).1 name = (trace.notes time).1 name
  rw [(trace.step time bounded).2]
  change (trace.state (time + 1) name).map (fun _ => ((trace.notes time).1 name).getD (time + 1)) =
    (trace.notes time).1 name
  change (trace.state (time + 1) name).map Fiber.component = (trace.state time name).map Fiber.component at component
  cases old : trace.state time name <;> cases new : trace.state (time + 1) name <;>
    simp only [old, new, Option.map_none, Option.map_some, reduceCtorEq] at component births ⊢
  · exact (births.mpr True.intro).symm
  · cases tag : (trace.notes time).1 name with
    | none => simp [tag] at births
    | some stamp => rfl

theorem Trace.actorSource_across_activation (trace : Trace program last) {time : Nat} (bounded : time < last)
    {rule : Labeled.Rule} {actor : Name} (step : Labeled.Step program rule actor (trace.state time) (trace.state (time + 1)))
    (active : Transposition.Activation rule) (event : Ev) (different : eventActor event ≠ actor)
    {row : Fiber Name Key Value Code (Inverse Name Key Value) Error}
    (present : trace.state time (eventActor event) = some row) :
    GuardedSuffix.actorSource (trace.state (time + 1)) (trace.notes (time + 1)) event =
      GuardedSuffix.actorSource (trace.state time) (trace.notes time) event := by
  obtain ⟨table, kept⟩ := Transposition.activation_other_table program step active _ row different present
  exact trace.actorSource_next bounded event (by simp only [kept, present, Option.map_some])

private theorem activation_target_component {rule : Labeled.Rule} {actor name : Name} {before after : R}
    (step : Labeled.Step program rule actor before after) (active : Transposition.Activation rule)
    (different : name ≠ actor) (notCreated : before name = none → after name = none) :
    (after name).map Fiber.component = (before name).map Fiber.component := by
  cases found : before name with
  | none => rw [notCreated found]
  | some row =>
    obtain ⟨table, retained⟩ := Transposition.activation_other_table program step active name row different found
    rw [retained]
    rfl

private theorem command_target_absence {command : Command Name Key Code} {left right after final : R}
    (first : command.Step left after) (second : command.Step right final) :
    left command.actor = none ↔ right command.actor = none := by
  cases command with
  | insert => exact ⟨fun _ => second.1.1, fun _ => first.1.1⟩
  | retire => exact ⟨fun absent => False.elim (first.1 absent), fun absent => False.elim (second.1 absent)⟩
  | remove name => exact ⟨fun absent => False.elim (Transposition.removable_present _ name first.1 absent),
      fun absent => False.elim (Transposition.removable_present _ name second.1 absent)⟩

theorem Trace.agree_prefix {original moved : Trace program last} {time : Nat} (bounded : time ≤ last)
    (states : ∀ cut, cut ≤ time → moved.state cut = original.state cut)
    (labels : ∀ cut, cut < time → moved.event cut = original.event cut) (cut : Nat) (before : cut ≤ time) :
    moved.state cut = original.state cut ∧ moved.notes cut = original.notes cut := by
  refine ⟨states cut before, ?_⟩
  induction cut with
  | zero => rw [moved.seed, original.seed]
  | succ cut ih =>
    rw [(moved.step cut (by omega)).2, (original.step cut (by omega)).2, states cut (by omega),
      states (cut + 1) before, labels cut (by omega), ih (by omega)]

/-- The stamp correspondence for a justified adjacent exchange. The two
crossed cuts supply their own actor comparisons, and all other cuts use
the original prefix or the aligned replay. -/
theorem RetainedEvents.of_adjacent_exchange {original moved : Trace program last} {time : Nat}
    (bounded : time + 1 < last)
    (labels : ∀ i, i < last → moved.event i = if i = time then original.event (time + 1)
      else if i = time + 1 then original.event time else original.event i)
    (unchanged : ∀ i, i ≤ time → moved.state i = original.state i ∧ moved.notes i = original.notes i)
    (first : GuardedSuffix.actorSource (moved.state time) (moved.notes time) (moved.event time) =
      GuardedSuffix.actorSource (original.state (time + 1)) (original.notes (time + 1)) (original.event (time + 1)))
    (second : GuardedSuffix.actorSource (moved.state (time + 1)) (moved.notes (time + 1)) (moved.event (time + 1)) =
      GuardedSuffix.actorSource (original.state time) (original.notes time) (original.event time))
    (suffix : ∀ i, time + 2 ≤ i → i < last →
      GuardedSuffix.actorSource (moved.state i) (reindexNotes (ExchangeReplay.exchangedIndex time) (moved.notes i))
        (moved.event i) = GuardedSuffix.actorSource (original.state i) (original.notes i) (original.event i)) :
    RetainedEvents original moved (ExchangeReplay.exchangedIndex time) := by
  let stamp := ExchangeReplay.exchangedIndex time
  have fixed (trace : Trace program last) (i : Nat) (earlier : i ≤ time) :
      reindexNotes stamp (trace.notes i) = trace.notes i :=
    trace.reindexNotes_fixed (by omega) stamp (fun _ lower => ExchangeReplay.exchangedIndex_other (by omega) (by omega))
  refine ⟨ExchangeReplay.exchangedIndex_injective _, ?_, ?_, ?_⟩
  · intro i inside
    by_cases atFirst : i = time
    · subst i; simp [show time + 2 ≤ last by omega]
    by_cases atSecond : i = time + 1
    · subst i; simp [show time + 1 ≤ last by omega]
    · rw [ExchangeReplay.exchangedIndex_other (by omega) (by omega)]
      exact ⟨Nat.zero_lt_succ _, inside⟩
  · intro i inside
    by_cases atFirst : i = time
    · subst i; simpa using labels time (by omega)
    by_cases atSecond : i = time + 1
    · subst i; simpa using labels (time + 1) bounded
    · rw [ExchangeReplay.exchangedIndex_other (by omega) (by omega), Nat.add_sub_cancel]
      simpa only [if_neg atFirst, if_neg atSecond] using labels i inside
  · intro i inside
    by_cases atFirst : i = time
    · subst i
      rw [fixed moved _ (by omega)]
      simpa using first
    by_cases atSecond : i = time + 1
    · subst i
      rw [actorSource_reindex, second, ← actorSource_reindex, fixed original _ (by omega)]
      simp
    · rw [ExchangeReplay.exchangedIndex_other (by omega) (by omega), Nat.add_sub_cancel]
      by_cases before : i ≤ time
      · rw [fixed moved _ before, (unchanged i before).1, (unchanged i before).2]
        rw [show moved.event i = original.event i by simpa [atFirst, atSecond] using labels i inside]
      · exact suffix i (by omega) inside

private def nonRootAt (trace : Trace program last) (cut : Nat) : List Ev :=
  if (eventRoots (trace.state cut) (trace.event cut)).isEmpty then [trace.event cut] else []

/-- Lifecycle events and commands acting on children, in execution order. -/
def nonRootEvents (trace : Trace program last) : List Ev :=
  (List.range last).flatMap (nonRootAt trace)

/-- An adjacent command exchange preserves the endpoint and all root payloads.
The event stamps and the per-cut root projections follow the exchanged events. -/
structure CommandEarlierExchange (source moved : Trace program last) (time : Nat) : Prop where
  event : moved.event = fun cut => if cut = time then source.event (time + 1)
    else if cut = time + 1 then source.event time else source.event cut
  state : ∀ cut, cut ≠ time + 1 → moved.state cut = source.state cut
  notes : ∀ cut, time + 2 ≤ cut → cut ≤ last →
    moved.notes cut = reindexNotes (ExchangeReplay.exchangedIndex time) (source.notes cut)
  firstRoot : eventRoots (moved.state time) (moved.event time) =
    eventRoots (source.state (time + 1)) (source.event (time + 1))
  secondRoot : eventRoots (moved.state (time + 1)) (moved.event (time + 1)) = []
  otherRoots : ∀ cut, cut ≠ time → cut ≠ time + 1 →
    eventRoots (moved.state cut) (moved.event cut) = eventRoots (source.state cut) (source.event cut)
  roots : originalRoots moved = originalRoots source
  nonRoots : eventRoots (source.state (time + 1)) (source.event (time + 1)) ≠ [] →
    nonRootEvents moved = nonRootEvents source
  openOnly : ¬ Nonempty (ClosedEpisode moved)
  quiet : Progress.Quiet (moved.state last)
  retained : RetainedEvents source moved (ExchangeReplay.exchangedIndex time)

theorem CommandEarlierExchange.prefix_eq {source moved : Trace program last} {time cut : Nat}
    (exchange : CommandEarlierExchange source moved time) (bounded : time ≤ last) (before : cut ≤ time) :
    moved.state cut = source.state cut ∧ moved.notes cut = source.notes cut :=
  Trace.agree_prefix bounded (fun i early => exchange.state i (by omega))
    (fun i early => by simp [exchange.event, show i ≠ time by omega, show i ≠ time + 1 by omega]) cut before

private theorem flatMap_pair {α : Type u} {time last : Nat} {source moved : Nat → List α}
    (bounded : time + 1 < last)
    (first : moved time = source (time + 1)) (second : moved (time + 1) = source time)
    (outside : ∀ cut, cut ≠ time → cut ≠ time + 1 → moved cut = source cut)
    (empty : source time = [] ∨ source (time + 1) = []) :
    (List.range last).flatMap moved = (List.range last).flatMap source := by
  have sameAt (indices : List Nat) (valid : ∀ cut ∈ indices, cut ≠ time ∧ cut ≠ time + 1) :
      indices.flatMap moved = indices.flatMap source := by
    rw [List.flatMap_def, List.flatMap_def]
    apply congrArg List.flatten
    apply List.map_congr_left
    intro cut member
    exact outside cut (valid cut member).1 (valid cut member).2
  have before := sameAt (List.range time) (by
    intro cut member
    have lower := List.mem_range.mp member
    omega)
  have after := sameAt (List.range' (time + 2) (last - (time + 2))) (by
    intro cut member
    obtain ⟨offset, _, placed⟩ := List.mem_range'.mp member
    have lower : time + 2 ≤ cut := by simp at placed; omega
    omega)
  rw [cut_range_pair bounded, List.flatMap_append, List.flatMap_append, before]
  rcases empty with earlier | later
  · simp [List.flatMap_cons, first, second, earlier, after]
  · simp [List.flatMap_cons, first, second, later, after]

private theorem Trace.exact_exchange (trace : Trace program last)
    (openOnly : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    {time : Nat} (bounded : time + 1 < last) (states : Nat → R)
    (stateOutside : ∀ cut, cut ≠ time + 1 → states cut = trace.state cut)
    (firstMoved : ∀ notes : Notes, GuardedSuffix.Transition program notes (trace.event (time + 1))
      (states time) (states (time + 1)))
    (secondMoved : ∀ notes : Notes, GuardedSuffix.Transition program notes (trace.event time)
      (states (time + 1)) (states (time + 2))) :
    ∃ result : Trace program last, result.state = states ∧
      result.event = (fun cut => if cut = time then trace.event (time + 1)
        else if cut = time + 1 then trace.event time else trace.event cut) ∧
      (¬ Nonempty (ClosedEpisode result)) ∧ Progress.Quiet (result.state last) := by
  let events (cut : Nat) := if cut = time then trace.event (time + 1)
    else if cut = time + 1 then trace.event time else trace.event cut
  let notes := cutNotes states (fun cut => eventActor (events cut))
  have initial : states 0 = fun _ => none := (stateOutside 0 (by omega)).trans trace.start
  have seed : notes 0 = (fun _ => none, fun _ => []) := by
    apply Prod.ext
    · funext name
      simp [notes, cutNotes, Incarnation.birthAt, initial]
    · rfl
  have movedStep (cut : Nat) (bound : cut < last) :
      GuardedSuffix.Transition program (notes cut) (events cut) (states cut) (states (cut + 1)) := by
    by_cases first : cut = time
    · subst cut
      simpa [events] using firstMoved (notes time)
    by_cases second : cut = time + 1
    · subst cut
      simpa [events] using secondMoved (notes (time + 1))
    rw [show events cut = trace.event cut by simp [events, first, second],
      stateOutside cut second, stateOutside (cut + 1) (by omega)]
    have original := (trace.step cut bound).1
    cases event : trace.event cut with
    | command =>
      rw [event] at original
      exact original
    | lifecycle kind actor =>
      rw [event] at original
      cases kind <;> first | exact original | exact False.elim (trace.no_unload openOnly bound event)
  let result : Trace program last :=
    ⟨states, notes, events, initial, seed, fun cut valid => ⟨movedStep cut valid, rfl⟩⟩
  refine ⟨result, rfl, rfl, ?_, ?_⟩
  · rintro ⟨closed⟩
    obtain ⟨unload, _⟩ := unload_boundary result closed.interval
    change events closed.closed = .lifecycle .unload closed.name at unload
    by_cases first : closed.closed = time
    · exact trace.no_unload openOnly bounded (by simpa [events, first] using unload)
    by_cases second : closed.closed = time + 1
    · exact trace.no_unload openOnly (time := time) (by omega) (by simpa [events, second] using unload)
    · exact trace.no_unload openOnly closed.interval.bounded (by simpa [events, first, second] using unload)
  · change Progress.Quiet (states last)
    rwa [stateOutside last (by omega)]

private theorem Trace.lift_command_exchange (trace : Trace program last)
    (openOnly : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    {time : Nat} (bounded : time + 1 < last) {command : Command Name Key Code}
    (commandEvent : trace.event (time + 1) = .command command)
    {indexed : Indexed.Trace program (fun _ => none) last}
    (exchange : ExchangeReplay.Exchange (trace.toIndexed openOnly) indexed time command)
    (secondMoved : ∀ notes : Notes, GuardedSuffix.Transition program notes (trace.event time)
      (indexed.state (time + 1)) (indexed.state (time + 2)))
    (firstTarget : (trace.state (time + 1) command.actor).map Fiber.component =
      (trace.state time command.actor).map Fiber.component)
    (secondTarget : (indexed.state (time + 1) (trace.actor time)).map Fiber.component =
      (trace.state time (trace.actor time)).map Fiber.component)
    (oldEmpty : eventRoots (trace.state time) (trace.event time) = [])
    (newEmpty : eventRoots (indexed.state (time + 1)) (trace.event time) = []) :
    ∃ moved : Trace program last, CommandEarlierExchange trace moved time := by
  obtain ⟨result, states, labels, resultOpen, resultQuiet⟩ :=
    trace.exact_exchange openOnly quiet bounded indexed.state exchange.state
      (fun notes => by rw [commandEvent]; exact exchange.commandStep) secondMoved
  have atFirst : result.event time = .command command := by simp [labels, commandEvent]
  have atSecond : result.event (time + 1) = trace.event time := by simp [labels]
  have outside (cut : Nat) (first : cut ≠ time) (second : cut ≠ time + 1) :
      result.event cut = trace.event cut := by simp [labels, first, second]
  have stateOutside (cut : Nat) (different : cut ≠ time + 1) : result.state cut = trace.state cut := by
    rw [states]
    exact exchange.state cut different
  have actorMatches : result.actor = indexed.actor := by
    funext cut
    unfold Trace.actor
    by_cases atTime : cut = time
    · subst cut
      rw [atFirst, exchange.first.2]
      rfl
    by_cases next : cut = time + 1
    · subst cut
      rw [atSecond, exchange.second.2]
      rfl
    · rw [outside cut atTime next, (exchange.label cut atTime next).2]
      rfl
  have firstRoot : eventRoots (result.state time) (result.event time) =
      eventRoots (trace.state (time + 1)) (trace.event (time + 1)) := by
    rw [states, atFirst, commandEvent]
    exact exchange.root
  have secondRoot : eventRoots (result.state (time + 1)) (result.event (time + 1)) = [] := by
    simpa only [states, atSecond] using newEmpty
  have otherRoots (cut : Nat) (first : cut ≠ time) (second : cut ≠ time + 1) :
      eventRoots (result.state cut) (result.event cut) = eventRoots (trace.state cut) (trace.event cut) := by
    rw [outside cut first second, stateOutside cut second]
  have notesAfter (cut : Nat) (later : time + 2 ≤ cut) (permitted : cut ≤ last) :
      result.notes cut = reindexNotes (ExchangeReplay.exchangedIndex time) (trace.notes cut) := by
    rw [trace.notes_eq cut permitted, result.notes_eq cut permitted, states, actorMatches]
    apply Prod.ext
    · exact funext (exchange.birth cut later)
    · exact funext (exchange.word cut later)
  have unchanged := Trace.agree_prefix (by omega : time ≤ last)
    (fun cut (earlier : cut ≤ time) => stateOutside cut (by omega))
    (fun cut (earlier : cut < time) => outside cut (by omega) (by omega))
  have retained : RetainedEvents trace result (ExchangeReplay.exchangedIndex time) := by
    refine RetainedEvents.of_adjacent_exchange bounded (fun cut _ => congrFun labels cut) unchanged ?_ ?_ ?_
    · rw [atFirst, ← commandEvent, (unchanged time (Nat.le_refl _)).1, (unchanged time (Nat.le_refl _)).2]
      exact (trace.actorSource_next (by omega) _ (by simpa [commandEvent, eventActor] using firstTarget)).symm
    · rw [atSecond, ← (unchanged time (Nat.le_refl _)).1, ← (unchanged time (Nat.le_refl _)).2]
      exact result.actorSource_next (by omega) _ (by simpa only [states, exchange.state time (by omega), Trace.actor] using secondTarget)
    · intro cut later valid
      rw [outside cut (by omega) (by omega), stateOutside cut (by omega), notesAfter cut later (Nat.le_of_lt valid),
        reindexNotes_involutive _ (ExchangeReplay.exchangedIndex_involutive time)]
  refine ⟨result, labels, stateOutside, notesAfter, firstRoot, secondRoot, otherRoots, ?_, ?_, resultOpen,
    resultQuiet, retained⟩
  · unfold originalRoots
    exact flatMap_pair bounded firstRoot (secondRoot.trans oldEmpty.symm) otherRoots (Or.inl oldEmpty)
  · intro classified
    have root : commandRoots (trace.state (time + 1)) command ≠ [] := by
      simpa only [commandEvent, eventRoots] using classified
    have lateRoot : nonRootAt trace (time + 1) = [] := by
      simp [nonRootAt, commandEvent, eventRoots, List.isEmpty_iff, root]
    apply flatMap_pair bounded ?_ ?_ ?_ (Or.inr lateRoot)
    · rw [lateRoot]
      unfold nonRootAt
      rw [firstRoot, commandEvent]
      simp [eventRoots, List.isEmpty_iff, root]
    · unfold nonRootAt
      rw [secondRoot, oldEmpty, atSecond]
    · intro cut different next
      unfold nonRootAt
      rw [otherRoots cut different next, outside cut different next]

private theorem Trace.lift_activation_exchange (trace : Trace program last)
    (openOnly : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    {time : Nat} (bounded : time + 1 < last) {kind : Lifecycle} {actor : Name}
    (activationEvent : trace.event time = .lifecycle kind actor)
    {command : Command Name Key Code}
    (commandEvent : trace.event (time + 1) = .command command)
    {indexed : Indexed.Trace program (fun _ => none) last}
    (exchange : ExchangeReplay.Exchange (trace.toIndexed openOnly) indexed time command) :
    ∃ moved : Trace program last, CommandEarlierExchange trace moved time := by
  have ordinary : kind ≠ .unload := by
    intro same
    subst kind
    exact trace.no_unload openOnly (by omega) activationEvent
  obtain ⟨active, original⟩ := trace.activation_at openOnly quiet (by omega) activationEvent
  have commandLater : command.Step (trace.state (time + 1)) (trace.state (time + 2)) := by
    have step := (trace.step (time + 1) bounded).1
    rwa [commandEvent] at step
  have commandEarlier : command.Step (trace.state time) (indexed.state (time + 1)) := by
    simpa only [exchange.state time (by omega)] using exchange.commandStep
  have distinct : command.actor ≠ actor := by
    intro equal
    exact activation_installs_view original active (equal ▸ trace.command_actor_inactive openOnly quiet bounded commandEvent)
  refine trace.lift_command_exchange openOnly quiet bounded commandEvent exchange ?_ ?_ ?_ ?_ ?_
  · intro notes
    rw [activationEvent]
    apply lifecycle_transition ordinary
    have step := indexed.step (time + 1) bounded
    rw [exchange.second.1, exchange.second.2] at step
    have label : (trace.toIndexed openOnly).rule time = kind.rule := by
      simp [Trace.toIndexed, Trace.rule, activationEvent, eventRule]
    have name : (trace.toIndexed openOnly).actor time = actor := by
      simp [Trace.toIndexed, Trace.actor, activationEvent, eventActor]
    rwa [label, name] at step
  · exact activation_target_component original active distinct (command_target_absence commandEarlier commandLater).mp
  · have same := CausalCommands.apply_other command (trace.state time) actor distinct.symm
    rw [commandEarlier.2, Trace.actor, activationEvent]
    exact congrArg (Option.map Fiber.component) same
  all_goals simp [activationEvent, eventRoots]

/-- A subsequent command crosses the activation in the guarded history
exactly when the activation does not create the command's target. -/
theorem Trace.command_crosses_activation_iff (trace : Trace program last)
    (openOnly : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    {time : Nat} (bounded : time + 1 < last) {kind : Lifecycle} {actor : Name}
    (activationEvent : trace.event time = .lifecycle kind actor)
    {command : Command Name Key Code}
    (commandEvent : trace.event (time + 1) = .command command) :
    (∃ moved : Trace program last, CommandEarlierExchange trace moved time) ↔
      (trace.state time command.actor = none → trace.state (time + 1) command.actor = none) := by
  constructor
  · rintro ⟨moved, exchange⟩ absent
    have atEarlier : moved.event time = .command command := by simp [exchange.event, commandEvent]
    have earlier := (moved.step time (by omega)).1
    rw [atEarlier, exchange.state time (by omega)] at earlier
    change command.Step (trace.state time) (moved.state (time + 1)) at earlier
    cases command with
    | insert =>
      have later := (trace.step (time + 1) bounded).1
      rw [commandEvent] at later
      exact later.1.1
    | retire => exact False.elim (earlier.1 absent)
    | remove name => exact False.elim (Transposition.removable_present _ name earlier.1 absent)
  · intro notCreated
    obtain ⟨moved, exchange⟩ :=
      trace.exchange_command_after_activation openOnly quiet bounded activationEvent command commandEvent notCreated
    exact trace.lift_activation_exchange openOnly quiet bounded activationEvent commandEvent exchange

/-- In a quiet history of open episodes, a root command can cross its
immediately preceding activation. -/
theorem Trace.root_crosses_activation (trace : Trace program last)
    (openOnly : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    {time : Nat} (bounded : time + 1 < last) {kind : Lifecycle} {actor : Name}
    (activationEvent : trace.event time = .lifecycle kind actor)
    (command : Command Name Key Code)
    (commandEvent : trace.event (time + 1) = .command command)
    (root : commandRoots (trace.state (time + 1)) command ≠ []) :
    ∃ moved : Trace program last, CommandEarlierExchange trace moved time := by
  obtain ⟨_, exchange⟩ :=
    trace.exchange_root_after_activation openOnly quiet bounded activationEvent command commandEvent root
  exact trace.lift_activation_exchange openOnly quiet bounded activationEvent commandEvent exchange

/-- In a quiet history of open episodes, an adjacent child and root command
exchange if the earlier cut satisfies the source-derived command guards. -/
theorem Trace.root_crosses_child (trace : Trace program last)
    (openOnly : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    {time : Nat} (bounded : time + 1 < last) {child root : Command Name Key Code}
    (childEvent : trace.event time = .command child)
    (rootEvent : trace.event (time + 1) = .command root)
    (childClass : commandRoots (trace.state time) child = [])
    (rootClass : commandRoots (trace.state (time + 1)) root ≠ [])
    (allowed : rootMayCrossChild child root (trace.state time)) :
    ∃ moved : Trace program last, CommandEarlierExchange trace moved time := by
  have childStep := (trace.step time (by omega)).1
  have rootStep := (trace.step (time + 1) bounded).1
  rw [childEvent] at childStep
  rw [rootEvent] at rootStep
  obtain ⟨middle, first, second⟩ :=
    (child_root_command_exchange child root childStep rootStep childClass rootClass).mpr allowed
  obtain ⟨indexed, exchange⟩ := ExchangeReplay.commands (trace.toIndexed openOnly) bounded child root
    (by simp [Trace.toIndexed, Trace.rule, childEvent, eventRule])
    (by simp [Trace.toIndexed, Trace.actor, childEvent, eventActor])
    ⟨by simp [Trace.toIndexed, Trace.rule, rootEvent, eventRule],
      by simp [Trace.toIndexed, Trace.actor, rootEvent, eventActor]⟩
    childStep rootStep allowed.1 first.1
  refine trace.lift_command_exchange openOnly quiet bounded rootEvent exchange ?_ ?_ ?_ ?_ ?_
  · intro notes
    rw [childEvent, exchange.middle, exchange.state (time + 2) (by omega)]
    change child.Step (root.apply (trace.state time)) (trace.state (time + 2))
    rw [← first.2]
    exact second
  · rw [childStep.2, CausalCommands.apply_other child _ root.actor allowed.1.symm]
  · rw [Trace.actor, childEvent, exchange.middle]
    change (root.apply (trace.state time) child.actor).map Fiber.component = _
    rw [CausalCommands.apply_other root _ child.actor allowed.1]
    rfl
  · simpa [childEvent, eventRoots] using childClass
  · rw [childEvent, exchange.middle]
    change commandRoots (root.apply (trace.state time)) child = []
    rw [commandRoots_same_row child (CausalCommands.apply_other root _ child.actor allowed.1)]
    exact childClass

/-- The guards are also necessary for exchanging the pair in its actual
guarded history, with the surrounding cuts fixed. -/
theorem Trace.root_crosses_child_iff (trace : Trace program last)
    (openOnly : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    {time : Nat} (bounded : time + 1 < last) {child root : Command Name Key Code}
    (childEvent : trace.event time = .command child)
    (rootEvent : trace.event (time + 1) = .command root)
    (childClass : commandRoots (trace.state time) child = [])
    (rootClass : commandRoots (trace.state (time + 1)) root ≠ []) :
    (∃ moved : Trace program last, CommandEarlierExchange trace moved time) ↔
      rootMayCrossChild child root (trace.state time) := by
  refine ⟨?_, trace.root_crosses_child openOnly quiet bounded childEvent rootEvent childClass rootClass⟩
  rintro ⟨moved, exchange⟩
  have childStep := (trace.step time (by omega)).1
  have rootStep := (trace.step (time + 1) bounded).1
  rw [childEvent] at childStep
  rw [rootEvent] at rootStep
  have earlier := (moved.step time (by omega)).1
  have later := (moved.step (time + 1) bounded).1
  have earlierEvent : moved.event time = .command root := by simp [exchange.event, rootEvent]
  have laterEvent : moved.event (time + 1) = .command child := by simp [exchange.event, childEvent]
  rw [earlierEvent, exchange.state time (by omega)] at earlier
  rw [laterEvent, exchange.state (time + 2) (by omega)] at later
  exact (child_root_command_exchange child root childStep rootStep childClass rootClass).mp ⟨_, earlier, later⟩

/-- In an actual removal–activation pair the activation can cross the
removal exactly when its births still work with the removed row present.
The row must remain removable immediately after the exchanged activation. -/
theorem Trace.activation_crosses_removal_iff (trace : Trace program last)
    (openOnly : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    {time : Nat} (bounded : time + 1 < last) {removed actor : Name} {kind : Lifecycle}
    (removal : trace.event time = .command (.remove removed))
    (activation : trace.event (time + 1) = .lifecycle kind actor) :
    (∃ middle, Labeled.Step program kind.rule actor (trace.state time) middle ∧
      (Command.remove (Key := Key) (Code := Code) removed).Step middle (trace.state (time + 2))) ↔
      Vestigial.CompatibleBirths (trace.state time) (trace.state (time + 2)) removed := by
  have command := (trace.step time (by omega)).1
  rw [removal] at command
  have removedAt : trace.state (time + 1) = erase (trace.state time) removed := command.2
  have ready : Removable (trace.state time) removed := command.1
  obtain ⟨active, step⟩ := trace.activation_at openOnly quiet bounded activation
  have different : actor ≠ removed := by
    intro same
    subst actor
    obtain ⟨_, _, found, _, _⟩ := Transposition.activation_source program step active
    rw [removedAt, erase] at found
    simp at found
  rw [removedAt] at step
  have reached := (trace.toIndexed openOnly).prefixRun time (by omega)
  have disjoint := (WellFormed.run_invariants program reached Safety.empty_parentClosed WellFormed.disjoint_empty
    ⟨Ordering.supported_empty, Ordering.local_empty⟩).2.1
  constructor
  · rintro ⟨middle, early, late⟩
    exact ((Vestigial.event_restore_iff (event := .lifecycle kind actor) step different ready disjoint).mp
      ⟨middle, early, late.2.symm⟩).1
  · intro births
    obtain ⟨middle, early, ends⟩ := Vestigial.lifecycle_restore kind step different ready births
    exact ⟨middle, early, (Vestigial.lifecycle_erase kind early different ready).1, ends.symm⟩

/-- The only command conditions for doing a subsequent activation earlier. -/
def commandMayFollowActivation (command : Command Name Key Code) (actor : Name) (before after : R) : Prop :=
  match command with
  | .insert name _ => actor ≠ name
  | .retire _ => True
  | .remove name => Vestigial.CompatibleBirths before after name

/-- Determine the ability to move an activation before the preceding
command from the actual pair, including the concrete birth reservations. -/
theorem Trace.activation_crosses_command_iff (trace : Trace program last)
    (openOnly : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    {time : Nat} (bounded : time + 1 < last) {command : Command Name Key Code} {actor : Name} {kind : Lifecycle}
    (commandEvent : trace.event time = .command command)
    (activation : trace.event (time + 1) = .lifecycle kind actor) :
    (∃ middle, Labeled.Step program kind.rule actor (trace.state time) middle ∧
      command.Step middle (trace.state (time + 2))) ↔
      commandMayFollowActivation command actor (trace.state time) (trace.state (time + 2)) := by
  have commandStep := (trace.step time (by omega)).1
  rw [commandEvent] at commandStep
  change command.Step (trace.state time) (trace.state (time + 1)) at commandStep
  obtain ⟨active, step⟩ := trace.activation_at openOnly quiet bounded activation
  cases command with
  | remove name =>
    exact trace.activation_crosses_removal_iff openOnly quiet bounded commandEvent activation
  | insert name component =>
    have vacant : trace.state time name = none := commandStep.1.1
    constructor
    · rintro ⟨_, early, _⟩ same
      subst name
      obtain ⟨_, _, present, _, _⟩ := Transposition.activation_source program early active
      rw [vacant] at present
      cases present
    · intro different
      have reached := (trace.toIndexed openOnly).prefixRun (time + 2) (by omega)
      have disjoint := (WellFormed.run_invariants program reached Safety.empty_parentClosed WellFormed.disjoint_empty
        ⟨Ordering.supported_empty, Ordering.local_empty⟩).2.1
      rw [commandStep.2] at step
      exact CausalCommands.activation_before_insert component commandStep.1 step active different
        (trace.parent_closed time (by omega)) disjoint
  | retire name =>
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    have beforePresent : trace.state time name ≠ none := commandStep.1
    rw [commandStep.2] at step
    have distinct : actor ≠ name := by
      intro same
      subst actor
      obtain ⟨row, view, present, _, target⟩ := Transposition.activation_source program step active
      have found : trace.state time name ≠ none := beforePresent
      cases original : trace.state time name with
      | none => exact found original
      | some entry =>
        have equality : {entry with retired := true} = row := Option.some.inj
          (by simpa [OrchestrationSorting.Command.apply, Calculus.retire, Calculus.modify, original] using present)
        simp only [Target, present] at target
        simpa [← equality] using target.1
    exact CausalCommands.activation_before_retire step active distinct beforePresent

/-- Perform the checked command–activation exchange throughout the guarded
history. The command keeps its payload and root classification, and each
later birth and capture follows the inverse stamp permutation. -/
theorem Trace.swap_activation_before_command (trace : Trace program last)
    (openOnly : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    {time : Nat} (bounded : time + 1 < last) {command : Command Name Key Code} {actor : Name} {kind : Lifecycle}
    (commandEvent : trace.event time = .command command)
    (activation : trace.event (time + 1) = .lifecycle kind actor)
    (allowed : commandMayFollowActivation command actor (trace.state time) (trace.state (time + 2))) :
    ∃ moved : Trace program last,
      moved.event = (fun cut => if cut = time then trace.event (time + 1)
        else if cut = time + 1 then trace.event time else trace.event cut) ∧
      (∀ cut, cut ≠ time + 1 → moved.state cut = trace.state cut) ∧
      (∀ cut, time + 2 ≤ cut → cut ≤ last →
        trace.notes cut = reindexNotes (ExchangeReplay.exchangedIndex time) (moved.notes cut)) ∧
      commandRoots (moved.state (time + 1)) command = commandRoots (trace.state time) command ∧
      originalRoots moved = originalRoots trace ∧
      (¬ Nonempty (ClosedEpisode moved)) ∧ Progress.Quiet (moved.state last) ∧
      RetainedEvents trace moved (ExchangeReplay.exchangedIndex time) := by
  obtain ⟨middle, earlier, later⟩ :=
    (trace.activation_crosses_command_iff openOnly quiet bounded commandEvent activation).mpr allowed
  let states (cut : Nat) := if cut = time + 1 then middle else trace.state cut
  have ordinary : kind ≠ .unload := by
    intro same
    subst kind
    exact trace.no_unload openOnly bounded activation
  have outside (cut : Nat) (different : cut ≠ time + 1) : states cut = trace.state cut := by
    simp [states, different]
  have atMiddle : states (time + 1) = middle := by simp [states]
  obtain ⟨moved, stateEq, events, stillOpen, stillQuiet⟩ :=
    trace.exact_exchange openOnly quiet bounded states outside
      (fun notes => by
        rw [activation, outside time (by omega), atMiddle]
        exact lifecycle_transition ordinary earlier)
      (fun notes => by
        rw [commandEvent, atMiddle, outside (time + 2) (by omega)]
        exact later)
  have swappedFirst : moved.event time = .lifecycle kind actor := by simp [events, activation]
  have swappedSecond : moved.event (time + 1) = .command command := by simp [events, commandEvent]
  have kept (cut : Nat) (different : cut ≠ time + 1) : moved.state cut = trace.state cut := by rw [stateEq, outside cut different]
  have differs (cut : Nat) (first : cut ≠ time) (second : cut ≠ time + 1) :
      moved.event cut = trace.event cut := by simp [events, first, second]
  have commandEarly := (trace.step time (by omega)).1
  rw [commandEvent] at commandEarly
  change command.Step (trace.state time) (trace.state (time + 1)) at commandEarly
  obtain ⟨active, firstStep⟩ := moved.activation_at stillOpen stillQuiet (by omega) swappedFirst
  have different : actor ≠ command.actor := by
    have installed := activation_installs_view firstStep active
    have inactive := moved.command_actor_inactive stillOpen stillQuiet bounded swappedSecond
    exact fun same => installed (same.symm ▸ inactive)
  have commandMoved := (moved.step (time + 1) bounded).1
  rw [swappedSecond] at commandMoved
  change command.Step (moved.state (time + 1)) (moved.state (time + 2)) at commandMoved
  have notCreated (absent : moved.state time command.actor = none) :
      moved.state (time + 1) command.actor = none := by
    rw [kept time (by omega)] at absent
    cases command with
    | insert => exact commandMoved.1.1
    | retire => exact False.elim (commandEarly.1 absent)
    | remove name => exact False.elim (Transposition.removable_present _ name commandEarly.1 absent)
  obtain ⟨returned, swapBack⟩ :=
    ExchangeReplay.activation_command (moved.toIndexed stillOpen) bounded command
      (by simpa [Trace.toIndexed, Trace.rule, swappedFirst, eventRule] using active)
      ⟨by simp [Trace.toIndexed, Trace.rule, swappedSecond, eventRule],
        by simp [Trace.toIndexed, Trace.actor, swappedSecond, eventActor]⟩
      commandMoved (by simpa [Trace.toIndexed, Trace.actor, swappedFirst, eventActor] using different) notCreated
  have recoveredStates : returned.state = trace.state := by
    funext cut
    by_cases next : cut = time + 1
    · subst cut
      rw [swapBack.middle]
      change command.apply (moved.state time) = trace.state (time + 1)
      rw [kept time (by omega)]
      exact commandEarly.2.symm
    · exact (swapBack.state cut next).trans (kept cut next)
  have recoveredActors : returned.actor = trace.actor := by
    funext cut
    by_cases first : cut = time
    · subst cut
      rw [swapBack.first.2]
      simp [Trace.actor, commandEvent, eventActor]
    by_cases second : cut = time + 1
    · subst cut
      rw [swapBack.second.2]
      simp [Trace.toIndexed, Trace.actor, swappedFirst, activation, eventActor]
    · rw [(swapBack.label cut first second).2]
      change eventActor (moved.event cut) = eventActor (trace.event cut)
      rw [differs cut first second]
  have sameRoots : commandRoots (moved.state (time + 1)) command = commandRoots (trace.state time) command :=
    ((congrArg (fun registry => commandRoots registry command) (congrFun recoveredStates time)).symm.trans swapBack.root).symm
  have notesAfter (cut : Nat) (afterPair : time + 2 ≤ cut) (valid : cut ≤ last) :
      trace.notes cut = reindexNotes (ExchangeReplay.exchangedIndex time) (moved.notes cut) := by
    have births := swapBack.birth cut afterPair
    have words := swapBack.word cut afterPair
    rw [recoveredStates] at births words
    rw [recoveredActors] at words
    rw [trace.notes_eq cut valid, moved.notes_eq cut valid]
    exact Prod.ext (funext births) (funext words)
  have unchanged := Trace.agree_prefix (by omega : time ≤ last)
    (fun cut (earlier : cut ≤ time) => kept cut (by omega))
    (fun cut (earlier : cut < time) => differs cut (by omega) (by omega))
  have retained : RetainedEvents trace moved (ExchangeReplay.exchangedIndex time) := by
    refine RetainedEvents.of_adjacent_exchange bounded (fun cut _ => congrFun events cut) unchanged ?_ ?_ ?_
    · rw [swappedFirst, ← activation, (unchanged time (Nat.le_refl _)).1, (unchanged time (Nat.le_refl _)).2]
      apply Eq.symm
      apply trace.actorSource_next (by omega)
      rw [activation, eventActor, commandEarly.2, CausalCommands.apply_other _ _ _ different]
    · rw [swappedSecond, ← commandEvent, ← (unchanged time (Nat.le_refl _)).1, ← (unchanged time (Nat.le_refl _)).2]
      apply moved.actorSource_next (by omega)
      rw [commandEvent, eventActor]
      exact activation_target_component firstStep active different.symm notCreated
    · intro cut later valid
      rw [differs cut (by omega) (by omega), kept cut (by omega), ← notesAfter cut later (Nat.le_of_lt valid)]
  refine ⟨moved, events, kept, notesAfter, sameRoots, ?_, stillOpen, stillQuiet, retained⟩
  unfold originalRoots
  refine flatMap_pair bounded ?_ ?_ ?_ (Or.inr (by simp [activation, eventRoots]))
  · simp [swappedFirst, activation, eventRoots]
  · simpa only [swappedSecond, commandEvent, eventRoots] using sameRoots
  · intro cut first second
    rw [differs cut first second, kept cut second]

/-- The adjacent activation exchange can be used again as a guarded source. -/
theorem Trace.swap_root_after_activation (trace : Trace program last)
    (openOnly : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    {time : Nat} (bounded : time + 1 < last) {kind : Lifecycle} {actor : Name}
    (activationEvent : trace.event time = .lifecycle kind actor)
    (command : Command Name Key Code)
    (commandEvent : trace.event (time + 1) = .command command)
    (root : commandRoots (trace.state (time + 1)) command ≠ []) :
    let events := fun cut => if cut = time then trace.event (time + 1)
      else if cut = time + 1 then trace.event time else trace.event cut
    ∃ moved : Trace program last, moved.event = events ∧
      (∀ cut, cut ≠ time + 1 → moved.state cut = trace.state cut) ∧
      (∀ cut, time + 2 ≤ cut → cut ≤ last →
        moved.notes cut = reindexNotes (ExchangeReplay.exchangedIndex time) (trace.notes cut)) ∧
      originalRoots moved = originalRoots trace ∧
      (¬ Nonempty (ClosedEpisode moved)) ∧ Progress.Quiet (moved.state last) := by
  obtain ⟨moved, exchange⟩ :=
    trace.root_crosses_activation openOnly quiet bounded activationEvent command commandEvent root
  exact ⟨moved, exchange.event, exchange.state, exchange.notes, exchange.roots, exchange.openOnly, exchange.quiet⟩

private def rootPositionSum (trace : Trace program last) : Nat :=
  ((List.range last).map fun cut => cut * (eventRoots (trace.state cut) (trace.event cut)).length).sum

private theorem CommandEarlierExchange.decreases {source moved : Trace program last} {time : Nat}
    (exchange : CommandEarlierExchange source moved time) (bounded : time + 1 < last)
    (earlier : eventRoots (source.state time) (source.event time) = [])
    {command : Command Name Key Code} (event : source.event (time + 1) = .command command)
    (root : commandRoots (source.state (time + 1)) command ≠ []) :
    rootPositionSum moved < rootPositionSum source := by
  have one : commandRoots (source.state (time + 1)) command = [command] := by
    cases command with
    | insert => rfl
    | retire name | remove name =>
      cases found : rootAt (source.state (time + 1)) name <;> simp_all [commandRoots]
  have later : eventRoots (source.state (time + 1)) (source.event (time + 1)) = [command] := by
    simpa [event, eventRoots] using one
  let positions (trace : Trace program last) (cut : Nat) :=
    cut * (eventRoots (trace.state cut) (trace.event cut)).length
  have before : (List.range time).map (positions moved) = (List.range time).map (positions source) := by
    apply List.map_congr_left
    intro cut member
    have lower := List.mem_range.mp member
    simp [positions, exchange.otherRoots cut (by omega) (by omega)]
  have after : (List.range' (time + 2) (last - (time + 2))).map (positions moved) =
      (List.range' (time + 2) (last - (time + 2))).map (positions source) := by
    apply List.map_congr_left
    intro cut member
    obtain ⟨offset, _, placed⟩ := List.mem_range'.mp member
    have lower : time + 2 ≤ cut := by simp at placed; omega
    simp [positions, exchange.otherRoots cut (by omega) (by omega)]
  change ((List.range last).map (positions moved)).sum < ((List.range last).map (positions source)).sum
  rw [cut_range_pair bounded]
  simp only [List.map_append, List.sum_append_nat, List.map_cons, List.sum_cons, before, after]
  simp only [positions, exchange.firstRoot, exchange.secondRoot, earlier, later, List.length_cons,
    List.length_nil, Nat.zero_add, Nat.mul_one, Nat.mul_zero]
  omega

/-- Every root command after the first cut follows either another root or
a child command that must precede it under the source's command guards. -/
def RootsAtBarriers (trace : Trace program last) : Prop :=
  ∀ time, time + 1 < last → ∀ root : Command Name Key Code,
    trace.event (time + 1) = .command root → commandRoots (trace.state (time + 1)) root ≠ [] →
    eventRoots (trace.state time) (trace.event time) ≠ [] ∨
      ∃ child : Command Name Key Code, trace.event time = .command child ∧
        commandRoots (trace.state time) child = [] ∧ ChildRemovalBarrier (trace.state time) child root

/-- Repeated adjacent exchanges move roots earlier in a quiet open history
until each root lies at the front, after another root, or at a command
barrier. The endpoint is identical and the root payloads remain in order. -/
theorem Trace.push_roots_to_barriers (trace : Trace program last)
    (openOnly : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last)) :
    ∃ moved : Trace program last, RootsAtBarriers moved ∧ originalRoots moved = originalRoots trace ∧
      nonRootEvents moved = nonRootEvents trace ∧ moved.state last = trace.state last ∧
      (¬ Nonempty (ClosedEpisode moved)) ∧
      Progress.Quiet (moved.state last) := by
  classical
  generalize measured : rootPositionSum trace = cost
  induction cost using Nat.strongRecOn generalizing trace with
  | ind cost ih =>
    by_cases available : ∃ time, ∃ bounded : time + 1 < last, ∃ root : Command Name Key Code,
        trace.event (time + 1) = .command root ∧ commandRoots (trace.state (time + 1)) root ≠ [] ∧
        eventRoots (trace.state time) (trace.event time) = [] ∧
        ((∃ kind actor, trace.event time = .lifecycle kind actor) ∨
          ∃ child : Command Name Key Code, trace.event time = .command child ∧
            rootMayCrossChild child root (trace.state time))
    · obtain ⟨time, bounded, root, event, rootClass, earlier, move⟩ := available
      have step : ∃ moved : Trace program last, CommandEarlierExchange trace moved time := by
        rcases move with ⟨kind, actor, activation⟩ | ⟨child, childEvent, allowed⟩
        · exact trace.root_crosses_activation openOnly quiet bounded activation root event rootClass
        · exact trace.root_crosses_child openOnly quiet bounded childEvent event
            (by simpa [childEvent, eventRoots] using earlier) rootClass allowed
      obtain ⟨moved, exchange⟩ := step
      have smaller := exchange.decreases bounded earlier event rootClass
      rw [measured] at smaller
      obtain ⟨result, sorted, roots, nonRoots, endpoint, finalOpen, finalQuiet⟩ :=
        ih _ smaller moved exchange.openOnly exchange.quiet rfl
      have rootEvent : eventRoots (trace.state (time + 1)) (trace.event (time + 1)) ≠ [] := by
        simpa only [event, eventRoots] using rootClass
      exact ⟨result, sorted, roots.trans exchange.roots, nonRoots.trans (exchange.nonRoots rootEvent),
        endpoint.trans (exchange.state last (by omega)), finalOpen, finalQuiet⟩
    · refine ⟨trace, ?_, rfl, rfl, rfl, openOnly, quiet⟩
      intro time bounded root rootEvent rootClass
      by_cases earlier : eventRoots (trace.state time) (trace.event time) = []
      · right
        cases event : trace.event time with
        | lifecycle kind actor =>
          exact False.elim (available ⟨time, bounded, root, rootEvent, rootClass, earlier,
            Or.inl ⟨kind, actor, event⟩⟩)
        | command child =>
          have childClass : commandRoots (trace.state time) child = [] := by
            simpa [event, eventRoots] using earlier
          refine ⟨child, rfl, childClass, ?_⟩
          have childStep := (trace.step time (by omega)).1
          have rootStep := (trace.step (time + 1) bounded).1
          rw [event] at childStep
          rw [rootEvent] at rootStep
          apply (child_root_barrier_iff child root childStep rootStep childClass rootClass).mp
          intro allowed
          exact available ⟨time, bounded, root, rootEvent, rootClass, earlier, Or.inr ⟨child, event, allowed⟩⟩
      · exact Or.inl earlier

end Cordis.Repairs.GuardedHistory
