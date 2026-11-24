import Cordis.Repairs.GuardedActivationExchange
import Cordis.Repairs.GuardedActivationOccurrence
import Cordis.Repairs.GuardedCommandAlignment
import Cordis.Repairs.GuardedReservationAlignment

/-! Synchronizing surviving activations across a block of other actors' stages. -/
namespace Cordis.Repairs.GuardedActivationAlignment
open Calculus Stages LegalHistory GuardedHistory GuardedBirthAddresses GuardedAddressSchedule
open GuardedScheduleMatching GuardedCommandAlignment
open GuardedActivationOccurrence (pending_activation_occurs)
open GuardedReservationAlignment (waiting_activation_crosses_removal_iff)
open GuardedBirthMatching (recorded_birth born_unique)
open GuardedLandingMatching (ChildContinuations matched_activation_kind)
open PaperEffectEquations (CoeffectOperations ValueOperationWitness)
open PaperObservationEquations (OperationRespects)
open PartialCoeffectIndependenceContracts (tableSetoid)
open TypedRegistry (encodeProgram Scalar)
open ExchangeReplay (exchangedIndex)
open OrchestrationSorting (Command)

universe u
variable {Name Key Code : Type u} {V : Key → Type u} {ops : CoeffectOperations V}
variable [DecidableEq Name] [DecidableEq Key]
variable {typedProgram : Code → TypedRegistry.Instruction Name ops Code} {last : Nat}
local notation "Source" => Trace (encodeProgram typedProgram) last
local notation "A" => Scalar ops

private theorem target_through_activations (trace : Source)
    (openOnly : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    {start span : Nat} (bounded : start + span ≤ last) {actor : Name} {view : View Name Key}
    (block : ∀ cut, start ≤ cut → cut < start + span →
      ∃ kind name, trace.event cut = .lifecycle kind name ∧ name ≠ actor)
    (ready : Target (trace.state start) actor view) : Target (trace.state (start + span)) actor view := by
  induction span with
  | zero => exact ready
  | succ span ih =>
    obtain ⟨kind, name, event, different⟩ := block (start + span) (by omega) (by omega)
    obtain ⟨active, step⟩ := trace.activation_at openOnly quiet (by omega) event
    exact Transposition.activation_target_forward (encodeProgram typedProgram) step active actor view different.symm
      (ih (by omega) (fun cut first before => block cut first (by omega)))

/-- A sequence of legal swaps of adjacent activations by distinct actors,
with the composed event map and an endpoint proof at each exchange. -/
inductive ActivationExchangePath [Setoid A] : Source → Source → (Nat → Nat) → Prop
  | refl (trace : Source) : ActivationExchangePath trace trace id
  | step {before middle after : Source} {cut : Nat} {expand : Nat → Nat}
      {firstKind secondKind : Lifecycle} {first second : Name} :
      cut + 1 < last →
      before.event cut = .lifecycle firstKind first →
      before.event (cut + 1) = .lifecycle secondKind second → first ≠ second →
      (∀ i, i < last → middle.event i =
        if i = cut then before.event (cut + 1)
        else if i = cut + 1 then before.event cut else before.event i) →
      StableActorAddresses before middle (exchangedIndex cut) →
      StageSimulation.Related Eq (before.state last) (middle.state last) →
      ActivationExchangePath middle after expand →
      ActivationExchangePath before after (exchangedIndex cut ∘ expand)

theorem ActivationExchangePath.trans [Setoid A] {before middle after : Source} {first second : Nat → Nat}
    (earlierPath : ActivationExchangePath before middle first) (suffix : ActivationExchangePath middle after second) :
    ActivationExchangePath before after (first ∘ second) := by
  induction earlierPath with
  | refl => exact suffix
  | step bounded earlier later different order addresses endpoint _ ih =>
    exact .step bounded earlier later different order addresses endpoint (ih suffix)

/-- A path preserves recursive birth addresses and endpoint observations. -/
theorem ActivationExchangePath.preserves [Setoid A] {before after : Source} {expand : Nat → Nat}
    (path : ActivationExchangePath before after expand)
    (self : StageSimulation.Related Eq (after.state last) (after.state last)) :
    StableActorAddresses before after expand ∧ StageSimulation.Related Eq (before.state last) (after.state last) := by
  induction path with
  | refl trace => exact ⟨.refl trace, self⟩
  | step _ _ _ _ _ addresses endpoint _ ih =>
    obtain ⟨rest, final⟩ := ih self
    exact ⟨addresses.trans rest,
      StageSimulation.Related.trans (Q := Eq) (fun a b => a.trans b) endpoint final⟩

theorem ActivationExchangePath.input_eq [Setoid A] {before after : Source} {expand : Nat → Nat}
    (path : ActivationExchangePath before after expand) :
    orchestrationInput after = orchestrationInput before := by
  induction path with
  | refl => rfl
  | step bounded earlier _ _ _ addresses _ _ ih =>
    exact ih.trans (command_input_of_activation_exchange addresses bounded (.inl ⟨_, _, earlier⟩))

/-- Move an actual activation across a preceding block of other actors'
activations. For Begin the target at the destination cut suffices for every
swap. The full command list and the addressed event are preserved. -/
theorem pull_activation_through_activations_with_path (trace : Source)
    (openOnly : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    {start span : Nat} (bounded : start + span < last) {kind : Lifecycle} {actor : Name}
    (event : trace.event (start + span) = .lifecycle kind actor)
    (block : ∀ cut, start ≤ cut → cut < start + span →
      ∃ earlier name, trace.event cut = .lifecycle earlier name ∧ name ≠ actor)
    (enabled : kind = .begin → ∃ view, Target (trace.state start) actor view)
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r) :
    letI : Setoid A := TypedCoeffectReplay.setoid observe
    ∃ (moved : Source) (expand : Nat → Nat),
      StableActorAddresses trace moved expand ∧
      (∀ stamp, stamp ≤ start → expand stamp = stamp) ∧
      (∀ cut, cut ≤ start → moved.state cut = trace.state cut ∧ moved.notes cut = trace.notes cut) ∧
      moved.event start = .lifecycle kind actor ∧
      addressedEventAt moved start = addressedEventAt trace (start + span) ∧
      orchestrationInput moved = orchestrationInput trace ∧
      StageSimulation.Related Eq (trace.state last) (moved.state last) ∧
      (¬ Nonempty (ClosedEpisode moved)) ∧ Progress.Quiet (moved.state last) ∧ ActivationExchangePath trace moved expand := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  induction span generalizing trace with
  | zero =>
    exact ⟨trace, id, .refl trace, fun _ _ => rfl, fun _ _ => ⟨rfl, rfl⟩, event, rfl, rfl,
      trace.self_related last (Nat.le_refl _)
        (TypedRegistry.encoded_program_callbacks ops observe typedProgram recovery commutative), openOnly, quiet, .refl trace⟩
  | succ span ih =>
    let time := start + span
    have finite : time + 1 < last := bounded
    have second : trace.event (time + 1) = .lifecycle kind actor := event
    obtain ⟨earlier, name, first, different⟩ := block time (by omega) (by omega)
    have ready (begins : kind = .begin) : ∃ view, Target (trace.state time) actor view := by
      obtain ⟨view, target⟩ := enabled begins
      exact ⟨view, target_through_activations trace openOnly quiet (start := start) (span := span) (by omega)
        (fun cut lower upper => block cut lower (by omega)) target⟩
    obtain ⟨mid, prefixEq, labels, _, suffix, retained, _, midOpen, midQuiet⟩ :=
      trace.swap_activations openOnly quiet finite first second different ready observe recovery commutative respect
    have stable : StableActorAddresses trace mid (exchangedIndex time) := by
      apply StableActorAddresses.adjacent finite retained
      · simp [isRootInsertion, first]
      · intro _ _
        simpa [Trace.actor, Vestigial.eventActor, first, second] using different
    have now : mid.event time = .lifecycle kind actor := by
      simpa only [labels time (by omega), if_pos rfl] using event
    have midBlock (cut : Nat) (lower : start ≤ cut) (upper : cut < start + span) :
        ∃ earlier name, mid.event cut = .lifecycle earlier name ∧ name ≠ actor := by
      simpa only [labels cut (by omega), if_neg (show cut ≠ time by omega), if_neg (show cut ≠ time + 1 by omega)] using
        block cut lower (by omega : cut < start + (span + 1))
    have midEnabled (begins : kind = .begin) : ∃ view, Target (mid.state start) actor view := by
      rw [(prefixEq start (by omega)).1]
      exact enabled begins
    obtain ⟨moved, expand, kept, stamps, cuts, nextEvent, key, input, endpoint, finalOpen, finalQuiet, path⟩ :=
      ih mid midOpen midQuiet (by omega) now midBlock midEnabled
    refine ⟨moved, exchangedIndex time ∘ expand, stable.trans kept, ?_, ?_, nextEvent, ?_,
      input.trans (command_input_of_activation_exchange stable finite (.inl ⟨earlier, name, first⟩)),
      StageSimulation.Related.trans (Q := Eq) (fun a b => a.trans b)
        (suffix last (by omega) (Nat.le_refl _)).1 endpoint, finalOpen, finalQuiet,
      .step finite first second different labels stable
        (suffix last (by omega) (Nat.le_refl _)).1 path⟩
    · intro stamp before
      rw [Function.comp_apply, stamps stamp before]
      exact ExchangeReplay.exchangedIndex_other (by omega) (by omega)
    · intro cut before
      have initial := cuts cut before
      have middle := prefixEq cut (by omega)
      exact ⟨initial.1.trans middle.1, initial.2.trans middle.2⟩
    · exact key.trans (by simpa only [ExchangeReplay.exchangedIndex_first, Nat.add_sub_cancel] using
        stable_addressed_event stable (cut := time) (by omega : time < last))

theorem pull_activation_through_activations (trace : Source)
    (openOnly : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    {start span : Nat} (bounded : start + span < last) {kind : Lifecycle} {actor : Name}
    (event : trace.event (start + span) = .lifecycle kind actor)
    (block : ∀ cut, start ≤ cut → cut < start + span →
      ∃ earlier name, trace.event cut = .lifecycle earlier name ∧ name ≠ actor)
    (enabled : kind = .begin → ∃ view, Target (trace.state start) actor view)
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r) :
    letI : Setoid A := TypedCoeffectReplay.setoid observe
    ∃ (moved : Source) (expand : Nat → Nat),
      StableActorAddresses trace moved expand ∧
      (∀ stamp, stamp ≤ start → expand stamp = stamp) ∧
      (∀ cut, cut ≤ start → moved.state cut = trace.state cut ∧ moved.notes cut = trace.notes cut) ∧
      moved.event start = .lifecycle kind actor ∧
      addressedEventAt moved start = addressedEventAt trace (start + span) ∧
      orchestrationInput moved = orchestrationInput trace ∧
      StageSimulation.Related Eq (trace.state last) (moved.state last) ∧
      (¬ Nonempty (ClosedEpisode moved)) ∧ Progress.Quiet (moved.state last) := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  obtain ⟨moved, expand, addresses, stamps, cuts, selected, address, input, endpoint, opened, settled, _⟩ :=
    pull_activation_through_activations_with_path trace openOnly quiet bounded event block enabled
      observe recovery commutative respect
  exact ⟨moved, expand, addresses, stamps, cuts, selected, address, input, endpoint, opened, settled⟩

/-- An actor with a usable target at the starting cut can move its
first activation in a command-free block to that cut. The later
witness can be any activation of the actor in the block. -/
theorem pull_first_ready_activation (trace : Source)
    (opened : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    {start limit : Nat} (lower : start ≤ limit) (bounded : limit < last)
    {kind : Lifecycle} {actor : Name} {view : View Name Key}
    (later : trace.event limit = .lifecycle kind actor)
    (ready : Target (trace.state start) actor view)
    (block : ∀ i, start ≤ i → i < limit → ∃ label name, trace.event i = .lifecycle label name)
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r) :
    letI : Setoid A := TypedCoeffectReplay.setoid observe
    ∃ (moved : Source) (expand : Nat → Nat) (label : Lifecycle),
      moved.event start = .lifecycle label actor ∧
      (∀ i, i < start → addressedEventAt trace i = addressedEventAt moved i) ∧
      actorAddress moved start = actorAddress trace limit ∧
      orchestrationInput moved = orchestrationInput trace ∧
      StageSimulation.Related Eq (trace.state last) (moved.state last) ∧
      (¬ Nonempty (ClosedEpisode moved)) ∧ Progress.Quiet (moved.state last) ∧
      ActivationExchangePath trace moved expand := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  have first (time : Nat) (afterStart : start ≤ time)
      (existsStage : ∃ label, trace.event time = .lifecycle label actor) :
      ∃ cut label, start ≤ cut ∧ cut ≤ time ∧ trace.event cut = .lifecycle label actor ∧
        ∀ i, start ≤ i → i < cut → ∀ kind, trace.event i ≠ .lifecycle kind actor := by
    induction time using Nat.strongRecOn with
    | ind time ih =>
      by_cases prior : ∃ i label, start ≤ i ∧ i < time ∧ trace.event i = .lifecycle label actor
      · obtain ⟨i, label, lo, hi, event⟩ := prior
        obtain ⟨cut, kind, begin, before, step, earlier⟩ := ih i hi lo ⟨label, event⟩
        exact ⟨cut, kind, begin, by omega, step, earlier⟩
      · obtain ⟨label, event⟩ := existsStage
        exact ⟨time, label, afterStart, Nat.le_refl _, event, fun i lo hi kind step =>
          prior ⟨i, kind, lo, hi, step⟩⟩
  obtain ⟨cut, label, fromStart, before, step, noEarlier⟩ := first limit lower ⟨kind, later⟩
  have atCut : start + (cut - start) = cut := by omega
  have foreignBlock (i : Nat) (lo : start ≤ i) (hi : i < start + (cut - start)) :
      ∃ kind name, trace.event i = .lifecycle kind name ∧ name ≠ actor := by
    obtain ⟨kind, name, event⟩ := block i lo (by omega)
    exact ⟨kind, name, event, fun same => noEarlier i lo (by omega) kind (same ▸ event)⟩
  obtain ⟨moved, expand, retained, stamps, cuts, next, _, input, endpoint, openMoved, quietMoved, path⟩ :=
    pull_activation_through_activations_with_path trace opened quiet (span := cut - start) (by omega)
      (by simpa only [atCut] using step) foreignBlock (fun _ => ⟨view, ready⟩)
      observe recovery commutative respect
  refine ⟨moved, expand, label, next, ?_, ?_, input, endpoint, openMoved, quietMoved, path⟩
  · intro i before
    have same := stable_addressed_event retained (cut := i) (by omega : i < last)
    rw [stamps (i + 1) (by omega), Nat.add_sub_cancel] at same
    exact same.symm
  · have finalCut : start + (limit - start) = limit := by omega
    cases found : trace.state start actor with
    | none => simp [Target, found] at ready
    | some row =>
      obtain ⟨_, _, _, sameStamp⟩ := GuardedReservationAlignment.reservation_survives_activation_block trace
        (span := limit - start) (by omega) (fun i lo hi => block i lo (by omega)) found
      rw [finalCut] at sameStamp
      have originalActor : trace.actor limit = actor := by simp [Trace.actor, Vestigial.eventActor, later]
      have movedActor : moved.actor start = actor := by simp [Trace.actor, Vestigial.eventActor, next]
      have notes := (cuts start (Nat.le_refl _)).2
      rw [actorAddress, actorAddress, movedActor, originalActor, notes, sameStamp]
      cases stamp : (trace.notes start).1 actor with
      | none => rfl
      | some birth =>
        obtain ⟨address, known⟩ := exists_address trace (recorded_birth trace (by omega : start ≤ last) stamp).1
        have movedTag : (moved.notes start).1 (moved.actor start) = some birth := by
          rw [movedActor, notes, stamp]
        obtain ⟨peer, peerKnown⟩ := exists_address moved
          (recorded_birth moved (by omega : start ≤ last) movedTag).1
        have earlierKnown := retained.address (by omega : start < last) movedTag peerKnown
        have birthBound := (recorded_birth moved (by omega : start ≤ last) movedTag).2
        have sameAddress : address = peer := known.unique (by
          simpa only [stamps birth birthBound] using earlierKnown)
        subst peer
        exact ((addressOf_eq_some moved).mpr peerKnown).trans ((addressOf_eq_some trace).mpr known).symm

private theorem activation_address (trace : Source) {cut birth : Nat} {kind : Lifecycle} {actor : Name}
    (event : trace.event cut = .lifecycle kind actor) (tag : (trace.notes cut).1 actor = some birth)
    {path : Address} (address : Addressed trace birth path) :
    addressedEventAt trace cut = some (.lifecycle kind path) := by
  have actorEq : trace.actor cut = actor := by simp [Trace.actor, Vestigial.eventActor, event]
  have addressed := (actorAddress_eq_some trace).mpr ⟨birth, actorEq.symm ▸ tag, address⟩
  simp [addressedEventAt, event, addressed]

/-- A legal adjacent swap moving an activation one cut earlier. The
previous event can be a command or another actor's activation. -/
structure AdjacentActivationExchange [Setoid A] (before after : Source) (cut : Nat) : Prop where
  bounded : cut + 1 < last
  activation : ∃ kind name, before.event (cut + 1) = .lifecycle kind name
  events : ∀ i, i < last → after.event i =
    if i = cut then before.event (cut + 1) else if i = cut + 1 then before.event cut else before.event i
  addresses : StableActorAddresses before after (exchangedIndex cut)
  input : orchestrationInput after = orchestrationInput before
  endpoint : StageSimulation.Related Eq (before.state last) (after.state last)
  openOnly : ¬ Nonempty (ClosedEpisode after)
  quiet : Progress.Quiet (after.state last)

/-- Move a waiting activation by one event in the other schedule. Equal
surviving inputs and the matched prefix discharge the reservation guard.
The exception is an adjacent removal whose raw name the activation reuses. -/
theorem move_waiting_activation_one_step_with_exchange {leftLength rightLength start cut parentBirth : Nat}
    (left : Trace (encodeProgram typedProgram) leftLength) (right : Trace (encodeProgram typedProgram) rightLength)
    (leftBound : start < leftLength) (rightBound : cut + 1 < rightLength) (order : start ≤ cut)
    (leftOpen : ¬ Nonempty (ClosedEpisode left)) (leftQuiet : Progress.Quiet (left.state leftLength))
    (rightOpen : ¬ Nonempty (ClosedEpisode right)) (rightQuiet : Progress.Quiet (right.state rightLength))
    (current : CutAgreement left right start)
    (past : ∀ time, time < start → addressedEventAt left time = addressedEventAt right time)
    (input : orchestrationInput left = orchestrationInput right)
    {leftKind rightKind : Lifecycle} {actor other : Name} (leftEvent : left.event start = .lifecycle leftKind actor)
    (rightEvent : right.event (cut + 1) = .lifecycle rightKind other)
    (leftTag : (left.notes start).1 actor = some parentBirth) (rightTag : (right.notes start).1 other = some parentBirth)
    (laterTag : (right.notes (cut + 1)).1 other = some parentBirth)
    {path : Address} (leftPath : Addressed left parentBirth path) (rightPath : Addressed right parentBirth path)
    (waiting : (right.state (cut + 1) other).map Fiber.phase = (right.state start other).map Fiber.phase)
    (first : ∀ time, start ≤ time → time < cut + 1 → ∀ k, right.event time ≠ .lifecycle k other)
    (ready : ∃ view, Target (right.state cut) other view)
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r) :
    letI : Setoid A := TypedCoeffectReplay.setoid observe
    (∃ moved : Trace (encodeProgram typedProgram) rightLength,
      StableActorAddresses right moved (exchangedIndex cut) ∧
      (∀ i, i ≤ cut → moved.state i = right.state i ∧ moved.notes i = right.notes i) ∧
      (∀ i, i < cut → moved.event i = right.event i) ∧
      moved.event cut = .lifecycle rightKind other ∧
      orchestrationInput moved = orchestrationInput right ∧
      StageSimulation.Related Eq (right.state rightLength) (moved.state rightLength) ∧
      (¬ Nonempty (ClosedEpisode moved)) ∧ Progress.Quiet (moved.state rightLength) ∧ AdjacentActivationExchange right moved cut) ∨
    ∃ removed, right.event cut = .command (.remove removed) ∧ right.state (cut + 2) removed ≠ none := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  cases previous : right.event cut with
  | lifecycle kind name =>
    have different : name ≠ other := fun equal => first cut order (by omega) kind (equal ▸ previous)
    obtain ⟨moved, cuts, labels, _, suffix, retained, _, opened, settled⟩ := right.swap_activations rightOpen rightQuiet
      rightBound previous rightEvent different (fun _ => ready) observe recovery commutative respect
    have kept : StableActorAddresses right moved (exchangedIndex cut) := by
      apply StableActorAddresses.adjacent rightBound retained
      · simp [isRootInsertion, previous]
      · intro _ _
        simpa [Trace.actor, Vestigial.eventActor, previous, rightEvent] using different
    have commands := command_input_of_activation_exchange kept rightBound (.inl ⟨kind, name, previous⟩)
    have endpoint := (suffix rightLength (by omega) (Nat.le_refl _)).1
    exact .inl ⟨moved, kept, cuts,
      (fun i prior => by
        simpa only [if_neg (show i ≠ cut by omega), if_neg (show i ≠ cut + 1 by omega)] using labels i (by omega)),
      (by simpa only [if_pos rfl] using (labels cut (by omega)).trans (by simp [rightEvent])),
      commands, endpoint, opened, settled,
      ⟨rightBound, ⟨rightKind, other, rightEvent⟩, labels, kept, commands, endpoint, opened, settled⟩⟩
  | command cmd =>
    have swapCommand (allowed : commandMayFollowActivation cmd other (right.state cut) (right.state (cut + 2))) :
        ∃ moved : Trace (encodeProgram typedProgram) rightLength,
          StableActorAddresses right moved (exchangedIndex cut) ∧
          (∀ i, i ≤ cut → moved.state i = right.state i ∧ moved.notes i = right.notes i) ∧
          (∀ i, i < cut → moved.event i = right.event i) ∧ moved.event cut = .lifecycle rightKind other ∧
          orchestrationInput moved = orchestrationInput right ∧
          StageSimulation.Related Eq (right.state rightLength) (moved.state rightLength) ∧
          (¬ Nonempty (ClosedEpisode moved)) ∧ Progress.Quiet (moved.state rightLength) ∧ AdjacentActivationExchange right moved cut := by
      obtain ⟨moved, labels, states, _, _, _, opened, settled, retained⟩ := right.swap_activation_before_command rightOpen rightQuiet
        rightBound previous rightEvent allowed
      have kept : StableActorAddresses right moved (exchangedIndex cut) := by
        apply StableActorAddresses.adjacent rightBound retained
        · simp [isRootInsertion, rightEvent]
        · intro stage _
          cases cmd <;> simp [Trace.rule, previous, eventRule, ExchangeReplay.commandRule, EpisodeSelection.canBirth] at stage
      have earlier (i : Nat) (inside : i < cut) : moved.event i = right.event i := by
        simp [labels, show i ≠ cut by omega, show i ≠ cut + 1 by omega]
      have commands := command_input_of_activation_exchange kept rightBound (.inr ⟨rightKind, other, rightEvent⟩)
      have endpoint : StageSimulation.Related Eq (right.state rightLength) (moved.state rightLength) := by
        rw [states rightLength (by omega)]
        exact right.self_related rightLength (Nat.le_refl _)
          (TypedRegistry.encoded_program_callbacks ops observe typedProgram recovery commutative)
      exact ⟨moved, kept, Trace.agree_prefix (by omega) (fun i hi => states i (by omega)) earlier,
        earlier, by simp [labels, rightEvent], commands, endpoint, opened, settled,
        ⟨rightBound, ⟨rightKind, other, rightEvent⟩, fun i _ => congrFun labels i,
          kept, commands, endpoint, opened, settled⟩⟩
    cases cmd with
    | retire => exact .inl (swapCommand trivial)
    | insert name component =>
      left
      apply swapCommand
      intro equal
      subst name
      have step := (right.step cut (by omega : cut < rightLength)).1
      rw [previous] at step
      have absent : right.state cut other = none := step.1.1
      obtain ⟨view, target⟩ := ready
      simp [Target, absent] at target
    | remove removed =>
      by_cases vacant : right.state (cut + 2) removed = none
      · exact .inl (swapCommand ((waiting_activation_crosses_removal_iff left right leftBound rightBound order
          leftOpen leftQuiet rightOpen rightQuiet current past input leftEvent rightEvent leftTag rightTag laterTag
          leftPath rightPath waiting first previous).mpr vacant))
      · exact .inr ⟨removed, rfl, vacant⟩

theorem move_waiting_activation_one_step {leftLength rightLength start cut parentBirth : Nat}
    (left : Trace (encodeProgram typedProgram) leftLength) (right : Trace (encodeProgram typedProgram) rightLength)
    (leftBound : start < leftLength) (rightBound : cut + 1 < rightLength) (order : start ≤ cut)
    (leftOpen : ¬ Nonempty (ClosedEpisode left)) (leftQuiet : Progress.Quiet (left.state leftLength))
    (rightOpen : ¬ Nonempty (ClosedEpisode right)) (rightQuiet : Progress.Quiet (right.state rightLength))
    (current : CutAgreement left right start)
    (past : ∀ time, time < start → addressedEventAt left time = addressedEventAt right time)
    (input : orchestrationInput left = orchestrationInput right)
    {leftKind rightKind : Lifecycle} {actor other : Name} (leftEvent : left.event start = .lifecycle leftKind actor)
    (rightEvent : right.event (cut + 1) = .lifecycle rightKind other)
    (leftTag : (left.notes start).1 actor = some parentBirth) (rightTag : (right.notes start).1 other = some parentBirth)
    (laterTag : (right.notes (cut + 1)).1 other = some parentBirth)
    {path : Address} (leftPath : Addressed left parentBirth path) (rightPath : Addressed right parentBirth path)
    (waiting : (right.state (cut + 1) other).map Fiber.phase = (right.state start other).map Fiber.phase)
    (first : ∀ time, start ≤ time → time < cut + 1 → ∀ k, right.event time ≠ .lifecycle k other)
    (ready : ∃ view, Target (right.state cut) other view)
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r) :
    letI : Setoid A := TypedCoeffectReplay.setoid observe
    (∃ moved : Trace (encodeProgram typedProgram) rightLength,
      StableActorAddresses right moved (exchangedIndex cut) ∧
      (∀ i, i ≤ cut → moved.state i = right.state i ∧ moved.notes i = right.notes i) ∧
      (∀ i, i < cut → moved.event i = right.event i) ∧
      moved.event cut = .lifecycle rightKind other ∧
      orchestrationInput moved = orchestrationInput right ∧
      StageSimulation.Related Eq (right.state rightLength) (moved.state rightLength) ∧
      (¬ Nonempty (ClosedEpisode moved)) ∧ Progress.Quiet (moved.state rightLength)) ∨
    ∃ removed, right.event cut = .command (.remove removed) ∧ right.state (cut + 2) removed ≠ none := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  rcases move_waiting_activation_one_step_with_exchange left right leftBound rightBound order leftOpen leftQuiet
    rightOpen rightQuiet current past input leftEvent rightEvent leftTag rightTag laterTag leftPath rightPath
    waiting first ready observe recovery commutative respect with
    ⟨moved, kept, fixed, earlier, selected, commands, endpoint, opened, quiet, _⟩ | reuse
  · exact Or.inl ⟨moved, kept, fixed, earlier, selected, commands, endpoint, opened, quiet⟩
  · exact Or.inr reuse

/-- A matched activation behind only other actors' activations can extend
the common prefix. The agreement at the earlier cut supplies Begin's
target even if the two executions chose different raw names. -/
theorem align_next_activation_with_path {leftLength rightLength start span : Nat}
    (left : Trace (encodeProgram typedProgram) leftLength) (right : Trace (encodeProgram typedProgram) rightLength)
    (leftBound : start < leftLength) (rightBound : start + span < rightLength)
    (leftOpen : ¬ Nonempty (ClosedEpisode left)) (leftQuiet : Progress.Quiet (left.state leftLength))
    (rightOpen : ¬ Nonempty (ClosedEpisode right)) (rightQuiet : Progress.Quiet (right.state rightLength))
    (current : CutAgreement left right start) (continuations : ChildContinuations (encodeProgram typedProgram))
    (past : ∀ i, i < start → addressedEventAt left i = addressedEventAt right i)
    {kind otherKind : Lifecycle} {actor other : Name} (first : left.event start = .lifecycle kind actor)
    (later : right.event (start + span) = .lifecycle otherKind other)
    {birth : Nat} {path : Address} (leftTag : (left.notes start).1 actor = some birth)
    (rightTag : (right.notes start).1 other = some birth) (laterTag : (right.notes (start + span)).1 other = some birth)
    (leftPath : Addressed left birth path) (rightPath : Addressed right birth path)
    (block : ∀ cut, start ≤ cut → cut < start + span →
      ∃ earlier name, right.event cut = .lifecycle earlier name ∧ name ≠ other)
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r) :
    letI : Setoid A := TypedCoeffectReplay.setoid observe
    ∃ (moved : Trace (encodeProgram typedProgram) rightLength) (expand : Nat → Nat),
      StableActorAddresses right moved expand ∧
      (∀ cut, cut < start + 1 → addressedEventAt left cut = addressedEventAt moved cut) ∧
      CutAgreement left moved (start + 1) ∧ orchestrationInput moved = orchestrationInput right ∧
      StageSimulation.Related Eq (right.state rightLength) (moved.state rightLength) ∧
      (¬ Nonempty (ClosedEpisode moved)) ∧ Progress.Quiet (moved.state rightLength) ∧ ActivationExchangePath right moved expand := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  obtain ⟨p, registry, live, words⟩ := current
  have actorEq := born_unique right (recorded_birth right (by omega : start ≤ rightLength) ((live actor).trans leftTag)).1
    (recorded_birth right (by omega : start ≤ rightLength) rightTag).1
  have ⟨active, step⟩ := left.activation_at leftOpen leftQuiet leftBound first
  have ready : ∃ view, Target (right.state start) other view := by
    obtain ⟨_, view, _, _, target⟩ := Transposition.activation_source (encodeProgram typedProgram) step active
    refine ⟨Renaming.view p view, ?_⟩
    have renamed := (Renaming.target_iff p (GuardedCutState.project (left.state start)) actor view).mpr
      ((GuardedCutState.project_target _ _ _).mpr target)
    rw [registry, actorEq] at renamed
    exact (GuardedCutState.project_target _ _ _).mp renamed
  obtain ⟨moved, expand, retained, stamps, cuts, movedEvent, address, commands, endpoint, opened, settled, exchanges⟩ :=
    pull_activation_through_activations_with_path right rightOpen rightQuiet rightBound later block (fun _ => ready)
      observe recovery commutative respect
  have previous (cut : Nat) (before : cut < start) : addressedEventAt left cut = addressedEventAt moved cut := by
    have kept := stable_addressed_event retained (cut := cut) (by omega)
    rw [stamps (cut + 1) (by omega), Nat.add_sub_cancel] at kept
    exact (past cut before).trans kept.symm
  have fixed := cuts start (Nat.le_refl _)
  have movedRegistry : Renaming.registry p (GuardedCutState.project (left.state start)) =
      GuardedCutState.project (moved.state start) := by rw [fixed.1]; exact registry
  have movedTags : ∀ n, (moved.notes start).1 (p.toFun n) = (left.notes start).1 n := by
    rw [fixed.2]
    exact live
  have movedCut : CutAgreement left moved start := by
    refine ⟨p, movedRegistry, movedTags, ?_⟩
    unfold GuardedBirthReplay.SavedMatch at words ⊢
    simpa only [fixed.2] using words
  have movedActive := (moved.activation_at opened settled (by omega : start < rightLength) movedEvent).1
  have kindEq := matched_activation_kind left moved leftBound (by omega : start < rightLength) (stamp := id)
    (by simpa using movedTags) rfl movedRegistry continuations first (actorEq.symm ▸ movedEvent) active movedActive
  have aligned := (activation_address left first leftTag leftPath).trans
    ((congrArg (fun stage => some (AddressedEvent.lifecycle (Key := Key) (Code := Code) stage path)) kindEq).trans
      ((activation_address right later laterTag rightPath).symm.trans address.symm))
  refine ⟨moved, expand, retained, ?_, advance_addressed_cut left moved leftBound (by omega) movedCut continuations
    (fun event => (left.activation_at leftOpen leftQuiet leftBound event).1)
    (fun event => (moved.activation_at opened settled (by omega) event).1) previous aligned,
    commands, endpoint, opened, settled, exchanges⟩
  intro cut inside
  rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ inside) with rfl | before
  · exact aligned
  · exact previous cut before


/-- The paired allocating stage can be advanced by ordinary activation
exchanges if it lies before the next command. No redraw is required. -/
theorem align_addressed_allocation_before_command {leftLength rightLength start span : Nat}
    (left : Trace (encodeProgram typedProgram) leftLength) (right : Trace (encodeProgram typedProgram) rightLength)
    (leftBound : start < leftLength) (rightBound : start + span < rightLength)
    (leftOpen : ¬ Nonempty (ClosedEpisode left)) (leftQuiet : Progress.Quiet (left.state leftLength))
    (rightOpen : ¬ Nonempty (ClosedEpisode right)) (rightQuiet : Progress.Quiet (right.state rightLength))
    (current : CutAgreement left right start) (continuations : ChildContinuations (encodeProgram typedProgram))
    (past : ∀ i, i < start → addressedEventAt left i = addressedEventAt right i)
    (input : orchestrationInput left = orchestrationInput right)
    {kind otherKind : Lifecycle} {actor other child drawn : Name} {address : Address}
    (first : left.event start = .lifecycle kind actor)
    (later : right.event (start + span) = .lifecycle otherKind other)
    (leftBorn : GuardedBirthMatching.BornAt left child (start + 1))
    (rightBorn : GuardedBirthMatching.BornAt right drawn (start + span + 1))
    (leftAddress : Addressed left (start + 1) address) (rightAddress : Addressed right (start + span + 1) address)
    (block : ∀ cut, start ≤ cut → cut < start + span → ∃ earlier name, right.event cut = .lifecycle earlier name)
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r) :
    letI : Setoid A := TypedCoeffectReplay.setoid observe
    ∃ (moved : Trace (encodeProgram typedProgram) rightLength) (expand : Nat → Nat),
      (∀ cut, cut < start + 1 → addressedEventAt left cut = addressedEventAt moved cut) ∧
      CutAgreement left moved (start + 1) ∧ orchestrationInput moved = orchestrationInput right ∧
      StageSimulation.Related Eq (right.state rightLength) (moved.state rightLength) ∧
      (¬ Nonempty (ClosedEpisode moved)) ∧ Progress.Quiet (moved.state rightLength) ∧ ActivationExchangePath right moved expand := by
  obtain ⟨birth, parent, leftTag, initialTag, laterTag, leftPath, rightPath, earliest⟩ :=
    GuardedReservationAlignment.addressed_allocation_is_first_pending left right leftBound rightBound (by omega)
      leftOpen leftQuiet rightOpen rightQuiet current past input first later leftBorn rightBorn leftAddress rightAddress
  have distinct (cut : Nat) (lower : start ≤ cut) (upper : cut < start + span) :
      ∃ stage name, right.event cut = .lifecycle stage name ∧ name ≠ other := by
    obtain ⟨stage, name, label⟩ := block cut lower upper
    exact ⟨stage, name, label, fun equal => earliest cut lower upper stage (equal ▸ label)⟩
  obtain ⟨moved, expand, _, order, cut, commands, endpoint, opened, quiet, path⟩ :=
    align_next_activation_with_path left right leftBound rightBound leftOpen leftQuiet rightOpen rightQuiet
      current continuations past first later leftTag initialTag laterTag leftPath rightPath distinct
      observe recovery commutative respect
  exact ⟨moved, expand, order, cut, commands, endpoint, opened, quiet, path⟩

/-- A later stage of the same addressed parent supplies a bound on
its next activation. If that stage is before the next command, the
parent's next activation can be aligned without crossing a command. -/
theorem align_pending_parent_before_required_stage {leftLength rightLength start limit : Nat}
    (left : Trace (encodeProgram typedProgram) leftLength) (right : Trace (encodeProgram typedProgram) rightLength)
    (leftBound : start < leftLength) (rightBound : limit < rightLength) (lower : start ≤ limit)
    (leftOpen : ¬ Nonempty (ClosedEpisode left)) (leftQuiet : Progress.Quiet (left.state leftLength))
    (rightOpen : ¬ Nonempty (ClosedEpisode right)) (rightQuiet : Progress.Quiet (right.state rightLength))
    (current : CutAgreement left right start) (continuations : ChildContinuations (encodeProgram typedProgram))
    (past : ∀ i, i < start → addressedEventAt left i = addressedEventAt right i)
    (input : orchestrationInput left = orchestrationInput right)
    {kind laterKind : Lifecycle} {actor allocator : Name} {leftBirth rightBirth : Nat} {parent : Address}
    (first : left.event start = .lifecycle kind actor)
    (later : right.event limit = .lifecycle laterKind allocator)
    (leftTag : (left.notes start).1 actor = some leftBirth) (rightTag : (right.notes limit).1 allocator = some rightBirth)
    (leftParent : Addressed left leftBirth parent) (rightParent : Addressed right rightBirth parent)
    (block : ∀ cut, start ≤ cut → cut < limit → ∃ label name, right.event cut = .lifecycle label name)
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r) :
    letI : Setoid A := TypedCoeffectReplay.setoid observe
    ∃ (moved : Trace (encodeProgram typedProgram) rightLength) (expand : Nat → Nat),
      (∀ cut, cut < start + 1 → addressedEventAt left cut = addressedEventAt moved cut) ∧
      CutAgreement left moved (start + 1) ∧ orchestrationInput moved = orchestrationInput right ∧
      StageSimulation.Related Eq (right.state rightLength) (moved.state rightLength) ∧
      (¬ Nonempty (ClosedEpisode moved)) ∧ Progress.Quiet (moved.state rightLength) ∧ ActivationExchangePath right moved expand := by
  obtain ⟨time, nextKind, other, birth, path, afterStart, within, next, tag, initial, laterTag,
      leftPath, rightPath, _, _, earliest⟩ :=
    pending_activation_occurs left right leftBound (by omega) leftOpen leftQuiet rightOpen rightQuiet
      current past input first
  have sameBirth := Option.some.inj (tag.symm.trans leftTag)
  subst leftBirth
  have samePath := leftPath.unique leftParent
  subst path
  have sameRightBirth := rightPath.injective rightParent rfl
  subst rightBirth
  have sameActor := born_unique right (recorded_birth right (by omega : time ≤ rightLength) laterTag).1
    (recorded_birth right (by omega : limit ≤ rightLength) rightTag).1
  subst allocator
  have ends : time ≤ limit := by
    apply Nat.le_of_not_gt
    intro late
    exact earliest limit lower late laterKind later
  have atTime : start + (time - start) = time := by omega
  have distinct (cut : Nat) (lo : start ≤ cut) (hi : cut < start + (time - start)) :
      ∃ label name, right.event cut = .lifecycle label name ∧ name ≠ other := by
    obtain ⟨label, name, event⟩ := block cut lo (by omega)
    exact ⟨label, name, event, fun same => earliest cut lo (by omega) label (same ▸ event)⟩
  obtain ⟨moved, expand, _, ordered, cut, commands, endpoint, opened, quiet, path⟩ :=
    align_next_activation_with_path left right leftBound (span := time - start) (by omega)
      leftOpen leftQuiet rightOpen rightQuiet current continuations past first (by rwa [atTime])
      tag initial (by rwa [atTime]) leftPath rightPath distinct observe recovery commutative respect
  exact ⟨moved, expand, ordered, cut, commands, endpoint, opened, quiet, path⟩

/-- A matched addressed prefix contains the same child births at
the same stamps, including births of children since removed. -/
theorem matched_prefix_contains_child_birth {leftLength rightLength through stamp ordinal : Nat}
    (left : Trace (encodeProgram typedProgram) leftLength) (right : Trace (encodeProgram typedProgram) rightLength)
    (leftBound : through ≤ leftLength) (rightBound : through ≤ rightLength) (before : stamp ≤ through)
    (leftOpen : ¬ Nonempty (ClosedEpisode left)) (leftQuiet : Progress.Quiet (left.state leftLength))
    (rightOpen : ¬ Nonempty (ClosedEpisode right)) (rightQuiet : Progress.Quiet (right.state rightLength))
    (stable : ChildContinuations (encodeProgram typedProgram))
    (past : ∀ i, i < through → addressedEventAt left i = addressedEventAt right i)
    {parent : Address} (birth : Addressed left stamp (.child parent ordinal)) :
    Addressed right stamp (.child parent ordinal) := by
  obtain ⟨name, born⟩ := birth.child_born
  obtain ⟨names, _, aligned, _⟩ := match_open_prefix left right stable stamp (by omega) (by omega) (by
    intro cut earlier
    exact match_addressed_event left right (by omega) (by omega)
      (fun event => (left.activation_at leftOpen leftQuiet (by omega) event).1)
      (fun event => (right.activation_at rightOpen rightQuiet (by omega) event).1)
      (fun i prior => past i (by omega)) (past cut (by omega)))
  have tag : (left.notes stamp).1 name = some stamp := by
    rw [left.notes_eq stamp (by omega)]
    have positive := born.1
    have boundary : stamp - 1 + 1 = stamp := by omega
    rw [← boundary]
    exact Incarnation.birthAt_of_created born.2.2.1 (by rw [boundary]; exact born.2.2.2)
  have peer := (recorded_birth right (by omega : stamp ≤ rightLength) ((aligned name).trans tag)).1
  obtain ⟨address, actual⟩ := exists_address right peer
  have same := address_of_matched_birth left right past before birth actual
  exact same.symm ▸ actual

/-- An ancestor can be aligned before the next command when that
command needs a descendant along an edge whose child has yet to be
allocated. The actual allocation along the edge gives the cutoff. -/
theorem align_pending_ancestor_before_required_birth {leftLength rightLength start birth : Nat}
    (left : Trace (encodeProgram typedProgram) leftLength) (right : Trace (encodeProgram typedProgram) rightLength)
    (leftBound : start < leftLength) (rightBound : start ≤ rightLength)
    (leftOpen : ¬ Nonempty (ClosedEpisode left)) (leftQuiet : Progress.Quiet (left.state leftLength))
    (rightOpen : ¬ Nonempty (ClosedEpisode right)) (rightQuiet : Progress.Quiet (right.state rightLength))
    (current : CutAgreement left right start) (continuations : ChildContinuations (encodeProgram typedProgram))
    (past : ∀ i, i < start → addressedEventAt left i = addressedEventAt right i)
    (input : orchestrationInput left = orchestrationInput right)
    {kind : Lifecycle} {actor : Name} {leftBirth ordinal : Nat} {parent descendant : Address}
    (first : left.event start = .lifecycle kind actor)
    (leftTag : (left.notes start).1 actor = some leftBirth) (leftParent : Addressed left leftBirth parent)
    (required : Addressed right birth descendant)
    (lineage : descendant.DescendsFrom (.child parent ordinal))
    (unborn : ∀ stamp, stamp ≤ start → ¬ Addressed left stamp (.child parent ordinal))
    (block : ∀ cut, start ≤ cut → cut < birth → ∃ label name, right.event cut = .lifecycle label name)
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r) :
    letI : Setoid A := TypedCoeffectReplay.setoid observe
    ∃ (moved : Trace (encodeProgram typedProgram) rightLength) (expand : Nat → Nat),
      start < rightLength ∧ (∀ cut, cut < start + 1 → addressedEventAt left cut = addressedEventAt moved cut) ∧
      CutAgreement left moved (start + 1) ∧ orchestrationInput moved = orchestrationInput right ∧
      StageSimulation.Related Eq (right.state rightLength) (moved.state rightLength) ∧
      (¬ Nonempty (ClosedEpisode moved)) ∧ Progress.Quiet (moved.state rightLength) ∧ ActivationExchangePath right moved expand := by
  obtain ⟨stamp, earlier, born⟩ := required.ancestor_birth lineage
  obtain ⟨cut, parentBirth, label, allocator, placed, bounded, event, tag, addressed⟩ := born.allocating_event
  have after : start < stamp := by
    apply Nat.lt_of_not_ge
    intro before
    exact unborn stamp before (matched_prefix_contains_child_birth right left rightBound (by omega)
      before rightOpen rightQuiet leftOpen leftQuiet continuations (fun i lo => (past i lo).symm) born)
  obtain ⟨moved, expand, ordered, final, commands, endpoint, opened, quiet, path⟩ :=
    align_pending_parent_before_required_stage left right leftBound bounded (by omega)
      leftOpen leftQuiet rightOpen rightQuiet current continuations past input first event leftTag tag leftParent addressed
      (fun i lo hi => block i lo (by omega)) observe recovery commutative respect
  exact ⟨moved, expand, by omega, ordered, final, commands, endpoint, opened, quiet, path⟩

theorem align_next_activation {leftLength rightLength start span : Nat}
    (left : Trace (encodeProgram typedProgram) leftLength) (right : Trace (encodeProgram typedProgram) rightLength)
    (leftBound : start < leftLength) (rightBound : start + span < rightLength)
    (leftOpen : ¬ Nonempty (ClosedEpisode left)) (leftQuiet : Progress.Quiet (left.state leftLength))
    (rightOpen : ¬ Nonempty (ClosedEpisode right)) (rightQuiet : Progress.Quiet (right.state rightLength))
    (current : CutAgreement left right start) (continuations : ChildContinuations (encodeProgram typedProgram))
    (past : ∀ i, i < start → addressedEventAt left i = addressedEventAt right i)
    {kind otherKind : Lifecycle} {actor other : Name} (first : left.event start = .lifecycle kind actor)
    (later : right.event (start + span) = .lifecycle otherKind other)
    {birth : Nat} {path : Address} (leftTag : (left.notes start).1 actor = some birth)
    (rightTag : (right.notes start).1 other = some birth) (laterTag : (right.notes (start + span)).1 other = some birth)
    (leftPath : Addressed left birth path) (rightPath : Addressed right birth path)
    (block : ∀ cut, start ≤ cut → cut < start + span →
      ∃ earlier name, right.event cut = .lifecycle earlier name ∧ name ≠ other)
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r) :
    letI : Setoid A := TypedCoeffectReplay.setoid observe
    ∃ (moved : Trace (encodeProgram typedProgram) rightLength) (expand : Nat → Nat),
      StableActorAddresses right moved expand ∧
      (∀ cut, cut < start + 1 → addressedEventAt left cut = addressedEventAt moved cut) ∧
      CutAgreement left moved (start + 1) ∧ orchestrationInput moved = orchestrationInput right ∧
      StageSimulation.Related Eq (right.state rightLength) (moved.state rightLength) ∧
      (¬ Nonempty (ClosedEpisode moved)) ∧ Progress.Quiet (moved.state rightLength) := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  obtain ⟨moved, expand, addresses, schedule, cut, input, endpoint, opened, settled, _⟩ :=
    align_next_activation_with_path left right leftBound rightBound leftOpen leftQuiet rightOpen rightQuiet
      current continuations past first later leftTag rightTag laterTag leftPath rightPath block
      observe recovery commutative respect
  exact ⟨moved, expand, addresses, schedule, cut, input, endpoint, opened, settled⟩

/-- The matching activation is the first of its incarnation since the
shared cut. It follows a removal and immediately reuses that raw name. -/
def RawNameReuseBarrier {leftLength rightLength : Nat}
    (left : Trace (encodeProgram typedProgram) leftLength) (right : Trace (encodeProgram typedProgram) rightLength)
    (start : Nat) (actor : Name) : Prop :=
  ∃ cut removed kind other, start ≤ cut ∧ cut + 1 < rightLength ∧
    right.event cut = .command (.remove removed) ∧ right.event (cut + 1) = .lifecycle kind other ∧
    right.state (cut + 2) removed ≠ none ∧
    (left.notes start).1 actor = (right.notes (cut + 1)).1 other ∧
    ∀ i, start ≤ i → i < cut + 1 → ∀ earlier, right.event i ≠ .lifecycle earlier other

/-- Move the actual counterpart left through the intervening events,
including external commands. Either it extends the shared addressed
prefix or it stops at a removal whose raw name it immediately reuses. -/
theorem align_pending_activation_or_reuse {leftLength rightLength start : Nat}
    (left : Trace (encodeProgram typedProgram) leftLength) (right : Trace (encodeProgram typedProgram) rightLength)
    (leftBound : start < leftLength) (rightBound : start ≤ rightLength)
    (leftOpen : ¬ Nonempty (ClosedEpisode left)) (leftQuiet : Progress.Quiet (left.state leftLength))
    (rightOpen : ¬ Nonempty (ClosedEpisode right)) (rightQuiet : Progress.Quiet (right.state rightLength))
    (current : CutAgreement left right start) (continuations : ChildContinuations (encodeProgram typedProgram))
    (past : ∀ i, i < start → addressedEventAt left i = addressedEventAt right i)
    (input : orchestrationInput left = orchestrationInput right)
    {kind : Lifecycle} {actor : Name} (event : left.event start = .lifecycle kind actor)
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r) :
    letI : Setoid A := TypedCoeffectReplay.setoid observe
    ∃ (moved : Trace (encodeProgram typedProgram) rightLength) (expand : Nat → Nat),
      start < rightLength ∧ StableActorAddresses right moved expand ∧ orchestrationInput moved = orchestrationInput right ∧
      StageSimulation.Related Eq (right.state rightLength) (moved.state rightLength) ∧
      (¬ Nonempty (ClosedEpisode moved)) ∧ Progress.Quiet (moved.state rightLength) ∧
      ((CutAgreement left moved (start + 1) ∧
        (∀ cut, cut < start + 1 → addressedEventAt left cut = addressedEventAt moved cut)) ∨
        (CutAgreement left moved start ∧ (∀ cut, cut < start → addressedEventAt left cut = addressedEventAt moved cut) ∧
          RawNameReuseBarrier left moved start actor)) := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  obtain ⟨time, otherKind, other, birth, path, lower, inside, next, leftTag, rightTag, _, leftPath, rightPath, _, waits, first⟩ :=
    pending_activation_occurs left right leftBound rightBound leftOpen leftQuiet rightOpen rightQuiet current past input event
  have search (span : Nat) (source : Trace (encodeProgram typedProgram) rightLength)
      (bounded : start + span < rightLength)
      (openOnly : ¬ Nonempty (ClosedEpisode source)) (quiet : Progress.Quiet (source.state rightLength))
      (matched : CutAgreement left source start)
      (ordered : ∀ i, i < start → addressedEventAt left i = addressedEventAt source i)
      (sameInput : orchestrationInput left = orchestrationInput source)
      (later : source.event (start + span) = .lifecycle otherKind other) (parent : Addressed source birth path)
      (through : ∀ i, start ≤ i → i ≤ start + span → (source.notes i).1 other = some birth ∧
        (source.state i other).map Fiber.phase = (source.state start other).map Fiber.phase ∧
        ∃ view, Target (source.state i) other view)
      (earliest : ∀ i, start ≤ i → i < start + span → ∀ earlier, source.event i ≠ .lifecycle earlier other) :
      ∃ (moved : Trace (encodeProgram typedProgram) rightLength) (expand : Nat → Nat),
        StableActorAddresses source moved expand ∧ orchestrationInput moved = orchestrationInput source ∧
        StageSimulation.Related Eq (source.state rightLength) (moved.state rightLength) ∧
        (¬ Nonempty (ClosedEpisode moved)) ∧ Progress.Quiet (moved.state rightLength) ∧
        ((CutAgreement left moved (start + 1) ∧
          (∀ cut, cut < start + 1 → addressedEventAt left cut = addressedEventAt moved cut)) ∨
          (CutAgreement left moved start ∧ (∀ cut, cut < start → addressedEventAt left cut = addressedEventAt moved cut) ∧
            RawNameReuseBarrier left moved start actor)) := by
    induction span generalizing source with
    | zero =>
      have tag := (through start (Nat.le_refl _) (Nat.le_refl _)).1
      obtain ⟨moved, expand, retained, longer, nextCut, commands, endpoint, opened, settled⟩ :=
        align_next_activation left source leftBound bounded leftOpen leftQuiet openOnly quiet matched continuations ordered
          event later leftTag tag tag leftPath parent (fun _ first before => by omega) observe recovery commutative respect
      exact ⟨moved, expand, retained, commands, endpoint, opened, settled, .inl ⟨nextCut, longer⟩⟩
    | succ span ih =>
      let cut := start + span
      have adjacent : cut + 1 < rightLength := bounded
      have nextEvent : source.event (cut + 1) = .lifecycle otherKind other := later
      have atStart := (through start (Nat.le_refl _) (by omega)).1
      have atNext := through (cut + 1) (by omega) (by omega)
      have before := through cut (by omega) (by omega)
      rcases move_waiting_activation_one_step left source leftBound adjacent (by omega) leftOpen leftQuiet openOnly quiet
        matched ordered sameInput event nextEvent leftTag atStart atNext.1 leftPath parent atNext.2.1 earliest before.2.2
        observe recovery commutative respect with
        ⟨mid, kept, fixed, labels, movedEvent, commands, endpoint, opened, settled⟩ | ⟨removed, action, rebound⟩
      · have midPrefix (i : Nat) (earlier : i < start) : addressedEventAt left i = addressedEventAt mid i := by
          have keptEvent := stable_addressed_event kept (cut := i) (by omega)
          rw [ExchangeReplay.exchangedIndex_other (by omega) (by omega), Nat.add_sub_cancel] at keptEvent
          exact (ordered i earlier).trans keptEvent.symm
        have initial := fixed start (by omega)
        have midCut : CutAgreement left mid start := by
          obtain ⟨names, registry, live, words⟩ := matched
          refine ⟨names, by simpa only [initial.1] using registry, by simpa only [initial.2] using live, ?_⟩
          unfold GuardedBirthReplay.SavedMatch at words ⊢
          simpa only [initial.2] using words
        have initialTag : (mid.notes start).1 other = some birth := by rw [initial.2]; exact atStart
        have actual := recorded_birth mid (by omega : start ≤ rightLength) initialTag
        obtain ⟨newPath, addressed⟩ := exists_address mid actual.1
        have samePath := address_of_matched_birth left mid midPrefix actual.2 leftPath addressed
        have midThrough (i : Nat) (lower : start ≤ i) (upper : i ≤ start + span) :
            (mid.notes i).1 other = some birth ∧
            (mid.state i other).map Fiber.phase = (mid.state start other).map Fiber.phase ∧
            ∃ view, Target (mid.state i) other view := by
          have keptCut := fixed i upper
          rw [keptCut.1, keptCut.2, initial.1]
          exact through i lower (by omega)
        have midFirst (i : Nat) (lower : start ≤ i) (upper : i < start + span) (earlier : Lifecycle) :
            mid.event i ≠ .lifecycle earlier other := by
          rw [labels i upper]
          exact earliest i lower (by omega) earlier
        obtain ⟨moved, expand, again, inputEq, related, openEnd, quietEnd, result⟩ :=
          ih mid (by omega) opened settled midCut midPrefix (sameInput.trans commands.symm) movedEvent
            (samePath.symm ▸ addressed) midThrough midFirst
        exact ⟨moved, exchangedIndex cut ∘ expand, kept.trans again, inputEq.trans commands,
          StageSimulation.Related.trans (Q := Eq) (fun a b => a.trans b) endpoint related, openEnd, quietEnd, result⟩
      · refine ⟨source, id, .refl source, rfl, ?_, openOnly, quiet, .inr ⟨matched, ordered, cut, removed,
          otherKind, other, by omega, adjacent, action, nextEvent, rebound, leftTag.trans atNext.1.symm, earliest⟩⟩
        exact source.self_related rightLength (Nat.le_refl _)
          (TypedRegistry.encoded_program_callbacks ops observe typedProgram recovery commutative)
  have place : start + (time - start) = time := by omega
  obtain ⟨moved, expand, kept, commands, endpoint, opened, settled, result⟩ :=
    search (time - start) right (place.symm ▸ inside) rightOpen rightQuiet current past input (place.symm ▸ next) rightPath
      (by simpa only [place] using waits) (by simpa only [place] using first)
  exact ⟨moved, expand, by omega, kept, commands, endpoint, opened, settled, result⟩

/-- Align arbitrary surviving schedules from the empty cut, retaining all
external commands. The only obstruction returned by these literal-name
exchanges is an actual removal followed by immediate reuse at a matched
incarnation's first pending activation. -/
theorem align_surviving_schedules_or_reuse {leftLength rightLength : Nat}
    (left : Trace (encodeProgram typedProgram) leftLength) (right : Trace (encodeProgram typedProgram) rightLength)
    (leftOpen : ¬ Nonempty (ClosedEpisode left)) (leftQuiet : Progress.Quiet (left.state leftLength))
    (rightOpen : ¬ Nonempty (ClosedEpisode right)) (rightQuiet : Progress.Quiet (right.state rightLength))
    (continuations : ChildContinuations (encodeProgram typedProgram))
    (input : orchestrationInput left = orchestrationInput right)
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r) :
    letI : Setoid A := TypedCoeffectReplay.setoid observe
    ∃ (moved : Trace (encodeProgram typedProgram) rightLength) (expand : Nat → Nat),
      StableActorAddresses right moved expand ∧ orchestrationInput moved = orchestrationInput right ∧
      StageSimulation.Related Eq (right.state rightLength) (moved.state rightLength) ∧
      (¬ Nonempty (ClosedEpisode moved)) ∧ Progress.Quiet (moved.state rightLength) ∧
      ((leftLength = rightLength ∧ CutAgreement left moved leftLength ∧
        (∀ i, i < leftLength → addressedEventAt left i = addressedEventAt moved i)) ∨
        ∃ start kind actor, start < leftLength ∧ left.event start = .lifecycle kind actor ∧
          CutAgreement left moved start ∧ (∀ i, i < start → addressedEventAt left i = addressedEventAt moved i) ∧
          RawNameReuseBarrier left moved start actor) := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  have align (remaining : Nat) {start : Nat} (source : Trace (encodeProgram typedProgram) rightLength)
      (count : start + remaining = leftLength) (rightBound : start ≤ rightLength)
      (opened : ¬ Nonempty (ClosedEpisode source)) (settled : Progress.Quiet (source.state rightLength))
      (matched : CutAgreement left source start)
      (past : ∀ i, i < start → addressedEventAt left i = addressedEventAt source i)
      (commands : orchestrationInput left = orchestrationInput source) :
      ∃ (moved : Trace (encodeProgram typedProgram) rightLength) (expand : Nat → Nat),
        StableActorAddresses source moved expand ∧ orchestrationInput moved = orchestrationInput source ∧
        StageSimulation.Related Eq (source.state rightLength) (moved.state rightLength) ∧
        (¬ Nonempty (ClosedEpisode moved)) ∧ Progress.Quiet (moved.state rightLength) ∧
        ((leftLength = rightLength ∧ CutAgreement left moved leftLength ∧
          (∀ i, i < leftLength → addressedEventAt left i = addressedEventAt moved i)) ∨
          ∃ start kind actor, start < leftLength ∧ left.event start = .lifecycle kind actor ∧
            CutAgreement left moved start ∧ (∀ i, i < start → addressedEventAt left i = addressedEventAt moved i) ∧
            RawNameReuseBarrier left moved start actor) := by
    induction remaining generalizing start source with
    | zero =>
      obtain rfl : start = leftLength := by omega
      have equal := matched_endpoint_is_terminal left source rightBound matched past commands leftQuiet settled opened
      refine ⟨source, id, .refl source, rfl, ?_, opened, settled, .inl ⟨equal, matched, past⟩⟩
      exact source.self_related rightLength (Nat.le_refl _)
        (TypedRegistry.encoded_program_callbacks ops observe typedProgram recovery commutative)
    | succ remaining ih =>
      have inside : start < leftLength := by omega
      have advance : ∃ (mid : Trace (encodeProgram typedProgram) rightLength) (stamp : Nat → Nat),
          start < rightLength ∧ StableActorAddresses source mid stamp ∧ orchestrationInput mid = orchestrationInput source ∧
          StageSimulation.Related Eq (source.state rightLength) (mid.state rightLength) ∧
          (¬ Nonempty (ClosedEpisode mid)) ∧ Progress.Quiet (mid.state rightLength) ∧
          ((CutAgreement left mid (start + 1) ∧
            (∀ i, i < start + 1 → addressedEventAt left i = addressedEventAt mid i)) ∨
            ∃ kind actor, left.event start = .lifecycle kind actor ∧ CutAgreement left mid start ∧
              (∀ i, i < start → addressedEventAt left i = addressedEventAt mid i) ∧ RawNameReuseBarrier left mid start actor) := by
        cases next : left.event start with
        | command cmd =>
          obtain ⟨mid, stamp, rightInside, retained, longer, cut, inputEq, endpoint, openMid, quietMid⟩ :=
            align_pending_command left source inside rightBound opened settled matched continuations past commands next
          refine ⟨mid, stamp, rightInside, retained, inputEq, ?_, openMid, quietMid, .inl ⟨cut, longer⟩⟩
          rw [endpoint]
          exact source.self_related rightLength (Nat.le_refl _)
            (TypedRegistry.encoded_program_callbacks ops observe typedProgram recovery commutative)
        | lifecycle kind actor =>
          obtain ⟨mid, stamp, rightInside, retained, inputEq, endpoint, openMid, quietMid, step⟩ :=
            align_pending_activation_or_reuse left source inside rightBound leftOpen leftQuiet opened settled matched
              continuations past commands next observe recovery commutative respect
          exact ⟨mid, stamp, rightInside, retained, inputEq, endpoint, openMid, quietMid,
            step.imp id (fun failure => ⟨kind, actor, rfl, failure⟩)⟩
      obtain ⟨mid, stamp, rightInside, retained, inputEq, endpoint, openMid, quietMid, step⟩ := advance
      rcases step with ⟨cut, longer⟩ | ⟨kind, actor, event, shared, ordered, reused⟩
      · obtain ⟨moved, expand, kept, word, related, openEnd, quietEnd, result⟩ :=
          ih mid (start := start + 1) (by omega) (by omega) openMid quietMid cut longer (commands.trans inputEq.symm)
        exact ⟨moved, stamp ∘ expand, retained.trans kept, word.trans inputEq,
          StageSimulation.Related.trans (Q := Eq) (fun a b => a.trans b) endpoint related, openEnd, quietEnd, result⟩
      · exact ⟨mid, stamp, retained, inputEq, endpoint, openMid, quietMid,
          .inr ⟨start, kind, actor, inside, event, shared, ordered, reused⟩⟩
  exact align leftLength (start := 0) right (Nat.zero_add _) (Nat.zero_le _) rightOpen rightQuiet
    (match_open_prefix left right continuations 0 (Nat.zero_le _) (Nat.zero_le _) (fun _ impossible => by omega))
    (fun _ impossible => by omega) input

/-- When the remaining suffix has no external commands, its first required
activation can be found and moved to the matched cut. -/
theorem align_pending_activation {leftLength rightLength start : Nat}
    (left : Trace (encodeProgram typedProgram) leftLength) (right : Trace (encodeProgram typedProgram) rightLength)
    (leftBound : start < leftLength) (rightBound : start ≤ rightLength)
    (leftOpen : ¬ Nonempty (ClosedEpisode left)) (leftQuiet : Progress.Quiet (left.state leftLength))
    (rightOpen : ¬ Nonempty (ClosedEpisode right)) (rightQuiet : Progress.Quiet (right.state rightLength))
    (current : CutAgreement left right start) (continuations : ChildContinuations (encodeProgram typedProgram))
    (past : ∀ i, i < start → addressedEventAt left i = addressedEventAt right i)
    (input : orchestrationInput left = orchestrationInput right)
    {kind : Lifecycle} {actor : Name} (event : left.event start = .lifecycle kind actor)
    (commandFree : ∀ cut, start ≤ cut → cut < rightLength → ∃ earlier name, right.event cut = .lifecycle earlier name)
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r) :
    letI : Setoid A := TypedCoeffectReplay.setoid observe
    ∃ (moved : Trace (encodeProgram typedProgram) rightLength) (expand : Nat → Nat),
      start < rightLength ∧ StableActorAddresses right moved expand ∧
      (∀ cut, cut < start + 1 → addressedEventAt left cut = addressedEventAt moved cut) ∧
      CutAgreement left moved (start + 1) ∧ orchestrationInput moved = orchestrationInput right ∧
      StageSimulation.Related Eq (right.state rightLength) (moved.state rightLength) ∧
      (¬ Nonempty (ClosedEpisode moved)) ∧ Progress.Quiet (moved.state rightLength) ∧ ActivationExchangePath right moved expand := by
  obtain ⟨time, otherKind, other, birth, path, later, within, next, leftTag, rightTag, laterTag, leftPath, rightPath, _, _, first⟩ :=
    pending_activation_occurs left right leftBound rightBound leftOpen leftQuiet rightOpen rightQuiet current past input event
  have location : start + (time - start) = time := by omega
  have bound : start + (time - start) < rightLength := by omega
  have block (cut : Nat) (lower : start ≤ cut) (upper : cut < start + (time - start)) :
      ∃ earlier name, right.event cut = .lifecycle earlier name ∧ name ≠ other := by
    obtain ⟨earlier, name, stage⟩ := commandFree cut lower (by omega)
    exact ⟨earlier, name, stage, fun same => first cut lower (by omega) earlier (same ▸ stage)⟩
  obtain ⟨moved, expand, addresses, prefixMatch, matched, commands, endpoint, openOnly, quiet, path⟩ :=
    align_next_activation_with_path left right leftBound bound leftOpen leftQuiet rightOpen rightQuiet current continuations past event
      (location.symm ▸ next) leftTag rightTag (location.symm ▸ laterTag) leftPath rightPath block
      observe recovery commutative respect
  exact ⟨moved, expand, by omega, addresses, prefixMatch, matched, commands, endpoint, openOnly, quiet, path⟩

/-- Equal surviving input and a matched cut after the last external command
give a common addressed continuation, even when the activations were
independently scheduled. The original right endpoint remains related to the
new one, while the two aligned endpoints have exact cut agreement. -/
theorem align_command_free_suffix {leftLength rightLength start : Nat}
    (left : Trace (encodeProgram typedProgram) leftLength) (right : Trace (encodeProgram typedProgram) rightLength)
    (leftBound : start ≤ leftLength) (rightBound : start ≤ rightLength)
    (leftOpen : ¬ Nonempty (ClosedEpisode left)) (leftQuiet : Progress.Quiet (left.state leftLength))
    (rightOpen : ¬ Nonempty (ClosedEpisode right)) (rightQuiet : Progress.Quiet (right.state rightLength))
    (current : CutAgreement left right start) (continuations : ChildContinuations (encodeProgram typedProgram))
    (past : ∀ i, i < start → addressedEventAt left i = addressedEventAt right i)
    (input : orchestrationInput left = orchestrationInput right)
    (commandFree : ∀ cut, start ≤ cut → cut < leftLength → ∃ kind name, left.event cut = .lifecycle kind name)
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r) :
    letI : Setoid A := TypedCoeffectReplay.setoid observe
    ∃ (moved : Trace (encodeProgram typedProgram) rightLength) (expand : Nat → Nat),
      leftLength = rightLength ∧ StableActorAddresses right moved expand ∧
      (∀ cut, cut < leftLength → addressedEventAt left cut = addressedEventAt moved cut) ∧
      CutAgreement left moved leftLength ∧ orchestrationInput moved = orchestrationInput right ∧
      StageSimulation.Related Eq (right.state rightLength) (moved.state rightLength) ∧
      (¬ Nonempty (ClosedEpisode moved)) ∧ Progress.Quiet (moved.state rightLength) ∧ ActivationExchangePath right moved expand := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  generalize measure : leftLength - start = remaining
  induction remaining generalizing start right with
  | zero =>
    obtain rfl : start = leftLength := by omega
    have equal := matched_endpoint_is_terminal left right rightBound current past input leftQuiet rightQuiet rightOpen
    exact ⟨right, id, equal, .refl right, past, current, rfl,
      right.self_related rightLength (Nat.le_refl _)
        (TypedRegistry.encoded_program_callbacks ops observe typedProgram recovery commutative), rightOpen, rightQuiet, .refl right⟩
  | succ remaining ih =>
    have inside : start < leftLength := by omega
    obtain ⟨kind, actor, event⟩ := commandFree start (Nat.le_refl _) inside
    have rightFree := command_free_of_matched_prefix left right leftBound rightBound past input commandFree
    obtain ⟨mid, stamp, rightInside, retained, matched, next, word, first, openOnly, quiet, firstPath⟩ :=
      align_pending_activation left right inside rightBound leftOpen leftQuiet rightOpen rightQuiet current continuations past
        input event rightFree observe recovery commutative respect
    obtain ⟨moved, expand, equal, later, schedule, final, commands, endpoint, opened, settled, restPath⟩ :=
      ih (start := start + 1) mid (by omega) (by omega) openOnly quiet next matched (input.trans word.symm)
        (fun cut lower upper => commandFree cut (by omega) upper) (by omega)
    exact ⟨moved, stamp ∘ expand, equal, retained.trans later, schedule, final, commands.trans word,
      StageSimulation.Related.trans (Q := Eq) (fun a b => a.trans b) first endpoint, opened, settled, firstPath.trans restPath⟩

/-- If one open execution has a prefix of all its external commands,
the shared input determines a full common schedule. The other execution
may interleave its commands with activations before alignment. -/
theorem align_commands_first {leftLength rightLength split : Nat}
    (left : Trace (encodeProgram typedProgram) leftLength) (right : Trace (encodeProgram typedProgram) rightLength)
    (bounded : split ≤ leftLength)
    (leftOpen : ¬ Nonempty (ClosedEpisode left)) (leftQuiet : Progress.Quiet (left.state leftLength))
    (rightOpen : ¬ Nonempty (ClosedEpisode right)) (rightQuiet : Progress.Quiet (right.state rightLength))
    (continuations : ChildContinuations (encodeProgram typedProgram))
    (input : orchestrationInput left = orchestrationInput right)
    (prefixCommands : ∀ cut, cut < split → ∃ cmd, left.event cut = .command cmd)
    (suffixActivations : ∀ cut, split ≤ cut → cut < leftLength → ∃ kind name, left.event cut = .lifecycle kind name)
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r) :
    letI : Setoid A := TypedCoeffectReplay.setoid observe
    ∃ (moved : Trace (encodeProgram typedProgram) rightLength) (expand : Nat → Nat),
      leftLength = rightLength ∧ StableActorAddresses right moved expand ∧
      (∀ cut, cut < leftLength → addressedEventAt left cut = addressedEventAt moved cut) ∧
      CutAgreement left moved leftLength ∧ orchestrationInput moved = orchestrationInput right ∧
      StageSimulation.Related Eq (right.state rightLength) (moved.state rightLength) ∧
      (¬ Nonempty (ClosedEpisode moved)) ∧ Progress.Quiet (moved.state rightLength) ∧
      ∃ (mid : Trace (encodeProgram typedProgram) rightLength) (commands activations : Nat → Nat),
        CommandExchangePath right mid commands ∧ ActivationExchangePath mid moved activations ∧
        expand = commands ∘ activations := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  have alignPrefix (cut : Nat) (within : cut ≤ split) :
      ∃ (mid : Trace (encodeProgram typedProgram) rightLength) (stamp : Nat → Nat),
        cut ≤ rightLength ∧ StableActorAddresses right mid stamp ∧
        (∀ i, i < cut → addressedEventAt left i = addressedEventAt mid i) ∧ CutAgreement left mid cut ∧
        orchestrationInput mid = orchestrationInput right ∧ mid.state rightLength = right.state rightLength ∧
        (¬ Nonempty (ClosedEpisode mid)) ∧ Progress.Quiet (mid.state rightLength) ∧ CommandExchangePath right mid stamp := by
    induction cut with
    | zero =>
      exact ⟨right, id, Nat.zero_le _, .refl right, fun _ impossible => by omega,
        match_open_prefix left right continuations 0 (Nat.zero_le _) (Nat.zero_le _) (fun _ impossible => by omega),
        rfl, rfl, rightOpen, rightQuiet, .refl right⟩
    | succ cut ih =>
      obtain ⟨mid, stamp, midBound, retained, past, current, word, midEnd, opened, settled, prefixPath⟩ := ih (by omega)
      obtain ⟨cmd, event⟩ := prefixCommands cut (by omega)
      have leftCut : cut < leftLength := by omega
      obtain ⟨moved, expand, rightCut, kept, matched, next, commands, endpoint, openOnly, quiet, movePath⟩ :=
        align_pending_command_with_path left mid leftCut midBound opened settled current continuations past (input.trans word.symm) event
      exact ⟨moved, stamp ∘ expand, by omega, retained.trans kept, matched, next, commands.trans word,
        endpoint.trans midEnd, openOnly, quiet, prefixPath.trans movePath⟩
  obtain ⟨mid, stamp, midBound, retained, past, current, word, midEnd, opened, settled, prefixPath⟩ := alignPrefix split (Nat.le_refl _)
  obtain ⟨moved, expand, equal, kept, schedule, final, commands, endpoint, openOnly, quiet, suffixPath⟩ :=
    align_command_free_suffix left mid bounded midBound leftOpen leftQuiet opened settled current continuations past
      (input.trans word.symm) suffixActivations observe recovery commutative respect
  exact ⟨moved, stamp ∘ expand, equal, retained.trans kept, schedule, final, commands.trans word,
    midEnd ▸ endpoint, openOnly, quiet, mid, stamp, expand, prefixPath, suffixPath, rfl⟩

end Cordis.Repairs.GuardedActivationAlignment
