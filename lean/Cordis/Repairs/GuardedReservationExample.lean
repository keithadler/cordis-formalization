import Cordis.Repairs.GuardedReservationOrder
import Cordis.Repairs.GuardedBirthExample
import Cordis.Repairs.ChildCommandConfluence
import Cordis.Repairs.GuardedAddressSchedule
import Cordis.Repairs.GuardedCommandAlignment
import Cordis.Repairs.GuardedActivationAlignment
import Cordis.Repairs.GuardedIncarnationRedraw

/-! Concrete addressed inputs for the different-target counterexample and
for a reservation that is released before its raw name is reused. -/
namespace Cordis.Repairs.GuardedReservationExample
open Calculus Stages LegalHistory GuardedHistory Incarnation
open GuardedBirthMatching GuardedBirthAddresses GuardedReservationOrder
open GuardedAddressSchedule (stable_addressed_command)
open GuardedScheduleMatching (CutAgreement match_open_prefix)
open GuardedCommandAlignment (align_pending_command command_input_of_activation_exchange)

section DifferentTargets
open ChildCommandConfluence

private theorem first_child_address (first : Bool) :
    Addressed (trace first) 4 (.child (.root (if first then 1 else 0)) 0) := by
  cases first
  · exact .child (time := 3) (name := 2) (parentBirth := 1)
      (by decide) rfl rfl (by change some _ ≠ none; simp) rfl
      (.root (time := 0) (by decide) rfl)
  · exact .child (time := 3) (name := 2) (parentBirth := 2)
      (by decide) rfl rfl (by change some _ ≠ none; simp) rfl
      (.root (time := 1) (by decide) rfl)

private theorem first_input (first : Bool) :
    orchestrationInput (trace first) =
      [.insert 0 (root false), .insert 1 (root true),
        .retire (.child (.root (if first then 1 else 0)) 0) (child first),
        .remove (.child (.root (if first then 1 else 0)) 0) (child first)] := by
  have retirement : targetAt (trace first) 4 2 =
      some (.child (.root (if first then 1 else 0)) 0, child first) := by
    apply (targetAt_eq_some _).mpr
    cases first
    · exact ⟨4, _, rfl, first_child_address false, rfl, rfl⟩
    · exact ⟨4, _, rfl, first_child_address true, rfl, rfl⟩
  have removal : targetAt (trace first) 5 2 =
      some (.child (.root (if first then 1 else 0)) 0, child first) := by
    apply (targetAt_eq_some _).mpr
    cases first
    · exact ⟨4, _, rfl, first_child_address false, rfl, rfl⟩
    · exact ⟨4, _, rfl, first_child_address true, rfl, rfl⟩
  have instructions (i : Nat) : (trace first).event i = events first i := rfl
  change ([0,1,2,3,4,5,6,7,8,9] : List Nat).filterMap (commandAt (trace first)) = _
  simp [commandAt, instructions, events, retirement, removal]

/-- Equal raw commands and birth stamp 4 select different addresses in
the existing pair of quiet histories. -/
theorem different_addressed_inputs :
    orchestrationInput (trace false) ≠ orchestrationInput (trace true) := by
  rw [first_input, first_input]
  simp

private theorem moved_stamp (source moved : Source) (point cut name birth : Nat)
    (same : source.notes cut = reindexNotes (ExchangeReplay.exchangedIndex point) (moved.notes cut))
    (original : (source.notes cut).1 name = some birth) :
    (moved.notes cut).1 name = some (ExchangeReplay.exchangedIndex point birth) := by
  have reverse := congrArg (reindexNotes (ExchangeReplay.exchangedIndex point)) same
  rw [reindexNotes_involutive _ (ExchangeReplay.exchangedIndex_involutive point)] at reverse
  have atName := congrArg (fun notes : Vestigial.CutNotes Nat Bool V => notes.1 name) reverse
  change ((source.notes cut).1 name).map (ExchangeReplay.exchangedIndex point) = _ at atName
  rw [original] at atName
  exact atName.symm

/-- Moving root Q's insertion after P's Begin and Finish changes P's
child birth from stamp 4 to stamp 3. The actual retire and remove retain
the same addressed orchestration input. -/
theorem changed_birth_stamp_same_input :
    ∃ (moved : Source) (expand : Nat → Nat), StableActorAddresses (trace false) moved expand ∧
      expand 3 = 4 ∧ orchestrationInput moved = orchestrationInput (trace false) ∧
      (moved.notes 4).1 2 = some 3 ∧ ((trace false).notes 4).1 2 = some 4 ∧
      moved.state 10 = (trace false).state 10 := by
  let source := trace false
  let insertion : OrchestrationSorting.Command Nat Bool Code := .insert 1 (root true)
  obtain ⟨mid, evMid, stateMid, notesMid, _, _, openMid, quietMid, retainedMid⟩ :=
    source.swap_activation_before_command (open_only false) (quiet false) (time := 1) (by decide)
      (command := insertion) (actor := 0) (kind := .begin) rfl rfl (show (0 : Nat) ≠ 1 by decide)
  have delayed : mid.event 2 = .command insertion := by rw [evMid]; rfl
  have finish : mid.event 3 = .lifecycle .finish 0 := by rw [evMid]; rfl
  obtain ⟨moved, _, stateMoved, notesMoved, _, _, _, _, retainedMoved⟩ :=
    mid.swap_activation_before_command openMid quietMid (time := 2) (by decide)
      delayed finish (show (0 : Nat) ≠ 1 by decide)
  have childFour : (moved.notes 4).1 2 = some 3 := by
    have first := moved_stamp source mid 1 4 2 4 (notesMid 4 (by decide) (by decide)) rfl
    exact moved_stamp mid moved 2 4 2 4 (notesMoved 4 (by decide) (by decide)) first
  have alignedMid := StableActorAddresses.adjacent (by decide) retainedMid (by decide) (by decide)
  have alignedMoved := StableActorAddresses.adjacent (by decide) retainedMoved (by simp [isRootInsertion, finish]) (by
    intro cannot _
    simp [Trace.rule, delayed, insertion, eventRule, ExchangeReplay.commandRule, EpisodeSelection.canBirth] at cannot)
  let expand := ExchangeReplay.exchangedIndex 1 ∘ ExchangeReplay.exchangedIndex 2
  have aligned : StableActorAddresses source moved expand := alignedMid.trans alignedMoved
  have addressed (i : Nat) (inside : i < 10) : commandAt moved i = commandAt source (expand (i + 1) - 1) :=
    stable_addressed_command aligned inside
  have endpoint : moved.state 10 = source.state 10 := by
    rw [stateMoved 10 (by decide), stateMid 10 (by decide)]
  refine ⟨moved, expand, aligned, rfl, ?_, childFour, rfl, endpoint⟩
  change ([0,1,2,3,4,5,6,7,8,9] : List Nat).filterMap (commandAt moved) =
    ([0,1,2,3,4,5,6,7,8,9] : List Nat).filterMap (commandAt source)
  simp only [List.filterMap_cons, List.filterMap_nil, addressed _ (by decide : 0 < 10), addressed _ (by decide : 1 < 10),
    addressed _ (by decide : 2 < 10), addressed _ (by decide : 3 < 10), addressed _ (by decide : 4 < 10),
    addressed _ (by decide : 5 < 10), addressed _ (by decide : 6 < 10), addressed _ (by decide : 7 < 10),
    addressed _ (by decide : 8 < 10), addressed _ (by decide : 9 < 10)]
  rfl

/-- A pending child removal can cross a foreign Begin after the matched
prefix has already identified the child incarnation. -/
theorem align_removal_after_foreign_begin :
    ∃ delayed aligned : Source,
      delayed.event 5 = .lifecycle .begin 1 ∧ delayed.event 6 = .command (.remove 2) ∧
      orchestrationInput delayed = orchestrationInput (trace false) ∧
      CutAgreement (trace false) aligned 6 ∧ aligned.state 10 = (trace false).state 10 ∧
      ∃ earlier : Source, earlier.event 5 = .lifecycle .begin 1 ∧
        orchestrationInput earlier = orchestrationInput (trace false) := by
  let source := trace false
  have allowed : Vestigial.CompatibleBirths (source.state 5) (source.state 7) 2 := by
    intro name row vacant found
    have endpoint : source.state 7 = mark (erase (source.state 5) 2) 1 (openedRoot true).phase := rfl
    have absent := (Transposition.mark_presence (erase (source.state 5) 2) 1 name (openedRoot true).phase).mpr vacant
    rw [endpoint, absent] at found
    cases found
  obtain ⟨delayed, labels, states, _, _, _, opened, settled, retained⟩ :=
    source.swap_activation_before_command (open_only false) (quiet false) (time := 5) (by decide)
      (command := .remove 2) (kind := .begin) (actor := 1) rfl rfl allowed
  have address := StableActorAddresses.adjacent (by decide) retained (by decide) (by decide)
  have input := command_input_of_activation_exchange address (by decide) (.inr ⟨.begin, 1, rfl⟩)
  have prior (cut : Nat) (inside : cut < 5) :
      GuardedAddressSchedule.addressedEventAt source cut = GuardedAddressSchedule.addressedEventAt delayed cut := by
    have moved := GuardedAddressSchedule.stable_addressed_event address (cut := cut) (by omega)
    rw [ExchangeReplay.exchangedIndex_other (by omega : cut + 1 ≠ 5 + 1) (by omega : cut + 1 ≠ 5 + 2),
      Nat.add_sub_cancel] at moved
    exact moved.symm
  have stable : GuardedLandingMatching.ChildContinuations program := by intro code _ _ _ _; cases code <;> rfl
  have current : CutAgreement source delayed 5 := by
    apply match_open_prefix source delayed stable 5 (by decide) (by decide)
    intro cut bounded
    exact GuardedAddressSchedule.match_addressed_event source delayed (by omega) (by omega)
      (fun event => (source.activation_at (open_only false) (quiet false) (by omega) event).1)
      (fun event => (delayed.activation_at opened settled (by omega) event).1)
      (fun earlier before => prior earlier (by omega)) (prior cut bounded)
  obtain ⟨aligned, _, _, _, _, compared, _, endpoint, _, _⟩ :=
    align_pending_command source delayed (start := 5) (by decide) (by decide) opened settled current stable prior input.symm
      (command := .remove 2) rfl
  have symmetricCurrent : CutAgreement delayed source 5 := by
    apply match_open_prefix delayed source stable 5 (by decide) (by decide)
    intro cut bounded
    exact GuardedAddressSchedule.match_addressed_event delayed source (by omega) (by omega)
      (fun event => (delayed.activation_at opened settled (by omega) event).1)
      (fun event => (source.activation_at (open_only false) (quiet false) (by omega) event).1)
      (fun earlier before => (prior earlier (by omega)).symm) (prior cut bounded).symm
  have beginEvent : delayed.event 5 = .lifecycle .begin 1 := by rw [labels]; rfl
  have firstAligned : ∃ earlier : Source, earlier.event 5 = .lifecycle .begin 1 ∧
      orchestrationInput earlier = orchestrationInput source := by
    have prefixEq := Trace.agree_prefix (by decide : 5 ≤ 10)
      (fun i hi => states i (by omega)) (fun i hi => by simp [labels, show i ≠ 5 by omega, show i ≠ 6 by omega]) 5 (by decide)
    have pending : (delayed.notes 5).1 1 = some 2 := by rw [prefixEq.2]; rfl
    have priorInsertion : delayed.event 1 = .command (.insert 1 (root true)) := by rw [labels]; rfl
    have firstInsertion : delayed.event 0 = .command (.insert 0 (root false)) := by rw [labels]; rfl
    have addressed : Addressed delayed 2 (.root 1) := by
      simpa [occurrencesBefore, isRootInsertion, firstInsertion] using
        Addressed.root (time := 1) (by decide : 1 < 10) priorInsertion
    have earlierRoot : Addressed source 2 (.root 1) := .root (time := 1) (by decide) rfl
    have waits (i : Nat) (lower : 5 ≤ i) (upper : i < 6) (kind : Lifecycle) :
        source.event i ≠ .lifecycle kind 1 := by
      obtain rfl : i = 5 := by omega
      exact fun impossible => Event.noConfusion impossible
    have ready : ∃ selected, Target (source.state 5) 1 selected := by
      refine ⟨view, ?_⟩
      change false = false ∧ ∀ key, false = true → _
      exact ⟨rfl, fun _ impossible => Bool.noConfusion impossible⟩
    let observe (_ : Bool) : Setoid Nat := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
    rcases GuardedActivationAlignment.move_waiting_activation_one_step delayed source (start := 5) (cut := 5)
      (by decide) (by decide) (by decide) opened settled (open_only false) (quiet false) symmetricCurrent
      (fun cut before => (prior cut before).symm) input beginEvent (show source.event 6 = .lifecycle .begin 1 from rfl)
      pending rfl rfl addressed earlierRoot rfl waits ready observe
      (fun _ action => nomatch action) (fun _ action => nomatch action) (fun _ action => nomatch action)
      with ⟨earlier, _, _, _, began, commands, _, _, _⟩ | ⟨removed, erased, rebound⟩
    · exact ⟨earlier, began, commands⟩
    · have named : (2 : Nat) = removed := OrchestrationSorting.Command.remove.inj (Event.command.inj erased)
      subst removed
      exact False.elim (rebound rfl)
  exact ⟨delayed, aligned, by rw [labels]; rfl, by rw [labels]; rfl, input, compared,
    endpoint.trans (states 10 (by decide)), firstAligned⟩

/-- Redraw the first child to name 3, which the other parent will later use.
The retirement saved by the first parent remains tied to its original
birth, and applying it leaves the later live child untouched. -/
theorem redraw_then_reuse_same_name :
    ∃ moved : Source,
      orchestrationInput moved = orchestrationInput (trace false) ∧
      (moved.notes 4).1 3 = some 4 ∧ (moved.notes 10).1 3 = some 8 ∧
      (⟨.retire 3, 4⟩ : IncarnationReplay.Capture Nat Bool V) ∈ (moved.notes 10).2 0 ∧
      IncarnationReplay.Capture.apply (moved.notes 10).1 ⟨.retire 3, 4⟩ (moved.state 10) = moved.state 10 ∧
      CutAgreement (trace false) moved 10 := by
  let source := trace false
  have life : Lifetime source 2 4 5 := lifetime_of_removal source (by decide) rfl rfl
  have stable : GuardedLandingMatching.ChildContinuations program := by intro code _ _ _ _; cases code <;> rfl
  have reserved (time : Nat) (lower : 4 - 1 ≤ time) (upper : time ≤ 5 + 1) (_ : time ≤ 10) :
      source.state time 3 = none := by
    have possible : time = 3 ∨ time = 4 ∨ time = 5 ∨ time = 6 := by omega
    rcases possible with rfl | rfl | rfl | rfl <;> rfl
  obtain ⟨moved, word, _, _, _, later, finish, _, _, _, born, captured, endpoint, opened, quiet, _, _⟩ :=
    GuardedIncarnationRedraw.redraw_child_incarnation source (open_only false) (ChildCommandConfluence.quiet false)
      stable (fresh := 3) life (by decide) (show source.event 3 = .lifecycle .finish 0 from rfl) reserved
  have tag : (moved.notes 10).1 3 = some 8 := by rw [later 10 (by decide) (by decide)]; rfl
  have actor : moved.actor 3 = 0 := by simp [Trace.actor, Vestigial.eventActor, finish]
  rw [actor] at captured
  obtain ⟨active, step⟩ := moved.activation_at opened quiet (by decide) finish
  have installed := activation_installs_view step active
  have remains (point : Nat) (order : 4 < point) (within : point ≤ 10) :
      ControlFrame.viewAt (moved.state point) 0 ≠ none := by
    rw [moved.installed_through opened 0 (by omega : 4 ≤ point) within installed]
    exact installed
  have kept := moved.capture_through_interval 0 (by decide : 4 ≤ 10) (by decide : 10 ≤ 10) remains captured
  exact ⟨moved, word, born, tag, kept, by simp [IncarnationReplay.Capture.apply, tag], endpoint⟩

end DifferentTargets

section Reuse
open CommandBarrier (parentComponent providerComponent)

private abbrev reused (second : Bool) := GuardedBirthExample.trace (if second then 2 else 1)
  (by cases second <;> decide)

private theorem child_address (second : Bool) : Addressed (reused second) 3 (.child (.root 0) 0) := by
  cases second
  · exact .child (time := 2) (name := 1) (parentBirth := 1)
      (by decide) rfl rfl (by change some _ ≠ none; simp) rfl (.root (time := 0) (by decide) rfl)
  · exact .child (time := 2) (name := 2) (parentBirth := 1)
      (by decide) rfl rfl (by change some _ ≠ none; simp) rfl (.root (time := 0) (by decide) rfl)

private theorem reissued_address (second : Bool) : Addressed (reused second) 6 (.root 1) := by
  cases second
  · exact .root (time := 5) (by decide) rfl
  · exact .root (time := 5) (by decide) rfl

private theorem recognises_commands (second : Bool) : orchestrationInput (reused second) =
    [.insert 0 parentComponent, .retire (.child (.root 0) 0) providerComponent,
      .remove (.child (.root 0) 0) providerComponent, .insert 1 providerComponent,
      .retire (.root 0) parentComponent] := by
  let child : Nat := if second then 2 else 1
  have retired : targetAt (reused second) 3 child = some (.child (.root 0) 0, providerComponent) := by
    apply (targetAt_eq_some _).mpr
    cases second
    · exact ⟨3, _, rfl, child_address false, rfl, rfl⟩
    · exact ⟨3, _, rfl, child_address true, rfl, rfl⟩
  have removed : targetAt (reused second) 4 child = some (.child (.root 0) 0, providerComponent) := by
    apply (targetAt_eq_some _).mpr
    cases second
    · exact ⟨3, _, rfl, child_address false, rfl, rfl⟩
    · exact ⟨3, _, rfl, child_address true, rfl, rfl⟩
  have parent : targetAt (reused second) 6 0 = some (.root 0, parentComponent) := by
    apply (targetAt_eq_some _).mpr
    cases second
    · exact ⟨1, _, rfl, .root (time := 0) (by decide) rfl, rfl, rfl⟩
    · exact ⟨1, _, rfl, .root (time := 0) (by decide) rfl, rfl, rfl⟩
  have e0 : (reused second).event 0 = .command (.insert 0 parentComponent) := rfl
  have e1 : (reused second).event 1 = .lifecycle .begin 0 := rfl
  have e2 : (reused second).event 2 = .lifecycle .finish 0 := rfl
  have e3 : (reused second).event 3 = .command (.retire child) := rfl
  have e4 : (reused second).event 4 = .command (.remove child) := rfl
  have e5 : (reused second).event 5 = .command (.insert 1 providerComponent) := rfl
  have e6 : (reused second).event 6 = .command (.retire 0) := rfl
  have e7 : (reused second).event 7 = .lifecycle .leave 0 := rfl
  have e8 : (reused second).event 8 = .lifecycle .unload 0 := rfl
  change ([0,1,2,3,4,5,6,7,8] : List Nat).filterMap (commandAt (reused second)) = _
  simp [commandAt, e0, e1, e2, e3, e4, e5, e6, e7, e8, retired, removed, parent]

private def childReservation (second : Bool) : Reservation (reused second) () where
  name := if second then 2 else 1
  birth := 3
  final := 4
  address := .child (.root 0) 0
  life := lifetime_of_removal (reused second) (by decide) rfl (by cases second <;> rfl)
  addressed := child_address second
  reserves := by cases second <;> exact ⟨_, rfl, rfl⟩

private def rootReservation (second : Bool) : Reservation (reused second) () where
  name := 1
  birth := 6
  final := 9
  address := .root 1
  life := ⟨resident_of_birthAt (by cases second <;> rfl), Nat.le_refl _, fun conflict =>
    False.elim (Nat.lt_irrefl _ conflict)⟩
  addressed := reissued_address second
  reserves := by cases second <;> exact ⟨_, rfl, rfl⟩

/-- Removal of the earlier reservation enables insertion of the later
root in both histories. The child draws are different, and one source
reuses the old child's raw name for that root. -/
theorem same_input_through_name_reuse :
    orchestrationInput (reused false) = orchestrationInput (reused true) ∧
      releaseRank (reused false) (.child (.root 0) 0) < releaseRank (reused false) (.root 1) ∧
      releaseRank (reused true) (.child (.root 0) 0) < releaseRank (reused true) (.root 1) ∧
      (reused false).event 4 = .command (.remove 1) ∧ (reused true).event 4 = .command (.remove 2) := by
  have heads (second : Bool) : (childReservation second).address ≠ (rootReservation second).address :=
    fun impossible => Address.noConfusion impossible
  obtain ⟨_, first, _⟩ := (childReservation false).release_before_birth (rootReservation false) (by decide)
  obtain ⟨_, second, _⟩ := (childReservation true).release_before_birth (rootReservation true) (by decide)
  exact ⟨(recognises_commands false).trans (recognises_commands true).symm,
    ((childReservation false).birth_order (rootReservation false) (heads false)).mp (by decide),
    ((childReservation true).birth_order (rootReservation true) (heads true)).mp (by decide), first, second⟩

end Reuse
end Cordis.Repairs.GuardedReservationExample
