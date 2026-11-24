import Cordis.Repairs.GuardedAddressSchedule

/-! An enabled surviving incarnation must take an activation in a quiet open history. -/
namespace Cordis.Repairs.GuardedActivationOccurrence
open Calculus Stages LegalHistory GuardedHistory GuardedBirthAddresses GuardedAddressSchedule
open GuardedScheduleMatching
open GuardedBirthMatching (recorded_birth born_unique)

universe u
variable {Name Key Value Code Error : Type u} [DecidableEq Name] [DecidableEq Key]
variable {program : Code → Instruction Name Key Value Code Error} {last : Nat}
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error

private def AwaitingActivation (state : R) (actor : Name) : Prop :=
  ∃ row view, state actor = some row ∧
    (row.phase = .inactive ∨ ∃ code word saved, row.phase = .reloading code word saved) ∧ Target state actor view

private theorem awaiting_at_activation (trace : Trace program last)
    (openOnly : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    {cut : Nat} (bounded : cut < last) {kind : Lifecycle} {actor : Name}
    (event : trace.event cut = .lifecycle kind actor) : AwaitingActivation (trace.state cut) actor := by
  obtain ⟨active, step⟩ := trace.activation_at openOnly quiet bounded event
  generalize selected : kind.rule = rule at active step
  generalize ending : trace.state (cut + 1) = after at step
  cases step with
  | begin _ _ row view found phase _ target => exact ⟨row, view, found, .inl phase, target⟩
  | iter _ _ _ row code acc view _ _ found phase target _
  | finish _ _ _ row code acc view _ found phase target _ =>
    exact ⟨row, view, found, .inr ⟨code, acc, view, phase⟩, target⟩
  | _ => simp [Transposition.Activation] at active

omit [DecidableEq Name] [DecidableEq Key] in
private theorem awaiting_transport {left right : R} (p : Renaming.Permutation Name) {actor : Name}
    (registry : Renaming.registry p (GuardedCutState.project left) = GuardedCutState.project right)
    (pending : AwaitingActivation left actor) : AwaitingActivation right (p.toFun actor) := by
  obtain ⟨row, view, found, status, target⟩ := pending
  have rows := congrFun registry (p.toFun actor)
  rw [Renaming.registry_at] at rows
  cases other : right (p.toFun actor) with
  | none => simp [GuardedCutState.project, found, other] at rows
  | some entry =>
    have rowEq : Renaming.fiber p (GuardedCutState.projectFiber actor row) =
        GuardedCutState.projectFiber (p.toFun actor) entry := by
      simpa [GuardedCutState.project, found, other] using rows
    have phases := congrArg Fiber.phase rowEq
    have targetMoved := (Renaming.target_iff p (GuardedCutState.project left) actor view).mpr
      ((GuardedCutState.project_target _ _ _).mpr target)
    rw [registry] at targetMoved
    refine ⟨entry, Renaming.view p view, other, ?_, (GuardedCutState.project_target _ _ _).mp targetMoved⟩
    rcases status with quiet | ⟨code, word, saved, reloading⟩
    · left
      cases phase : entry.phase <;>
        simp [GuardedCutState.projectFiber, GuardedCutState.projectPhase, Renaming.fiber, Renaming.phase, quiet, phase] at phases ⊢
    · right
      cases phase : entry.phase <;>
        simp [GuardedCutState.projectFiber, GuardedCutState.projectPhase, Renaming.fiber, Renaming.phase, reloading, phase] at phases ⊢

omit [DecidableEq Name] [DecidableEq Key] in
private theorem not_quiet_of_awaiting {state : R} {actor : Name} (pending : AwaitingActivation state actor) :
    ¬ Progress.Quiet state := by
  rintro quiet
  obtain ⟨row, view, found, phase, target⟩ := pending
  have settled := quiet actor row found
  rcases phase with inactive | ⟨code, word, saved, reloading⟩
  · rw [inactive] at settled
    exact settled view target
  · rwa [reloading] at settled

private theorem recorded_at_next (trace : Trace program last) {cut : Nat} (bounded : cut < last)
    {actor : Name} {birth : Nat} (tag : (trace.notes cut).1 actor = some birth)
    (present : trace.state (cut + 1) actor ≠ none) : (trace.notes (cut + 1)).1 actor = some birth := by
  rw [(trace.step cut bounded).2]
  change (trace.state (cut + 1) actor).map (fun _ => ((trace.notes cut).1 actor).getD (cut + 1)) = some birth
  rw [tag]
  cases found : trace.state (cut + 1) actor with
  | none => exact False.elim (present found)
  | some => rfl

/-- The addressed command word contains no retirement of an incarnation
that takes an activation in a quiet open history. Earlier retirement persists
through the lifetime, and later retirement cannot target an installed row. -/
theorem activating_address_not_retired (trace : Trace program last)
    (openOnly : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    {cut : Nat} (bounded : cut < last) {kind : Lifecycle} {actor : Name}
    (event : trace.event cut = .lifecycle kind actor)
    {birth : Nat} {path : Address} (tag : (trace.notes cut).1 actor = some birth)
    (address : Addressed trace birth path) (component : Component Key Code) :
    .retire path component ∉ orchestrationInput trace := by
  intro member
  obtain ⟨time, placed, key⟩ := List.mem_filterMap.mp member
  have inside := List.mem_range.mp placed
  cases label : trace.event time with
  | lifecycle => simp [commandAt, label] at key
  | command command =>
    cases command with
    | insert => simp [commandAt, label] at key
    | remove name =>
      obtain ⟨_, _, target⟩ := targetAt_command trace inside (.inr label)
      simp [commandAt, label, target] at key
    | retire name =>
      obtain ⟨addressed, part, target⟩ := targetAt_command trace inside (.inl label)
      have keyEq : AddressedCommand.retire (Name := Name) addressed part = .retire path component :=
        Option.some.inj (by simpa [commandAt, label, target] using key)
      have samePath := (AddressedCommand.retire.inj keyEq).1
      subst addressed
      obtain ⟨oldBirth, row, oldTag, oldAddress, found, _⟩ := (targetAt_eq_some trace).mp target
      have sameBirth := address.injective oldAddress rfl
      subst oldBirth
      have sameName := born_unique trace (recorded_birth trace (Nat.le_of_lt inside) oldTag).1
        (recorded_birth trace (Nat.le_of_lt bounded) tag).1
      subst name
      obtain ⟨active, executed⟩ := trace.activation_at openOnly quiet bounded event
      have command := (trace.step time inside).1
      rw [label] at command
      rcases Nat.lt_trichotomy time cut with earlier | rfl | later
      · obtain ⟨current, view, present, _, enabled⟩ := Transposition.activation_source program executed active
        have marked : (trace.state (time + 1) actor).map Fiber.retired = some true := by
          rw [command.2]
          simp [OrchestrationSorting.Command.apply, Calculus.retire, Calculus.modify, found]
        have residence := Incarnation.resident_of_birthAt ((trace.notes_eq cut (Nat.le_of_lt bounded)) ▸ tag)
        have stays := EpisodeBoundary.retired_through_residency trace.state
          (last := last) (fun i bound => transition_stable (trace.step i bound).1) residence
          (by have := (recorded_birth trace (Nat.le_of_lt inside) oldTag).2; omega)
          (by omega) (Nat.le_of_lt bounded) marked
        have retired : current.retired = true := by simpa [present] using stays
        simp [Target, present, retired] at enabled
      · rw [label] at event
        cases event
      · have installed := activation_installs_view executed active
        have still := trace.installed_through openOnly actor (by omega : cut + 1 ≤ time) (Nat.le_of_lt inside) installed
        exact installed (still ▸ trace.command_actor_inactive openOnly quiet inside label)

private theorem awaiting_next (trace : Trace program last)
    (openOnly : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    {cut : Nat} (bounded : cut < last) {actor : Name} {birth : Nat} {path : Address}
    (tag : (trace.notes cut).1 actor = some birth) (address : Addressed trace birth path)
    (noRetire : ∀ component, .retire path component ∉ orchestrationInput trace)
    (noAct : ∀ kind, trace.event cut ≠ .lifecycle kind actor)
    (pending : AwaitingActivation (trace.state cut) actor) :
    AwaitingActivation (trace.state (cut + 1)) actor ∧ (trace.notes (cut + 1)).1 actor = some birth ∧
      (trace.state (cut + 1) actor).map Fiber.phase = (trace.state cut actor).map Fiber.phase := by
  obtain ⟨row, view, found, phase, ready⟩ := pending
  have next : AwaitingActivation (trace.state (cut + 1)) actor ∧
      (trace.state (cut + 1) actor).map Fiber.phase = (trace.state cut actor).map Fiber.phase := by
    cases label : trace.event cut with
    | lifecycle kind name =>
      have different : actor ≠ name := fun same => noAct kind (same ▸ label)
      obtain ⟨active, step⟩ := trace.activation_at openOnly quiet bounded label
      obtain ⟨table, kept⟩ := Transposition.activation_other_table program step active actor row different found
      exact ⟨⟨_, view, kept, phase, Transposition.activation_target_forward program step active actor view different ready⟩,
        by simp only [kept, found, Option.map_some]⟩
    | command command =>
      have step := (trace.step cut bounded).1
      rw [label] at step
      cases command with
      | insert name component =>
        have absent : trace.state cut name = none := step.1.1
        have different : actor ≠ name := by
          intro same
          rw [← same, found] at absent
          cases absent
        rw [step.2]
        have kept := Transposition.put_other (trace.state cut) actor name (fresh component none) different
        exact ⟨⟨row, view, kept.trans found, phase,
          (Transposition.fresh_put_target _ _ _ _ _ different absent view).mpr ready⟩, congrArg (Option.map Fiber.phase) kept⟩
      | retire name =>
        have different : actor ≠ name := by
          rintro rfl
          have target := (targetAt_eq_some trace).mpr ⟨birth, row, tag, address, found, rfl⟩
          exact noRetire row.component (List.mem_filterMap.mpr ⟨cut, List.mem_range.mpr bounded,
            by simp [commandAt, label, target]⟩)
        rw [step.2]
        have kept := Transposition.retire_other (trace.state cut) actor name different
        exact ⟨⟨row, view, kept.trans found, phase,
          (Transposition.retire_target _ _ _ view different).mpr ready⟩, congrArg (Option.map Fiber.phase) kept⟩
      | remove name =>
        have removable : Removable (trace.state cut) name := step.1
        have different : actor ≠ name := by
          rintro rfl
          simp only [Removable, found] at removable
          simp [Target, found, removable.1] at ready
        rw [step.2]
        have kept := Transposition.erase_other (trace.state cut) actor name different
        exact ⟨⟨row, view, kept.trans found, phase,
          (Transposition.removable_erase_target _ _ _ different removable view).mpr ready⟩, congrArg (Option.map Fiber.phase) kept⟩
  have present : trace.state (cut + 1) actor ≠ none := by
    obtain ⟨_, _, found, _, _⟩ := next.1
    simp [found]
  exact ⟨next.1, recorded_at_next trace bounded tag present, next.2⟩

private theorem first_awaited_activation (trace : Trace program last)
    (openOnly : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    {start : Nat} (bounded : start ≤ last) {actor : Name} {birth : Nat} {path : Address}
    (tag : (trace.notes start).1 actor = some birth) (address : Addressed trace birth path)
    (noRetire : ∀ component, .retire path component ∉ orchestrationInput trace)
    (pending : AwaitingActivation (trace.state start) actor) :
    ∃ time kind, start ≤ time ∧ time < last ∧ trace.event time = .lifecycle kind actor ∧
      (trace.notes time).1 actor = some birth ∧
      (trace.state time actor).map Fiber.phase = (trace.state start actor).map Fiber.phase ∧
      (∀ cut, start ≤ cut → cut ≤ time → (trace.notes cut).1 actor = some birth ∧
        (trace.state cut actor).map Fiber.phase = (trace.state start actor).map Fiber.phase ∧
        ∃ view, Target (trace.state cut) actor view) ∧
      ∀ cut, start ≤ cut → cut < time → ∀ earlier, trace.event cut ≠ .lifecycle earlier actor := by
  classical
  have search (span : Nat) (endBound : start + span ≤ last) :
      (∃ time kind, start ≤ time ∧ time < start + span ∧ trace.event time = .lifecycle kind actor ∧
        (trace.notes time).1 actor = some birth ∧
        (trace.state time actor).map Fiber.phase = (trace.state start actor).map Fiber.phase ∧
        (∀ cut, start ≤ cut → cut ≤ time → (trace.notes cut).1 actor = some birth ∧
          (trace.state cut actor).map Fiber.phase = (trace.state start actor).map Fiber.phase ∧
          ∃ view, Target (trace.state cut) actor view) ∧
        ∀ cut, start ≤ cut → cut < time → ∀ earlier, trace.event cut ≠ .lifecycle earlier actor) ∨
      (AwaitingActivation (trace.state (start + span)) actor ∧ (trace.notes (start + span)).1 actor = some birth ∧
        (trace.state (start + span) actor).map Fiber.phase = (trace.state start actor).map Fiber.phase ∧
        (∀ cut, start ≤ cut → cut ≤ start + span → (trace.notes cut).1 actor = some birth ∧
          (trace.state cut actor).map Fiber.phase = (trace.state start actor).map Fiber.phase ∧
          ∃ view, Target (trace.state cut) actor view) ∧
        ∀ cut, start ≤ cut → cut < start + span → ∀ earlier, trace.event cut ≠ .lifecycle earlier actor) := by
    induction span with
    | zero =>
      refine .inr ⟨pending, tag, rfl, ?_, fun _ lower upper => by omega⟩
      intro cut lower upper
      obtain rfl : cut = start := by omega
      obtain ⟨_, view, _, _, target⟩ := pending
      exact ⟨tag, rfl, view, target⟩
    | succ span ih =>
      rcases ih (by omega) with ⟨time, kind, later, before, event, known, phaseEq, targets, first⟩ |
        ⟨still, known, phaseEq, targets, first⟩
      · exact .inl ⟨time, kind, later, by omega, event, known, phaseEq, targets, first⟩
      · by_cases next : ∃ kind, trace.event (start + span) = .lifecycle kind actor
        · obtain ⟨kind, event⟩ := next
          exact .inl ⟨start + span, kind, by omega, by omega, event, known, phaseEq, targets, first⟩
        · have excluded (kind : Lifecycle) : trace.event (start + span) ≠ .lifecycle kind actor := fun event => next ⟨kind, event⟩
          have ⟨moved, same, samePhase⟩ := awaiting_next trace openOnly quiet (by omega) known address noRetire excluded still
          refine .inr ⟨moved, same, samePhase.trans phaseEq, ?_, ?_⟩
          · intro cut lower upper
            by_cases latest : cut = start + (span + 1)
            · subst cut
              obtain ⟨_, view, _, _, target⟩ := moved
              exact ⟨same, samePhase.trans phaseEq, view, target⟩
            · exact targets cut lower (by omega)
          · intro cut lower upper earlier
            rcases Nat.eq_or_lt_of_le (by omega : cut ≤ start + span) with rfl | prior
            · exact excluded earlier
            · exact first cut lower prior earlier
  have lastCut : start + (last - start) = last := by omega
  rcases search (last - start) (by omega) with first | ⟨stalled, _, _, _, _⟩
  · simpa only [lastCut] using first
  · rw [lastCut] at stalled
    exact False.elim (not_quiet_of_awaiting stalled quiet)

/-- In the other trace, the matching live incarnation must take a next
activation. Equal surviving command input excludes its retirement, so a
foreign event cannot permanently disable it. The actor and its new event
position are derived from the actual histories. -/
theorem pending_activation_occurs {leftLength rightLength start : Nat}
    (left : Trace program leftLength) (right : Trace program rightLength)
    (leftBound : start < leftLength) (rightBound : start ≤ rightLength)
    (leftOpen : ¬ Nonempty (ClosedEpisode left)) (leftQuiet : Progress.Quiet (left.state leftLength))
    (rightOpen : ¬ Nonempty (ClosedEpisode right)) (rightQuiet : Progress.Quiet (right.state rightLength))
    (current : CutAgreement left right start)
    (past : ∀ cut, cut < start → addressedEventAt left cut = addressedEventAt right cut)
    (input : orchestrationInput left = orchestrationInput right)
    {kind : Lifecycle} {actor : Name} (event : left.event start = .lifecycle kind actor) :
    ∃ time otherKind other birth path,
      start ≤ time ∧ time < rightLength ∧ right.event time = .lifecycle otherKind other ∧
      (left.notes start).1 actor = some birth ∧ (right.notes start).1 other = some birth ∧
      (right.notes time).1 other = some birth ∧ Addressed left birth path ∧ Addressed right birth path ∧
      (right.state time other).map Fiber.phase = (right.state start other).map Fiber.phase ∧
      (∀ cut, start ≤ cut → cut ≤ time → (right.notes cut).1 other = some birth ∧
        (right.state cut other).map Fiber.phase = (right.state start other).map Fiber.phase ∧
        ∃ view, Target (right.state cut) other view) ∧
      ∀ cut, start ≤ cut → cut < time → ∀ earlier, right.event cut ≠ .lifecycle earlier other := by
  obtain ⟨p, registry, live, _⟩ := current
  have leftPending := awaiting_at_activation left leftOpen leftQuiet leftBound event
  have present : left.state start actor ≠ none := by
    obtain ⟨_, _, found, _, _⟩ := leftPending
    simp [found]
  cases tag : (left.notes start).1 actor with
  | none => exact False.elim (present ((left.births_agree start (Nat.le_of_lt leftBound) actor).mp tag))
  | some birth =>
    have rightTag : (right.notes start).1 (p.toFun actor) = some birth := (live actor).trans tag
    have first := recorded_birth left (Nat.le_of_lt leftBound) tag
    have second := recorded_birth right rightBound rightTag
    obtain ⟨path, leftPath⟩ := exists_address left first.1
    obtain ⟨otherPath, rightPath⟩ := exists_address right second.1
    have samePath := address_of_matched_birth left right past first.2 leftPath rightPath
    subst otherPath
    have noRetire (component : Component Key Code) : .retire path component ∉ orchestrationInput right := by
      rw [← input]
      exact activating_address_not_retired left leftOpen leftQuiet leftBound event tag leftPath component
    obtain ⟨time, otherKind, later, within, next, sameBorn, samePhase, targets, firstEvent⟩ := first_awaited_activation right rightOpen
      rightQuiet rightBound rightTag rightPath noRetire (awaiting_transport p registry leftPending)
    exact ⟨time, otherKind, p.toFun actor, birth, path, later, within, next, rfl, rightTag, sameBorn,
      leftPath, rightPath, samePhase, targets, firstEvent⟩

end Cordis.Repairs.GuardedActivationOccurrence
