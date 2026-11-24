import Cordis.Repairs.GuardedIncarnationRedraw

/-! Match complete open schedules by moving the next command or activation.
Fresh redraws let each pending activation cross its remaining removal barriers. -/
namespace Cordis.Repairs.GuardedCompleteAlignment
open Calculus Stages LegalHistory GuardedHistory GuardedCutState
open GuardedAddressSchedule GuardedBirthAddresses GuardedScheduleMatching
open GuardedLandingMatching (ChildContinuations)
open GuardedBirthMatching (born_unique recorded_birth)
open GuardedActivationOccurrence (pending_activation_occurs)
open GuardedActivationAlignment (ActivationExchangePath AdjacentActivationExchange
  align_next_activation_with_path move_waiting_activation_one_step_with_exchange)
open GuardedIncarnationRedraw (cross_reuse_with_local_redraw redraw_child_incarnation spare_of_finite_history ConsistentRedraw)
open GuardedCommandAlignment (CommandExchangePath matched_endpoint_is_terminal)
open PaperEffectEquations (CoeffectOperations ValueOperationWitness)
open PaperObservationEquations (OperationRespects)
open PartialCoeffectIndependenceContracts (tableSetoid)
open TypedRegistry (encodeProgram Scalar)

universe u
variable {Name Key Code : Type u} [DecidableEq Name] [DecidableEq Key]
variable {V : Key → Type u} {ops : CoeffectOperations V}
variable {program : Code → TypedRegistry.Instruction Name ops Code}
local notation "A" => Scalar ops

/-- A path inside the original name set. Adjacent swaps retain their
local certificates, and a redraw retains its addressed order and
renaming agreement. -/
inductive ScheduleAlignmentPath [Setoid A] {length : Nat} :
    Trace (encodeProgram program) length → Trace (encodeProgram program) length → Prop
  | refl (trace : Trace (encodeProgram program) length) : ScheduleAlignmentPath trace trace
  | command {before after : Trace (encodeProgram program) length} {expand : Nat → Nat} :
      CommandExchangePath before after expand → ScheduleAlignmentPath before after
  | activation {before after : Trace (encodeProgram program) length} {expand : Nat → Nat} :
      ActivationExchangePath before after expand →
      StageSimulation.Related Eq (before.state length) (after.state length) →
      ScheduleAlignmentPath before after
  | swap {before after : Trace (encodeProgram program) length} {cut : Nat} :
      AdjacentActivationExchange before after cut → ScheduleAlignmentPath before after
  | redraw {before after : Trace (encodeProgram program) length} :
      CutAgreement before after length →
      orchestrationInput after = orchestrationInput before →
      addressedEvents after = addressedEvents before →
      ConsistentRedraw before after →
      ScheduleAlignmentPath before after
  | reverse {before after : Trace (encodeProgram program) length} :
      ScheduleAlignmentPath before after → ScheduleAlignmentPath after before
  | trans {before middle after : Trace (encodeProgram program) length} :
      ScheduleAlignmentPath before middle → ScheduleAlignmentPath middle after →
      ScheduleAlignmentPath before after

/-- Every composed alignment path preserves endpoint observations and
the multiset of addressed events. -/
theorem ScheduleAlignmentPath.preserves [Setoid A] {length : Nat}
    {before after : Trace (encodeProgram program) length} (path : ScheduleAlignmentPath before after) :
    ProjectedAgreement (before.state length) (after.state length) ∧
      (addressedEvents after).Perm (addressedEvents before) := by
  induction path with
  | refl trace => exact ⟨ProjectedAgreement.refl _, .refl _⟩
  | command exchanges =>
    obtain ⟨endpoint, _, addresses⟩ := exchanges.preserves
    exact ⟨endpoint.symm ▸ ProjectedAgreement.refl _, addressedEvents_perm_of_stable addresses⟩
  | activation exchanges endpoint =>
    obtain ⟨addresses, _⟩ := exchanges.preserves
      (StageSimulation.Related.trans (Q := Eq) (fun a b => a.trans b)
        (endpoint.symm (fun _ _ h => h.symm)) endpoint)
    exact ⟨.of_related endpoint, addressedEvents_perm_of_stable addresses⟩
  | swap exchange => exact ⟨.of_related exchange.endpoint, addressedEvents_perm_of_stable exchange.addresses⟩
  | redraw agreement _ events _ =>
    obtain ⟨_, endpoint, _, _⟩ := agreement
    exact ⟨.of_rename_eq endpoint, List.Perm.of_eq events⟩
  | reverse _ ih => exact ⟨ih.1.symm, ih.2.symm⟩
  | trans _ _ first second => exact ⟨first.1.trans second.1, second.2.trans first.2⟩

/-- Every intermediate schedule in a certified path can inherit
openness and endpoint quiescence from its source. -/
theorem ScheduleAlignmentPath.open_quiet [Setoid A] {length : Nat}
    {before after : Trace (encodeProgram program) length} (path : ScheduleAlignmentPath before after)
    (openOnly : ¬ Nonempty (ClosedEpisode before)) (quiet : Progress.Quiet (before.state length)) :
    (¬ Nonempty (ClosedEpisode after)) ∧ Progress.Quiet (after.state length) := by
  obtain ⟨⟨names, compared⟩, events⟩ := path.preserves
  have projected := (project_quiet_iff _).mpr quiet
  have renamed := GuardedRenaming.quiet_transport names projected
  exact ⟨open_of_addressed_events_perm events openOnly,
    (project_quiet_iff _).mp (quiet_of_related compared renamed)⟩

/-- A certified path preserves the birth addresses of its active endpoint
rows, including across redraws and reversed exchanges. -/
theorem ScheduleAlignmentPath.active_endpoint_addresses [Setoid A] {length : Nat}
    {before after : Trace (encodeProgram program) length} (path : ScheduleAlignmentPath before after)
    (openOnly : ¬ Nonempty (ClosedEpisode before)) (quiet : Progress.Quiet (before.state length))
    (address : Address) :
    (∃ name row birth, before.state length name = some row ∧ row.phase.available ∧
      (before.notes length).1 name = some birth ∧ Addressed before birth address) ↔
    (∃ name row birth, after.state length name = some row ∧ row.phase.available ∧
      (after.notes length).1 name = some birth ∧ Addressed after birth address) := by
  obtain ⟨afterOpen, afterQuiet⟩ := path.open_quiet openOnly quiet
  exact (addressed_finish_iff_active before openOnly quiet address).symm.trans
    (path.preserves.2.mem_iff.symm.trans (addressed_finish_iff_active after afterOpen afterQuiet address))

/-- At a matched active birth address, a certified path preserves the
component and compares each binding using the value observation. -/
theorem ScheduleAlignmentPath.active_endpoint_payload [Setoid A] {length : Nat}
    {before after : Trace (encodeProgram program) length} (path : ScheduleAlignmentPath before after)
    {address : Address} :
    (¬ Nonempty (ClosedEpisode before)) → Progress.Quiet (before.state length) →
    ∀ {name peer row other}, ActiveEndpoint before address name row → ActiveEndpoint after address peer other →
      row.component = other.component ∧
        ∀ key, Iterators.OptionRel (fun a b : A => a ≈ b) (row.table key) (other.table key) := by
  induction path with
  | refl trace =>
    intro _ _ _ _ row _ first second
    obtain ⟨_, rfl⟩ := first.unique second
    exact ⟨rfl, fun key => by cases row.table key <;> simp [Iterators.OptionRel, Setoid.refl]⟩
  | command moves =>
    intro opened quiet _ _ _ _ first second
    obtain ⟨endpoint, _, stable⟩ := moves.preserves
    obtain ⟨afterOpen, afterQuiet⟩ := (ScheduleAlignmentPath.command moves).open_quiet opened quiet
    exact stable_active_endpoint_payload stable (endpoint.symm ▸ project_self_related _)
      opened quiet afterOpen afterQuiet first second
  | activation moves endpoint =>
    intro opened quiet _ _ _ _ first second
    have stable := (moves.preserves
      (StageSimulation.Related.trans (Q := Eq) (fun a b => a.trans b)
        (endpoint.symm (fun _ _ h => h.symm)) endpoint)).1
    obtain ⟨afterOpen, afterQuiet⟩ := (ScheduleAlignmentPath.activation moves endpoint).open_quiet opened quiet
    exact stable_active_endpoint_payload stable (project_related endpoint) opened quiet afterOpen afterQuiet first second
  | swap exchange =>
    intro opened quiet _ _ _ _ first second
    obtain ⟨afterOpen, afterQuiet⟩ := (ScheduleAlignmentPath.swap exchange).open_quiet opened quiet
    exact stable_active_endpoint_payload exchange.addresses (project_related exchange.endpoint) opened quiet afterOpen afterQuiet first second
  | redraw _ _ _ redraw =>
    intro _ _ _ _ row _ first second
    obtain ⟨component, tables⟩ := redraw.active_endpoint_payload first second
    refine ⟨component, fun key => ?_⟩
    rw [← tables]
    cases row.table key <;> simp [Iterators.OptionRel, Setoid.refl]
  | reverse forwards ih =>
    intro opened quiet _ _ _ _ first second
    obtain ⟨beforeOpen, beforeQuiet⟩ := (ScheduleAlignmentPath.reverse forwards).open_quiet opened quiet
    obtain ⟨component, tables⟩ := ih beforeOpen beforeQuiet second first
    exact ⟨component.symm, fun key => Iterators.OptionRel.mono (fun _ _ h => Setoid.symm h)
      (Iterators.OptionRel.symm (tables key))⟩
  | trans earlier later ihEarlier ihLater =>
    intro opened quiet name _ row _ first second
    obtain ⟨middleOpen, middleQuiet⟩ := earlier.open_quiet opened quiet
    obtain ⟨birth, tag, known⟩ := first.2.2
    obtain ⟨middleName, middleRow, middleBirth, present, active, middleTag, middleAddress⟩ :=
      (earlier.active_endpoint_addresses opened quiet address).mp ⟨name, row, birth, first.1, first.2.1, tag, known⟩
    have middle : ActiveEndpoint _ address middleName middleRow :=
      ⟨present, active, middleBirth, middleTag, middleAddress⟩
    obtain ⟨leftComponent, leftTables⟩ := ihEarlier opened quiet first middle
    obtain ⟨rightComponent, rightTables⟩ := ihLater middleOpen middleQuiet middle second
    exact ⟨leftComponent.trans rightComponent, fun key =>
      Iterators.OptionRel.trans (R := fun a b : A => a ≈ b) (fun _ _ _ h j => Setoid.trans h j) (leftTables key) (rightTables key)⟩

/-- Available providers of the same key at any two cuts of schedules
connected by a certified path have the same birth address. Availability
makes both reservations persist, and the endpoint has only one reservation
of the key. The cuts may precede different command prefixes. -/
theorem ScheduleAlignmentPath.available_providers_match [Setoid A] {length : Nat}
    {before after : Trace (encodeProgram program) length} (path : ScheduleAlignmentPath before after)
    (opened : ¬ Nonempty (ClosedEpisode before)) (quiet : Progress.Quiet (before.state length))
    {leftCut rightCut : Nat} (leftBound : leftCut ≤ length) (rightBound : rightCut ≤ length)
    {name peer : Name} {key : Key}
    {row : Fiber Name Key A Code (Inverse Name Key A) PUnit.{u + 1}}
    {other : Fiber Name Key A Code (Inverse Name Key A) PUnit.{u + 1}}
    (found : before.state leftCut name = some row) (active : row.phase.available)
    (reserves : row.component.provides key = true)
    (otherFound : after.state rightCut peer = some other) (otherActive : other.phase.available)
    (otherReserves : other.component.provides key = true) :
    ∃ address birth otherBirth, (before.notes leftCut).1 name = some birth ∧
      (after.notes rightCut).1 peer = some otherBirth ∧
      Addressed before birth address ∧ Addressed after otherBirth address := by
  obtain ⟨afterOpen, afterQuiet⟩ := path.open_quiet opened quiet
  exact available_providers_of_endpoint_comparison opened quiet afterOpen afterQuiet path.preserves.2.symm
    (fun first second => (path.active_endpoint_payload opened quiet first second).1)
    leftBound rightBound found active reserves otherFound otherActive otherReserves

/-- Two valid targets in schedules connected by a certified path
select the same provider incarnation at a shared required key. -/
theorem ScheduleAlignmentPath.selected_providers_match [Setoid A] {length : Nat}
    {before after : Trace (encodeProgram program) length} (path : ScheduleAlignmentPath before after)
    (opened : ¬ Nonempty (ClosedEpisode before)) (quiet : Progress.Quiet (before.state length))
    {leftCut rightCut : Nat} (leftBound : leftCut ≤ length) (rightBound : rightCut ≤ length)
    {name peer : Name} {key : Key} {leftView rightView : View Name Key}
    {row other : Fiber Name Key A Code (Inverse Name Key A) PUnit.{u + 1}}
    (found : before.state leftCut name = some row) (needed : row.component.requires key = true)
    (leftTarget : Target (before.state leftCut) name leftView)
    (otherFound : after.state rightCut peer = some other) (otherNeeded : other.component.requires key = true)
    (rightTarget : Target (after.state rightCut) peer rightView) :
    ∃ address birth otherBirth, (before.notes leftCut).1 (leftView key) = some birth ∧
      (after.notes rightCut).1 (rightView key) = some otherBirth ∧
      Addressed before birth address ∧ Addressed after otherBirth address := by
  obtain ⟨_, provider, active, reserves⟩ := selected_provider_at_cut leftBound found needed leftTarget
  obtain ⟨_, otherProvider, otherActive, otherReserves⟩ := selected_provider_at_cut rightBound otherFound otherNeeded rightTarget
  exact path.available_providers_match opened quiet leftBound rightBound
    provider active reserves otherProvider otherActive otherReserves

/-- Traversing a certified exchange in either direction preserves every
command's address and its position in the command word. -/
theorem ScheduleAlignmentPath.input_eq [Setoid A] {length : Nat}
    {before after : Trace (encodeProgram program) length} (path : ScheduleAlignmentPath before after) :
    orchestrationInput after = orchestrationInput before := by
  induction path with
  | refl => rfl
  | command moves => exact moves.input_eq
  | activation moves _ => exact moves.input_eq
  | swap exchange => exact exchange.input
  | redraw _ same _ _ => exact same
  | reverse _ ih => exact ih.symm
  | trans _ _ first second => exact second.trans first

/-- An identical addressed schedule and command word certify a
consistent redraw within the original name set. -/
theorem path_of_same_addressed_schedule [Setoid A] {length : Nat}
    (left right : Trace (encodeProgram program) length)
    (leftOpen : ¬ Nonempty (ClosedEpisode left)) (leftQuiet : Progress.Quiet (left.state length))
    (rightOpen : ¬ Nonempty (ClosedEpisode right)) (rightQuiet : Progress.Quiet (right.state length))
    (stable : ChildContinuations (encodeProgram program))
    (input : orchestrationInput left = orchestrationInput right)
    (order : ∀ i, i < length → addressedEventAt left i = addressedEventAt right i) :
    ScheduleAlignmentPath left right := by
  have schedule := open_events_of_ordered_addresses left right leftOpen rightOpen leftQuiet rightQuiet order
  have roots (i : Nat) (name peer : Name) (component : Component Key Code) (bounded : i < length)
      (first : left.event i = .command (.insert name component))
      (second : right.event i = .command (.insert peer component)) : name = peer := by
    have same := GuardedCommandAlignment.next_commands_agree left right (span := 0)
      bounded (by omega) (fun cut before => order cut (by omega)) input first
      (by simpa using second) (fun _ lo hi => by omega)
    simpa [commandAt, first, second] using same
  exact .redraw (match_open_prefix left right stable length (Nat.le_refl _) (Nat.le_refl _) schedule)
    input.symm (addressedEvents_congr left right order).symm
    (GuardedIncarnationRedraw.consistent_redraw_of_open_events left right stable schedule roots)

/-- Align a birth and its following command when the peer's first
pending command waits for that same birth. Both exchanges take place
in the original name set. -/
theorem align_birth_and_dependent_command {leftLength rightLength start span : Nat}
    (left : Trace (encodeProgram program) leftLength) (right : Trace (encodeProgram program) rightLength)
    (leftBound : start + 1 < leftLength) (rightBound : start + span + 1 < rightLength)
    (leftOpen : ¬ Nonempty (ClosedEpisode left)) (leftQuiet : Progress.Quiet (left.state leftLength))
    (rightOpen : ¬ Nonempty (ClosedEpisode right)) (rightQuiet : Progress.Quiet (right.state rightLength))
    (rightNormal : GuardedCommandAlignment.CommandsAtBirthBarriersFrom right start)
    (current : CutAgreement left right start) (stable : ChildContinuations (encodeProgram program))
    (past : ∀ cut, cut < start → addressedEventAt left cut = addressedEventAt right cut)
    (input : orchestrationInput left = orchestrationInput right)
    {kind : Lifecycle} {actor : Name} (allocation : left.event start = .lifecycle kind actor)
    {first later : OrchestrationSorting.Command Name Key Code}
    (leftCommand : left.event (start + 1) = .command first)
    (leftBorn : GuardedBirthMatching.BornAt left first.actor (start + 1))
    (rightCommand : right.event (start + span + 1) = .command later)
    (block : ∀ cut, start ≤ cut → cut < start + span + 1 →
      ∃ label name, right.event cut = .lifecycle label name)
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r) :
    letI : Setoid A := TypedCoeffectReplay.setoid observe
    ∃ moved : Trace (encodeProgram program) rightLength,
      (∀ cut, cut < start + 2 → addressedEventAt left cut = addressedEventAt moved cut) ∧
      CutAgreement left moved (start + 2) ∧
      (¬ Nonempty (ClosedEpisode moved)) ∧ Progress.Quiet (moved.state rightLength) ∧
      ScheduleAlignmentPath right moved := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  have leftBlock (cut : Nat) (lower : start ≤ cut) (upper : cut < start + 1) :
      ∃ label name, left.event cut = .lifecycle label name := by
    obtain rfl : cut = start := by omega
    exact ⟨_, _, allocation⟩
  have rightBlock (cut : Nat) (lower : start ≤ cut) (upper : cut < start + (span + 1)) :=
    block cut lower (by omega)
  obtain ⟨_, _, rightBorn, _, _, _⟩ :=
    GuardedCommandAlignment.delayed_command_birth_at_suffix_frontier right (span := span + 1)
      (by omega) (by omega) rightNormal (by simpa only [Nat.add_assoc] using rightCommand) rightBlock
  obtain ⟨address, _, _, _, leftAddress, rightAddress, _, _⟩ :=
    GuardedCommandAlignment.commands_at_birth_cuts_share_target left right
      (leftSpan := 1) (rightSpan := span + 1) leftBound (by omega) past input
      leftCommand (by simpa only [Nat.add_assoc] using rightCommand) leftBorn rightBorn leftBlock rightBlock
  obtain ⟨otherKind, other, otherEvent⟩ := block (start + span) (by omega) (by omega)
  obtain ⟨mid, expand, aligned, boundary, commands, endpoint, openMid, quietMid, activationPath⟩ :=
    GuardedActivationAlignment.align_addressed_allocation_before_command left right
      (span := span) (by omega) (by omega) leftOpen leftQuiet rightOpen rightQuiet current stable past input
      allocation otherEvent leftBorn (by simpa only [Nat.add_assoc] using rightBorn)
      leftAddress (by simpa only [Nat.add_assoc] using rightAddress)
      (fun cut lower upper => block cut lower (by omega)) observe recovery commutative respect
  obtain ⟨moved, _, commandPath, _, _, _, _, _, word, final, opened, quiet⟩ :=
    GuardedCommandAlignment.normalize_suffix_to_match_pending_command left mid leftBound (by omega)
      openMid quietMid boundary stable aligned (input.trans commands.symm) leftCommand
  exact ⟨moved, word, final, opened, quiet, .trans (.activation activationPath endpoint) (.command commandPath)⟩

/-- Find and align the required birth and command from the common
prefix and command word. The peer's suffix and command position are
derived from certified exchanges on its actual history. -/
theorem align_required_birth_from_matched_cut {leftLength rightLength start : Nat}
    (left : Trace (encodeProgram program) leftLength) (right : Trace (encodeProgram program) rightLength)
    (leftBound : start + 1 < leftLength) (rightBound : start ≤ rightLength)
    (leftOpen : ¬ Nonempty (ClosedEpisode left)) (leftQuiet : Progress.Quiet (left.state leftLength))
    (rightOpen : ¬ Nonempty (ClosedEpisode right)) (rightQuiet : Progress.Quiet (right.state rightLength))
    (current : CutAgreement left right start) (stable : ChildContinuations (encodeProgram program))
    (past : ∀ cut, cut < start → addressedEventAt left cut = addressedEventAt right cut)
    (input : orchestrationInput left = orchestrationInput right)
    {kind : Lifecycle} {actor : Name} (allocation : left.event start = .lifecycle kind actor)
    {command : OrchestrationSorting.Command Name Key Code} (leftCommand : left.event (start + 1) = .command command)
    (leftBorn : GuardedBirthMatching.BornAt left command.actor (start + 1))
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r) :
    letI : Setoid A := TypedCoeffectReplay.setoid observe
    ∃ moved : Trace (encodeProgram program) rightLength,
      start + 2 ≤ rightLength ∧
      (∀ cut, cut < start + 2 → addressedEventAt left cut = addressedEventAt moved cut) ∧
      CutAgreement left moved (start + 2) ∧
      (¬ Nonempty (ClosedEpisode moved)) ∧ Progress.Quiet (moved.state rightLength) ∧
      ScheduleAlignmentPath right moved := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  obtain ⟨mid, _, normal, _, commands, _, _, opened, quiet, originalPath, cuts, _, addresses⟩ :=
    GuardedCommandAlignment.push_commands_to_birth_barriers_from right start rightOpen rightQuiet
  have earlier (cut : Nat) (before : cut < start) : addressedEventAt left cut = addressedEventAt mid cut :=
    (past cut before).trans (addresses cut before (by omega)).symm
  have nextInput := input.trans commands.symm
  have midCut : CutAgreement left mid start := by
    obtain ⟨names, states, stamps, saved⟩ := current
    obtain ⟨stateEq, noteEq⟩ := cuts start (Nat.le_refl _) rightBound
    refine ⟨names, stateEq.symm ▸ states, ?_, ?_⟩
    · simpa only [noteEq] using stamps
    · unfold GuardedBirthReplay.SavedMatch at saved ⊢
      simpa only [noteEq] using saved
  have leftBlock (cut : Nat) (lower : start ≤ cut) (upper : cut < start + 1) :
      ∃ label name, left.event cut = .lifecycle label name := by
    obtain rfl : cut = start := by omega
    exact ⟨_, _, allocation⟩
  obtain ⟨span, next, bounded, external, block⟩ :=
    GuardedCommandAlignment.pending_delayed_command_occurs left mid (leftSpan := 1) leftBound rightBound
      earlier nextInput leftCommand leftBlock
  cases span with
  | zero =>
    have atStart : mid.event start = .command next := external
    have matched : CutAgreement mid left start :=
      match_open_prefix mid left stable start rightBound (by omega) (fun cut before =>
        match_addressed_event mid left (by omega) (by omega)
          (fun event => (mid.activation_at opened quiet (by omega) event).1)
          (fun event => (left.activation_at leftOpen leftQuiet (by omega) event).1)
          (fun i earlierCut => (earlier i (by omega)).symm) (earlier cut before).symm)
    exact False.elim (GuardedCommandAlignment.newborn_command_excludes_immediate_peer left mid leftBound
      (by omega) matched earlier nextInput allocation leftCommand atStart leftBorn)
  | succ span =>
    obtain ⟨moved, ordered, final, openMoved, quietMoved, path⟩ :=
      align_birth_and_dependent_command left mid leftBound (span := span) (by omega)
        leftOpen leftQuiet opened quiet normal midCut stable earlier nextInput allocation
        leftCommand leftBorn (by simpa only [Nat.add_assoc] using external)
        (fun cut lo hi => block cut lo (by omega)) observe recovery commutative respect
    exact ⟨moved, by omega, ordered, final, openMoved, quietMoved, .trans (.command originalPath) path⟩

/-- If the reference's next step belongs to the parent needed by the
first delayed command, advance that parent's matching step in the
peer before crossing any command. -/
theorem align_stage_of_parent_needed_by_next_command {leftLength rightLength start leftSpan rightSpan : Nat}
    (left : Trace (encodeProgram program) leftLength) (right : Trace (encodeProgram program) rightLength)
    (leftBound : start + leftSpan + 1 < leftLength) (rightBound : start + rightSpan + 1 < rightLength)
    (leftOpen : ¬ Nonempty (ClosedEpisode left)) (leftQuiet : Progress.Quiet (left.state leftLength))
    (rightOpen : ¬ Nonempty (ClosedEpisode right)) (rightQuiet : Progress.Quiet (right.state rightLength))
    (leftNormal : GuardedCommandAlignment.CommandsAtBirthBarriersFrom left start)
    (rightNormal : GuardedCommandAlignment.CommandsAtBirthBarriersFrom right start)
    (current : CutAgreement left right start) (stable : ChildContinuations (encodeProgram program))
    (past : ∀ i, i < start → addressedEventAt left i = addressedEventAt right i)
    (input : orchestrationInput left = orchestrationInput right)
    {kind : Lifecycle} {actor : Name} (first : left.event start = .lifecycle kind actor)
    (sameParent : (left.notes start).1 actor = (left.notes (start + leftSpan)).1 (left.actor (start + leftSpan)))
    {leftCommand rightCommand : OrchestrationSorting.Command Name Key Code}
    (leftEvent : left.event (start + leftSpan + 1) = .command leftCommand)
    (rightEvent : right.event (start + rightSpan + 1) = .command rightCommand)
    (leftBlock : ∀ cut, start ≤ cut → cut < start + leftSpan + 1 → ∃ label name, left.event cut = .lifecycle label name)
    (rightBlock : ∀ cut, start ≤ cut → cut < start + rightSpan + 1 → ∃ label name, right.event cut = .lifecycle label name)
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r) :
    letI : Setoid A := TypedCoeffectReplay.setoid observe
    ∃ moved : Trace (encodeProgram program) rightLength,
      (∀ i, i < start + 1 → addressedEventAt left i = addressedEventAt moved i) ∧
      CutAgreement left moved (start + 1) ∧
      (¬ Nonempty (ClosedEpisode moved)) ∧ Progress.Quiet (moved.state rightLength) ∧
      ScheduleAlignmentPath right moved := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  obtain ⟨parent, _, leftBirth, rightBirth, leftActor, rightActor, leftKind, rightKind, _, lastLeft, lastRight,
      leftTag, rightTag, leftParent, rightParent, _, _, _, _⟩ :=
    GuardedCommandAlignment.delayed_commands_wait_for_same_allocating_stage left right
      (leftSpan := leftSpan + 1) (rightSpan := rightSpan + 1) (by omega) (by omega) (by omega) (by omega)
      leftNormal rightNormal past input (by simpa only [Nat.add_assoc] using leftEvent)
      (by simpa only [Nat.add_assoc] using rightEvent) (fun i lo hi => leftBlock i lo (by omega))
      (fun i lo hi => rightBlock i lo (by omega))
  have leftCut : start + (leftSpan + 1) - 1 = start + leftSpan := by omega
  have rightCut : start + (rightSpan + 1) - 1 = start + rightSpan := by omega
  simp only [leftCut] at lastLeft leftTag
  simp only [rightCut] at lastRight rightTag
  have actorEq : left.actor (start + leftSpan) = leftActor := by
    simp [Trace.actor, Vestigial.eventActor, lastLeft]
  rw [actorEq, leftTag] at sameParent
  obtain ⟨moved, expand, order, cut, _, endpoint, opened, quiet, path⟩ :=
    GuardedActivationAlignment.align_pending_parent_before_required_stage left right (by omega) (by omega) (by omega)
      leftOpen leftQuiet rightOpen rightQuiet current stable past input first lastRight sameParent rightTag leftParent rightParent
      (fun i lo hi => rightBlock i lo (by omega)) observe recovery commutative respect
  exact ⟨moved, order, cut, opened, quiet, .activation path endpoint⟩

/-- A redraw is needed when the next activation is blocked by the
removal of the name it draws. The alternative may itself be used at
other cuts. -/
def RedrawAtReuseFor {length : Nat} (source : Trace (encodeProgram program) length) : Prop :=
  (¬ Nonempty (ClosedEpisode source)) → Progress.Quiet (source.state length) →
    ∀ {cut final : Nat} {old parent : Name} {kind : Lifecycle},
      source.event cut = .command (.remove old) →
      source.event (cut + 1) = .lifecycle kind parent →
      GuardedReservationOrder.Lifetime source old (cut + 2) final →
      GuardedIncarnationRedraw.RedrawForExchange source old (cut + 2) kind parent

/-- The redraw premise at a matched prefix, with the actual capacity
witness of the waiting birth and any intervening occupant. -/
def WaitingReuseFor {length : Nat}
    (source : Trace (encodeProgram program) length) (start : Nat) (result : Nat → Name → Name → Lifecycle → Prop) : Prop :=
  (¬ Nonempty (ClosedEpisode source)) → Progress.Quiet (source.state length) →
    ∀ {cut final : Nat} {old parent : Name} {kind : Lifecycle} {childAddress : Address},
      start ≤ cut →
      source.event cut = .command (.remove old) →
      source.event (cut + 1) = .lifecycle kind parent →
      GuardedReservationOrder.Lifetime source old (cut + 2) final →
      Addressed source (cut + 2) childAddress →
      (∃ spare, source.state start spare = none) →
      ((∀ name, source.state cut name ≠ none) →
        ∃ spare birth address, source.state start spare = none ∧ start < birth ∧ birth ≤ cut ∧
          GuardedBirthMatching.BornAt source spare birth ∧
          Incarnation.Residency source.state spare birth cut ∧ Addressed source birth address ∧ address ≠ childAddress) →
      result cut old parent kind

abbrev RedrawAtWaitingReuseFor {length : Nat}
    (source : Trace (encodeProgram program) length) (start : Nat) : Prop :=
  WaitingReuseFor source start fun cut old parent kind =>
    GuardedIncarnationRedraw.RedrawForExchange source old (cut + 2) kind parent

/-- A reuse barrier can be handled by redrawing or by a certified
reordering after the matched prefix that advances the waiting actor. -/
def ResolveWaitingReuseFor [Setoid A] {length : Nat}
    (source : Trace (encodeProgram program) length) (start : Nat) : Prop :=
  WaitingReuseFor source start fun cut old parent kind =>
    GuardedIncarnationRedraw.RedrawForExchange source old (cut + 2) kind parent ∨
      ∃ (moved : Trace (encodeProgram program) length) (time : Nat) (actor : Name) (label : Lifecycle),
        start ≤ time ∧ time ≤ cut ∧ moved.event time = .lifecycle label actor ∧
        (moved.notes time).1 actor = (source.notes (cut + 1)).1 parent ∧
        (∀ i, i < start → addressedEventAt source i = addressedEventAt moved i) ∧
        (¬ Nonempty (ClosedEpisode moved)) ∧ Progress.Quiet (moved.state length) ∧
        ScheduleAlignmentPath source moved

theorem RedrawAtWaitingReuseFor.resolve [Setoid A] {length start : Nat}
    {source : Trace (encodeProgram program) length} (redraw : RedrawAtWaitingReuseFor source start) :
    ResolveWaitingReuseFor source start := by
  intro opened quiet cut final old parent kind address order removal activation life child vacant consumed
  exact .inl (redraw opened quiet order removal activation life child vacant consumed)

theorem RedrawAtReuseFor.at_waiting_reuse {length : Nat}
    {source : Trace (encodeProgram program) length} (redraw : RedrawAtReuseFor source) (start : Nat) :
    RedrawAtWaitingReuseFor source start := by
  intro opened quiet _ _ _ _ _ _ _ removal activation life _ _ _
  exact redraw opened quiet removal activation life

def RedrawAtReuse (inputs : List (AddressedCommand Name Key Code) → Prop := fun _ => True) : Prop :=
  ∀ {length : Nat} (source : Trace (encodeProgram program) length),
    inputs (orchestrationInput source) → RedrawAtReuseFor source

/-- When the common input contains no removals, no intermediate history
with that input can require a redraw across a removal. -/
theorem redrawAtReuse_of_no_removals (input : List (AddressedCommand Name Key Code))
    (none : ∀ address component, .remove address component ∉ input) :
    RedrawAtReuse (program := program) (· = input) := by
  intro length source same _ _ cut final old parent kind removal _ life
  have bounded := life.bounded
  have birthBeforeEnd := life.resident.ordered
  obtain ⟨address, component, found⟩ := targetAt_command source (by omega : cut < length) (.inr removal)
  have member : .remove address component ∈ orchestrationInput source :=
    List.mem_filterMap.mpr ⟨cut, List.mem_range.mpr (by omega), by simp [commandAt, removal, found]⟩
  exact False.elim (none address component (same ▸ member))

/-- Boundary vacancies suffice for the local redraw. The second name may
be occupied by another child inside the interval. Root insertions at that
name would change the original command payload and must stay outside. -/
theorem redrawAtReuse_of_boundary_vacancies
    {inputs : List (AddressedCommand Name Key Code) → Prop}
    (stable : ChildContinuations (encodeProgram program))
    (vacancies : ∀ {length : Nat} (source : Trace (encodeProgram program) length),
      inputs (orchestrationInput source) →
      (¬ Nonempty (ClosedEpisode source)) → Progress.Quiet (source.state length) →
      ∀ {cut final : Nat} {old parent : Name} {kind : Lifecycle},
        source.event cut = .command (.remove old) →
        source.event (cut + 1) = .lifecycle kind parent →
        GuardedReservationOrder.Lifetime source old (cut + 2) final →
        ∃ spare, old ≠ spare ∧ source.state (cut + 1) spare = none ∧
          (final < length → source.state (final + 1) spare = none) ∧
          ∀ i component, cut + 1 ≤ i → i ≤ final → i < length →
            source.event i ≠ .command (.insert spare component)) :
    RedrawAtReuse (program := program) inputs := by
  intro length source allowed opened quiet cut final old parent kind removal event life
  obtain ⟨spare, different, before, after, noInsert⟩ :=
    vacancies source allowed opened quiet removal event life
  refine GuardedIncarnationRedraw.redraw_for_exchange_of_child_redraw
    (GuardedIncarnationRedraw.redraw_child_incarnation_with_reuse
    source opened quiet stable life (by omega) ?_ different ?_ after ?_)
  · simpa only [Nat.add_sub_cancel] using event
  · simpa only [Nat.add_sub_cancel] using before
  · simpa only [Nat.add_sub_cancel] using noInsert

/-- The canonical alignment can use an assignment of all remaining
child names to discharge a reuse barrier. -/
theorem redrawAtReuseFor_of_assignments {length : Nat} (source : Trace (encodeProgram program) length)
    (stable : ChildContinuations (encodeProgram program))
    (assignments : ∀ {cut final : Nat} {old parent : Name} {kind : Lifecycle},
      source.event cut = .command (.remove old) →
      source.event (cut + 1) = .lifecycle kind parent →
      GuardedReservationOrder.Lifetime source old (cut + 2) final →
      GuardedIncarnationRedraw.AssignmentForExchange source old (cut + 2)) :
    RedrawAtReuseFor source := by
  intro opened quiet cut final old parent kind removal event life
  have through := life.resident.ordered
  have born : GuardedBirthMatching.BornAt source old (cut + 2) :=
    ⟨by omega, Nat.le_trans through life.bounded, life.resident.boundary.resolve_left (by omega),
      life.resident.present _ (Nat.le_refl _) through⟩
  apply (GuardedIncarnationRedraw.redraw_for_exchange_iff_assignment source opened quiet stable born ?_).mpr
  · exact assignments removal event life
  · simpa only [Nat.add_sub_cancel] using event

/-- A successful finite search supplies the redraw required by the
canonical driver at every barrier where the search succeeds. -/
theorem redrawAtReuseFor_of_search {length : Nat} (source : Trace (encodeProgram program) length)
    (stable : ChildContinuations (encodeProgram program))
    (pool : List Name) (covers : ∀ name, name ∈ pool)
    (found : ∀ {cut final : Nat} {old parent : Name} {kind : Lifecycle},
      source.event cut = .command (.remove old) →
      source.event (cut + 1) = .lifecycle kind parent →
      GuardedReservationOrder.Lifetime source old (cut + 2) final →
      (GuardedIncarnationRedraw.findExchangeAssignment source pool old (cut + 2)).isSome = true) :
    RedrawAtReuseFor source := by
  apply redrawAtReuseFor_of_assignments source stable
  intro cut final old parent kind removal event life
  exact (GuardedIncarnationRedraw.findExchangeAssignment_iff source pool covers old (by omega)
    (Nat.le_trans life.resident.ordered life.bounded)).mp (found removal event life)

/-- Supply redraws from actual vacancies at the removal and at a later
restoration cut. The two names need only be free of root insertions
while the swap is in force. -/
theorem redrawAtReuseFor_of_restoration_cuts {length : Nat} (source : Trace (encodeProgram program) length)
    (stable : ChildContinuations (encodeProgram program))
    (vacancies : ∀ {cut final : Nat} {old parent : Name} {kind : Lifecycle},
      source.event cut = .command (.remove old) →
      source.event (cut + 1) = .lifecycle kind parent →
      GuardedReservationOrder.Lifetime source old (cut + 2) final →
      ∃ spare stop, final ≤ stop ∧ stop ≤ length ∧ source.state cut spare = none ∧
        (stop < length → source.state (stop + 1) old = none) ∧
        (stop < length → source.state (stop + 1) spare = none) ∧
        ∀ time name component, cut < time → time ≤ stop → time < length →
          source.event time = .command (.insert name component) → name ≠ old ∧ name ≠ spare) :
    RedrawAtReuseFor source := by
  intro opened quiet cut final old parent kind removal event life
  obtain ⟨_, _, through, bounded, vacant, oldAfter, spareAfter, noInsertion⟩ :=
    vacancies removal event life
  exact GuardedIncarnationRedraw.redraw_for_exchange_before_restoration
    source opened quiet stable removal event life through bounded vacant oldAfter spareAfter noInsertion

/-- A swap may stay in force through the remaining history. This only
needs a vacancy at the redraw cut and no later root insertion at either
swapped name. Child births can use the names in the meantime. -/
theorem redrawAtReuseFor_of_suffix_swap {length : Nat} (source : Trace (encodeProgram program) length)
    (stable : ChildContinuations (encodeProgram program))
    (vacancies : ∀ {cut final : Nat} {old parent : Name} {kind : Lifecycle},
      source.event cut = .command (.remove old) →
      source.event (cut + 1) = .lifecycle kind parent →
      GuardedReservationOrder.Lifetime source old (cut + 2) final →
      ∃ spare, old ≠ spare ∧ source.state (cut + 1) spare = none ∧
        ∀ time name component, cut + 1 ≤ time → time < length →
          source.event time = .command (.insert name component) → name ≠ old ∧ name ≠ spare) :
    RedrawAtReuseFor source := by
  intro opened quiet cut final old parent kind removal event life
  obtain ⟨spare, distinct, vacant, noInsert⟩ := vacancies removal event life
  refine GuardedIncarnationRedraw.redraw_for_exchange_of_child_redraw
    (GuardedIncarnationRedraw.redraw_child_with_swap_interval
    source opened quiet stable life (by omega) life.bounded (Nat.le_refl _)
    ?_ distinct ?_ (fun impossible => (Nat.lt_irrefl _ impossible).elim)
    (fun impossible => (Nat.lt_irrefl _ impossible).elim) ?_)
  · simpa only [Nat.add_sub_cancel] using event
  · simpa only [Nat.add_sub_cancel] using vacant
  · intro time name component earlier _ bounded inserted
    exact noInsert time name component (by omega) bounded inserted

/-- A name vacant throughout the source works for every required redraw. -/
theorem redrawAtReuseFor_of_spare {length : Nat} (source : Trace (encodeProgram program) length)
    (stable : ChildContinuations (encodeProgram program))
    (vacancy : ∃ spare, ∀ time, time ≤ length → source.state time spare = none) :
    RedrawAtReuseFor source := by
  intro opened quiet cut final old parent kind _ event life
  obtain ⟨spare, unused⟩ := vacancy
  exact GuardedIncarnationRedraw.redraw_for_exchange_of_child_redraw
    (redraw_child_incarnation source opened quiet stable (fresh := spare) life (by omega)
    (by simpa only [Nat.add_sub_cancel] using event) (fun i _ _ bounded => unused i bounded))

theorem redrawAtReuseFor_of_birth_slots {length : Nat} (source : Trace (encodeProgram program) length)
    (stable : ChildContinuations (encodeProgram program))
    (supply : ∀ used : List Name, used.length ≤ GuardedIncarnationRedraw.birthSlotsThrough source length → ∃ spare, spare ∉ used) :
    RedrawAtReuseFor source :=
  redrawAtReuseFor_of_spare source stable (GuardedIncarnationRedraw.spare_of_birth_slots source supply)

theorem redrawAtReuseFor_of_bounded_supply {length : Nat} (source : Trace (encodeProgram program) length)
    (stable : ChildContinuations (encodeProgram program))
    (supply : ∀ used : List Name, used.length ≤ length → ∃ spare, spare ∉ used) :
    RedrawAtReuseFor source :=
  redrawAtReuseFor_of_birth_slots source stable
    (fun used size => supply used (Nat.le_trans size (GuardedIncarnationRedraw.birthSlotsThrough_le source length)))

/-- An unbounded name supply satisfies the local redraw condition. -/
theorem redrawAtReuse_of_supply (stable : ChildContinuations (encodeProgram program))
    (supply : ∀ used : List Name, ∃ spare, spare ∉ used) : RedrawAtReuse (program := program) :=
  fun source _ => redrawAtReuseFor_of_bounded_supply source stable (fun used _ => supply used)

theorem matched_prefix {leftLength rightLength start : Nat}
    (left : Trace (encodeProgram program) leftLength) (right : Trace (encodeProgram program) rightLength)
    (leftBound : start ≤ leftLength) (rightBound : start ≤ rightLength)
    (leftOpen : ¬ Nonempty (ClosedEpisode left)) (leftQuiet : Progress.Quiet (left.state leftLength))
    (rightOpen : ¬ Nonempty (ClosedEpisode right)) (rightQuiet : Progress.Quiet (right.state rightLength))
    (stable : ChildContinuations (encodeProgram program))
    (past : ∀ cut, cut < start → addressedEventAt left cut = addressedEventAt right cut) : CutAgreement left right start := by
  apply match_open_prefix left right stable start leftBound rightBound
  intro cut inside
  exact match_addressed_event left right (by omega) (by omega)
    (fun event => (left.activation_at leftOpen leftQuiet (by omega) event).1)
    (fun event => (right.activation_at rightOpen rightQuiet (by omega) event).1)
    (fun i earlier => past i (by omega)) (past cut inside)

/-- The actor at the matched cut owns an as-yet unallocated edge on
the lineage of the next command's target. -/
def RequiredAncestor {length : Nat} (trace : Trace (encodeProgram program) length)
    (start : Nat) (actor : Name) (commandCut : Nat) (target : Name) : Prop :=
  ∃ (birth ordinal : Nat) (parent descendant : Address) (component : Component Key Code),
    (trace.notes start).1 actor = some birth ∧ Addressed trace birth parent ∧
    targetAt trace commandCut target = some (descendant, component) ∧
    descendant.DescendsFrom (.child parent ordinal) ∧
    ∀ stamp, stamp ≤ start → ¬ Addressed trace stamp (.child parent ordinal)

/-- Find the peer's first delayed command by normalizing its suffix.
If the reference's next step belongs to the required parent or
ancestor, no release or redraw is needed to align that step. -/
theorem align_required_actor_from_matched_cut {leftLength rightLength start span : Nat}
    (left : Trace (encodeProgram program) leftLength) (right : Trace (encodeProgram program) rightLength)
    (leftBound : start + span + 1 < leftLength) (rightBound : start ≤ rightLength)
    (leftOpen : ¬ Nonempty (ClosedEpisode left)) (leftQuiet : Progress.Quiet (left.state leftLength))
    (rightOpen : ¬ Nonempty (ClosedEpisode right)) (rightQuiet : Progress.Quiet (right.state rightLength))
    (leftNormal : GuardedCommandAlignment.CommandsAtBirthBarriersFrom left start)
    (current : CutAgreement left right start) (stable : ChildContinuations (encodeProgram program))
    (past : ∀ cut, cut < start → addressedEventAt left cut = addressedEventAt right cut)
    (input : orchestrationInput left = orchestrationInput right)
    {kind : Lifecycle} {actor : Name} (first : left.event start = .lifecycle kind actor)
    {command : OrchestrationSorting.Command Name Key Code}
    (leftCommand : left.event (start + span + 1) = .command command)
    (required : (left.notes start).1 actor = (left.notes (start + span)).1 (left.actor (start + span)) ∨
      RequiredAncestor left start actor (start + span + 1) command.actor)
    (leftBlock : ∀ cut, start ≤ cut → cut < start + span + 1 →
      ∃ label name, left.event cut = .lifecycle label name)
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r) :
    letI : Setoid A := TypedCoeffectReplay.setoid observe
    ∃ moved : Trace (encodeProgram program) rightLength,
      start < rightLength ∧ (∀ cut, cut < start + 1 → addressedEventAt left cut = addressedEventAt moved cut) ∧
      CutAgreement left moved (start + 1) ∧
      (¬ Nonempty (ClosedEpisode moved)) ∧ Progress.Quiet (moved.state rightLength) ∧
      ScheduleAlignmentPath right moved := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  obtain ⟨mid, _, normal, _, commands, _, _, opened, quiet, commandPath, cuts, _, addresses⟩ :=
    GuardedCommandAlignment.push_commands_to_birth_barriers_from right start rightOpen rightQuiet
  have earlier (cut : Nat) (before : cut < start) : addressedEventAt left cut = addressedEventAt mid cut :=
    (past cut before).trans (addresses cut before (by omega)).symm
  have inputMid := input.trans commands.symm
  obtain ⟨delay, next, bounded, external, block⟩ :=
    GuardedCommandAlignment.pending_delayed_command_occurs left mid (leftSpan := span + 1)
      (by omega) rightBound earlier inputMid (by simpa only [Nat.add_assoc] using leftCommand)
      (fun i lo hi => leftBlock i lo (by omega))
  cases delay with
  | zero =>
    have atStart : mid.event start = .command next := external
    have reverse := matched_prefix mid left rightBound (by omega) opened quiet leftOpen leftQuiet stable
      (fun i before => (earlier i before).symm)
    obtain ⟨_, ⟨_, impossible⟩, _⟩ :=
      GuardedCommandAlignment.pending_command_at_suffix_birth_frontier mid left (by omega) (by omega)
        leftNormal reverse (fun i before => (earlier i before).symm) inputMid.symm atStart
    rw [first] at impossible
    cases impossible
  | succ delay =>
    have midCut : CutAgreement left mid start := by
      obtain ⟨names, states, stamps, saved⟩ := current
      obtain ⟨stateEq, noteEq⟩ := cuts start (Nat.le_refl _) rightBound
      refine ⟨names, stateEq.symm ▸ states, ?_, ?_⟩
      · simpa only [noteEq] using stamps
      · unfold GuardedBirthReplay.SavedMatch at saved ⊢
        simpa only [noteEq] using saved
    rcases required with sameParent | ancestor
    · obtain ⟨moved, ordered, final, openMoved, quietMoved, path⟩ :=
        align_stage_of_parent_needed_by_next_command left mid leftBound (rightSpan := delay) (by omega)
          leftOpen leftQuiet opened quiet leftNormal normal midCut stable earlier inputMid first sameParent leftCommand
          (by simpa only [Nat.add_assoc] using external) leftBlock (fun i lo hi => block i lo (by omega))
          observe recovery commutative respect
      exact ⟨moved, by omega, ordered, final, openMoved, quietMoved, .trans (.command commandPath) path⟩
    · obtain ⟨birth, ordinal, parent, descendant, component, tag, parentAddress, target, lineage, unborn⟩ := ancestor
      obtain ⟨actual, payload, _, _, _, needed, found, _⟩ :=
        GuardedCommandAlignment.delayed_commands_wait_for_same_birth left mid
          (leftSpan := span + 1) (rightSpan := delay + 1) (by omega) (by omega) (by omega) (by omega)
          leftNormal normal earlier inputMid (by simpa only [Nat.add_assoc] using leftCommand)
          external (fun i lo hi => leftBlock i lo (by omega)) block
      have atCommand : targetAt left (start + (span + 1)) command.actor = some (descendant, component) := by
        simpa only [Nat.add_assoc] using target
      have same := Prod.mk.inj (Option.some.inj (found.symm.trans atCommand))
      obtain ⟨rfl, rfl⟩ := same
      obtain ⟨moved, expand, inside, ordered, final, _, endpoint, openMoved, quietMoved, path⟩ :=
        GuardedActivationAlignment.align_pending_ancestor_before_required_birth left mid (by omega) rightBound
          leftOpen leftQuiet opened quiet midCut stable earlier inputMid first tag parentAddress needed lineage unborn
          block observe recovery commutative respect
      exact ⟨moved, inside, ordered, final, openMoved, quietMoved,
        .trans (.command commandPath) (.activation path endpoint)⟩


/-- If the next command targets the child born at the shared cut,
advance that command past any intervening activations in the reference.
The prepared reference then certifies the matching birth in the peer. -/
theorem align_required_birth_before_delayed_command {leftLength rightLength start span : Nat}
    (left : Trace (encodeProgram program) leftLength) (right : Trace (encodeProgram program) rightLength)
    (leftBound : start + 1 + span < leftLength) (rightBound : start ≤ rightLength)
    (leftOpen : ¬ Nonempty (ClosedEpisode left)) (leftQuiet : Progress.Quiet (left.state leftLength))
    (rightOpen : ¬ Nonempty (ClosedEpisode right)) (rightQuiet : Progress.Quiet (right.state rightLength))
    (current : CutAgreement left right start) (stable : ChildContinuations (encodeProgram program))
    (past : ∀ cut, cut < start → addressedEventAt left cut = addressedEventAt right cut)
    (input : orchestrationInput left = orchestrationInput right)
    {kind : Lifecycle} {actor : Name} (allocation : left.event start = .lifecycle kind actor)
    {command : OrchestrationSorting.Command Name Key Code}
    (leftCommand : left.event (start + 1 + span) = .command command)
    (leftBorn : GuardedBirthMatching.BornAt left command.actor (start + 1))
    (block : ∀ cut, start + 1 ≤ cut → cut < start + 1 + span →
      ∃ label name, left.event cut = .lifecycle label name)
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r) :
    letI : Setoid A := TypedCoeffectReplay.setoid observe
    ∃ moved : Trace (encodeProgram program) rightLength,
      start < rightLength ∧ (∀ cut, cut < start + 1 → addressedEventAt left cut = addressedEventAt moved cut) ∧
      CutAgreement left moved (start + 1) ∧ (¬ Nonempty (ClosedEpisode moved)) ∧
      Progress.Quiet (moved.state rightLength) ∧ ScheduleAlignmentPath right moved := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  obtain ⟨prepared, expand, addresses, fixed, cuts, events, commandNow, _, commands, _, opened, quiet, _⟩ :=
    GuardedCommandAlignment.pull_command_through_activations_with_path left leftOpen leftQuiet
      leftBound leftCommand block (fun absent => False.elim (leftBorn.2.2.2 absent))
  have earlier (i : Nat) (lower : i < start + 1) :
      addressedEventAt prepared i = addressedEventAt left i := by
    have matchEvent := stable_addressed_event addresses (cut := i) (by omega)
    rw [fixed _ (by omega : i + 1 ≤ start + 1), Nat.add_sub_cancel] at matchEvent
    exact matchEvent
  have newPast (i : Nat) (lower : i < start) : addressedEventAt prepared i = addressedEventAt right i :=
    (earlier i (by omega)).trans (past i lower)
  have preparedCut : CutAgreement prepared right start := by
    obtain ⟨names, states, tags, saved⟩ := current
    obtain ⟨stateEq, noteEq⟩ := cuts start (by omega)
    refine ⟨names, by rw [stateEq]; exact states, by rw [noteEq]; exact tags, ?_⟩
    unfold GuardedBirthReplay.SavedMatch at saved ⊢
    simpa only [noteEq] using saved
  have allocationNow := (events start (by omega)).trans allocation
  have bornNow : GuardedBirthMatching.BornAt prepared command.actor (start + 1) := by
    refine ⟨leftBorn.1, leftBorn.2.1, ?_, ?_⟩
    · rw [(cuts (start + 1 - 1) (by omega)).1]
      exact leftBorn.2.2.1
    · rw [(cuts (start + 1) (Nat.le_refl _)).1]
      exact leftBorn.2.2.2
  obtain ⟨moved, bounded, pair, _, openMoved, quietMoved, path⟩ :=
    align_required_birth_from_matched_cut prepared right (by omega) rightBound opened quiet rightOpen rightQuiet
      preparedCut stable newPast (commands.trans input) allocationNow commandNow bornNow observe recovery commutative respect
  have ordered (i : Nat) (before : i < start + 1) : addressedEventAt left i = addressedEventAt moved i :=
    (earlier i before).symm.trans (pair i (by omega))
  exact ⟨moved, by omega, ordered,
    matched_prefix left moved (by omega) (by omega) leftOpen leftQuiet openMoved quietMoved stable ordered,
    openMoved, quietMoved, path⟩

private theorem stamp_fixed_by_exchange {point birth : Nat} {tag : Option Nat}
    (earlier : birth ≤ point) (mapped : tag.map (ExchangeReplay.exchangedIndex point) = some birth) :
    tag = some birth := by
  obtain ⟨stamp, found, image⟩ := Option.map_eq_some_iff.mp mapped
  have fixed : ExchangeReplay.exchangedIndex point birth = birth :=
    ExchangeReplay.exchangedIndex_other (by omega) (by omega)
  have unique : stamp = birth := by
    have same := congrArg (ExchangeReplay.exchangedIndex point) (image.trans fixed.symm)
    simpa only [ExchangeReplay.exchangedIndex_involutive] using same
  exact found.trans (congrArg some unique)

/-- Move the preceding activation after a ready command block ending
in the removal. The waiting activation then advances across that
preceding activation, using the vacancy made by the same commands. -/
theorem advance_waiting_activation_by_earlier_command_block {length : Nat}
    (source : Trace (encodeProgram program) length)
    (opened : ¬ Nonempty (ClosedEpisode source)) (quiet : Progress.Quiet (source.state length))
    {pivot span birth : Nat} (bounded : pivot + span + 1 < length) (born : birth ≤ pivot)
    {previous waiting : Name} {previousKind kind : Lifecycle}
    (earlier : source.event pivot = .lifecycle previousKind previous)
    (activation : source.event (pivot + span + 1) = .lifecycle kind waiting)
    (tag : (source.notes (pivot + span + 1)).1 waiting = some birth)
    (block : ∀ cut, pivot < cut → cut ≤ pivot + span →
      ∃ command, source.event cut = .command command)
    (ready : ∀ cut, pivot < cut → cut ≤ pivot + span → ∀ command,
      source.event cut = .command command → source.state pivot command.actor = none →
      source.state (pivot + 1) command.actor = none)
    (distinct : previous ≠ waiting) (notBegin : kind ≠ .begin)
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r) :
    letI : Setoid A := TypedCoeffectReplay.setoid observe
    ∃ moved : Trace (encodeProgram program) length,
      moved.event (pivot + span) = .lifecycle kind waiting ∧
      (moved.notes (pivot + span)).1 waiting = some birth ∧
      (∀ i, i < pivot → addressedEventAt source i = addressedEventAt moved i) ∧
      (¬ Nonempty (ClosedEpisode moved)) ∧ Progress.Quiet (moved.state length) ∧
      ScheduleAlignmentPath source moved := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  obtain ⟨mid, expand, commands, movedEarlier, _, editPrefix, editSuffix, fixed, openMid, quietMid, _, _, _⟩ :=
    GuardedCommandAlignment.push_activation_through_command_block source opened quiet (by omega) earlier block ready
  have middleEvent : mid.event (pivot + span + 1) = .lifecycle kind waiting :=
    (editSuffix _ (by omega) bounded).trans activation
  have middleTag : (mid.notes (pivot + span + 1)).1 waiting = some birth := by
    have retained := commands.preserves.2.2.retained
    have mapped := retained.actor_birth bounded
    rw [fixed _ (.inr (by omega)), Nat.add_sub_cancel] at mapped
    have image : ((mid.notes (pivot + span + 1)).1 waiting).map expand = some birth := by
      simpa [Trace.actor, Vestigial.eventActor, middleEvent, activation, tag] using mapped
    obtain ⟨stamp, found, same⟩ := Option.map_eq_some_iff.mp image
    exact found.trans (congrArg some (retained.injective (same.trans (fixed _ (.inl born)).symm)))
  obtain ⟨moved, _, labels, _, suffix, retained, _, openMoved, quietMoved⟩ :=
    mid.swap_activations openMid quietMid bounded movedEarlier middleEvent distinct
      (fun begins => (notBegin begins).elim) observe recovery commutative respect
  have addresses : StableActorAddresses mid moved (ExchangeReplay.exchangedIndex (pivot + span)) := by
    apply StableActorAddresses.adjacent bounded retained
    · simp [isRootInsertion, movedEarlier]
    · intro _ _
      simpa [Trace.actor, Vestigial.eventActor, movedEarlier, middleEvent] using distinct
  have movedEvent : moved.event (pivot + span) = .lifecycle kind waiting := by
    simpa only [labels (pivot + span) (by omega), if_pos rfl] using middleEvent
  have movedTag : (moved.notes (pivot + span)).1 waiting = some birth := by
    apply stamp_fixed_by_exchange (point := pivot + span) (by omega)
    have mapped := retained.actor_birth (cut := pivot + span) (by omega)
    simpa [Trace.actor, Vestigial.eventActor, movedEvent, middleEvent, middleTag] using mapped
  have endpoint := (suffix length (by omega) (Nat.le_refl _)).1
  have input := GuardedCommandAlignment.command_input_of_activation_exchange addresses bounded
    (.inr ⟨kind, waiting, middleEvent⟩)
  have lastMove : ScheduleAlignmentPath mid moved :=
    .swap ⟨bounded, ⟨kind, waiting, middleEvent⟩, labels, addresses, input, endpoint, openMoved, quietMoved⟩
  refine ⟨moved, movedEvent, movedTag, ?_, openMoved, quietMoved, .trans (.command commands) lastMove⟩
  intro i before
  have same := stable_addressed_event addresses (cut := i) (by omega)
  rw [ExchangeReplay.exchangedIndex_other (by omega) (by omega), Nat.add_sub_cancel] at same
  exact (editPrefix i before).symm.trans same.symm

/-- Each exchange moves the first pending activation to a strictly earlier
cut. Replacing its draw does not change its birth provenance or the matched
prefix. The original and replayed endpoints agree up to renaming. -/
theorem align_activation_with_reuse_resolution {leftLength rightLength start : Nat}
    (left : Trace (encodeProgram program) leftLength) (right : Trace (encodeProgram program) rightLength)
    (leftBound : start < leftLength) (rightBound : start ≤ rightLength)
    (leftOpen : ¬ Nonempty (ClosedEpisode left)) (leftQuiet : Progress.Quiet (left.state leftLength))
    (rightOpen : ¬ Nonempty (ClosedEpisode right)) (rightQuiet : Progress.Quiet (right.state rightLength))
    (current : CutAgreement left right start) (stable : ChildContinuations (encodeProgram program))
    (past : ∀ cut, cut < start → addressedEventAt left cut = addressedEventAt right cut)
    (input : orchestrationInput left = orchestrationInput right)
    {kind : Lifecycle} {actor : Name} (event : left.event start = .lifecycle kind actor)
    (observe : ∀ key, Setoid (V key))
    (resolve : ∀ source : Trace (encodeProgram program) rightLength,
      orchestrationInput source = orchestrationInput left →
      (addressedEvents source).Perm (addressedEvents right) →
      GuardedIncarnationRedraw.LiveDomainRenaming (right.state rightLength) (source.state rightLength) →
      @ResolveWaitingReuseFor Name Key Code _ _ V ops program
        (TypedCoeffectReplay.setoid observe) rightLength source start)
    (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r) :
    letI : Setoid A := TypedCoeffectReplay.setoid observe
    ∃ moved : Trace (encodeProgram program) rightLength,
      start < rightLength ∧ CutAgreement left moved (start + 1) ∧
      (∀ i, i < start + 1 → addressedEventAt left i = addressedEventAt moved i) ∧
      orchestrationInput moved = orchestrationInput right ∧ ProjectedAgreement (right.state rightLength) (moved.state rightLength) ∧
      (¬ Nonempty (ClosedEpisode moved)) ∧ Progress.Quiet (moved.state rightLength) ∧
      (addressedEvents moved).Perm (addressedEvents right) ∧ ScheduleAlignmentPath right moved := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  have seek (span : Nat) (source : Trace (encodeProgram program) rightLength)
      (opened : ¬ Nonempty (ClosedEpisode source)) (settled : Progress.Quiet (source.state rightLength))
      (matched : CutAgreement left source start)
      (ordered : ∀ i, i < start → addressedEventAt left i = addressedEventAt source i)
      (word : orchestrationInput left = orchestrationInput source)
      (permutation : (addressedEvents source).Perm (addressedEvents right))
      (endpointFromRight : ProjectedAgreement (right.state rightLength) (source.state rightLength))
      (candidate : ∃ time label name, start ≤ time ∧ time < rightLength ∧ time ≤ start + span ∧
        source.event time = .lifecycle label name ∧ (source.notes time).1 name = (left.notes start).1 actor) :
      ∃ moved : Trace (encodeProgram program) rightLength,
        start < rightLength ∧ CutAgreement left moved (start + 1) ∧
        (∀ i, i < start + 1 → addressedEventAt left i = addressedEventAt moved i) ∧
        orchestrationInput moved = orchestrationInput source ∧ ProjectedAgreement (source.state rightLength) (moved.state rightLength) ∧
        (¬ Nonempty (ClosedEpisode moved)) ∧ Progress.Quiet (moved.state rightLength) ∧
        (addressedEvents moved).Perm (addressedEvents source) ∧ ScheduleAlignmentPath source moved := by
    induction span using Nat.strongRecOn generalizing source with
    | ind span ih =>
      obtain ⟨time, otherKind, other, birth, path, lower, within, next, leftTag, rightTag, laterTag, leftPath, rightPath,
        phase, through, earliest⟩ := pending_activation_occurs left source leftBound rightBound leftOpen leftQuiet
          opened settled matched ordered word event
      obtain ⟨whereAt, label, name, bornAfter, knownBound, beforeLimit, found, knownTag⟩ := candidate
      have sameName := born_unique source (recorded_birth source (Nat.le_of_lt knownBound) (knownTag.trans leftTag)).1
        (recorded_birth source (Nat.le_of_lt within) laterTag).1
      have beforeCandidate : time ≤ whereAt := by
        apply Nat.le_of_not_gt
        intro smaller
        exact earliest whereAt bornAfter smaller label (sameName ▸ found)
      rcases Nat.eq_or_lt_of_le lower with equal | earlier
      · subst time
        obtain ⟨moved, _, kept, longer, cut, inputEq, endpoints, stillOpen, stillQuiet, path⟩ :=
          align_next_activation_with_path left source (span := 0) leftBound within leftOpen leftQuiet opened settled
            matched stable ordered event next leftTag rightTag laterTag leftPath rightPath (fun _ lower upper => by omega)
            observe recovery commutative respect
        exact ⟨moved, within, cut, longer, inputEq, .of_related endpoints, stillOpen, stillQuiet,
          addressedEvents_perm_of_stable kept, .activation path endpoints⟩
      · cases time with
        | zero => omega
        | succ cut =>
          have swap : ∃ (mid : Trace (encodeProgram program) rightLength) (time : Nat) (name : Name) (label : Lifecycle),
              start ≤ time ∧ time ≤ cut ∧ mid.event time = .lifecycle label name ∧
              (mid.notes time).1 name = (left.notes start).1 actor ∧
              (∀ i, i < start → addressedEventAt left i = addressedEventAt mid i) ∧
              orchestrationInput mid = orchestrationInput source ∧
              ProjectedAgreement (source.state rightLength) (mid.state rightLength) ∧
              (¬ Nonempty (ClosedEpisode mid)) ∧ Progress.Quiet (mid.state rightLength) ∧
              (addressedEvents mid).Perm (addressedEvents source) ∧ ScheduleAlignmentPath source mid := by
            have ready := through cut (by omega) (by omega)
            rcases move_waiting_activation_one_step_with_exchange left source leftBound within (by omega) leftOpen leftQuiet opened settled
              matched ordered word event next leftTag rightTag laterTag leftPath rightPath phase earliest ready.2.2
              observe recovery commutative respect with
              ⟨mid, kept, fixed, _, movedEvent, inputEq, endpoint, openMid, quietMid, exchange⟩ | ⟨removed, removal, rebound⟩
            · have movedTag : (mid.notes cut).1 other = (left.notes start).1 actor := by
                rw [(fixed cut (Nat.le_refl _)).2, ready.1, leftTag]
              refine ⟨mid, cut, other, otherKind, by omega, Nat.le_refl _, movedEvent, movedTag, ?_, inputEq, .of_related endpoint, openMid, quietMid,
                addressedEvents_perm_of_stable kept, .swap exchange⟩
              intro i before
              have same := stable_addressed_event kept (cut := i) (by omega)
              rw [ExchangeReplay.exchangedIndex_other (by omega) (by omega), Nat.add_sub_cancel] at same
              exact (ordered i before).trans same.symm
            · by_cases canAdvanceBlock : ∃ pivot previousKind previous,
                  start ≤ pivot ∧ pivot < cut ∧ source.event pivot = .lifecycle previousKind previous ∧
                  otherKind ≠ .begin ∧
                  (∀ i, pivot < i → i ≤ cut → ∃ command, source.event i = .command command) ∧
                  (∀ i, pivot < i → i ≤ cut → ∀ command,
                    source.event i = .command command → source.state pivot command.actor = none →
                    source.state (pivot + 1) command.actor = none)
              · obtain ⟨pivot, previousKind, previous, afterStart, beforeCut, prior, notBegin, block, ready⟩ :=
                  canAdvanceBlock
                have earlierBirth := (recorded_birth source (by omega : start ≤ rightLength) rightTag).2
                have distinct : previous ≠ other := by
                  rintro rfl
                  exact earliest pivot afterStart (by omega) previousKind prior
                have split : pivot + (cut - pivot) = cut := by omega
                obtain ⟨mid, movedEvent, movedTag, earlierEvents, openMid, quietMid, path⟩ :=
                  advance_waiting_activation_by_earlier_command_block source opened settled
                    (pivot := pivot) (span := cut - pivot) (birth := birth) (by omega) (by omega) prior
                    (by simpa only [split] using next) (by simpa only [split] using laterTag)
                    (by simpa only [split] using block) (by simpa only [split] using ready)
                    distinct notBegin observe recovery commutative respect
                obtain ⟨endpoint, events⟩ := path.preserves
                rw [split] at movedEvent movedTag
                exact ⟨mid, cut, other, otherKind, by omega, Nat.le_refl _, movedEvent,
                  movedTag.trans leftTag.symm, fun i before => (ordered i before).trans (earlierEvents i (by omega)),
                  path.input_eq, endpoint, openMid, quietMid, events, path⟩
              · obtain ⟨_, childAddress, _, _, childAtRight, vacantAtStart, consumed⟩ :=
                  GuardedReservationAlignment.waiting_reuse_capacity left source leftBound within (by omega)
                    leftOpen leftQuiet opened settled matched ordered event next leftTag rightTag laterTag
                    leftPath rightPath phase earliest removal rebound
                have gone := (source.step cut (by omega)).1
                rw [removal] at gone
                have nowVacant : source.state (cut + 1) removed = none := by
                  rw [gone.2]
                  simp [OrchestrationSorting.Command.apply, erase]
                have newBirth : GuardedBirthMatching.BornAt source removed (cut + 2) :=
                  ⟨by omega, by omega, by simpa only [Nat.add_sub_cancel] using nowVacant, rebound⟩
                obtain ⟨final, life⟩ := GuardedReservationOrder.lifetime_of_birth source newBirth
                rcases resolve source word.symm permutation
                  (GuardedIncarnationRedraw.live_domain_of_projected_agreement endpointFromRight) opened settled
                  (by omega) removal next life childAtRight vacantAtStart consumed with drawn | reordered
                · obtain ⟨redrawn, mid, drawCut, kept, inputEq, movedEvent, movedTag, prior, exchanged, openMid, quietMid,
                    sameEvents, drawCommands, exchange, redrawNames⟩ :=
                    cross_reuse_with_local_redraw left source leftBound within (by omega) leftOpen leftQuiet stable
                      ordered word event removal rebound (leftTag.trans laterTag.symm) earliest
                      (fun _ _ => drawn)
                      observe recovery commutative respect
                  have redrawPath : ScheduleAlignmentPath source redrawn := .redraw drawCut drawCommands sameEvents redrawNames
                  obtain ⟨_, drawnEndpoint, _, _⟩ := drawCut
                  exact ⟨mid, cut, other, otherKind, by omega, Nat.le_refl _, movedEvent, movedTag, fun i before => (ordered i before).trans (prior i (by omega)).symm,
                    inputEq, (ProjectedAgreement.of_rename_eq drawnEndpoint).trans (.of_related exchanged), openMid, quietMid,
                    (addressedEvents_perm_of_stable kept).trans (List.Perm.of_eq sameEvents),
                    .trans redrawPath (.swap exchange)⟩
                · obtain ⟨mid, atTime, name, label, lower, upper, movedEvent, movedTag, prior, openMid, quietMid, path⟩ := reordered
                  obtain ⟨endpoint, events⟩ := path.preserves
                  exact ⟨mid, atTime, name, label, lower, upper, movedEvent, movedTag.trans (laterTag.trans leftTag.symm),
                    fun i bound => (ordered i bound).trans (prior i bound), path.input_eq, endpoint,
                    openMid, quietMid, events, path⟩
          obtain ⟨mid, atTime, movedName, movedLabel, earlier, upper, movedEvent, movedTag, earlierEvents, inputEq, related, openMid, quietMid, exchangedEvents, firstPath⟩ := swap
          have currentMid := matched_prefix left mid (Nat.le_of_lt leftBound) rightBound leftOpen leftQuiet
            openMid quietMid stable earlierEvents
          have smaller : cut - start < span := by omega
          obtain ⟨moved, canAdvance, final, longer, commands, endpoint, openEnd, quietEnd, finalEvents, restPath⟩ :=
            ih (cut - start) smaller mid openMid quietMid currentMid earlierEvents (word.trans inputEq.symm)
              (exchangedEvents.trans permutation) (endpointFromRight.trans related) ⟨atTime, movedLabel, movedName, earlier, by omega, by omega, movedEvent, movedTag⟩
          exact ⟨moved, canAdvance, final, longer, commands.trans inputEq, related.trans endpoint, openEnd, quietEnd,
            finalEvents.trans exchangedEvents, firstPath.trans restPath⟩
  obtain ⟨time, label, name, birth, path, lower, within, next, leftTag, _, laterTag, _, _, _, _, _⟩ :=
    pending_activation_occurs left right leftBound rightBound leftOpen leftQuiet rightOpen rightQuiet current past input event
  exact seek (time - start) right rightOpen rightQuiet current past input (.refl _) (.refl _)
    ⟨time, label, name, lower, within, by omega, next, laterTag.trans leftTag.symm⟩

theorem align_activation_with_waiting_redraw {leftLength rightLength start : Nat}
    (left : Trace (encodeProgram program) leftLength) (right : Trace (encodeProgram program) rightLength)
    (leftBound : start < leftLength) (rightBound : start ≤ rightLength)
    (leftOpen : ¬ Nonempty (ClosedEpisode left)) (leftQuiet : Progress.Quiet (left.state leftLength))
    (rightOpen : ¬ Nonempty (ClosedEpisode right)) (rightQuiet : Progress.Quiet (right.state rightLength))
    (current : CutAgreement left right start) (stable : ChildContinuations (encodeProgram program))
    (past : ∀ cut, cut < start → addressedEventAt left cut = addressedEventAt right cut)
    (input : orchestrationInput left = orchestrationInput right)
    {kind : Lifecycle} {actor : Name} (event : left.event start = .lifecycle kind actor)
    (redraw : ∀ source : Trace (encodeProgram program) rightLength,
      orchestrationInput source = orchestrationInput left →
      (addressedEvents source).Perm (addressedEvents right) →
      GuardedIncarnationRedraw.LiveDomainRenaming (right.state rightLength) (source.state rightLength) →
      RedrawAtWaitingReuseFor source start)
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r) :
    letI : Setoid A := TypedCoeffectReplay.setoid observe
    ∃ moved : Trace (encodeProgram program) rightLength,
      start < rightLength ∧ CutAgreement left moved (start + 1) ∧
      (∀ i, i < start + 1 → addressedEventAt left i = addressedEventAt moved i) ∧
      orchestrationInput moved = orchestrationInput right ∧ ProjectedAgreement (right.state rightLength) (moved.state rightLength) ∧
      (¬ Nonempty (ClosedEpisode moved)) ∧ Progress.Quiet (moved.state rightLength) ∧
      (addressedEvents moved).Perm (addressedEvents right) ∧ ScheduleAlignmentPath right moved := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  exact align_activation_with_reuse_resolution left right leftBound rightBound leftOpen leftQuiet
    rightOpen rightQuiet current stable past input event observe
    (fun source same events domain => (redraw source same events domain).resolve)
    recovery commutative respect

theorem align_activation_with_local_redraw {leftLength rightLength start : Nat}
    (left : Trace (encodeProgram program) leftLength) (right : Trace (encodeProgram program) rightLength)
    (leftBound : start < leftLength) (rightBound : start ≤ rightLength)
    (leftOpen : ¬ Nonempty (ClosedEpisode left)) (leftQuiet : Progress.Quiet (left.state leftLength))
    (rightOpen : ¬ Nonempty (ClosedEpisode right)) (rightQuiet : Progress.Quiet (right.state rightLength))
    (current : CutAgreement left right start) (stable : ChildContinuations (encodeProgram program))
    (past : ∀ cut, cut < start → addressedEventAt left cut = addressedEventAt right cut)
    (input : orchestrationInput left = orchestrationInput right)
    {kind : Lifecycle} {actor : Name} (event : left.event start = .lifecycle kind actor)
    (redraw : ∀ source : Trace (encodeProgram program) rightLength,
      orchestrationInput source = orchestrationInput left →
      (addressedEvents source).Perm (addressedEvents right) →
      GuardedIncarnationRedraw.LiveDomainRenaming (right.state rightLength) (source.state rightLength) →
      RedrawAtReuseFor source)
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r) :
    letI : Setoid A := TypedCoeffectReplay.setoid observe
    ∃ moved : Trace (encodeProgram program) rightLength,
      start < rightLength ∧ CutAgreement left moved (start + 1) ∧
      (∀ i, i < start + 1 → addressedEventAt left i = addressedEventAt moved i) ∧
      orchestrationInput moved = orchestrationInput right ∧ ProjectedAgreement (right.state rightLength) (moved.state rightLength) ∧
      (¬ Nonempty (ClosedEpisode moved)) ∧ Progress.Quiet (moved.state rightLength) ∧
      (addressedEvents moved).Perm (addressedEvents right) ∧ ScheduleAlignmentPath right moved := by
  exact align_activation_with_waiting_redraw left right leftBound rightBound leftOpen leftQuiet
    rightOpen rightQuiet current stable past input event
    (fun source same events domain => (redraw source same events domain).at_waiting_reuse start)
    observe recovery commutative respect

theorem align_activation_with_spare_names {leftLength rightLength start : Nat}
    (left : Trace (encodeProgram program) leftLength) (right : Trace (encodeProgram program) rightLength)
    (leftBound : start < leftLength) (rightBound : start ≤ rightLength)
    (leftOpen : ¬ Nonempty (ClosedEpisode left)) (leftQuiet : Progress.Quiet (left.state leftLength))
    (rightOpen : ¬ Nonempty (ClosedEpisode right)) (rightQuiet : Progress.Quiet (right.state rightLength))
    (current : CutAgreement left right start) (stable : ChildContinuations (encodeProgram program))
    (past : ∀ cut, cut < start → addressedEventAt left cut = addressedEventAt right cut)
    (input : orchestrationInput left = orchestrationInput right)
    {kind : Lifecycle} {actor : Name} (event : left.event start = .lifecycle kind actor)
    (supply : ∀ used : List Name, ∃ spare, spare ∉ used)
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r) :
    letI : Setoid A := TypedCoeffectReplay.setoid observe
    ∃ moved : Trace (encodeProgram program) rightLength,
      start < rightLength ∧ CutAgreement left moved (start + 1) ∧
      (∀ i, i < start + 1 → addressedEventAt left i = addressedEventAt moved i) ∧
      orchestrationInput moved = orchestrationInput right ∧ ProjectedAgreement (right.state rightLength) (moved.state rightLength) ∧
      (¬ Nonempty (ClosedEpisode moved)) ∧ Progress.Quiet (moved.state rightLength) ∧
      (addressedEvents moved).Perm (addressedEvents right) := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  obtain ⟨moved, bounded, cut, order, commands, endpoint, opened, quiet, events, _⟩ :=
    align_activation_with_local_redraw left right leftBound rightBound leftOpen leftQuiet rightOpen rightQuiet
      current stable past input event (fun source _ _ _ => redrawAtReuse_of_supply stable supply source trivial) observe recovery commutative respect
  exact ⟨moved, bounded, cut, order, commands, endpoint, opened, quiet, events⟩

/-- Equal surviving command words align complete quiet open histories.
The local redraw condition supplies the needed changes of draw. -/
theorem align_surviving_schedules_with_reuse_resolution {leftLength rightLength : Nat}
    (left : Trace (encodeProgram program) leftLength) (right : Trace (encodeProgram program) rightLength)
    (leftOpen : ¬ Nonempty (ClosedEpisode left)) (leftQuiet : Progress.Quiet (left.state leftLength))
    (rightOpen : ¬ Nonempty (ClosedEpisode right)) (rightQuiet : Progress.Quiet (right.state rightLength))
    (stable : ChildContinuations (encodeProgram program)) (input : orchestrationInput left = orchestrationInput right)
    (observe : ∀ key, Setoid (V key))
    (resolve : ∀ source : Trace (encodeProgram program) rightLength,
      orchestrationInput source = orchestrationInput left →
      (addressedEvents source).Perm (addressedEvents right) →
      GuardedIncarnationRedraw.LiveDomainRenaming (right.state rightLength) (source.state rightLength) →
      ∀ start, @ResolveWaitingReuseFor Name Key Code _ _ V ops program
        (TypedCoeffectReplay.setoid observe) rightLength source start)
    (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r) :
    letI : Setoid A := TypedCoeffectReplay.setoid observe
    ∃ moved : Trace (encodeProgram program) rightLength,
      leftLength = rightLength ∧ CutAgreement left moved leftLength ∧
      (∀ time, time < leftLength → addressedEventAt left time = addressedEventAt moved time) ∧
      orchestrationInput moved = orchestrationInput right ∧ ProjectedAgreement (right.state rightLength) (moved.state rightLength) ∧
      (¬ Nonempty (ClosedEpisode moved)) ∧ Progress.Quiet (moved.state rightLength) ∧
      (addressedEvents moved).Perm (addressedEvents right) ∧ ScheduleAlignmentPath right moved := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  have align (remaining : Nat) {start : Nat} (source : Trace (encodeProgram program) rightLength)
      (count : start + remaining = leftLength) (inside : start ≤ rightLength)
      (opened : ¬ Nonempty (ClosedEpisode source)) (settled : Progress.Quiet (source.state rightLength))
      (current : CutAgreement left source start)
      (past : ∀ i, i < start → addressedEventAt left i = addressedEventAt source i)
      (commands : orchestrationInput left = orchestrationInput source)
      (permutation : (addressedEvents source).Perm (addressedEvents right))
      (endpointFromRight : ProjectedAgreement (right.state rightLength) (source.state rightLength)) :
      ∃ moved : Trace (encodeProgram program) rightLength,
        leftLength = rightLength ∧ CutAgreement left moved leftLength ∧
        (∀ time, time < leftLength → addressedEventAt left time = addressedEventAt moved time) ∧
        orchestrationInput moved = orchestrationInput source ∧
        ProjectedAgreement (source.state rightLength) (moved.state rightLength) ∧
        (¬ Nonempty (ClosedEpisode moved)) ∧ Progress.Quiet (moved.state rightLength) ∧
        (addressedEvents moved).Perm (addressedEvents source) ∧ ScheduleAlignmentPath source moved := by
    induction remaining generalizing start source with
    | zero =>
      obtain rfl : start = leftLength := by omega
      have same := matched_endpoint_is_terminal left source inside current past commands leftQuiet settled opened
      exact ⟨source, same, current, past, rfl, ProjectedAgreement.refl _, opened, settled, .refl _, .refl _⟩
    | succ remaining ih =>
      have leftBound : start < leftLength := by omega
      have next : ∃ mid : Trace (encodeProgram program) rightLength,
          start < rightLength ∧ CutAgreement left mid (start + 1) ∧
          (∀ i, i < start + 1 → addressedEventAt left i = addressedEventAt mid i) ∧
          orchestrationInput mid = orchestrationInput source ∧
          ProjectedAgreement (source.state rightLength) (mid.state rightLength) ∧
          (¬ Nonempty (ClosedEpisode mid)) ∧ Progress.Quiet (mid.state rightLength) ∧
          (addressedEvents mid).Perm (addressedEvents source) ∧ ScheduleAlignmentPath source mid := by
        cases event : left.event start with
        | command command =>
          obtain ⟨mid, _, path, _, canAdvance, _, _, _, longer, cut, openMid, quietMid⟩ :=
            GuardedCommandAlignment.normalize_suffix_to_match_pending_command left source leftBound inside
              opened settled current stable past commands event
          have step : ScheduleAlignmentPath source mid := .command path
          obtain ⟨endpoint, events⟩ := step.preserves
          exact ⟨mid, canAdvance, cut, longer, step.input_eq, endpoint, openMid, quietMid, events, step⟩
        | lifecycle kind actor =>
          by_cases dependent : ∃ (span : Nat) (command : OrchestrationSorting.Command Name Key Code),
              start + 1 + span < leftLength ∧ left.event (start + 1 + span) = .command command ∧
              GuardedBirthMatching.BornAt left command.actor (start + 1) ∧
              ∀ cut, start + 1 ≤ cut → cut < start + 1 + span →
                ∃ label name, left.event cut = .lifecycle label name
          · obtain ⟨span, command, leftNext, leftCommand, leftBorn, block⟩ := dependent
            obtain ⟨mid, canAdvance, ordered, nextCut, openMid, quietMid, path⟩ :=
              align_required_birth_before_delayed_command left source leftNext inside leftOpen leftQuiet opened settled
                current stable past commands event leftCommand leftBorn block observe recovery commutative respect
            obtain ⟨endpoint, events⟩ := path.preserves
            exact ⟨mid, canAdvance, nextCut, ordered, path.input_eq, endpoint, openMid, quietMid, events, path⟩
          · by_cases requiredParent : GuardedCommandAlignment.CommandsAtBirthBarriersFrom left start ∧
                ∃ (span : Nat) (command : OrchestrationSorting.Command Name Key Code),
                  start + span + 1 < leftLength ∧ left.event (start + span + 1) = .command command ∧
                  ((left.notes start).1 actor = (left.notes (start + span)).1 (left.actor (start + span)) ∨
                    RequiredAncestor left start actor (start + span + 1) command.actor) ∧
                  ∀ cut, start ≤ cut → cut < start + span + 1 →
                    ∃ label name, left.event cut = .lifecycle label name
            · obtain ⟨normal, span, command, leftNext, leftCommand, required, block⟩ := requiredParent
              obtain ⟨mid, canAdvance, ordered, nextCut, openMid, quietMid, path⟩ :=
                align_required_actor_from_matched_cut left source leftNext inside leftOpen leftQuiet opened settled
                  normal current stable past commands event leftCommand required block observe recovery commutative respect
              obtain ⟨endpoint, events⟩ := path.preserves
              exact ⟨mid, canAdvance, nextCut, ordered, path.input_eq, endpoint, openMid, quietMid, events, path⟩
            · exact align_activation_with_reuse_resolution left source leftBound inside leftOpen leftQuiet opened settled
                current stable past commands event observe
                (fun intermediate same events domain => resolve intermediate same (events.trans permutation)
                  ((GuardedIncarnationRedraw.live_domain_of_projected_agreement endpointFromRight).trans domain) start)
                recovery commutative respect
      obtain ⟨mid, canAdvance, cut, longer, words, firstEndpoint, openMid, quietMid, midEvents, firstPath⟩ := next
      obtain ⟨moved, same, final, schedule, word, lastEndpoint, openEnd, quietEnd, finalEvents, restPath⟩ := ih mid (start := start + 1)
        (by omega) (by omega) openMid quietMid cut longer (commands.trans words.symm) (midEvents.trans permutation)
        (endpointFromRight.trans firstEndpoint)
      exact ⟨moved, same, final, schedule, word.trans words, firstEndpoint.trans lastEndpoint, openEnd, quietEnd,
        finalEvents.trans midEvents, firstPath.trans restPath⟩
  exact align leftLength (start := 0) right (Nat.zero_add _) (Nat.zero_le _) rightOpen rightQuiet
    (match_open_prefix left right stable 0 (Nat.zero_le _) (Nat.zero_le _) (fun _ impossible => by omega))
    (fun _ impossible => by omega) input (.refl _) (.refl _)

theorem align_surviving_schedules_with_waiting_redraw {leftLength rightLength : Nat}
    (left : Trace (encodeProgram program) leftLength) (right : Trace (encodeProgram program) rightLength)
    (leftOpen : ¬ Nonempty (ClosedEpisode left)) (leftQuiet : Progress.Quiet (left.state leftLength))
    (rightOpen : ¬ Nonempty (ClosedEpisode right)) (rightQuiet : Progress.Quiet (right.state rightLength))
    (stable : ChildContinuations (encodeProgram program)) (input : orchestrationInput left = orchestrationInput right)
    (redraw : ∀ source : Trace (encodeProgram program) rightLength,
      orchestrationInput source = orchestrationInput left →
      (addressedEvents source).Perm (addressedEvents right) →
      GuardedIncarnationRedraw.LiveDomainRenaming (right.state rightLength) (source.state rightLength) →
      ∀ start, RedrawAtWaitingReuseFor source start)
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r) :
    letI : Setoid A := TypedCoeffectReplay.setoid observe
    ∃ moved : Trace (encodeProgram program) rightLength,
      leftLength = rightLength ∧ CutAgreement left moved leftLength ∧
      (∀ time, time < leftLength → addressedEventAt left time = addressedEventAt moved time) ∧
      orchestrationInput moved = orchestrationInput right ∧ ProjectedAgreement (right.state rightLength) (moved.state rightLength) ∧
      (¬ Nonempty (ClosedEpisode moved)) ∧ Progress.Quiet (moved.state rightLength) ∧
      (addressedEvents moved).Perm (addressedEvents right) ∧ ScheduleAlignmentPath right moved := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  exact align_surviving_schedules_with_reuse_resolution left right leftOpen leftQuiet rightOpen rightQuiet
    stable input observe (fun source same events domain start => (redraw source same events domain start).resolve)
    recovery commutative respect

theorem align_surviving_schedules_with_local_redraw {leftLength rightLength : Nat}
    (left : Trace (encodeProgram program) leftLength) (right : Trace (encodeProgram program) rightLength)
    (leftOpen : ¬ Nonempty (ClosedEpisode left)) (leftQuiet : Progress.Quiet (left.state leftLength))
    (rightOpen : ¬ Nonempty (ClosedEpisode right)) (rightQuiet : Progress.Quiet (right.state rightLength))
    (stable : ChildContinuations (encodeProgram program)) (input : orchestrationInput left = orchestrationInput right)
    (redraw : ∀ source : Trace (encodeProgram program) rightLength,
      orchestrationInput source = orchestrationInput left →
      (addressedEvents source).Perm (addressedEvents right) →
      GuardedIncarnationRedraw.LiveDomainRenaming (right.state rightLength) (source.state rightLength) →
      RedrawAtReuseFor source)
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r) :
    letI : Setoid A := TypedCoeffectReplay.setoid observe
    ∃ moved : Trace (encodeProgram program) rightLength,
      leftLength = rightLength ∧ CutAgreement left moved leftLength ∧
      (∀ time, time < leftLength → addressedEventAt left time = addressedEventAt moved time) ∧
      orchestrationInput moved = orchestrationInput right ∧ ProjectedAgreement (right.state rightLength) (moved.state rightLength) ∧
      (¬ Nonempty (ClosedEpisode moved)) ∧ Progress.Quiet (moved.state rightLength) ∧
      (addressedEvents moved).Perm (addressedEvents right) ∧ ScheduleAlignmentPath right moved := by
  exact align_surviving_schedules_with_waiting_redraw left right leftOpen leftQuiet rightOpen rightQuiet stable input
    (fun source same events domain start => (redraw source same events domain).at_waiting_reuse start)
    observe recovery commutative respect

theorem align_surviving_schedules_with_spare_names {leftLength rightLength : Nat}
    (left : Trace (encodeProgram program) leftLength) (right : Trace (encodeProgram program) rightLength)
    (leftOpen : ¬ Nonempty (ClosedEpisode left)) (leftQuiet : Progress.Quiet (left.state leftLength))
    (rightOpen : ¬ Nonempty (ClosedEpisode right)) (rightQuiet : Progress.Quiet (right.state rightLength))
    (stable : ChildContinuations (encodeProgram program)) (input : orchestrationInput left = orchestrationInput right)
    (supply : ∀ used : List Name, ∃ spare, spare ∉ used)
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r) :
    letI : Setoid A := TypedCoeffectReplay.setoid observe
    ∃ moved : Trace (encodeProgram program) rightLength,
      leftLength = rightLength ∧ CutAgreement left moved leftLength ∧
      (∀ time, time < leftLength → addressedEventAt left time = addressedEventAt moved time) ∧
      orchestrationInput moved = orchestrationInput right ∧ ProjectedAgreement (right.state rightLength) (moved.state rightLength) ∧
      (¬ Nonempty (ClosedEpisode moved)) ∧ Progress.Quiet (moved.state rightLength) ∧
      (addressedEvents moved).Perm (addressedEvents right) ∧ ScheduleAlignmentPath right moved := by
  exact align_surviving_schedules_with_local_redraw left right leftOpen leftQuiet rightOpen rightQuiet stable input
    (fun source _ _ _ => redrawAtReuse_of_supply stable supply source trivial) observe recovery commutative respect

end Cordis.Repairs.GuardedCompleteAlignment
