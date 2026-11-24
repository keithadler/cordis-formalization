import Cordis.Repairs.GuardedAddressSchedule

/-! Replay surviving steps under a chosen rematching of vacant names.
Open rules use only the projected cut and append to the actual saved word. -/
namespace Cordis.Repairs.GuardedDrawReplay
open Calculus Stages LegalHistory GuardedHistory GuardedCutState
open GuardedLandingMatching (ChildContinuations)
open GuardedBirthAddresses GuardedAddressSchedule GuardedScheduleMatching
open OrchestrationSorting (Command)

universe u
variable {Name Key Value Code Error : Type u} [DecidableEq Name] [DecidableEq Key]
variable {program : Code → Instruction Name Key Value Code Error}
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
local notation "P" => Renaming.Permutation Name

omit [DecidableEq Name] [DecidableEq Key] in
private theorem row_at_projection {left right : R} (equation : project left = project right)
    {actor : Name} {row : F} (found : left actor = some row) :
    ∃ entry, right actor = some entry ∧ projectFiber actor row = projectFiber actor entry := by
  have rows := congrFun equation actor
  cases current : right actor with
  | none => simp [project, found, current] at rows
  | some entry => exact ⟨entry, rfl, Option.some.inj (by simpa [project, found, current] using rows)⟩

private theorem land_from_projection {left middle right : R} (equation : project left = project right)
    {actor : Name} {code : Code} {token} {next : Option Code} (landed : Land program actor code left middle token next) :
    ∃ after, Land program actor code right after token next ∧ project middle = project after := by
  cases landed with
  | unit _ _ _ action => exact ⟨right, .unit _ _ _ action, equation⟩
  | provide _ _ _ row key value action found declared empty =>
    obtain ⟨entry, present, agrees⟩ := row_at_projection equation found
    have component := congrArg Fiber.component agrees
    have table := congrArg Fiber.table agrees
    change row.component = entry.component at component
    change row.table = entry.table at table
    refine ⟨_, .provide right actor code entry key value action present (component ▸ declared) (table ▸ empty), ?_⟩
    rw [project_write, project_write, equation]
  | operate _ _ _ key run owner before after inverse value action located evaluated =>
    have locationEq : location left actor key = location right actor key := by
      rw [← project_location left, equation, project_location right]
    refine ⟨_, .operate right actor code key run owner before after inverse value action (locationEq ▸ located) evaluated, ?_⟩
    rw [project_write, project_write, equation]
  | instantiate _ _ _ component child action ready =>
    have ready' := (project_insertable left child component (some actor)).mpr ready
    rw [equation] at ready'
    refine ⟨_, .instantiate right actor code component child action ((project_insertable _ _ _ _).mp ready'), ?_⟩
    rw [project_put, project_put, equation]

omit [DecidableEq Key] in
/-- The destination of a native command is determined by a projected cut.
The target registry keeps its own saved words and unused view coordinates. -/
theorem command_from_projection (command : Command Name Key Code) {left right after : R}
    (equation : project left = project right) (step : command.Step left after) :
    command.Step right (command.apply right) ∧ project after = project (command.apply right) := by
  obtain ⟨enabled, rfl⟩ := step
  cases command with
  | insert name component =>
    have ready := (project_insertable left name component none).mpr enabled
    rw [equation] at ready
    refine ⟨⟨(project_insertable _ _ _ _).mp ready, rfl⟩, ?_⟩
    simp only [Command.apply, project_put, equation]
  | retire name =>
    have present : project left name ≠ none := fun vacant => enabled ((project_present _ _).mp vacant)
    rw [equation] at present
    exact ⟨⟨fun vacant => present ((project_present _ _).mpr vacant), rfl⟩,
      by simp only [Command.apply, project_retire, equation]⟩
  | remove name =>
    have ready := (project_removable left name).mpr enabled
    rw [equation] at ready
    exact ⟨⟨(project_removable _ _).mp ready, rfl⟩,
      by simp only [Command.apply, project_erase, equation]⟩

omit [DecidableEq Name] [DecidableEq Key] in
private theorem reloading_at_projection {left right : R} (equation : project left = project right)
    {actor : Name} {row : F} (found : left actor = some row) {code word originalView}
    (phase : row.phase = .reloading code word originalView) :
    ∃ entry otherWord otherView, right actor = some entry ∧ entry.phase = .reloading code otherWord otherView ∧
      row.component = entry.component ∧
      requiredView actor row.component.requires originalView = requiredView actor entry.component.requires otherView := by
  obtain ⟨entry, present, agrees⟩ := row_at_projection equation found
  have components := congrArg Fiber.component agrees
  change row.component = entry.component at components
  have phases := congrArg Fiber.phase agrees
  cases otherPhase : entry.phase with
  | reloading otherCode otherWord otherView =>
    simp [projectFiber, projectPhase, phase, otherPhase] at phases
    exact ⟨entry, otherWord, otherView, present, phases.1.symm ▸ otherPhase, components, phases.2⟩
  | inactive | active | unloading => simp [projectFiber, projectPhase, phase, otherPhase] at phases

omit [DecidableEq Name] [DecidableEq Key] in
private theorem target_from_projection {left right : R} (equation : project left = project right)
    {actor : Name} {view : View Name Key} (target : Target left actor view) : Target right actor view := by
  have projected := (project_target left actor view).mpr target
  rw [equation] at projected
  exact (project_target right actor view).mp projected

omit [DecidableEq Name] [DecidableEq Key] in
private theorem target_of_required_view {state : R} {actor : Name} {row : F} (found : state actor = some row)
    {first second : View Name Key} (agrees : requiredView actor row.component.requires first =
      requiredView actor row.component.requires second) (ready : Target state actor first) : Target state actor second := by
  simp only [Target, found] at ready ⊢
  refine ⟨ready.1, fun key required => ?_⟩
  have atKey : first key = second key := by simpa [requiredView, required] using congrFun agrees key
  exact atKey ▸ ready.2 key required

/-- An open activation replays under exact projected equality with the
same primitive outcome and the target cut's actual accumulator. -/
theorem activation_from_projection {left right after : R} (equation : project left = project right)
    {rule : Labeled.Rule} {actor : Name} (step : Labeled.Step program rule actor left after)
    (activation : Transposition.Activation rule) :
    ∃ moved, Labeled.Step program rule actor right moved ∧ project after = project moved := by
  cases step with
  | begin _ _ row view found phase _ ready =>
    obtain ⟨entry, present, agrees⟩ := row_at_projection equation found
    have components := congrArg Fiber.component agrees
    change row.component = entry.component at components
    have phases := congrArg Fiber.phase agrees
    have inactive : entry.phase = .inactive := by
      cases current : entry.phase <;> simp [projectFiber, projectPhase, phase, current] at phases ⊢
    refine ⟨_, .begin right actor entry view present inactive (by simp [ErrorFree, present])
      (target_from_projection equation ready), ?_⟩
    rw [project_mark left actor found, project_mark right actor present, equation, components]
  | iter _ middle _ row code word view inverse next found phase ready landed =>
    obtain ⟨entry, nextWord, nextView, present, reloading, components, views⟩ := reloading_at_projection equation found phase
    have target := target_of_required_view present (components ▸ views) (target_from_projection equation ready)
    obtain ⟨moved, landed', related⟩ := land_from_projection equation landed
    obtain ⟨firstTable, firstFound⟩ := Transposition.land_existing_table program landed actor row found
    obtain ⟨otherTable, otherFound⟩ := Transposition.land_existing_table program landed' actor entry present
    refine ⟨_, .iter right moved actor entry code nextWord nextView inverse next present reloading target landed', ?_⟩
    rw [project_mark middle actor firstFound, project_mark moved actor otherFound, related]
    simp only [projectPhase]
    rw [views]
  | finish _ middle _ row code word view inverse found phase ready landed =>
    obtain ⟨entry, nextWord, nextView, present, reloading, components, views⟩ := reloading_at_projection equation found phase
    have target := target_of_required_view present (components ▸ views) (target_from_projection equation ready)
    obtain ⟨moved, landed', related⟩ := land_from_projection equation landed
    obtain ⟨firstTable, firstFound⟩ := Transposition.land_existing_table program landed actor row found
    obtain ⟨otherTable, otherFound⟩ := Transposition.land_existing_table program landed' actor entry present
    refine ⟨_, .finish right moved actor entry code nextWord nextView inverse present reloading target landed', ?_⟩
    rw [project_mark middle actor firstFound, project_mark moved actor otherFound, related]
    simp only [projectPhase]
    rw [views]
  | _ => simp [Transposition.Activation] at activation

/-- A projected cut can execute an actual open-history event under the
chosen permutation. The real step carries the destination's saved words,
and the same program selects its continuation on the new draw. -/
theorem open_event_from_renamed_projection {last time : Nat} (trace : Trace program last) (bounded : time < last)
    (openOnly : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    (stable : ChildContinuations program) (p : P) {target : R}
    (equation : Renaming.registry p (project (trace.state time)) = project target)
    (notes : Vestigial.CutNotes Name Key Value) :
    ∃ after, GuardedSuffix.Transition program notes (GuardedRenaming.event p (trace.event time)) target after ∧
      Renaming.registry p (project (trace.state (time + 1))) = project after := by
  have states : project (Renaming.registry p (trace.state time)) = project target := by rw [project_rename, equation]
  cases event : trace.event time with
  | command cmd =>
    have step := (trace.step time bounded).1
    rw [event] at step
    obtain ⟨moved, projected⟩ := command_from_projection (GuardedRenaming.command p cmd) states
      (GuardedRenaming.command_step p cmd step)
    exact ⟨_, moved, (project_rename p _).symm.trans projected⟩
  | lifecycle kind actor =>
    obtain ⟨activation, step⟩ := trace.activation_at openOnly quiet bounded event
    have branches : Renaming.PreservesChildBranches p program := fun code component action child =>
      stable code component action (p.toFun child) child
    obtain ⟨after, moved, projected⟩ := activation_from_projection states (Renaming.labeled_step_map_same p branches step) activation
    have ordinary : kind ≠ .unload := by
      intro unload
      subst kind
      simp [Transposition.Activation, Lifecycle.rule] at activation
    exact ⟨after, lifecycle_transition ordinary moved, (project_rename p _).symm.trans projected⟩

/-- Replay a complete open history using the supplied draw at each event.
The permutations may change between events, provided they agree on the
incarnations still live at the intervening cut. Each old word on the new
trace keeps the tokens it actually captured, even after its raw name is reused. -/
theorem replay_with_consistent_names {last : Nat} (trace : Trace program last)
    (openOnly : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    (stable : ChildContinuations program) (names : Nat → P)
    (keeps : ∀ time, time < last → ∀ name, trace.state (time + 1) name ≠ none →
      (names time).toFun name = (names (time + 1)).toFun name) :
    ∃ moved : Trace program last,
      (∀ time, time < last → moved.event time = GuardedRenaming.event (names time) (trace.event time)) ∧
      (∀ time, time ≤ last → Renaming.registry (names time) (project (trace.state time)) = project (moved.state time) ∧
        ∀ name, (moved.notes time).1 ((names time).toFun name) = (trace.notes time).1 name) ∧
      (¬ Nonempty (ClosedEpisode moved)) ∧ Progress.Quiet (moved.state last) := by
  have replay (time : Nat) (bounded : time ≤ last) : ∃ built : Trace program time,
      (∀ cut, cut < time → built.event cut = GuardedRenaming.event (names cut) (trace.event cut)) ∧
      ∀ cut, cut ≤ time → Renaming.registry (names cut) (project (trace.state cut)) = project (built.state cut) ∧
        ∀ name, (built.notes cut).1 ((names cut).toFun name) = (trace.notes cut).1 name := by
    induction time with
    | zero =>
      let built : Trace program 0 := ⟨trace.state, trace.notes, trace.event, trace.start, trace.seed,
        fun _ h => False.elim (by omega)⟩
      refine ⟨built, fun _ h => False.elim (by omega), ?_⟩
      intro cut valid
      obtain rfl : cut = 0 := by omega
      change Renaming.registry (names 0) (project (trace.state 0)) = project (trace.state 0) ∧
        ∀ name, (trace.notes 0).1 ((names 0).toFun name) = (trace.notes 0).1 name
      rw [trace.start, trace.seed]
      exact ⟨rfl, fun _ => rfl⟩
    | succ time ih =>
      have inside : time < last := by omega
      obtain ⟨built, labels, cuts⟩ := ih (by omega)
      have ⟨states, tags⟩ := cuts time (Nat.le_refl _)
      obtain ⟨after, actual, mapped⟩ := open_event_from_renamed_projection trace inside openOnly quiet stable
        (names time) states (built.notes time)
      let event := GuardedRenaming.event (names time) (trace.event time)
      let recorded := Vestigial.noteStep (built.state time) after (Vestigial.eventActor event) (time + 1) (built.notes time)
      let next := built.extendAt (time := time) (Nat.le_refl _) (event := event) (after := after) (recorded := recorded) ⟨actual, rfl⟩
      have prevState (cut : Nat) (old : cut ≤ time) : next.state cut = built.state cut := if_pos old
      have prevNotes (cut : Nat) (old : cut ≤ time) : next.notes cut = built.notes cut := if_pos old
      have nextState : next.state (time + 1) = after := if_neg (by omega)
      have stepMatch : Renaming.registry (names time) (project (trace.state (time + 1))) = project (next.state (time + 1)) := by
        rw [nextState]; exact mapped
      have matchWithNext : Renaming.registry (names (time + 1)) (project (trace.state (time + 1))) =
          project (next.state (time + 1)) :=
        (rename_on_live trace (by omega : time + 1 ≤ last) (keeps time inside)).symm.trans stepMatch
      have absence (p : P) (eq : Renaming.registry p (project (trace.state (time + 1))) = project (next.state (time + 1)))
          (name : Name) : next.state (time + 1) (p.toFun name) = none ↔ trace.state (time + 1) name = none := by
        rw [← project_present (next.state (time + 1)), ← eq, Renaming.registry_at]
        simp [project_present]
      have nextTags := GuardedBirthMatching.advance_cut trace next inside (Nat.lt_succ_self time) (p := names time) (stamp := id)
        (fun name => by rw [prevNotes time (Nat.le_refl _)]; simpa only [Option.map_id] using tags name)
        (absence (names time) stepMatch) rfl
      refine ⟨next, ?_, ?_⟩
      · intro cut before
        rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ before) with rfl | old
        · exact if_neg (Nat.lt_irrefl _)
        · exact (if_pos old).trans (labels cut old)
      · intro cut valid
        by_cases old : cut ≤ time
        · rw [prevState cut old, prevNotes cut old]
          exact cuts cut old
        · obtain rfl : cut = time + 1 := by omega
          refine ⟨matchWithNext, fun name => ?_⟩
          by_cases vacant : trace.state (time + 1) name = none
          · rw [(trace.births_agree _ bounded name).mpr vacant]
            exact (next.births_agree _ (Nat.le_refl _) _).mpr ((absence _ matchWithNext _).mpr vacant)
          · rw [← keeps time inside name vacant]
            simpa only [Option.map_id] using nextTags name
  obtain ⟨moved, labels, cuts⟩ := replay last (Nat.le_refl _)
  refine ⟨moved, labels, cuts, ?_, ?_⟩
  · rintro ⟨episode⟩
    have within := episode.interval.bounded
    have unload := (unload_boundary moved episode.interval).1
    rw [labels _ within] at unload
    cases source : trace.event episode.closed with
    | command cmd => simp [GuardedRenaming.event, source] at unload
    | lifecycle kind name =>
      have kindEq : kind = .unload := (Event.lifecycle.inj (by simpa only [GuardedRenaming.event, source] using unload)).1
      subst kind
      exact trace.no_unload openOnly within source
  · have projected := (project_quiet_iff _).mpr quiet
    have remapped := GuardedRenaming.quiet_transport (names last) projected
    rw [(cuts last (Nat.le_refl _)).1] at remapped
    exact (project_quiet_iff _).mp remapped

private theorem count_with_same_prefix (left right : Nat → Bool) {cut : Nat}
    (same : ∀ i, i < cut → left i = right i) : occurrencesBefore left cut = occurrencesBefore right cut := by
  induction cut with
  | zero => rfl
  | succ cut ih =>
    rw [occurrencesBefore, occurrencesBefore, same cut (by omega), ih (fun i before => same i (by omega))]

/-- Moving the raw names cyclically or changing them between incarnations
does not change the address assigned to any actual birth. -/
theorem birth_addresses_of_consistent_names {last : Nat} (trace moved : Trace program last) (names : Nat → P)
    (labels : ∀ time, time < last → moved.event time = GuardedRenaming.event (names time) (trace.event time))
    (cuts : ∀ time, time ≤ last → Renaming.registry (names time) (project (trace.state time)) = project (moved.state time) ∧
      ∀ name, (moved.notes time).1 ((names time).toFun name) = (trace.notes time).1 name)
    (keeps : ∀ time, time < last → ∀ name, trace.state (time + 1) name ≠ none →
      (names time).toFun name = (names (time + 1)).toFun name)
    {birth : Nat} {path : Address} (addressed : Addressed trace birth path) : Addressed moved birth path := by
  have rootEq {time : Nat} (bounded : time < last) : isRootInsertion trace time = isRootInsertion moved time := by
    rw [isRootInsertion, isRootInsertion, labels time bounded]
    cases event : trace.event time with
    | lifecycle => rfl
    | command cmd => cases cmd <;> rfl
  have sameRule {time : Nat} (bounded : time < last) : moved.rule time = trace.rule time := by
    rw [Trace.rule, Trace.rule, labels time bounded]
    cases event : trace.event time with
    | lifecycle => rfl
    | command cmd => cases cmd <;> rfl
  have sameTag {time : Nat} (bounded : time < last) : (moved.notes time).1 (moved.actor time) =
      (trace.notes time).1 (trace.actor time) := by
    simp only [Trace.actor, labels time bounded, GuardedRenaming.actor_event]
    exact (cuts time (Nat.le_of_lt bounded)).2 _
  have sameStage (parentBirth : Nat) {time : Nat} (bounded : time < last) :
      isParentStage trace parentBirth time = isParentStage moved parentBirth time := by
    simp only [isParentStage, sameRule bounded, sameTag bounded]
  have vacant_iff {time : Nat} (bounded : time ≤ last) (name : Name) :
      moved.state time ((names time).toFun name) = none ↔ trace.state time name = none := by
    rw [← project_present (moved.state time), ← (cuts time bounded).1, Renaming.registry_at]
    simp [project_present]
  induction addressed with
  | @root time name component bounded event =>
    have movedEvent : moved.event time = .command (.insert ((names time).toFun name) component) := by
      rw [labels time bounded, event]; rfl
    have sameCount := count_with_same_prefix (isRootInsertion trace) (isRootInsertion moved) (cut := time)
      (fun i prior => rootEq (by omega : i < last))
    rw [sameCount]
    exact .root bounded movedEvent
  | @child time parentBirth name parent bounded rule vacant born stamp addressed ih =>
    have vacantMoved := (vacant_iff (Nat.le_of_lt bounded) name).mpr vacant
    have bornMoved : moved.state (time + 1) ((names time).toFun name) ≠ none := by
      rw [keeps time bounded name born]
      exact fun missing => born ((vacant_iff (Nat.succ_le_of_lt bounded) name).mp missing)
    have sameCount := count_with_same_prefix (isParentStage trace parentBirth) (isParentStage moved parentBirth) (cut := time)
      (fun i prior => sameStage parentBirth (by omega : i < last))
    rw [sameCount]
    exact .child bounded ((sameRule bounded).symm ▸ rule) vacantMoved bornMoved
      ((sameTag bounded).trans stamp) ih

/-- Whole-history renaming may change at a vacant name. Every existing
target's birth address and exact component stay in the addressed word. -/
theorem command_input_of_consistent_names {last : Nat} (trace moved : Trace program last) (names : Nat → P)
    (labels : ∀ time, time < last → moved.event time = GuardedRenaming.event (names time) (trace.event time))
    (cuts : ∀ time, time ≤ last → Renaming.registry (names time) (project (trace.state time)) = project (moved.state time) ∧
      ∀ name, (moved.notes time).1 ((names time).toFun name) = (trace.notes time).1 name)
    (keeps : ∀ time, time < last → ∀ name, trace.state (time + 1) name ≠ none →
      (names time).toFun name = (names (time + 1)).toFun name)
    (rootNames : ∀ {time name component}, time < last → trace.event time = .command (.insert name component) →
      (names time).toFun name = name) : orchestrationInput moved = orchestrationInput trace := by
  have target (time : Nat) (bounded : time < last) {name path component}
      (found : targetAt trace time name = some (path, component)) :
      targetAt moved time ((names time).toFun name) = some (path, component) := by
    obtain ⟨birth, old, tag, address, present, payload⟩ := (targetAt_eq_some trace).mp found
    have movedAddress := birth_addresses_of_consistent_names trace moved names labels cuts keeps address
    have compared := congrFun (cuts time (Nat.le_of_lt bounded)).1 ((names time).toFun name)
    rw [Renaming.registry_at] at compared
    cases new : moved.state time ((names time).toFun name) with
    | none => simp [project, present, new] at compared
    | some row =>
      have projected : Renaming.fiber (names time) (projectFiber name old) = projectFiber ((names time).toFun name) row :=
        Option.some.inj (by simpa only [project, present, new, Option.map_some] using compared)
      have part := congrArg Fiber.component projected
      change old.component = row.component at part
      exact (targetAt_eq_some moved).mpr ⟨birth, row, ((cuts time (Nat.le_of_lt bounded)).2 name).trans tag,
        movedAddress, new, part.symm.trans payload⟩
  have same (time : Nat) (bounded : time < last) : commandAt moved time = commandAt trace time := by
    cases event : trace.event time with
    | lifecycle => simp [commandAt, labels time bounded, event, GuardedRenaming.event]
    | command cmd =>
      cases cmd with
      | insert name component =>
        simp [commandAt, labels time bounded, event, GuardedRenaming.event, GuardedRenaming.command, rootNames bounded event]
      | retire name =>
        obtain ⟨_, _, pin⟩ := targetAt_command trace bounded (.inl event)
        simp [commandAt, labels time bounded, event, GuardedRenaming.event, GuardedRenaming.command, pin,
          target time bounded pin]
      | remove name =>
        obtain ⟨_, _, pin⟩ := targetAt_command trace bounded (.inr event)
        simp [commandAt, labels time bounded, event, GuardedRenaming.event, GuardedRenaming.command, pin,
          target time bounded pin]
  have mapEq : (List.range last).map (commandAt moved) = (List.range last).map (commandAt trace) := by
    apply List.map_congr_left
    exact fun time member => same time (List.mem_range.mp member)
  simpa only [orchestrationInput, List.filterMap_map, Function.id_comp] using congrArg (List.filterMap id) mapEq

/-- The replay also preserves the addressed event schedule at each cut. -/
theorem addressed_event_of_consistent_names {last : Nat} (trace moved : Trace program last) (names : Nat → P)
    (labels : ∀ time, time < last → moved.event time = GuardedRenaming.event (names time) (trace.event time))
    (cuts : ∀ time, time ≤ last → Renaming.registry (names time) (project (trace.state time)) = project (moved.state time) ∧
      ∀ name, (moved.notes time).1 ((names time).toFun name) = (trace.notes time).1 name)
    (keeps : ∀ time, time < last → ∀ name, trace.state (time + 1) name ≠ none →
      (names time).toFun name = (names (time + 1)).toFun name)
    {time : Nat} (bounded : time < last) : addressedEventAt moved time = addressedEventAt trace time := by
  have sameActor : moved.actor time = (names time).toFun (trace.actor time) := by
    simp only [Trace.actor, labels time bounded, GuardedRenaming.actor_event]
  have actorKey : actorAddress moved time = actorAddress trace time := by
    have synced := (cuts time (Nat.le_of_lt bounded)).2 (trace.actor time)
    cases known : (trace.notes time).1 (trace.actor time) with
    | none => simp [actorAddress, sameActor, synced, known]
    | some birth =>
      have first := GuardedBirthMatching.recorded_birth trace (Nat.le_of_lt bounded) known
      obtain ⟨path, address⟩ := exists_address trace first.1
      have movedAddress := birth_addresses_of_consistent_names trace moved names labels cuts keeps address
      exact ((actorAddress_eq_some moved).mpr ⟨birth, by rw [sameActor, synced, known], movedAddress⟩).trans
        ((actorAddress_eq_some trace).mpr ⟨birth, known, address⟩).symm
  cases event : trace.event time with
  | lifecycle => simp [addressedEventAt, labels time bounded, event, GuardedRenaming.event, actorKey]
  | command cmd =>
    cases cmd <;> simp [addressedEventAt, labels time bounded, event, GuardedRenaming.event, GuardedRenaming.command, actorKey]

/-- The incarnation that a step's renaming must cover. A removal
uses the pre-step incarnation and an allocation uses the new one. -/
def eventBirth {last : Nat} (trace : Trace program last) (cut : Nat) (name : Name) : Option Nat :=
  (trace.notes cut).1 name <|> (trace.notes (min (cut + 1) last)).1 name

private theorem eventBirth_after {last : Nat} (trace : Trace program last)
    {cut : Nat} (bounded : cut < last) {name : Name} {birth : Nat}
    (found : (trace.notes (cut + 1)).1 name = some birth) :
    eventBirth trace cut name = some birth := by
  unfold eventBirth
  rw [Nat.min_eq_left (by omega : cut + 1 ≤ last)]
  cases old : (trace.notes cut).1 name with
  | none => simpa [old] using found
  | some prior =>
    rw [(trace.step cut bounded).2] at found
    change (trace.state (cut + 1) name).map (fun _ => ((trace.notes cut).1 name).getD (cut + 1)) =
      some birth at found
    cases present : trace.state (cut + 1) name <;> simp_all

/-- A name assignment is legal at each event if the rows it touches
have distinct assigned names and the root insertions keep their names. -/
def BirthNameAssignment {last : Nat} (trace : Trace program last) (assign : Nat → Name) : Prop :=
  (∀ cut, cut ≤ last → ∀ {left right a b}, eventBirth trace cut left = some a →
    eventBirth trace cut right = some b → assign a = assign b → left = right) ∧
  (∀ cut name component, cut < last → trace.event cut = .command (.insert name component) →
    assign (cut + 1) = name)

private theorem assignment_permutation {last : Nat} (trace : Trace program last) (assign : Nat → Name)
    (legal : BirthNameAssignment trace assign) (cut : Nat) (bounded : cut ≤ last) :
    ∃ p : P, ∀ name birth, eventBirth trace cut name = some birth → p.toFun name = assign birth := by
  obtain ⟨before, coversBefore⟩ := trace.support_finite cut bounded
  obtain ⟨after, coversAfter⟩ := trace.support_finite (min (cut + 1) last) (Nat.min_le_right _ _)
  let pairs := (before ++ after).filterMap (fun name =>
    (eventBirth trace cut name).map fun birth => (name, assign birth))
  have origin {name target : Name} (member : (name, target) ∈ pairs) :
      ∃ birth, eventBirth trace cut name = some birth ∧ assign birth = target := by
    obtain ⟨source, _, pair⟩ := List.mem_filterMap.mp member
    obtain ⟨birth, fixed, equal⟩ := Option.map_eq_some_iff.mp pair
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
    exact ⟨birth, fixed, rfl⟩
  obtain ⟨p, agrees⟩ := GuardedBirthMatching.extend_pairs pairs
    (fun a b => by
      obtain ⟨first, found, rfl⟩ := origin a
      obtain ⟨second, also, rfl⟩ := origin b
      exact congrArg assign (Option.some.inj (found.symm.trans also)))
    (fun a b => by
      obtain ⟨first, found, exactFirst⟩ := origin a
      obtain ⟨second, also, exactSecond⟩ := origin b
      exact legal.1 cut bounded found also (exactFirst.trans exactSecond.symm))
  refine ⟨p, fun name birth found => agrees (List.mem_filterMap.mpr ⟨name, ?_, by simp [found]⟩)⟩
  apply List.mem_append.mpr
  cases first : trace.state cut name with
  | some row => exact .inl (coversBefore name row first)
  | none =>
    have noPrior := (trace.births_agree cut bounded name).mpr first
    cases second : trace.state (min (cut + 1) last) name with
    | some row => exact .inr (coversAfter name row second)
    | none =>
      have noLater := (trace.births_agree _ (Nat.min_le_right _ _) name).mpr second
      simp [eventBirth, noPrior, noLater] at found

private theorem root_event_birth {last : Nat} (trace : Trace program last)
    {time : Nat} {name : Name} {component : Component Key Code} (bounded : time < last)
    (event : trace.event time = .command (.insert name component)) :
    eventBirth trace time name = some (time + 1) := by
  have step := (trace.step time bounded).1
  rw [event] at step
  have absent := (trace.births_agree _ (Nat.le_of_lt bounded) name).mpr step.1.1
  apply eventBirth_after trace bounded
  rw [(trace.step time bounded).2]
  change (trace.state (time + 1) name).map (fun _ => ((trace.notes time).1 name).getD (time + 1)) = _
  rw [step.2]
  simp [Command.apply, put_self, absent]

/-- A consistent sequence of cut permutations induces one assignment
per actual birth. Its values off the birth stamps are immaterial. -/
theorem birth_assignment_of_consistent_names {last : Nat} (trace : Trace program last)
    (names : Nat → P) (fallback : Name)
    (keeps : ∀ time, time < last → ∀ name, trace.state (time + 1) name ≠ none →
      (names time).toFun name = (names (time + 1)).toFun name)
    (rootNames : ∀ {time name component}, time < last → trace.event time = .command (.insert name component) →
      (names time).toFun name = name) :
    ∃ assign : Nat → Name, BirthNameAssignment trace assign ∧
      ∀ time, time ≤ last → ∀ name birth, eventBirth trace time name = some birth →
        (names time).toFun name = assign birth := by
  classical
  let assign (birth : Nat) : Name :=
    if born : ∃ name, GuardedBirthMatching.BornAt trace name birth then
      (names birth).toFun (Classical.choose born)
    else fallback
  have liveMaps (time : Nat) (bounded : time ≤ last) (name : Name) (birth : Nat)
      (stamp : (trace.notes time).1 name = some birth) : (names time).toFun name = assign birth := by
    obtain ⟨born, _⟩ := GuardedBirthMatching.recorded_birth trace bounded stamp
    have witness : ∃ name, GuardedBirthMatching.BornAt trace name birth := ⟨name, born⟩
    have unique := GuardedBirthMatching.born_unique trace born (Classical.choose_spec witness)
    have indexed := stamp
    rw [trace.notes_eq time bounded] at indexed
    have resident := Incarnation.resident_of_birthAt indexed
    have constant (cut : Nat) (fromBirth : birth ≤ cut) (toTime : cut ≤ time) :
        (names cut).toFun name = (names birth).toFun name := by
      induction cut with
      | zero =>
        obtain rfl : birth = 0 := by omega
        rfl
      | succ cut ih =>
        by_cases atBirth : cut + 1 = birth
        · rw [atBirth]
        · exact (keeps cut (by omega) name (resident.present _ fromBirth toTime)).symm.trans
            (ih (by omega) (by omega))
    simpa only [assign, dif_pos witness, ← unique] using constant time resident.ordered (Nat.le_refl _)
  have maps (time : Nat) (bounded : time ≤ last) (name : Name) (birth : Nat)
      (stamp : eventBirth trace time name = some birth) : (names time).toFun name = assign birth := by
    unfold eventBirth at stamp
    cases before : (trace.notes time).1 name with
    | some earlier =>
      have same : earlier = birth := Option.some.inj (by simpa [before] using stamp)
      exact liveMaps time bounded name birth (before.trans (congrArg some same))
    | none =>
      by_cases prior : time < last
      · have next : (trace.notes (time + 1)).1 name = some birth := by
          simpa [before, Nat.min_eq_left (by omega : time + 1 ≤ last)] using stamp
        have present : trace.state (time + 1) name ≠ none := by
          intro missing
          rw [((trace.births_agree _ (by omega) name).mpr missing)] at next
          cases next
        exact (keeps time prior name present).trans (liveMaps (time + 1) (by omega) name birth next)
      · have atEnd : min (time + 1) last = time := by omega
        simp [before, atEnd] at stamp
  refine ⟨assign, ⟨?_, ?_⟩, maps⟩
  · intro cut bounded left right a b first second same
    exact (names cut).injective ((maps cut bounded left a first).trans (same.trans (maps cut bounded right b second).symm))
  · intro time name component bounded event
    exact (maps time (Nat.le_of_lt bounded) name _ (root_event_birth trace bounded event)).symm.trans
      (rootNames bounded event)

/-- Every collision-free assignment of names to the actual births
replays within the original name set. It preserves addressed events and
literal root insertions, and carries the actual saved words. -/
theorem replay_with_birth_assignment {last : Nat} (trace : Trace program last)
    (opened : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    (stable : ChildContinuations program) (assign : Nat → Name) (legal : BirthNameAssignment trace assign) :
    ∃ (moved : Trace program last) (names : Nat → P),
      (∀ time, time < last → moved.event time = GuardedRenaming.event (names time) (trace.event time)) ∧
      (∀ time, time ≤ last → Renaming.registry (names time) (project (trace.state time)) = project (moved.state time) ∧
        ∀ name, (moved.notes time).1 ((names time).toFun name) = (trace.notes time).1 name) ∧
      (∀ time, time < last → ∀ name, trace.state (time + 1) name ≠ none →
        (names time).toFun name = (names (time + 1)).toFun name) ∧
      (∀ time name component, time < last → trace.event time = .command (.insert name component) →
        (names time).toFun name = name) ∧
      (∀ time, time ≤ last → ∀ name birth, (trace.notes time).1 name = some birth →
        (names time).toFun name = assign birth) ∧
      (¬ Nonempty (ClosedEpisode moved)) ∧ Progress.Quiet (moved.state last) ∧
      orchestrationInput moved = orchestrationInput trace ∧ addressedEvents moved = addressedEvents trace := by
  classical
  let chosen (time : Nat) (bounded : time ≤ last) :=
    Classical.choose (assignment_permutation trace assign legal time bounded)
  let names (time : Nat) : P := if inside : time ≤ last then chosen time inside else Renaming.Permutation.identity
  have mapped (time : Nat) (bounded : time ≤ last) (name : Name) (birth : Nat)
      (found : eventBirth trace time name = some birth) : (names time).toFun name = assign birth := by
    simp only [names, dif_pos bounded]
    exact Classical.choose_spec (assignment_permutation trace assign legal time bounded) name birth found
  have keeps (time : Nat) (bounded : time < last) (name : Name)
      (present : trace.state (time + 1) name ≠ none) :
      (names time).toFun name = (names (time + 1)).toFun name := by
    have nextBound := Nat.succ_le_of_lt bounded
    cases tag : (trace.notes (time + 1)).1 name with
    | none => exact False.elim (present ((trace.births_agree _ nextBound name).mp tag))
    | some birth =>
      exact (mapped time (Nat.le_of_lt bounded) name birth (eventBirth_after trace bounded tag)).trans
        (mapped (time + 1) nextBound name birth (by simp [eventBirth, tag])).symm
  have rootFixed {time name component} (bounded : time < last)
      (event : trace.event time = .command (.insert name component)) : (names time).toFun name = name := by
    exact (mapped time (Nat.le_of_lt bounded) name (time + 1) (root_event_birth trace bounded event)).trans
      (legal.2 time name component bounded event)
  obtain ⟨moved, labels, cuts, stillOpen, stillQuiet⟩ :=
    replay_with_consistent_names trace opened quiet stable names keeps
  exact ⟨moved, names, labels, cuts, keeps, fun _ _ _ => rootFixed,
    fun time bounded name birth found => mapped time bounded name birth (by simp [eventBirth, found]),
    stillOpen, stillQuiet, command_input_of_consistent_names trace moved names labels cuts keeps rootFixed,
    addressedEvents_congr _ _ (fun time bounded => addressed_event_of_consistent_names trace moved names labels cuts keeps bounded)⟩

end Cordis.Repairs.GuardedDrawReplay
