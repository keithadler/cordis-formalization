import Cordis.Repairs.GuardedEpisodeBoundary
import Cordis.Repairs.SupportLinearization
import Cordis.TranspositionActivation

/-! The remaining episodes after deletion use the ordinary activation
rules. This connects the guarded history to the paper's ordering proof. -/
namespace Cordis.Repairs.GuardedHistory
open Calculus Stages LegalHistory
open EpisodeBoundary (prefix_since_absence)
universe u
variable {Name Key Value Code Error : Type u} [DecidableEq Name] [DecidableEq Key]
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
local notation "I" => Inverse Name Key Value
local notation "Program" => Code → Instruction Name Key Value Code Error
variable {program : Code → Stages.Instruction Name Key Value Code Error} {last : Nat}

theorem Trace.no_unload (trace : Trace program last) (openOnly : ¬ Nonempty (ClosedEpisode trace))
    {time : Nat} (bounded : time < last) {actor : Name} :
    trace.event time ≠ .lifecycle .unload actor := by
  intro event
  have step := (trace.step time bounded).1
  rw [event] at step
  have ended := unload_views step actor
  rw [if_pos rfl] at ended
  obtain ⟨row, view, found, phase, _, _⟩ := step
  have installed : ControlFrame.viewAt (trace.state time) actor ≠ none := by
    simp [ControlFrame.viewAt, found, phase, Phase.committed]
  have absent : ControlFrame.viewAt (trace.state 0) actor = none := by
    simp [trace.start, ControlFrame.viewAt]
  obtain ⟨opened, _, segment⟩ :=
    prefix_since_absence (last := last) trace.state actor (Nat.zero_le _) (Nat.le_of_lt bounded) absent installed
  exact openOnly ⟨⟨actor, opened, time,
    ⟨segment.positive, segment.ordered, bounded, segment.installed, segment.before, ended⟩⟩⟩

/-- The native indexed calculus agrees with a guarded trace whose episodes
all survive. Every retained event has the same source and endpoint. -/
def Trace.toIndexed (trace : Trace program last) (openOnly : ¬ Nonempty (ClosedEpisode trace)) :
    Indexed.Trace program (fun _ => none) last where
  state := trace.state
  actor := trace.actor
  rule := trace.rule
  start := trace.start
  step time bounded := by
    rcases transition_cases (trace.step time bounded).1 with native | ⟨actor, event, _⟩
    · exact native
    · exact False.elim (trace.no_unload openOnly bounded event)

theorem Trace.indexed_roots (trace : Trace program last) (openOnly : ¬ Nonempty (ClosedEpisode trace)) :
    PaperLifecycleClaims.RootInsertions (trace.toIndexed openOnly) :=
  fun _ bounded rule => trace.root_insertion bounded rule

theorem Trace.rule_ne_unload (trace : Trace program last) (openOnly : ¬ Nonempty (ClosedEpisode trace))
    {time : Nat} (bounded : time < last) : trace.rule time ≠ .unload := by
  intro unload
  cases event : trace.event time with
  | lifecycle kind actor =>
    cases kind
    case unload => exact trace.no_unload openOnly bounded event
    all_goals simp [Trace.rule, event, eventRule, Lifecycle.rule] at unload
  | command command => cases command <;> simp [Trace.rule, event, eventRule, ExchangeReplay.commandRule] at unload

private def UnloadingAt (state : R) (name : Name) : Prop :=
  ∃ row word view, state name = some row ∧ row.phase = .unloading word view

omit [DecidableEq Name] [DecidableEq Key] in
private theorem unloading_stable {before after : R} {name : Name}
    (frame : Ordering.ExistingPhases before after) (old : UnloadingAt before name) : UnloadingAt after name := by
  obtain ⟨row, word, view, found, phase⟩ := old
  obtain ⟨retained, present, same⟩ := frame name row found
  exact ⟨retained, word, view, present, same.trans phase⟩

private theorem unloading_mark {state : R} {name actor : Name} (phase : Phase Name Key Code I)
    (different : name ≠ actor) (old : UnloadingAt state name) : UnloadingAt (mark state actor phase) name := by
  obtain ⟨row, oldWord, view, found, oldPhase⟩ := old
  exact ⟨row, oldWord, view, (Transposition.mark_other _ _ _ _ different).trans found, oldPhase⟩

omit [DecidableEq Name] [DecidableEq Key] in
private theorem different_from_phase {before : R} {name actor : Name} {row : F}
    (present : before actor = some row) (old : UnloadingAt before name)
    (incompatible : ∀ word view, row.phase ≠ .unloading word view) : name ≠ actor := by
  intro same
  subst name
  obtain ⟨entry, word, view, found, phase⟩ := old
  have equal := Option.some.inj (present.symm.trans found)
  exact incompatible word view (equal ▸ phase)

private theorem unloading_persists {before after : R} {rule : Labeled.Rule} {actor name : Name}
    (step : Labeled.Step program rule actor before after) (kept : rule ≠ .unload)
    (old : UnloadingAt before name) : UnloadingAt after name := by
  cases step with
  | insert _ _ component parent enabled =>
    obtain ⟨row, word, view, found, phase⟩ := old
    have different : name ≠ actor := by
      intro same
      subst name
      rw [enabled.1] at found
      cases found
    exact ⟨row, word, view, (Transposition.put_other _ _ _ _ different).trans found, phase⟩
  | retire =>
    exact unloading_stable (Ordering.modify_existing_phases _ _ _ (fun _ => rfl)) old
  | remove _ _ enabled =>
    obtain ⟨row, word, view, found, phase⟩ := old
    have different : name ≠ actor := by
      intro same
      subst name
      simp [Removable, found, phase] at enabled
    exact ⟨row, word, view, (Transposition.erase_other _ _ _ different).trans found, phase⟩
  | begin _ _ row view found phase _ _ =>
    exact unloading_mark _ (different_from_phase found old (by simp [phase])) old
  | iter _ _ _ row _ _ _ _ _ found phase _ land
  | finish _ _ _ row _ _ _ _ found phase _ land =>
    exact unloading_mark _ (different_from_phase found old (by simp [phase]))
      (unloading_stable (Ordering.land_existing_phases program land) old)
  | divert _ _ _ row _ _ _ _ found phase _ branch =>
    have different := different_from_phase found old (by simp [phase])
    rcases branch with ⟨rfl, _⟩ | ⟨inverse, next, land, _⟩
    · exact unloading_mark _ different old
    · exact unloading_mark _ different (unloading_stable (Ordering.land_existing_phases program land) old)
  | leave _ _ row _ _ found phase _ =>
    exact unloading_mark _ (different_from_phase found old (by simp [phase])) old
  | unload => exact False.elim (kept rfl)

private theorem unloading_until_end (trace : Trace program last) (openOnly : ¬ Nonempty (ClosedEpisode trace))
    (quiet : Progress.Quiet (trace.state last)) {first : Nat} (bounded : first ≤ last) (name : Name) :
    ¬ UnloadingAt (trace.state first) name := by
  intro old
  have persisted (time : Nat) (lower : first ≤ time) (upper : time ≤ last) :
      UnloadingAt (trace.state time) name := by
    induction time with
    | zero => exact (show first = 0 by omega) ▸ old
    | succ time ih =>
      by_cases start : first = time + 1
      · exact start ▸ old
      have step := (trace.toIndexed openOnly).step time (by omega)
      exact unloading_persists step (trace.rule_ne_unload openOnly (by omega)) (ih (by omega) (by omega))
  obtain ⟨row, word, view, found, phase⟩ := persisted last bounded (Nat.le_refl _)
  have settled := quiet name row found
  simp [phase] at settled

/-- Quiet open-only histories have neither a closing unload nor a step
entering an unload. The remaining lifecycle phases are Begin, Iter, Finish. -/
theorem Trace.no_cleanup (trace : Trace program last) (openOnly : ¬ Nonempty (ClosedEpisode trace))
    (quiet : Progress.Quiet (trace.state last)) {time : Nat} (bounded : time < last) :
    trace.rule time ≠ .leave ∧ trace.rule time ≠ .divert ∧ trace.rule time ≠ .unload := by
  have noUnload := trace.rule_ne_unload openOnly bounded
  have step := (trace.toIndexed openOnly).step time bounded
  change Labeled.Step program (trace.rule time) (trace.actor time)
    (trace.state time) (trace.state (time + 1)) at step
  refine ⟨?_, ?_, noUnload⟩
  · intro isLeave
    rw [isLeave] at step
    generalize endpoint : trace.state (time + 1) = after at step
    cases step with
    | leave _ _ row word view found phase stale =>
      apply unloading_until_end trace openOnly quiet (by omega : time + 1 ≤ last) (trace.actor time)
      exact ⟨_, word, view, endpoint ▸ mark_self _ _ _ _ found, rfl⟩
  · intro isDivert
    rw [isDivert] at step
    generalize endpoint : trace.state (time + 1) = after at step
    cases step with
    | divert _ _ _ row code word view tail found phase stale branch =>
      have entered : UnloadingAt (trace.state (time + 1)) (trace.actor time) := by
        rcases branch with ⟨rfl, _⟩ | ⟨inverse, next, land, _⟩
        · exact ⟨_, tail ++ word, view, endpoint ▸ mark_self _ _ _ _ found, rfl⟩
        · obtain ⟨retained, present, _⟩ := Ordering.land_existing_phases program land (trace.actor time) row found
          exact ⟨_, tail ++ word, view, endpoint ▸ mark_self _ _ _ _ present, rfl⟩
      exact unloading_until_end trace openOnly quiet (by omega) (trace.actor time) entered

/-- The repaired support order applies directly to the remaining active
episodes, using native root provenance derived at each command cut. -/
theorem Trace.remaining_active_order (trace : Trace program last) (openOnly : ¬ Nonempty (ClosedEpisode trace))
    (quiet : Progress.Quiet (trace.state last)) (total : SupportAtQuiescence.TotalProvision (trace.state last)) :
    ∃ order, SupportLinearization.Linearization (SupportAtQuiescence.Active (trace.state last))
      (SupportUniqueness.ActivePredecessor (trace.state last)) order := by
  have run := Results.rootTrace (trace.toIndexed openOnly) (trace.indexed_roots openOnly) last (Nat.le_refl _)
  exact SupportLinearization.active_linearization program run quiet total

/-- Without closing episodes an installed view survives all later cuts. -/
theorem Trace.installed_through (trace : Trace program last) (openOnly : ¬ Nonempty (ClosedEpisode trace))
    (name : Name) {first time : Nat} (lower : first ≤ time) (upper : time ≤ last)
    (installed : ControlFrame.viewAt (trace.state first) name ≠ none) :
    ControlFrame.viewAt (trace.state time) name = ControlFrame.viewAt (trace.state first) name := by
  induction time with
  | zero =>
    have equal : first = 0 := by omega
    rw [equal]
  | succ time ih =>
    by_cases firstHere : first = time + 1
    · rw [firstHere]
    have prior := ih (by omega) (by omega)
    have kept : ControlFrame.viewAt (trace.state time) name ≠ none := fun missing => installed (prior ▸ missing)
    have bounded : time < last := by omega
    have native := (trace.toIndexed openOnly).step time bounded
    change Labeled.Step program (trace.rule time) (trace.actor time) (trace.state time) (trace.state (time + 1)) at native
    have noUnload := trace.rule_ne_unload openOnly bounded
    generalize selected : trace.rule time = rule at native noUnload
    have frame := ControlFrame.labeled_view_cases program native
    have next : ControlFrame.viewAt (trace.state (time + 1)) name = ControlFrame.viewAt (trace.state time) name := by
      cases rule
      case begin =>
        obtain ⟨row, view, found, phase, _, _, endpoint⟩ := frame
        have different : name ≠ trace.actor time := by
          intro same
          subst name
          exact kept (by simp [ControlFrame.viewAt, found, phase, Phase.committed])
        rw [endpoint, ControlFrame.mark_viewAt _ _ _ _ found, if_neg different]
      case unload => exact False.elim (noUnload rfl)
      all_goals exact congrFun frame name
    exact next.trans prior

/-- An installed row stays present with its declaration and birth
stamp for the remainder of an open history. -/
theorem Trace.installed_row_through (trace : Trace program last)
    (opened : ¬ Nonempty (ClosedEpisode trace))
    {cut time : Nat} (lower : cut ≤ time) (upper : time ≤ last) {name : Name} {row : F}
    (found : trace.state cut name = some row)
    (installed : ControlFrame.viewAt (trace.state cut) name ≠ none) :
    ∃ current, trace.state time name = some current ∧ current.component = row.component ∧
      (trace.notes time).1 name = (trace.notes cut).1 name ∧
        (row.retired = true → current.retired = true) := by
  induction time with
  | zero =>
    have same : cut = 0 := by omega
    subst cut
    exact ⟨row, found, rfl, rfl, id⟩
  | succ time ih =>
    by_cases same : cut = time + 1
    · subst cut
      exact ⟨row, found, rfl, rfl, id⟩
    obtain ⟨previous, present, component, stamp, retired⟩ := ih (by omega) (by omega)
    have retained := trace.installed_through opened name lower upper installed
    have still : ControlFrame.viewAt (trace.state (time + 1)) name ≠ none := fun absent =>
      installed (retained.symm.trans absent)
    cases next : trace.state (time + 1) name with
    | none => simp [ControlFrame.viewAt, next] at still
    | some current =>
      have stable := transition_stable (trace.step time (by omega)).1 name previous current present next
      have stampEq : (trace.notes (time + 1)).1 name = (trace.notes time).1 name := by
        rw [trace.notes_eq _ upper, trace.notes_eq time (by omega)]
        exact Incarnation.birth_stays trace.state name time (by simp [present]) (by simp [next])
      exact ⟨current, rfl, stable.1.symm.trans component, stampEq.trans stamp, stable.2.2 ∘ retired⟩

/-- In a quiet history with only open episodes, an installed row cannot
be retired. A command may still target an inactive row or a vacant name. -/
theorem Trace.command_actor_inactive (trace : Trace program last) (openOnly : ¬ Nonempty (ClosedEpisode trace))
    (quiet : Progress.Quiet (trace.state last)) {time : Nat} (bounded : time < last)
    {command : OrchestrationSorting.Command Name Key Code} (event : trace.event time = .command command) :
    ControlFrame.viewAt (trace.state time) command.actor = none := by
  have commandStep := (trace.step time bounded).1
  rw [event] at commandStep
  change command.Step (trace.state time) (trace.state (time + 1)) at commandStep
  cases command with
  | insert name component =>
    have vacant : trace.state time name = none := commandStep.1.1
    simp [OrchestrationSorting.Command.actor, ControlFrame.viewAt, vacant]
  | remove name =>
    have ready : Removable (trace.state time) name := commandStep.1
    cases found : trace.state time name with
    | none => simp [ControlFrame.viewAt, OrchestrationSorting.Command.actor, found]
    | some row =>
      rw [Removable, found] at ready
      simp [ControlFrame.viewAt, OrchestrationSorting.Command.actor, found, ready.2.1, Phase.committed]
  | retire name =>
    apply Classical.byContradiction
    intro installed
    change ControlFrame.viewAt (trace.state time) name ≠ none at installed
    have persistent (cut : Nat) (later : time ≤ cut) (inside : cut ≤ last) :
        ControlFrame.viewAt (trace.state cut) name ≠ none := by
      rw [trace.installed_through openOnly name later inside installed]
      exact installed
    obtain ⟨row, present, _⟩ := (ControlFrame.viewAt_present_iff _ _).mp installed
    have marked : (trace.state (time + 1) name).map Fiber.retired = some true := by
      rw [commandStep.2]
      simp [OrchestrationSorting.Command.apply, retire, Calculus.modify, present]
    have live : Incarnation.birthAt trace.state name time ≠ none :=
      fun missing => installed (by simp [ControlFrame.viewAt, Incarnation.birthAt_none.mp missing])
    cases tag : Incarnation.birthAt trace.state name time with
    | none => exact live tag
    | some birth =>
      have initial := Incarnation.resident_of_birthAt tag
      have lives : Incarnation.Residency trace.state name birth last := by
        refine ⟨by have := initial.ordered; omega, ?_, initial.boundary⟩
        intro cut born byEnd vacant
        by_cases earlier : cut ≤ time
        · exact initial.present cut born earlier vacant
        · exact persistent cut (by omega) byEnd (by simp [ControlFrame.viewAt, vacant])
      have finalRetired := EpisodeBoundary.retired_through_residency (last := last) trace.state
        (fun t bound => transition_stable (trace.step t bound).1) lives
        (by have := initial.ordered; omega) (by omega) (Nat.le_refl _) marked
      obtain ⟨lastRow, atEnd, active⟩ :=
        (ControlFrame.viewAt_present_iff _ _).mp (persistent last (by omega) (Nat.le_refl _))
      have flag : lastRow.retired = true := by simpa [atEnd] using finalRetired
      have stable := quiet name lastRow atEnd
      cases status : lastRow.phase with
      | inactive => exact active status
      | active => simp [status, Target, atEnd, flag] at stable
      | reloading | unloading => simp [status] at stable

/-- The complete native execution retains the actual event payloads of
the open-only source, and derives its roots from the very same cuts. -/
theorem Trace.native_segment (trace : Trace program last) (openOnly : ¬ Nonempty (ClosedEpisode trace))
    (start length : Nat) (bounded : start + length ≤ last) :
    let cuts := List.range' start length
    RootExec program (cuts.map trace.event) (trace.state start) (trace.state (start + length))
      (cuts.flatMap fun time => eventRoots (trace.state time) (trace.event time)) := by
  dsimp only
  induction length generalizing start with
  | zero => exact .nil _
  | succ length ih =>
    have bound : start < last := by omega
    have actual : (trace.event start).Step program (trace.state start) (trace.state (start + 1)) := by
      have step := (trace.step start bound).1
      cases event : trace.event start with
      | command command =>
        rw [event] at step
        exact step
      | lifecycle kind name =>
        rw [event] at step
        cases kind
        case unload => exact False.elim (trace.no_unload openOnly bound event)
        all_goals exact step
    have same : start + 1 + length = start + (length + 1) := by omega
    rw [List.range'_succ, List.map_cons, List.flatMap_cons, ← same]
    exact .cons actual (ih (start + 1) (by omega))

theorem activation_installs_view {before after : R} {rule : Labeled.Rule} {actor : Name}
    (step : Labeled.Step program rule actor before after) (activation : Transposition.Activation rule) :
    ControlFrame.viewAt after actor ≠ none := by
  cases step with
  | begin _ _ row view present _ _ _ =>
    simp [ControlFrame.mark_viewAt _ _ _ _ present, Phase.committed]
  | iter _ _ _ row _ _ _ _ _ present phase _ land
  | finish _ _ _ row _ _ _ _ present phase _ land =>
    obtain ⟨entry, found, _⟩ := Ordering.land_existing_phases program land actor row present
    simp [ControlFrame.mark_viewAt _ _ _ _ found, Phase.committed]
  | _ => simp [Transposition.Activation] at activation

theorem Trace.activation_at (trace : Trace program last)
    (openOnly : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    {time : Nat} (bounded : time < last) {kind : Lifecycle} {actor : Name}
    (event : trace.event time = .lifecycle kind actor) :
    Transposition.Activation kind.rule ∧
      Labeled.Step program kind.rule actor (trace.state time) (trace.state (time + 1)) := by
  have label : trace.rule time = kind.rule := by simp [Trace.rule, event, eventRule]
  have owner : trace.actor time = actor := by simp [Trace.actor, event, Vestigial.eventActor]
  constructor
  · have ordinary := trace.no_cleanup openOnly quiet bounded
    rw [label] at ordinary
    cases kind <;> simp [Lifecycle.rule, Transposition.Activation] at ordinary ⊢
  · have executed := (trace.toIndexed openOnly).step time bounded
    change Labeled.Step program (trace.rule time) (trace.actor time) (trace.state time) (trace.state (time + 1)) at executed
    rwa [label, owner] at executed

/-- A lifecycle activation keeps the acting incarnation's birth stamp
through every later cut of a quiet open history. -/
theorem Trace.activation_stamp_through (trace : Trace program last)
    (opened : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    {cut time : Nat} (bounded : cut < last) (lower : cut ≤ time) (upper : time ≤ last)
    {kind : Lifecycle} {actor : Name} (event : trace.event cut = .lifecycle kind actor) :
    (trace.notes cut).1 actor = (trace.notes time).1 actor := by
  by_cases same : cut = time
  · rw [same]
  obtain ⟨activation, step⟩ := trace.activation_at opened quiet bounded event
  obtain ⟨row, _, found, _, _⟩ := Transposition.activation_source program step activation
  have installed := activation_installs_view step activation
  cases next : trace.state (cut + 1) actor with
  | none => simp [ControlFrame.viewAt, next] at installed
  | some current =>
    obtain ⟨_, _, _, retained, _⟩ := trace.installed_row_through opened (by omega) upper next installed
    have immediate : (trace.notes (cut + 1)).1 actor = (trace.notes cut).1 actor := by
      rw [trace.notes_eq _ (Nat.succ_le_of_lt bounded), trace.notes_eq cut (Nat.le_of_lt bounded)]
      exact Incarnation.birth_stays trace.state actor cut (by simp [found]) (by simp [next])
    exact (retained.trans immediate).symm

/-- Each installed view in the open history has an actual opening event. -/
theorem Trace.begin_of_installed (trace : Trace program last) {time : Nat} (bounded : time ≤ last)
    {actor : Name} (installed : ControlFrame.viewAt (trace.state time) actor ≠ none) :
    ∃ cut, cut < time ∧ trace.event cut = .lifecycle .begin actor := by
  have absent : ControlFrame.viewAt (trace.state 0) actor = none := by simp [trace.start, ControlFrame.viewAt]
  obtain ⟨opened, positive, interval⟩ :=
    prefix_since_absence (last := last) trace.state actor (Nat.zero_le _) bounded absent installed
  have order := interval.ordered
  have next : opened - 1 + 1 = opened := by omega
  have begins := begin_at_view_change trace (time := opened - 1) (by omega) interval.before
    (next ▸ interval.installed opened (Nat.le_refl _) order)
  exact ⟨opened - 1, by omega, begins.1⟩

theorem Trace.opening_of_activation (trace : Trace program last)
    (openOnly : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    {time : Nat} (bounded : time < last) {kind : Lifecycle} {actor : Name}
    (event : trace.event time = .lifecycle kind actor) :
    ∃ cut, cut ≤ time ∧ trace.event cut = .lifecycle .begin actor := by
  obtain ⟨active, step⟩ := trace.activation_at openOnly quiet bounded event
  obtain ⟨cut, before, opening⟩ := trace.begin_of_installed (by omega) (activation_installs_view step active)
  exact ⟨cut, by omega, opening⟩

theorem Trace.begin_unique (trace : Trace program last) (openOnly : ¬ Nonempty (ClosedEpisode trace))
    {first second : Nat} (firstBound : first < last) (secondBound : second < last) {actor : Name}
    (firstEvent : trace.event first = .lifecycle .begin actor)
    (secondEvent : trace.event second = .lifecycle .begin actor) : first = second := by
  have earlier_impossible {left right : Nat} (leftBound : left < last) (rightBound : right < last)
      (leftEvent : trace.event left = .lifecycle .begin actor)
      (rightEvent : trace.event right = .lifecycle .begin actor) (earlier : left < right) : False := by
    have leftStep := (trace.step left leftBound).1
    have rightStep := (trace.step right rightBound).1
    rw [leftEvent] at leftStep
    rw [rightEvent] at rightStep
    have installed := activation_installs_view
      (show Labeled.Step program .begin actor (trace.state left) (trace.state (left + 1)) from leftStep) (Or.inl rfl)
    have rightBegin := ControlFrame.labeled_view_cases program
      (show Labeled.Step program .begin actor (trace.state right) (trace.state (right + 1)) from rightStep)
    obtain ⟨row, _, found, inactive, _, _, _⟩ := rightBegin
    have absent : ControlFrame.viewAt (trace.state right) actor = none := by
      simp [ControlFrame.viewAt, found, inactive, Phase.committed]
    exact installed ((trace.installed_through openOnly actor earlier (by omega) installed).symm.trans absent)
  rcases Nat.lt_trichotomy first second with earlier | same | later
  · exact False.elim (earlier_impossible firstBound secondBound firstEvent secondEvent earlier)
  · exact same
  · exact False.elim (earlier_impossible secondBound firstBound secondEvent firstEvent later)

/-- Earlier applicability of a later Begin is determined by the row already
being present and its actual selected providers being available before the
foreign activation. A different total view on unused keys changes neither guard. -/
theorem Trace.earlier_begin_target_iff (trace : Trace program last)
    (openOnly : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    {time : Nat} (bounded : time < last) {kind : Lifecycle} {actor other : Name}
    (event : trace.event time = .lifecycle kind actor) (different : other ≠ actor)
    {row : F} {view : View Name Key} (found : trace.state (time + 1) other = some row)
    (target : Target (trace.state (time + 1)) other view) :
    (∃ selected, Target (trace.state time) other selected) ↔
      trace.state time other ≠ none ∧ ∀ key, row.component.requires key = true → view key ≠ actor := by
  obtain ⟨active, step⟩ := trace.activation_at openOnly quiet bounded event
  have reached := (trace.toIndexed openOnly).prefixRun time (by omega)
  have owned := Transposition.reachable_owned program reached
  have disjoint := (WellFormed.run_invariants program reached Safety.empty_parentClosed WellFormed.disjoint_empty
    ⟨Ordering.supported_empty, Ordering.local_empty⟩).2.1
  have guard := Transposition.selected_target_before_activation_iff program step active different found target
  exact ⟨fun earlier => guard.mp (Transposition.earlier_target_for_selected_view program step active owned disjoint
    other row view different found target earlier), fun ready => ⟨view, guard.mpr ready⟩⟩

/-- A foreign activation that first enables an existing consumer's
selected view must finish a provider selected at a required key. -/
theorem Trace.finish_enables_selected_target (trace : Trace program last)
    (opened : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    {cut : Nat} (bounded : cut < last) {kind : Lifecycle} {actor consumer : Name}
    (activation : trace.event cut = .lifecycle kind actor) (different : consumer ≠ actor)
    (present : trace.state cut consumer ≠ none)
    {row : F} {view : View Name Key} (found : trace.state (cut + 1) consumer = some row)
    (before : ¬ Target (trace.state cut) consumer view)
    (after : Target (trace.state (cut + 1)) consumer view) :
    kind = .finish ∧ ∃ key, row.component.requires key = true ∧ view key = actor := by
  obtain ⟨active, step⟩ := trace.activation_at opened quiet bounded activation
  have selected : ∃ key, row.component.requires key = true ∧ view key = actor := by
    apply Classical.byContradiction
    intro none
    apply before
    exact (Transposition.selected_target_before_activation_iff program step active different found after).mpr
      ⟨present, fun key required equal => none ⟨key, required, equal⟩⟩
  obtain ⟨key, required, equal⟩ := selected
  simp only [Target, found] at after
  have supplied := after.2 key required
  rw [equal] at supplied
  refine ⟨?_, key, required, equal⟩
  generalize afterCut : trace.state (cut + 1) = result at step supplied
  cases kind with
  | begin =>
    cases step with
    | begin _ _ provider selected found _ _ _ =>
      rw [mark_self _ _ _ _ found] at supplied
      exact False.elim supplied.1
  | iter =>
    cases step with
    | iter _ _ _ provider _ _ _ _ _ found _ _ land =>
      obtain ⟨retained, present, _⟩ := Ordering.land_existing_phases program land actor provider found
      rw [mark_self _ _ _ _ present] at supplied
      exact False.elim supplied.1
  | finish => rfl
  | divert | leave | unload => simp [Transposition.Activation, Lifecycle.rule] at active

/-- In a command-free block of foreign activations, a consumer already
present at the first cut can gain its selected target only at a Finish
of a required provider. -/
theorem Trace.selected_target_requires_provider_finish (trace : Trace program last)
    (opened : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    {start span : Nat} (bounded : start + span ≤ last) {consumer : Name} {view : View Name Key}
    (present : trace.state start consumer ≠ none)
    (before : ¬ Target (trace.state start) consumer view)
    (after : Target (trace.state (start + span)) consumer view)
    (block : ∀ i, start ≤ i → i < start + span →
      ∃ kind actor, trace.event i = .lifecycle kind actor ∧ consumer ≠ actor) :
    ∃ cut row key, start ≤ cut ∧ cut < start + span ∧
      trace.event cut = .lifecycle .finish (view key) ∧
      trace.state (cut + 1) consumer = some row ∧ row.component.requires key = true ∧
      ¬ Target (trace.state cut) consumer view ∧ Target (trace.state (cut + 1)) consumer view := by
  have kept (i : Nat) (atMost : i ≤ span) : trace.state (start + i) consumer ≠ none := by
    induction i with
    | zero => exact present
    | succ i ih =>
      obtain ⟨kind, actor, event, different⟩ := block (start + i) (by omega) (by omega)
      obtain ⟨active, step⟩ := trace.activation_at opened quiet (by omega) event
      have prior := ih (by omega)
      cases found : trace.state (start + i) consumer with
      | none => exact False.elim (prior found)
      | some row =>
        obtain ⟨_, saved⟩ := Transposition.activation_other_table program step active consumer row different found
        intro absent
        change trace.state (start + i + 1) consumer = none at absent
        rw [absent] at saved
        cases saved
  induction span with
  | zero => exact False.elim (before after)
  | succ span ih =>
    by_cases ready : Target (trace.state (start + span)) consumer view
    · obtain ⟨cut, row, key, lower, upper, event, found, required, before, after⟩ :=
        ih (by omega) ready (fun i lo hi => block i lo (by omega)) (fun i hi => kept i (by omega))
      exact ⟨cut, row, key, lower, by omega, event, found, required, before, after⟩
    · obtain ⟨kind, actor, event, different⟩ := block (start + span) (by omega) (by omega)
      have afterStep : Target (trace.state (start + span + 1)) consumer view := after
      cases found : trace.state (start + span + 1) consumer with
      | none => simp [Target, found] at afterStep
      | some row =>
        obtain ⟨rfl, key, required, rfl⟩ := trace.finish_enables_selected_target opened quiet (by omega)
          event different (kept span (by omega)) found ready afterStep
        exact ⟨start + span, row, key, by omega, by omega, event, found, required, ready, afterStep⟩

/-- An active row in a quiet open history remains active with the same
declaration, birth stamp, and binding domain at every later cut. -/
theorem Trace.active_row_survives (trace : Trace program last)
    (opened : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    {first final : Nat} (ordered : first ≤ final) (bounded : final ≤ last)
    {name : Name} {row : F} (found : trace.state first name = some row) (active : row.phase.available) :
    ∃ later, trace.state final name = some later ∧ later.phase = row.phase ∧ later.component = row.component ∧
      (trace.notes final).1 name = (trace.notes first).1 name ∧
      ∀ key, later.table key = none ↔ row.table key = none := by
  induction final with
  | zero =>
    obtain rfl : first = 0 := by omega
    exact ⟨row, found, rfl, rfl, rfl, fun _ => Iff.rfl⟩
  | succ time ih =>
    by_cases same : first = time + 1
    · subst first
      exact ⟨row, found, rfl, rfl, rfl, fun _ => Iff.rfl⟩
    obtain ⟨previous, present, phase, component, tag, domain⟩ := ih (by omega) (by omega)
    have available : previous.phase.available := phase.symm ▸ active
    have installed : ControlFrame.viewAt (trace.state time) name ≠ none := by
      cases status : previous.phase <;> simp [ControlFrame.viewAt, present, status, Phase.committed, Phase.available] at available ⊢
    have current : ∃ later, trace.state (time + 1) name = some later ∧ later.phase = previous.phase ∧
        later.component = previous.component ∧ ∀ key, later.table key = none ↔ previous.table key = none := by
      cases event : trace.event time with
      | command cmd =>
        have distinct : name ≠ cmd.actor := fun equal => installed
          (equal ▸ trace.command_actor_inactive opened quiet (by omega) event)
        have step := (trace.step time (by omega)).1
        rw [event] at step
        have same := step.2
        refine ⟨previous, ?_, rfl, rfl, fun _ => Iff.rfl⟩
        rw [same]
        cases cmd <;> simp only [OrchestrationSorting.Command.actor] at distinct <;>
          simpa [OrchestrationSorting.Command.apply, put, erase, retire, Calculus.modify, distinct] using present
      | lifecycle kind actor =>
        obtain ⟨activation, step⟩ := trace.activation_at opened quiet (by omega) event
        have different : name ≠ actor := by
          rintro rfl
          obtain ⟨other, _, otherAt, unavailable, _⟩ := Transposition.activation_source program step activation
          obtain rfl : other = previous := Option.some.inj (otherAt.symm.trans present)
          exact unavailable available
        obtain ⟨table, kept, domains⟩ :=
          Transposition.activation_other_table_domains program step activation name previous different present
        exact ⟨_, kept, rfl, rfl, domains⟩
    obtain ⟨later, laterAt, samePhase, sameComponent, sameDomain⟩ := current
    have sameTag : (trace.notes (time + 1)).1 name = (trace.notes time).1 name := by
      rw [trace.notes_eq (time + 1) bounded, trace.notes_eq time (by omega)]
      exact Incarnation.birth_stays trace.state name time (by simp [present]) (by simp [laterAt])
    exact ⟨later, laterAt, samePhase.trans phase, sameComponent.trans component, sameTag.trans tag,
      fun key => (sameDomain key).trans (domain key)⟩

/-- An active row at an actual cut has a prior Finish of that same
incarnation. Its address can therefore be recovered from an event. -/
theorem Trace.active_row_has_finish (trace : Trace program last)
    (opened : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    {time : Nat} (bounded : time ≤ last) {name : Name} {row : F}
    (found : trace.state time name = some row) (active : row.phase.available) :
    ∃ cut, cut < time ∧ trace.event cut = .lifecycle .finish name ∧
      (trace.notes cut).1 name = (trace.notes time).1 name := by
  induction time generalizing row with
  | zero =>
    rw [trace.start] at found
    cases found
  | succ time ih =>
    have valid : time < last := by omega
    have older (previous : F) (present : trace.state time name = some previous)
        (available : previous.phase.available) :
        ∃ cut, cut < time + 1 ∧ trace.event cut = .lifecycle .finish name ∧
          (trace.notes cut).1 name = (trace.notes (time + 1)).1 name := by
      obtain ⟨cut, earlier, event, tag⟩ := ih (by omega) present available
      have same : (trace.notes (time + 1)).1 name = (trace.notes time).1 name := by
        rw [trace.notes_eq _ bounded, trace.notes_eq time (by omega)]
        exact Incarnation.birth_stays trace.state name time (by simp [present]) (by simp [found])
      exact ⟨cut, by omega, event, tag.trans same.symm⟩
    cases event : trace.event time with
    | command cmd =>
      have step := (trace.step time valid).1
      rw [event] at step
      have endpoint := step.2
      by_cases equal : name = cmd.actor
      · cases cmd with
        | insert target component =>
          change name = target at equal
          rw [endpoint] at found
          simp [OrchestrationSorting.Command.apply, put, equal] at found
          subst row
          exact False.elim active
        | remove target =>
          change name = target at equal
          rw [endpoint] at found
          simp [OrchestrationSorting.Command.apply, erase, equal] at found
        | retire target =>
          change name = target at equal
          subst target
          cases present : trace.state time name with
          | none => simp [endpoint, OrchestrationSorting.Command.apply, retire, Calculus.modify, present] at found
          | some previous =>
            have kept : previous.phase = row.phase := by
              simp [endpoint, OrchestrationSorting.Command.apply, retire, Calculus.modify, present] at found
              have phases := congrArg Fiber.phase found
              exact phases
            exact older previous present (kept.symm ▸ active)
      · have prior : trace.state time name = some row := by
          rw [endpoint] at found
          cases cmd <;> simp only [OrchestrationSorting.Command.actor] at equal <;>
            simpa [OrchestrationSorting.Command.apply, put, erase, retire, Calculus.modify, equal] using found
        exact older row prior active
    | lifecycle kind actor =>
      obtain ⟨activation, step⟩ := trace.activation_at opened quiet valid event
      by_cases same : name = actor
      · subst actor
        generalize state : trace.state (time + 1) = endpoint at step found
        cases kind with
        | begin =>
          cases step with
          | begin _ _ prev view present _ _ _ =>
            rw [mark_self _ _ _ (.reloading prev.component.entry [] view) present] at found
            cases found
            exact False.elim active
        | iter =>
          cases step with
          | iter _ _ _ prev _ word view token next present _ _ land =>
            obtain ⟨retained, kept, _⟩ := Ordering.land_existing_phases program land name prev present
            rw [mark_self _ _ _ (.reloading next (token :: word) view) kept] at found
            cases found
            exact False.elim active
        | finish =>
          cases step with
          | finish _ _ _ prev _ _ _ _ present _ _ _ =>
            have sameTag : (trace.notes (time + 1)).1 name = (trace.notes time).1 name := by
              rw [trace.notes_eq _ bounded, trace.notes_eq time (by omega)]
              exact Incarnation.birth_stays trace.state name time (by simp [present]) (by rw [state, found]; simp)
            exact ⟨time, by omega, event, sameTag.symm⟩
        | divert | leave | unload => simp [Transposition.Activation, Lifecycle.rule] at activation
      · cases present : trace.state time name with
        | none =>
          have created := (Transposition.activation_creates_iff program step activation name (Ne.symm same)).mpr
            ⟨present, by simp [found]⟩
          obtain ⟨component, made⟩ := EpisodeBoundary.born_row present created
          have equal := Option.some.inj (found.symm.trans made)
          subst row
          exact False.elim active
        | some previous =>
          obtain ⟨table, kept⟩ := Transposition.activation_other_table program step activation name previous same present
          have equal := Option.some.inj (found.symm.trans kept)
          subst row
          exact older previous present active

/-- A Finish witnesses an active row at every later cut, with its
original birth stamp. -/
theorem Trace.finished_row_at_cut (trace : Trace program last)
    (opened : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    {cut final : Nat} (earlier : cut < final) (bounded : final ≤ last)
    {name : Name} (event : trace.event cut = .lifecycle .finish name) :
    ∃ row, trace.state final name = some row ∧ row.phase.available ∧
      (trace.notes final).1 name = (trace.notes cut).1 name := by
  have step := (trace.step cut (by omega)).1
  rw [event] at step
  change Labeled.Step program .finish name (trace.state cut) (trace.state (cut + 1)) at step
  generalize endStep : trace.state (cut + 1) = after at step
  cases step with
  | finish _ _ _ previous _ word view token present _ _ land =>
    obtain ⟨retained, retainedAt, _⟩ := Ordering.land_existing_phases program land name previous present
    have finished := endStep.symm ▸ mark_self _ _ _ (.active (token :: word) view) retainedAt
    obtain ⟨row, found, phase, _, stamp, _⟩ :=
      trace.active_row_survives opened quiet (by omega : cut + 1 ≤ final) bounded finished trivial
    have stepStamp : (trace.notes (cut + 1)).1 name = (trace.notes cut).1 name := by
      rw [trace.notes_eq _ (by omega), trace.notes_eq cut (by omega)]
      exact Incarnation.birth_stays trace.state name cut (by simp [present]) (by simp [finished])
    exact ⟨row, found, phase.symm ▸ trivial, stamp.trans stepStamp⟩

/-- A live installed view in a quiet open history still gives a valid target.
The real prefix gives the retained provider and its binding. With no
unloading provider, retained supply is active supply. -/
theorem Trace.committed_target (trace : Trace program last)
    (openOnly : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    {time : Nat} (bounded : time ≤ last) {actor : Name} {row : F} {view : View Name Key}
    (present : trace.state time actor = some row) (live : row.retired = false)
    (installed : row.phase.committed = some view) : Target (trace.state time) actor view := by
  have supported := trace.supported time bounded
  simp only [Target, present]
  refine ⟨live, ?_⟩
  intro key required
  have demand : Ordering.Demand (trace.state time) actor (view key) key := ⟨row, view, present, required, installed, rfl⟩
  obtain ⟨_, provider, found, retained, bound⟩ := supported actor (view key) key demand
  rw [found]
  refine ⟨?_, bound⟩
  cases phase : provider.phase with
  | inactive | reloading => simp [phase, Ordering.Retained] at retained
  | active => trivial
  | unloading word selected =>
    exact False.elim (unloading_until_end trace openOnly quiet bounded (view key)
      ⟨provider, word, selected, found, phase⟩)

/-- Every installed view of a quiet open history is already a valid
target. Retirement would persist and contradict endpoint quiescence. -/
theorem Trace.installed_has_target (trace : Trace program last)
    (opened : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    {cut : Nat} (bounded : cut ≤ last) {actor : Name}
    (installed : ControlFrame.viewAt (trace.state cut) actor ≠ none) :
    ∃ view, Target (trace.state cut) actor view := by
  obtain ⟨row, found, hasView⟩ := (ControlFrame.viewAt_present_iff _ _).mp installed
  cases viewAt : row.phase.committed with
  | none => exact False.elim (installed (by simp [ControlFrame.viewAt, found, viewAt]))
  | some view =>
    obtain ⟨later, present, _, _, retired⟩ :=
      trace.installed_row_through opened bounded (Nat.le_refl _) found installed
    have kept : ControlFrame.viewAt (trace.state last) actor ≠ none := by
      rw [trace.installed_through opened actor bounded (Nat.le_refl _) installed]
      exact installed
    have terminal := quiet actor later present
    have live : row.retired = false := by
      cases flag : row.retired
      · rfl
      · have marked := retired flag
        cases phase : later.phase <;> simp [ControlFrame.viewAt, present, phase, Phase.committed,
          Target, marked] at kept terminal
    exact ⟨view, trace.committed_target opened quiet bounded found live viewAt⟩

private theorem Trace.landing_source_before (trace : Trace program last)
    (openOnly : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    {time : Nat} (bounded : time < last) {rule : Labeled.Rule} {actor other : Name}
    (step : Labeled.Step program rule actor (trace.state time) (trace.state (time + 1)))
    (active : Transposition.Activation rule) (different : actor ≠ other)
    {current : F} (found : trace.state (time + 1) other = some current)
    {code : Code} {word : List I} {view : View Name Key} (phase : current.phase = .reloading code word view)
    (target : Target (trace.state (time + 1)) other view) :
    ∃ original : F, trace.state time other = some original ∧
      original.phase = .reloading code word view ∧ Target (trace.state time) other view := by
  cases present : trace.state time other with
  | none =>
    have created := (Transposition.activation_creates_iff program step active other different).mpr
      ⟨present, by simp [found]⟩
    obtain ⟨_, component, landed, _, _, endpoint⟩ := created
    have birth : trace.state (time + 1) other = some (fresh component (some actor)) := by
      rw [endpoint, Transposition.mark_other _ _ _ _ (Ne.symm different), put_self]
    have same := Option.some.inj (birth.symm.trans found)
    subst current
    simp [fresh] at phase
  | some original =>
    obtain ⟨table, after⟩ := Transposition.activation_other_table program step active other original
      (Ne.symm different) present
    have same := Option.some.inj (after.symm.trans found)
    have stored : original.phase = .reloading code word view := (congrArg Fiber.phase same).trans phase
    have laterLive : current.retired = false := by
      simp only [Target, found] at target
      exact target.1
    have earlierLive : original.retired = false := (congrArg Fiber.retired same).trans laterLive
    exact ⟨original, rfl, stored, trace.committed_target openOnly quiet (by omega) present earlierLive
      (by simp [stored, Phase.committed])⟩

/-- Different actors' adjacent activations can exchange when a later Begin
already has a valid target. For a later Iter or Finish the earlier phase and
target come from the actual prefix, including the committed providers. -/
theorem Trace.exchange_activations (trace : Trace program last)
    (openOnly : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    {time : Nat} (bounded : time + 1 < last) {firstKind secondKind : Lifecycle} {first second : Name}
    (firstEvent : trace.event time = .lifecycle firstKind first)
    (secondEvent : trace.event (time + 1) = .lifecycle secondKind second) (different : first ≠ second)
    (beginTarget : secondKind = .begin → ∃ view, Target (trace.state time) second view)
    [Setoid Value] (callbacks : ∀ code, Transposition.CallbackWitness program code)
    (independent : Transposition.CurrentCallbackPair program (trace.state time) first second) :
    ∃ middle final,
      Labeled.Step program secondKind.rule second (trace.state time) middle ∧
      Labeled.Step program firstKind.rule first middle final ∧
      StageSimulation.Related Eq final (trace.state (time + 2)) := by
  obtain ⟨firstActive, firstStep⟩ := trace.activation_at openOnly quiet (by omega) firstEvent
  obtain ⟨secondActive, secondStep⟩ := trace.activation_at openOnly quiet bounded secondEvent
  have reached := (trace.toIndexed openOnly).prefixRun time (by omega)
  apply Transposition.activation_diamond_of_sources program firstStep firstActive secondStep secondActive _ _
    different reached callbacks independent
  · intro isBegin
    have kindBegin : secondKind = .begin := by
      cases secondKind <;> simp [Lifecycle.rule] at isBegin ⊢
    obtain ⟨view, target⟩ := beginTarget kindBegin
    have later := ControlFrame.labeled_view_cases program (isBegin ▸ secondStep)
    obtain ⟨current, _, found, inactive, _, _, _⟩ := later
    cases present : trace.state time second with
    | none => simp [Target, present] at target
    | some original =>
      obtain ⟨table, after⟩ := Transposition.activation_other_table program firstStep firstActive second original
        (Ne.symm different) present
      have same := Option.some.inj (after.symm.trans found)
      have unchanged : original.phase = .inactive := (congrArg Fiber.phase same).trans inactive
      exact ⟨_, .begin _ _ original view present unchanged (by simp [present]) target⟩
  · intro _ current code word view found phase target
    exact trace.landing_source_before openOnly quiet (by omega) firstStep firstActive different found phase target

/-- A subsequent command can cross a foreign activation when that
activation did not create its target. The trace supplies actor separation. -/
theorem Trace.exchange_command_after_activation (trace : Trace program last)
    (openOnly : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    {time : Nat} (bounded : time + 1 < last) {kind : Lifecycle} {actor : Name}
    (activationEvent : trace.event time = .lifecycle kind actor)
    (command : OrchestrationSorting.Command Name Key Code)
    (commandEvent : trace.event (time + 1) = .command command)
    (notCreated : trace.state time command.actor = none → trace.state (time + 1) command.actor = none) :
    ∃ moved, ExchangeReplay.Exchange (trace.toIndexed openOnly) moved time command := by
  have owner : trace.actor time = actor := by simp [Trace.actor, activationEvent, Vestigial.eventActor]
  obtain ⟨activation, executed⟩ := trace.activation_at openOnly quiet (by omega) activationEvent
  have installed := activation_installs_view executed activation
  have commandInactive := trace.command_actor_inactive openOnly quiet bounded commandEvent
  have different : actor ≠ command.actor := fun same => installed (same.symm ▸ commandInactive)
  have late := (trace.step (time + 1) bounded).1
  rw [commandEvent] at late
  change command.Step (trace.state (time + 1)) (trace.state (time + 2)) at late
  apply ExchangeReplay.activation_command (trace.toIndexed openOnly) bounded command
  · change Transposition.Activation (trace.rule time)
    simpa [Trace.rule, activationEvent, eventRule] using activation
  · exact ⟨by simp [Trace.toIndexed, Trace.rule, commandEvent, eventRule],
      by simp [Trace.toIndexed, Trace.actor, commandEvent, Vestigial.eventActor]⟩
  · exact late
  · change trace.actor time ≠ command.actor
    rwa [owner]
  · exact notCreated

/-- A root command immediately after an activation can cross it. The
actual source proves both the distinct actor and the absence of a birth
dependency. The exchange carries command provenance and capture indices. -/
theorem Trace.exchange_root_after_activation (trace : Trace program last)
    (openOnly : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    {time : Nat} (bounded : time + 1 < last) {kind : Lifecycle} {actor : Name}
    (activationEvent : trace.event time = .lifecycle kind actor)
    (command : OrchestrationSorting.Command Name Key Code)
    (commandEvent : trace.event (time + 1) = .command command)
    (root : commandRoots (trace.state (time + 1)) command ≠ []) :
    ∃ moved, ExchangeReplay.Exchange (trace.toIndexed openOnly) moved time command := by
  obtain ⟨_, executed⟩ := trace.activation_at openOnly quiet (by omega) activationEvent
  have late := (trace.step (time + 1) bounded).1
  rw [commandEvent] at late
  change command.Step (trace.state (time + 1)) (trace.state (time + 2)) at late
  have alreadyRoot (isRoot : rootAt (trace.state (time + 1)) command.actor = true)
      (absent : trace.state time command.actor = none) : False := by
    rw [rootAt_lifecycle kind executed, rootAt, absent] at isRoot
    cases isRoot
  have notCreated (absent : trace.state time command.actor = none) :
      trace.state (time + 1) command.actor = none := by
    cases command with
    | insert => exact late.1.1
    | retire target | remove target =>
      apply False.elim
      apply alreadyRoot _ absent
      by_cases classified : rootAt (trace.state (time + 1)) target = true
      · exact classified
      · simp [commandRoots, classified] at root
  exact trace.exchange_command_after_activation openOnly quiet bounded activationEvent command commandEvent notCreated

end Cordis.Repairs.GuardedHistory
