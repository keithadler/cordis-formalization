import Cordis.Repairs.GuardedSuffix

/-! Empty-origin source histories using guarded unload at every cut.
Recorded births and captures are computed from the actual transitions.
The same replay summaries serve the native and the guarded calculus. -/
namespace Cordis.Repairs.GuardedHistory
open Calculus Stages LegalHistory Incarnation IncarnationReplay
open Vestigial (CutNotes cutNotes eventActor noteStep)
open PartialReplayRegistry (saved ReplayEvent Coeffects SlotHistory)
universe u
variable {Name Key Value Code Error : Type u} [DecidableEq Name] [DecidableEq Key]
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
local notation "I" => Inverse Name Key Value
local notation "C" => Capture Name Key Value
local notation "Notes" => CutNotes Name Key Value
local notation "Ev" => Event Name Key Code
local notation "Program" => Code → Instruction Name Key Value Code Error

def eventRule : Ev → Labeled.Rule
  | .lifecycle kind _ => kind.rule
  | .command command => ExchangeReplay.commandRule command

structure Trace (program : Program) (last : Nat) where
  state : Nat → R
  notes : Nat → Notes
  event : Nat → Ev
  start : state 0 = (fun _ => none)
  seed : notes 0 = (fun _ => none, fun _ => [])
  step : ∀ time, time < last →
    GuardedSuffix.Step program (event time) (time + 1) (state time) (notes time) (state (time + 1)) (notes (time + 1))

variable {program : Code → Stages.Instruction Name Key Value Code Error} {last : Nat}

def Trace.actor (trace : Trace program last) (time : Nat) : Name := eventActor (trace.event time)

def Trace.rule (trace : Trace program last) (time : Nat) : Labeled.Rule := eventRule (trace.event time)

/-- Keep a trace's actual prefix through a cut and append the supplied
legal event with its recorded next annotations. -/
def Trace.extendAt (trace : Trace program last) {time : Nat} (bounded : time ≤ last)
    {event : Ev} {after : R} {recorded : Notes}
    (newStep : GuardedSuffix.Step program event (time + 1)
      (trace.state time) (trace.notes time) after recorded) : Trace program (time + 1) where
  state cut := if cut ≤ time then trace.state cut else after
  notes cut := if cut ≤ time then trace.notes cut else recorded
  event cut := if cut < time then trace.event cut else event
  start := by simpa only [Nat.zero_le, if_true] using trace.start
  seed := by simpa only [Nat.zero_le, if_true] using trace.seed
  step cut valid := by
    by_cases earlier : cut < time
    · simpa only [if_pos earlier, if_pos (show cut ≤ time by omega), if_pos (show cut + 1 ≤ time by omega)]
        using trace.step cut (by omega)
    · have same : cut = time := by omega
      subst cut
      simpa only [if_neg (Nat.lt_irrefl _), if_pos (Nat.le_refl _), if_neg (show ¬ time + 1 ≤ time by omega)]
        using newStep

def originalRoots (trace : Trace program last) : List (OrchestrationSorting.Command Name Key Code) :=
  (List.range last).flatMap fun time => eventRoots (trace.state time) (trace.event time)

theorem cut_range_pair {time last : Nat} (bounded : time + 1 < last) :
    List.range last = List.range time ++ time :: (time + 1) ::
      List.range' (time + 2) (last - (time + 2)) := by
  have initial : List.range last = List.range time ++ List.range' time (last - time) := by
    simpa only [List.range_eq_range', Nat.zero_add, show time + (last - time) = last by omega] using
      (List.range'_append_1 (s := 0) (m := time) (n := last - time)).symm
  rw [initial, show last - time = (last - (time + 2)) + 1 + 1 by omega, List.range'_succ, List.range'_succ]

theorem lifecycle_transition {kind : Lifecycle} {actor : Name} {before after : R} {notes : Notes}
    (ordinary : kind ≠ .unload) (step : Labeled.Step program kind.rule actor before after) :
    GuardedSuffix.Transition program notes (.lifecycle kind actor) before after := by
  cases kind
  case unload => exact False.elim (ordinary rfl)
  all_goals exact step

/-- The supplied notes are uniquely determined by the actual execution.
Each capture stamp is the index just after its source event. -/
theorem Trace.notes_eq (trace : Trace program last) (time : Nat) (bounded : time ≤ last) :
    trace.notes time = cutNotes trace.state trace.actor time := by
  induction time with
  | zero =>
    rw [trace.seed]
    apply Prod.ext
    · funext name
      simp [cutNotes, birthAt, trace.start]
    · rfl
  | succ time ih =>
    rw [(trace.step time (by omega)).2, ih (by omega)]
    rfl

theorem Trace.projects (trace : Trace program last) (time : Nat) (bounded : time ≤ last) :
    GuardedSuffix.SavedWordsAgree (trace.state time) (trace.notes time) := by
  induction time with
  | zero =>
    intro name
    simp [trace.seed, trace.start, saved]
  | succ time ih => exact GuardedSuffix.step_projects (trace.step time (by omega)) (ih (by omega))

theorem Trace.births_agree (trace : Trace program last) (time : Nat) (bounded : time ≤ last) :
    GuardedSuffix.BirthsAgree (trace.state time) (trace.notes time) := by
  rw [trace.notes_eq time bounded]
  intro name
  exact birthAt_none

/-- The only transition whose endpoint uses a different discharge is
L-Unload. The labels and guards of every other event are native. -/
theorem transition_cases {notes : Notes} {event : Ev} {before after : R}
    (step : GuardedSuffix.Transition program notes event before after) :
    Labeled.Step program (eventRule event) (eventActor event) before after ∨
      (∃ actor, event = .lifecycle .unload actor ∧ GuardedSuffix.Unload actor before notes after) := by
  cases event with
  | command command => exact .inl (ExchangeReplay.command_labeled command step)
  | lifecycle kind actor =>
    cases kind
    case unload => exact .inr ⟨actor, rfl, step⟩
    all_goals exact .inl step

private theorem replay_views (live : Name → Option Nat) (word : List C) (state : R) :
    ControlFrame.viewAt (replay live word state) = ControlFrame.viewAt state := by
  funext name
  cases found : state name with
  | none => simp [ControlFrame.viewAt, found, (replay_presence live word state name).mpr found]
  | some row =>
    obtain ⟨reverted, present, _, _, phase⟩ := replay_keeps_control live word state name row found
    simp [ControlFrame.viewAt, present, found, phase]

theorem unload_views {actor : Name} {state after : R} {notes : Notes}
    (step : GuardedSuffix.Unload actor state notes after) (name : Name) :
    ControlFrame.viewAt after name = if name = actor then none else ControlFrame.viewAt state name := by
  obtain ⟨row, view, present, _, _, rfl⟩ := step
  obtain ⟨retained, found, _, _, _⟩ := replay_keeps_control notes.1 (notes.2 actor) state actor row present
  rw [ControlFrame.mark_viewAt _ _ _ _ found, replay_views]
  rfl

/-- A guarded unload preserves all live stamps and clears just its own stack. -/
theorem unload_update_notes {before after : R} {actor : Name} {notes : Notes} (stamp : Nat)
    (step : GuardedSuffix.Unload actor before notes after) (births : GuardedSuffix.BirthsAgree before notes) :
    noteStep before after actor stamp notes =
      (notes.1, fun name => if name = actor then [] else notes.2 name) := by
  obtain ⟨row, view, found, _, _, endpoint⟩ := step
  have kept (name : Name) : after name = none ↔ before name = none := by
    rw [endpoint, Transposition.mark_presence, replay_presence]
  have clears (name : Name) : saved after name = if name = actor then [] else saved before name := by
    rw [endpoint]
    obtain ⟨retained, present, _, _, _⟩ := replay_keeps_control notes.1 (notes.2 actor) before actor row found
    rw [PartialReplayRegistry.saved_mark _ _ _ present, GuardedSuffix.replay_saved]
    rfl
  apply Prod.ext
  · funext name
    change (after name).map (fun _ => (notes.1 name).getD stamp) = notes.1 name
    cases current : after name with
    | none => exact ((births name).mpr ((kept name).mp current)).symm
    | some entry =>
      cases birth : notes.1 name with
      | none =>
        have missing := (kept name).mpr ((births name).mp birth)
        rw [current] at missing
        cases missing
      | some index => rfl
  · exact advance_cleanup actor stamp notes.2 clears

theorem Trace.unload_notes (trace : Trace program last) {time : Nat} {actor : Name}
    (bound : time < last) (event : trace.event time = .lifecycle .unload actor) :
    trace.notes (time + 1) =
      ((trace.notes time).1, fun name => if name = actor then [] else (trace.notes time).2 name) := by
  have step := trace.step time bound
  rw [event] at step
  exact step.2.trans (unload_update_notes (time + 1) step.1 (trace.births_agree time (Nat.le_of_lt bound)))

theorem transition_stable {notes : Notes} {event : Ev} {before after : R}
    (step : GuardedSuffix.Transition program notes event before after) : Frame.Stable before after := by
  rcases transition_cases step with native | ⟨actor, _, unload⟩
  · exact Frame.step_stable program native.toCalculus
  · obtain ⟨row, view, present, phase, free, rfl⟩ := unload
    apply Frame.mark_after
    intro name old new oldAt newAt
    obtain ⟨found, atFound, component, parent, _⟩ := replay_keeps_control notes.1 (notes.2 actor) before name old oldAt
    have same := Option.some.inj (atFound.symm.trans newAt)
    subst new
    refine ⟨component.symm, parent.symm, fun retired => ?_⟩
    have flag := replay_retired notes.1 (notes.2 actor) before name
    simpa [atFound, oldAt, retired] using flag

theorem Trace.parent_closed (trace : Trace program last) (time : Nat) (bounded : time ≤ last) :
    Safety.ParentClosed (trace.state time) := by
  induction time with
  | zero => rw [trace.start]; exact Safety.empty_parentClosed
  | succ time ih =>
    have prior := ih (by omega)
    rcases transition_cases (trace.step time (by omega)).1 with native | ⟨actor, _, unload⟩
    · exact Safety.step_parentClosed program native.toCalculus prior
    · obtain ⟨row, view, present, phase, free, endpoint⟩ := unload
      rw [endpoint]
      apply Safety.mark_parentClosed
      let state := trace.state time
      let live := (trace.notes time).1
      let word := (trace.notes time).2 actor
      intro child row parent found parentOf absent
      have oldPresent : state child ≠ none := fun missing => by
        rw [(replay_presence live word state child).mpr missing] at found
        cases found
      cases atChild : state child with
      | none => exact oldPresent atChild
      | some original =>
        obtain ⟨retained, atRetained, _, sameParent, _⟩ := replay_keeps_control live word state child original atChild
        have same := Option.some.inj (atRetained.symm.trans found)
        subst row
        exact prior child original parent atChild (sameParent.symm.trans parentOf)
          ((replay_presence live word state parent).mp absent)

/-- The slot-event summary of guarded unload is the same table discharge
and stack clearing as in the paper. The stamps only change retirements. -/
theorem transition_event {notes : Notes} {event : Ev} {before after : R}
    (step : GuardedSuffix.Transition program notes event before after) :
    ReplayEvent program (eventActor event) before after := by
  rcases transition_cases step with native | ⟨actor, rfl, unload⟩
  · exact PartialReplayRegistry.event_of_step program native
  · have closed := unload_views unload actor
    rw [if_pos rfl] at closed
    obtain ⟨row, view, present, phase, free, rfl⟩ := unload
    let word := notes.2 actor
    have selected : saved before actor = word.map Capture.token := by
      simp [saved, present, phase, Phase.accumulator, word]
    obtain ⟨reverted, found, _, _, _⟩ := replay_keeps_control notes.1 word before actor row present
    refine .cleanup selected free ?_ ?_ closed
    · intro name key
      rw [StageRecovery.tableAt_mark]
      exact replay_tables notes.1 word (left := before) (right := before) (fun _ _ => rfl) name key
    · intro name
      rw [PartialReplayRegistry.saved_mark _ _ _ found, GuardedSuffix.replay_saved]
      rfl

theorem Trace.replayEvent (trace : Trace program last) {time : Nat} (bounded : time < last) :
    ReplayEvent program (trace.actor time) (trace.state time) (trace.state (time + 1)) :=
  transition_event (trace.step time bounded).1

theorem Trace.capture_origin (trace : Trace program last) (time : Nat) (bounded : time ≤ last)
    (name : Name) (capture : C) (recorded : capture ∈ (trace.notes time).2 name) :
    capture.index ≤ time ∧ OriginOn program last trace.state trace.actor name capture := by
  rw [trace.notes_eq time bounded] at recorded
  exact (track_facts trace.state trace.actor trace.start
    (fun _ bound => trace.replayEvent bound) time bounded).2 name capture recorded

/-- The component of a saved capture is the component at its producing
landing. A removal would empty the acting stack, so no retained capture
can be inherited by a later incarnation of its actor. -/
theorem Trace.capture_origin_component (trace : Trace program last) {time : Nat} (bounded : time ≤ last)
    {name : Name} {entry : F} (current : trace.state time name = some entry)
    (capture : C) (recorded : capture ∈ (trace.notes time).2 name) :
    capture.index ≤ time ∧ ∃ step, step < last ∧ capture.index = step + 1 ∧ trace.actor step = name ∧
      ∃ prior : F, trace.state step name = some prior ∧ prior.component = entry.component ∧
        ∃ middle code next, Land program name code (trace.state step) middle capture.token next := by
  obtain ⟨age, step, inside, index, acted, middle, code, next, landed, pushed, presence⟩ :=
    trace.capture_origin time bounded name capture recorded
  have source : trace.state step name ≠ none := by
    intro absent
    have after : trace.state (step + 1) name ≠ none := by
      intro missing
      have impossible := pushed name
      simp [saved, missing, absent] at impossible
    obtain ⟨component, _, ready, _⟩ := Transposition.land_new_name program landed name absent
      (fun missing => after ((presence name).mpr missing))
    exact ready.2.1 name rfl absent
  have retained (cut : Nat) (lower : step ≤ cut) (upper : cut ≤ time) : trace.state cut name ≠ none := by
    by_cases original : cut = step
    · simpa only [original] using source
    intro absent
    have empty : (trace.notes cut).2 name = [] := by
      have projected := trace.projects cut (Nat.le_trans upper bounded) name
      have rawEmpty : saved (trace.state cut) name = [] := by simp [saved, absent]
      exact List.map_eq_nil_iff.mp (projected.trans rawEmpty)
    rw [trace.notes_eq cut (Nat.le_trans upper bounded)] at empty
    have tracked : capture ∈ track trace.state trace.actor time name := by
      simpa only [trace.notes_eq time bounded] using recorded
    have newer := capture_after_empty trace.state trace.actor name upper empty tracked
    omega
  cases found : trace.state step name with
  | none => exact False.elim (source found)
  | some prior =>
    have metadata (cut : Nat) (lower : step ≤ cut) (upper : cut ≤ time) (row : F)
        (present : trace.state cut name = some row) : prior.component = row.component := by
      induction cut generalizing row with
      | zero =>
        have same : step = 0 := by omega
        rw [same, present] at found
        exact congrArg Fiber.component (Option.some.inj found).symm
      | succ cut ih =>
        by_cases same : step = cut + 1
        · rw [same, present] at found
          exact congrArg Fiber.component (Option.some.inj found).symm
        · cases previous : trace.state cut name with
          | none => exact False.elim (retained cut (by omega) (by omega) previous)
          | some old =>
            have stable := transition_stable (trace.step cut (by omega : cut < last)).1 name old row previous present
            exact (ih (by omega) (by omega) old previous).trans stable.1
    exact ⟨age, step, inside, index, acted, prior, found, metadata time (by omega) (by omega) entry current,
      middle, code, next, landed⟩

/-- The actor's birth and component immediately before the stamped event. -/
def Trace.sourceAt (trace : Trace program last) (stamp : Nat) : Option (GuardedSuffix.ActorSource Key Code) :=
  some (GuardedSuffix.actorSource (trace.state (stamp - 1)) (trace.notes (stamp - 1)) (trace.event (stamp - 1)))

@[simp] theorem Trace.sourceAt_succ (trace : Trace program last) (time : Nat) :
    trace.sourceAt (time + 1) = some (GuardedSuffix.actorSource (trace.state time) (trace.notes time) (trace.event time)) := rfl

/-- A segment retaining the source actor data and root classification at
each original event cut. -/
theorem Trace.source_segment (trace : Trace program last) (start length : Nat) (bounded : start + length ≤ last) :
    let cuts := List.range' start length
    GuardedSuffix.ExecWith program trace.sourceAt (cuts.map fun time => (time + 1, trace.event time))
      (trace.state start) (trace.notes start) (trace.state (start + length)) (trace.notes (start + length))
      (cuts.flatMap fun time => eventRoots (trace.state time) (trace.event time)) := by
  dsimp only
  induction length generalizing start with
  | zero => exact .nil _ _
  | succ length ih =>
    have same : start + 1 + length = start + (length + 1) := by omega
    rw [List.range'_succ, List.map_cons, List.flatMap_cons, ← same]
    exact .cons (trace.step start (by omega)) (ih (start + 1) (by omega)) (by simp [GuardedSuffix.CheckedSource])

theorem Trace.segment (trace : Trace program last) (start length : Nat) (bounded : start + length ≤ last) :
    let cuts := List.range' start length
    GuardedSuffix.Exec program (cuts.map fun time => (time + 1, trace.event time))
      (trace.state start) (trace.notes start) (trace.state (start + length)) (trace.notes (start + length))
      (cuts.flatMap fun time => eventRoots (trace.state time) (trace.event time)) :=
  (trace.source_segment start length bounded).forgetSources

theorem Trace.capture_through_interval (trace : Trace program last)
    (name : Name) {first time : Nat} (lower : first ≤ time) (bounded : time ≤ last)
    (installed : ∀ point, first < point → point ≤ time → ControlFrame.viewAt (trace.state point) name ≠ none)
    {capture : C} (recorded : capture ∈ (trace.notes first).2 name) :
    capture ∈ (trace.notes time).2 name := by
  induction time with
  | zero => exact (show first = 0 by omega) ▸ recorded
  | succ time ih =>
    by_cases same : first = time + 1
    · exact same ▸ recorded
    have step := trace.step time (by omega)
    rw [step.2]
    change capture ∈ advance (trace.state time) (trace.state (time + 1)) (trace.actor time)
      (time + 1) (trace.notes time).2 name
    apply event_capture_persists (trace.replayEvent (by omega : time < last)) _ _ (trace.projects time (by omega))
      name (installed (time + 1) (by omega) (by omega))
    exact ih (by omega) (by omega) (fun point later earlier => installed point later (by omega))

/-- Every retained callback came from an actual landing in the guarded trace. -/
theorem Trace.captured (trace : Trace program last) (time : Nat) (bounded : time ≤ last) :
    AccumulatorProvenance.Accumulators (AccumulatorProvenance.Captured program) (trace.state time) := by
  intro name row found token member
  have stored : token ∈ saved (trace.state time) name := by simpa [saved, found] using member
  rw [← trace.projects time bounded name] at stored
  obtain ⟨capture, recorded, rfl⟩ := List.mem_map.mp stored
  obtain ⟨_, _, _, _, _, _, _, landed, _, _⟩ := (trace.capture_origin time bounded name capture recorded).2
  exact AccumulatorProvenance.land_captured program _ _ _ _ _ _ landed

theorem Trace.self_related [Setoid Value] (trace : Trace program last)
    (time : Nat) (bounded : time ≤ last) (witnesses : StageRecovery.OperationWitnesses program) :
    StageSimulation.Related Eq (trace.state time) (trace.state time) := by
  apply Transposition.state_self_related
  intro name row found token member
  exact AccumulatorProvenance.captured_respects program witnesses token
    (trace.captured time bounded name row found token member)

private theorem replay_ordering (live : Name → Option Nat) (word : List C) (state : R) (actor : Name)
    (own : ∀ inverse ∈ word.map Capture.token, Ordering.OwnInverse actor inverse)
    (free : ¬ Relied state actor) (valid : Ordering.Invariant state) :
    Ordering.Invariant (replay live word state) ∧ ¬ Relied (replay live word state) actor := by
  induction word generalizing state with
  | nil => exact ⟨valid, free⟩
  | cons capture rest ih =>
    have writes (inverse : I) (allowed : Ordering.OwnInverse actor inverse) :
        Ordering.Invariant (Stages.undo inverse state) ∧ ¬ Relied (Stages.undo inverse state) actor :=
      ⟨⟨Ordering.undo_supported state actor inverse allowed free valid.1, Ordering.undo_local state inverse valid.2⟩,
        Ordering.undo_not_relied state inverse actor free⟩
    have one := writes capture.token (own capture.token (by simp))
    have applied : Ordering.Invariant (capture.apply live state) ∧ ¬ Relied (capture.apply live state) actor := by
      obtain ⟨token, index⟩ := capture
      cases token with
      | retire child =>
        by_cases current : live child = some index
        · simpa only [Capture.apply, if_pos current] using one
        · simpa only [Capture.apply, if_neg current] using And.intro valid free
      | _ => exact one
    exact ih _ (fun inverse member => own inverse (by simp [member])) applied.2 applied.1

private theorem replay_scoped (live : Name → Option Nat) (word : List C) (state : R)
    (routes : PartialReplayRouting.ScopedAccumulators state) :
    PartialReplayRouting.ScopedAccumulators (replay live word state) := by
  intro name row after inverse member
  cases original : state name with
  | none =>
    have absent := (replay_presence live word state name).mpr original
    rw [after] at absent
    cases absent
  | some prior =>
    obtain ⟨retained, found, component, _, phase⟩ := replay_keeps_control live word state name prior original
    have same := Option.some.inj (after.symm.trans found)
    subst retained
    rw [component, phase]
    exact routes name prior original inverse (by simpa only [phase] using member)

/-- The guarded transition preserves the actual supplying bindings and
the stored routes used by later slot replays. -/
theorem transition_invariants {notes : Notes} {event : Ev} {before after : R}
    (step : GuardedSuffix.Transition program notes event before after)
    (valid : Ordering.Invariant before) (routes : PartialReplayRouting.ScopedAccumulators before) :
    Ordering.Invariant after ∧ PartialReplayRouting.ScopedAccumulators after := by
  rcases transition_cases step with native | ⟨actor, _, unload⟩
  · exact ⟨Ordering.step_invariant program native.toCalculus valid,
      PartialReplayRouting.step_scoped program native.toCalculus routes⟩
  · obtain ⟨row, view, present, phase, free, rfl⟩ := unload
    let word := notes.2 actor
    let reverted := replay notes.1 word before
    have own (inverse : I) (member : inverse ∈ word.map Capture.token) : Ordering.OwnInverse actor inverse :=
      valid.2 actor row present inverse (by simpa only [phase, Phase.accumulator] using member)
    obtain ⟨supported, stillFree⟩ := replay_ordering notes.1 word before actor own free valid
    exact ⟨⟨Ordering.mark_inactive_supported reverted actor stillFree supported.1,
      Ordering.mark_local reverted actor .inactive supported.2 (by simp [Phase.accumulator])⟩,
      PartialReplayRouting.mark_scoped reverted actor .inactive (by simp [Phase.accumulator])
        (replay_scoped notes.1 word before routes)⟩

theorem Trace.invariants (trace : Trace program last) (time : Nat) (bounded : time ≤ last) :
    Ordering.Invariant (trace.state time) ∧ PartialReplayRouting.ScopedAccumulators (trace.state time) := by
  induction time with
  | zero => rw [trace.start]; exact ⟨⟨Ordering.supported_empty, Ordering.local_empty⟩, PartialReplayRouting.scoped_empty⟩
  | succ time ih =>
    have prior := ih (by omega)
    exact transition_invariants (trace.step time (by omega)).1 prior.1 prior.2

theorem Trace.supported (trace : Trace program last) (time : Nat) (bounded : time ≤ last) :
    Ordering.Supported (trace.state time) := (trace.invariants time bounded).1.1

private theorem replay_owned (live : Name → Option Nat) (word : List C) (state : R)
    (owned : Safety.Owned state) : Safety.Owned (replay live word state) := by
  induction word generalizing state with
  | nil => exact owned
  | cons capture rest ih =>
    apply ih
    rcases capture with ⟨token, index⟩
    cases token with
    | unit => exact owned
    | restrict owner key => exact Safety.undo_owned state (.restrict owner key) owned
    | operate owner key inverse => exact Safety.undo_owned state (.operate owner key inverse) owned
    | retire child =>
      simp only [Capture.apply]
      split
      · exact Safety.retire_owned _ _ owned
      · exact owned

/-- Table ownership and declaration disjointness also hold with guarded
unload. They give uniqueness of the declared provider chosen by Begin. -/
theorem Trace.ownership (trace : Trace program last) (time : Nat) (bounded : time ≤ last) :
    Safety.Owned (trace.state time) ∧ WellFormed.Disjoint (trace.state time) := by
  induction time with
  | zero => rw [trace.start]; exact ⟨Safety.empty_owned, WellFormed.disjoint_empty⟩
  | succ time ih =>
    obtain ⟨owned, disjoint⟩ := ih (by omega)
    rcases transition_cases (trace.step time (by omega)).1 with native | ⟨actor, _, unload⟩
    · exact ⟨Safety.step_owned program native.toCalculus owned, WellFormed.step_disjoint program native.toCalculus disjoint⟩
    · obtain ⟨row, view, present, phase, free, endpoint⟩ := unload
      rw [endpoint]
      refine ⟨Safety.mark_owned _ _ _ (replay_owned _ _ _ owned), WellFormed.mark_disjoint _ _ _ ?_⟩
      apply WellFormed.disjoint_of_origins ?_ disjoint
      intro name observed found
      cases initial : trace.state time name with
      | none =>
        have vacant := (replay_presence (trace.notes time).1 ((trace.notes time).2 actor)
          (trace.state time) name).mpr initial
        rw [found] at vacant
        cases vacant
      | some original =>
        obtain ⟨actual, retained, component, _, _⟩ := replay_keeps_control (trace.notes time).1
          ((trace.notes time).2 actor) (trace.state time) name original initial
        exact ⟨original, rfl, component.symm.trans (congrArg Fiber.component (Option.some.inj (retained.symm.trans found)))⟩

/-- Every actual unload prefix retains the dependency and inverse-routing
invariants while the unloader's own committed view is still installed. -/
theorem Trace.unload_prefix_invariants (trace : Trace program last) {time : Nat} (bounded : time < last)
    {actor : Name} (event : trace.event time = .lifecycle .unload actor)
    {prefixWord suffixWord : List C} (splitWord : (trace.notes time).2 actor = prefixWord ++ suffixWord) :
    let intermediate := replay (trace.notes time).1 prefixWord (trace.state time)
    Ordering.Invariant intermediate ∧ PartialReplayRouting.ScopedAccumulators intermediate ∧
      ¬ Relied intermediate actor := by
  have step := (trace.step time bounded).1
  rw [event] at step
  obtain ⟨row, view, present, phase, free, _⟩ := step
  have valid := trace.invariants time (Nat.le_of_lt bounded)
  have own (inverse : I) (member : inverse ∈ prefixWord.map Capture.token) : Ordering.OwnInverse actor inverse := by
    obtain ⟨capture, inPrefix, rfl⟩ := List.mem_map.mp member
    apply valid.1.2 actor row present
    rw [phase]
    change capture.token ∈ ((trace.notes time).2 actor).map Capture.token
    rw [splitWord]
    exact List.mem_map.mpr ⟨capture, List.mem_append_left _ inPrefix, rfl⟩
  obtain ⟨supported, stillFree⟩ := replay_ordering _ prefixWord _ actor own free valid.1
  exact ⟨supported, replay_scoped _ _ _ valid.2, stillFree⟩

/-- A foreign operation from the actual saved word still has a retained
binding at every intermediate replay cut, including just before its turn. -/
theorem Trace.unload_prefix_provider (trace : Trace program last) {time : Nat} (bounded : time < last)
    {actor owner : Name} (event : trace.event time = .lifecycle .unload actor)
    {prefixWord suffixWord : List C} (splitWord : (trace.notes time).2 actor = prefixWord ++ suffixWord)
    {capture : C} (member : capture ∈ (trace.notes time).2 actor)
    {key : Key} {inverse : Value → Value} (token : capture.token = .operate owner key inverse)
    (foreignOwner : owner ≠ actor) :
    Ordering.Supply (replay (trace.notes time).1 prefixWord (trace.state time)) owner key := by
  have step := (trace.step time bounded).1
  rw [event] at step
  obtain ⟨row, view, present, phase, _, _⟩ := step
  obtain ⟨intermediate, found, _, _, samePhase⟩ :=
    replay_keeps_control (trace.notes time).1 prefixWord (trace.state time) actor row present
  have stored : .operate owner key inverse ∈ intermediate.phase.accumulator := by
    rw [samePhase, phase, Phase.accumulator, ← token]
    exact List.mem_map.mpr ⟨capture, member, rfl⟩
  have valid := trace.unload_prefix_invariants bounded event splitWord
  obtain ⟨chosen, committed, required, route⟩ :=
    (valid.2.1 actor intermediate found _ stored).resolve_left foreignOwner
  exact (valid.1.1 actor owner key ⟨intermediate, chosen, found, required, committed, route⟩).2

/-- Both legal replay orders can use the partial slot history calculated
from the guarded source trace, including its actual unload steps. -/
theorem Trace.slot_history (trace : Trace program last) (meaning : Coeffects program)
    (time : Nat) (bounded : time ≤ last) (owner : Name) (key : Key) :
    SlotHistory meaning (trace.state time) owner key := by
  induction time with
  | zero => rw [trace.start]; exact PartialReplayRegistry.slot_history_empty meaning owner key
  | succ time ih =>
    exact PartialReplayRegistry.slot_history_step meaning (trace.replayEvent (by omega : time < last))
      (trace.invariants time (by omega)).2 (ih (by omega))

end Cordis.Repairs.GuardedHistory
