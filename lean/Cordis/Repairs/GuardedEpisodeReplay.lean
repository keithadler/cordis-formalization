import Cordis.Repairs.GuardedEpisodeBoundary

/-! Control and binding-domain preservation for guarded interior replay. -/
namespace Cordis.Repairs.GuardedHistory
open Calculus Stages Incarnation IncarnationReplay LegalHistory
open EpisodeReplayGuards (Projection)
open PartialReplayRegistry (saved)
open Vestigial (CutNotes noteStep)
universe u
variable {Name Key Value Code Error : Type u} [DecidableEq Name] [DecidableEq Key]
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
local notation "I" => Inverse Name Key Value
local notation "Notes" => CutNotes Name Key Value
local notation "Program" => Code → Instruction Name Key Value Code Error
variable {program : Code → Instruction Name Key Value Code Error} {last : Nat}

theorem probe_projects (trace : Trace program last) (episode : ClosedEpisode trace)
    (maximal : ∀ later : ClosedEpisode trace, ¬ EpisodeEdge episode later)
    (quiet : Progress.Quiet (trace.state last))
    {time : Nat} (lower : episode.opened ≤ time) (upper : time ≤ episode.closed) :
    Projection episode.name (fun name => withdraws trace episode time name = true)
      (trace.state time) (probeAt trace episode time) := by
  have lastBound := episode.interval.bounded
  let source := trace.state time
  let word := (trace.notes time).2 episode.name
  obtain ⟨owner, _, ownerAt, _⟩ := OrderingIntervals.installed_view source episode.name
    (episode.interval.installed time lower upper)
  have scope : ∀ token ∈ word.map Capture.token, TableFrame.Scoped episode.name owner.component.requires token := by
    intro token carried
    have project := trace.projects time (by omega) episode.name
    change word.map Capture.token = saved source episode.name at project
    rw [project] at carried
    exact trace.table_scope time (by omega) episode.name owner ownerAt token (by simpa [saved, ownerAt] using carried)
  exact EpisodeRollback.projection_of_saved_word source episode.name owner.component.requires (trace.notes time).1
    word scope (by
      intro name omitted
      obtain ⟨birth, starts, earlier, creator, rule, lives⟩ := withdrawn_birth trace episode lower upper omitted
      exact child_never_installed trace episode maximal quiet starts earlier creator rule (by omega) lives)

theorem probe_keeps_phase (trace : Trace program last) (episode : ClosedEpisode trace)
    {time : Nat} {actor : Name} {row : F} (different : actor ≠ episode.name)
    (kept : ¬ withdraws trace episode time actor = true)
    (present : trace.state time actor = some row) :
    ∃ paired, probeAt trace episode time actor = some paired ∧ paired.phase = row.phase := by
  obtain ⟨paired, found, _, _, phase⟩ := replay_keeps_control (trace.notes time).1
    ((trace.notes time).2 episode.name) (trace.state time) actor row present
  exact ⟨paired, by simpa [probeAt, rollbackOf, kept, Transposition.mark_other _ _ _ _ different] using found, phase⟩

theorem closing_actor_retained (trace : Trace program last) (episode : ClosedEpisode trace)
    {time : Nat} (lower : episode.opened ≤ time) (upper : time ≤ episode.closed) :
    ¬ withdraws trace episode time episode.name = true := by
  intro selected
  obtain ⟨birth, starts, earlier, _, _, lives⟩ := withdrawn_birth trace episode lower upper selected
  have vacant : trace.state birth episode.name = none := by
    simpa using lives.boundary.resolve_left (by omega)
  exact episode.interval.installed birth starts (by omega) (by simp [ControlFrame.viewAt, vacant])

theorem probe_keeps_saved (trace : Trace program last) (episode : ClosedEpisode trace) {time : Nat} {actor : Name}
    (different : actor ≠ episode.name) (kept : ¬ withdraws trace episode time actor = true) :
    saved (probeAt trace episode time) actor = saved (trace.state time) actor := by
  cases found : trace.state time actor with
  | none =>
    have absent : probeAt trace episode time actor = none := by
      change (if withdraws trace episode time actor then none else
        mark (replay (trace.notes time).1 ((trace.notes time).2 episode.name) (trace.state time))
          episode.name .inactive actor) = none
      rw [if_neg kept, Transposition.mark_presence, replay_presence]
      exact found
    simp [saved, found, absent]
  | some row =>
    obtain ⟨paired, present, phase⟩ := probe_keeps_phase trace episode different kept found
    simp [saved, present, found, phase]

/-- The first probe is the source registry before the omitted opening Begin. -/
theorem probe_at_opening (trace : Trace program last) (episode : ClosedEpisode trace) :
    probeAt trace episode episode.opened = trace.state (episode.opened - 1) := by
  have empty := empty_on_entry trace episode
  obtain ⟨fiber, _, found, inactive, _, _, together⟩ := (begin_boundary trace episode.interval).2
  funext name
  have noneWithdrawn : withdraws trace episode episode.opened name = false := by simp [withdraws, empty]
  simp only [probeAt, rollbackOf, noneWithdrawn, Bool.false_eq_true, if_false, empty, replay]
  rw [together]
  by_cases same : name = episode.name
  · subst name
    rw [mark_self _ _ _ _ (mark_self _ _ _ _ found), found]
    cases fiber
    simp_all
  · rw [Transposition.mark_other _ _ _ _ same, Transposition.mark_other _ _ _ _ same]

theorem Trace.live_unchanged_at (trace : Trace program last) {time : Nat} (bound : time < last)
    (name : Name) (presence : trace.state (time + 1) name = none ↔ trace.state time name = none) :
    (trace.notes (time + 1)).1 name = (trace.notes time).1 name := by
  rw [trace.notes_eq (time + 1) (by omega), trace.notes_eq time (by omega)]
  exact EpisodeRollback.birthAt_same_presence_at trace.state time name presence

theorem Trace.live_unchanged (trace : Trace program last) {time : Nat} (bound : time < last)
    (presence : ∀ name, trace.state (time + 1) name = none ↔ trace.state time name = none) :
    (trace.notes (time + 1)).1 = (trace.notes time).1 :=
  funext fun name => trace.live_unchanged_at bound name (presence name)

theorem Trace.foreign_word_unchanged (trace : Trace program last) {time : Nat} (bound : time < last)
    {name : Name} (foreign : name ≠ trace.actor time) :
    (trace.notes (time + 1)).2 name = (trace.notes time).2 name := by
  rw [(trace.step time bound).2]
  change advance _ _ (trace.actor time) _ _ name = _
  rw [advance, if_neg foreign]

theorem mask_unchanged (trace : Trace program last) (episode : ClosedEpisode trace) {time : Nat}
    (live : (trace.notes (time + 1)).1 = (trace.notes time).1)
    (word : (trace.notes (time + 1)).2 episode.name = (trace.notes time).2 episode.name) :
    withdraws trace episode (time + 1) = withdraws trace episode time := by
  funext name
  unfold withdraws
  rw [live, word]

theorem probe_notes_at_opening (trace : Trace program last) (episode : ClosedEpisode trace) :
    probeNotes trace episode episode.opened = trace.notes (episode.opened - 1) := by
  let time := episode.opened - 1
  have bound := episode.interval.bounded
  have order := episode.interval.ordered
  have positive := episode.interval.positive
  have next : time + 1 = episode.opened := by dsimp [time]; omega
  obtain ⟨event, row, view, found, inactive, _, _, endpoint⟩ := begin_boundary trace episode.interval
  have empty := empty_on_entry trace episode
  have live := trace.live_unchanged (time := time) (by omega) (by
    intro name
    rw [next, endpoint, Transposition.mark_presence])
  have actor : trace.actor time = episode.name := by simp [Trace.actor, time, event, Vestigial.eventActor]
  apply Prod.ext
  · funext name
    have kept : withdraws trace episode episode.opened name = false := by simp [withdraws, empty]
    change (if withdraws trace episode episode.opened name then none
      else (trace.notes episode.opened).1 name) = (trace.notes time).1 name
    rw [if_neg (by simp [kept]), ← next, live]
  · funext name
    change (if name = episode.name then [] else (trace.notes episode.opened).2 name) = (trace.notes time).2 name
    by_cases same : name = episode.name
    · subst name
      rw [if_pos rfl]
      have projects := trace.projects time (by omega) episode.name
      have nil : ((trace.notes time).2 episode.name).map Capture.token = [] := by
        simpa [saved, time, found, inactive, Phase.accumulator] using projects
      exact (List.map_eq_nil_iff.mp nil).symm
    · rw [if_neg same, ← next]
      exact trace.foreign_word_unchanged (by omega) (fun equal => same (equal.trans actor))

theorem committed_avoids_closing (trace : Trace program last) (episode : ClosedEpisode trace)
    (maximal : ∀ later : ClosedEpisode trace, ¬ EpisodeEdge episode later)
    {time : Nat} (lower : episode.opened ≤ time) (upper : time ≤ episode.closed)
    {actor : Name} {fiber : F} {view : View Name Key}
    (present : trace.state time actor = some fiber) (committed : fiber.phase.committed = some view) :
    ∀ key, fiber.component.requires key → view key ≠ episode.name := by
  intro key required selects
  exact no_demand_on_closing trace episode maximal lower upper
    ⟨fiber, view, present, required, committed, selects⟩

/-- Retained operations keep their occupied provider address. -/
theorem location_on_probe (trace : Trace program last) (episode : ClosedEpisode trace)
    (maximal : ∀ later : ClosedEpisode trace, ¬ EpisodeEdge episode later)
    (quiet : Progress.Quiet (trace.state last))
    {time : Nat} (lower : episode.opened ≤ time) (upper : time ≤ episode.closed)
    {actor owner : Name} (different : actor ≠ episode.name)
    (kept : ¬ withdraws trace episode time actor = true) {row : F}
    (present : trace.state time actor = some row) {key : Key} {value : Value}
    (located : location (trace.state time) actor key = some (owner, value)) :
    ∃ other, location (probeAt trace episode time) actor key = some (owner, other) := by
  have lastBound := episode.interval.bounded
  exact (probe_projects trace episode maximal quiet lower upper).location_forward kept different
    (trace.supported time (by omega))
    (fun _ => no_demand_on_closing trace episode maximal lower upper) present located

theorem rollbackOf_mark (trace : Trace program last) (episode : ClosedEpisode trace)
    (time : Nat) (state : R) (actor : Name) (phase : Phase Name Key Code I)
    (different : actor ≠ episode.name) (kept : ¬ withdraws trace episode time actor = true) :
    rollbackOf trace episode time (mark state actor phase) = mark (rollbackOf trace episode time state) actor phase := by
  let restored := replay (trace.notes time).1 ((trace.notes time).2 episode.name) state
  unfold rollbackOf
  rw [EpisodeRollback.replay_mark]
  funext name
  change (if withdraws trace episode time name then none
    else mark (mark restored actor phase) episode.name .inactive name) = _
  rw [← Transposition.marks_commute restored actor episode.name phase .inactive different]
  by_cases same : name = actor
  · subst name
    simp [kept, mark, Calculus.modify, restored]
  · simp [mark, Calculus.modify, same, restored]

/-- Marking a retained actor commutes with rollback. The other edits may
change bindings, provided that they preserve presence at every name. -/
theorem probe_after_foreign_edit (trace : Trace program last) (episode : ClosedEpisode trace)
    {time : Nat} (bound : time < last) {phase : Phase Name Key Code I} {middle : R}
    (different : trace.actor time ≠ episode.name)
    (kept : ¬ withdraws trace episode time (trace.actor time) = true)
    (presence : ∀ name, middle name = none ↔ trace.state time name = none)
    (marked : trace.state (time + 1) = mark middle (trace.actor time) phase) :
    probeAt trace episode (time + 1) =
      mark (rollbackOf trace episode time middle) (trace.actor time) phase := by
  have word := trace.foreign_word_unchanged bound (Ne.symm different)
  have live := trace.live_unchanged bound (fun name => by
    rw [marked]
    exact (Transposition.mark_presence _ _ _ _).trans (presence name))
  have mask := mask_unchanged trace episode live word
  change rollbackOf trace episode (time + 1) (trace.state (time + 1)) = _
  have same : rollbackOf trace episode (time + 1) (trace.state (time + 1)) =
      rollbackOf trace episode time (trace.state (time + 1)) := by
    unfold rollbackOf
    rw [mask, word, live]
  rw [same, marked]
  exact rollbackOf_mark trace episode time middle (trace.actor time) phase different kept

theorem probe_after_foreign_mark (trace : Trace program last) (episode : ClosedEpisode trace)
    {time : Nat} (bound : time < last) {phase : Phase Name Key Code I}
    (different : trace.actor time ≠ episode.name)
    (kept : ¬ withdraws trace episode time (trace.actor time) = true)
    (marked : trace.state (time + 1) = mark (trace.state time) (trace.actor time) phase) :
    probeAt trace episode (time + 1) = mark (probeAt trace episode time) (trace.actor time) phase :=
  probe_after_foreign_edit trace episode bound different kept (fun _ => Iff.rfl) marked

theorem probe_saved_closing (trace : Trace program last) (episode : ClosedEpisode trace) (time : Nat) :
    saved (probeAt trace episode time) episode.name = [] := by
  by_cases hidden : withdraws trace episode time episode.name = true
  · have absent : probeAt trace episode time episode.name = none := if_pos hidden
    simp [saved, absent]
  · have kept : probeAt trace episode time episode.name =
        mark (replay (trace.notes time).1 ((trace.notes time).2 episode.name) (trace.state time))
          episode.name .inactive episode.name := if_neg hidden
    simp only [saved, kept, mark, Calculus.modify]
    cases replay (trace.notes time).1 ((trace.notes time).2 episode.name) (trace.state time) episode.name <;> rfl

/-- An exact replay step computes its cut notes by the source stamp. An
unmasked endpoint cannot revive a formerly hidden live incarnation. -/
theorem probe_notes_of_step (trace : Trace program last) (episode : ClosedEpisode trace) {time : Nat}
    (bound : time < last)
    (noRevival : ∀ name, probeAt trace episode (time + 1) name ≠ none → ¬ withdraws trace episode time name = true)
    (beforeSaved : trace.actor time ≠ episode.name → saved (probeAt trace episode time) (trace.actor time) =
      saved (trace.state time) (trace.actor time))
    (afterSaved : trace.actor time ≠ episode.name → saved (probeAt trace episode (time + 1)) (trace.actor time) =
      saved (trace.state (time + 1)) (trace.actor time)) :
    probeNotes trace episode (time + 1) = noteStep (probeAt trace episode time) (probeAt trace episode (time + 1))
      (trace.actor time) (time + 1) (probeNotes trace episode time) := by
  have actual := (trace.step time bound).2
  apply Prod.ext
  · funext name
    have targetNotes := probe_births trace episode (time + 1) (by omega) name
    change (probeNotes trace episode (time + 1)).1 name =
      (probeAt trace episode (time + 1) name).map (fun _ => ((probeNotes trace episode time).1 name).getD (time + 1))
    cases found : probeAt trace episode (time + 1) name with
    | none => exact targetNotes.mpr found
    | some row =>
      have kept : ¬ withdraws trace episode (time + 1) name = true := fun hidden =>
        Option.noConfusion (found.symm.trans (if_pos hidden))
      have prior := noRevival name (by simp [found])
      change (if withdraws trace episode (time + 1) name then none else (trace.notes (time + 1)).1 name) = _
      rw [if_neg kept]
      have sourcePresent : trace.state (time + 1) name ≠ none := by
        intro absent
        have tag := (trace.births_agree (time + 1) (by omega) name).mpr absent
        have missing := targetNotes.mp (show (probeNotes trace episode (time + 1)).1 name = none by
          change (if withdraws trace episode (time + 1) name then none else (trace.notes (time + 1)).1 name) = none
          rw [if_neg kept, tag])
        rw [found] at missing
        cases missing
      have priorStamp : (probeNotes trace episode time).1 name = (trace.notes time).1 name := if_neg prior
      rw [priorStamp, actual]
      change (trace.state (time + 1) name).map (fun _ => ((trace.notes time).1 name).getD (time + 1)) = _
      cases exactRow : trace.state (time + 1) name with
      | none => exact False.elim (sourcePresent exactRow)
      | some entry => rfl
  · funext name
    change (if name = episode.name then [] else (trace.notes (time + 1)).2 name) =
      advance (probeAt trace episode time) (probeAt trace episode (time + 1)) (trace.actor time)
        (time + 1) (probeNotes trace episode time).2 name
    by_cases actor : name = trace.actor time
    · subst name
      by_cases selected : trace.actor time = episode.name
      · rw [if_pos selected]
        simp [advance, probe_saved_closing trace episode (time + 1), selected]
      · rw [if_neg selected, actual]
        change advance (trace.state time) (trace.state (time + 1)) (trace.actor time) (time + 1)
          (trace.notes time).2 (trace.actor time) = _
        simp only [advance, beforeSaved selected, afterSaved selected]
        cases source : saved (trace.state (time + 1)) (trace.actor time) <;> simp [probeNotes, selected]
    · have unchanged := trace.foreign_word_unchanged bound actor
      simp only [advance, if_neg actor, probeNotes, unchanged]

theorem probe_notes_after_foreign_mark (trace : Trace program last) (episode : ClosedEpisode trace)
    {time : Nat} (bound : time < last) {phase : Phase Name Key Code I}
    (different : trace.actor time ≠ episode.name)
    (kept : ¬ withdraws trace episode time (trace.actor time) = true)
    (marked : trace.state (time + 1) = mark (trace.state time) (trace.actor time) phase) :
    probeNotes trace episode (time + 1) = noteStep (probeAt trace episode time) (probeAt trace episode (time + 1))
      (trace.actor time) (time + 1) (probeNotes trace episode time) := by
  have word := trace.foreign_word_unchanged bound (Ne.symm different)
  have live := trace.live_unchanged bound fun name => by rw [marked, Transposition.mark_presence]
  have mask := mask_unchanged trace episode live word
  apply probe_notes_of_step trace episode bound
  · intro name found hidden
    have hiddenNext : withdraws trace episode (time + 1) name = true := by rwa [mask]
    exact found (if_pos hiddenNext)
  · exact fun _ => probe_keeps_saved trace episode different kept
  · exact fun _ => probe_keeps_saved trace episode different (by rwa [mask])

private theorem replay_foreign_marked_step (trace : Trace program last) (episode : ClosedEpisode trace)
    {time : Nat} (bound : time < last) {phase : Phase Name Key Code I}
    {kind : Lifecycle} (event : trace.event time = .lifecycle kind (trace.actor time)) (native : kind ≠ .unload)
    (different : trace.actor time ≠ episode.name)
    (kept : ¬ withdraws trace episode time (trace.actor time) = true)
    (marked : trace.state (time + 1) = mark (trace.state time) (trace.actor time) phase)
    (moved : Labeled.Step program kind.rule (trace.actor time)
      (probeAt trace episode time) (mark (probeAt trace episode time) (trace.actor time) phase)) :
    GuardedSuffix.Step program (trace.event time) (time + 1) (probeAt trace episode time) (probeNotes trace episode time)
      (probeAt trace episode (time + 1)) (probeNotes trace episode (time + 1)) := by
  refine ⟨?_, probe_notes_after_foreign_mark trace episode bound different kept marked⟩
  rw [event, probe_after_foreign_mark trace episode bound different kept marked]
  cases kind
  case unload => exact False.elim (native rfl)
  all_goals exact moved

theorem replay_begin_between_probes (trace : Trace program last) (episode : ClosedEpisode trace)
    (maximal : ∀ later : ClosedEpisode trace, ¬ EpisodeEdge episode later)
    (quiet : Progress.Quiet (trace.state last))
    {time : Nat} (lower : episode.opened ≤ time) (upper : time < episode.closed)
    (different : trace.actor time ≠ episode.name)
    (kept : ¬ withdraws trace episode time (trace.actor time) = true)
    (event : trace.event time = .lifecycle .begin (trace.actor time)) :
    GuardedSuffix.Step program (trace.event time) (time + 1) (probeAt trace episode time) (probeNotes trace episode time)
      (probeAt trace episode (time + 1)) (probeNotes trace episode (time + 1)) := by
  have bound : time < last := Nat.lt_trans upper episode.interval.bounded
  have actual := (trace.step time bound).1
  rw [event] at actual
  change Labeled.Step program .begin (trace.actor time) _ _ at actual
  generalize endpoint : trace.state (time + 1) = after at actual
  cases actual with
  | begin _ _ row view found inactive _ target =>
    obtain ⟨other, atOther, fields⟩ := (probe_projects trace episode maximal quiet lower (by omega)).forward_row kept found
    have atNext : trace.state (time + 1) (trace.actor time) =
        some {row with phase := .reloading row.component.entry [] view} := by
      rw [endpoint, mark_self _ _ _ _ found]
    have avoids := committed_avoids_closing trace episode maximal (by omega) (by omega) atNext
      (show (Phase.reloading row.component.entry ([] : List I) view).committed = some view from rfl)
    have moved := Labeled.Step.begin (program := program) _ _ other view atOther
      ((GuardObservations.phase_inactive_iff (fields.phase different)).mp inactive) (by simp [atOther])
      ((probe_projects trace episode maximal quiet lower (by omega)).target_forward kept found view avoids target)
    rw [← fields.component] at moved
    exact replay_foreign_marked_step trace episode bound event (by decide) different kept endpoint moved

theorem replay_leave_between_probes (trace : Trace program last) (episode : ClosedEpisode trace)
    (maximal : ∀ later : ClosedEpisode trace, ¬ EpisodeEdge episode later)
    (quiet : Progress.Quiet (trace.state last))
    {time : Nat} (lower : episode.opened ≤ time) (upper : time < episode.closed)
    (different : trace.actor time ≠ episode.name)
    (kept : ¬ withdraws trace episode time (trace.actor time) = true)
    (event : trace.event time = .lifecycle .leave (trace.actor time)) :
    GuardedSuffix.Step program (trace.event time) (time + 1) (probeAt trace episode time) (probeNotes trace episode time)
      (probeAt trace episode (time + 1)) (probeNotes trace episode (time + 1)) := by
  have bound : time < last := Nat.lt_trans upper episode.interval.bounded
  have actual := (trace.step time bound).1
  rw [event] at actual
  change Labeled.Step program .leave (trace.actor time) _ _ at actual
  generalize endpoint : trace.state (time + 1) = after at actual
  cases actual with
  | leave _ _ row word view present phase stale =>
    obtain ⟨other, found, projectedPhase⟩ := probe_keeps_phase trace episode different kept present
    have projection := probe_projects trace episode maximal quiet lower (Nat.le_of_lt upper)
    exact replay_foreign_marked_step trace episode bound event (by decide) different kept endpoint
      (.leave _ _ other word view found (projectedPhase.trans phase)
        (fun active => stale (projection.target_backward _ _ active)))

theorem replay_bare_divert_between_probes (trace : Trace program last) (episode : ClosedEpisode trace)
    (maximal : ∀ later : ClosedEpisode trace, ¬ EpisodeEdge episode later)
    (quiet : Progress.Quiet (trace.state last))
    {time : Nat} (lower : episode.opened ≤ time) (upper : time < episode.closed)
    (different : trace.actor time ≠ episode.name)
    (kept : ¬ withdraws trace episode time (trace.actor time) = true)
    (event : trace.event time = .lifecycle .divert (trace.actor time))
    {row : F} {code : Code} {word : List I} {view : View Name Key}
    (present : trace.state time (trace.actor time) = some row)
    (phase : row.phase = .reloading code word view)
    (stale : ¬ Target (trace.state time) (trace.actor time) view)
    (marked : trace.state (time + 1) = mark (trace.state time) (trace.actor time) (.unloading word view)) :
    GuardedSuffix.Step program (trace.event time) (time + 1) (probeAt trace episode time) (probeNotes trace episode time)
      (probeAt trace episode (time + 1)) (probeNotes trace episode (time + 1)) := by
  obtain ⟨other, found, projectedPhase⟩ := probe_keeps_phase trace episode different kept present
  have projected := probe_projects trace episode maximal quiet lower (Nat.le_of_lt upper)
  apply replay_foreign_marked_step trace episode (Nat.lt_trans upper episode.interval.bounded) event (by decide)
    different kept marked
  simpa only [List.nil_append] using
    (Labeled.Step.divert (program := program) (probeAt trace episode time) (probeAt trace episode time)
      (trace.actor time) other code word view [] found (projectedPhase.trans phase)
      (fun active => stale (projected.target_backward _ _ active)) (.inl ⟨rfl, rfl⟩))

theorem replay_unit_activation (trace : Trace program last) (episode : ClosedEpisode trace)
    (maximal : ∀ later : ClosedEpisode trace, ¬ EpisodeEdge episode later)
    (quiet : Progress.Quiet (trace.state last))
    {time : Nat} (lower : episode.opened ≤ time) (upper : time < episode.closed)
    {kind : Lifecycle} (event : trace.event time = .lifecycle kind (trace.actor time))
    (different : trace.actor time ≠ episode.name)
    (kept : ¬ withdraws trace episode time (trace.actor time) = true)
    {row : F} {code : Code} {word : List I} {view : View Name Key}
    (present : trace.state time (trace.actor time) = some row)
    (phase : row.phase = .reloading code word view)
    (target : Target (trace.state time) (trace.actor time) view)
    (action : (program code).action = .unit)
    (label : kind.rule = Transposition.landedRule ((program code).next .unit))
    (marked : trace.state (time + 1) = mark (trace.state time) (trace.actor time)
      (Transposition.landedPhase ((program code).next .unit) .unit word view)) :
    GuardedSuffix.Step program (trace.event time) (time + 1) (probeAt trace episode time) (probeNotes trace episode time)
      (probeAt trace episode (time + 1)) (probeNotes trace episode (time + 1)) := by
  obtain ⟨other, found, projectedPhase⟩ := probe_keeps_phase trace episode different kept present
  have upper' := Nat.le_of_lt upper
  have projected := probe_projects trace episode maximal quiet lower upper'
  have avoids := committed_avoids_closing trace episode maximal lower upper' present
    (show row.phase.committed = some view by simp [phase, Phase.committed])
  have native : kind ≠ .unload := by
    intro impossible
    subst kind
    cases next : (program code).next .unit <;> simp [Lifecycle.rule, Transposition.landedRule, next] at label
  apply replay_foreign_marked_step trace episode (Nat.lt_trans upper episode.interval.bounded) event native different kept marked
  rw [label]
  exact Transposition.landed_step program other word view found (projectedPhase.trans phase)
    (projected.target_forward kept present view avoids target) (.unit _ _ _ action)

theorem replay_unit_divert (trace : Trace program last) (episode : ClosedEpisode trace)
    (maximal : ∀ later : ClosedEpisode trace, ¬ EpisodeEdge episode later)
    (quiet : Progress.Quiet (trace.state last))
    {time : Nat} (lower : episode.opened ≤ time) (upper : time < episode.closed)
    (different : trace.actor time ≠ episode.name)
    (kept : ¬ withdraws trace episode time (trace.actor time) = true)
    (event : trace.event time = .lifecycle .divert (trace.actor time))
    {row : F} {code : Code} {word : List I} {view : View Name Key}
    (present : trace.state time (trace.actor time) = some row)
    (phase : row.phase = .reloading code word view)
    (stale : ¬ Target (trace.state time) (trace.actor time) view)
    (action : (program code).action = .unit)
    (marked : trace.state (time + 1) = mark (trace.state time) (trace.actor time) (.unloading (.unit :: word) view)) :
    GuardedSuffix.Step program (trace.event time) (time + 1) (probeAt trace episode time) (probeNotes trace episode time)
      (probeAt trace episode (time + 1)) (probeNotes trace episode (time + 1)) := by
  obtain ⟨other, found, projectedPhase⟩ := probe_keeps_phase trace episode different kept present
  have projected := probe_projects trace episode maximal quiet lower (Nat.le_of_lt upper)
  exact replay_foreign_marked_step trace episode (Nat.lt_trans upper episode.interval.bounded) event (by decide)
    different kept marked (.divert _ _ _ other code word view [.unit] found (projectedPhase.trans phase)
      (fun active => stale (projected.target_backward _ _ active)) (.inr ⟨_, _, .unit _ _ _ action, rfl⟩))

theorem probe_projects_notes (trace : Trace program last) (episode : ClosedEpisode trace)
    (maximal : ∀ later : ClosedEpisode trace, ¬ EpisodeEdge episode later)
    (quiet : Progress.Quiet (trace.state last))
    {time : Nat} (lower : episode.opened ≤ time) (upper : time ≤ episode.closed) :
    GuardedSuffix.SavedWordsAgree (probeAt trace episode time) (probeNotes trace episode time) := by
  have bounded : time ≤ last := Nat.le_trans upper (Nat.le_of_lt episode.interval.bounded)
  have projected := probe_projects trace episode maximal quiet lower upper
  intro name
  by_cases selected : name = episode.name
  · subst name
    change (if episode.name = episode.name then [] else (trace.notes time).2 episode.name).map Capture.token = _
    rw [if_pos rfl, probe_saved_closing trace episode time]
    rfl
  · change (if name = episode.name then [] else (trace.notes time).2 name).map Capture.token = _
    rw [if_neg selected, trace.projects time bounded name]
    by_cases hidden : withdraws trace episode time name = true
    · have absent := projected.absent name hidden
      have dormant := projected.dormant name hidden
      cases found : trace.state time name with
      | none => simp [saved, absent, found]
      | some row =>
        have inactive : row.phase = .inactive := by
          cases phase : row.phase <;> simp [ControlFrame.viewAt, found, phase, Phase.committed] at dormant ⊢
        simp [saved, found, absent, inactive, Phase.accumulator]
    · exact (probe_keeps_saved trace episode selected hidden).symm

/-- A withdrawn incarnation cannot take a retained lifecycle step. A
Begin for that same incarnation would contradict its source lifetime. -/
theorem withdrawn_lifecycle_impossible (trace : Trace program last) (episode : ClosedEpisode trace)
    (maximal : ∀ later : ClosedEpisode trace, ¬ EpisodeEdge episode later)
    (quiet : Progress.Quiet (trace.state last))
    {time : Nat} (lower : episode.opened ≤ time) (upper : time ≤ episode.closed)
    {kind : Lifecycle} (event : trace.event time = .lifecycle kind (trace.actor time))
    (withdrawn : withdraws trace episode time (trace.actor time) = true) : False := by
  have bounded := episode.interval.bounded
  obtain ⟨birth, starts, earlier, creator, bornBy, lives⟩ := withdrawn_birth trace episode lower upper withdrawn
  have dormant := child_never_installed trace episode maximal quiet starts earlier creator bornBy (by omega) lives
  have noView (row : F) (found : trace.state time (trace.actor time) = some row) :
      row.phase.committed = none := by
    simpa [ControlFrame.viewAt, found] using dormant
  rcases transition_cases (trace.step time (by omega)).1 with native | ⟨actor, unloadEvent, unload⟩
  · change Labeled.Step program (trace.rule time) (trace.actor time) _ _ at native
    have lifecycle : EpisodeSelection.lifecycle (trace.rule time) = true := by
      cases kind <;> simp [Trace.rule, event, eventRule, Lifecycle.rule, EpisodeSelection.lifecycle]
    generalize rule : trace.rule time = label at native lifecycle
    generalize endpoint : trace.state (time + 1) = after at native
    cases native with
    | insert | retire | remove => simp [EpisodeSelection.lifecycle] at lifecycle
    | begin _ _ row view found _ _ _ =>
      have nextRow : trace.state (time + 1) (trace.actor time) =
          some {row with phase := .reloading row.component.entry [] view} := by
        rw [endpoint, mark_self _ _ _ _ found]
      have age := lives.ordered
      have continues : Residency trace.state (trace.actor time) (birth + 1) (time + 1) := by
        refine ⟨by omega, ?_, lives.boundary⟩
        intro point afterBirth beforeNext absent
        by_cases early : point ≤ time
        · exact lives.present point afterBirth early absent
        · have lastPoint : point = time + 1 := by omega
          rw [lastPoint, nextRow] at absent
          cases absent
      have blocked := child_never_installed trace episode maximal quiet starts earlier creator bornBy (by omega) continues
      simp [ControlFrame.viewAt, nextRow, Phase.committed] at blocked
    | iter _ _ _ row _ _ _ _ _ found phase _ _
    | finish _ _ _ row _ _ _ _ found phase _ _
    | divert _ _ _ row _ _ _ _ found phase _ _
    | leave _ _ row _ _ found phase _
    | unload _ _ row _ _ found phase _ =>
      have invalid := noView row found
      simp [phase, Phase.committed] at invalid
  · have same : trace.actor time = actor := by simp [Trace.actor, unloadEvent, Vestigial.eventActor]
    obtain ⟨row, _, found, phase, _, _⟩ := unload
    have invalid := noView row (same.symm ▸ found)
    simp [phase, Phase.committed] at invalid

end Cordis.Repairs.GuardedHistory
