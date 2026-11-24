import Cordis.Repairs.EpisodeAnnotations
import Cordis.Repairs.EpisodeOmission
import Cordis.Repairs.EpisodeOperationReplay
import Cordis.Repairs.EpisodeUnload
import Cordis.Repairs.ExchangeReplay

/-! Each actual lifecycle event strictly inside the selected episode is
either omitted with an exact stutter or replayed at its original rule and
actor. Retained external commands use the same probe invariant. -/
namespace Cordis.Repairs.EpisodeInterior
open Calculus Stages Indexed IncarnationReplay
open EpisodeDependencies EpisodeRollback EpisodeOperationReplay EpisodeOmission EpisodeUnload
open EpisodeAnnotations
open PaperEffectEquations (CoeffectOperations ValueOperationWitness)
open PartialCoeffectIndependenceContracts (tableSetoid)
open TypedRegistry (encodeProgram RawRegistry RawFiber Scalar)
open LegalHistory (Event RootExec eventRoots)
open Vestigial (CutNotes cutNotes noteStep recordSuffix)
universe u
variable {Name Key Code : Type u} {V : Key → Type u} {ops : CoeffectOperations V}
variable [DecidableEq Name] [DecidableEq Key]
variable {program : Code → TypedRegistry.Instruction Name ops Code} {last : Nat}
local notation "A" => Scalar ops
local notation "R" => RawRegistry Name ops Code
local notation "F" => RawFiber Name ops Code
local notation "Ev" => Event Name Key Code
local notation "Notes" => CutNotes Name Key A
variable (trace : Trace (encodeProgram program) (fun _ => none : RawRegistry Name ops Code) last)
variable (episode : ClosedEpisode trace)
variable (maximal : ∀ later : ClosedEpisode trace, ¬ EpisodeEdge episode later)
variable (quiet : Progress.Quiet (trace.state last))
variable (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
variable (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
local notation "Related" => @StageSimulation.Related Name Key A Code _
  (TypedCoeffectReplay.setoid observe) Eq
local notation "NotesMatch" => @NotesRelated Name Key A (TypedCoeffectReplay.setoid observe)

include recovery commutative in
private theorem probe_self (time : Nat) (bounded : time ≤ last) :
    Related (probeAt trace episode time) (probeAt trace episode time) := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  exact rollbackOf_self trace episode time (Transposition.reachable_self_related (encodeProgram program)
    (TypedRegistry.encoded_program_callbacks ops observe program recovery commutative) (trace.prefixRun time bounded))

include maximal quiet recovery commutative

private theorem replay_activation (time : Nat) (lower : episode.opened ≤ time) (upper : time < episode.closed)
    (different : trace.actor time ≠ episode.name)
    (kept : ¬ withdraws trace episode time (trace.actor time) = true)
    {fiber : F} {code : Code} {view : View Name Key} {stack : List (Inverse Name Key A)}
    (present : trace.state time (trace.actor time) = some fiber)
    (phase : fiber.phase = .reloading code stack view)
    (target : Target (trace.state time) (trace.actor time) view)
    {middle : R} {next : Option Code} {inverse : Inverse Name Key A}
    (landed : Land (encodeProgram program) (trace.actor time) code (trace.state time) middle inverse next)
    (ended : trace.state (time + 1) = mark middle (trace.actor time) (Transposition.landedPhase next inverse stack view)) :
    ∃ after, Labeled.Step (encodeProgram program) (Transposition.landedRule next) (trace.actor time)
      (probeAt trace episode time) after ∧ Related after (probeAt trace episode (time + 1)) := by
  have bound := episode.interval.bounded
  have self := probe_self trace episode observe recovery commutative (time + 1) (by omega)
  have cutoff := Nat.le_of_lt upper
  cases landed with
  | unit _ _ _ action =>
    exact ⟨_, replay_unit_activation trace episode maximal quiet lower cutoff different kept present phase target action ended, self⟩
  | provide _ _ _ provider key value action found declared empty =>
    exact replay_provision_activation trace episode maximal quiet observe recovery commutative lower cutoff different kept
      present phase target action (by simpa [Option.some.inj (found.symm.trans present)] using declared)
      (by simpa [Option.some.inj (found.symm.trans present)] using empty) ended
  | operate _ _ _ key call owner input output inverse outcome action located called =>
    exact replay_operation_activation trace episode maximal quiet observe recovery commutative lower cutoff different kept
      present phase target action located called ended
  | instantiate _ _ _ component child action ready =>
    exact ⟨_, replay_allocation_activation trace episode maximal quiet lower cutoff different kept present phase target action ready ended, self⟩

private theorem replay_landed_divert (time : Nat) (lower : episode.opened ≤ time) (upper : time < episode.closed)
    (different : trace.actor time ≠ episode.name)
    (kept : ¬ withdraws trace episode time (trace.actor time) = true)
    {fiber : F} {code : Code} {view : View Name Key} {stack : List (Inverse Name Key A)}
    (present : trace.state time (trace.actor time) = some fiber)
    (phase : fiber.phase = .reloading code stack view)
    (stale : ¬ Target (trace.state time) (trace.actor time) view)
    {middle : R} {next : Option Code} {inverse : Inverse Name Key A}
    (landed : Land (encodeProgram program) (trace.actor time) code (trace.state time) middle inverse next)
    (ended : trace.state (time + 1) = mark middle (trace.actor time) (.unloading (inverse :: stack) view)) :
    ∃ after, Labeled.Step (encodeProgram program) .divert (trace.actor time)
      (probeAt trace episode time) after ∧ Related after (probeAt trace episode (time + 1)) := by
  have bound := episode.interval.bounded
  have self := probe_self trace episode observe recovery commutative (time + 1) (by omega)
  have cutoff := Nat.le_of_lt upper
  cases landed with
  | unit _ _ _ action =>
    exact ⟨_, replay_unit_divert trace episode maximal quiet lower cutoff different kept present phase stale action ended, self⟩
  | provide _ _ _ provider key value action found declared empty =>
    exact replay_provision_divert trace episode maximal quiet observe recovery commutative lower cutoff different kept
      present phase stale action (by simpa [Option.some.inj (found.symm.trans present)] using declared)
      (by simpa [Option.some.inj (found.symm.trans present)] using empty) ended
  | operate _ _ _ key call owner input output inverse outcome action located called =>
    exact replay_operation_divert trace episode maximal quiet observe recovery commutative lower cutoff different kept
      present phase stale action located called ended
  | instantiate _ _ _ component child action ready =>
    exact ⟨_, replay_allocation_divert trace episode maximal quiet lower cutoff different kept present phase stale action ready ended, self⟩

/-- Every retained lifecycle label is replayable from its rollback probe.
The rule's actual landing, when present, determines the paired step. -/
theorem replay_lifecycle_between_probes {time : Nat} (lower : episode.opened ≤ time) (upper : time < episode.closed)
    (different : trace.actor time ≠ episode.name)
    (kept : ¬ withdraws trace episode time (trace.actor time) = true)
    (lifecycle : EpisodeSelection.lifecycle (trace.rule time) = true) :
    ∃ after, Labeled.Step (encodeProgram program) (trace.rule time) (trace.actor time)
      (probeAt trace episode time) after ∧ Related after (probeAt trace episode (time + 1)) := by
  have bound := episode.interval.bounded
  have actual := trace.step time (by omega)
  have self := probe_self trace episode observe recovery commutative (time + 1) (by omega)
  have cutoff := Nat.le_of_lt upper
  generalize rule : trace.rule time = selected at actual lifecycle ⊢
  generalize ended : trace.state (time + 1) = after at actual
  cases actual with
  | insert | retire | remove => simp [EpisodeSelection.lifecycle] at lifecycle
  | begin => exact ⟨_, replay_begin_between_probes trace episode maximal quiet lower upper different kept rule, self⟩
  | iter _ _ _ fiber code stack view inverse next present phase target landed =>
    exact replay_activation trace episode maximal quiet observe recovery commutative time lower upper different kept
      present phase target landed ended
  | finish _ _ _ fiber code stack view inverse present phase target landed =>
    exact replay_activation trace episode maximal quiet observe recovery commutative time lower upper different kept
      present phase target landed ended
  | divert _ _ _ fiber code stack view tail present phase stale branch =>
    rcases branch with ⟨rfl, rfl⟩ | ⟨inverse, next, landed, rfl⟩
    · exact ⟨_, replay_bare_divert_between_probes trace episode maximal quiet lower cutoff different kept
        present phase stale ended, self⟩
    · exact replay_landed_divert trace episode maximal quiet observe recovery commutative time lower upper different kept
        present phase stale landed ended
  | leave => exact ⟨_, replay_leave_between_probes trace episode maximal quiet lower cutoff different kept rule, self⟩
  | unload =>
    exact replay_unload_between_probes trace episode maximal quiet observe recovery commutative
      lower cutoff different kept rule

omit maximal quiet recovery commutative in
/-- An actual event at an indexed cut, including the component payload
of an external insertion and the original lifecycle label. -/
def SourceEvent (time : Nat) (event : Ev) : Prop :=
  event.Step (encodeProgram program) (trace.state time) (trace.state (time + 1)) ∧
    match event with
    | .command command => ExchangeReplay.commandRule command = trace.rule time ∧ command.actor = trace.actor time
    | .lifecycle kind actor => kind.rule = trace.rule time ∧ actor = trace.actor time

omit maximal quiet recovery commutative in
private theorem source_event_labels {time : Nat} {event : Ev} (actual : SourceEvent trace time event)
    {before after : R} (moved : event.Step (encodeProgram program) before after) :
    Labeled.Step (encodeProgram program) (trace.rule time) (trace.actor time) before after := by
  cases event with
  | command command =>
    obtain ⟨_, rule, actor⟩ := actual
    simpa only [rule, actor] using ExchangeReplay.command_labeled command moved
  | lifecycle kind name =>
    obtain ⟨_, rule, actor⟩ := actual
    simpa only [Event.Step, rule, actor] using moved

omit maximal quiet recovery commutative in
theorem source_event_exists (roots : PaperLifecycleClaims.RootInsertions trace) (time : Nat) (bounded : time < last) :
    ∃ event, SourceEvent trace time event := by
  have actual := trace.step time bounded
  cases rule : trace.rule time with
  | insert =>
    rw [rule] at actual
    generalize ended : trace.state (time + 1) = after at actual
    cases actual with
    | insert _ _ component parent ready =>
      obtain ⟨row, found, root⟩ := roots time bounded rule
      rw [ended, put_self] at found
      have newParent := congrArg Fiber.parent (Option.some.inj found)
      have rootParent : parent = none := newParent.trans root
      subst parent
      exact ⟨.command (.insert (trace.actor time) component), ⟨ready, ended⟩, rule.symm, rfl⟩
  | retire =>
    rw [rule] at actual
    generalize ended : trace.state (time + 1) = after at actual
    cases actual with
    | retire _ _ present => exact ⟨.command (.retire (trace.actor time)), ⟨present, ended⟩, rule.symm, rfl⟩
  | remove =>
    rw [rule] at actual
    generalize ended : trace.state (time + 1) = after at actual
    cases actual with
    | remove _ _ ready => exact ⟨.command (.remove (trace.actor time)), ⟨ready, ended⟩, rule.symm, rfl⟩
  | begin => exact ⟨.lifecycle .begin (trace.actor time), by simpa only [Event.Step, LegalHistory.Lifecycle.rule, rule] using actual, rule.symm, rfl⟩
  | iter => exact ⟨.lifecycle .iter (trace.actor time), by simpa only [Event.Step, LegalHistory.Lifecycle.rule, rule] using actual, rule.symm, rfl⟩
  | finish => exact ⟨.lifecycle .finish (trace.actor time), by simpa only [Event.Step, LegalHistory.Lifecycle.rule, rule] using actual, rule.symm, rfl⟩
  | divert => exact ⟨.lifecycle .divert (trace.actor time), by simpa only [Event.Step, LegalHistory.Lifecycle.rule, rule] using actual, rule.symm, rfl⟩
  | leave => exact ⟨.lifecycle .leave (trace.actor time), by simpa only [Event.Step, LegalHistory.Lifecycle.rule, rule] using actual, rule.symm, rfl⟩
  | unload => exact ⟨.lifecycle .unload (trace.actor time), by simpa only [Event.Step, LegalHistory.Lifecycle.rule, rule] using actual, rule.symm, rfl⟩

variable (respect : ∀ key, PaperObservationEquations.OperationRespects ops key (observe key).r)

include respect in
private theorem replay_source_event {time : Nat} (lower : episode.opened ≤ time) (upper : time < episode.closed)
    {event : Ev} (actual : SourceEvent trace time event)
    {before : R} (source : Related before (probeAt trace episode time)) :
    if EpisodeSelection.keeps trace episode.name episode.opened episode.closed time then
      ∃ after, event.Step (encodeProgram program) before after ∧ Related after (probeAt trace episode (time + 1)) ∧
        eventRoots (trace.state time) event = eventRoots before event
    else probeAt trace episode (time + 1) = probeAt trace episode time ∧ eventRoots (trace.state time) event = [] := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  have cutoff := Nat.le_of_lt upper
  have mask := withdrawn_eq_mask trace episode lower cutoff
  cases event with
  | command command =>
    obtain ⟨step, label, actor⟩ := actual
    have kind : EpisodeSelection.lifecycle (trace.rule time) = false := by
      rw [← label]
      cases command <;> rfl
    by_cases kept : withdraws trace episode time command.actor = true
    · have omitted := probe_omits_withdrawn_command trace episode maximal quiet lower cutoff command actor kept step
      have deleted : EpisodeSelection.keeps trace episode.name episode.opened episode.closed time = false := by
        simp [EpisodeSelection.keeps, mask, ← actor, kept]
      simpa only [deleted, Bool.false_eq_true, if_false, eventRoots] using omitted
    · have moved := replay_command_from_related_probe trace episode maximal quiet lower cutoff command actor kept step source
      have retained : EpisodeSelection.keeps trace episode.name episode.opened episode.closed time = true := by
        simp [EpisodeSelection.keeps, mask, kind, ← actor, Bool.eq_false_iff.mpr kept]
      simpa only [retained, if_true, eventRoots] using Exists.intro (command.apply before) moved
  | lifecycle kind actor =>
    obtain ⟨_, label, rfl⟩ := actual
    have life : EpisodeSelection.lifecycle (trace.rule time) = true := by
      rw [← label]
      cases kind <;> rfl
    by_cases selected : trace.actor time = episode.name
    · have same := probe_omits_selected_step trace episode recovery lower upper selected life
      have opening : episode.opened - 1 ≤ time := by omega
      have deleted : EpisodeSelection.keeps trace episode.name episode.opened episode.closed time = false := by
        simp [EpisodeSelection.keeps, life, selected, opening, cutoff]
      simp only [deleted, Bool.false_eq_true, if_false]
      exact ⟨same, rfl⟩
    · have kept : ¬ withdraws trace episode time (trace.actor time) = true := by
        intro withdrawn
        have impossible := withdrawn_has_no_lifecycle trace episode maximal quiet lower cutoff withdrawn
        rw [life] at impossible
        cases impossible
      have retained : EpisodeSelection.keeps trace episode.name episode.opened episode.closed time = true := by
        simp [EpisodeSelection.keeps, mask, selected, Bool.eq_false_iff.mpr kept]
      obtain ⟨canonical, step, related⟩ := replay_lifecycle_between_probes trace episode maximal quiet observe recovery
        commutative lower upper selected kept life
      obtain ⟨after, native, endpoint⟩ := replay_from_related_probe trace episode observe respect source step related
      rw [retained, if_pos rfl]
      exact ⟨after, by simpa only [Event.Step, label] using native, endpoint, rfl⟩

include respect in
private theorem replay_interval (events : Nat → Ev)
    (actual : ∀ time, time < last → SourceEvent trace time (events time))
    (start length : Nat) (lower : episode.opened ≤ start) (upper : start + length ≤ episode.closed)
    {before : R} (source : Related before (probeAt trace episode start))
    (notes : Notes) (annotated : NotesMatch notes (probeNotes trace episode start)) :
    let kept := (List.range' start length).filter (EpisodeSelection.keeps trace episode.name episode.opened episode.closed)
    ∃ after, RootExec (encodeProgram program)
      (kept.map events)
      before after ((List.range' start length).flatMap fun time => eventRoots (trace.state time) (events time)) ∧
      Related after (probeAt trace episode (start + length)) ∧
      ∃ moved : Trace (encodeProgram program) before kept.length,
        moved.state kept.length = after ∧
        (∀ index old, kept[index]? = some old →
          moved.rule index = trace.rule old ∧ moved.actor index = trace.actor old ∧
          (events old).Step (encodeProgram program) (moved.state index) (moved.state (index + 1))) ∧
        NotesMatch (recordSuffix moved.state moved.actor 0 kept notes) (probeNotes trace episode (start + length)) := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  dsimp only
  induction length generalizing start before notes with
  | zero =>
    refine ⟨before, .nil before, source, ⟨fun _ => before, trace.rule, trace.actor, rfl, ?_⟩, rfl, ?_, annotated⟩
    · intro _ impossible
      exact False.elim (Nat.not_lt_zero _ impossible)
    · intro _ _ impossible
      cases impossible
  | succ length ih =>
    have bounded := episode.interval.bounded
    have event := actual start (by omega)
    have interior : start < episode.closed := by omega
    have move := replay_source_event trace episode maximal quiet observe recovery commutative respect lower interior event source
    have endIndex : start + 1 + length = start + (length + 1) := by omega
    simp only [List.range'_succ, List.flatMap_cons]
    by_cases kept : EpisodeSelection.keeps trace episode.name episode.opened episode.closed start = true
    · rw [if_pos kept] at move
      obtain ⟨middle, moved, middleRelated, roots⟩ := move
      have stepped := source_event_labels trace event moved
      let nextNotes := noteStep before middle (trace.actor start) (start + 1) notes
      have paired : NotesMatch nextNotes (probeNotes trace episode (start + 1)) := by
        rw [← probeNotes_step trace episode maximal quiet lower interior]
        exact noteStep_related source middleRelated (trace.actor start) (start + 1) annotated
      obtain ⟨final, rest, endpoint, suffix, finish, labels, recorded⟩ :=
        ih (start + 1) (by omega) (by omega) middleRelated nextNotes paired
      rw [List.filter_cons_of_pos kept, List.map_cons, roots]
      refine ⟨final, .cons moved rest, endIndex ▸ endpoint, Vestigial.prepend stepped suffix, finish, ?_, ?_⟩
      · intro index old tagged
        cases index with
        | zero =>
          change some start = some old at tagged
          cases tagged
          exact ⟨rfl, rfl, by simpa only [Vestigial.prepend, suffix.start] using moved⟩
        | succ index => exact labels index old tagged
      · rw [recordSuffix, Vestigial.record_shift]
        change NotesMatch (recordSuffix suffix.state suffix.actor 0 _
          (noteStep before (suffix.state 0) (trace.actor start) (start + 1) notes)) _
        rw [suffix.start]
        exact endIndex ▸ recorded
    · rw [if_neg kept] at move
      have same := probeNotes_stutter trace episode maximal quiet lower interior move.1
      obtain ⟨final, rest, endpoint, suffix, finish, labels, recorded⟩ := ih (start + 1) (by omega) (by omega)
        (move.1.symm ▸ source) notes (same.symm ▸ annotated)
      rw [List.filter_cons_of_neg kept, move.2, List.nil_append]
      exact ⟨final, rest, endIndex ▸ endpoint, suffix, finish, labels, endIndex ▸ recorded⟩

include respect in
/-- Replay all retained events between the omitted Begin and its closing
Unload. The actual indexed trace determines the full external payloads,
and the replay keeps precisely the filter's subsequence and all its roots. -/
theorem replay_interior_from_opening (rootInsertions : PaperLifecycleClaims.RootInsertions trace) :
    let cuts := List.range' episode.opened (episode.closed - episode.opened)
    let kept := cuts.filter (EpisodeSelection.keeps trace episode.name episode.opened episode.closed)
    ∃ (events : Nat → Ev) (after : R),
      (∀ time, time < last → SourceEvent trace time (events time)) ∧
      RootExec (encodeProgram program) (kept.map events)
        (trace.state (episode.opened - 1)) after (cuts.flatMap fun time => eventRoots (trace.state time) (events time)) ∧
      Related after (probeAt trace episode episode.closed) ∧
      ∃ moved : Trace (encodeProgram program) (trace.state (episode.opened - 1)) kept.length,
        moved.state kept.length = after ∧
        (∀ index old, kept[index]? = some old →
          moved.rule index = trace.rule old ∧ moved.actor index = trace.actor old ∧
          (events old).Step (encodeProgram program) (moved.state index) (moved.state (index + 1))) ∧
        NotesMatch (recordSuffix moved.state moved.actor 0 kept (cutNotes trace.state trace.actor (episode.opened - 1)))
          (probeNotes trace episode episode.closed) ∧
        (∀ name, ((recordSuffix moved.state moved.actor 0 kept
          (cutNotes trace.state trace.actor (episode.opened - 1))).2 name).map Capture.token =
          PartialReplayRegistry.saved after name) := by
  classical
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  let events (time : Nat) : Ev := if bound : time < last then
    Classical.choose (source_event_exists trace rootInsertions time bound) else .lifecycle .begin (trace.actor time)
  have actual (time : Nat) (bounded : time < last) : SourceEvent trace time (events time) := by
    simp only [events, dif_pos bounded]
    exact Classical.choose_spec (source_event_exists trace rootInsertions time bounded)
  have ordered := episode.interval.ordered
  have bounded := episode.interval.bounded
  have entry : Related (trace.state (episode.opened - 1)) (probeAt trace episode episode.opened) := by
    rw [← probe_at_opening trace episode]
    exact probe_self trace episode observe recovery commutative episode.opened (by omega)
  have annotated : NotesMatch (cutNotes trace.state trace.actor (episode.opened - 1)) (probeNotes trace episode episode.opened) := by
    rw [← probeNotes_at_opening trace episode]
    exact notesRelated_self (probe_self trace episode observe recovery commutative episode.opened (by omega)) _
      (probeNotes_projects trace episode maximal quiet (Nat.le_refl _) ordered)
  have endIndex : episode.opened + (episode.closed - episode.opened) = episode.closed := by omega
  obtain ⟨after, run, endpoint, moved, finish, labels, recorded⟩ := replay_interval trace episode maximal quiet observe
    recovery commutative respect events actual episode.opened (episode.closed - episode.opened) (Nat.le_refl _) (by omega)
    entry _ annotated
  rw [endIndex] at endpoint recorded
  refine ⟨events, after, actual, run, endpoint, moved, finish, labels, recorded, ?_⟩
  let kept := (List.range' episode.opened (episode.closed - episode.opened)).filter
    (EpisodeSelection.keeps trace episode.name episode.opened episode.closed)
  have starts (name : Name) : ((cutNotes trace.state trace.actor (episode.opened - 1)).2 name).map Capture.token =
      PartialReplayRegistry.saved (moved.state 0) name := by
    rw [moved.start]
    exact (tracked_stack trace (episode.opened - 1) (by omega)).projects name
  intro name
  have projects := Vestigial.recordSuffix_projects moved 0 kept (by simp [kept]) _ starts name
  change moved.state kept.length = after at finish
  rw [Nat.zero_add, finish] at projects
  exact projects

end Cordis.Repairs.EpisodeInterior
