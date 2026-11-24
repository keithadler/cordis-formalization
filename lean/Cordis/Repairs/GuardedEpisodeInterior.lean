import Cordis.Repairs.GuardedEpisodeCommands
import Cordis.Repairs.GuardedEpisodeOmission
import Cordis.Repairs.GuardedEpisodeOperation
import Cordis.Repairs.GuardedEpisodeUnload
import Cordis.Repairs.GuardedPartialApplications
import Cordis.Repairs.GuardedSuffixTransport

/-! Finite replay of the selected episode's interior. The source and replay
both use the incarnation-aware unload rule. -/
namespace Cordis.Repairs.GuardedHistory
open Calculus Stages IncarnationReplay LegalHistory
open EpisodeAnnotations (NotesRelated notesRelated_self)
open PaperEffectEquations (CoeffectOperations ValueOperationWitness)
open PartialCoeffectIndependenceContracts (tableSetoid)
open PaperObservationEquations (OperationRespects)
open TypedRegistry (encodeProgram RawRegistry RawFiber Scalar)
open Vestigial (CutNotes)
universe u
variable {Name Key Code : Type u} {V : Key → Type u} {ops : CoeffectOperations V}
variable [DecidableEq Name] [DecidableEq Key]
variable {program : Code → TypedRegistry.Instruction Name ops Code} {last : Nat}
local notation "A" => Scalar ops
local notation "R" => RawRegistry Name ops Code
local notation "F" => RawFiber Name ops Code
local notation "I" => Inverse Name Key A
local notation "Ev" => Event Name Key Code
local notation "Notes" => CutNotes Name Key A
local notation "Source" => Trace (encodeProgram program) last

variable (trace : Trace (encodeProgram program) last) (episode : ClosedEpisode trace)
variable (maximal : ∀ later : ClosedEpisode trace, ¬ EpisodeEdge episode later)
variable (quiet : Progress.Quiet (trace.state last))
variable (observe : ∀ key, Setoid (V key))
variable (recovery : ValueOperationWitness ops)
variable (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
variable (respect : ∀ key, OperationRespects ops key (observe key).r)
local notation "Related" => @StageSimulation.Related Name Key A Code _ (TypedCoeffectReplay.setoid observe) Eq
local notation "Paired" => @NotesRelated Name Key A (TypedCoeffectReplay.setoid observe)

include recovery commutative in
private theorem probe_self (time : Nat) (bounded : time ≤ last) :
    Related (probeAt trace episode time) (probeAt trace episode time) := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  exact EpisodeRollback.rollback_self episode.name (trace.notes time).1 ((trace.notes time).2 episode.name)
    (trace.self_related time bounded (TypedRegistry.encoded_program_callbacks ops observe program recovery commutative))

def ProbeStep (time : Nat) : Prop :=
  ∃ next recorded,
    GuardedSuffix.Step (encodeProgram program) (trace.event time) (time + 1)
      (probeAt trace episode time) (probeNotes trace episode time) next recorded ∧
    Related next (probeAt trace episode (time + 1)) ∧ Paired recorded (probeNotes trace episode (time + 1))

include maximal quiet recovery commutative

private theorem exact_probe_step {time : Nat} (lower : episode.opened ≤ time) (upper : time < episode.closed)
    (step : GuardedSuffix.Step (encodeProgram program) (trace.event time) (time + 1)
      (probeAt trace episode time) (probeNotes trace episode time)
      (probeAt trace episode (time + 1)) (probeNotes trace episode (time + 1))) :
    ProbeStep trace episode observe time := by
  have lastBound := episode.interval.bounded
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  have self := probe_self trace episode observe recovery commutative (time + 1) (by omega)
  exact ⟨_, _, step, self, notesRelated_self self _ (probe_projects_notes trace episode maximal quiet (by omega) (by omega))⟩

private theorem replay_activation {time : Nat} (lower : episode.opened ≤ time) (upper : time < episode.closed)
    {kind : Lifecycle} (event : trace.event time = .lifecycle kind (trace.actor time))
    (different : trace.actor time ≠ episode.name)
    (kept : ¬ withdraws trace episode time (trace.actor time) = true)
    {fiber : F} {code : Code} {view : View Name Key} {stack : List I}
    (present : trace.state time (trace.actor time) = some fiber)
    (phase : fiber.phase = .reloading code stack view)
    (target : Target (trace.state time) (trace.actor time) view)
    {middle : R} {next : Option Code} {inverse : I}
    (landed : Land (encodeProgram program) (trace.actor time) code (trace.state time) middle inverse next)
    (label : kind.rule = Transposition.landedRule next)
    (ended : trace.state (time + 1) = mark middle (trace.actor time) (Transposition.landedPhase next inverse stack view)) :
    ProbeStep trace episode observe time := by
  cases landed with
  | unit _ _ _ action =>
    exact exact_probe_step trace episode maximal quiet observe recovery commutative lower upper
      (replay_unit_activation trace episode maximal quiet lower upper event different kept present phase target action label ended)
  | provide _ _ _ provider key value action found declared empty =>
    have same := Option.some.inj (found.symm.trans present)
    exact replay_provision_activation trace episode maximal quiet observe recovery commutative lower upper event different kept
      present phase target action (same ▸ declared) (same ▸ empty) label ended
  | operate _ _ _ key call owner input output inverse outcome action located called =>
    exact replay_operation_activation trace episode maximal quiet observe recovery commutative lower upper event different kept
      present phase target action located called label ended
  | instantiate _ _ _ component child action ready =>
    exact exact_probe_step trace episode maximal quiet observe recovery commutative lower upper
      (replay_allocation_activation trace episode maximal quiet lower upper event different kept present phase target action ready label ended)

private theorem replay_landed_divert {time : Nat} (lower : episode.opened ≤ time) (upper : time < episode.closed)
    (event : trace.event time = .lifecycle .divert (trace.actor time))
    (different : trace.actor time ≠ episode.name)
    (kept : ¬ withdraws trace episode time (trace.actor time) = true)
    {fiber : F} {code : Code} {view : View Name Key} {stack : List I}
    (present : trace.state time (trace.actor time) = some fiber)
    (phase : fiber.phase = .reloading code stack view)
    (stale : ¬ Target (trace.state time) (trace.actor time) view)
    {middle : R} {next : Option Code} {inverse : I}
    (landed : Land (encodeProgram program) (trace.actor time) code (trace.state time) middle inverse next)
    (ended : trace.state (time + 1) = mark middle (trace.actor time) (.unloading (inverse :: stack) view)) :
    ProbeStep trace episode observe time := by
  cases landed with
  | unit _ _ _ action =>
    exact exact_probe_step trace episode maximal quiet observe recovery commutative lower upper
      (replay_unit_divert trace episode maximal quiet lower upper different kept event present phase stale action ended)
  | provide _ _ _ provider key value action found declared empty =>
    have same := Option.some.inj (found.symm.trans present)
    exact replay_provision_divert trace episode maximal quiet observe recovery commutative lower upper event different kept
      present phase stale action (same ▸ declared) (same ▸ empty) ended
  | operate _ _ _ key call owner input output inverse outcome action located called =>
    exact replay_operation_divert trace episode maximal quiet observe recovery commutative lower upper event different kept
      present phase stale action located called ended
  | instantiate _ _ _ component child action ready =>
    exact exact_probe_step trace episode maximal quiet observe recovery commutative lower upper
      (replay_allocation_divert trace episode maximal quiet lower upper event different kept present phase stale action ready ended)

theorem replay_lifecycle_between_probes {time : Nat} (lower : episode.opened ≤ time) (upper : time < episode.closed)
    {kind : Lifecycle} (event : trace.event time = .lifecycle kind (trace.actor time))
    (different : trace.actor time ≠ episode.name)
    (kept : ¬ withdraws trace episode time (trace.actor time) = true) :
    ProbeStep trace episode observe time := by
  have bound : time < last := Nat.lt_trans upper episode.interval.bounded
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  have exactStep := exact_probe_step trace episode maximal quiet observe recovery commutative lower upper
  cases kind with
  | begin => exact exactStep (replay_begin_between_probes trace episode maximal quiet lower upper different kept event)
  | leave => exact exactStep (replay_leave_between_probes trace episode maximal quiet lower upper different kept event)
  | iter =>
    have actual := (trace.step time bound).1
    rw [event] at actual
    change Labeled.Step (encodeProgram program) .iter (trace.actor time) _ _ at actual
    generalize ended : trace.state (time + 1) = after at actual
    cases actual with
    | iter _ _ _ fiber code stack view inverse next present phase target landed =>
      exact replay_activation trace episode maximal quiet observe recovery commutative lower upper
        event different kept present phase target landed rfl ended
  | finish =>
    have actual := (trace.step time bound).1
    rw [event] at actual
    change Labeled.Step (encodeProgram program) .finish (trace.actor time) _ _ at actual
    generalize ended : trace.state (time + 1) = after at actual
    cases actual with
    | finish _ _ _ fiber code stack view inverse present phase target landed =>
      exact replay_activation trace episode maximal quiet observe recovery commutative lower upper
        event different kept present phase target landed rfl ended
  | divert =>
    have actual := (trace.step time bound).1
    rw [event] at actual
    change Labeled.Step (encodeProgram program) .divert (trace.actor time) _ _ at actual
    generalize ended : trace.state (time + 1) = after at actual
    cases actual with
    | divert _ _ _ fiber code stack view tail present phase stale branch =>
      rcases branch with ⟨rfl, rfl⟩ | ⟨inverse, next, landed, rfl⟩
      · exact exactStep (replay_bare_divert_between_probes trace episode maximal quiet lower upper
          different kept event present phase stale ended)
      · exact replay_landed_divert trace episode maximal quiet observe recovery commutative lower upper
          event different kept present phase stale landed ended
  | unload =>
    obtain ⟨after, step, related⟩ := replay_unload_between_probes trace episode observe recovery commutative bound event different kept
    have actual : GuardedSuffix.Step (encodeProgram program) (trace.event time) (time + 1)
        (probeAt trace episode time) (probeNotes trace episode time) after (probeNotes trace episode (time + 1)) := event.symm ▸ step
    have self := probe_self trace episode observe recovery commutative (time + 1) (by omega)
    exact ⟨_, _, actual, related, notesRelated_self self _ (probe_projects_notes trace episode maximal quiet (by omega) (by omega))⟩

omit maximal quiet recovery commutative respect observe in
/-- The interior filter omits the selected actor's lifecycle events and
commands against a withdrawn live incarnation. -/
def keepsInterior (time : Nat) : Bool :=
  match trace.event time with
  | .lifecycle _ actor => decide (actor ≠ episode.name)
  | .command command => !withdraws trace episode time command.actor

private theorem replay_source_event {time : Nat} (lower : episode.opened ≤ time) (upper : time < episode.closed) :
    if keepsInterior trace episode time then
      ProbeStep trace episode observe time ∧
        eventRoots (trace.state time) (trace.event time) = eventRoots (probeAt trace episode time) (trace.event time)
    else probeAt trace episode (time + 1) = probeAt trace episode time ∧
      probeNotes trace episode (time + 1) = probeNotes trace episode time ∧
      eventRoots (trace.state time) (trace.event time) = [] := by
  cases event : trace.event time with
  | command command =>
    by_cases omitted : withdraws trace episode time command.actor = true
    · have moved := probe_omits_withdrawn_command trace episode maximal quiet lower upper command event omitted
      simpa only [keepsInterior, event, omitted, Bool.not_true, Bool.false_eq_true, if_false] using moved
    · have kept := Bool.eq_false_iff.mpr omitted
      have ⟨step, agreed⟩ := replay_command_between_probes trace episode maximal quiet lower upper command event omitted
      have moved := exact_probe_step trace episode maximal quiet observe recovery commutative lower upper step
      simpa only [keepsInterior, event, kept, Bool.not_false, if_true] using And.intro moved agreed
  | lifecycle kind name =>
    have actor : trace.actor time = name := by simp [Trace.actor, event, Vestigial.eventActor]
    have selected : trace.event time = .lifecycle kind (trace.actor time) := by rw [actor]; exact event
    by_cases own : name = episode.name
    · have ⟨same, notes⟩ := probe_omits_selected_step trace episode maximal quiet recovery lower upper (actor.trans own) selected
      simp only [keepsInterior, event, own, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, if_false]
      exact ⟨same, notes, rfl⟩
    · have different := actor ▸ own
      have kept : ¬ withdraws trace episode time (trace.actor time) = true :=
        withdrawn_lifecycle_impossible trace episode maximal quiet lower (Nat.le_of_lt upper) selected
      have moved := replay_lifecycle_between_probes trace episode maximal quiet observe recovery commutative
        lower upper selected different kept
      simp only [keepsInterior, event, decide_eq_true_eq, if_pos own]
      exact ⟨moved, rfl⟩

/-- Every retained interior step has a defined factorization on its
canonical rollback probe. For unload this certifies the complete second
word after the selected episode's rollback and child erasures. -/
theorem retained_probe_factorization {time : Nat} (lower : episode.opened ≤ time) (upper : time < episode.closed)
    (kept : keepsInterior trace episode time = true) :
    ∃ next recorded,
      GuardedSuffix.Step (encodeProgram program) (trace.event time) (time + 1)
        (probeAt trace episode time) (probeNotes trace episode time) next recorded ∧
      GuardedPartialApplications.Factored (TypedReplayContracts.coeffects ops observe program recovery commutative)
        (probeNotes trace episode time) (trace.event time) (probeAt trace episode time) next ∧
      Related next (probeAt trace episode (time + 1)) ∧ Paired recorded (probeNotes trace episode (time + 1)) ∧
      eventRoots (trace.state time) (trace.event time) = eventRoots (probeAt trace episode time) (trace.event time) := by
  have candidate := replay_source_event trace episode maximal quiet observe recovery commutative lower upper
  rw [if_pos kept] at candidate
  obtain ⟨⟨next, recorded, step, endpoints, notes⟩, roots⟩ := candidate
  refine ⟨next, recorded, step, GuardedPartialApplications.transition_factorization _ step.1 ?_, endpoints, notes, roots⟩
  intro actor event
  have different : actor ≠ episode.name := by
    intro same
    simp [keepsInterior, event, same] at kept
  exact probe_foreign_word_defined trace episode maximal quiet _ lower (Nat.le_of_lt upper) different

omit recovery commutative in
private theorem retained_actor_source {time : Nat} (lower : episode.opened ≤ time) (upper : time < episode.closed)
    (kept : keepsInterior trace episode time = true) :
    GuardedSuffix.actorSource (probeAt trace episode time) (probeNotes trace episode time) (trace.event time) =
      GuardedSuffix.actorSource (trace.state time) (trace.notes time) (trace.event time) := by
  have visible : ¬ withdraws trace episode time (trace.actor time) = true := by
    cases event : trace.event time with
    | command command =>
      intro omitted
      simp [Trace.actor, event, Vestigial.eventActor] at omitted
      simp [keepsInterior, event, omitted] at kept
    | lifecycle kind name =>
      have actor : trace.actor time = name := by simp [Trace.actor, event, Vestigial.eventActor]
      exact withdrawn_lifecycle_impossible trace episode maximal quiet lower (Nat.le_of_lt upper) (actor ▸ event)
  change ((probeNotes trace episode time).1 (trace.actor time),
    (probeAt trace episode time (trace.actor time)).map Fiber.component) = _
  apply Prod.ext
  · exact if_neg visible
  · have fields := (probe_projects trace episode maximal quiet lower (Nat.le_of_lt upper)).kept _ visible
    change (probeAt trace episode time (trace.actor time)).map Fiber.component =
      (trace.state time (trace.actor time)).map Fiber.component
    cases found : trace.state time (trace.actor time) <;>
      cases moved : probeAt trace episode time (trace.actor time) <;>
      simp only [found, moved, Iterators.OptionRel, Option.map_none, Option.map_some] at fields ⊢
    exact congrArg some fields.component.symm

include respect in
private theorem replay_interval
    (start length : Nat) (lower : episode.opened ≤ start) (upper : start + length ≤ episode.closed)
    {before : R} {notes : Notes} (source : Related before (probeAt trace episode start))
    (annotated : Paired notes (probeNotes trace episode start)) (projects : GuardedSuffix.SavedWordsAgree before notes) :
    let cuts := List.range' start length
    let kept := cuts.filter (keepsInterior trace episode)
    let roots := cuts.flatMap fun time => eventRoots (trace.state time) (trace.event time)
    ∃ after recorded,
      GuardedSuffix.ExecWith (encodeProgram program) trace.sourceAt (kept.map fun time => (time + 1, trace.event time))
        before notes after recorded roots ∧
      Related after (probeAt trace episode (start + length)) ∧
      Paired recorded (probeNotes trace episode (start + length)) ∧ GuardedSuffix.SavedWordsAgree after recorded := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  dsimp only
  induction length generalizing start before notes with
  | zero => exact ⟨before, notes, .nil _ _, source, annotated, projects⟩
  | succ length ih =>
    have inside : start < episode.closed := by omega
    have endIndex : start + 1 + length = start + (length + 1) := by omega
    simp only [List.range'_succ, List.flatMap_cons]
    by_cases kept : keepsInterior trace episode start = true
    · obtain ⟨localAfter, localNotes, localStep, _, endpoint, recorded, rootsAgree⟩ :=
        retained_probe_factorization trace episode maximal quiet observe recovery commutative lower inside kept
      obtain ⟨middle, middleNotes, step, moved, paired, nextProjects, rootsStay⟩ :=
        GuardedSuffix.transport_step observe program respect localStep (source.symm (fun _ _ h => h.symm)) annotated.symm projects
      have next : Related middle (probeAt trace episode (start + 1)) :=
        StageSimulation.Related.trans (Q := Eq) (fun first second => first.trans second)
          (moved.symm (fun _ _ h => h.symm)) endpoint
      have nextNotes : Paired middleNotes (probeNotes trace episode (start + 1)) :=
        paired.symm.trans recorded
      obtain ⟨after, notes, rest, compared, stamped, finalProjects⟩ :=
        ih (start + 1) (by omega) (by omega) next nextNotes nextProjects
      rw [List.filter_cons_of_pos kept, List.map_cons, rootsAgree, rootsStay]
      refine ⟨after, notes, .cons step rest ?_, endIndex ▸ compared, endIndex ▸ stamped, finalProjects⟩
      rw [GuardedSuffix.CheckedSource, trace.sourceAt_succ]
      exact (GuardedSuffix.actorSource_related observe _ source annotated).trans
        (retained_actor_source trace episode maximal quiet lower inside kept)
    · have candidate := replay_source_event trace episode maximal quiet observe recovery commutative lower inside
      rw [if_neg kept] at candidate
      obtain ⟨same, notesStay, noRoot⟩ := candidate
      obtain ⟨after, notes, rest, compared, stamped, finalProjects⟩ :=
        ih (start + 1) (by omega) (by omega) (same.symm ▸ source) (notesStay.symm ▸ annotated) projects
      rw [List.filter_cons_of_neg kept, noRoot, List.nil_append]
      exact ⟨after, notes, rest, endIndex ▸ compared, endIndex ▸ stamped, finalProjects⟩

include respect in
theorem replay_interior_from_opening :
    let cuts := List.range' episode.opened (episode.closed - episode.opened)
    let kept := cuts.filter (keepsInterior trace episode)
    let roots := cuts.flatMap fun time => eventRoots (trace.state time) (trace.event time)
    ∃ after recorded,
      GuardedSuffix.ExecWith (encodeProgram program) trace.sourceAt (kept.map fun time => (time + 1, trace.event time))
        (trace.state (episode.opened - 1)) (trace.notes (episode.opened - 1)) after recorded roots ∧
      Related after (probeAt trace episode episode.closed) ∧
      Paired recorded (probeNotes trace episode episode.closed) ∧ GuardedSuffix.SavedWordsAgree after recorded := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  have ordered := episode.interval.ordered
  have bounded := episode.interval.bounded
  have first := probe_self trace episode observe recovery commutative episode.opened (by omega)
  have projects := probe_projects_notes trace episode maximal quiet (Nat.le_refl _) ordered
  have annotated := notesRelated_self first (probeNotes trace episode episode.opened) projects
  have full := replay_interval trace episode maximal quiet observe recovery commutative respect
    episode.opened (episode.closed - episode.opened) (Nat.le_refl _) (by omega) first annotated projects
  rw [show episode.opened + (episode.closed - episode.opened) = episode.closed by omega,
    probe_at_opening trace episode, probe_notes_at_opening trace episode] at full
  exact full

end Cordis.Repairs.GuardedHistory
