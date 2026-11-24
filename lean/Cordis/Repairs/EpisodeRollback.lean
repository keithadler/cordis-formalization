import Cordis.Repairs.EpisodeReplayGuards
import Cordis.TranspositionStates

/-! The actual source for every interior deletion probe. Roll back the
selected parent's tracked word, deactivate the parent, and omit precisely
the children whose live births match that word. -/
namespace Cordis.Repairs.EpisodeRollback
open Calculus Stages Indexed Incarnation IncarnationReplay
open EpisodeDependencies EpisodeBoundary EpisodeReplayGuards
open PartialReplayRegistry (saved)
open Iterators (OptionRel)
universe u
variable {Name Key Value Code Error : Type u} [DecidableEq Name] [DecidableEq Key]
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
variable {program : Code → Instruction Name Key Value Code Error} {last : Nat}
local notation "History" => Trace program (fun _ => none : R) last

def withdraws (trace : History) (episode : ClosedEpisode trace) (time : Nat) (name : Name) : Bool :=
  (track trace.state trace.actor time episode.name).any
    (Capture.retires (fun child => birthAt trace.state child time) name)

private theorem vacant_not_withdrawn (trace : History) (episode : ClosedEpisode trace) (time : Nat)
    {name : Name} (vacant : trace.state time name = none) : ¬ withdraws trace episode time name = true := by
  intro withdrawn
  obtain ⟨capture, _, matched⟩ := List.any_eq_true.mp withdrawn
  cases token : capture.token with
  | retire target =>
    have live : name = target ∧ birthAt trace.state target time = some capture.index := by
      simpa [Capture.retires, token] using matched
    rw [← live.1, birthAt_none.mpr vacant] at live
    exact Option.noConfusion live.2
  | _ => simp [Capture.retires, token] at matched

def rollbackOf (trace : History) (episode : ClosedEpisode trace) (time : Nat) (state : R) : R :=
  let reverted := replay (fun name => birthAt trace.state name time)
    (track trace.state trace.actor time episode.name) state
  fun name => if withdraws trace episode time name then none else mark reverted episode.name .inactive name

def probeAt (trace : History) (episode : ClosedEpisode trace) (time : Nat) : R :=
  rollbackOf trace episode time (trace.state time)

/-- Apply a cut's saved word, deactivate its actor, and erase the children
whose live births match that word. -/
def rollback (closing : Name) (live : Name → Option Nat) (word : List (Capture Name Key Value))
    (state : R) : R :=
  fun name => if word.any (Capture.retires live name) then none else mark (replay live word state) closing .inactive name

theorem rollback_tableAt (closing : Name) (live : Name → Option Nat) (word : List (Capture Name Key Value))
    (state : R) (name : Name) (key : Key) :
    StageRecovery.tableAt (rollback closing live word state) name key =
      if word.any (Capture.retires live name) then none else StageRecovery.tableAt (replay live word state) name key := by
  by_cases omitted : word.any (Capture.retires live name) = true
  · simp [rollback, StageRecovery.tableAt, omitted]
  · rw [if_neg omitted]
    change (if word.any (Capture.retires live name) then none else
      mark (replay live word state) closing .inactive name).bind (fun row => row.table key) = _
    rw [if_neg omitted]
    exact StageRecovery.tableAt_mark _ _ _ _ _

theorem rollback_table (trace : History) (episode : ClosedEpisode trace) (time : Nat)
    (state : R) (name : Name) (key : Key) :
    StageRecovery.tableAt (rollbackOf trace episode time state) name key =
      if withdraws trace episode time name then none
      else StageRecovery.tableAt
        (replay (fun child => birthAt trace.state child time) (track trace.state trace.actor time episode.name) state)
        name key :=
  rollback_tableAt episode.name (fun name => birthAt trace.state name time)
    (track trace.state trace.actor time episode.name) state name key

theorem probe_table (trace : History) (episode : ClosedEpisode trace) (time : Nat)
    (name : Name) (key : Key) :
    StageRecovery.tableAt (probeAt trace episode time) name key =
      if withdraws trace episode time name then none
      else StageRecovery.tableAt (replayAt trace.state time (track trace.state trace.actor time episode.name)) name key :=
  rollback_table trace episode time (trace.state time) name key

/-- The same saved word and birth tests preserve control agreement. -/
theorem rollback_controls (closing : Name) (live : Name → Option Nat) (word : List (Capture Name Key Value))
    {left right : R} (controls : Transposition.SameControls left right) :
    Transposition.SameControls (rollback closing live word left) (rollback closing live word right) := by
  intro name
  by_cases omitted : word.any (Capture.retires live name) = true
  · simp [rollback, omitted, OptionRel]
  simp only [rollback, if_neg omitted]
  change OptionRel Transposition.SameFields
    (mark (replay live word left) closing .inactive name)
    (mark (replay live word right) closing .inactive name)
  have fields := controls name
  cases first : left name with
  | none =>
    have second : right name = none := by cases found : right name <;> simp_all [OptionRel]
    have firstReplay := (replay_presence live word left name).mpr first
    have secondReplay := (replay_presence live word right name).mpr second
    by_cases same : name = closing
    · subst name
      simp [mark, Calculus.modify, firstReplay, secondReplay, OptionRel]
    · simp [mark, Calculus.modify, same, firstReplay, secondReplay, OptionRel]
  | some a =>
    cases second : right name with
    | none => simp [first, second, OptionRel] at fields
    | some b =>
      rw [first, second] at fields
      change Transposition.SameFields a b at fields
      obtain ⟨p, atLeft, componentLeft, parentLeft, phaseLeft⟩ := replay_keeps_control live word left name a first
      obtain ⟨q, atRight, componentRight, parentRight, phaseRight⟩ := replay_keeps_control live word right name b second
      have firstFlag := replay_retired live word left name
      have secondFlag := replay_retired live word right name
      rw [atLeft, first] at firstFlag
      rw [atRight, second] at secondFlag
      simp only [Option.map_some] at firstFlag secondFlag
      rw [fields.retired] at firstFlag
      have retired := Option.some.inj (firstFlag.trans secondFlag.symm)
      have updated : Transposition.SameFields p q :=
        ⟨componentLeft.trans (fields.component.trans componentRight.symm),
          parentLeft.trans (fields.parent.trans parentRight.symm), retired,
          phaseLeft.trans (fields.phase.trans phaseRight.symm)⟩
      by_cases same : name = closing
      · simp only [mark, Calculus.modify, if_pos same, atLeft, atRight, Option.map_some, OptionRel]
        exact ⟨updated.component, updated.parent, updated.retired, rfl⟩
      · simpa [mark, Calculus.modify, same, atLeft, atRight, OptionRel] using updated

theorem rollbackOf_controls (trace : History) (episode : ClosedEpisode trace) (time : Nat)
    {left right : R} (controls : Transposition.SameControls left right) :
    Transposition.SameControls (rollbackOf trace episode time left) (rollbackOf trace episode time right) :=
  rollback_controls episode.name (fun name => birthAt trace.state name time)
    (track trace.state trace.actor time episode.name) controls

/-- Discharge preserves the phase and its saved word at each existing row. -/
theorem replay_self_related [Setoid Value] (live : Name → Option Nat) (word : List (Capture Name Key Value))
    {state : R} (self : StageSimulation.Related Eq state state) :
    StageSimulation.Related Eq (replay live word state) (replay live word state) := by
  intro name
  cases found : state name with
  | none => simp [(replay_presence live word state name).mpr found, OptionRel]
  | some row =>
    obtain ⟨after, result, _, _, phase⟩ := replay_keeps_control live word state name row found
    have rowSelf := self name
    rw [found] at rowSelf
    change StageSimulation.FiberRelated Eq row row at rowSelf
    rw [result]
    exact ⟨⟨rfl, rfl, rfl⟩, rfl, rfl, by simpa only [phase] using rowSelf.phase,
      fun key => PartialObservedMapClosure.option_refl (inferInstance : Setoid Value) (after.table key)⟩

/-- A fixed rollback preserves self-relatedness at every surviving word. -/
theorem rollback_self [Setoid Value] (closing : Name) (live : Name → Option Nat)
    (word : List (Capture Name Key Value)) {state : R} (self : StageSimulation.Related Eq state state) :
    StageSimulation.Related Eq (rollback closing live word state) (rollback closing live word state) := by
  have marked := StageSimulation.mark_related (replay_self_related live word self) closing .inactive
  intro name
  by_cases omitted : word.any (Capture.retires live name) = true
  · simp [rollback, omitted, OptionRel]
  · simpa only [rollback, if_neg omitted] using marked name

theorem rollbackOf_self [Setoid Value] (trace : History) (episode : ClosedEpisode trace) (time : Nat)
    {state : R} (self : StageSimulation.Related Eq state state) :
    StageSimulation.Related Eq (rollbackOf trace episode time state) (rollbackOf trace episode time state) :=
  rollback_self episode.name (fun name => birthAt trace.state name time)
    (track trace.state trace.actor time episode.name) self

theorem empty_on_entry (trace : History) (episode : ClosedEpisode trace) :
    track trace.state trace.actor episode.opened episode.name = [] := by
  have project := (tracked_stack trace episode.opened
    (by have := episode.interval.bounded; have := episode.interval.ordered; omega)).projects episode.name
  obtain ⟨row, view, found, _, _, _, begins⟩ := begin_boundary trace episode.interval
  have empty : saved (trace.state episode.opened) episode.name = [] := by
    rw [begins, saved, mark_self _ _ _ _ found]
    rfl
  exact List.map_eq_nil_iff.mp (project.trans empty)

/-- A matching live retirement in the current word belongs to this
episode. Its source index, creator, and rule are read from the trace. -/
theorem withdrawn_birth (trace : History) (episode : ClosedEpisode trace)
    {time : Nat} (lower : episode.opened ≤ time) (upper : time ≤ episode.closed)
    {child : Name} (withdrawn : withdraws trace episode time child = true) :
    ∃ birthStep, episode.opened ≤ birthStep ∧ birthStep < episode.closed ∧
      trace.actor birthStep = episode.name ∧ EpisodeSelection.canBirth (trace.rule birthStep) = true ∧
      Residency trace.state child (birthStep + 1) time := by
  have lastBound := episode.interval.bounded
  obtain ⟨capture, recorded, matchesBirth⟩ := List.any_eq_true.mp withdrawn
  cases selected : capture.token with
  | retire childName =>
    have matching : child = childName ∧ birthAt trace.state childName time = some capture.index := by
      simpa [Capture.retires, selected] using matchesBirth
    obtain ⟨rfl, current⟩ := matching
    have age := capture_after_empty trace.state trace.actor episode.name lower (empty_on_entry trace episode) recorded
    have ⟨captureBound, origin⟩ := (tracked_stack trace time (by omega)).origins episode.name capture recorded
    obtain ⟨birthStep, inRange, stamp, creator, _, _, _, _, _, _⟩ := origin
    have starts : episode.opened ≤ birthStep := by omega
    have residency : Residency trace.state child (birthStep + 1) time :=
      resident_of_birthAt (current.trans (congrArg some stamp))
    have vacant : trace.state birthStep child = none := by
      simpa using residency.boundary.resolve_left (by omega)
    have born := residency.present (birthStep + 1) (Nat.le_refl _) residency.ordered
    have steps := trace.step birthStep inRange
    have birthRule : EpisodeSelection.canBirth (trace.rule birthStep) = true := by
      rcases new_entry_rule steps vacant born with ⟨_, same⟩ | native
      · have missing : trace.state birthStep episode.name = none := (same.trans creator) ▸ vacant
        exact False.elim (episode.interval.installed birthStep starts (by omega)
          (by simp [ControlFrame.viewAt, missing]))
      · exact native
    exact ⟨birthStep, starts, by omega, creator, birthRule, residency⟩
  | _ => simp [Capture.retires, selected] at matchesBirth

/-- At every interior cut, the episode deletion filter and the replay mask
select the same actual incarnation. The filter's birth test supplies the
captured token, and a matching token supplies the filter's birth test. -/
theorem withdrawn_eq_mask (trace : History) (episode : ClosedEpisode trace)
    {time : Nat} (lower : episode.opened ≤ time) (upper : time ≤ episode.closed) :
    EpisodeSelection.withdrawn trace episode.name episode.opened episode.closed time =
      withdraws trace episode time (trace.actor time) := by
  have bounded := episode.interval.bounded
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro selected
    obtain ⟨birth, positive, starts, _, creator, birthRule, vacant, lives, _, _, _⟩ :=
      EpisodeSelection.withdrawn_birth trace episode.name episode.opened episode.closed time selected
    have after : birth - 1 + 1 = birth := by omega
    have born := lives.present birth (Nat.le_refl _) lives.ordered
    have earlier : birth - 1 < time := by have := lives.ordered; omega
    have recorded := birth_capture_at_cut trace episode starts earlier upper creator birthRule vacant (after ▸ born)
    have current := birthAt_eq_some.mpr lives
    apply List.any_eq_true.mpr
    exact ⟨_, recorded, by simp [Capture.retires, current, after]⟩
  · intro masked
    obtain ⟨step, starts, earlier, creator, birthRule, lives⟩ := withdrawn_birth trace episode lower upper masked
    have vacant : trace.state step (trace.actor time) = none := by simpa using lives.boundary.resolve_left (by omega)
    have born := lives.present (step + 1) (Nat.le_refl _) lives.ordered
    have creation := (EpisodeSelection.actual_child_birth (trace.step step (by omega)) birthRule vacant born).1
    rw [creator] at creation
    obtain ⟨component, start⟩ := born_row vacant creation
    have current := birthAt_eq_some.mpr lives
    simp [EpisodeSelection.withdrawn, current, starts, Nat.le_of_lt earlier, creator, birthRule, start, fresh]

/-- The rollback preserves the controls and binding domains used by
retained steps. The mask erases exactly the matched child retirements. -/
theorem projection_of_saved_word (source : R) (closing : Name) (requires : Key → Bool)
    (live : Name → Option Nat) (word : List (Capture Name Key Value))
    (scope : ∀ token ∈ word.map Capture.token, TableFrame.Scoped closing requires token)
    (dormant : ∀ name, word.any (Capture.retires live name) = true → ControlFrame.viewAt source name = none) :
    Projection closing (fun name => word.any (Capture.retires live name) = true) source
      (fun name => if word.any (Capture.retires live name) then none
        else mark (replay live word source) closing .inactive name) := by
  let reverted := replay live word source
  let mask := fun name => word.any (Capture.retires live name)
  let probe : R := fun name => if mask name then none else mark reverted closing .inactive name
  change Projection closing (fun name => mask name = true) source probe
  have frame := TableFrame.discharge_frame source closing requires (word.map Capture.token) scope
  have values := replay_tables live word (left := source) (right := source) (fun _ _ => rfl)
  refine ⟨?_, ?_, ?_⟩
  · intro name omitted
    simp [probe, omitted]
  · exact dormant
  · intro name retained
    have notWithdrawn : mask name = false := Bool.eq_false_iff.mpr retained
    have probeRow : probe name = mark reverted closing .inactive name := by
      exact if_neg retained
    rw [probeRow]
    cases originalAt : source name with
    | none =>
      have erased : reverted name = none := (replay_presence live word source name).mpr originalAt
      simp [mark, Calculus.modify, erased, OptionRel]
    | some original =>
      obtain ⟨after, found, comp, parent, phase⟩ := replay_keeps_control live word source name original originalAt
      change reverted name = some after at found
      have retired : after.retired = original.retired := by
        have same := replay_retired live word source name
        change (reverted name).map Fiber.retired = _ at same
        rw [found, originalAt] at same
        have flag : word.any (Capture.retires live name) = false := notWithdrawn
        simpa [flag] using same
      by_cases same : name = closing
      · subst name
        rw [mark_self _ _ _ _ found]
        exact ⟨comp.symm, parent.symm, retired.symm, fun _ => rfl, fun impossible => (impossible rfl).elim,
          fun impossible => (impossible rfl).elim, fun impossible => (impossible rfl).elim⟩
      · have originalDomain (key : Key) : original.table key = none ↔ after.table key = none := by
          obtain ⟨native, nativeAt, _⟩ := Ordering.discharge_existing_phases source (word.map Capture.token)
            name original originalAt
          have binding := (frame name original native originalAt nativeAt same key).1
          have equal := values name key
          have tableSame : native.table key = after.table key := by
            simpa [StageRecovery.tableAt, nativeAt, show replay live word source name = some after from found] using equal
          rwa [tableSame] at binding
        rw [Transposition.mark_other _ _ _ _ same, found]
        exact ⟨comp.symm, parent.symm, retired.symm, fun impossible => (same impossible).elim,
          fun _ => congrArg GuardObservations.phaseKind phase.symm,
          fun _ => congrArg Phase.committed phase.symm, fun _ => originalDomain⟩

/-- Every actual rollback probe inside the selected episode has the
projected controls and binding domains required by the replay guard
proofs. The foreign table values may have changed, but no foreign slot
is lost or fabricated. -/
theorem probe_projects (trace : History) (episode : ClosedEpisode trace)
    (maximal : ∀ later : ClosedEpisode trace, ¬ EpisodeEdge episode later)
    (quiet : Progress.Quiet (trace.state last))
    {time : Nat} (lower : episode.opened ≤ time) (upper : time ≤ episode.closed) :
    Projection episode.name (fun name => withdraws trace episode time name = true)
      (trace.state time) (probeAt trace episode time) := by
  have lastBound := episode.interval.bounded
  let source := trace.state time
  let live := fun name => birthAt trace.state name time
  let word := track trace.state trace.actor time episode.name
  obtain ⟨owner, _, ownerAt, _⟩ := OrderingIntervals.installed_view source episode.name
    (episode.interval.installed time lower upper)
  have scopes := TableFrame.reachable_scoped program (trace.prefixRun time (by omega))
  have records := tracked_stack trace time (by omega)
  have scope : ∀ token ∈ word.map Capture.token, TableFrame.Scoped episode.name owner.component.requires token := by
    intro token carried
    have project : word.map Capture.token = saved source episode.name := records.projects episode.name
    rw [project] at carried
    exact scopes episode.name owner ownerAt token (by simpa [saved, ownerAt] using carried)
  exact projection_of_saved_word source episode.name owner.component.requires live word scope (by
    intro child omitted
    obtain ⟨step, starts, earlier, creator, native, lives⟩ := withdrawn_birth trace episode lower upper omitted
    exact child_never_installed trace episode maximal quiet starts earlier creator native (by omega) lives)

theorem closing_actor_retained (trace : History) (episode : ClosedEpisode trace)
    {time : Nat} (lower : episode.opened ≤ time) (upper : time ≤ episode.closed) :
    ¬ withdraws trace episode time episode.name = true := by
  intro selected
  obtain ⟨birth, starts, earlier, _, _, lives⟩ := withdrawn_birth trace episode lower upper selected
  have vacant : trace.state birth episode.name = none := by
    simpa using lives.boundary.resolve_left (by omega)
  exact episode.interval.installed birth starts (by omega) (by simp [ControlFrame.viewAt, vacant])

/-- A withdrawn birth has no lifecycle step inside the deleted interval.
In particular a Begin would install the child on the following cut of the
same incarnation, contradicting the selected episode's maximality. -/
theorem withdrawn_has_no_lifecycle (trace : History) (episode : ClosedEpisode trace)
    (maximal : ∀ later : ClosedEpisode trace, ¬ EpisodeEdge episode later)
    (quiet : Progress.Quiet (trace.state last))
    {time : Nat} (lower : episode.opened ≤ time) (upper : time ≤ episode.closed)
    (withdrawn : withdraws trace episode time (trace.actor time) = true) :
    EpisodeSelection.lifecycle (trace.rule time) = false := by
  have bounded := episode.interval.bounded
  obtain ⟨birth, starts, earlier, creator, bornBy, lives⟩ := withdrawn_birth trace episode lower upper withdrawn
  have dormant := child_never_installed trace episode maximal quiet starts earlier creator bornBy (by omega) lives
  have noView (row : F) (found : trace.state time (trace.actor time) = some row) :
      row.phase.committed = none := by
    simpa [ControlFrame.viewAt, found] using dormant
  have actual := trace.step time (by omega)
  generalize tag : trace.rule time = rule at actual ⊢
  generalize endpoint : trace.state (time + 1) = after at actual
  cases actual with
  | insert | retire | remove => rfl
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

/-- Every omitted live row was born as a child and still belongs to that
incarnation. Removing it from the probe preserves root membership. -/
theorem probe_rootAt (trace : History) (episode : ClosedEpisode trace)
    (maximal : ∀ later : ClosedEpisode trace, ¬ EpisodeEdge episode later)
    (quiet : Progress.Quiet (trace.state last))
    {time : Nat} (lower : episode.opened ≤ time) (upper : time ≤ episode.closed) (name : Name) :
    LegalHistory.rootAt (trace.state time) name = LegalHistory.rootAt (probeAt trace episode time) name := by
  have projected := probe_projects trace episode maximal quiet lower upper
  by_cases omitted : withdraws trace episode time name = true
  · obtain ⟨step, _, earlier, creator, birthRule, lives⟩ := withdrawn_birth trace episode lower upper omitted
    have bounded := episode.interval.bounded
    have vacant : trace.state step name = none := by simpa using lives.boundary.resolve_left (by omega)
    have born := lives.present (step + 1) (Nat.le_refl _) lives.ordered
    have creation := (EpisodeSelection.actual_child_birth (trace.step step (by omega)) birthRule vacant born).1
    rw [creator] at creation
    obtain ⟨component, start⟩ := born_row vacant creation
    cases present : trace.state time name with
    | none => simp [LegalHistory.rootAt, present, projected.absent name omitted]
    | some row =>
      have parent := (lives.metadata trace (by omega) start present).2.symm
      simp [LegalHistory.rootAt, present, projected.absent name omitted, parent, fresh]
  · have paired := projected.kept name omitted
    cases source : trace.state time name <;> cases target : probeAt trace episode time name <;>
      simp_all [LegalHistory.rootAt, OptionRel]
    rw [paired.parent]

/-- The first probe is exactly the registry before the omitted L-Begin.
There is no pending rollback or withdrawal at the opening cut. -/
theorem probe_at_opening (trace : History) (episode : ClosedEpisode trace) :
    probeAt trace episode episode.opened = trace.state (episode.opened - 1) := by
  have empty := empty_on_entry trace episode
  obtain ⟨fiber, _, found, inactive, _, _, together⟩ := begin_boundary trace episode.interval
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

/-- The live children selected by the rollback mask meet the premises of
the suffix deletion at the original closing boundary. -/
theorem withdrawn_at_closure_vestigial (trace : History) (episode : ClosedEpisode trace)
    (roots : PaperLifecycleClaims.RootInsertions trace)
    (maximal : ∀ later : ClosedEpisode trace, ¬ EpisodeEdge episode later)
    (quiet : Progress.Quiet (trace.state last)) {child : Name}
    (withdrawn : withdraws trace episode episode.closed child = true) :
    Removable (trace.state (episode.closed + 1)) child ∧
      LegalHistory.rootAt (trace.state (episode.closed + 1)) child = false := by
  obtain ⟨_, starts, earlier, creator, native, lives⟩ :=
    withdrawn_birth trace episode episode.interval.ordered (Nat.le_refl _) withdrawn
  exact closing_child_is_vestigial trace episode roots maximal quiet starts earlier creator native lives

/-- The last rollback probe has the original post-unload table, including
at the erased children, where the native table is empty. This uses actual
captured discharge and the original boundary's vestige conditions. -/
theorem probe_at_closure_tables (trace : History) (episode : ClosedEpisode trace)
    (roots : PaperLifecycleClaims.RootInsertions trace)
    (maximal : ∀ later : ClosedEpisode trace, ¬ EpisodeEdge episode later)
    (quiet : Progress.Quiet (trace.state last)) :
    RuleEvaluation.TablesUnchanged (trace.state (episode.closed + 1)) (probeAt trace episode episode.closed) := by
  let word := track trace.state trace.actor episode.closed episode.name
  let before := trace.state episode.closed
  let live := fun name => birthAt trace.state name episode.closed
  obtain ⟨fiber, raw, view, present, unloading, _, endpoint⟩ := unload_boundary trace episode.interval
  have projected : word.map Capture.token = raw := by
    have tracked := tracked_stack trace episode.closed (by have := episode.interval.bounded; omega)
    change (track trace.state trace.actor episode.closed episode.name).map Capture.token = raw
    rw [tracked.projects]
    simp [saved, present, unloading, Phase.accumulator]
  have tables := replay_tables live word (left := before) (right := before) (fun _ _ => rfl)
  rw [projected] at tables
  intro name key
  by_cases omitted : withdraws trace episode episode.closed name = true
  · have removable := (withdrawn_at_closure_vestigial trace episode roots maximal quiet omitted).1
    have empty := Transposition.removable_tables (trace.state (episode.closed + 1)) name removable key
    rw [empty]
    simp [StageRecovery.tableAt, probeAt, rollbackOf, omitted]
  · rw [endpoint, StageRecovery.tableAt_mark]
    have same : probeAt trace episode episode.closed name =
        mark (replay live word before) episode.name .inactive name := by simp [probeAt, rollbackOf, omitted, live, word, before]
    change StageRecovery.tableAt (discharge Stages.undo raw before) name key =
      ((probeAt trace episode episode.closed name).bind fun row => row.table key)
    rw [same]
    change StageRecovery.tableAt (discharge Stages.undo raw before) name key =
      StageRecovery.tableAt (mark (replay live word before) episode.name .inactive) name key
    rw [StageRecovery.tableAt_mark]
    exact tables name key

theorem replay_mark (live : Name → Option Nat) (word : List (Capture Name Key Value))
    (state : R) (actor : Name) (phase : Phase Name Key Code (Inverse Name Key Value)) :
    replay live word (mark state actor phase) = mark (replay live word state) actor phase := by
  induction word generalizing state with
  | nil => rfl
  | cons capture rest ih =>
    have one : capture.apply live (mark state actor phase) = mark (capture.apply live state) actor phase := by
      rcases capture with ⟨token, index⟩
      cases token with
      | unit => rfl
      | restrict owner key => exact Transposition.write_mark state owner actor phase key none
      | operate owner key callback =>
        funext name
        by_cases target : name = owner
        · subst name
          by_cases acts : owner = actor <;>
            simp [Capture.apply, Stages.undo, Calculus.modify, mark, acts, Function.comp_def]
        · by_cases acts : name = actor
          · subst name
            simp [Capture.apply, Stages.undo, Calculus.modify, mark, target]
          · simp [Capture.apply, Stages.undo, Calculus.modify, mark, target, acts]
      | retire child =>
        by_cases current : live child = some index <;>
          simp [Capture.apply, current, Transposition.mark_retire]
    rw [replay, replay, one, ih]

omit [DecidableEq Name] [DecidableEq Key] in
theorem birthAt_same_presence_at (states : Nat → R) (time : Nat) (name : Name)
    (same : states (time + 1) name = none ↔ states time name = none) :
    birthAt states name (time + 1) = birthAt states name time := by
  cases current : states (time + 1) name with
  | none =>
    have absent : states time name = none := same.mp current
    exact (birthAt_none.mpr current).trans (birthAt_none.mpr absent).symm
  | some row =>
    cases birth : birthAt states name time with
    | none =>
      have absentNext : states (time + 1) name = none := same.mpr (birthAt_none.mp birth)
      rw [current] at absentNext
      cases absentNext
    | some born => simp [birthAt, current, birth]

omit [DecidableEq Name] [DecidableEq Key] in
theorem birthAt_same_presence (states : Nat → R) (time : Nat)
    (same : ∀ name, states (time + 1) name = none ↔ states time name = none) :
    (fun name => birthAt states name (time + 1)) = (fun name => birthAt states name time) :=
  funext fun name => birthAt_same_presence_at states time name (same name)

private theorem rollbackOf_mark (trace : History) (episode : ClosedEpisode trace) (time : Nat)
    (state : R) (actor : Name) (phase : Phase Name Key Code (Inverse Name Key Value))
    (different : actor ≠ episode.name) (kept : ¬ withdraws trace episode time actor = true) :
    rollbackOf trace episode time (mark state actor phase) = mark (rollbackOf trace episode time state) actor phase := by
  let live := fun name => birthAt trace.state name time
  let word := track trace.state trace.actor time episode.name
  let reverted := replay live word state
  funext name
  change (if withdraws trace episode time name then none else
    mark (replay live word (mark state actor phase)) episode.name .inactive name) = _
  rw [replay_mark, ← Transposition.marks_commute reverted actor episode.name phase .inactive different]
  by_cases same : name = actor
  · subst name
    simp [rollbackOf, kept, mark, Calculus.modify, reverted, live, word]
  · simp [rollbackOf, mark, Calculus.modify, same, reverted, live, word]

/-- A retained actor's phase update commutes with rollback after an edit
that preserves the set of live names. -/
theorem probe_after_foreign_edit (trace : History) (episode : ClosedEpisode trace)
    {time : Nat} {phase : Phase Name Key Code (Inverse Name Key Value)} {middle : R}
    (different : trace.actor time ≠ episode.name)
    (kept : ¬ withdraws trace episode time (trace.actor time) = true)
    (presence : ∀ name, middle name = none ↔ trace.state time name = none)
    (marked : trace.state (time + 1) = mark middle (trace.actor time) phase) :
    probeAt trace episode (time + 1) =
      mark (rollbackOf trace episode time middle) (trace.actor time) phase := by
  have words : track trace.state trace.actor (time + 1) episode.name =
      track trace.state trace.actor time episode.name := by
    simp [track, advance, Ne.symm different]
  have births := birthAt_same_presence trace.state time fun name => by
    rw [marked]
    exact (Transposition.mark_presence _ _ _ _).trans (presence name)
  have withdrawals : withdraws trace episode (time + 1) = withdraws trace episode time := by
    funext name
    simp only [withdraws, words, births]
  have sameRollback : rollbackOf trace episode (time + 1) (trace.state (time + 1)) =
      rollbackOf trace episode time (trace.state (time + 1)) := by
    unfold rollbackOf
    rw [words, births, withdrawals]
  unfold probeAt
  rw [sameRollback, marked]
  exact rollbackOf_mark trace episode time middle (trace.actor time) phase different kept

theorem probe_after_foreign_mark (trace : History) (episode : ClosedEpisode trace)
    {time : Nat} {phase : Phase Name Key Code (Inverse Name Key Value)}
    (different : trace.actor time ≠ episode.name)
    (kept : ¬ withdraws trace episode time (trace.actor time) = true)
    (marked : trace.state (time + 1) = mark (trace.state time) (trace.actor time) phase) :
    probeAt trace episode (time + 1) = mark (probeAt trace episode time) (trace.actor time) phase :=
  probe_after_foreign_edit trace episode different kept (fun _ => Iff.rfl) marked

/-- A fresh birth by a retained actor cannot match a capture already in the
closing actor's word. Changing the cut preserves rollback on any input. -/
private theorem rollbackOf_next_birth (trace : History) (episode : ClosedEpisode trace)
    {time : Nat} (bounded : time ≤ last) {name : Name}
    (different : trace.actor time ≠ episode.name)
    (vacant : trace.state time name = none) (born : trace.state (time + 1) name ≠ none)
    (outside : ∀ other, other ≠ name → (trace.state (time + 1) other = none ↔ trace.state time other = none))
    (state : R) : rollbackOf trace episode (time + 1) state = rollbackOf trace episode time state := by
  let word := track trace.state trace.actor time episode.name
  have words : track trace.state trace.actor (time + 1) episode.name = word := by
    simp [track, advance, Ne.symm different, word]
  have agrees (capture : Capture Name Key Value) (member : capture ∈ word) (target : Name) :
      (birthAt trace.state target (time + 1) = some capture.index ↔
        birthAt trace.state target time = some capture.index) := by
    by_cases selected : target = name
    · subst target
      have age := ((tracked_stack trace time bounded).origins episode.name capture member).1
      have earlier : time + 1 ≠ capture.index := by omega
      simp [birthAt_of_created vacant born, birthAt_none.mpr vacant, earlier]
    · rw [birthAt_same_presence_at trace.state time target (outside target selected)]
  have replayed : replay (fun n => birthAt trace.state n (time + 1)) word state =
      replay (fun n => birthAt trace.state n time) word state :=
    replay_congr_matches word state (fun capture member target _ => agrees capture member target)
  have mask : withdraws trace episode (time + 1) = withdraws trace episode time := by
    funext query
    have tested (capture : Capture Name Key Value) (member : capture ∈ word) :
        Capture.retires (fun n => birthAt trace.state n (time + 1)) query capture =
          Capture.retires (fun n => birthAt trace.state n time) query capture := by
      cases token : capture.token with
      | retire target => simp only [Capture.retires, token, agrees capture member target]
      | _ => simp [Capture.retires, token]
    apply Bool.eq_iff_iff.mpr
    simp only [withdraws, words, List.any_eq_true]
    constructor
    · rintro ⟨capture, member, triggered⟩
      exact ⟨capture, member, (tested capture member).symm.trans triggered⟩
    · rintro ⟨capture, member, triggered⟩
      exact ⟨capture, member, (tested capture member).trans triggered⟩
  unfold rollbackOf
  rw [words, replayed, mask]

private theorem rollbackOf_put_fresh (trace : History) (episode : ClosedEpisode trace) (time : Nat)
    {name : Name} (component : Component Key Code) (parent : Option Name)
    (vacant : trace.state time name = none) (different : name ≠ episode.name) :
    rollbackOf trace episode time (put (trace.state time) name (fresh component parent)) =
      put (probeAt trace episode time) name (fresh component parent) := by
  have unmasked := vacant_not_withdrawn trace episode time vacant
  let live := fun n => birthAt trace.state n time
  let word := track trace.state trace.actor time episode.name
  let reverted := replay live word (trace.state time)
  funext query
  change (if withdraws trace episode time query then none else
    mark (replay live word (put (trace.state time) name (fresh component parent))) episode.name .inactive query) = _
  rw [replay_put_fresh live word _ _ component parent (birthAt_none.mpr vacant),
    Transposition.mark_put reverted episode.name name (fresh component parent) .inactive (Ne.symm different)]
  by_cases selected : query = name
  · subst query
    simp [unmasked]
  · simp [put, selected, probeAt, rollbackOf, reverted, live, word]

/-- The actual marked allocation endpoint commutes exactly with the old
rollback, including when the new child name was used by a deleted child. -/
theorem probe_after_foreign_birth (trace : History) (episode : ClosedEpisode trace)
    {time : Nat} (bounded : time ≤ last) {child : Name} {component : Component Key Code}
    {phase : Phase Name Key Code (Inverse Name Key Value)}
    (different : trace.actor time ≠ episode.name)
    (kept : ¬ withdraws trace episode time (trace.actor time) = true)
    (freshName : trace.state time child = none)
    (childDifferent : child ≠ episode.name)
    (ended : trace.state (time + 1) = mark
      (put (trace.state time) child (fresh component (some (trace.actor time)))) (trace.actor time) phase) :
    probeAt trace episode (time + 1) = mark
      (put (probeAt trace episode time) child (fresh component (some (trace.actor time)))) (trace.actor time) phase := by
  have born : trace.state (time + 1) child ≠ none := by
    rw [ended, ne_eq, Transposition.mark_presence]
    simp
  have outside (other : Name) (distinct : other ≠ child) :
      trace.state (time + 1) other = none ↔ trace.state time other = none := by
    rw [ended, Transposition.mark_presence, Transposition.put_other _ _ _ _ distinct]
  unfold probeAt at *
  rw [rollbackOf_next_birth trace episode bounded different freshName born outside, ended,
    rollbackOf_mark _ _ _ _ _ _ different kept]
  exact congrArg (fun r => mark r (trace.actor time) phase)
    (rollbackOf_put_fresh trace episode time component (some (trace.actor time)) freshName childDifferent)

theorem replay_retire (live : Name → Option Nat) (word : List (Capture Name Key Value))
    (state : R) (name : Name) :
    replay live word (Calculus.retire state name) = Calculus.retire (replay live word state) name := by
  induction word generalizing state with
  | nil => rfl
  | cons capture rest ih =>
    have step : capture.apply live (Calculus.retire state name) = Calculus.retire (capture.apply live state) name := by
      obtain ⟨token, index⟩ := capture
      cases token with
      | unit => rfl
      | restrict owner key => exact Transposition.write_retire state owner name key none
      | operate owner key inverse => exact Transposition.modify_retire state owner name _ (fun _ => rfl)
      | retire child =>
        by_cases liveChild : live child = some index
        · simp only [Capture.apply, if_pos liveChild]
          exact Transposition.modify_retire state child name _ (fun _ => rfl)
        · simp [Capture.apply, liveChild]
    rw [replay, replay, step, ih]

private theorem probe_after_retire (trace : History) (episode : ClosedEpisode trace)
    {time : Nat} (bounded : time ≤ last)
    (ended : trace.state (time + 1) = Calculus.retire (trace.state time) (trace.actor time)) :
    probeAt trace episode (time + 1) = Calculus.retire (probeAt trace episode time) (trace.actor time) := by
  let actor := trace.actor time
  let source := trace.state time
  let word := track trace.state trace.actor time episode.name
  have stable : saved (trace.state (time + 1)) = saved source := by
    rw [ended]
    funext name
    by_cases selected : name = actor
    · subst name
      cases found : source actor <;> simp [saved, Calculus.retire, Calculus.modify, source, actor, found]
    · unfold saved
      rw [Transposition.retire_other _ _ _ selected]
  have words : track trace.state trace.actor (time + 1) episode.name = word := by
    exact congrFun (advance_control actor (time + 1) _ (tracked_stack trace time bounded).projects stable) episode.name
  have births := birthAt_same_presence trace.state time fun name => by rw [ended, Transposition.retire_presence]
  have mask : withdraws trace episode (time + 1) = withdraws trace episode time := by
    funext name
    simp only [withdraws, words, births, word]
  unfold probeAt rollbackOf
  rw [mask, births, words, ended, replay_retire]
  dsimp only
  rw [Transposition.mark_retire]
  funext name
  by_cases selected : name = actor
  · subst name
    by_cases omitted : withdraws trace episode time actor = true <;>
      simp [Calculus.retire, Calculus.modify, omitted, actor, word]
  · simp [Calculus.retire, Calculus.modify, selected, actor, word]

private theorem probe_after_remove (trace : History) (episode : ClosedEpisode trace) {time : Nat}
    (different : trace.actor time ≠ episode.name)
    (ended : trace.state (time + 1) = erase (trace.state time) (trace.actor time)) :
    probeAt trace episode (time + 1) = erase (probeAt trace episode time) (trace.actor time) := by
  let actor := trace.actor time
  let word := track trace.state trace.actor time episode.name
  have words : track trace.state trace.actor (time + 1) episode.name = word := by
    simp [track, advance, Ne.symm different, word]
  have births (name : Name) (other : name ≠ actor) :
      birthAt trace.state name (time + 1) = birthAt trace.state name time := by
    apply birthAt_same_presence_at
    simp [ended, erase, actor, other]
  have replayed := Vestigial.replay_erase (trace.state time) actor births word
  unfold probeAt rollbackOf
  rw [words, ended, replayed]
  dsimp only
  unfold mark
  rw [Vestigial.modify_erase]
  funext name
  by_cases selected : name = actor
  · subst name
    simp [erase, actor]
  · have mask : withdraws trace episode (time + 1) name = withdraws trace episode time name := by
      unfold withdraws
      apply List.any_congr words
      intro capture
      cases token : capture.token with
      | retire child =>
        by_cases same : name = child
        · subst child
          simp only [Capture.retires, token, births name selected]
        · simp [Capture.retires, token, same]
      | _ => simp [Capture.retires, token]
    simp [erase, mask, selected, actor, word]

/-- From one actual rollback probe to the next, a retained native Begin
selects its original code and view. The endpoint is computed by rollback
of the next original cut. -/
theorem replay_begin_between_probes (trace : History) (episode : ClosedEpisode trace)
    (maximal : ∀ later : ClosedEpisode trace, ¬ EpisodeEdge episode later)
    (quiet : Progress.Quiet (trace.state last))
    {time : Nat} (lower : episode.opened ≤ time) (upper : time < episode.closed)
    (different : trace.actor time ≠ episode.name)
    (kept : ¬ withdraws trace episode time (trace.actor time) = true)
    (rule : trace.rule time = .begin) :
    Labeled.Step program .begin (trace.actor time) (probeAt trace episode time) (probeAt trace episode (time + 1)) := by
  have event := trace.step time (by have := episode.interval.bounded; omega)
  rw [rule] at event
  have projection := probe_projects trace episode maximal quiet lower (by omega)
  generalize aligns : trace.state (time + 1) = after at event
  cases event with
  | begin _ _ fiber view found inactive _ target =>
    rw [probe_after_foreign_mark trace episode different kept aligns]
    exact begin_on_probe trace episode maximal (by omega) (by omega) projection kept different
      found inactive target aligns

theorem probe_keeps_phase (trace : History) (episode : ClosedEpisode trace)
    {time : Nat} {actor : Name} {row : F} (different : actor ≠ episode.name)
    (kept : ¬ withdraws trace episode time actor = true)
    (present : trace.state time actor = some row) :
    ∃ paired, probeAt trace episode time actor = some paired ∧ paired.phase = row.phase := by
  obtain ⟨paired, found, _, _, phase⟩ := replay_keeps_control (fun child => birthAt trace.state child time)
    (track trace.state trace.actor time episode.name) (trace.state time) actor row present
  exact ⟨paired, by simpa [probeAt, rollbackOf, kept, Transposition.mark_other _ _ _ _ different] using found, phase⟩

/-- A retained unit landing changes only the phase and pushes its native
unit token, so its selected continuation reaches the next probe exactly. -/
theorem replay_unit_activation (trace : History) (episode : ClosedEpisode trace)
    (maximal : ∀ later : ClosedEpisode trace, ¬ EpisodeEdge episode later)
    (quiet : Progress.Quiet (trace.state last))
    {time : Nat} (lower : episode.opened ≤ time) (upper : time ≤ episode.closed)
    {row : F} {code : Code} {word : List (Inverse Name Key Value)} {view : View Name Key}
    (different : trace.actor time ≠ episode.name)
    (kept : ¬ withdraws trace episode time (trace.actor time) = true)
    (present : trace.state time (trace.actor time) = some row)
    (phase : row.phase = .reloading code word view)
    (target : Target (trace.state time) (trace.actor time) view)
    (action : (program code).action = .unit)
    (marked : trace.state (time + 1) = mark (trace.state time) (trace.actor time)
      (Transposition.landedPhase ((program code).next .unit) .unit word view)) :
    Labeled.Step program (Transposition.landedRule ((program code).next .unit)) (trace.actor time)
      (probeAt trace episode time) (probeAt trace episode (time + 1)) := by
  obtain ⟨paired, found, projectedPhase⟩ := probe_keeps_phase trace episode different kept present
  have projection := probe_projects trace episode maximal quiet lower upper
  have avoids := committed_avoids_closing trace episode maximal lower upper present
    (show row.phase.committed = some view by simp [phase, Phase.committed])
  rw [probe_after_foreign_mark trace episode different kept marked]
  exact Transposition.landed_step program paired word view found (projectedPhase.trans phase)
    (projection.target_forward kept present view avoids target) (.unit _ _ _ action)

/-- Landed Divert with a unit head preserves both the stale target and
the exact appended token in the next probe. -/
theorem replay_unit_divert (trace : History) (episode : ClosedEpisode trace)
    (maximal : ∀ later : ClosedEpisode trace, ¬ EpisodeEdge episode later)
    (quiet : Progress.Quiet (trace.state last))
    {time : Nat} (lower : episode.opened ≤ time) (upper : time ≤ episode.closed)
    {row : F} {code : Code} {word : List (Inverse Name Key Value)} {view : View Name Key}
    (different : trace.actor time ≠ episode.name)
    (kept : ¬ withdraws trace episode time (trace.actor time) = true)
    (present : trace.state time (trace.actor time) = some row)
    (phase : row.phase = .reloading code word view)
    (stale : ¬ Target (trace.state time) (trace.actor time) view)
    (action : (program code).action = .unit)
    (marked : trace.state (time + 1) = mark (trace.state time) (trace.actor time) (.unloading (.unit :: word) view)) :
    Labeled.Step program .divert (trace.actor time) (probeAt trace episode time) (probeAt trace episode (time + 1)) := by
  obtain ⟨paired, found, projectedPhase⟩ := probe_keeps_phase trace episode different kept present
  have projection := probe_projects trace episode maximal quiet lower upper
  rw [probe_after_foreign_mark trace episode different kept marked]
  exact .divert _ _ _ paired code word view [.unit] found (projectedPhase.trans phase)
    (fun target => stale (projection.target_backward _ _ target)) (.inr ⟨_, _, .unit _ _ _ action, rfl⟩)

private theorem vacant_ne_closing (trace : History) (episode : ClosedEpisode trace)
    {time : Nat} (lower : episode.opened ≤ time) (upper : time ≤ episode.closed)
    {name : Name} (vacant : trace.state time name = none) : name ≠ episode.name := by
  intro same
  subst name
  exact episode.interval.installed time lower upper (by simp [ControlFrame.viewAt, vacant])

open OrchestrationSorting (Command) in
/-- Each retained orchestration command transports its actual payload and
reaches the next probe exactly. Retirement may target the closing actor. -/
theorem replay_command_between_probes (trace : History) (episode : ClosedEpisode trace)
    (maximal : ∀ later : ClosedEpisode trace, ¬ EpisodeEdge episode later)
    (quiet : Progress.Quiet (trace.state last))
    {time : Nat} (lower : episode.opened ≤ time) (upper : time ≤ episode.closed)
    (command : Command Name Key Code) (actor : command.actor = trace.actor time)
    (kept : ¬ withdraws trace episode time command.actor = true)
    (actual : command.Step (trace.state time) (trace.state (time + 1))) :
    command.Step (probeAt trace episode time) (probeAt trace episode (time + 1)) := by
  have bounded : time ≤ last := by have := episode.interval.bounded; omega
  have removeForeign (name : Name) (selected : command = .remove name) : name ≠ episode.name := by
    subst command
    have ready : Removable (trace.state time) name := actual.1
    intro same
    subst name
    apply episode.interval.installed time lower upper
    cases found : trace.state time episode.name with
    | none => simp [ControlFrame.viewAt, found]
    | some row =>
      rw [Removable, found] at ready
      simp [ControlFrame.viewAt, found, ready.2.1, Phase.committed]
  have permitted := (probe_projects trace episode maximal quiet lower upper).command command kept removeForeign actual
  refine ⟨permitted.1, ?_⟩
  cases command with
  | insert name component =>
    have sameName : name = trace.actor time := actor
    have ready : Insertable (trace.state time) name component none := actual.1
    have different := vacant_ne_closing trace episode lower upper ready.1
    have ended : trace.state (time + 1) = put (trace.state time) name (fresh component none) := actual.2
    have born : trace.state (time + 1) name ≠ none := by simp [ended]
    have outside (other : Name) (distinct : other ≠ name) :
        trace.state (time + 1) other = none ↔ trace.state time other = none := by
      rw [ended, Transposition.put_other _ _ _ _ distinct]
    change rollbackOf trace episode (time + 1) (trace.state (time + 1)) = _
    rw [rollbackOf_next_birth trace episode bounded (sameName ▸ different) ready.1 born outside, ended]
    exact rollbackOf_put_fresh trace episode time component none ready.1 different
  | retire name =>
    have sameName : name = trace.actor time := actor
    have ended : trace.state (time + 1) = Calculus.retire (trace.state time) (trace.actor time) := by
      simpa only [Command.apply, sameName] using actual.2
    simpa only [Command.apply, sameName] using probe_after_retire trace episode bounded ended
  | remove name =>
    have sameName : name = trace.actor time := actor
    have ended : trace.state (time + 1) = erase (trace.state time) (trace.actor time) := by
      simpa only [Command.apply, sameName] using actual.2
    simpa only [Command.apply, sameName] using probe_after_remove trace episode (sameName ▸ removeForeign name rfl) ended

open OrchestrationSorting (Command) in
/-- Replaying a command after observational steps retains its payload and
source-derived root classification. -/
theorem replay_command_from_related_probe [Setoid Value]
    (trace : History) (episode : ClosedEpisode trace)
    (maximal : ∀ later : ClosedEpisode trace, ¬ EpisodeEdge episode later)
    (quiet : Progress.Quiet (trace.state last))
    {time : Nat} (lower : episode.opened ≤ time) (upper : time ≤ episode.closed)
    (command : Command Name Key Code) (actor : command.actor = trace.actor time)
    (kept : ¬ withdraws trace episode time command.actor = true)
    (actual : command.Step (trace.state time) (trace.state (time + 1)))
    {state : R} (source : StageSimulation.Related Eq state (probeAt trace episode time)) :
    command.Step state (command.apply state) ∧
      StageSimulation.Related Eq (command.apply state) (probeAt trace episode (time + 1)) ∧
      LegalHistory.commandRoots (trace.state time) command = LegalHistory.commandRoots state command := by
  have rootAgreement (name : Name) : LegalHistory.rootAt (trace.state time) name = LegalHistory.rootAt state name := by
    rw [probe_rootAt trace episode maximal quiet lower upper name]
    have controls := source.observed name
    cases left : state name <;> cases right : probeAt trace episode time name <;>
      simp_all [LegalHistory.rootAt, OptionRel]
    rw [controls.parent]
  have roots := LegalHistory.eventRoots_agree (.command command) rootAgreement
  have native := replay_command_between_probes trace episode maximal quiet lower upper command actor kept actual
  rw [native.2]
  refine ⟨⟨?_, rfl⟩, ?_, roots⟩
  · cases command with
    | insert name component => exact (GuardObservations.insertable_iff source.observed name component none).mpr native.1
    | retire name => exact fun absent => native.1 ((GuardObservations.none_iff source.observed name).mp absent)
    | remove name => exact (GuardObservations.removable_iff source.observed name).mpr native.1
  · cases command with
    | insert name component => exact StageSimulation.put_related source name (StageSimulation.fresh_related ⟨rfl, rfl, rfl⟩ none)
    | retire name => exact StageSimulation.retire_related source name
    | remove name => exact StageSimulation.erase_related source name

open OrchestrationSorting (Command) in
/-- A command at a withdrawn name can only retire or remove that live
child incarnation. Its omission fixes the probe and drops no root command. -/
theorem probe_omits_withdrawn_command (trace : History) (episode : ClosedEpisode trace)
    (maximal : ∀ later : ClosedEpisode trace, ¬ EpisodeEdge episode later)
    (quiet : Progress.Quiet (trace.state last))
    {time : Nat} (lower : episode.opened ≤ time) (upper : time ≤ episode.closed)
    (command : Command Name Key Code) (actor : command.actor = trace.actor time)
    (withdrawn : withdraws trace episode time command.actor = true)
    (actual : command.Step (trace.state time) (trace.state (time + 1))) :
    probeAt trace episode (time + 1) = probeAt trace episode time ∧
      LegalHistory.commandRoots (trace.state time) command = [] := by
  have bounded : time ≤ last := by have := episode.interval.bounded; omega
  have absent : probeAt trace episode time command.actor = none := if_pos withdrawn
  have child : LegalHistory.rootAt (trace.state time) command.actor = false := by
    rw [probe_rootAt trace episode maximal quiet lower upper, LegalHistory.rootAt, absent]
    rfl
  have different : command.actor ≠ episode.name := by
    intro same
    exact closing_actor_retained trace episode lower upper (same ▸ withdrawn)
  cases command with
  | insert name component => exact False.elim (vacant_not_withdrawn trace episode time actual.1.1 withdrawn)
  | retire name =>
    have sameName : name = trace.actor time := actor
    have ended : trace.state (time + 1) = Calculus.retire (trace.state time) (trace.actor time) := by
      simpa only [Command.apply, sameName] using actual.2
    rw [probe_after_retire trace episode bounded ended, ← sameName]
    refine ⟨?_, by simp [LegalHistory.commandRoots, show LegalHistory.rootAt (trace.state time) name = false from child]⟩
    funext query
    by_cases selected : query = name
    · subst query
      simp [Calculus.retire, Calculus.modify, show probeAt trace episode time name = none from absent]
    · simp [Calculus.retire, Calculus.modify, selected]
  | remove name =>
    have sameName : name = trace.actor time := actor
    have ended : trace.state (time + 1) = erase (trace.state time) (trace.actor time) := by
      simpa only [Command.apply, sameName] using actual.2
    rw [probe_after_remove trace episode (actor ▸ different) ended, ← sameName]
    refine ⟨?_, by simp [LegalHistory.commandRoots, show LegalHistory.rootAt (trace.state time) name = false from child]⟩
    funext query
    by_cases selected : query = name
    · subst query
      simp [erase, show probeAt trace episode time name = none from absent]
    · simp [erase, selected]

/-- A retained allocation keeps the original child name, declaration,
retirement token and outcome-selected continuation. -/
theorem replay_allocation_activation (trace : History) (episode : ClosedEpisode trace)
    (maximal : ∀ later : ClosedEpisode trace, ¬ EpisodeEdge episode later)
    (quiet : Progress.Quiet (trace.state last))
    {time : Nat} (lower : episode.opened ≤ time) (upper : time ≤ episode.closed)
    {row : F} {code : Code} {word : List (Inverse Name Key Value)} {view : View Name Key}
    (different : trace.actor time ≠ episode.name)
    (kept : ¬ withdraws trace episode time (trace.actor time) = true)
    (present : trace.state time (trace.actor time) = some row)
    (phase : row.phase = .reloading code word view)
    (target : Target (trace.state time) (trace.actor time) view)
    {child : Name} {component : Component Key Code} (action : (program code).action = .instantiate component)
    (ready : Insertable (trace.state time) child component (some (trace.actor time)))
    (ended : trace.state (time + 1) = mark
      (put (trace.state time) child (fresh component (some (trace.actor time)))) (trace.actor time)
      (Transposition.landedPhase ((program code).next (.child child)) (.retire child) word view)) :
    Labeled.Step program (Transposition.landedRule ((program code).next (.child child))) (trace.actor time)
      (probeAt trace episode time) (probeAt trace episode (time + 1)) := by
  obtain ⟨pair, found, aligned⟩ := probe_keeps_phase trace episode different kept present
  have projected := probe_projects trace episode maximal quiet lower upper
  have avoids := committed_avoids_closing trace episode maximal lower upper present
    (show row.phase.committed = some view by simp [phase, Phase.committed])
  have pairedReady := projected.insertable (fun parent identifies => by cases identifies; exact kept) ready
  have bounded : time ≤ last := by have := episode.interval.bounded; omega
  rw [probe_after_foreign_birth trace episode bounded different kept ready.1
    (vacant_ne_closing trace episode lower upper ready.1) ended]
  exact Transposition.landed_step program pair word view found (aligned.trans phase)
    (projected.target_forward kept present view avoids target) (.instantiate _ _ _ _ _ action pairedReady)

/-- Landed Divert keeps its original allocation despite the stale
target. The supplied child and its parent are present in the next probe. -/
theorem replay_allocation_divert (trace : History) (episode : ClosedEpisode trace)
    (maximal : ∀ later : ClosedEpisode trace, ¬ EpisodeEdge episode later)
    (quiet : Progress.Quiet (trace.state last))
    {time : Nat} (lower : episode.opened ≤ time) (upper : time ≤ episode.closed)
    {row : F} {code : Code} {word : List (Inverse Name Key Value)} {view : View Name Key}
    (different : trace.actor time ≠ episode.name)
    (kept : ¬ withdraws trace episode time (trace.actor time) = true)
    (present : trace.state time (trace.actor time) = some row)
    (phase : row.phase = .reloading code word view)
    (stale : ¬ Target (trace.state time) (trace.actor time) view)
    {child : Name} {component : Component Key Code} (action : (program code).action = .instantiate component)
    (ready : Insertable (trace.state time) child component (some (trace.actor time)))
    (ended : trace.state (time + 1) = mark
      (put (trace.state time) child (fresh component (some (trace.actor time)))) (trace.actor time)
      (.unloading (.retire child :: word) view)) :
    Labeled.Step program .divert (trace.actor time) (probeAt trace episode time) (probeAt trace episode (time + 1)) := by
  obtain ⟨pair, found, aligned⟩ := probe_keeps_phase trace episode different kept present
  have projected := probe_projects trace episode maximal quiet lower upper
  have pairedReady := projected.insertable (fun parent identifies => by cases identifies; exact kept) ready
  have bounded : time ≤ last := by have := episode.interval.bounded; omega
  rw [probe_after_foreign_birth trace episode bounded different kept ready.1
    (vacant_ne_closing trace episode lower upper ready.1) ended]
  exact .divert _ _ _ pair code word view [.retire child] found (aligned.trans phase)
    (fun target => stale (projected.target_backward _ _ target))
    (.inr ⟨_, _, .instantiate _ _ _ _ _ action pairedReady, rfl⟩)

/-- A retained Leave has its original false target on the probe, and
the native phase transition reaches the next probe exactly. -/
theorem replay_leave_between_probes (trace : History) (episode : ClosedEpisode trace)
    (maximal : ∀ later : ClosedEpisode trace, ¬ EpisodeEdge episode later)
    (quiet : Progress.Quiet (trace.state last))
    {time : Nat} (lower : episode.opened ≤ time) (upper : time ≤ episode.closed)
    (different : trace.actor time ≠ episode.name)
    (kept : ¬ withdraws trace episode time (trace.actor time) = true)
    (rule : trace.rule time = .leave) :
    Labeled.Step program .leave (trace.actor time) (probeAt trace episode time) (probeAt trace episode (time + 1)) := by
  have event := trace.step time (by have := episode.interval.bounded; omega)
  rw [rule] at event
  have projection := probe_projects trace episode maximal quiet lower upper
  generalize aligns : trace.state (time + 1) = after at event
  cases event with
  | leave _ _ row word view present phase stale =>
    obtain ⟨paired, found, projectedPhase⟩ := probe_keeps_phase trace episode different kept present
    rw [probe_after_foreign_mark trace episode different kept aligns]
    exact .leave _ _ paired word view found (projectedPhase.trans phase)
      (fun active => stale (projection.target_backward _ _ active))

/-- The no-landing alternative of Divert retains exactly the old word.
The applicable branch is the one already taken by the original trace. -/
theorem replay_bare_divert_between_probes (trace : History) (episode : ClosedEpisode trace)
    (maximal : ∀ later : ClosedEpisode trace, ¬ EpisodeEdge episode later)
    (quiet : Progress.Quiet (trace.state last))
    {time : Nat} (lower : episode.opened ≤ time) (upper : time ≤ episode.closed)
    {row : F} {code : Code} {word : List (Inverse Name Key Value)} {view : View Name Key}
    (different : trace.actor time ≠ episode.name)
    (kept : ¬ withdraws trace episode time (trace.actor time) = true)
    (present : trace.state time (trace.actor time) = some row)
    (phase : row.phase = .reloading code word view)
    (stale : ¬ Target (trace.state time) (trace.actor time) view)
    (marked : trace.state (time + 1) = mark (trace.state time) (trace.actor time) (.unloading word view)) :
    Labeled.Step program .divert (trace.actor time) (probeAt trace episode time) (probeAt trace episode (time + 1)) := by
  obtain ⟨paired, found, projectedPhase⟩ := probe_keeps_phase trace episode different kept present
  have projection := probe_projects trace episode maximal quiet lower upper
  rw [probe_after_foreign_mark trace episode different kept marked]
  simpa only [List.nil_append] using
    (Labeled.Step.divert (program := program) (probeAt trace episode time) (probeAt trace episode time)
      (trace.actor time) paired code word view [] found (projectedPhase.trans phase)
      (fun active => stale (projection.target_backward _ _ active)) (.inl ⟨rfl, rfl⟩))

end Cordis.Repairs.EpisodeRollback
