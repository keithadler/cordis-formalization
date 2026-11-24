import Cordis.Repairs.GuardedEpisodeDependencies
import Cordis.Repairs.EpisodeClosure
import Cordis.SupportUniqueness

/-! Boundary properties of the selected episode in a guarded source history. -/
namespace Cordis.Repairs.GuardedHistory
open Calculus Stages Incarnation IncarnationReplay LegalHistory OrchestrationSorting
open StageRecovery (tableAt tableAt_mark tableAt_restrict tableAt_operate tableAt_retire)
open EpisodeBoundary (Leaf born_row prefix_since_absence prefix_closes_or_extends retired_through_residency
  leaf_at_birth new_parent_requires_view empty_table_during_inactivity)
universe u
variable {Name Key Value Code Error : Type u} [DecidableEq Name] [DecidableEq Key]
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
local notation "I" => Inverse Name Key Value
local notation "C" => Capture Name Key Value
local notation "Notes" => Vestigial.CutNotes Name Key Value
local notation "Ev" => Event Name Key Code
local notation "Program" => Code → Instruction Name Key Value Code Error
variable {program : Code → Instruction Name Key Value Code Error} {last : Nat}

theorem Trace.actual_child_birth (trace : Trace program last)
    {time : Nat} {child : Name} (bounded : time < last) (birthRule : EpisodeSelection.canBirth (trace.rule time) = true)
    (vacant : trace.state time child = none) (born : trace.state (time + 1) child ≠ none) :
    Transposition.CreatesChild program (trace.actor time) (trace.state time) (trace.state (time + 1)) child ∧
      (⟨.retire child, time + 1⟩ : C) ∈ (trace.notes (time + 1)).2 (trace.actor time) := by
  have step := trace.step time bounded
  rcases transition_cases step.1 with native | ⟨actor, unload, _⟩
  · have ⟨creation, pushed⟩ := EpisodeSelection.actual_child_birth native birthRule vacant born
    refine ⟨creation, ?_⟩
    rw [step.2]
    change _ ∈ advance (trace.state time) (trace.state (time + 1)) (trace.actor time)
      (time + 1) (trace.notes time).2 (trace.actor time)
    rw [Trace.actor, advance_capture _ _ _ _ pushed]
    simp
  · simp [Trace.rule, unload, eventRule, LegalHistory.Lifecycle.rule, EpisodeSelection.canBirth] at birthRule

theorem birth_capture_at_cut (trace : Trace program last) (episode : ClosedEpisode trace)
    {birthStep time : Nat} {child : Name}
    (lower : episode.opened ≤ birthStep) (earlier : birthStep < time) (upper : time ≤ episode.closed)
    (creator : trace.actor birthStep = episode.name)
    (birthRule : EpisodeSelection.canBirth (trace.rule birthStep) = true)
    (vacant : trace.state birthStep child = none) (born : trace.state (birthStep + 1) child ≠ none) :
    (⟨.retire child, birthStep + 1⟩ : C) ∈ (trace.notes time).2 episode.name := by
  have bound := episode.interval.bounded
  have capture := (trace.actual_child_birth (by omega) birthRule vacant born).2
  rw [creator] at capture
  exact trace.capture_through_interval episode.name (by omega) (by omega)
    (fun point later earlier => episode.interval.installed point (by omega) (by omega)) capture

theorem child_retired_at_closure (trace : Trace program last) (episode : ClosedEpisode trace)
    {birthStep : Nat} {child : Name}
    (lower : episode.opened ≤ birthStep) (upper : birthStep < episode.closed)
    (creator : trace.actor birthStep = episode.name)
    (birthRule : EpisodeSelection.canBirth (trace.rule birthStep) = true)
    (lives : Residency trace.state child (birthStep + 1) episode.closed) :
    (trace.state (episode.closed + 1) child).map Fiber.retired = some true := by
  have vacant : trace.state birthStep child = none := by
    simpa using lives.boundary.resolve_left (by omega)
  have born := lives.present (birthStep + 1) (Nat.le_refl _) lives.ordered
  have recorded := birth_capture_at_cut trace episode lower upper (Nat.le_refl _) creator birthRule vacant born
  have installed := episode.interval.installed birthStep lower (by omega)
  have distinct : child ≠ episode.name := by
    intro same
    have empty : trace.state birthStep episode.name = none := same ▸ vacant
    exact installed (by simp [ControlFrame.viewAt, empty])
  have liveBirth : (trace.notes episode.closed).1 child = some (birthStep + 1) := by
    rw [trace.notes_eq episode.closed (Nat.le_of_lt episode.interval.bounded)]
    exact birthAt_eq_some.mpr lives
  obtain ⟨_, _, _, _, _, endpoint⟩ := (unload_boundary trace episode.interval).2
  rw [endpoint, Transposition.mark_other _ _ _ _ distinct, replay_retired]
  cases found : trace.state episode.closed child with
  | none => exact False.elim (lives.present _ lives.ordered (Nat.le_refl _) found)
  | some row =>
    have matching : ((trace.notes episode.closed).2 episode.name).any
        (Capture.retires (trace.notes episode.closed).1 child) = true :=
      List.any_eq_true.mpr ⟨_, recorded, by simp [Capture.retires, liveBirth]⟩
    simp [matching]

/-- The selected episode's retained neighbors cannot have a committed
demand on it, including neighbors whose episodes remain open. -/
theorem no_demand_on_closing (trace : Trace program last) (episode : ClosedEpisode trace)
    (maximal : ∀ later : ClosedEpisode trace, ¬ EpisodeEdge episode later)
    {consumer : Name} {key : Key} {time : Nat}
    (lower : episode.opened ≤ time) (upper : time ≤ episode.closed) :
    ¬ Ordering.Demand (trace.state time) consumer episode.name key := by
  intro demand
  have bound := episode.interval.bounded
  have installed : ControlFrame.viewAt (trace.state time) consumer ≠ none := by
    obtain ⟨fiber, view, present, _, committed, _⟩ := demand
    simp [ControlFrame.viewAt, present, committed]
  have absent : ControlFrame.viewAt (trace.state 0) consumer = none := by
    simp [trace.start, ControlFrame.viewAt]
  obtain ⟨opened, _, segment⟩ := prefix_since_absence (last := last) trace.state consumer (Nat.zero_le _) (by omega : time ≤ last)
    absent installed
  rcases prefix_closes_or_extends (last := last) trace.state segment with ⟨closed, later, clipped⟩ | full
  · exact maximal ⟨consumer, opened, closed, clipped⟩
      (.inl ⟨time, key, lower, upper, segment.ordered, later, demand⟩)
  · have atUnload := (demand_through_installation trace upper (by omega)
      (fun point after before => full.installed point (by have := segment.ordered; omega) (by omega))).mp demand
    obtain ⟨different, _⟩ := trace.supported episode.closed (by omega) consumer episode.name key atUnload
    obtain ⟨_, _, _, _, free, _⟩ := (unload_boundary trace episode.interval).2
    exact free (Ordering.demand_relied _ consumer _ key atUnload different)

theorem not_relied_in_closing (trace : Trace program last) (episode : ClosedEpisode trace)
    (maximal : ∀ later : ClosedEpisode trace, ¬ EpisodeEdge episode later)
    {time : Nat} (lower : episode.opened ≤ time) (upper : time ≤ episode.closed) :
    ¬ Relied (trace.state time) episode.name := by
  rintro ⟨consumer, _, selected⟩
  cases present : trace.state time consumer with
  | none => simp [present] at selected
  | some fiber =>
    cases view : fiber.phase.committed with
    | none => simp [present, view] at selected
    | some chosen =>
      obtain ⟨key, req, provider⟩ := by simpa [present, view] using selected
      exact no_demand_on_closing trace episode maximal lower upper
        ⟨fiber, chosen, present, req, view, provider⟩

/-- Any child allocated by this episode remains inactive throughout that
incarnation, even after the original closing event. -/
theorem child_never_installed (trace : Trace program last) (episode : ClosedEpisode trace)
    (maximal : ∀ later : ClosedEpisode trace, ¬ EpisodeEdge episode later)
    (quiet : Progress.Quiet (trace.state last))
    {birthStep time : Nat} {child : Name}
    (lower : episode.opened ≤ birthStep) (upper : birthStep < episode.closed)
    (creator : trace.actor birthStep = episode.name)
    (birthRule : EpisodeSelection.canBirth (trace.rule birthStep) = true)
    (bounded : time ≤ last) (lives : Residency trace.state child (birthStep + 1) time) :
    ControlFrame.viewAt (trace.state time) child = none := by
  apply Classical.byContradiction
  intro installed
  have bound := episode.interval.bounded
  have vacant : trace.state birthStep child = none := by
    simpa using lives.boundary.resolve_left (by omega)
  have born := lives.present (birthStep + 1) (Nat.le_refl _) lives.ordered
  have creation := (trace.actual_child_birth (by omega) birthRule vacant born).1
  rw [creator] at creation
  obtain ⟨component, initial⟩ := born_row vacant creation
  have inertAtBirth : ControlFrame.viewAt (trace.state (birthStep + 1)) child = none := by
    simp [ControlFrame.viewAt, initial, fresh, Phase.committed]
  obtain ⟨opened, earliest, segment⟩ :=
    prefix_since_absence (last := last) trace.state child lives.ordered bounded inertAtBirth installed
  rcases prefix_closes_or_extends (last := last) trace.state segment with ⟨closed, _, closedEpisode⟩ | openEpisode
  · apply maximal ⟨child, opened, closed, closedEpisode⟩
    exact .inr ⟨birthStep, lower, by omega, creation, lives.prefix opened (by omega) segment.ordered⟩
  · have livesToEnd : Residency trace.state child (birthStep + 1) last := by
      refine ⟨by have := lives.ordered; omega, ?_, lives.boundary⟩
      intro point earlier within missing
      by_cases before : point ≤ time
      · exact lives.present point earlier before missing
      · exact openEpisode.installed point (by have := segment.ordered; omega) within
          (by simp [ControlFrame.viewAt, missing])
    have flagAtClosure := child_retired_at_closure trace episode lower upper creator birthRule
      (livesToEnd.prefix episode.closed (by omega) (by omega))
    have finalRetired := retired_through_residency (last := last) trace.state
      (fun time bounded => transition_stable (trace.step time bounded).1) livesToEnd (by omega) (by omega)
      (Nat.le_refl _) flagAtClosure
    obtain ⟨row, found, notInactive⟩ := (ControlFrame.viewAt_present_iff _ _).mp
      (openEpisode.installed last openEpisode.ordered (Nat.le_refl _))
    have retired : row.retired = true := by simpa [found] using finalRetired
    have stable := quiet child row found
    cases phase : row.phase with
    | inactive => exact notInactive phase
    | active => simp [phase, Target, found, retired] at stable
    | reloading => simp [phase] at stable
    | unloading => simp [phase] at stable

theorem Trace.root_insertion (trace : Trace program last) {time : Nat} (bounded : time < last)
    (rule : trace.rule time = .insert) :
    ∃ row, trace.state (time + 1) (trace.actor time) = some row ∧ row.parent = none := by
  cases event : trace.event time with
  | lifecycle kind actor =>
    cases kind <;> simp [Trace.rule, event, eventRule, Lifecycle.rule] at rule
  | command command =>
    cases command with
    | insert name component =>
      have step := (trace.step time bounded).1
      rw [event] at step
      obtain ⟨_, endpoint⟩ := step
      exact ⟨fresh component none, by simp [Trace.actor, event, Vestigial.eventActor, Command.actor,
        Command.apply, endpoint, put_self], rfl⟩
    | retire | remove => simp [Trace.rule, event, eventRule, ExchangeReplay.commandRule] at rule

/-- A live child has its own stamped retirement in its parent's current
stack. An earlier capture at the same draw cannot witness this property. -/
theorem Trace.live_child_capture (trace : Trace program last) {time : Nat} (bounded : time ≤ last)
    {child parent : Name} {row : F} (found : trace.state time child = some row)
    (parentOf : row.parent = some parent) (live : row.retired = false) :
    ∃ birth, (trace.notes time).1 child = some birth ∧
      (⟨.retire child, birth⟩ : C) ∈ (trace.notes time).2 parent := by
  have recorded : (trace.notes time).1 child ≠ none := by
    intro missing
    have absent := (trace.births_agree time bounded child).mp missing
    rw [found] at absent
    cases absent
  cases stamp : (trace.notes time).1 child with
  | none => exact False.elim (recorded stamp)
  | some birth =>
    have tag := stamp
    rw [trace.notes_eq time bounded] at tag
    have resident := resident_of_birthAt tag
    have byTime := resident.ordered
    cases birth with
    | zero =>
      exact False.elim (resident.present 0 (Nat.le_refl _) (Nat.zero_le _) (congrFun trace.start child))
    | succ first =>
      have vacant : trace.state first child = none := by
        simpa using resident.boundary.resolve_left (by omega)
      have born := resident.present (first + 1) (Nat.le_refl _) byTime
      have inside : first < last := by omega
      have ancestry (initial : F) (initialAt : trace.state (first + 1) child = some initial)
          (cut : Nat) (lower : first + 1 ≤ cut) (upper : cut ≤ time)
          (entry : F) (entryAt : trace.state cut child = some entry) : entry.parent = initial.parent := by
        induction cut generalizing entry with
        | zero => omega
        | succ cut ih =>
          by_cases equal : cut = first
          · subst cut
            cases Option.some.inj (entryAt.symm.trans initialAt)
            rfl
          cases prior : trace.state cut child with
          | none => exact False.elim (resident.present cut (by omega) (by omega) prior)
          | some old =>
            exact ((transition_stable (trace.step cut (by omega)).1 child old entry prior entryAt).2.1).symm.trans
              (ih (by omega) (by omega) old prior)
      have native : Labeled.Step program (trace.rule first) (trace.actor first)
          (trace.state first) (trace.state (first + 1)) := by
        rcases transition_cases (trace.step first inside).1 with native | ⟨actor, _, guarded⟩
        · exact native
        · obtain ⟨_, _, _, _, _, endpoint⟩ := guarded
          exact False.elim (born (endpoint.symm ▸ (Transposition.mark_presence _ _ _ _).mpr
            ((replay_presence _ _ _ _).mpr vacant)))
      have rule : EpisodeSelection.canBirth (trace.rule first) = true := by
        rcases EpisodeBoundary.new_entry_rule native vacant born with ⟨insertion, who⟩ | grows
        · obtain ⟨root, rootAt, rootParent⟩ := trace.root_insertion inside insertion
          rw [← who] at rootAt
          rw [ancestry root rootAt time byTime (Nat.le_refl _) row found, rootParent] at parentOf
          cases parentOf
        · exact grows
      obtain ⟨creation, captured⟩ := trace.actual_child_birth inside rule vacant born
      obtain ⟨component, childAt⟩ := born_row vacant creation
      have creator := Option.some.inj ((ancestry _ childAt time byTime (Nat.le_refl _) row found).symm.trans parentOf)
      rw [creator] at captured
      have installed : ControlFrame.viewAt (trace.state (first + 1)) parent ≠ none := by
        intro missing
        have empty : PartialReplayRegistry.saved (trace.state (first + 1)) parent = [] := by
          cases parentAt : trace.state (first + 1) parent with
          | none => simp [PartialReplayRegistry.saved, parentAt]
          | some owner =>
            cases phase : owner.phase <;>
              simp_all [ControlFrame.viewAt, Phase.committed, PartialReplayRegistry.saved, Phase.accumulator]
        have noCaptures := List.map_eq_nil_iff.mp ((trace.projects (first + 1) (by omega) parent).trans empty)
        rw [noCaptures] at captured
        simp at captured
      obtain ⟨opened, _, initialEpisode⟩ := prefix_since_absence (last := last) trace.state parent
        (Nat.zero_le _) (by omega : first + 1 ≤ last) (by simp [trace.start, ControlFrame.viewAt]) installed
      rcases prefix_closes_or_extends trace.state initialEpisode with ⟨closed, afterBirth, closes⟩ | persists
      · by_cases earlier : closed < time
        · have openingBefore : opened ≤ first := by
            have before := initialEpisode.before
            have order := initialEpisode.ordered
            apply Nat.le_of_not_gt
            intro tooLate
            have equal : opened = first + 1 := by omega
            have actorInstalled : ControlFrame.viewAt (trace.state first) parent ≠ none := by
              generalize selected : trace.rule first = tag at native rule
              cases tag <;> simp [EpisodeSelection.canBirth] at rule
              all_goals
                intro missing
                exact installed ((congrFun (ControlFrame.labeled_view_cases program native) parent).trans missing)
            exact actorInstalled (by simpa [equal] using before)
          have retirement : (trace.state (closed + 1) child).map Fiber.retired = some true :=
            child_retired_at_closure trace ⟨parent, opened, closed, closes⟩ openingBefore
              (show first < closed by omega) creator rule (resident.prefix closed (by omega) (by omega))
          have retired := retired_through_residency (last := last) trace.state
            (fun cut within => transition_stable (trace.step cut within).1) resident
            (by omega) (by omega) bounded retirement
          simp [found, live] at retired
        · exact ⟨first + 1, rfl, trace.capture_through_interval parent byTime bounded
            (fun point lower upper => closes.installed point (by have := initialEpisode.ordered; omega) (by omega)) captured⟩
      · exact ⟨first + 1, rfl, trace.capture_through_interval parent byTime bounded
          (fun point lower upper => persists.installed point (by have := initialEpisode.ordered; omega) (by omega)) captured⟩

theorem Trace.child_provenance (trace : Trace program last) (time : Nat) (bounded : time ≤ last) :
    ChildProvenance.Captured (trace.state time) := by
  intro child row parent found ancestry live
  obtain ⟨birth, _, captured⟩ := trace.live_child_capture bounded found ancestry live
  have parentPresent := trace.parent_closed time bounded child row parent found ancestry
  have member : (.retire child : I) ∈ ((trace.notes time).2 parent).map Capture.token :=
    List.mem_map.mpr ⟨(⟨.retire child, birth⟩ : C), captured, rfl⟩
  rw [trace.projects time bounded parent] at member
  cases present : trace.state time parent with
  | none => exact False.elim (parentPresent present)
  | some owner => exact ⟨owner, rfl, by simpa [PartialReplayRegistry.saved, present] using member⟩

/-- Begin ranks continue to order installed edges after guarded unload.
The cleanup removes the unloader's view and preserves every surviving view. -/
theorem Trace.support_ranked (trace : Trace program last) (time : Nat) (bounded : time ≤ last) :
    SupportOrder.Ranked (trace.state time) := by
  induction time with
  | zero => rw [trace.start]; exact SupportOrder.empty_ranked
  | succ time ih =>
    obtain ⟨rank, limit, within, ordered⟩ := ih (by omega)
    have step := (trace.step time (by omega)).1
    have stable := transition_stable step
    rcases transition_views step with views | ⟨actor, _, begins⟩ | ⟨actor, _, unload⟩
    · exact ⟨rank, limit, within, SupportOrder.ordered_of_stable_views stable
        (fun name view found => (congrFun views name) ▸ found) rank ordered⟩
    · obtain ⟨row, view, found, inactive, _, ready, endpoint⟩ := begins
      rw [endpoint]
      refine ⟨SupportOrder.advance rank actor limit, limit + 1, ?_,
        SupportOrder.begin_ordered _ actor row view found inactive ready
          (trace.supported time (by omega)) (trace.child_provenance time (by omega))
          rank limit within ordered⟩
      intro name
      by_cases same : name = actor
      · simp [SupportOrder.advance, same]
      · simpa [SupportOrder.advance, same] using Nat.le_trans (within name) (Nat.le_succ limit)
    · refine ⟨rank, limit, within, SupportOrder.ordered_of_stable_views stable ?_ rank ordered⟩
      intro name view found
      rw [unload_views unload name] at found
      by_cases same : name = actor <;> simp_all

theorem Trace.support_finite (trace : Trace program last) (time : Nat) (bounded : time ≤ last) :
    SupportUniqueness.FiniteDomain (trace.state time) := by
  induction time with
  | zero =>
    rw [trace.start]
    exact ⟨[], fun _ _ found => by cases found⟩
  | succ time ih =>
    have finite := ih (by omega)
    rcases transition_cases (trace.step time (by omega)).1 with native | ⟨actor, _, unload⟩
    · exact SupportUniqueness.calculus_step_finite program native.toCalculus finite
    · obtain ⟨names, covers⟩ := finite
      obtain ⟨_, _, _, _, _, endpoint⟩ := unload
      refine ⟨names, fun name row found => ?_⟩
      cases prior : trace.state time name with
      | some old => exact covers name old prior
      | none =>
        rw [endpoint, (Transposition.mark_presence _ _ _ _).mpr
          ((replay_presence _ _ _ _).mpr prior)] at found
        cases found

theorem Trace.table_scope (trace : Trace program last) (time : Nat) (bounded : time ≤ last) :
    TableFrame.ScopedAccumulators (trace.state time) := by
  intro name row found token stored
  have scope := (trace.invariants time bounded).2 name row found token stored
  cases token with
  | unit | retire => trivial
  | restrict => exact scope
  | operate => exact scope.imp_right fun ⟨_, _, declared, _⟩ => declared

private theorem discharge_keeps_empty (state : R) (word : List I) (name : Name) (key : Key)
    (empty : tableAt state name key = none) :
    tableAt (discharge Stages.undo word state) name key = none := by
  induction word generalizing state with
  | nil => exact empty
  | cons token rest ih =>
    apply ih
    cases token with
    | unit => exact empty
    | retire => simpa only [Stages.undo, tableAt_retire] using empty
    | restrict => rw [tableAt_restrict, empty]; split <;> rfl
    | operate =>
      rw [tableAt_operate]
      split
      · rename_i same
        rcases same with ⟨rfl, rfl⟩
        rw [empty]
        rfl
      · exact empty

private theorem empty_table_from_birth (trace : Trace program last) {birthStep time : Nat} {parent child : Name}
    (bounded : time ≤ last) (lives : Residency trace.state child (birthStep + 1) time)
    (vacant : trace.state birthStep child = none)
    (creation : Transposition.CreatesChild program parent (trace.state birthStep)
      (trace.state (birthStep + 1)) child)
    (noView : ∀ t, birthStep < t → t ≤ time → ControlFrame.viewAt (trace.state t) child = none)
    {row : F} (found : trace.state time child = some row) : ∀ key, row.table key = none := by
  induction time generalizing row with
  | zero => have := lives.ordered; omega
  | succ time ih =>
    by_cases first : time = birthStep
    · subst time
      obtain ⟨component, new⟩ := born_row vacant creation
      have same := Option.some.inj (new.symm.trans found)
      subst row
      intro key
      rfl
    · have born : birthStep + 1 ≤ time := by have := lives.ordered; omega
      cases before : trace.state time child with
      | none => exact False.elim (lives.present time born (by omega) before)
      | some old =>
        have empty := ih (by omega) (lives.prefix time born (by omega))
          (fun t lo hi => noView t lo (by omega)) before
        rcases transition_cases (trace.step time (by omega)).1 with native | ⟨actor, _, guarded⟩
        · exact empty_table_during_inactivity native (trace.table_scope time (by omega)) before found
            (noView time (by omega) (by omega)) (noView (time + 1) (by omega) (by omega)) empty
        · intro key
          obtain ⟨_, _, _, _, _, endpoint⟩ := guarded
          have realized := congrArg (fun state => tableAt state child key) endpoint
          dsimp only at realized
          rw [tableAt_mark] at realized
          have replayed := replay_tables (trace.notes time).1 ((trace.notes time).2 actor)
            (left := trace.state time) (right := trace.state time) (fun _ _ => rfl) child key
          have stillEmpty := discharge_keeps_empty (trace.state time)
            (((trace.notes time).2 actor).map Capture.token) child key (by simpa [tableAt, before] using empty key)
          simpa only [tableAt, found, Option.bind_some] using realized.trans (replayed.symm.trans stillEmpty)

private theorem leaf_from_birth (trace : Trace program last) {birthStep time : Nat} {parent child : Name}
    (earlier : birthStep < time) (bounded : time ≤ last)
    (vacant : trace.state birthStep child = none)
    (creation : Transposition.CreatesChild program parent (trace.state birthStep) (trace.state (birthStep + 1)) child)
    (noView : ∀ t, birthStep < t → t ≤ time → ControlFrame.viewAt (trace.state t) child = none) :
    Leaf (trace.state time) child := by
  induction time with
  | zero => omega
  | succ time ih =>
    by_cases first : time = birthStep
    · subst time
      exact leaf_at_birth (trace.parent_closed birthStep (by omega)) vacant creation
    · have previous := ih (by omega) (by omega) (fun t lo hi => noView t lo (by omega))
      have step := (trace.step time (by omega)).1
      rcases transition_cases step with native | ⟨actor, _, guarded⟩
      · exact new_parent_requires_view native (trace.root_insertion (by omega))
          (noView time (by omega) (by omega)) previous
      · intro other row found childOf
        cases oldAt : trace.state time other with
        | none =>
          obtain ⟨_, _, _, _, _, endpoint⟩ := guarded
          rw [endpoint, (Transposition.mark_presence _ _ _ _).mpr
            ((replay_presence _ _ _ _).mpr oldAt)] at found
          cases found
        | some old =>
          have preserved := (transition_stable step other old row oldAt found).2.1
          exact previous other old oldAt (preserved.trans childOf)

/-- The guarded closing cut itself meets the vestige-suffix premises for
every surviving child allocated by the selected episode. -/
theorem closing_child_is_vestigial (trace : Trace program last) (episode : ClosedEpisode trace)
    (maximal : ∀ later : ClosedEpisode trace, ¬ EpisodeEdge episode later)
    (quiet : Progress.Quiet (trace.state last))
    {birthStep : Nat} {child : Name}
    (lower : episode.opened ≤ birthStep) (upper : birthStep < episode.closed)
    (creator : trace.actor birthStep = episode.name)
    (birthRule : EpisodeSelection.canBirth (trace.rule birthStep) = true)
    (lives : Residency trace.state child (birthStep + 1) episode.closed) :
    Removable (trace.state (episode.closed + 1)) child ∧
      rootAt (trace.state (episode.closed + 1)) child = false := by
  have bound := episode.interval.bounded
  have vacant : trace.state birthStep child = none := by
    simpa using lives.boundary.resolve_left (by omega)
  have born := lives.present (birthStep + 1) (Nat.le_refl _) lives.ordered
  have creation := (trace.actual_child_birth (by omega) birthRule vacant born).1
  rw [creator] at creation
  have flag := child_retired_at_closure trace episode lower upper creator birthRule lives
  cases after : trace.state (episode.closed + 1) child with
  | none => simp [after] at flag
  | some row =>
    have continued : Residency trace.state child (birthStep + 1) (episode.closed + 1) := by
      refine ⟨by omega, ?_, lives.boundary⟩
      intro time bornAt latest vacantAt
      by_cases before : time ≤ episode.closed
      · exact lives.present time bornAt before vacantAt
      · have lastCut : time = episode.closed + 1 := by omega
        rw [lastCut, after] at vacantAt
        cases vacantAt
    have inert (time : Nat) (early : birthStep < time) (late : time ≤ episode.closed + 1) :
        ControlFrame.viewAt (trace.state time) child = none :=
      child_never_installed trace episode maximal quiet lower upper creator birthRule (by omega)
        (continued.prefix time (by omega) late)
    have inactive := inert (episode.closed + 1) (by omega) (Nat.le_refl _)
    have phase : row.phase = .inactive := by
      cases current : row.phase <;> simp [ControlFrame.viewAt, after, current, Phase.committed] at inactive ⊢
    have empty := empty_table_from_birth trace (by omega) continued vacant creation inert after
    have leaf := leaf_from_birth trace (by omega) (by omega) vacant creation inert
    obtain ⟨component, start⟩ := born_row vacant creation
    have parent := (continued.metadata_of_stable (last := last)
      (fun time bounded => transition_stable (trace.step time bounded).1) (by omega) start after).2.symm
    constructor
    · rw [Removable, after]
      refine ⟨by simpa [after] using flag, phase, empty, ?_⟩
      intro other
      cases found : trace.state (episode.closed + 1) other with
      | none => trivial
      | some entry => exact leaf other entry found
    · simp [rootAt, after, parent, fresh]

def withdraws (trace : Trace program last) (episode : ClosedEpisode trace) (time : Nat) (name : Name) : Bool :=
  ((trace.notes time).2 episode.name).any (Capture.retires (trace.notes time).1 name)

def rollbackOf (trace : Trace program last) (episode : ClosedEpisode trace) (time : Nat) (state : R) : R :=
  let reverted := replay (trace.notes time).1 ((trace.notes time).2 episode.name) state
  fun name => if withdraws trace episode time name then none else mark reverted episode.name .inactive name

def probeAt (trace : Trace program last) (episode : ClosedEpisode trace) (time : Nat) : R :=
  rollbackOf trace episode time (trace.state time)

def probeNotes (trace : Trace program last) (episode : ClosedEpisode trace) (time : Nat) : Notes :=
  (fun name => if withdraws trace episode time name then none else (trace.notes time).1 name,
    fun name => if name = episode.name then [] else (trace.notes time).2 name)

theorem probe_births (trace : Trace program last) (episode : ClosedEpisode trace) (time : Nat)
    (bounded : time ≤ last) : GuardedSuffix.BirthsAgree (probeAt trace episode time) (probeNotes trace episode time) := by
  intro name
  by_cases hidden : withdraws trace episode time name = true
  · simp [probeNotes, probeAt, rollbackOf, hidden]
  · simp only [probeNotes, probeAt, rollbackOf, if_neg hidden, Transposition.mark_presence, replay_presence]
    exact trace.births_agree time bounded name

theorem empty_on_entry (trace : Trace program last) (episode : ClosedEpisode trace) :
    (trace.notes episode.opened).2 episode.name = [] := by
  have order := episode.interval.ordered
  have bound := episode.interval.bounded
  obtain ⟨row, view, found, _, _, _, endpoint⟩ := (begin_boundary trace episode.interval).2
  have empty : PartialReplayRegistry.saved (trace.state episode.opened) episode.name = [] := by
    rw [endpoint, PartialReplayRegistry.saved, mark_self _ _ _ _ found]
    rfl
  exact List.map_eq_nil_iff.mp ((trace.projects episode.opened (by omega) episode.name).trans empty)

/-- A mask bit identifies a specific child landing of the closing episode,
using the actual stack position and live birth. -/
theorem withdrawn_birth (trace : Trace program last) (episode : ClosedEpisode trace)
    {time : Nat} (lower : episode.opened ≤ time) (upper : time ≤ episode.closed)
    {child : Name} (withdrawn : withdraws trace episode time child = true) :
    ∃ birthStep, episode.opened ≤ birthStep ∧ birthStep < episode.closed ∧
      trace.actor birthStep = episode.name ∧ EpisodeSelection.canBirth (trace.rule birthStep) = true ∧
      Residency trace.state child (birthStep + 1) time := by
  have bound := episode.interval.bounded
  obtain ⟨capture, recorded, matchBirth⟩ := List.any_eq_true.mp withdrawn
  cases token : capture.token with
  | retire target =>
    have matching : child = target ∧ (trace.notes time).1 target = some capture.index := by
      simpa [Capture.retires, token] using matchBirth
    obtain ⟨rfl, current⟩ := matching
    rw [trace.notes_eq time (by omega)] at current
    have initial := empty_on_entry trace episode
    rw [trace.notes_eq episode.opened (by omega)] at initial
    have ⟨captureBound, origin⟩ := trace.capture_origin time (by omega) episode.name capture recorded
    obtain ⟨birthStep, inRange, stamp, creator, _, _, _, _, _, _⟩ := origin
    have recorded' := recorded
    rw [trace.notes_eq time (by omega)] at recorded'
    have age := capture_after_empty trace.state trace.actor episode.name lower initial recorded'
    have residency : Residency trace.state child (birthStep + 1) time :=
      resident_of_birthAt (current.trans (congrArg some stamp))
    have vacant : trace.state birthStep child = none := by
      simpa using residency.boundary.resolve_left (by omega)
    have born := residency.present (birthStep + 1) (Nat.le_refl _) residency.ordered
    have step := (trace.step birthStep inRange).1
    have birthRule : EpisodeSelection.canBirth (trace.rule birthStep) = true := by
      rcases transition_cases step with native | ⟨actor, _, unload⟩
      · rcases EpisodeBoundary.new_entry_rule native vacant born with ⟨_, same⟩ | allocation
        · have isActor : child = episode.name := same.trans creator
          have missing : trace.state birthStep episode.name = none := isActor ▸ vacant
          exact False.elim (episode.interval.installed birthStep (by omega) (by omega)
            (by simp [ControlFrame.viewAt, missing]))
        · exact allocation
      · obtain ⟨_, _, _, _, _, endpoint⟩ := unload
        exact False.elim (born (endpoint.symm ▸ (Transposition.mark_presence _ _ _ _).mpr
          ((replay_presence _ _ _ _).mpr vacant)))
    exact ⟨birthStep, by omega, by omega, creator, birthRule, residency⟩
  | _ => simp [Capture.retires, token] at matchBirth

/-- Hiding the selected episode's inert children and clearing its phase
leaves every table of the actual rollback intact. -/
theorem probe_replay_tables (trace : Trace program last) (episode : ClosedEpisode trace)
    (maximal : ∀ later : ClosedEpisode trace, ¬ EpisodeEdge episode later)
    (quiet : Progress.Quiet (trace.state last))
    {time : Nat} (lower : episode.opened ≤ time) (upper : time ≤ episode.closed) :
    RuleEvaluation.TablesUnchanged
      (replay (trace.notes time).1 ((trace.notes time).2 episode.name) (trace.state time))
      (probeAt trace episode time) := by
  intro name key
  have bounded := episode.interval.bounded
  by_cases hidden : withdraws trace episode time name = true
  · obtain ⟨birth, earliest, latest, creator, rule, lives⟩ := withdrawn_birth trace episode lower upper hidden
    have vacant : trace.state birth name = none := by
      simpa using lives.boundary.resolve_left (by omega)
    have born := lives.present (birth + 1) (Nat.le_refl _) lives.ordered
    have creation := (trace.actual_child_birth (by omega) rule vacant born).1
    have dormant (cut : Nat) (later : birth < cut) (earlier : cut ≤ time) :
        ControlFrame.viewAt (trace.state cut) name = none :=
      child_never_installed trace episode maximal quiet earliest latest creator rule (by omega)
        (lives.prefix cut (by omega) earlier)
    have empty : tableAt (trace.state time) name key = none := by
      cases found : trace.state time name with
      | none => simp [tableAt, found]
      | some row =>
        simp only [tableAt, found, Option.bind_some]
        exact empty_table_from_birth trace (by omega) lives vacant creation dormant found key
    have native := discharge_keeps_empty (trace.state time) (((trace.notes time).2 episode.name).map Capture.token)
      name key empty
    have reverted := (replay_tables (trace.notes time).1 ((trace.notes time).2 episode.name)
      (left := trace.state time) (right := trace.state time) (fun _ _ => rfl)) name key
    rw [← reverted, native]
    simp [tableAt, probeAt, rollbackOf, hidden]
  · have kept : probeAt trace episode time name = mark
        (replay (trace.notes time).1 ((trace.notes time).2 episode.name) (trace.state time))
        episode.name .inactive name := by simp [probeAt, rollbackOf, hidden]
    change _ = (probeAt trace episode time name).bind (fun row => row.table key)
    rw [kept]
    exact (StageRecovery.tableAt_mark _ _ _ _ _).symm

theorem closing_withdrawals (trace : Trace program last) (episode : ClosedEpisode trace)
    (maximal : ∀ later : ClosedEpisode trace, ¬ EpisodeEdge episode later)
    (quiet : Progress.Quiet (trace.state last)) :
    ∃ names : List Name, names.Nodup ∧ (∀ name, name ∈ names ↔ withdraws trace episode episode.closed name = true) ∧
      probeAt trace episode episode.closed = Vestigial.eraseAll names (trace.state (episode.closed + 1)) ∧
      probeNotes trace episode episode.closed = GuardedSuffix.eraseAllNotes names (trace.notes (episode.closed + 1)) ∧
      ∀ name ∈ names, Removable (trace.state (episode.closed + 1)) name ∧
        rootAt (trace.state (episode.closed + 1)) name = false := by
  let time := episode.closed
  have bound := episode.interval.bounded
  obtain ⟨names, unique, membership⟩ :=
    EpisodeClosure.matching_children (trace.notes time).1 ((trace.notes time).2 episode.name)
  change (∀ name, name ∈ names ↔ withdraws trace episode time name = true) at membership
  have children (name : Name) (member : name ∈ names) :
      Removable (trace.state (time + 1)) name ∧ rootAt (trace.state (time + 1)) name = false := by
    obtain ⟨birth, lower, upper, creator, rule, lives⟩ :=
      withdrawn_birth trace episode episode.interval.ordered (Nat.le_refl _) ((membership name).mp member)
    exact closing_child_is_vestigial trace episode maximal quiet lower upper creator rule lives
  obtain ⟨event, row, view, found, phase, free, endpoint⟩ := unload_boundary trace episode.interval
  have updated := trace.unload_notes bound (show trace.event time = .lifecycle .unload episode.name from event)
  have bornIdentical (name : Name) : (trace.notes (time + 1)).1 name = (trace.notes time).1 name :=
    congrFun (congrArg Prod.fst updated) name
  have stacks (name : Name) : (trace.notes (time + 1)).2 name =
      if name = episode.name then [] else (trace.notes time).2 name :=
    congrArg (fun notes : Notes => notes.2 name) updated
  refine ⟨names, unique, membership, ?_, ?_, children⟩
  · funext name
    rw [Vestigial.eraseAll_apply]
    change (if withdraws trace episode time name then none else
      mark (replay (trace.notes time).1 ((trace.notes time).2 episode.name) (trace.state time))
        episode.name .inactive name) = _
    rw [← endpoint]
    by_cases member : name ∈ names
    · rw [if_pos member, if_pos ((membership name).mp member)]
    · rw [if_neg member, if_neg (fun withdrawn => member ((membership name).mpr withdrawn))]
  · rw [GuardedSuffix.eraseAllNotes_apply]
    apply Prod.ext
    · funext name
      change (if withdraws trace episode time name then none else (trace.notes time).1 name) =
        if name ∈ names then none else (trace.notes (time + 1)).1 name
      rw [bornIdentical]
      by_cases member : name ∈ names
      · rw [if_pos member, if_pos ((membership name).mp member)]
      · rw [if_neg member, if_neg (fun withdrawn => member ((membership name).mpr withdrawn))]
    · funext name
      change (if name = episode.name then [] else (trace.notes time).2 name) =
        if name ∈ names then [] else (trace.notes (time + 1)).2 name
      rw [← stacks]
      by_cases member : name ∈ names
      · rw [if_pos member]
        have ready := (children name member).1
        cases current : trace.state (time + 1) name with
        | none => simp [Removable, current] at ready
        | some entry =>
          rw [Removable, current] at ready
          have phase : entry.phase = .inactive := ready.2.1
          have projected := trace.projects (time + 1) (by omega) name
          have empty : ((trace.notes (time + 1)).2 name).map Capture.token = [] := by
            simpa [PartialReplayRegistry.saved, current, phase, Phase.accumulator] using projected
          exact List.map_eq_nil_iff.mp empty
      · rw [if_neg member]

/-- Excision's suffix is the actual guarded source suffix with exactly the
selected vestiges erased until their original removals. -/
theorem project_suffix (trace : Trace program last) (episode : ClosedEpisode trace)
    (maximal : ∀ later : ClosedEpisode trace, ¬ EpisodeEdge episode later)
    (quiet : Progress.Quiet (trace.state last)) :
    let start := episode.closed + 1
    let cuts := List.range' start (last - start)
    let events := cuts.map fun time => (time + 1, trace.event time)
    let roots := cuts.flatMap fun time => eventRoots (trace.state time) (trace.event time)
    ∃ names, names.Nodup ∧ (∀ name, name ∈ names ↔ withdraws trace episode episode.closed name = true) ∧
      GuardedSuffix.ExecWith program trace.sourceAt (GuardedSuffix.pruneAll names events)
        (probeAt trace episode episode.closed) (probeNotes trace episode episode.closed)
        (Vestigial.eraseAll (GuardedSuffix.stillPresent names events) (trace.state last))
        (GuardedSuffix.eraseAllNotes (GuardedSuffix.stillPresent names events) (trace.notes last)) roots ∧
      ∀ name ∈ GuardedSuffix.stillPresent names events, Removable (trace.state last) name ∧
        rootAt (trace.state last) name = false := by
  dsimp only
  have bound := episode.interval.bounded
  have full := trace.source_segment (episode.closed + 1) (last - (episode.closed + 1)) (by omega)
  rw [show episode.closed + 1 + (last - (episode.closed + 1)) = last by omega] at full
  obtain ⟨names, unique, members, registry, notes, children⟩ := closing_withdrawals trace episode maximal quiet
  have projected := GuardedSuffix.prune_all full names unique (trace.births_agree _ (by omega)) children
  rw [← registry, ← notes] at projected
  refine ⟨names, unique, members, projected, ?_⟩
  intro name retained
  have ⟨member, still⟩ := List.mem_filter.mp retained
  obtain ⟨ready, child⟩ := children name member
  exact GuardedSuffix.remaining_vestige full name ready child (by simpa using still)

end Cordis.Repairs.GuardedHistory
