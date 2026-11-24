import Cordis.Repairs.GuardedHistory

/-! Provider and child edges of the repaired Lemma 79 over the actual
guarded source history. Only the guarded L-Unload closes an episode. -/
namespace Cordis.Repairs.GuardedHistory
open Calculus Stages LegalHistory Incarnation IncarnationReplay
open Vestigial (CutNotes)
universe u
variable {Name Key Value Code Error : Type u} [DecidableEq Name] [DecidableEq Key]
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "C" => Capture Name Key Value
local notation "Ev" => Event Name Key Code
local notation "Notes" => CutNotes Name Key Value
variable {program : Code → Instruction Name Key Value Code Error} {last : Nat}

theorem transition_views {event : Ev} {before after : R} {notes : Notes}
    (step : GuardedSuffix.Transition program notes event before after) :
    ControlFrame.viewAt after = ControlFrame.viewAt before ∨
      (∃ actor, event = .lifecycle .begin actor ∧ ControlFrame.BeginsAt before after actor) ∨
      (∃ actor, event = .lifecycle .unload actor ∧ GuardedSuffix.Unload actor before notes after) := by
  cases event with
  | command command =>
    have facts := ControlFrame.labeled_view_cases program (ExchangeReplay.command_labeled (program := program) command step)
    cases command <;> exact .inl facts
  | lifecycle kind actor =>
    cases kind
    case begin => exact .inr (.inl ⟨actor, rfl, ControlFrame.labeled_view_cases program step⟩)
    case unload => exact .inr (.inr ⟨actor, rfl, step⟩)
    all_goals exact .inl (ControlFrame.labeled_view_cases program step)

theorem begin_at_view_change (trace : Trace program last) {actor : Name} {time : Nat}
    (bounded : time < last) (outside : ControlFrame.viewAt (trace.state time) actor = none)
    (inside : ControlFrame.viewAt (trace.state (time + 1)) actor ≠ none) :
    trace.event time = .lifecycle .begin actor ∧
      ControlFrame.BeginsAt (trace.state time) (trace.state (time + 1)) actor := by
  have views := transition_views (trace.step time bounded).1
  rcases views with remains | ⟨opener, rule, begins⟩ | ⟨other, _, unload⟩
  · exact False.elim (inside ((congrFun remains actor).trans outside))
  · by_cases same : actor = opener
    · subst opener
      exact ⟨rule, begins⟩
    · obtain ⟨before, view, found, _, _, _, endpoint⟩ := begins
      rw [endpoint, ControlFrame.mark_viewAt _ _ _ _ found, if_neg same] at inside
      exact False.elim (inside outside)
  · have gone := unload_views unload actor
    rw [outside] at gone
    exact False.elim (inside (by simpa using gone))

theorem begin_boundary (trace : Trace program last) {actor : Name} {opened closed : Nat}
    (episode : Indexed.EpisodeAtOn trace.state last actor opened closed) :
    trace.event (opened - 1) = .lifecycle .begin actor ∧
      ControlFrame.BeginsAt (trace.state (opened - 1)) (trace.state opened) actor := by
  have positive := episode.positive
  have order := episode.ordered
  have bound := episode.bounded
  have next : opened - 1 + 1 = opened := by omega
  have begins := begin_at_view_change trace (by omega) episode.before (by
    rw [next]
    exact episode.installed opened (Nat.le_refl _) order)
  simpa only [next] using begins

theorem unload_boundary (trace : Trace program last) {actor : Name} {opened closed : Nat}
    (episode : Indexed.EpisodeAtOn trace.state last actor opened closed) :
    trace.event closed = .lifecycle .unload actor ∧
      GuardedSuffix.Unload actor (trace.state closed) (trace.notes closed) (trace.state (closed + 1)) := by
  have inside := episode.installed closed episode.ordered (Nat.le_refl _)
  rcases transition_views (trace.step closed episode.bounded).1 with remains | ⟨other, _, begins⟩ | ⟨unloader, rule, unload⟩
  · exact False.elim (inside ((congrFun remains actor).symm.trans episode.after))
  · obtain ⟨before, view, found, _, _, _, endpoint⟩ := begins
    have gone := episode.after
    rw [endpoint, ControlFrame.mark_viewAt _ _ _ _ found] at gone
    by_cases same : actor = other
    · simp [same, Phase.committed] at gone
    · exact False.elim (inside (by simpa [same] using gone))
  · by_cases same : actor = unloader
    · subst unloader
      exact ⟨rule, unload⟩
    · have gone := unload_views unload actor
      rw [if_neg same, episode.after] at gone
      exact False.elim (inside gone.symm)

private theorem replay_demand (live : Name → Option Nat) (word : List C) (state : R) (consumer provider : Name) (key : Key) :
    Ordering.Demand state consumer provider key ↔ Ordering.Demand (replay live word state) consumer provider key := by
  cases before : state consumer with
  | none => simp [Ordering.Demand, before, (replay_presence live word state consumer).mpr before]
  | some row =>
    obtain ⟨retained, found, component, _, phase⟩ := replay_keeps_control live word state consumer row before
    simp [Ordering.Demand, before, found, component, phase]

private theorem demand_step {event : Ev} {before after : R} {notes : Notes}
    {consumer provider : Name} {key : Key}
    (step : GuardedSuffix.Transition program notes event before after)
    (old : ControlFrame.viewAt before consumer ≠ none) (new : ControlFrame.viewAt after consumer ≠ none) :
    Ordering.Demand before consumer provider key ↔ Ordering.Demand after consumer provider key := by
  rcases transition_cases step with native | ⟨actor, _, unload⟩
  · exact EpisodeDependencies.demand_step native old new
  · have different : consumer ≠ actor := fun same => new ((unload_views unload consumer).trans (if_pos same))
    obtain ⟨row, view, present, phase, free, rfl⟩ := unload
    have stable := replay_demand notes.1 (notes.2 actor) before consumer provider key
    simpa only [Ordering.Demand, Transposition.mark_other _ _ _ _ different] using stable

theorem demand_through_installation (trace : Trace program last) {consumer provider : Name} {key : Key}
    {first time : Nat} (lower : first ≤ time) (bounded : time ≤ last)
    (installed : ∀ point, first ≤ point → point ≤ time → ControlFrame.viewAt (trace.state point) consumer ≠ none) :
    Ordering.Demand (trace.state first) consumer provider key ↔ Ordering.Demand (trace.state time) consumer provider key := by
  induction time with
  | zero =>
    have same : first = 0 := by omega
    rw [same]
  | succ time ih =>
    by_cases same : first = time + 1
    · rw [same]
    · have earlier := ih (by omega) (by omega) (fun point after before => installed point after (by omega))
      exact earlier.trans (demand_step (trace.step time (by omega)).1
        (installed time (by omega) (by omega)) (installed (time + 1) lower (Nat.le_refl _)))

/-- A required provider supplies the key throughout an installed interval
with a single actual birth stamp. This includes retired providers whose
bindings are still retained by the consumer's committed view. -/
theorem provider_birth_through_installation (trace : Trace program last)
    {consumer provider : Name} {key : Key} {first time : Nat} (lower : first ≤ time) (bounded : time ≤ last)
    (installed : ∀ point, first ≤ point → point ≤ time → ControlFrame.viewAt (trace.state point) consumer ≠ none)
    (demand : Ordering.Demand (trace.state first) consumer provider key) :
    ∃ birth, Residency trace.state provider birth time ∧
      ∀ point, first ≤ point → point ≤ time →
        (trace.notes point).1 provider = some birth ∧ Ordering.Supply (trace.state point) provider key := by
  have supplies (point : Nat) (after : first ≤ point) (before : point ≤ time) :
      Ordering.Supply (trace.state point) provider key :=
    (trace.supported point (by omega) consumer provider key
      ((demand_through_installation trace after (by omega)
        (fun cut start finish => installed cut start (by omega))).mp demand)).2
  have present (point : Nat) (after : first ≤ point) (before : point ≤ time) :
      trace.state point provider ≠ none := by
    obtain ⟨row, found, _, _⟩ := supplies point after before
    simp [found]
  cases initial : birthAt trace.state provider first with
  | none => exact False.elim (present first (Nat.le_refl _) lower (birthAt_none.mp initial))
  | some birth =>
    have prior := resident_of_birthAt initial
    have birthBound := prior.ordered
    have residency : Residency trace.state provider birth time := by
      refine ⟨by omega, ?_, prior.boundary⟩
      intro point after before
      by_cases earlier : point ≤ first
      · exact prior.present point after earlier
      · exact present point (by omega) before
    refine ⟨birth, residency, fun point after before => ⟨?_, supplies point after before⟩⟩
    rw [trace.notes_eq point (by omega)]
    exact birthAt_eq_some.mpr (residency.prefix point (by omega) before)

theorem demand_in_episode (trace : Trace program last) {consumer provider : Name} {key : Key} {opened closed : Nat}
    (episode : Indexed.EpisodeAtOn trace.state last consumer opened closed) (time : Nat) (lower : opened ≤ time) (upper : time ≤ closed) :
    Ordering.Demand (trace.state opened) consumer provider key ↔ Ordering.Demand (trace.state time) consumer provider key := by
  have bound := episode.bounded
  exact demand_through_installation trace lower (by omega)
    (fun point after before => episode.installed point after (by omega))

theorem provider_during_episode (trace : Trace program last) {consumer provider : Name} {key : Key} {opened closed : Nat}
    (episode : Indexed.EpisodeAtOn trace.state last consumer opened closed)
    (demand : Ordering.Demand (trace.state opened) consumer provider key) (time : Nat) (lower : opened ≤ time) (upper : time ≤ closed) :
    ControlFrame.viewAt (trace.state time) provider ≠ none := by
  have bound := episode.bounded
  obtain ⟨_, row, present, retained, _⟩ := trace.supported time (by omega) consumer provider key
    ((demand_in_episode trace episode time lower upper).mp demand)
  cases phase : row.phase <;> simp [phase, Ordering.Retained] at retained <;>
    simp [ControlFrame.viewAt, present, phase, Phase.committed]

theorem provider_strictly_encloses (trace : Trace program last)
    {consumer provider : Name} {key : Key} {b u providerBegin providerEnd time : Nat}
    (episode : Indexed.EpisodeAtOn trace.state last consumer b u)
    (providing : Indexed.EpisodeAtOn trace.state last provider providerBegin providerEnd)
    (lower : b ≤ time) (upper : time ≤ u) (providerLower : providerBegin ≤ time) (providerUpper : time ≤ providerEnd)
    (demand : Ordering.Demand (trace.state time) consumer provider key) : providerBegin < b ∧ u < providerEnd := by
  have original := (demand_in_episode trace episode time lower upper).mpr demand
  have present := EpisodeDependencies.provider_before_opening (begin_boundary trace episode).2 original
  have positive := episode.positive
  have lastConsumer := episode.bounded
  have earlier : providerBegin < b := by
    by_cases same : providerBegin = b
    · exact False.elim (present (same ▸ providing.before))
    · by_cases startsBefore : providerBegin < b
      · exact startsBefore
      · exact False.elim (provider_during_episode trace episode original (providerBegin - 1)
          (by omega) (by omega) providing.before)
  refine ⟨earlier, ?_⟩
  by_cases closesTogether : providerEnd = u
  · have finalDemand := (demand_in_episode trace episode u episode.ordered (Nat.le_refl _)).mp original
    obtain ⟨different, _⟩ := trace.supported u (by omega) consumer provider key finalDemand
    obtain ⟨row, view, present, phase, free, _⟩ := (unload_boundary trace providing).2
    rw [closesTogether] at free
    exact False.elim (free (Ordering.demand_relied _ _ _ _ finalDemand different))
  · by_cases endsAfter : u < providerEnd
    · exact endsAfter
    · exact False.elim (provider_during_episode trace episode original (providerEnd + 1)
        (by omega) (by omega) providing.after)

structure ClosedEpisode (trace : Trace program last) where
  name : Name
  opened : Nat
  closed : Nat
  interval : Indexed.EpisodeAtOn trace.state last name opened closed

def EpisodeEdge {trace : Trace program last} (earlier later : ClosedEpisode trace) : Prop :=
  (∃ time key, earlier.opened ≤ time ∧ time ≤ earlier.closed ∧
    later.opened ≤ time ∧ time ≤ later.closed ∧ Ordering.Demand (trace.state time) later.name earlier.name key) ∨
  (∃ time, earlier.opened ≤ time ∧ time ≤ earlier.closed ∧
    Transposition.CreatesChild program earlier.name (trace.state time) (trace.state (time + 1)) later.name ∧
    Residency trace.state later.name (time + 1) later.opened)

theorem episode_edge_earlier {trace : Trace program last} {earlier later : ClosedEpisode trace}
    (edge : EpisodeEdge earlier later) : earlier.opened < later.opened := by
  rcases edge with ⟨time, key, providerStart, providerEnd, start, finish, demand⟩ |
    ⟨time, created, _, _, residency⟩
  · exact (provider_strictly_encloses trace later.interval earlier.interval start finish providerStart providerEnd demand).1
  · have bornBefore := residency.ordered
    omega

/-- The latest actual Begin has no outward edge to another closing
episode under the same guarded rules used for the suffix. -/
theorem select_closing (trace : Trace program last) (closed : Nonempty (ClosedEpisode trace)) :
    ∃ selected : ClosedEpisode trace, ∀ later : ClosedEpisode trace, ¬ EpisodeEdge selected later := by
  let eligible (time : Nat) := ∃ episode : ClosedEpisode trace, episode.opened = time
  have bound (episode : ClosedEpisode trace) : episode.opened < last :=
    Nat.lt_of_le_of_lt episode.interval.ordered episode.interval.bounded
  obtain ⟨episode⟩ := closed
  obtain ⟨index, _, ⟨selected, found⟩, greatest⟩ :=
    EpisodeDependencies.latest_index eligible last ⟨episode.opened, bound episode, episode, rfl⟩
  refine ⟨selected, fun later edge => ?_⟩
  have before := episode_edge_earlier edge
  have latest := greatest later.opened (bound later) ⟨later, rfl⟩
  omega

end Cordis.Repairs.GuardedHistory
