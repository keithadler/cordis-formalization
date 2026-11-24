import Cordis.OrderingIntervals
import Cordis.TranspositionRetirement
import Cordis.Repairs.Incarnation

/-!
Actual dependency edges between episodes. A committed provider is installed
before the consumer begins and remains installed until after the consumer
unloads. This order uses episode indices and can distinguish successive
episodes or incarnations at a reusable name.
-/
namespace Cordis.Repairs.EpisodeDependencies

open Calculus Stages Indexed
universe u
variable {Name Key Value Code Error : Type u} [DecidableEq Name] [DecidableEq Key]
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "Program" => Code → Instruction Name Key Value Code Error
variable {program : Code → Instruction Name Key Value Code Error}
variable {initial : Registry Name Key Value Code (Inverse Name Key Value) Error} {last : Nat}

theorem begin_boundary (trace : Trace program initial last)
    {name : Name} {b u : Nat} (episode : EpisodeAt trace name b u) :
    ControlFrame.BeginsAt (trace.state (b - 1)) (trace.state b) name := by
  have positive := episode.positive
  have order := episode.ordered
  have bound := episode.bounded
  have next : b - 1 + 1 = b := by omega
  have step := (trace.step (b - 1) (by omega)).toCalculus
  rw [next] at step
  have installed := episode.installed b (Nat.le_refl _) order
  rcases ControlFrame.step_view_cases program step with same | ⟨actor, begins⟩ | ⟨actor, unloads⟩
  · exact False.elim (installed (congrFun same name |>.trans episode.before))
  · by_cases acts : name = actor
    · exact acts ▸ begins
    · obtain ⟨fiber, view, present, _, _, _, endpoint⟩ := begins
      rw [endpoint, ControlFrame.mark_viewAt _ _ _ _ present, if_neg acts] at installed
      exact False.elim (installed episode.before)
  · obtain ⟨fiber, word, view, present, _, _, endpoint⟩ := unloads
    obtain ⟨retained, retainedAt, _⟩ := Ordering.discharge_existing_phases _ word actor fiber present
    rw [endpoint, ControlFrame.mark_viewAt _ _ _ _ retainedAt] at installed
    simp [Phase.committed, ControlFrame.discharge_views, episode.before] at installed

theorem unload_boundary (trace : Trace program initial last)
    {name : Name} {b u : Nat} (episode : EpisodeAt trace name b u) :
    ControlFrame.UnloadsAt (trace.state u) (trace.state (u + 1)) name := by
  have step := (trace.step u episode.bounded).toCalculus
  have installed := episode.installed u episode.ordered (Nat.le_refl _)
  rcases ControlFrame.step_view_cases program step with same | ⟨actor, begins⟩ | ⟨actor, unloads⟩
  · exact False.elim (installed ((congrFun same name).symm.trans episode.after))
  · obtain ⟨fiber, view, present, _, _, _, endpoint⟩ := begins
    have gone := episode.after
    rw [endpoint, ControlFrame.mark_viewAt _ _ _ _ present] at gone
    by_cases acts : name = actor
    · simp [acts, Phase.committed] at gone
    · exact False.elim (installed (by simpa [acts] using gone))
  · by_cases acts : name = actor
    · exact acts ▸ unloads
    · obtain ⟨fiber, word, view, present, _, _, endpoint⟩ := unloads
      obtain ⟨retained, retainedAt, _⟩ := Ordering.discharge_existing_phases _ word actor fiber present
      have gone := episode.after
      rw [endpoint, ControlFrame.mark_viewAt _ _ _ _ retainedAt, if_neg acts,
        ControlFrame.discharge_views] at gone
      exact False.elim (installed gone)

theorem demand_step {r s : R} {actor consumer provider : Name} {key : Key} {rule : Labeled.Rule}
    (step : Labeled.Step program rule actor r s)
    (before : ControlFrame.viewAt r consumer ≠ none) (after : ControlFrame.viewAt s consumer ≠ none) :
    Ordering.Demand r consumer provider key ↔ Ordering.Demand s consumer provider key := by
  obtain ⟨old, oldView, oldAt, oldCommitted⟩ := OrderingIntervals.installed_view r consumer before
  obtain ⟨new, newView, newAt, newCommitted⟩ := OrderingIntervals.installed_view s consumer after
  have view := Ordering.step_views_stable program step.toCalculus consumer old new oldView newView
    oldAt newAt oldCommitted newCommitted
  have component := (Frame.step_stable program step.toCalculus consumer old new oldAt newAt).1
  constructor
  · rintro ⟨fiber, chosen, found, required, committed, owner⟩
    have same := Option.some.inj (found.symm.trans oldAt)
    subst fiber
    have sameView := Option.some.inj (committed.symm.trans oldCommitted)
    subst chosen
    exact ⟨new, newView, newAt, component ▸ required, newCommitted, view ▸ owner⟩
  · rintro ⟨fiber, chosen, found, required, committed, owner⟩
    have same := Option.some.inj (found.symm.trans newAt)
    subst fiber
    have sameView := Option.some.inj (committed.symm.trans newCommitted)
    subst chosen
    exact ⟨old, oldView, oldAt, component.symm ▸ required, oldCommitted, view.symm ▸ owner⟩

/-- A demand persists throughout continuous installation, including in an
episode that remains open at the endpoint. -/
theorem demand_through_installation (trace : Trace program initial last)
    {consumer provider : Name} {key : Key} {first time : Nat}
    (lower : first ≤ time) (bounded : time ≤ last)
    (installed : ∀ point, first ≤ point → point ≤ time →
      ControlFrame.viewAt (trace.state point) consumer ≠ none) :
    Ordering.Demand (trace.state first) consumer provider key ↔
      Ordering.Demand (trace.state time) consumer provider key := by
  induction time with
  | zero =>
    have same : first = 0 := by omega
    simp [same]
  | succ time ih =>
    by_cases same : first = time + 1
    · rw [same]
    · have earlier := ih (by omega) (by omega) (fun point after before => installed point after (by omega))
      exact earlier.trans (demand_step (trace.step time (by omega))
        (installed time (by omega) (by omega)) (installed (time + 1) lower (Nat.le_refl _)))

theorem demand_in_episode (trace : Trace program initial last)
    {consumer provider : Name} {key : Key} {b u : Nat}
    (episode : EpisodeAt trace consumer b u) (time : Nat) (lower : b ≤ time) (upper : time ≤ u) :
    Ordering.Demand (trace.state b) consumer provider key ↔
      Ordering.Demand (trace.state time) consumer provider key := by
  have bound := episode.bounded
  exact demand_through_installation trace lower (by omega)
    (fun point after before => episode.installed point after (by omega))

omit [DecidableEq Key] in
theorem provider_before_opening {source opened : R} {consumer provider : Name} {key : Key}
    (begins : ControlFrame.BeginsAt source opened consumer)
    (demand : Ordering.Demand opened consumer provider key) : ControlFrame.viewAt source provider ≠ none := by
  obtain ⟨before, view, found, inactive, _, target, endpoint⟩ := begins
  obtain ⟨after, chosen, afterAt, required, committed, identifies⟩ := demand
  rw [endpoint] at afterAt
  have same := Option.some.inj
    ((by simp [mark, Calculus.modify, found] : mark source consumer
      (.reloading before.component.entry [] view) consumer = some
      {before with phase := .reloading before.component.entry [] view}).symm.trans afterAt)
  subst after
  have chosenEq : view = chosen := Option.some.inj committed
  subst chosen
  simp only [Target, found] at target
  have ready := target.2 key required
  cases related : source (view key) with
  | none => simp [related] at ready
  | some row =>
    have facts := ready
    simp only [related] at facts
    rw [← identifies]
    cases phase : row.phase <;> simp [phase, Phase.available] at facts <;>
      simp [ControlFrame.viewAt, related, phase, Phase.committed]

theorem provider_before_begin (trace : Trace program initial last)
    {consumer provider : Name} {key : Key} {b u : Nat}
    (episode : EpisodeAt trace consumer b u)
    (demand : Ordering.Demand (trace.state b) consumer provider key) :
    ControlFrame.viewAt (trace.state (b - 1)) provider ≠ none :=
  provider_before_opening (begin_boundary trace episode) demand

theorem supported_at (trace : Trace program (fun _ => none) last)
    (time : Nat) (bounded : time ≤ last) : Ordering.Supported (trace.state time) :=
  (WellFormed.run_invariants program (trace.prefixRun time bounded)
    (by simp [Safety.ParentClosed]) WellFormed.disjoint_empty
    ⟨Ordering.supported_empty, Ordering.local_empty⟩).2.2.1

theorem provider_during_episode (trace : Trace program (fun _ => none) last)
    {consumer provider : Name} {key : Key} {b u : Nat}
    (episode : EpisodeAt trace consumer b u)
    (demand : Ordering.Demand (trace.state b) consumer provider key) (time : Nat)
    (lower : b ≤ time) (upper : time ≤ u) :
    ControlFrame.viewAt (trace.state time) provider ≠ none := by
  have bounded := episode.bounded
  obtain ⟨_, entry, found, retained, _⟩ :=
    supported_at trace time (by omega) consumer provider key
      ((demand_in_episode trace episode time lower upper).mp demand)
  cases phase : entry.phase <;> simp [phase, Ordering.Retained] at retained <;>
    simp [ControlFrame.viewAt, found, phase, Phase.committed]

/-- A provider episode covering a real demand must start before and close
after the consumer's episode. This uses the installed binding, so a later
owner of the same declaration cannot create a backwards episode edge. -/
theorem provider_strictly_encloses (trace : Trace program (fun _ => none) last)
    {consumer provider : Name} {key : Key} {b u providerBegin providerEnd time : Nat}
    (episode : EpisodeAt trace consumer b u)
    (providing : EpisodeAt trace provider providerBegin providerEnd)
    (lower : b ≤ time) (upper : time ≤ u)
    (providerLower : providerBegin ≤ time) (providerUpper : time ≤ providerEnd)
    (demand : Ordering.Demand (trace.state time) consumer provider key) :
    providerBegin < b ∧ u < providerEnd := by
  have original := (demand_in_episode trace episode time lower upper).mpr demand
  have positive := episode.positive
  have lastConsumer := episode.bounded
  have lastProvider := providing.bounded
  have shorter : providerBegin < b := by
    by_cases sameBegin : providerBegin = b
    · exact False.elim (provider_before_begin trace episode original
        (sameBegin ▸ providing.before))
    · by_cases earlier : providerBegin < b
      · exact earlier
      · exact False.elim (provider_during_episode trace episode original (providerBegin - 1)
          (by omega) (by omega) providing.before)
  refine ⟨shorter, ?_⟩
  by_cases sameEnd : providerEnd = u
  · have finalDemand := (demand_in_episode trace episode u episode.ordered (Nat.le_refl _)).mp original
    obtain ⟨different, _⟩ := supported_at trace u (by omega) consumer provider key finalDemand
    obtain ⟨fiber, word, actualView, found, phase, free, _⟩ := unload_boundary trace providing
    rw [sameEnd] at free
    exact False.elim (free (Ordering.demand_relied _ _ _ _ finalDemand different))
  · by_cases later : u < providerEnd
    · exact later
    · exact False.elim (provider_during_episode trace episode original (providerEnd + 1)
        (by omega) (by omega) providing.after)

structure ClosedEpisode (trace : Trace program initial last) where
  name : Name
  opened : Nat
  closed : Nat
  interval : EpisodeAt trace name opened closed

/-- Interpret the dependencies used for selecting an episode by actual
simultaneous installation or by the birth of the consumer incarnation. -/
def EpisodeEdge {trace : Trace program initial last}
    (earlier later : ClosedEpisode trace) : Prop :=
  (∃ time key, earlier.opened ≤ time ∧ time ≤ earlier.closed ∧
    later.opened ≤ time ∧ time ≤ later.closed ∧ Ordering.Demand (trace.state time) later.name earlier.name key) ∨
  (∃ time, earlier.opened ≤ time ∧ time ≤ earlier.closed ∧
    Transposition.CreatesChild program earlier.name (trace.state time) (trace.state (time + 1)) later.name ∧
    Incarnation.Residency trace.state later.name (time + 1) later.opened)

theorem episode_edge_earlier {trace : Trace program (fun _ => none) last}
    {earlier later : ClosedEpisode trace} (edge : EpisodeEdge earlier later) :
    earlier.opened < later.opened := by
  rcases edge with ⟨time, key, providerStart, providerEnd, start, finish, demand⟩ |
    ⟨time, created, _, _, residency⟩
  · exact (provider_strictly_encloses trace later.interval earlier.interval start finish
      providerStart providerEnd demand).1
  · have bornBefore := residency.ordered
    omega

theorem episode_order {trace : Trace program (fun _ => none) last} :
    WellFounded (EpisodeEdge (trace := trace)) :=
  Subrelation.wf (fun {_ _} edge => episode_edge_earlier edge) (measure ClosedEpisode.opened).wf

theorem latest_index (eligible : Nat → Prop) (bound : Nat)
    (existsIndex : ∃ time, time < bound ∧ eligible time) :
    ∃ latest, latest < bound ∧ eligible latest ∧
      ∀ time, time < bound → eligible time → time ≤ latest := by
  classical
  induction bound with
  | zero => obtain ⟨_, impossible, _⟩ := existsIndex; omega
  | succ bound ih =>
    by_cases lastEligible : eligible bound
    · exact ⟨bound, by omega, lastEligible, fun time inRange _ => by omega⟩
    · have earlier : ∃ time, time < bound ∧ eligible time := by
        obtain ⟨time, inRange, allowed⟩ := existsIndex
        have different : time ≠ bound := fun same => lastEligible (same ▸ allowed)
        exact ⟨time, by omega, allowed⟩
      obtain ⟨latest, inRange, allowed, greatest⟩ := ih earlier
      refine ⟨latest, by omega, allowed, fun time smaller eligibleAt => ?_⟩
      have different : time ≠ bound := fun same => lastEligible (same ▸ eligibleAt)
      exact greatest time (by omega) eligibleAt

/-- Whenever there are closing episodes, one has no outgoing actual
episode edge to another closing episode. The proof selects the latest
Begin and does not use declaration edges between disjoint lifetimes. -/
theorem select_closing (trace : Trace program (fun _ => none) last)
    (closed : Nonempty (ClosedEpisode trace)) :
    ∃ selected : ClosedEpisode trace, ∀ later : ClosedEpisode trace, ¬ EpisodeEdge selected later := by
  let eligible (time : Nat) := ∃ episode : ClosedEpisode trace, episode.opened = time
  have bounded (episode : ClosedEpisode trace) : episode.opened < last :=
    Nat.lt_of_le_of_lt episode.interval.ordered episode.interval.bounded
  obtain ⟨episode⟩ := closed
  obtain ⟨index, _, ⟨selected, exactIndex⟩, greatest⟩ :=
    latest_index eligible last ⟨episode.opened, bounded episode, episode, rfl⟩
  refine ⟨selected, fun later edge => ?_⟩
  have before := episode_edge_earlier edge
  have contradicts := greatest later.opened (bounded later) ⟨later, rfl⟩
  omega

end Cordis.Repairs.EpisodeDependencies
