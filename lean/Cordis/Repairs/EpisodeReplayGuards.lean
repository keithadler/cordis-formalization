import Cordis.Repairs.EpisodeBoundary
import Cordis.GuardObservations

/-! The control and binding-domain obligations for a cut inside episode
deletion. Retained rows keep their metadata and binding presence. The
closing actor stays registered but inactive, and withdrawn children are
absent. No comparison of operation results or inverses is built into the
guard argument. -/
namespace Cordis.Repairs.EpisodeReplayGuards
open Calculus Stages Indexed EpisodeDependencies EpisodeBoundary
open Iterators (OptionRel)
universe u
variable {Name Key Value Code Error : Type u} [DecidableEq Name] [DecidableEq Key]
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error

omit [DecidableEq Name] [DecidableEq Key] in
structure RetainedRow (suspended : Prop) (original paired : F) : Prop where
  component : original.component = paired.component
  parent : original.parent = paired.parent
  retired : original.retired = paired.retired
  inactive : suspended → paired.phase = .inactive
  phase : ¬ suspended → GuardObservations.phaseKind original.phase = GuardObservations.phaseKind paired.phase
  view : ¬ suspended → original.phase.committed = paired.phase.committed
  domain : ¬ suspended → ∀ key, original.table key = none ↔ paired.table key = none

omit [DecidableEq Name] [DecidableEq Key] in
structure Projection (closing : Name) (withdrawn : Name → Prop) (source probe : R) : Prop where
  absent : ∀ name, withdrawn name → probe name = none
  dormant : ∀ name, withdrawn name → ControlFrame.viewAt source name = none
  kept : ∀ name, ¬ withdrawn name → OptionRel (RetainedRow (name = closing)) (source name) (probe name)

omit [DecidableEq Name] [DecidableEq Key] in
theorem Projection.forward_row {closing : Name} {withdrawn : Name → Prop} {source probe : R}
    (projected : Projection closing withdrawn source probe) {name : Name} (kept : ¬ withdrawn name)
    {original : F} (found : source name = some original) :
    ∃ paired, probe name = some paired ∧ RetainedRow (name = closing) original paired := by
  have related := projected.kept name kept
  rw [found] at related
  cases slot : probe name with
  | none => simp [slot, OptionRel] at related
  | some paired => exact ⟨paired, rfl, by simpa [slot, OptionRel] using related⟩

omit [DecidableEq Name] [DecidableEq Key] in
theorem Projection.backward_row {closing : Name} {withdrawn : Name → Prop} {source probe : R}
    (projected : Projection closing withdrawn source probe) {name : Name}
    {paired : F} (found : probe name = some paired) :
    ¬ withdrawn name ∧ ∃ original, source name = some original ∧ RetainedRow (name = closing) original paired := by
  have kept : ¬ withdrawn name := fun omitted => by
    have absent := projected.absent name omitted
    rw [found] at absent
    cases absent
  have related := projected.kept name kept
  rw [found] at related
  refine ⟨kept, ?_⟩
  cases slot : source name with
  | none => simp [slot, OptionRel] at related
  | some original => exact ⟨original, rfl, by simpa [slot, OptionRel] using related⟩

omit [DecidableEq Name] [DecidableEq Key] in
private theorem available_not_dormant {state : R} {name : Name} {row : F}
    (found : state name = some row) (ready : row.phase.available) :
    ControlFrame.viewAt state name ≠ none := by
  cases phase : row.phase <;> simp [phase, Phase.available] at ready <;>
    simp [ControlFrame.viewAt, found, phase, Phase.committed]

omit [DecidableEq Name] [DecidableEq Key] in
/-- A successful target survives if its required bindings avoid the closing
actor. Withdrawn children are unavailable in the source, by dormancy. -/
theorem Projection.target_forward {closing : Name} {withdrawn : Name → Prop} {source probe : R}
    (projected : Projection closing withdrawn source probe) {actor : Name} (kept : ¬ withdrawn actor)
    {fiber : F} (present : source actor = some fiber) (view : View Name Key)
    (avoids : ∀ key, fiber.component.requires key → view key ≠ closing)
    (target : Target source actor view) : Target probe actor view := by
  obtain ⟨counterpart, paired, fields⟩ := projected.forward_row kept present
  simp only [Target, present] at target
  simp only [Target, paired, ← fields.component, ← fields.retired]
  refine ⟨target.1, ?_⟩
  intro key required
  have valid := target.2 key required
  cases bound : source (view key) with
  | none => simp [bound] at valid
  | some provider =>
    rw [bound] at valid
    have visible : ¬ withdrawn (view key) := fun omitted =>
      available_not_dormant bound valid.1 (projected.dormant _ omitted)
    obtain ⟨provided, visibleAt, stable⟩ := projected.forward_row visible bound
    rw [visibleAt]
    exact ⟨(GuardObservations.phase_available_iff (stable.phase (avoids key required))).mp valid.1,
      fun absent => valid.2 ((stable.domain (avoids key required) key).mpr absent)⟩

omit [DecidableEq Name] [DecidableEq Key] in
/-- Erasing rows and deactivating the closing actor cannot turn a false
target into a true one. This is the direction used by Divert and Leave. -/
theorem Projection.target_backward {closing : Name} {withdrawn : Name → Prop} {source probe : R}
    (projected : Projection closing withdrawn source probe) (actor : Name) (view : View Name Key)
    (target : Target probe actor view) : Target source actor view := by
  cases found : probe actor with
  | none => simp [Target, found] at target
  | some paired =>
    obtain ⟨_, original, oldAt, fields⟩ := projected.backward_row found
    simp only [Target, found] at target
    simp only [Target, oldAt, fields.component, fields.retired]
    refine ⟨target.1, ?_⟩
    intro key required
    have valid := target.2 key required
    cases bound : probe (view key) with
    | none => simp [bound] at valid
    | some provider =>
      rw [bound] at valid
      obtain ⟨_, old, sourceAt, stable⟩ := projected.backward_row bound
      have different : view key ≠ closing := fun same => by
        simp [stable.inactive same, Phase.available] at valid
      rw [sourceAt]
      exact ⟨(GuardObservations.phase_available_iff (stable.phase different)).mpr valid.1,
        fun absent => valid.2 ((stable.domain different key).mp absent)⟩

omit [DecidableEq Name] [DecidableEq Key] in
/-- Erasure and deactivation can only remove committed consumers.
Therefore the negative Relied guard of a retained Unload is preserved. -/
theorem Projection.relied_backward {closing : Name} {withdrawn : Name → Prop} {source probe : R}
    (projected : Projection closing withdrawn source probe) {provider : Name}
    (relied : Relied probe provider) : Relied source provider := by
  obtain ⟨consumer, different, demands⟩ := relied
  cases found : probe consumer with
  | none => simp [found] at demands
  | some paired =>
    obtain ⟨_, prior, present, stable⟩ := projected.backward_row found
    have retained : consumer ≠ closing := fun same => by
      simp [found, stable.inactive same, Phase.committed] at demands
    refine ⟨consumer, different, ?_⟩
    simpa [present, stable.component, stable.view retained, found] using demands

omit [DecidableEq Name] [DecidableEq Key] in
theorem Projection.insertable {closing : Name} {withdrawn : Name → Prop} {source probe : R}
    (projected : Projection closing withdrawn source probe) {name : Name}
    {component : Component Key Code} {parent : Option Name}
    (parentRetained : ∀ p, parent = some p → ¬ withdrawn p)
    (ready : Insertable source name component parent) :
    Insertable probe name component parent := by
  refine ⟨?_, ?_, ?_⟩
  · cases found : probe name with
    | none => rfl
    | some row =>
      obtain ⟨_, old, present, _⟩ := projected.backward_row found
      rw [ready.1] at present
      cases present
  · intro p selected missing
    cases present : source p with
    | none => exact ready.2.1 p selected present
    | some f =>
      obtain ⟨row, placed, _⟩ := projected.forward_row (parentRetained p selected) present
      rw [missing] at placed
      cases placed
  · intro other key
    cases found : probe other with
    | none => trivial
    | some row =>
      obtain ⟨_, prior, present, fields⟩ := projected.backward_row found
      have old := ready.2.2 other key
      simpa [present, fields.component] using old

omit [DecidableEq Name] [DecidableEq Key] in
theorem Projection.removable {closing : Name} {withdrawn : Name → Prop} {source probe : R}
    (projected : Projection closing withdrawn source probe) {name : Name}
    (kept : ¬ withdrawn name) (different : name ≠ closing) (ready : Removable source name) :
    Removable probe name := by
  cases found : source name with
  | none => simp [Removable, found] at ready
  | some old =>
    obtain ⟨paired, present, fields⟩ := projected.forward_row kept found
    simp only [Removable, found] at ready
    simp only [Removable, present]
    refine ⟨fields.retired ▸ ready.1, (GuardObservations.phase_inactive_iff (fields.phase different)).mp ready.2.1,
      fun key => (fields.domain different key).mp (ready.2.2.1 key), ?_⟩
    intro child
    cases childAt : probe child with
    | none => trivial
    | some entry =>
      obtain ⟨_, prior, before, stable⟩ := projected.backward_row childAt
      have noChild := ready.2.2.2 child
      simpa [before, stable.parent] using noChild

omit [DecidableEq Name] [DecidableEq Key] in
/-- A retained operation's owner survives the projection, whether it is
the actor itself or a retained provider in its committed view. -/
theorem Projection.location_owner_retained {closing actor owner : Name} {withdrawn : Name → Prop}
    {source probe : R} (projected : Projection closing withdrawn source probe)
    (kept : ¬ withdrawn actor) (different : actor ≠ closing)
    (supported : Ordering.Supported source)
    (noDemand : ∀ key, ¬ Ordering.Demand source actor closing key)
    {fiber : F} (present : source actor = some fiber)
    {key : Key} {value : Value} (located : location source actor key = some (owner, value)) :
    ¬ withdrawn owner ∧ owner ≠ closing := by
  rcases location_scope present located with ⟨rfl, _⟩ | ⟨view, committed, required, selects⟩
  · exact ⟨kept, different⟩
  · have demand : Ordering.Demand source actor owner key :=
      ⟨fiber, view, present, required, committed, selects⟩
    have notClosing : owner ≠ closing := fun same => noDemand key (same ▸ demand)
    obtain ⟨_, provider, providerAt, available, _⟩ := supported actor owner key demand
    have installed : ControlFrame.viewAt source owner ≠ none := by
      cases phase : provider.phase <;> simp [phase, Ordering.Retained] at available <;>
        simp [ControlFrame.viewAt, providerAt, phase, Phase.committed]
    exact ⟨fun omitted => installed (projected.dormant owner omitted), notClosing⟩

omit [DecidableEq Name] [DecidableEq Key] in
/-- A retained operation has the same occupied route. This establishes
its input domain before any comparison of scalar values or callbacks. -/
theorem Projection.location_forward {closing actor owner : Name} {withdrawn : Name → Prop}
    {source probe : R} (projected : Projection closing withdrawn source probe)
    (kept : ¬ withdrawn actor) (different : actor ≠ closing)
    (supported : Ordering.Supported source)
    (noDemand : ∀ key, ¬ Ordering.Demand source actor closing key)
    {fiber : F} (present : source actor = some fiber)
    {key : Key} {value : Value} (located : location source actor key = some (owner, value)) :
    ∃ other, location probe actor key = some (owner, other) := by
  have retained := projected.location_owner_retained kept different supported noDemand present located
  obtain ⟨actorRow, actorAt, stable⟩ := projected.forward_row kept present
  have route : bindingOwner probe actor key = some owner := by
    have original := location_owner located
    simpa [bindingOwner, present, actorAt, stable.component, stable.view different] using original
  obtain ⟨provider, providerAt, literal⟩ := Safety.location_binding source actor owner key value located
  obtain ⟨row, rowAt, fields⟩ := projected.forward_row retained.1 providerAt
  have occupied : row.table key ≠ none := fun empty => by
    have missing := (fields.domain retained.2 key).mpr empty
    rw [literal] at missing
    cases missing
  cases target : row.table key with
  | none => exact False.elim (occupied target)
  | some other => exact ⟨other, by simp [location, route, rowAt, target]⟩

variable {program : Code → Instruction Name Key Value Code Error} {last : Nat}
local notation "History" => Trace program (fun _ => none : R) last

/-- A scheduled target that uses an already committed view cannot choose
the selected closing fiber on any required key. -/
theorem committed_avoids_closing (trace : History) (episode : ClosedEpisode trace)
    (maximal : ∀ later : ClosedEpisode trace, ¬ EpisodeEdge episode later)
    {time : Nat} (lower : episode.opened ≤ time) (upper : time ≤ episode.closed)
    {actor : Name} {fiber : F} {view : View Name Key}
    (present : trace.state time actor = some fiber) (committed : fiber.phase.committed = some view) :
    ∀ key, fiber.component.requires key → view key ≠ episode.name := by
  intro key required selects
  exact no_demand_on_closing trace episode maximal lower upper
    ⟨fiber, view, present, required, committed, selects⟩

/-- A true L-Begin guard reads the view which the actual step installs.
The new demand would already contradict the closing-episode selection. -/
theorem begin_avoids_closing (trace : History) (episode : ClosedEpisode trace)
    (maximal : ∀ later : ClosedEpisode trace, ¬ EpisodeEdge episode later)
    {time : Nat} (lower : episode.opened ≤ time + 1) (upper : time + 1 ≤ episode.closed)
    {actor : Name} {fiber : F} {view : View Name Key}
    (present : trace.state time actor = some fiber)
    (opened : trace.state (time + 1) = mark (trace.state time) actor (.reloading fiber.component.entry [] view)) :
    ∀ key, fiber.component.requires key → view key ≠ episode.name := by
  have afterAt : trace.state (time + 1) actor =
      some {fiber with phase := .reloading fiber.component.entry [] view} := by
    rw [opened, mark_self _ _ _ _ present]
  exact committed_avoids_closing trace episode maximal lower upper
    (fiber := {fiber with phase := .reloading fiber.component.entry [] view}) afterAt rfl

/-- The actual L-Begin is legal on a projected probe. It chooses the same
view and entering code even if the closing actor's original table has been
rolled back, or the newborn children have been omitted. -/
theorem begin_on_probe (trace : History) (episode : ClosedEpisode trace)
    (maximal : ∀ later : ClosedEpisode trace, ¬ EpisodeEdge episode later)
    {time : Nat} (lower : episode.opened ≤ time + 1) (upper : time + 1 ≤ episode.closed)
    {actor : Name} {fiber : F} {view : View Name Key} {withdrawn : Name → Prop} {probe : R}
    (projected : Projection episode.name withdrawn (trace.state time) probe)
    (kept : ¬ withdrawn actor) (different : actor ≠ episode.name)
    (present : trace.state time actor = some fiber) (inactive : fiber.phase = .inactive)
    (target : Target (trace.state time) actor view)
    (opened : trace.state (time + 1) = mark (trace.state time) actor (.reloading fiber.component.entry [] view)) :
    Labeled.Step program .begin actor probe (mark probe actor (.reloading fiber.component.entry [] view)) := by
  have avoids := begin_avoids_closing trace episode maximal lower upper present opened
  obtain ⟨row, found, fields⟩ := projected.forward_row kept present
  have opens : Labeled.Step program .begin actor probe (mark probe actor (.reloading row.component.entry [] view)) :=
    .begin _ _ row view found ((GuardObservations.phase_inactive_iff (fields.phase different)).mp inactive)
      (by simp [found]) (projected.target_forward kept present view avoids target)
  simpa only [← fields.component] using opens

/-- A native operation inside the retained part of the interval has a
defined route on the projected registry. Its value may have changed when
the closing actor's pending operations were rolled back. -/
theorem location_on_probe (trace : History) (episode : ClosedEpisode trace)
    (maximal : ∀ later : ClosedEpisode trace, ¬ EpisodeEdge episode later)
    {time : Nat} (lower : episode.opened ≤ time) (upper : time ≤ episode.closed)
    {actor owner : Name} {withdrawn : Name → Prop} {probe : R}
    (projected : Projection episode.name withdrawn (trace.state time) probe)
    (kept : ¬ withdrawn actor) (different : actor ≠ episode.name)
    {fiber : F} (present : trace.state time actor = some fiber)
    {key : Key} {value : Value} (located : location (trace.state time) actor key = some (owner, value)) :
    ∃ other, location probe actor key = some (owner, other) := by
  exact projected.location_forward kept different
    (supported_at trace time (by have := episode.interval.bounded; omega))
    (fun key => no_demand_on_closing trace episode maximal lower upper) present located

omit [DecidableEq Key] in
open OrchestrationSorting (Command) in
/-- The surviving orchestration command keeps its exact payload. Retirement
of the closing actor itself also survives, because the entry stays in the
projected registry. -/
theorem Projection.command {closing : Name} {withdrawn : Name → Prop} {source probe after : R}
    (projected : Projection closing withdrawn source probe) (command : Command Name Key Code)
    (kept : ¬ withdrawn command.actor)
    (preserveRemoval : ∀ name, command = .remove name → name ≠ closing) (actual : command.Step source after) :
    command.Step probe (command.apply probe) := by
  refine ⟨?_, rfl⟩
  cases command with
  | insert name component =>
    exact projected.insertable (by intro p impossible; cases impossible) actual.1
  | retire name =>
    change probe name ≠ none
    have live : source name ≠ none := actual.1
    cases found : source name with
    | none => exact False.elim (live found)
    | some fiber =>
      obtain ⟨row, paired, _⟩ := projected.forward_row kept found
      change probe name = some row at paired
      simp [paired]
  | remove name => exact projected.removable kept (preserveRemoval name rfl) actual.1

end Cordis.Repairs.EpisodeReplayGuards
