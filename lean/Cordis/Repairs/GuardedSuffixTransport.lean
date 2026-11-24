import Cordis.Repairs.GuardedSuffix
import Cordis.TypedCallbackExchange

/-! Lift a legal guarded suffix to a related starting registry and cut
notes. Retained unloads use those notes to discharge the related word. -/
namespace Cordis.Repairs.GuardedSuffix
open Calculus Stages LegalHistory
open EpisodeAnnotations (NotesRelated noteStep_related replay_related_of_notes)
open Vestigial (CutNotes eventActor noteStep)
open PaperEffectEquations (CoeffectOperations)
open PaperObservationEquations (OperationRespects)
open OrchestrationSorting (Command)
open TypedRegistry (Scalar RawRegistry encodeProgram)
open Iterators (OptionRel)
universe u
variable {Name Key Code : Type u} {V : Key → Type u} {ops : CoeffectOperations V}
variable [DecidableEq Name] [DecidableEq Key]
local notation "A" => Scalar ops
local notation "R" => RawRegistry Name ops Code
local notation "Ev" => Event Name Key Code
local notation "Notes" => CutNotes Name Key A
variable (observe : ∀ key, Setoid (V key))
local notation "Related" => @StageSimulation.Related Name Key A Code _ (TypedCoeffectReplay.setoid observe) Eq
local notation "Paired" => @NotesRelated Name Key A (TypedCoeffectReplay.setoid observe)

private theorem command_related (command : Command Name Key Code) {left right after : R}
    (states : Related left right) (step : command.Step left after) :
    command.Step right (command.apply right) ∧ Related after (command.apply right) := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  obtain ⟨ready, rfl⟩ := step
  refine ⟨⟨?_, rfl⟩, ?_⟩
  · cases command with
    | insert name component => exact (GuardObservations.insertable_iff states.observed name component none).mp ready
    | retire name => exact fun absent => ready ((GuardObservations.none_iff states.observed name).mpr absent)
    | remove name => exact (GuardObservations.removable_iff states.observed name).mp ready
  · cases command with
    | insert name component => exact StageSimulation.put_related states name (StageSimulation.fresh_related ⟨rfl, rfl, rfl⟩ none)
    | retire name => exact StageSimulation.retire_related states name
    | remove name => exact StageSimulation.erase_related states name

private theorem unload_related {left right after : R} {first second : Notes} {actor : Name}
    (states : Related left right) (paired : Paired first second) (projects : SavedWordsAgree right second)
    (step : Unload actor left first after) : ∃ moved, Unload actor right second moved ∧ Related after moved := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  obtain ⟨row, view, present, phase, free, rfl⟩ := step
  obtain ⟨other, found, fields⟩ := StageSimulation.present_related states actor row present
  obtain ⟨word, unloading, _⟩ := StageSimulation.phase_unloading (phase ▸ fields.phase)
  have correct : (second.2 actor).map IncarnationReplay.Capture.token = word := by
    simpa [PartialReplayRegistry.saved, found, unloading, Phase.accumulator] using projects actor
  refine ⟨_, ⟨other, view, found, by rw [correct]; exact unloading, ?_, rfl⟩, ?_⟩
  · exact fun relied => free ((GuardObservations.relied_iff states.observed actor).mpr relied)
  · exact StageSimulation.mark_related (replay_related_of_notes states paired actor) actor .inactive

private theorem transition_related (program : Code → TypedRegistry.Instruction Name ops Code)
    (respect : ∀ key, OperationRespects ops key (observe key).r)
    {left right after : R} {first second : Notes} {event : Ev}
    (states : Related left right) (paired : Paired first second) (projects : SavedWordsAgree right second)
    (step : Transition (encodeProgram program) first event left after) :
    ∃ moved, Transition (encodeProgram program) second event right moved ∧ Related after moved := by
  cases event with
  | command command => exact ⟨_, command_related observe command states step⟩
  | lifecycle kind actor =>
    cases kind
    case unload => exact unload_related observe states paired projects step
    all_goals exact TypedRegistry.encoded_step_simulation ops observe program respect states step

theorem related_roots {left right : R} (states : Related left right) (name : Name) :
    rootAt left name = rootAt right name := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  have controls := states.observed name
  cases l : left name <;> cases r : right name <;> simp_all [rootAt, OptionRel]
  rw [controls.parent]

/-- Transport one actual guarded event without changing its stamp or root
classification. The replayed unload discharges its own recorded word. -/
theorem transport_step (program : Code → TypedRegistry.Instruction Name ops Code)
    (respect : ∀ key, OperationRespects ops key (observe key).r)
    {event : Ev} {stamp : Nat} {before after : R} {first recorded : Notes}
    (step : Step (encodeProgram program) event stamp before first after recorded)
    {replayed : R} {second : Notes} (states : Related before replayed) (paired : Paired first second)
    (projects : SavedWordsAgree replayed second) :
    ∃ next notes, Step (encodeProgram program) event stamp replayed second next notes ∧
      Related after next ∧ Paired recorded notes ∧ SavedWordsAgree next notes ∧
      eventRoots before event = eventRoots replayed event := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  obtain ⟨actual, rfl⟩ := step
  obtain ⟨next, moved, compared⟩ := transition_related observe program respect states paired projects actual
  let notes := noteStep replayed next (eventActor event) stamp second
  have replayedStep : Step (encodeProgram program) event stamp replayed second next notes := ⟨moved, rfl⟩
  exact ⟨next, notes, replayedStep, compared, noteStep_related states compared (eventActor event) stamp paired,
    step_projects replayedStep projects, eventRoots_agree event (related_roots observe states)⟩

omit [DecidableEq Name] [DecidableEq Key] in
theorem actorSource_related {left right : R} {first second : Notes} (event : Ev)
    (states : Related left right) (paired : Paired first second) :
    actorSource left first event = actorSource right second event := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  unfold actorSource
  apply Prod.ext
  · exact congrFun paired.births (eventActor event)
  · have compared := states (eventActor event)
    cases l : left (eventActor event) <;> cases r : right (eventActor event) <;>
      simp only [l, r, OptionRel, Option.map_some, Option.map_none] at compared ⊢
    rename_i a b
    have same : a.component = b.component := by
      have fields := compared.component
      generalize ha : a.component = ca at fields ⊢
      generalize hb : b.component = cb at fields ⊢
      cases ca
      cases cb
      obtain ⟨rfl, rfl, rfl⟩ := fields
      rfl
    exact congrArg some same

/-- The same root commands and stamps execute from a related guarded cut.
Every simulated unload uses the recorded word of its own source registry. -/
theorem transport_exec (program : Code → TypedRegistry.Instruction Name ops Code)
    (respect : ∀ key, OperationRespects ops key (observe key).r)
    {events : List (Nat × Ev)} {before final : R} {first finalNotes : Notes} {roots : List (Command Name Key Code)}
    {sources : Nat → Option (ActorSource Key Code)}
    (run : ExecWith (encodeProgram program) sources events before first final finalNotes roots)
    {replayed : R} {second : Notes} (states : Related before replayed) (paired : Paired first second)
    (projects : SavedWordsAgree replayed second) :
    ∃ after notes, ExecWith (encodeProgram program) sources events replayed second after notes roots ∧
      Related final after ∧ Paired finalNotes notes ∧ SavedWordsAgree after notes := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  induction run generalizing replayed second with
  | nil => exact ⟨replayed, second, .nil _ _, states, paired, projects⟩
  | @cons stamp event events before first middle recorded final finalNotes roots step suffix checked ih =>
    obtain ⟨next, notes, moved, compared, aligned, nextProjects, rootsAgree⟩ :=
      transport_step observe program respect step states paired projects
    obtain ⟨after, notes, rest, endpoint, finalPair, finalProjects⟩ := ih compared aligned nextProjects
    rw [rootsAgree]
    refine ⟨after, notes, .cons moved rest ?_, endpoint, finalPair, finalProjects⟩
    unfold CheckedSource at *
    rw [← actorSource_related observe event states paired]
    exact checked

end Cordis.Repairs.GuardedSuffix
