import Cordis.Repairs.GuardedEpisodeReplay
import Cordis.Repairs.EpisodeOperationReplay

/-! The retained operation uses the guarded source's actual per-slot replay
history and its occupied provider route at the rollback probe. -/
namespace Cordis.Repairs.GuardedHistory
open Calculus Stages IncarnationReplay LegalHistory
open EpisodeAnnotations (NotesRelated noteStep_related)
open Vestigial (noteStep)
open PaperEffectEquations (CoeffectOperations ValueOperationWitness)
open PartialCoeffectIndependenceContracts (tableSetoid)
open PartialInverseObservation (MapRelated)
open TypedRegistry (encodeProgram Scalar RawFiber)
open StageRecovery (tableAt)
open EpisodeOperationReplay (located_owner_present)
universe u
variable {Name Key Code : Type u} {V : Key → Type u} {ops : CoeffectOperations V}
variable [DecidableEq Name] [DecidableEq Key]
variable {program : Code → TypedRegistry.Instruction Name ops Code} {last : Nat}
local notation "A" => Scalar ops
local notation "Source" => Trace (encodeProgram program) last

local notation "R" => TypedRegistry.RawRegistry Name ops Code
local notation "I" => Inverse Name Key A
local notation "Related" => fun observe => @StageSimulation.Related Name Key A Code _
  (TypedCoeffectReplay.setoid observe) Eq
local notation "Paired" => fun observe => @NotesRelated Name Key A (TypedCoeffectReplay.setoid observe)

/-- The retained call succeeds at the canonical rollback probe, follows
the original outcome-selected continuation, and captures a related
inverse. Evaluating the retained call then gives a value related to
rolling back the original operation's actual output. -/
theorem operate_on_rollback (trace : Source) (episode : ClosedEpisode trace)
    (maximal : ∀ later : ClosedEpisode trace, ¬ EpisodeEdge episode later)
    (quiet : Progress.Quiet (trace.state last))
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops
      (tableSetoid observe (fun _ => True)) key)
    {time : Nat} (lower : episode.opened ≤ time) (upper : time ≤ episode.closed)
    {actor owner : Name} {entry : RawFiber Name ops Code}
    (different : actor ≠ episode.name) (kept : ¬ withdraws trace episode time actor = true)
    (present : trace.state time actor = some entry)
    {code : Code} {key : Key} {call : A → Except PUnit.{u + 1} (A × (A → A) × A)}
    (action : (encodeProgram program code).action = .operate key call)
    {input output outcome : A} {inverse : A → A}
    (located : location (trace.state time) actor key = some (owner, input))
    (performed : call input = .ok (output, inverse, outcome)) :
    ∃ adjusted after actualInverse reverted,
      location (probeAt trace episode time) actor key = some (owner, adjusted) ∧
      call adjusted = .ok (after, actualInverse, outcome) ∧
      Land (encodeProgram program) actor code (probeAt trace episode time)
        (write (probeAt trace episode time) owner key (some after))
        (.operate owner key actualInverse) ((encodeProgram program code).next (.value outcome)) ∧
      MapRelated (TypedCoeffectReplay.setoid (Yield := TypedRegistry.Yield ops) observe).r
        (TypedCoeffectReplay.decodeInverse key actualInverse)
        (TypedCoeffectReplay.decodeInverse key inverse) ∧
      @Effects.Related A (TypedCoeffectReplay.setoid observe) actualInverse inverse ∧
      tableAt (replay (trace.notes time).1 ((trace.notes time).2 episode.name)
        (write (trace.state time) owner key (some output))) owner key = some reverted ∧
      (TypedCoeffectReplay.setoid (Yield := TypedRegistry.Yield ops) observe).r after reverted := by
  have bounded : time ≤ last := by have := episode.interval.bounded; omega
  let meaning := TypedReplayContracts.coeffects ops observe program recovery commutative
  exact EpisodeOperationReplay.operate_on_saved_word observe recovery commutative (trace.state time) episode.name
    (trace.notes time).1 ((trace.notes time).2 episode.name) (trace.projects time bounded episode.name)
    (trace.table_scope time bounded) (trace.slot_history meaning time bounded) different kept present
    (trace.supported time bounded) (fun _ => no_demand_on_closing trace episode maximal lower upper)
    (probe_projects trace episode maximal quiet lower upper) action located performed

private theorem replay_write_step (trace : Source) (episode : ClosedEpisode trace)
    (maximal : ∀ later : ClosedEpisode trace, ¬ EpisodeEdge episode later)
    (quiet : Progress.Quiet (trace.state last))
    (observe : ∀ key, Setoid (V key))
    {time : Nat} (lower : episode.opened ≤ time) (upper : time < episode.closed)
    {kind : Lifecycle} (event : trace.event time = .lifecycle kind (trace.actor time)) (native : kind ≠ .unload)
    {owner : Name} {key : Key} {output after reverted : A}
    {originalPhase replayPhase : Phase Name Key Code I}
    (different : trace.actor time ≠ episode.name)
    (kept : ¬ withdraws trace episode time (trace.actor time) = true)
    (sourceSelf : Related observe (trace.state time) (trace.state time))
    (phases : @StageSimulation.PhaseRelated Name Key A Code (TypedCoeffectReplay.setoid observe) Eq replayPhase originalPhase)
    (liveInSource : trace.state time owner ≠ none)
    (liveInProbe : probeAt trace episode time owner ≠ none)
    (ended : trace.state (time + 1) =
      mark (write (trace.state time) owner key (some output)) (trace.actor time) originalPhase)
    (rolled : tableAt (replay (trace.notes time).1 ((trace.notes time).2 episode.name)
      (write (trace.state time) owner key (some output))) owner key = some reverted)
    (related : (TypedCoeffectReplay.setoid (Yield := TypedRegistry.Yield ops) observe).r after reverted)
    (moved : Labeled.Step (encodeProgram program) kind.rule (trace.actor time) (probeAt trace episode time)
      (mark (write (probeAt trace episode time) owner key (some after)) (trace.actor time) replayPhase)) :
    ∃ next recorded,
      GuardedSuffix.Step (encodeProgram program) (trace.event time) (time + 1) (probeAt trace episode time)
        (probeNotes trace episode time) next recorded ∧
      Related observe next (probeAt trace episode (time + 1)) ∧
      Paired observe recorded (probeNotes trace episode (time + 1)) := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  have bound : time < last := Nat.lt_trans upper episode.interval.bounded
  let middle := write (trace.state time) owner key (some output)
  let next := mark (write (probeAt trace episode time) owner key (some after)) (trace.actor time) replayPhase
  have presence (name : Name) : middle name = none ↔ trace.state time name = none := by
    by_cases same : name = owner <;> simp [middle, write, Calculus.modify, same]
  have edited := EpisodeOperationReplay.compare_rollback_write observe (trace.state time) episode.name
    (trace.notes time).1 ((trace.notes time).2 episode.name) sourceSelf liveInSource liveInProbe rolled related
  have endpoint : Related observe next (probeAt trace episode (time + 1)) := by
    rw [probe_after_foreign_edit trace episode bound different kept presence ended]
    exact StageSimulation.mark_related edited (trace.actor time) phases
  have probeSelf : Related observe (probeAt trace episode time) (probeAt trace episode time) :=
    EpisodeRollback.rollback_self episode.name (trace.notes time).1 ((trace.notes time).2 episode.name) sourceSelf
  have notes := EpisodeAnnotations.notesRelated_self probeSelf (probeNotes trace episode time)
    (probe_projects_notes trace episode maximal quiet lower (Nat.le_of_lt upper))
  have recorded := noteStep_related probeSelf endpoint (trace.actor time) (time + 1) notes
  have live := trace.live_unchanged bound fun name => by
    rw [ended, Transposition.mark_presence]
    exact presence name
  have mask := mask_unchanged trace episode live (trace.foreign_word_unchanged bound (Ne.symm different))
  have targetNotes := probe_notes_of_step trace episode bound
    (fun name present omitted => present (if_pos ((congrFun mask name).trans omitted)))
    (fun _ => probe_keeps_saved trace episode different kept)
    (fun _ => probe_keeps_saved trace episode different (by rwa [mask]))
  rw [← targetNotes] at recorded
  refine ⟨next, noteStep (probeAt trace episode time) next (trace.actor time) (time + 1) (probeNotes trace episode time),
    ⟨?_, rfl⟩, endpoint, recorded⟩
  rw [event]
  cases kind
  case unload => exact False.elim (native rfl)
  all_goals exact moved

private theorem provide_on_rollback (trace : Source) (episode : ClosedEpisode trace)
    (maximal : ∀ later : ClosedEpisode trace, ¬ EpisodeEdge episode later)
    (quiet : Progress.Quiet (trace.state last))
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops
      (tableSetoid observe (fun _ => True)) key)
    {time : Nat} (lower : episode.opened ≤ time) (upper : time ≤ episode.closed)
    {entry : RawFiber Name ops Code} {code : Code} {key : Key} {value : A}
    (different : trace.actor time ≠ episode.name)
    (kept : ¬ withdraws trace episode time (trace.actor time) = true)
    (present : trace.state time (trace.actor time) = some entry)
    (action : (encodeProgram program code).action = .provide key value)
    (declared : entry.component.provides key = true) (empty : entry.table key = none) :
    ∃ row, probeAt trace episode time (trace.actor time) = some row ∧ row.phase = entry.phase ∧
      Land (encodeProgram program) (trace.actor time) code (probeAt trace episode time)
        (write (probeAt trace episode time) (trace.actor time) key (some value))
        (.restrict (trace.actor time) key) ((encodeProgram program code).next (.value value)) ∧
      tableAt (replay (trace.notes time).1 ((trace.notes time).2 episode.name)
        (write (trace.state time) (trace.actor time) key (some value))) (trace.actor time) key = some value := by
  let actor := trace.actor time
  let before := trace.state time
  let meaning := TypedReplayContracts.coeffects ops observe program recovery commutative
  have bounded : time ≤ last := Nat.le_trans upper (Nat.le_of_lt episode.interval.bounded)
  obtain ⟨row, rowAt, fields⟩ := (probe_projects trace episode maximal quiet lower upper).forward_row kept present
  obtain ⟨phaseRow, phaseAt, samePhase⟩ := probe_keeps_phase trace episode different kept present
  have sameRow := Option.some.inj (rowAt.symm.trans phaseAt)
  subst phaseRow
  have landed : Land (encodeProgram program) actor code (probeAt trace episode time)
      (write (probeAt trace episode time) actor key (some value)) (.restrict actor key)
      ((encodeProgram program code).next (.value value)) :=
    .provide _ _ _ row key value action rowAt (by simpa only [← fields.component] using declared)
      ((fields.domain different key).mp empty)
  exact ⟨row, rowAt, samePhase, landed,
    EpisodeOperationReplay.rollback_foreign_provision meaning before episode.name actor key value
      (trace.notes time).1 ((trace.notes time).2 episode.name) (trace.projects time bounded episode.name)
      (trace.table_scope time bounded) different (trace.slot_history meaning time bounded actor key)
      (by simp [before, actor, present]) (by simp [tableAt, before, actor, present, empty])⟩

private theorem source_and_stack_self (trace : Source) (time : Nat) (bounded : time ≤ last)
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops
      (tableSetoid observe (fun _ => True)) key)
    {actor : Name} {entry : RawFiber Name ops Code} {code : Code} {stack : List I} {view : View Name Key}
    (present : trace.state time actor = some entry)
    (phase : entry.phase = .reloading code stack view) :
    Related observe (trace.state time) (trace.state time) ∧
      @StageSimulation.StackRelated Name Key A (TypedCoeffectReplay.setoid observe) stack stack := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  have self := trace.self_related time bounded (TypedRegistry.encoded_program_callbacks ops observe program recovery commutative)
  exact ⟨self, Transposition.self_reloading_stack self actor entry present code stack view phase⟩

omit [DecidableEq Name] [DecidableEq Key] in
private theorem landed_ne_unload {kind : Lifecycle} {next : Option Code}
    (label : kind.rule = Transposition.landedRule next) : kind ≠ .unload := by
  intro impossible
  subst kind
  cases next <;> simp [Lifecycle.rule, Transposition.landedRule] at label

theorem replay_operation_activation (trace : Source) (episode : ClosedEpisode trace)
    (maximal : ∀ later : ClosedEpisode trace, ¬ EpisodeEdge episode later)
    (quiet : Progress.Quiet (trace.state last))
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops
      (tableSetoid observe (fun _ => True)) key)
    {time : Nat} (lower : episode.opened ≤ time) (upper : time < episode.closed)
    {owner : Name} {entry : RawFiber Name ops Code}
    {kind : Lifecycle} (event : trace.event time = .lifecycle kind (trace.actor time))
    (different : trace.actor time ≠ episode.name)
    (kept : ¬ withdraws trace episode time (trace.actor time) = true)
    (present : trace.state time (trace.actor time) = some entry)
    {code : Code} {stack : List (Inverse Name Key A)} {view : View Name Key}
    (phase : entry.phase = .reloading code stack view)
    (target : Target (trace.state time) (trace.actor time) view)
    {key : Key} {call : A → Except PUnit.{u + 1} (A × (A → A) × A)}
    (action : (encodeProgram program code).action = .operate key call)
    {input output outcome : A} {inverse : A → A}
    (located : location (trace.state time) (trace.actor time) key = some (owner, input))
    (performed : call input = .ok (output, inverse, outcome))
    (label : kind.rule = Transposition.landedRule ((encodeProgram program code).next (.value outcome)))
    (ended : trace.state (time + 1) =
      mark (write (trace.state time) owner key (some output)) (trace.actor time)
        (Transposition.landedPhase ((encodeProgram program code).next (.value outcome))
          (.operate owner key inverse) stack view)) :
    ∃ next recorded,
      GuardedSuffix.Step (encodeProgram program) (trace.event time) (time + 1) (probeAt trace episode time)
        (probeNotes trace episode time) next recorded ∧
      Related observe next (probeAt trace episode (time + 1)) ∧
      Paired observe recorded (probeNotes trace episode (time + 1)) := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  let next := (encodeProgram program code).next (.value outcome)
  obtain ⟨_, after, captured, reverted, routed, _, landed, _, inverseRelated, rolled, related⟩ :=
    operate_on_rollback trace episode maximal quiet observe recovery commutative lower (Nat.le_of_lt upper)
      different kept present action located performed
  obtain ⟨row, holds, samePhase⟩ := probe_keeps_phase trace episode different kept present
  have projected := probe_projects trace episode maximal quiet lower (Nat.le_of_lt upper)
  have avoids := committed_avoids_closing trace episode maximal lower (Nat.le_of_lt upper) present
    (show entry.phase.committed = some view by simp [phase, Phase.committed])
  have actual := Transposition.landed_step (encodeProgram program) row stack view holds (samePhase.trans phase)
    (projected.target_forward kept present view avoids target) landed
  have bounded : time ≤ last := by have := episode.interval.bounded; omega
  obtain ⟨self, oldStack⟩ := source_and_stack_self trace time bounded observe recovery commutative present phase
  have phases := Transposition.landed_phases_related next (.operate owner key inverseRelated) stack oldStack view
  exact replay_write_step trace episode maximal quiet observe lower upper event (landed_ne_unload label)
    different kept self phases (located_owner_present located) (located_owner_present routed) ended rolled related
    (label.symm ▸ actual)

theorem replay_operation_divert (trace : Source) (episode : ClosedEpisode trace)
    (maximal : ∀ later : ClosedEpisode trace, ¬ EpisodeEdge episode later)
    (quiet : Progress.Quiet (trace.state last))
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops
      (tableSetoid observe (fun _ => True)) key)
    {time : Nat} (lower : episode.opened ≤ time) (upper : time < episode.closed)
    {owner : Name} {entry : RawFiber Name ops Code}
    (event : trace.event time = .lifecycle .divert (trace.actor time))
    (different : trace.actor time ≠ episode.name)
    (kept : ¬ withdraws trace episode time (trace.actor time) = true)
    (present : trace.state time (trace.actor time) = some entry)
    {code : Code} {stack : List (Inverse Name Key A)} {view : View Name Key}
    (phase : entry.phase = .reloading code stack view)
    (stale : ¬ Target (trace.state time) (trace.actor time) view)
    {key : Key} {call : A → Except PUnit.{u + 1} (A × (A → A) × A)}
    (action : (encodeProgram program code).action = .operate key call)
    {input output outcome : A} {inverse : A → A}
    (located : location (trace.state time) (trace.actor time) key = some (owner, input))
    (performed : call input = .ok (output, inverse, outcome))
    (ended : trace.state (time + 1) =
      mark (write (trace.state time) owner key (some output)) (trace.actor time)
        (.unloading (.operate owner key inverse :: stack) view)) :
    ∃ next recorded,
      GuardedSuffix.Step (encodeProgram program) (trace.event time) (time + 1) (probeAt trace episode time)
        (probeNotes trace episode time) next recorded ∧
      Related observe next (probeAt trace episode (time + 1)) ∧
      Paired observe recorded (probeNotes trace episode (time + 1)) := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  obtain ⟨_, after, captured, reverted, routed, _, landed, _, inverseRelated, rolled, related⟩ :=
    operate_on_rollback trace episode maximal quiet observe recovery commutative lower (Nat.le_of_lt upper)
      different kept present action located performed
  obtain ⟨row, holds, samePhase⟩ := probe_keeps_phase trace episode different kept present
  have projected := probe_projects trace episode maximal quiet lower (Nat.le_of_lt upper)
  have actual := Labeled.Step.divert _ _ _ row code stack view [.operate owner key captured] holds (samePhase.trans phase)
    (fun target => stale (projected.target_backward _ _ target)) (.inr ⟨_, _, landed, rfl⟩)
  have bounded : time ≤ last := by have := episode.interval.bounded; omega
  obtain ⟨self, oldStack⟩ := source_and_stack_self trace time bounded observe recovery commutative present phase
  have extended := StageSimulation.StackRelated.cons (.operate owner key inverseRelated) oldStack
  exact replay_write_step trace episode maximal quiet observe lower upper event (by decide)
    different kept self (.unloading view extended) (located_owner_present located) (located_owner_present routed)
    ended rolled related actual

theorem replay_provision_activation (trace : Source) (episode : ClosedEpisode trace)
    (maximal : ∀ later : ClosedEpisode trace, ¬ EpisodeEdge episode later)
    (quiet : Progress.Quiet (trace.state last))
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops
      (tableSetoid observe (fun _ => True)) key)
    {time : Nat} (lower : episode.opened ≤ time) (upper : time < episode.closed)
    {entry : RawFiber Name ops Code} {code : Code} {stack : List (Inverse Name Key A)} {view : View Name Key}
    {kind : Lifecycle} (event : trace.event time = .lifecycle kind (trace.actor time))
    (different : trace.actor time ≠ episode.name)
    (kept : ¬ withdraws trace episode time (trace.actor time) = true)
    (present : trace.state time (trace.actor time) = some entry)
    (phase : entry.phase = .reloading code stack view)
    (target : Target (trace.state time) (trace.actor time) view)
    {key : Key} {value : A} (action : (encodeProgram program code).action = .provide key value)
    (declared : entry.component.provides key = true) (empty : entry.table key = none)
    (label : kind.rule = Transposition.landedRule ((encodeProgram program code).next (.value value)))
    (ended : trace.state (time + 1) = mark (write (trace.state time) (trace.actor time) key (some value))
      (trace.actor time) (Transposition.landedPhase ((encodeProgram program code).next (.value value))
        (.restrict (trace.actor time) key) stack view)) :
    ∃ next recorded,
      GuardedSuffix.Step (encodeProgram program) (trace.event time) (time + 1) (probeAt trace episode time)
        (probeNotes trace episode time) next recorded ∧
      Related observe next (probeAt trace episode (time + 1)) ∧
      Paired observe recorded (probeNotes trace episode (time + 1)) := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  let next := (encodeProgram program code).next (.value value)
  obtain ⟨row, found, aligned, landed, rolled⟩ := provide_on_rollback trace episode maximal quiet observe recovery
    commutative lower (Nat.le_of_lt upper) different kept present action declared empty
  have projection := probe_projects trace episode maximal quiet lower (Nat.le_of_lt upper)
  have avoids := committed_avoids_closing trace episode maximal lower (Nat.le_of_lt upper) present
    (show entry.phase.committed = some view by simp [phase, Phase.committed])
  have actual := Transposition.landed_step (encodeProgram program) row stack view found (aligned.trans phase)
    (projection.target_forward kept present view avoids target) landed
  have bounded : time ≤ last := by have := episode.interval.bounded; omega
  obtain ⟨self, oldStack⟩ := source_and_stack_self trace time bounded observe recovery commutative present phase
  have phases := Transposition.landed_phases_related next (.restrict (trace.actor time) key) stack oldStack view
  exact replay_write_step trace episode maximal quiet observe lower upper event (landed_ne_unload label)
    different kept self phases (by simp [present]) (by simp [found]) ended rolled (Setoid.refl value)
    (label.symm ▸ actual)

theorem replay_provision_divert (trace : Source) (episode : ClosedEpisode trace)
    (maximal : ∀ later : ClosedEpisode trace, ¬ EpisodeEdge episode later)
    (quiet : Progress.Quiet (trace.state last))
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops
      (tableSetoid observe (fun _ => True)) key)
    {time : Nat} (lower : episode.opened ≤ time) (upper : time < episode.closed)
    {entry : RawFiber Name ops Code} {code : Code} {stack : List (Inverse Name Key A)} {view : View Name Key}
    (event : trace.event time = .lifecycle .divert (trace.actor time))
    (different : trace.actor time ≠ episode.name)
    (kept : ¬ withdraws trace episode time (trace.actor time) = true)
    (present : trace.state time (trace.actor time) = some entry)
    (phase : entry.phase = .reloading code stack view)
    (stale : ¬ Target (trace.state time) (trace.actor time) view)
    {key : Key} {value : A} (action : (encodeProgram program code).action = .provide key value)
    (declared : entry.component.provides key = true) (empty : entry.table key = none)
    (ended : trace.state (time + 1) = mark (write (trace.state time) (trace.actor time) key (some value))
      (trace.actor time) (.unloading (.restrict (trace.actor time) key :: stack) view)) :
    ∃ next recorded,
      GuardedSuffix.Step (encodeProgram program) (trace.event time) (time + 1) (probeAt trace episode time)
        (probeNotes trace episode time) next recorded ∧
      Related observe next (probeAt trace episode (time + 1)) ∧
      Paired observe recorded (probeNotes trace episode (time + 1)) := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  obtain ⟨row, found, aligned, landed, rolled⟩ := provide_on_rollback trace episode maximal quiet observe recovery
    commutative lower (Nat.le_of_lt upper) different kept present action declared empty
  have projection := probe_projects trace episode maximal quiet lower (Nat.le_of_lt upper)
  have actual := Labeled.Step.divert _ _ _ row code stack view [.restrict (trace.actor time) key] found
    (aligned.trans phase) (fun target => stale (projection.target_backward _ _ target)) (.inr ⟨_, _, landed, rfl⟩)
  have bounded : time ≤ last := by have := episode.interval.bounded; omega
  obtain ⟨self, oldStack⟩ := source_and_stack_self trace time bounded observe recovery commutative present phase
  exact replay_write_step trace episode maximal quiet observe lower upper event (by decide)
    different kept self (.unloading view (.cons (.restrict _ _) oldStack)) (by simp [present]) (by simp [found])
    ended rolled (Setoid.refl value) actual

end Cordis.Repairs.GuardedHistory
