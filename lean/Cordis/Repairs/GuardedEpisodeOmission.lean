import Cordis.Repairs.GuardedEpisodeReplay
import Cordis.Repairs.EpisodeOmission

/-! Omitting the selected actor's interior lifecycle steps exactly preserves
the guarded rollback probe and its source-derived cut notes. -/
namespace Cordis.Repairs.GuardedHistory
open Calculus Stages Incarnation IncarnationReplay LegalHistory
open PartialReplayRegistry (saved)
open EpisodeOmission (mark_overwrite)
open EpisodeRollback (replay_mark)
open Vestigial (noteStep)
universe u
variable {Name Key Value Code Error : Type u} [DecidableEq Name] [DecidableEq Key]
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
local notation "I" => Inverse Name Key Value
local notation "C" => Capture Name Key Value
variable {program : Code → Instruction Name Key Value Code Error} {last : Nat}

private theorem probe_omits_own_mark (trace : Trace program last) (episode : ClosedEpisode trace)
    {time : Nat} (bound : time < last)
    {row : F} (present : trace.state time episode.name = some row)
    (phase : Phase Name Key Code I) (stack : phase.accumulator = row.phase.accumulator)
    (ended : trace.state (time + 1) = mark (trace.state time) episode.name phase) :
    probeAt trace episode (time + 1) = probeAt trace episode time := by
  have stable : saved (trace.state (time + 1)) = saved (trace.state time) := by
    rw [ended]
    funext name
    rw [PartialReplayRegistry.saved_mark _ _ _ present, stack]
    by_cases same : name = episode.name <;> simp [same, saved, present]
  have words : (trace.notes (time + 1)).2 episode.name = (trace.notes time).2 episode.name := by
    rw [(trace.step time bound).2]
    change advance _ _ (trace.actor time) (time + 1) (trace.notes time).2 episode.name = _
    rw [advance_control _ _ _ (trace.projects time (Nat.le_of_lt bound)) stable]
  have births := trace.live_unchanged bound fun name => by rw [ended, Transposition.mark_presence]
  have masks : withdraws trace episode (time + 1) = withdraws trace episode time := by
    funext name
    simp only [withdraws, words, births]
  unfold probeAt rollbackOf
  rw [masks, words, births, ended, replay_mark]
  dsimp only
  rw [mark_overwrite]

private theorem word_after_own_capture (trace : Trace program last) (episode : ClosedEpisode trace)
    {time : Nat} (bound : time < last) (actor : trace.actor time = episode.name) {middle : R} {code : Code} {next : Option Code}
    {inverse : I} (landed : Land program episode.name code (trace.state time) middle inverse next)
    {row : F} (present : trace.state time episode.name = some row)
    {phase : Phase Name Key Code I} (stack : phase.accumulator = inverse :: row.phase.accumulator)
    (ended : trace.state (time + 1) = mark middle episode.name phase) :
    (trace.notes (time + 1)).2 episode.name =
      (⟨inverse, time + 1⟩ : C) :: (trace.notes time).2 episode.name := by
  have pushed : ∀ name, saved (trace.state (time + 1)) name =
      if name = trace.actor time then inverse :: saved (trace.state time) name else saved (trace.state time) name := by
    rw [actor, ended]
    exact PartialReplayRegistry.saved_after_landing program landed row present phase stack
  rw [(trace.step time bound).2]
  change advance (trace.state time) (trace.state (time + 1)) (trace.actor time) (time + 1)
    ((trace.notes time).2) episode.name = _
  rw [advance_capture _ _ _ _ pushed]
  simp [actor]

/-- Exact primitive recovery cancels a pushed unit, restriction or
operation capture before the older rollback word runs. -/
private theorem probe_omits_recovered_capture (trace : Trace program last) (episode : ClosedEpisode trace)
    {time : Nat} (bound : time < last) (actor : trace.actor time = episode.name) {middle : R} {code : Code} {next : Option Code}
    {inverse : I} (landed : Land program episode.name code (trace.state time) middle inverse next)
    {row : F} (present : trace.state time episode.name = some row)
    {phase : Phase Name Key Code I} (stack : phase.accumulator = inverse :: row.phase.accumulator)
    (ended : trace.state (time + 1) = mark middle episode.name phase)
    (ordinary : ∀ child, inverse ≠ .retire child)
    (presence : ∀ name, middle name = none ↔ trace.state time name = none)
    (recovers : Stages.undo inverse middle = trace.state time) :
    probeAt trace episode (time + 1) = probeAt trace episode time := by
  let head : C := ⟨inverse, time + 1⟩
  let live := (trace.notes time).1
  have words := word_after_own_capture trace episode bound actor landed present stack ended
  have births := trace.live_unchanged bound fun name => by
    rw [ended, Transposition.mark_presence]
    exact presence name
  have uninterested (name : Name) : Capture.retires live name head = false := by
    cases inverse with
    | retire child => exact False.elim (ordinary child rfl)
    | _ => rfl
  have applied : head.apply live middle = trace.state time := by
    cases inverse with
    | retire child => exact False.elim (ordinary child rfl)
    | _ => exact recovers
  have masks : withdraws trace episode (time + 1) = withdraws trace episode time := by
    funext name
    simp only [withdraws, words, births, List.any_cons]
    change (Capture.retires live name head || _) = _
    rw [uninterested name, Bool.false_or]
  unfold probeAt rollbackOf
  rw [masks, words, births, ended, replay_mark]
  change (fun name => if withdraws trace episode time name then none else
    mark (mark (replay live ((trace.notes time).2 episode.name) (head.apply live middle))
      episode.name phase) episode.name .inactive name) = _
  rw [applied, mark_overwrite]

/-- The pushed retirement matches precisely the new birth. Erasing its
row leaves the old rollback word acting on the original registry. -/
private theorem probe_omits_own_birth (trace : Trace program last) (episode : ClosedEpisode trace)
    {time : Nat} (bound : time < last) (actor : trace.actor time = episode.name) {code : Code} {child : Name}
    {component : Component Key Code} (action : (program code).action = .instantiate component)
    (ready : Insertable (trace.state time) child component (some episode.name))
    {row : F} (present : trace.state time episode.name = some row)
    {phase : Phase Name Key Code I} (stack : phase.accumulator = .retire child :: row.phase.accumulator)
    (ended : trace.state (time + 1) = mark
      (put (trace.state time) child (fresh component (some episode.name))) episode.name phase) :
    probeAt trace episode (time + 1) = probeAt trace episode time := by
  let head : C := ⟨.retire child, time + 1⟩
  let word := (trace.notes time).2 episode.name
  let live := (trace.notes time).1
  let later := (trace.notes (time + 1)).1
  let middle := put (trace.state time) child (fresh component (some episode.name))
  let applied := head.apply later middle
  have land : Land program episode.name code (trace.state time) middle (.retire child)
      ((program code).next (.child child)) := .instantiate _ _ _ _ _ action ready
  have words : (trace.notes (time + 1)).2 episode.name = head :: word :=
    word_after_own_capture trace episode bound actor land present stack ended
  have born : trace.state (time + 1) child ≠ none := by
    rw [ended, ne_eq, Transposition.mark_presence, put_self]
    simp
  have bornAt : later child = some (time + 1) := by
    change (trace.notes (time + 1)).1 child = _
    rw [trace.notes_eq (time + 1) (by omega)]
    exact birthAt_of_created ready.1 born
  have outside (name : Name) (different : name ≠ child) : later name = live name := by
    apply trace.live_unchanged_at bound
    rw [ended, Transposition.mark_presence, Transposition.put_other _ _ _ _ different]
  have earlier : erase applied child = trace.state time := by
    change erase (if later child = some (time + 1) then Calculus.retire middle child else middle) child = _
    rw [if_pos bornAt]
    funext name
    by_cases selected : name = child
    · subst name
      simp [erase, ready.1]
    · simp [erase, Calculus.retire, Calculus.modify, middle, put, selected]
  have replayErased := Vestigial.replay_erase applied child
    (fun name different => (outside name different).symm) word
  rw [earlier] at replayErased
  have markedErased := congrArg (fun state => mark state episode.name .inactive) replayErased
  unfold mark at markedErased
  dsimp only at markedErased
  rw [Vestigial.modify_erase] at markedErased
  have newChild : withdraws trace episode (time + 1) child = true := by
    change ((trace.notes (time + 1)).2 episode.name).any (Capture.retires later child) = true
    simp [words, Capture.retires, head, bornAt]
  have oldVacant : mark (replay live word (trace.state time)) episode.name .inactive child = none :=
    (Transposition.mark_presence _ _ _ _).mpr ((replay_presence live word _ child).mpr ready.1)
  have maskOutside (name : Name) (different : name ≠ child) :
      withdraws trace episode (time + 1) name = withdraws trace episode time name := by
    change ((trace.notes (time + 1)).2 episode.name).any (Capture.retires later name) =
      word.any (Capture.retires live name)
    rw [words, List.any_cons]
    simp only [head, Capture.retires, different, false_and, decide_false, Bool.false_or]
    apply List.any_congr rfl
    intro capture
    cases token : capture.token with
    | retire target =>
      by_cases selected : name = target
      · subst target
        simp only [Capture.retires, token, outside name different]
      · simp [Capture.retires, token, selected]
    | _ => simp [Capture.retires, token]
  unfold probeAt rollbackOf
  rw [words, ended, replay_mark]
  change (fun name => if withdraws trace episode (time + 1) name then none else
    mark (mark (replay later word applied) episode.name phase) episode.name .inactive name) = _
  rw [mark_overwrite]
  funext name
  change (if withdraws trace episode (time + 1) name then none else
    mark (replay later word applied) episode.name .inactive name) =
      if withdraws trace episode time name then none else mark (replay live word (trace.state time)) episode.name .inactive name
  by_cases selected : name = child
  · subst name
    simp [newChild, oldVacant]
  · have atName : mark (replay live word (trace.state time)) episode.name .inactive name =
        mark (replay later word applied) episode.name .inactive name := by
      simpa only [erase, if_neg selected] using congrFun markedErased name
    rw [maskOutside name selected, atName]

section Typed
open PaperEffectEquations (CoeffectOperations ValueOperationWitness)
open TypedRegistry (encodeProgram RawRegistry RawFiber Scalar)
variable {V : Key → Type u} {ops : CoeffectOperations V}
variable {typedProgram : Code → TypedRegistry.Instruction Name ops Code}
local notation "TypedSource" => Trace (encodeProgram typedProgram) last
local notation "A" => Scalar ops

private theorem probe_omits_landing (trace : TypedSource) (episode : ClosedEpisode trace)
    (recovery : ValueOperationWitness ops)
    {time : Nat} (bound : time < last) (actor : trace.actor time = episode.name)
    {middle : RawRegistry Name ops Code} {code : Code} {next : Option Code} {inverse : Inverse Name Key A}
    (landed : Land (encodeProgram typedProgram) episode.name code (trace.state time) middle inverse next)
    {row : RawFiber Name ops Code} (present : trace.state time episode.name = some row)
    {phase : Phase Name Key Code (Inverse Name Key A)} (stack : phase.accumulator = inverse :: row.phase.accumulator)
    (ended : trace.state (time + 1) = mark middle episode.name phase) :
    probeAt trace episode (time + 1) = probeAt trace episode time := by
  have recovers (ordinary : ∀ child, inverse ≠ .retire child) := EpisodeOmission.landing_recovers recovery landed ordinary
  cases landed with
  | instantiate _ _ _ component child action ready =>
    exact probe_omits_own_birth trace episode bound actor action ready present stack ended
  | unit _ _ _ action =>
    exact probe_omits_recovered_capture trace episode bound actor (.unit _ _ _ action) present stack ended
      (by intro _ impossible; cases impossible) (fun _ => Iff.rfl) rfl
  | provide _ _ _ fiber key value action found declared empty =>
    have ordinary : ∀ child, (.restrict episode.name key : Inverse Name Key A) ≠ .retire child := by
      intro _ impossible; cases impossible
    have original := recovers ordinary
    exact probe_omits_recovered_capture trace episode bound actor (.provide _ _ _ _ _ _ action found declared empty)
      present stack ended ordinary original.1 original.2
  | operate _ _ _ key callback owner input output undo outcome action located called =>
    have ordinary : ∀ child, (.operate owner key undo : Inverse Name Key A) ≠ .retire child := by
      intro _ impossible; cases impossible
    have original := recovers ordinary
    exact probe_omits_recovered_capture trace episode bound actor (.operate _ _ _ _ _ _ _ _ _ _ action located called)
      present stack ended ordinary original.1 original.2

/-- Each actual lifecycle event of the selected actor between the opening
and closing boundaries contributes no transition to the projected history. -/
private theorem probe_omits_selected_registry (trace : TypedSource) (episode : ClosedEpisode trace)
    (recovery : ValueOperationWitness ops)
    {time : Nat} (lower : episode.opened ≤ time) (upper : time < episode.closed)
    (actor : trace.actor time = episode.name)
    {kind : Lifecycle} (event : trace.event time = .lifecycle kind (trace.actor time)) :
    probeAt trace episode (time + 1) = probeAt trace episode time := by
  have bound : time < last := Nat.lt_trans upper episode.interval.bounded
  rcases transition_cases (trace.step time bound).1 with actual | unloadStep
  · have lifecycle : EpisodeSelection.lifecycle (trace.rule time) = true := by
      cases kind <;> simp [Trace.rule, event, eventRule, Lifecycle.rule, EpisodeSelection.lifecycle]
    change Labeled.Step (encodeProgram typedProgram) (trace.rule time) (trace.actor time) _ _ at actual
    rw [actor] at actual
    generalize tag : trace.rule time = rule at actual lifecycle
    generalize endpoint : trace.state (time + 1) = after at actual
    cases actual with
    | insert | retire | remove => simp [EpisodeSelection.lifecycle] at lifecycle
    | begin _ _ row view present inactive _ _ =>
      exact False.elim (episode.interval.installed time lower (by omega)
        (by simp [ControlFrame.viewAt, present, inactive, Phase.committed]))
    | iter _ _ _ row _ _ _ _ _ present phase _ landed =>
      exact probe_omits_landing trace episode recovery bound actor landed present
        (by simp [phase, Phase.accumulator]) endpoint
    | finish _ _ _ row _ _ _ _ present phase _ landed =>
      exact probe_omits_landing trace episode recovery bound actor landed present
        (by simp [phase, Phase.accumulator]) endpoint
    | divert _ _ _ row _ _ _ tail present phase _ branch =>
      rcases branch with ⟨rfl, rfl⟩ | ⟨inverse, next, landed, rfl⟩
      · exact probe_omits_own_mark trace episode bound present _
          (by simp [phase, Phase.accumulator]) endpoint
      · exact probe_omits_landing trace episode recovery bound actor landed present
          (by simp [phase, Phase.accumulator]) endpoint
    | leave _ _ row _ _ present phase _ =>
      exact probe_omits_own_mark trace episode bound present _
        (by simp [phase, Phase.accumulator]) endpoint
    | unload _ _ row word _ present _ _ =>
      obtain ⟨surviving, found, _⟩ := Ordering.discharge_existing_phases (trace.state time) word episode.name row present
      exact False.elim (episode.interval.installed (time + 1) (by omega) (by omega)
        (by simp [endpoint, ControlFrame.viewAt, mark_self _ _ _ _ found, Phase.committed]))
  · obtain ⟨other, unloadEvent, unload⟩ := unloadStep
    have acted : trace.actor time = other := by simp [Trace.actor, unloadEvent, Vestigial.eventActor]
    have gone := unload_views unload episode.name
    rw [if_pos (actor.symm.trans acted)] at gone
    exact False.elim (episode.interval.installed (time + 1) (by omega) (by omega) gone)

theorem probe_omits_selected_step (trace : TypedSource) (episode : ClosedEpisode trace)
    (maximal : ∀ later : ClosedEpisode trace, ¬ EpisodeEdge episode later)
    (quiet : Progress.Quiet (trace.state last)) (recovery : ValueOperationWitness ops)
    {time : Nat} (lower : episode.opened ≤ time) (upper : time < episode.closed)
    (actor : trace.actor time = episode.name)
    {kind : Lifecycle} (event : trace.event time = .lifecycle kind (trace.actor time)) :
    probeAt trace episode (time + 1) = probeAt trace episode time ∧
      probeNotes trace episode (time + 1) = probeNotes trace episode time := by
  have bound : time < last := Nat.lt_trans upper episode.interval.bounded
  have same := probe_omits_selected_registry trace episode recovery lower upper actor event
  have notes := probe_notes_of_step trace episode bound
    (fun name present hidden => present (same.symm ▸ if_pos hidden))
    (fun different => False.elim (different actor)) (fun different => False.elim (different actor))
  refine ⟨same, ?_⟩
  rw [notes, same]
  apply Prod.ext
  · funext name
    change (probeAt trace episode time name).map (fun _ => ((probeNotes trace episode time).1 name).getD (time + 1)) = _
    have agrees := probe_births trace episode time (Nat.le_of_lt bound) name
    cases birth : (probeNotes trace episode time).1 name with
    | none => rw [agrees.mp birth]; rfl
    | some born =>
      cases present : probeAt trace episode time name with
      | none =>
        have absent := agrees.mpr present
        rw [birth] at absent
        cases absent
      | some row => rfl
  · exact advance_control _ _ _ (probe_projects_notes trace episode maximal quiet lower (Nat.le_of_lt upper)) rfl

end Typed
end Cordis.Repairs.GuardedHistory
