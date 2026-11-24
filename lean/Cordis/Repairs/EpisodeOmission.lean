import Cordis.Repairs.EpisodeRollback
import Cordis.TypedCallbackExchange

/-! The interior lifecycle steps of the selected episode become stutters
under its rollback probe. The just-captured inverse recovers a unit,
provision or operation exactly. For a birth, the new stamp identifies the
single row omitted by the new retirement capture. -/
namespace Cordis.Repairs.EpisodeOmission
open Calculus Stages Indexed Incarnation IncarnationReplay
open EpisodeDependencies EpisodeBoundary EpisodeRollback
open PartialReplayRegistry (saved)
universe u
variable {Name Key Value Code Error : Type u} [DecidableEq Name] [DecidableEq Key]
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
local notation "I" => Inverse Name Key Value
local notation "C" => Capture Name Key Value
variable {program : Code → Instruction Name Key Value Code Error} {last : Nat}
local notation "History" => Trace program (fun _ => none : R) last

omit [DecidableEq Key] in
theorem mark_overwrite (state : R) (actor : Name) (first second : Phase Name Key Code I) :
    mark (mark state actor first) actor second = mark state actor second := by
  funext name
  by_cases selected : name = actor <;> simp [mark, Calculus.modify, selected, Option.map_map, Function.comp_def]

private theorem probe_omits_own_mark (trace : History) (episode : ClosedEpisode trace)
    {time : Nat} (bounded : time ≤ last)
    {row : F} (present : trace.state time episode.name = some row)
    (phase : Phase Name Key Code I) (stack : phase.accumulator = row.phase.accumulator)
    (ended : trace.state (time + 1) = mark (trace.state time) episode.name phase) :
    probeAt trace episode (time + 1) = probeAt trace episode time := by
  have stable : saved (trace.state (time + 1)) = saved (trace.state time) := by
    rw [ended]
    funext name
    rw [PartialReplayRegistry.saved_mark _ _ _ present, stack]
    by_cases same : name = episode.name <;> simp [same, saved, present]
  have words : track trace.state trace.actor (time + 1) episode.name = track trace.state trace.actor time episode.name :=
    congrFun (advance_control (trace.actor time) (time + 1) _ (tracked_stack trace time bounded).projects stable) episode.name
  have births := birthAt_same_presence trace.state time fun name => by rw [ended, Transposition.mark_presence]
  have masks : withdraws trace episode (time + 1) = withdraws trace episode time := by
    funext name
    simp only [withdraws, words, births]
  unfold probeAt rollbackOf
  rw [masks, words, births, ended, replay_mark]
  dsimp only
  rw [mark_overwrite]

private theorem word_after_own_capture (trace : History) (episode : ClosedEpisode trace)
    {time : Nat} (actor : trace.actor time = episode.name) {middle : R} {code : Code} {next : Option Code}
    {inverse : I} (landed : Land program episode.name code (trace.state time) middle inverse next)
    {row : F} (present : trace.state time episode.name = some row)
    {phase : Phase Name Key Code I} (stack : phase.accumulator = inverse :: row.phase.accumulator)
    (ended : trace.state (time + 1) = mark middle episode.name phase) :
    track trace.state trace.actor (time + 1) episode.name =
      (⟨inverse, time + 1⟩ : C) :: track trace.state trace.actor time episode.name := by
  have pushed : ∀ name, saved (trace.state (time + 1)) name =
      if name = trace.actor time then inverse :: saved (trace.state time) name else saved (trace.state time) name := by
    rw [actor, ended]
    exact PartialReplayRegistry.saved_after_landing program landed row present phase stack
  change advance (trace.state time) (trace.state (time + 1)) (trace.actor time) (time + 1)
    (track trace.state trace.actor time) episode.name = _
  rw [advance_capture _ _ _ _ pushed]
  simp [actor]

/-- Exact primitive recovery cancels a pushed unit, restriction or
operation capture before the older rollback word runs. -/
private theorem probe_omits_recovered_capture (trace : History) (episode : ClosedEpisode trace)
    {time : Nat} (actor : trace.actor time = episode.name) {middle : R} {code : Code} {next : Option Code}
    {inverse : I} (landed : Land program episode.name code (trace.state time) middle inverse next)
    {row : F} (present : trace.state time episode.name = some row)
    {phase : Phase Name Key Code I} (stack : phase.accumulator = inverse :: row.phase.accumulator)
    (ended : trace.state (time + 1) = mark middle episode.name phase)
    (ordinary : ∀ child, inverse ≠ .retire child)
    (presence : ∀ name, middle name = none ↔ trace.state time name = none)
    (recovers : Stages.undo inverse middle = trace.state time) :
    probeAt trace episode (time + 1) = probeAt trace episode time := by
  let head : C := ⟨inverse, time + 1⟩
  let live := fun name => birthAt trace.state name time
  have words := word_after_own_capture trace episode actor landed present stack ended
  have births := birthAt_same_presence trace.state time fun name => by
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
    mark (mark (replay live (track trace.state trace.actor time episode.name) (head.apply live middle))
      episode.name phase) episode.name .inactive name) = _
  rw [applied, mark_overwrite]

/-- The pushed retirement matches precisely the new birth. Erasing its
row leaves the old rollback word acting on the original registry. -/
private theorem probe_omits_own_birth (trace : History) (episode : ClosedEpisode trace)
    {time : Nat} (actor : trace.actor time = episode.name) {code : Code} {child : Name}
    {component : Component Key Code} (action : (program code).action = .instantiate component)
    (ready : Insertable (trace.state time) child component (some episode.name))
    {row : F} (present : trace.state time episode.name = some row)
    {phase : Phase Name Key Code I} (stack : phase.accumulator = .retire child :: row.phase.accumulator)
    (ended : trace.state (time + 1) = mark
      (put (trace.state time) child (fresh component (some episode.name))) episode.name phase) :
    probeAt trace episode (time + 1) = probeAt trace episode time := by
  let head : C := ⟨.retire child, time + 1⟩
  let word := track trace.state trace.actor time episode.name
  let live := fun name => birthAt trace.state name time
  let later := fun name => birthAt trace.state name (time + 1)
  let middle := put (trace.state time) child (fresh component (some episode.name))
  let applied := head.apply later middle
  have land : Land program episode.name code (trace.state time) middle (.retire child)
      ((program code).next (.child child)) := .instantiate _ _ _ _ _ action ready
  have words : track trace.state trace.actor (time + 1) episode.name = head :: word :=
    word_after_own_capture trace episode actor land present stack ended
  have born : trace.state (time + 1) child ≠ none := by
    rw [ended, ne_eq, Transposition.mark_presence, put_self]
    simp
  have bornAt : later child = some (time + 1) := birthAt_of_created ready.1 born
  have outside (name : Name) (different : name ≠ child) : later name = live name := by
    apply birthAt_same_presence_at
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
    change (track trace.state trace.actor (time + 1) episode.name).any (Capture.retires later child) = true
    simp [words, Capture.retires, head, bornAt]
  have oldVacant : mark (replay live word (trace.state time)) episode.name .inactive child = none :=
    (Transposition.mark_presence _ _ _ _).mpr ((replay_presence live word _ child).mpr ready.1)
  have maskOutside (name : Name) (different : name ≠ child) :
      withdraws trace episode (time + 1) name = withdraws trace episode time name := by
    change (track trace.state trace.actor (time + 1) episode.name).any (Capture.retires later name) =
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

private theorem write_presence (state : R) (owner : Name) (key : Key) (value : Value) (name : Name) :
    write state owner key (some value) name = none ↔ state name = none := by
  by_cases selected : name = owner <;> simp [write, Calculus.modify, selected]

private theorem restore_written_slot (state : R) (owner : Name) (key : Key) (value : Value)
    (restore : Option Value → Option Value) {row : F} (present : state owner = some row)
    (recovered : restore (some value) = row.table key) :
    Calculus.modify (write state owner key (some value)) owner (fun fiber => {fiber with
      table := fun query => if query = key then restore (fiber.table key) else fiber.table query}) = state := by
  funext name
  by_cases selected : name = owner
  · subst name
    simp only [write, Calculus.modify_self, present, Option.map_some, if_true]
    have tables : (fun query => if query = key then restore (some value)
      else if query = key then some value else row.table query) = row.table := by
      funext query
      by_cases same : query = key <;> simp [same, recovered]
    exact congrArg (fun table => some {row with table := table}) tables
  · simp [write, Calculus.modify, selected]

section Typed
open PaperEffectEquations (CoeffectOperations ValueOperationWitness)
open TypedRegistry (encodeProgram RawRegistry RawFiber Scalar)
variable {V : Key → Type u} {ops : CoeffectOperations V}
variable {typedProgram : Code → TypedRegistry.Instruction Name ops Code}
local notation "TypedHistory" => Trace (encodeProgram typedProgram) (fun _ => none : RawRegistry Name ops Code) last
local notation "A" => Scalar ops

/-- Recovery for a unit, restriction or operation token is exact on the
registry produced by the actual landing. Allocation has its own birth case. -/
theorem landing_recovers (recovery : ValueOperationWitness ops)
    {state middle : RawRegistry Name ops Code} {actor : Name} {code : Code}
    {next : Option Code} {inverse : Inverse Name Key A}
    (landed : Land (encodeProgram typedProgram) actor code state middle inverse next)
    (ordinary : ∀ child, inverse ≠ .retire child) :
    (∀ name, middle name = none ↔ state name = none) ∧ Stages.undo inverse middle = state := by
  cases landed with
  | unit => exact ⟨fun _ => Iff.rfl, rfl⟩
  | provide _ _ _ fiber key value _ found _ empty =>
    exact ⟨write_presence _ _ _ _, restore_written_slot state actor key value (fun _ => none) found empty.symm⟩
  | operate _ _ _ key callback owner input output undo outcome action located called =>
    obtain ⟨provider, bound, old⟩ := Safety.location_binding _ _ _ _ _ located
    obtain ⟨name, argument, rfl⟩ := TypedRegistry.encoded_operation_action ops typedProgram code action
    obtain ⟨before, after, saved, result, beforeEq, performed, afterEq, savedEq, _⟩ :=
      TypedRegistry.encoded_call_sound ops called
    have recovered : undo output = input := by
      rw [savedEq, afterEq, beforeEq, TypedCoeffectReplay.encodeMap_pack,
        recovery key name argument before after saved result performed]
      rfl
    exact ⟨write_presence _ _ _ _, restore_written_slot state owner key output (Option.map undo) bound
      (show (some output).map undo = provider.table key from (congrArg some recovered).trans old.symm)⟩
  | instantiate _ _ _ _ child _ _ => exact False.elim (ordinary child rfl)

private theorem probe_omits_landing (trace : TypedHistory) (episode : ClosedEpisode trace)
    (recovery : ValueOperationWitness ops)
    {time : Nat} (actor : trace.actor time = episode.name)
    {middle : RawRegistry Name ops Code} {code : Code} {next : Option Code} {inverse : Inverse Name Key A}
    (landed : Land (encodeProgram typedProgram) episode.name code (trace.state time) middle inverse next)
    {row : RawFiber Name ops Code} (present : trace.state time episode.name = some row)
    {phase : Phase Name Key Code (Inverse Name Key A)} (stack : phase.accumulator = inverse :: row.phase.accumulator)
    (ended : trace.state (time + 1) = mark middle episode.name phase) :
    probeAt trace episode (time + 1) = probeAt trace episode time := by
  have recovers (ordinary : ∀ child, inverse ≠ .retire child) := landing_recovers recovery landed ordinary
  cases landed with
  | instantiate _ _ _ component child action ready =>
    exact probe_omits_own_birth trace episode actor action ready present stack ended
  | unit _ _ _ action =>
    exact probe_omits_recovered_capture trace episode actor (.unit _ _ _ action) present stack ended
      (by intro _ impossible; cases impossible) (fun _ => Iff.rfl) rfl
  | provide _ _ _ fiber key value action found declared empty =>
    have ordinary : ∀ child, (.restrict episode.name key : Inverse Name Key A) ≠ .retire child := by
      intro _ impossible; cases impossible
    have original := recovers ordinary
    exact probe_omits_recovered_capture trace episode actor (.provide _ _ _ _ _ _ action found declared empty)
      present stack ended ordinary original.1 original.2
  | operate _ _ _ key callback owner input output undo outcome action located called =>
    have ordinary : ∀ child, (.operate owner key undo : Inverse Name Key A) ≠ .retire child := by
      intro _ impossible; cases impossible
    have original := recovers ordinary
    exact probe_omits_recovered_capture trace episode actor (.operate _ _ _ _ _ _ _ _ _ _ action located called)
      present stack ended ordinary original.1 original.2

/-- Each actual lifecycle event of the selected actor between the opening
and closing boundaries contributes no transition to the projected history. -/
theorem probe_omits_selected_step (trace : TypedHistory) (episode : ClosedEpisode trace)
    (recovery : ValueOperationWitness ops)
    {time : Nat} (lower : episode.opened ≤ time) (upper : time < episode.closed)
    (actor : trace.actor time = episode.name)
    (lifecycle : EpisodeSelection.lifecycle (trace.rule time) = true) :
    probeAt trace episode (time + 1) = probeAt trace episode time := by
  have lastBound := episode.interval.bounded
  have bounded : time ≤ last := by omega
  have actual := trace.step time (by omega)
  rw [actor] at actual
  generalize tag : trace.rule time = rule at actual lifecycle
  generalize endpoint : trace.state (time + 1) = after at actual
  cases actual with
  | insert | retire | remove => simp [EpisodeSelection.lifecycle] at lifecycle
  | begin _ _ row view present inactive _ _ =>
    exact False.elim (episode.interval.installed time lower (by omega)
      (by simp [ControlFrame.viewAt, present, inactive, Phase.committed]))
  | iter _ _ _ row _ _ _ _ _ present phase _ landed =>
    exact probe_omits_landing trace episode recovery actor landed present
      (by simp [phase, Phase.accumulator]) endpoint
  | finish _ _ _ row _ _ _ _ present phase _ landed =>
    exact probe_omits_landing trace episode recovery actor landed present
      (by simp [phase, Phase.accumulator]) endpoint
  | divert _ _ _ row _ _ _ tail present phase _ branch =>
    rcases branch with ⟨rfl, rfl⟩ | ⟨inverse, next, landed, rfl⟩
    · exact probe_omits_own_mark trace episode bounded present _
        (by simp [phase, Phase.accumulator]) endpoint
    · exact probe_omits_landing trace episode recovery actor landed present
        (by simp [phase, Phase.accumulator]) endpoint
  | leave _ _ row _ _ present phase _ =>
    exact probe_omits_own_mark trace episode bounded present _
      (by simp [phase, Phase.accumulator]) endpoint
  | unload _ _ row word _ present _ _ =>
    obtain ⟨surviving, found, _⟩ := Ordering.discharge_existing_phases (trace.state time) word episode.name row present
    exact False.elim (episode.interval.installed (time + 1) (by omega) (by omega)
      (by simp [endpoint, ControlFrame.viewAt, mark_self _ _ _ _ found, Phase.committed]))

end Typed

end Cordis.Repairs.EpisodeOmission
