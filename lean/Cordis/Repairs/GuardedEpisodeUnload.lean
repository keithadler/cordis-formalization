import Cordis.Repairs.GuardedEpisodeBoundary
import Cordis.Repairs.EpisodeUnload
import Cordis.Repairs.ReplayBindingDomains

/-! The retained guarded unload step in the episode interior. Both orders of
discharge are justified by the actual source cut's saved operation history. -/
namespace Cordis.Repairs.GuardedHistory
open Calculus Stages IncarnationReplay LegalHistory
open PaperEffectEquations (CoeffectOperations ValueOperationWitness)
open PartialCoeffectIndependenceContracts (tableSetoid)
open TypedRegistry (encodeProgram Scalar)
universe u
variable {Name Key Value Code Error : Type u} [DecidableEq Name] [DecidableEq Key]
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
variable {sourceProgram : Code → Instruction Name Key Value Code Error} {length : Nat}

private theorem probe_relied (trace : Trace sourceProgram length) (episode : ClosedEpisode trace) (time : Nat)
    {actor : Name} (needed : Relied (probeAt trace episode time) actor) :
    Relied (trace.state time) actor := by
  obtain ⟨consumer, different, demand⟩ := needed
  refine ⟨consumer, different, ?_⟩
  let live := (trace.notes time).1
  let word := (trace.notes time).2 episode.name
  let restored := replay live word (trace.state time)
  have projected : probeAt trace episode time consumer = if withdraws trace episode time consumer then none
      else mark restored episode.name .inactive consumer := rfl
  rw [projected] at demand
  by_cases hidden : withdraws trace episode time consumer = true
  · simp [hidden] at demand
  rw [if_neg hidden] at demand
  cases found : trace.state time consumer with
  | none =>
    have absent := (replay_presence live word (trace.state time) consumer).mpr found
    rw [(Transposition.mark_presence _ _ _ _).mpr absent] at demand
    exact demand
  | some row =>
    obtain ⟨retained, present, component, _, phase⟩ :=
      replay_keeps_control live word (trace.state time) consumer row found
    change restored consumer = some retained at present
    by_cases same : consumer = episode.name
    · rw [← same, mark_self _ _ _ _ present] at demand
      simp [Phase.committed] at demand
    · rw [Transposition.mark_other _ _ _ _ same, present] at demand
      simpa only [component, phase] using demand

omit [DecidableEq Key] in
private theorem mask_mark (mask : Name → Bool) (state : R) (actor : Name)
    (kept : ¬ mask actor = true) :
    mark (fun name => if mask name then none else state name) actor .inactive =
      fun name => if mask name then none else mark state actor .inactive name := by
  funext name
  by_cases selected : name = actor
  · subst name
    simp [mark, Calculus.modify, kept]
  · simp [mark, Calculus.modify, selected]

/-- The retained actor's whole saved word is defined at the actual
excision probe. The selected rollback is free of dependents and the mask
erases only empty tables. -/
theorem probe_foreign_word_defined (trace : Trace sourceProgram length) (episode : ClosedEpisode trace)
    (maximal : ∀ later : ClosedEpisode trace, ¬ EpisodeEdge episode later)
    (quiet : Progress.Quiet (trace.state length)) (meaning : PartialReplayRegistry.Coeffects sourceProgram)
    {time : Nat} (lower : episode.opened ≤ time) (upper : time ≤ episode.closed)
    {actor : Name} (different : actor ≠ episode.name) :
    ReplayBindingDomains.WordDefined meaning (probeNotes trace episode time).1
      ((probeNotes trace episode time).2 actor) (probeAt trace episode time) := by
  have bound := episode.interval.bounded
  have free := not_relied_in_closing trace episode maximal lower upper
  have defined := ReplayBindingDomains.second_word_defined trace time (by omega) meaning (Ne.symm different) free
  rw [show (probeNotes trace episode time).2 actor = (trace.notes time).2 actor from if_neg different]
  exact ReplayBindingDomains.WordDefined.of_same_tables meaning defined
    (probe_replay_tables trace episode maximal quiet lower upper)

section Typed
variable {V : Key → Type u} {ops : CoeffectOperations V} {last : Nat}
variable {program : Code → TypedRegistry.Instruction Name ops Code}
local notation "A" => Scalar ops
local notation "Source" => Trace (encodeProgram program) last

theorem replay_unload_between_probes (trace : Source) (episode : ClosedEpisode trace)
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    {time : Nat} (bound : time < last) {actor : Name} (event : trace.event time = .lifecycle .unload actor)
    (different : actor ≠ episode.name) (kept : ¬ withdraws trace episode time actor = true) :
    ∃ next, GuardedSuffix.Step (encodeProgram program) (.lifecycle .unload actor) (time + 1)
        (probeAt trace episode time) (probeNotes trace episode time) next (probeNotes trace episode (time + 1)) ∧
      @StageSimulation.Related Name Key A Code PUnit.{u + 1} (TypedCoeffectReplay.setoid observe) Eq
        next (probeAt trace episode (time + 1)) := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  let source := trace.state time
  let notes := trace.notes time
  let prior := probeAt trace episode time
  let priorNotes := probeNotes trace episode time
  let closingWord := notes.2 episode.name
  let foreignWord := notes.2 actor
  let mask := withdraws trace episode time
  let meaning := TypedReplayContracts.coeffects ops observe program recovery commutative
  have step := (trace.step time bound).1
  rw [event] at step
  obtain ⟨row, view, present, phase, free, endpoint⟩ := step
  obtain ⟨retained, found, _, _, aligned⟩ := replay_keeps_control notes.1 closingWord source actor row present
  have atProbe : prior actor = some retained := by
    change (if mask actor then none else mark (replay notes.1 closingWord source) episode.name .inactive actor) = _
    rw [if_neg kept, Transposition.mark_other _ _ _ _ different]
    exact found
  have foreign : priorNotes.2 actor = foreignWord := if_neg different
  let next := mark (replay priorNotes.1 foreignWord prior) actor .inactive
  have moved : GuardedSuffix.Unload actor prior priorNotes next := by
    refine ⟨retained, view, atProbe, ?_, fun demand => free (probe_relied trace episode time demand), ?_⟩
    · rw [foreign]
      exact aligned.trans phase
    · rw [foreign]
  have paired := EpisodeUnload.replay_pair_of_history meaning source
    (trace.slot_history meaning time (Nat.le_of_lt bound))
    (fun _ => rfl)
    (trace.self_related time (Nat.le_of_lt bound)
      (TypedRegistry.encoded_program_callbacks ops observe program recovery commutative))
    (Ne.symm different) notes.1 notes.1 closingWord foreignWord
    (trace.projects time (Nat.le_of_lt bound) episode.name) (trace.projects time (Nat.le_of_lt bound) actor)
  have afterNotes := trace.unload_notes bound event
  have afterLive := congrArg Prod.fst afterNotes
  have afterWord : (trace.notes (time + 1)).2 episode.name = closingWord := by
    rw [afterNotes]
    exact if_neg (Ne.symm different)
  have sameMask : withdraws trace episode (time + 1) = mask := by
    funext name
    unfold withdraws
    rw [afterLive, afterWord]
    rfl
  refine ⟨next, ⟨moved, ?_⟩, ?_⟩
  · change probeNotes trace episode (time + 1) = Vestigial.noteStep prior next actor (time + 1) priorNotes
    rw [unload_update_notes _ moved (probe_births trace episode time (Nat.le_of_lt bound))]
    apply Prod.ext
    · change (fun name => if withdraws trace episode (time + 1) name then none else (trace.notes (time + 1)).1 name) = _
      rw [sameMask, afterLive]
      rfl
    · have afterStacks := congrArg Prod.snd afterNotes
      change (fun name => if name = episode.name then [] else (trace.notes (time + 1)).2 name) = _
      rw [afterStacks]
      funext name
      by_cases selected : name = episode.name <;> by_cases foreignActor : name = actor <;>
        simp [priorNotes, probeNotes, selected, foreignActor]
  have priorLive (name : Name) (hidden : ¬ mask name = true) : priorNotes.1 name = notes.1 name :=
    if_neg hidden
  have left : next = fun name => if mask name then none else
      mark (mark (replay notes.1 foreignWord (replay notes.1 closingWord source)) episode.name .inactive)
        actor .inactive name := by
    change mark (replay priorNotes.1 foreignWord
      (fun name => if mask name then none else mark (replay notes.1 closingWord source) episode.name .inactive name))
      actor .inactive = _
    rw [EpisodeUnload.replay_mask mask notes.1 priorNotes.1 _ _ priorLive, EpisodeRollback.replay_mark, mask_mark _ _ _ kept]
  have right : probeAt trace episode (time + 1) = fun name => if mask name then none else
      mark (mark (replay notes.1 closingWord (replay notes.1 foreignWord source)) episode.name .inactive)
        actor .inactive name := by
    unfold probeAt rollbackOf
    rw [sameMask, afterLive, afterWord, endpoint, EpisodeRollback.replay_mark,
      Transposition.marks_commute _ actor episode.name _ _ different]
  rw [left, right]
  intro name
  dsimp only
  by_cases hidden : mask name = true
  · rw [if_pos hidden, if_pos hidden]
    trivial
  · rw [if_neg hidden, if_neg hidden]
    exact StageSimulation.mark_related (StageSimulation.mark_related paired episode.name .inactive) actor .inactive name

end Typed
end Cordis.Repairs.GuardedHistory
