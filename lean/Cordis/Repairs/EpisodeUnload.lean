import Cordis.Repairs.EpisodeRollback
import Cordis.TypedReplayContracts

/-! A retained unload compares the two orders of its own saved word and
the selected episode's rollback word. The original cut supplies the
partial domains and actual capture provenance. -/
namespace Cordis.Repairs.EpisodeUnload
open Calculus Stages Indexed Incarnation IncarnationReplay
open EpisodeDependencies EpisodeBoundary EpisodeReplayGuards EpisodeRollback
open PartialReplayRegistry (saved)
open Iterators (OptionRel)
universe u
variable {Name Key Value Code Error : Type u} [DecidableEq Name] [DecidableEq Key]
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
local notation "C" => Capture Name Key Value

theorem replay_mask (mask : Name → Bool) (live projectedLive : Name → Option Nat) (word : List C) (state : R)
    (agree : ∀ name, ¬ mask name = true → projectedLive name = live name) :
    replay projectedLive word (fun name => if mask name then none else state name) =
      fun name => if mask name then none else replay live word state name := by
  have modifyMask (r : R) (actor : Name) (edit : F → F) :
      Calculus.modify (fun name => if mask name then none else r name) actor edit =
        fun name => if mask name then none else Calculus.modify r actor edit name := by
    funext name
    by_cases selected : name = actor
    · subst name
      by_cases hidden : mask actor = true <;> simp [Calculus.modify, hidden]
    · simp [Calculus.modify, selected]
  induction word generalizing state with
  | nil => rfl
  | cons capture rest ih =>
    have step : capture.apply projectedLive (fun name => if mask name then none else state name) =
        fun name => if mask name then none else capture.apply live state name := by
      obtain ⟨token, index⟩ := capture
      cases token with
      | unit => rfl
      | restrict owner key => exact modifyMask state owner _
      | operate owner key fn => exact modifyMask state owner _
      | retire child =>
        by_cases hidden : mask child = true
        · have unchanged : (fun name => if mask name then none else Calculus.retire state child name) =
              (fun name => if mask name then none else state name) := by
            funext name
            by_cases same : name = child
            · subst name; simp [hidden]
            · simp [Calculus.retire, Calculus.modify, same]
          simp only [Capture.apply]
          split <;> split
          · exact modifyMask state child _
          · exact (modifyMask state child _).trans unchanged
          · exact unchanged.symm
          · rfl
        · simp only [Capture.apply, agree child hidden]
          split
          · exact modifyMask state child _
          · rfl
    rw [replay, step, ih, replay]

/-- The order of two discharges affects only the observed binding values.
Presence, phase, component and parent are untouched, and both orders set
the union of the two words' matching retirement flags. -/
private theorem replay_pair_controls (firstLive secondLive : Name → Option Nat) (first second : List C) (state : R) :
    Transposition.SameControls (replay secondLive second (replay firstLive first state))
      (replay firstLive first (replay secondLive second state)) := by
  intro name
  cases found : state name with
  | none =>
    have left := (replay_presence secondLive second _ name).mpr ((replay_presence firstLive first state name).mpr found)
    have right := (replay_presence firstLive first _ name).mpr ((replay_presence secondLive second state name).mpr found)
    simp [left, right, OptionRel]
  | some row =>
    obtain ⟨x, atX, compX, parentX, phaseX⟩ := replay_keeps_control firstLive first state name row found
    obtain ⟨y, atY, compY, parentY, phaseY⟩ := replay_keeps_control secondLive second state name row found
    obtain ⟨p, atP, compP, parentP, phaseP⟩ := replay_keeps_control secondLive second _ name x atX
    obtain ⟨q, atQ, compQ, parentQ, phaseQ⟩ := replay_keeps_control firstLive first _ name y atY
    have flagX := replay_retired firstLive first state name
    have flagY := replay_retired secondLive second state name
    have flagP := replay_retired secondLive second (replay firstLive first state) name
    have flagQ := replay_retired firstLive first (replay secondLive second state) name
    rw [atX, found] at flagX
    rw [atY, found] at flagY
    rw [atP, atX] at flagP
    rw [atQ, atY] at flagQ
    simp only [Option.map_some, Option.some.injEq] at flagX flagY flagP flagQ
    rw [atP, atQ]
    exact ⟨(compP.trans compX).trans (compQ.trans compY).symm,
      (parentP.trans parentX).trans (parentQ.trans parentY).symm,
      by rw [flagP, flagQ, flagX, flagY, Bool.or_right_comm],
      (phaseP.trans phaseX).trans (phaseQ.trans phaseY).symm⟩

section Typed
open PaperEffectEquations (CoeffectOperations ValueOperationWitness)
open PartialCoeffectIndependenceContracts (tableSetoid)
open TypedRegistry (encodeProgram RawRegistry Scalar)
open StageRecovery (tableAt)
variable {V : Key → Type u} {ops : CoeffectOperations V}
variable {program : Code → TypedRegistry.Instruction Name ops Code} {last : Nat}
local notation "A" => Scalar ops
local notation "Raw" => RawRegistry Name ops Code
local notation "History" => Trace (encodeProgram program) (fun _ => none : Raw) last

private theorem discharge_slot {program : Code → Instruction Name Key Value Code Error}
    (meaning : PartialReplayRegistry.Coeffects program) (state : R)
    (firstLive secondLive : Name → Option Nat) (first second : List C) (name : Name) (key : Key) (value : Option Value)
    (success : PartialReplayHistory.run
      ((first.map Capture.token ++ second.map Capture.token).map (PartialReplaySlots.project meaning.denote name key))
      (tableAt state name key) = some value) :
    tableAt (replay secondLive second (replay firstLive first state)) name key = value := by
  have native : tableAt (discharge Stages.undo (first.map Capture.token ++ second.map Capture.token) state) name key = value :=
    PartialReplaySlots.project_word meaning.denote meaning.agrees name key _ state value success
  rw [PartialReplayRegistry.discharge_append] at native
  have matched := replay_tables secondLive second (replay_tables firstLive first (left := state) (right := state)
    (fun _ _ => rfl)) name key
  exact matched.symm.trans native

/-- Replay both words from the same cut, using its actual per-slot histories
and the observational contracts of its saved operations. -/
theorem replay_pair_of_history {program : Code → Instruction Name Key Value Code Error} [Setoid Value]
    (meaning : PartialReplayRegistry.Coeffects program) (source : R)
    (history : ∀ name key, PartialReplayRegistry.SlotHistory meaning source name key)
    (observe : ∀ key, (meaning.observe key).r = (fun a b : Value => a ≈ b))
    (self : StageSimulation.Related Eq source source)
    {firstActor secondActor : Name} (different : firstActor ≠ secondActor)
    (firstLive secondLive : Name → Option Nat) (first second : List C)
    (firstProjects : first.map Capture.token = saved source firstActor)
    (secondProjects : second.map Capture.token = saved source secondActor) :
    StageSimulation.Related Eq (replay secondLive second (replay firstLive first source))
      (replay firstLive first (replay secondLive second source)) := by
  have tables : StageRecovery.TablesRelated
      (replay secondLive second (replay firstLive first source))
      (replay firstLive first (replay secondLive second source)) := by
    intro name key
    have compared := PartialReplayRegistry.saved_words_commute_of_history meaning firstActor secondActor name different key (history name key)
    dsimp only at compared
    rw [← firstProjects, ← secondProjects] at compared
    obtain ⟨left, right, leftReady, rightReady, related⟩ := compared
    rw [discharge_slot meaning source firstLive secondLive first second name key left leftReady,
      discharge_slot meaning source secondLive firstLive second first name key right rightReady]
    simpa only [← observe key] using related
  exact Transposition.related_of_controls_tables (replay_pair_controls firstLive secondLive first second source)
    tables (replay_self_related firstLive first (replay_self_related secondLive second self))

private theorem replay_pair_on_trace (trace : History) (time : Nat) (bounded : time ≤ last)
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    {firstActor secondActor : Name} (different : firstActor ≠ secondActor)
    (firstLive secondLive : Name → Option Nat) (first second : List (Capture Name Key A))
    (firstProjects : first.map Capture.token = saved (trace.state time) firstActor)
    (secondProjects : second.map Capture.token = saved (trace.state time) secondActor) :
    @StageSimulation.Related Name Key A Code PUnit.{u + 1} (TypedCoeffectReplay.setoid observe) Eq
      (replay secondLive second (replay firstLive first (trace.state time)))
      (replay firstLive first (replay secondLive second (trace.state time))) := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  let source := trace.state time
  let meaning := TypedReplayContracts.coeffects ops observe program recovery commutative
  have reached := trace.prefixRun time bounded
  exact replay_pair_of_history meaning source
    (PartialReplayRegistry.reachable_slot_history meaning reached)
    (fun _ => rfl)
    (Transposition.reachable_self_related (encodeProgram program)
      (TypedRegistry.encoded_program_callbacks ops observe program recovery commutative) reached)
    different firstLive secondLive first second firstProjects secondProjects

/-- A discharge at a foreign cut compares both orders of the two actual
saved words. Its chosen retirement tests may be incarnation-sensitive;
the same tests are used for the original cut and its probe. -/
theorem replay_discharge_on_probe (trace : History) (episode : ClosedEpisode trace)
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    {time : Nat} (bounded : time ≤ last)
    (different : trace.actor time ≠ episode.name)
    (kept : ¬ withdraws trace episode time (trace.actor time) = true)
    (live : Name → Option Nat) (word : List (Capture Name Key A))
    (projects : word.map Capture.token = saved (trace.state time) (trace.actor time))
    (ended : trace.state (time + 1) = mark (replay live word (trace.state time)) (trace.actor time) .inactive) :
    @StageSimulation.Related Name Key A Code PUnit.{u + 1} (TypedCoeffectReplay.setoid observe) Eq
      (mark (replay live word (probeAt trace episode time)) (trace.actor time) .inactive)
      (probeAt trace episode (time + 1)) := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  let before := trace.state time
  let closingLive := fun name => birthAt trace.state name time
  let closingWord := track trace.state trace.actor time episode.name
  let mask := withdraws trace episode time
  have closingProjects := (tracked_stack trace time bounded).projects episode.name
  have paired := replay_pair_on_trace trace time bounded observe recovery commutative (Ne.symm different)
    closingLive live closingWord word closingProjects projects
  have marked := StageSimulation.mark_related paired episode.name .inactive
  have moved : replay live word (probeAt trace episode time) = fun name =>
      if mask name then none else mark (replay live word (replay closingLive closingWord before)) episode.name .inactive name := by
    change replay live word (fun name => if mask name then none else
      mark (replay closingLive closingWord before) episode.name .inactive name) = _
    rw [replay_mask _ _ _ _ _ (fun _ _ => rfl), replay_mark]
  have related : StageSimulation.Related Eq (replay live word (probeAt trace episode time))
      (rollbackOf trace episode time (replay live word before)) := by
    rw [moved]
    intro name
    by_cases omitted : mask name = true
    · simp [rollbackOf, mask, omitted, OptionRel]
    · simpa only [rollbackOf, mask, if_neg omitted] using marked name
  rw [probe_after_foreign_edit trace episode different kept (fun name => replay_presence live word before name) ended]
  exact StageSimulation.mark_related related (trace.actor time) .inactive

/-- A retained native Unload remains legal and reaches a registry
structurally related to the next rollback probe. -/
theorem replay_unload_between_probes (trace : History) (episode : ClosedEpisode trace)
    (maximal : ∀ later : ClosedEpisode trace, ¬ EpisodeEdge episode later)
    (quiet : Progress.Quiet (trace.state last))
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    {time : Nat} (lower : episode.opened ≤ time) (upper : time ≤ episode.closed)
    (different : trace.actor time ≠ episode.name)
    (kept : ¬ withdraws trace episode time (trace.actor time) = true)
    (rule : trace.rule time = .unload) :
    ∃ next, Labeled.Step (encodeProgram program) .unload (trace.actor time) (probeAt trace episode time) next ∧
      @StageSimulation.Related Name Key A Code PUnit.{u + 1} (TypedCoeffectReplay.setoid observe) Eq
        next (probeAt trace episode (time + 1)) := by
  have bounded := episode.interval.bounded
  have step := trace.step time (by omega)
  rw [rule] at step
  generalize ended : trace.state (time + 1) = after at step
  cases step with
  | unload _ _ row word view present phase unrelied =>
    obtain ⟨paired, found, aligned⟩ := probe_keeps_phase trace episode different kept present
    have projected := probe_projects trace episode maximal quiet lower upper
    have moved := Labeled.Step.unload (program := encodeProgram program) _ _ paired word view found
      (aligned.trans phase) (fun relied => unrelied (projected.relied_backward relied))
    let rawWord := word.map fun token => (⟨token, 0⟩ : Capture Name Key A)
    have projects : rawWord.map Capture.token = saved (trace.state time) (trace.actor time) := by
      simp [rawWord, List.map_map, Function.comp_def, saved, present, phase, Phase.accumulator]
    have ended' : trace.state (time + 1) = mark (replay (fun _ => some 0) rawWord (trace.state time)) (trace.actor time) .inactive := by
      rw [replay_native_discharge]
      exact ended
    have related := replay_discharge_on_probe trace episode observe recovery commutative (by omega) different kept
      (fun _ => some 0) rawWord projects ended'
    rw [replay_native_discharge] at related
    exact ⟨_, moved, related⟩

end Typed

end Cordis.Repairs.EpisodeUnload
