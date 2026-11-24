import Cordis.Repairs.EpisodeRollback

/-! Live births and saved captures on the interior rollback probes. The
source cut supplies the stamps. Replay computes its own tokens and keeps
the stamps of the original birth and capture events. -/
namespace Cordis.Repairs.EpisodeAnnotations
open Calculus Stages Indexed Incarnation IncarnationReplay
open EpisodeDependencies EpisodeBoundary EpisodeRollback
open Vestigial (CutNotes cutNotes noteStep)
open PartialReplayRegistry (saved)
open Iterators (OptionRel)
universe u
variable {Name Key Value Code Error : Type u} [DecidableEq Name] [DecidableEq Key]
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "I" => Inverse Name Key Value
local notation "Notes" => CutNotes Name Key Value
variable {program : Code → Instruction Name Key Value Code Error} {last : Nat}
local notation "History" => Trace program (fun _ => none : R) last

/-- Withdrawn live births are absent. The closing stack was rolled back;
all other stacks keep their source stamps, including earlier captures. -/
def probeNotes (trace : History) (episode : ClosedEpisode trace) (time : Nat) : Notes :=
  (fun name => if withdraws trace episode time name then none else birthAt trace.state name time,
    fun name => if name = episode.name then [] else track trace.state trace.actor time name)

theorem probeNotes_absent (trace : History) (episode : ClosedEpisode trace) (time : Nat) (name : Name) :
    (probeNotes trace episode time).1 name = none ↔ probeAt trace episode time name = none := by
  by_cases omitted : withdraws trace episode time name = true
  · simp [probeNotes, probeAt, rollbackOf, omitted]
  · simp only [probeNotes, probeAt, rollbackOf, if_neg omitted, Transposition.mark_presence, replay_presence]
    exact birthAt_none

private theorem saved_probe (trace : History) (episode : ClosedEpisode trace)
    (maximal : ∀ later : ClosedEpisode trace, ¬ EpisodeEdge episode later)
    (quiet : Progress.Quiet (trace.state last))
    {time : Nat} (lower : episode.opened ≤ time) (upper : time ≤ episode.closed) (name : Name) :
    saved (probeAt trace episode time) name = if name = episode.name then [] else saved (trace.state time) name := by
  by_cases selected : name = episode.name
  · subst name
    rw [if_pos rfl]
    change saved (rollbackOf trace episode time (trace.state time)) episode.name = []
    unfold saved rollbackOf
    by_cases omitted : withdraws trace episode time episode.name = true
    · simp [omitted]
    · simp only [if_neg omitted, mark, modify_self]
      cases replay (fun name => birthAt trace.state name time) (track trace.state trace.actor time episode.name)
          (trace.state time) episode.name <;> rfl
  · rw [if_neg selected]
    by_cases omitted : withdraws trace episode time name = true
    · have dormant := (probe_projects trace episode maximal quiet lower upper).dormant name omitted
      have absent : probeAt trace episode time name = none := if_pos omitted
      cases present : trace.state time name with
      | none => simp [saved, absent, present]
      | some row =>
        cases phase : row.phase <;> simp_all [ControlFrame.viewAt, Phase.committed, Phase.accumulator, saved]
    · cases present : trace.state time name with
      | none =>
        have absent := (probeNotes_absent trace episode time name).mp (by simp [probeNotes, omitted, birthAt_none.mpr present])
        simp [saved, absent, present]
      | some row =>
        obtain ⟨paired, present', phases⟩ := probe_keeps_phase trace episode selected omitted present
        simp [saved, present, present', phases]

theorem probeNotes_projects (trace : History) (episode : ClosedEpisode trace)
    (maximal : ∀ later : ClosedEpisode trace, ¬ EpisodeEdge episode later)
    (quiet : Progress.Quiet (trace.state last))
    {time : Nat} (lower : episode.opened ≤ time) (upper : time ≤ episode.closed) (name : Name) :
    ((probeNotes trace episode time).2 name).map Capture.token = saved (probeAt trace episode time) name := by
  have bounded := episode.interval.bounded
  rw [saved_probe trace episode maximal quiet lower upper]
  by_cases selected : name = episode.name
  · simp [probeNotes, selected]
  · simpa only [probeNotes, if_neg selected] using (tracked_stack trace time (by omega)).projects name

private theorem withdraws_persists (trace : History) (episode : ClosedEpisode trace)
    {time : Nat} (lower : episode.opened ≤ time) (upper : time < episode.closed) {name : Name}
    (sameBirth : birthAt trace.state name (time + 1) = birthAt trace.state name time)
    (withdrawn : withdraws trace episode time name = true) : withdraws trace episode (time + 1) name = true := by
  have bound := episode.interval.bounded
  obtain ⟨capture, earlier, matched⟩ := List.any_eq_true.mp withdrawn
  have later := capture_persists trace (by omega) episode.name
    (episode.interval.installed (time + 1) (by omega) (by omega)) earlier
  apply List.any_eq_true.mpr
  refine ⟨capture, later, ?_⟩
  cases token : capture.token with
  | retire child =>
    obtain ⟨rfl, born⟩ : name = child ∧ birthAt trace.state child time = some capture.index := by
      simpa [Capture.retires, token] using matched
    simp [Capture.retires, token, sameBirth, born]
  | _ => simp [Capture.retires, token] at matched

/-- The ordinary recorder on the canonical probes advances their source
stamps. A surviving old birth was visible at the previous probe. -/
theorem probeNotes_step (trace : History) (episode : ClosedEpisode trace)
    (maximal : ∀ later : ClosedEpisode trace, ¬ EpisodeEdge episode later)
    (quiet : Progress.Quiet (trace.state last))
    {time : Nat} (lower : episode.opened ≤ time) (upper : time < episode.closed) :
    noteStep (probeAt trace episode time) (probeAt trace episode (time + 1)) (trace.actor time) (time + 1)
      (probeNotes trace episode time) = probeNotes trace episode (time + 1) := by
  have cutoff : time + 1 ≤ episode.closed := by omega
  apply Prod.ext
  · funext name
    change (probeAt trace episode (time + 1) name).map (fun _ => ((probeNotes trace episode time).1 name).getD (time + 1)) = _
    cases next : probeAt trace episode (time + 1) name with
    | none => exact ((probeNotes_absent trace episode (time + 1) name).mpr next).symm
    | some row =>
      have shown : (probeNotes trace episode (time + 1)).1 name ≠ none := by
        intro absent
        have missing := (probeNotes_absent trace episode (time + 1) name).mp absent
        rw [next] at missing
        cases missing
      have unmasked : ¬ withdraws trace episode (time + 1) name = true := by
        intro omitted
        exact shown (if_pos omitted)
      have origin : trace.state (time + 1) name ≠ none := by
        intro absent
        exact shown (by simp [probeNotes, unmasked, birthAt_none.mpr absent])
      have beforeVisible : ¬ withdraws trace episode time name = true := by
        intro omitted
        obtain ⟨birth, _, _, _, _, lives⟩ := withdrawn_birth trace episode lower (by omega) omitted
        have present := lives.present time lives.ordered (Nat.le_refl _)
        have sameBirth := birthAt_same_presence_at trace.state time name ⟨fun missing => (origin missing).elim,
          fun missing => (present missing).elim⟩
        exact unmasked (withdraws_persists trace episode lower upper sameBirth omitted)
      cases found : trace.state (time + 1) name with
      | none => exact False.elim (origin found)
      | some prior => simp [probeNotes, beforeVisible, unmasked, birthAt, found]
  · funext name
    let actor := trace.actor time
    change advance (probeAt trace episode time) (probeAt trace episode (time + 1)) actor (time + 1)
      (probeNotes trace episode time).2 name = (probeNotes trace episode (time + 1)).2 name
    by_cases selected : name = episode.name
    · subst name
      have empty := saved_probe trace episode maximal quiet (by omega : episode.opened ≤ time + 1) cutoff episode.name
      rw [if_pos rfl] at empty
      by_cases acts : episode.name = actor
      · rw [advance, if_pos acts, empty]
        simp [probeNotes]
      · simp [advance, acts, probeNotes]
    · have before := saved_probe trace episode maximal quiet lower (by omega : time ≤ episode.closed) name
      have after := saved_probe trace episode maximal quiet (by omega : episode.opened ≤ time + 1) cutoff name
      simp only [if_neg selected] at before after
      simp only [probeNotes, if_neg selected]
      change _ = advance (trace.state time) (trace.state (time + 1)) actor (time + 1)
        (track trace.state trace.actor time) name
      simp only [advance, before, after, if_neg selected]

/-- The annotated replay starts with the actual prefix annotations before
the episode's omitted Begin. Begin itself records neither birth nor capture. -/
theorem probeNotes_at_opening (trace : History) (episode : ClosedEpisode trace) :
    probeNotes trace episode episode.opened = cutNotes trace.state trace.actor (episode.opened - 1) := by
  let previous := episode.opened - 1
  have positive := episode.interval.positive
  have ordered := episode.interval.ordered
  have bounded := episode.interval.bounded
  have next : previous + 1 = episode.opened := by omega
  obtain ⟨fiber, view, present, inactive, _, _, ended⟩ := begin_boundary trace episode.interval
  have stable : saved (trace.state episode.opened) = saved (trace.state previous) := by
    change saved (trace.state episode.opened) = saved (trace.state (episode.opened - 1))
    rw [ended]
    funext name
    rw [PartialReplayRegistry.saved_mark _ _ _ present]
    by_cases target : name = episode.name
    · subst name
      simp [saved, present, inactive, Phase.accumulator]
    · simp [target]
  have words : track trace.state trace.actor episode.opened = track trace.state trace.actor previous := by
    calc
      track trace.state trace.actor episode.opened = track trace.state trace.actor (previous + 1) :=
        congrArg (track trace.state trace.actor) next.symm
      _ = track trace.state trace.actor previous := advance_control _ _ _
        (tracked_stack trace previous (by omega)).projects (by rwa [next])
  have empty := empty_on_entry trace episode
  apply Prod.ext
  · funext name
    have visible : withdraws trace episode episode.opened name = false := by simp [withdraws, empty]
    have presence : trace.state (previous + 1) name = none ↔ trace.state previous name = none := by
      rw [next, ended, Transposition.mark_presence]
    have same := birthAt_same_presence_at trace.state previous name presence
    rw [next] at same
    simpa only [probeNotes, cutNotes, visible, Bool.false_eq_true, if_false] using same
  · funext name
    by_cases target : name = episode.name
    · subst name
      change (if episode.name = episode.name then [] else _) = _
      rw [if_pos rfl]
      exact empty.symm.trans (congrFun words episode.name)
    · simpa only [probeNotes, cutNotes, if_neg target] using congrFun words name

/-- A skipped source event keeps the expected prefix annotations as well
as the canonical registry. Its source stamp is never assigned in replay. -/
theorem probeNotes_stutter (trace : History) (episode : ClosedEpisode trace)
    (maximal : ∀ later : ClosedEpisode trace, ¬ EpisodeEdge episode later)
    (quiet : Progress.Quiet (trace.state last))
    {time : Nat} (lower : episode.opened ≤ time) (upper : time < episode.closed)
    (same : probeAt trace episode (time + 1) = probeAt trace episode time) :
    probeNotes trace episode (time + 1) = probeNotes trace episode time := by
  have moved := probeNotes_step trace episode maximal quiet lower upper
  rw [same] at moved
  rw [← moved]
  apply Prod.ext
  · funext name
    change (probeAt trace episode time name).map (fun _ => ((probeNotes trace episode time).1 name).getD (time + 1)) = _
    cases birth : (probeNotes trace episode time).1 name with
    | none => rw [(probeNotes_absent trace episode time name).mp birth]; rfl
    | some born =>
      cases present : probeAt trace episode time name with
      | none =>
        have absent := (probeNotes_absent trace episode time name).mpr present
        rw [birth] at absent
        cases absent
      | some row => rfl
  · exact advance_control _ _ _ (probeNotes_projects trace episode maximal quiet lower (by omega)) rfl

/-- The closing probe already has the post-unload annotations. Remove the
withdrawn births and use the original post-unload saved words unchanged. -/
theorem probeNotes_at_closure (trace : History) (episode : ClosedEpisode trace) :
    probeNotes trace episode episode.closed =
      (fun name => if withdraws trace episode episode.closed name then none else birthAt trace.state name (episode.closed + 1),
        track trace.state trace.actor (episode.closed + 1)) := by
  let time := episode.closed
  have bounded := episode.interval.bounded
  obtain ⟨row, word, view, present, phase, _, ended⟩ := unload_boundary trace episode.interval
  have endState : trace.state (time + 1) = mark (discharge Stages.undo word (trace.state time)) episode.name .inactive := ended
  have sourceTrack := (tracked_stack trace time (by omega)).projects
  have nextTrack := (tracked_stack trace (time + 1) (by omega)).projects
  have cleared (name : Name) : saved (trace.state (time + 1)) name =
      if name = episode.name then [] else saved (trace.state time) name := by
    obtain ⟨surviving, found, _⟩ := Ordering.discharge_existing_phases _ word episode.name row present
    rw [endState, PartialReplayRegistry.saved_mark _ _ _ found, PartialReplayRegistry.saved_discharge]
    rfl
  have births := birthAt_same_presence trace.state time fun name => by
    rw [endState, Transposition.mark_presence]
    constructor
    · intro missing
      cases found : trace.state time name with
      | none => rfl
      | some fiber =>
        obtain ⟨retained, held, _⟩ := Ordering.discharge_existing_phases _ word name fiber found
        rw [held] at missing
        cases missing
    · exact EntangledApplications.discharge_preserves_absence word _ name
  apply Prod.ext
  · funext name
    have same := congrFun births name
    change (if withdraws trace episode time name then none else birthAt trace.state name time) =
      if withdraws trace episode time name then none else birthAt trace.state name (time + 1)
    rw [same]
  · funext name
    change (if name = episode.name then [] else track trace.state trace.actor time name) =
      track trace.state trace.actor (time + 1) name
    by_cases selected : name = episode.name
    · rw [if_pos selected]
      exact (List.map_eq_nil_iff.mp ((nextTrack name).trans (by rw [cleared, if_pos selected]))).symm
    · rw [if_neg selected]
      change track trace.state trace.actor time name = advance (trace.state time) (trace.state (time + 1))
        (trace.actor time) (time + 1) (track trace.state trace.actor time) name
      rw [advance, cleared, if_neg selected]
      by_cases acts : name = trace.actor time
      · rw [if_pos acts]
        cases raw : saved (trace.state time) name with
        | nil => exact List.map_eq_nil_iff.mp ((sourceTrack name).trans raw)
        | cons inverse rest => simp
      · rw [if_neg acts]

section RelatedNotes
variable [Setoid Value]

structure NotesRelated (left right : Notes) : Prop where
  births : left.1 = right.1
  stamps : ∀ name, (left.2 name).map Capture.index = (right.2 name).map Capture.index
  words : ∀ name, StageSimulation.StackRelated ((left.2 name).map Capture.token) ((right.2 name).map Capture.token)

theorem NotesRelated.symm {left right : Notes} (related : NotesRelated left right) : NotesRelated right left :=
  ⟨related.births.symm, fun name => (related.stamps name).symm, fun name => (related.words name).symm⟩

theorem NotesRelated.trans {left middle right : Notes} (first : NotesRelated left middle)
    (second : NotesRelated middle right) : NotesRelated left right :=
  ⟨first.births.trans second.births, fun name => (first.stamps name).trans (second.stamps name),
    fun name => (first.words name).trans (second.words name)⟩

omit [DecidableEq Name] [DecidableEq Key] in
private theorem accumulators_related {left right : Phase Name Key Code I}
    (related : StageSimulation.PhaseRelated Eq left right) :
    StageSimulation.StackRelated left.accumulator right.accumulator := by
  cases related with
  | inactive => exact .nil
  | reloading _ _ stacks | active _ stacks | unloading _ stacks => exact stacks

omit [DecidableEq Name] [DecidableEq Key] in
private theorem stack_length {left right : List I} (related : StageSimulation.StackRelated left right) :
    left.length = right.length := by
  induction related with
  | nil => rfl
  | cons _ _ same => simpa only [List.length_cons] using congrArg Nat.succ same

omit [DecidableEq Name] [DecidableEq Key] in
theorem saved_related {left right : R} (related : StageSimulation.Related Eq left right) (name : Name) :
    StageSimulation.StackRelated (saved left name) (saved right name) := by
  have rows := related name
  cases first : left name <;> cases second : right name <;> simp only [first, second, OptionRel] at rows
  · simpa only [saved, first, second] using (StageSimulation.StackRelated.nil (Name := Name) (Key := Key) (Value := Value))
  · simpa only [saved, first, second, Option.map_some, Option.getD_some] using accumulators_related rows.phase

omit [DecidableEq Name] [DecidableEq Key] in
theorem notesRelated_self {state : R} (related : StageSimulation.Related Eq state state) (notes : Notes)
    (projects : ∀ name, (notes.2 name).map Capture.token = saved state name) : NotesRelated notes notes := by
  refine ⟨rfl, fun _ => rfl, ?_⟩
  intro name
  rw [projects name]
  exact saved_related related name

/-- Recording compares stamps exactly and the actual emitted tokens
semantically. Both registries detect the same stack growth and birth. -/
theorem noteStep_related {left right nextLeft nextRight : R}
    (before : StageSimulation.Related Eq left right) (after : StageSimulation.Related Eq nextLeft nextRight)
    (actor : Name) (stamp : Nat) {first second : Notes} (related : NotesRelated first second) :
    NotesRelated (noteStep left nextLeft actor stamp first) (noteStep right nextRight actor stamp second) := by
  let firstNext := noteStep left nextLeft actor stamp first
  let secondNext := noteStep right nextRight actor stamp second
  have births : firstNext.1 = secondNext.1 := by
    funext name
    have absent := GuardObservations.none_iff after.observed name
    cases l : nextLeft name <;> cases r : nextRight name <;>
      simp_all [firstNext, secondNext, noteStep, related.births]
  have stacks (name : Name) : (firstNext.2 name).map Capture.index = (secondNext.2 name).map Capture.index ∧
      StageSimulation.StackRelated ((firstNext.2 name).map Capture.token) ((secondNext.2 name).map Capture.token) := by
    by_cases acts : name = actor
    · have prior := stack_length (saved_related before name)
      have next := saved_related after name
      unfold firstNext secondNext
      simp only [noteStep, advance, if_pos acts]
      cases l : saved nextLeft name <;> cases r : saved nextRight name <;> rw [l, r] at next
      · exact ⟨rfl, .nil⟩
      · cases next
      · cases next
      · cases next with
        | cons head tail =>
          simp only [List.length_cons, prior, stack_length tail]
          split
          · exact ⟨by simp [related.stamps name], .cons head (related.words name)⟩
          · exact ⟨related.stamps name, related.words name⟩
    · simpa only [firstNext, secondNext, noteStep, advance, if_neg acts] using
        And.intro (related.stamps name) (related.words name)
  exact ⟨births, fun name => (stacks name).1, fun name => (stacks name).2⟩

/-- Related annotations preserve each live-birth test during unload and
apply related partial-map representatives to the surviving bindings. -/
theorem replay_related_of_notes {left right : R} (states : StageSimulation.Related Eq left right)
    {first second : Notes} (notes : NotesRelated first second) (actor : Name) :
    StageSimulation.Related Eq (replay first.1 (first.2 actor) left) (replay second.1 (second.2 actor) right) := by
  have matching (live : Name → Option Nat) (firstWord secondWord : List (Capture Name Key Value))
      (stamps : firstWord.map Capture.index = secondWord.map Capture.index)
      (tokens : StageSimulation.StackRelated (firstWord.map Capture.token) (secondWord.map Capture.token))
      {left right : R} (states : StageSimulation.Related Eq left right) :
      StageSimulation.Related Eq (replay live firstWord left) (replay live secondWord right) := by
    induction firstWord generalizing secondWord left right with
    | nil => cases secondWord <;> cases stamps; exact states
    | cons first rest ih =>
      cases secondWord with
      | nil => cases stamps
      | cons second tail =>
        obtain ⟨headIndex, tailIndices⟩ := List.cons.inj stamps
        cases tokens with
        | cons heads tails =>
          have applyRelated : StageSimulation.Related Eq (first.apply live left) (second.apply live right) := by
            rcases first with ⟨first, stamp⟩
            rcases second with ⟨second, otherStamp⟩
            change stamp = otherStamp at headIndex
            subst otherStamp
            change StageSimulation.InverseRelated first second at heads
            cases heads with
            | unit => exact states
            | restrict owner key => exact StageSimulation.undo_related states (.restrict owner key)
            | operate owner key functions => exact StageSimulation.undo_related states (.operate owner key functions)
            | retire child =>
              by_cases liveChild : live child = some stamp
              · simpa only [Capture.apply, if_pos liveChild] using StageSimulation.retire_related states child
              · simpa only [Capture.apply, if_neg liveChild] using states
          exact ih tail tailIndices tails applyRelated
  rw [notes.births]
  exact matching second.1 (first.2 actor) (second.2 actor) (notes.stamps actor) (notes.words actor) states

end RelatedNotes

end Cordis.Repairs.EpisodeAnnotations
