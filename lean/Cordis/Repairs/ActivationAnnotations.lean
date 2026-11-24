import Cordis.Repairs.GuardedSuffix
import Cordis.TranspositionActivation

/-! Annotation correspondence for two exchanged activations. The source
event stamps remain attached to their events in both orders. -/
namespace Cordis.Repairs.EpisodeAnnotations
open Calculus Stages
open IncarnationReplay (Capture advance_capture advance_control)
open PartialReplayRegistry (saved saved_mark saved_after_landing)
open Vestigial (CutNotes noteStep noteStep_projects)
universe u
variable {Name Key Value Code Error : Type u} [DecidableEq Name] [DecidableEq Key]
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "Notes" => CutNotes Name Key Value
variable {program : Code → Instruction Name Key Value Code Error}

private theorem activation_retains {before after : R} {rule : Labeled.Rule} {actor name : Name}
    (step : Labeled.Step program rule actor before after) (activation : Transposition.Activation rule)
    (present : before name ≠ none) : after name ≠ none := by
  intro gone
  cases step with
  | begin => exact present ((Transposition.mark_presence _ _ _ _).mp gone)
  | iter _ _ _ _ _ _ _ _ _ _ _ _ land | finish _ _ _ _ _ _ _ _ _ _ _ land =>
    cases found : before name with
    | none => exact present found
    | some row =>
      obtain ⟨_, retained, _, _⟩ := Ordering.land_existing_control program land name row found
      have missing := (Transposition.mark_presence _ _ _ _).mp gone
      rw [retained] at missing
      cases missing
  | _ => simp [Transposition.Activation] at activation

private theorem activation_birth_parent {before after : R} {rule : Labeled.Rule} {actor name : Name}
    (step : Labeled.Step program rule actor before after) (activation : Transposition.Activation rule)
    (absent : before name = none) {row : Fiber Name Key Value Code (Inverse Name Key Value) Error}
    (found : after name = some row) : row.parent = some actor := by
  have different : actor ≠ name := by
    intro equal
    subst name
    obtain ⟨_, _, present, _, _⟩ := Transposition.activation_source program step activation
    rw [absent] at present
    cases present
  obtain ⟨_, component, phase, _, _, endpoint⟩ :=
    (Transposition.activation_creates_iff program step activation name different).mpr ⟨absent, by simp [found]⟩
  rw [endpoint, Transposition.mark_other _ _ _ phase (Ne.symm different), put_self] at found
  exact (congrArg Fiber.parent (Option.some.inj found)).symm

private theorem pair_births {before middle after : R} {firstRule secondRule : Labeled.Rule} {first second : Name}
    (one : Labeled.Step program firstRule first before middle) (firstActive : Transposition.Activation firstRule)
    (two : Labeled.Step program secondRule second middle after) (secondActive : Transposition.Activation secondRule)
    (stamp : Name → Nat) (notes : Notes) (valid : GuardedSuffix.BirthsAgree before notes) (name : Name) :
    (noteStep middle after second (stamp second) (noteStep before middle first (stamp first) notes)).1 name =
      (after name).map (fun row => (notes.1 name).getD ((row.parent.map stamp).getD 0)) := by
  cases atEnd : after name with
  | none => simp [noteStep, atEnd]
  | some row =>
    cases prior : notes.1 name with
    | some original =>
      have present : before name ≠ none := by
        intro absent
        have noStamp := (valid name).mpr absent
        rw [prior] at noStamp
        cases noStamp
      have retained := activation_retains one firstActive present
      cases atMid : middle name with
      | none => exact False.elim (retained atMid)
      | some => simp [noteStep, atMid, atEnd, prior]
    | none =>
      have absent := (valid name).mp prior
      cases atMid : middle name with
      | none =>
        have parent := activation_birth_parent two secondActive atMid atEnd
        simp [noteStep, atMid, atEnd, prior, parent]
      | some midRow =>
        have parent := activation_birth_parent one firstActive absent atMid
        have stable := (Frame.step_stable program two.toCalculus name midRow row atMid atEnd).2.1
        simp [noteStep, atMid, atEnd, prior, stable.symm.trans parent]

private theorem activation_stamps {before after : R} {rule : Labeled.Rule} {actor : Name}
    (step : Labeled.Step program rule actor before after) (activation : Transposition.Activation rule)
    (stamp : Nat) (notes : Notes) (projects : GuardedSuffix.SavedWordsAgree before notes) (name : Name) :
    ((noteStep before after actor stamp notes).2 name).map Capture.index =
      (if rule = .begin ∨ name ≠ actor then [] else [stamp]) ++ (notes.2 name).map Capture.index := by
  cases step with
  | begin _ _ row view found inactive _ _ =>
    have unchanged : saved (mark before actor (.reloading row.component.entry [] view)) = saved before := by
      funext other
      rw [saved_mark _ _ _ found]
      by_cases same : other = actor
      · subst other
        simp [saved, found, inactive, Phase.accumulator]
      · simp [same]
    rw [noteStep, advance_control _ _ _ projects unchanged]
    simp
  | iter _ _ _ row _ word view inverse next found phase _ landing =>
    have pushed := saved_after_landing program landing row found (.reloading next (inverse :: word) view)
      (by simp only [phase, Phase.accumulator])
    rw [noteStep, advance_capture _ _ _ _ pushed]
    by_cases acts : name = actor <;> simp [acts]
  | finish _ _ _ row _ word view inverse found phase _ landing =>
    have pushed := saved_after_landing program landing row found (.active (inverse :: word) view)
      (by simp only [phase, Phase.accumulator])
    rw [noteStep, advance_capture _ _ _ _ pushed]
    by_cases acts : name = actor <;> simp [acts]
  | _ => simp [Transposition.Activation] at activation

/-- Both orders attach a new birth to its parent's actual event and a new
capture to its actor's actual landing. Saved words compare according to the
landings' endpoint relation, with their original stamps unchanged. -/
theorem exchanged_activation_notes [Setoid Value]
    {before middle after swappedMiddle swappedAfter : R} {firstRule secondRule : Labeled.Rule} {first second : Name}
    (one : Labeled.Step program firstRule first before middle) (firstActive : Transposition.Activation firstRule)
    (two : Labeled.Step program secondRule second middle after) (secondActive : Transposition.Activation secondRule)
    (swappedOne : Labeled.Step program secondRule second before swappedMiddle)
    (swappedTwo : Labeled.Step program firstRule first swappedMiddle swappedAfter)
    (different : first ≠ second) (endpoint : StageSimulation.Related Eq after swappedAfter)
    (notes : Notes) (valid : GuardedSuffix.BirthsAgree before notes)
    (projects : GuardedSuffix.SavedWordsAgree before notes) (firstStamp secondStamp : Nat) :
    NotesRelated
      (noteStep middle after second secondStamp (noteStep before middle first firstStamp notes))
      (noteStep swappedMiddle swappedAfter first firstStamp (noteStep before swappedMiddle second secondStamp notes)) := by
  let stamp (actor : Name) := if actor = first then firstStamp else secondStamp
  have firstStampEq : stamp first = firstStamp := by simp [stamp]
  have secondStampEq : stamp second = secondStamp := by simp [stamp, Ne.symm different]
  have leftProjects := noteStep_projects one firstStamp notes projects
  have rightProjects := noteStep_projects swappedOne secondStamp notes projects
  constructor
  · funext name
    rw [← firstStampEq, ← secondStampEq, pair_births one firstActive two secondActive stamp notes valid,
      pair_births swappedOne secondActive swappedTwo firstActive stamp notes valid]
    have related := endpoint name
    cases left : after name <;> cases right : swappedAfter name <;> simp only [left, right, Iterators.OptionRel] at related
    · rfl
    · simp only [Option.map_some, related.parent]
  · intro name
    rw [activation_stamps two secondActive secondStamp _ leftProjects,
      activation_stamps one firstActive firstStamp _ projects,
      activation_stamps swappedTwo firstActive firstStamp _ rightProjects,
      activation_stamps swappedOne secondActive secondStamp _ projects]
    by_cases acts : name = first
    · subst name
      simp [different]
    · simp [acts]
  · intro name
    rw [noteStep_projects two secondStamp _ leftProjects name, noteStep_projects swappedTwo firstStamp _ rightProjects name]
    exact saved_related endpoint name

end Cordis.Repairs.EpisodeAnnotations
