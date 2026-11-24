import Cordis.PaperRemainingClaims
import Cordis.EntangledApplications
import Cordis.PartialReplayRegistry

/-! Lemmas 59 and 67 of arXiv:2608.25512v1 concern rule applications in §4.3.
The ordinary rules here use §4.2's lifecycle semantics. -/

namespace Cordis.Results

open Calculus Stages PaperLifecycleClaims
universe u
variable {Name Key Value Code Error : Type u}
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
local notation "Program" => Code → Instruction Name Key Value Code Error

private theorem committedAt_eq_none_iff (r : R) (name : Name) :
    committedAt r name = none ↔ ControlFrame.viewAt r name = none := by
  cases present : r name with
  | none => simp [committedAt, ControlFrame.viewAt, present]
  | some fiber =>
    cases view : fiber.phase.committed <;>
      simp [committedAt, ControlFrame.viewAt, present, view]

private theorem committedAt_stable {r s : R} (metadata : Frame.Stable r s)
    (views : Ordering.ViewStable r s) (name : Name)
    (before : committedAt r name ≠ none) (after : committedAt s name ≠ none) :
    committedAt r name = committedAt s name := by
  cases source : r name with
  | none => simp [committedAt, source] at before
  | some old =>
    cases target : s name with
    | none => simp [committedAt, target] at after
    | some new =>
      cases sourceView : old.phase.committed with
      | none => simp [committedAt, source, sourceView] at before
      | some oldView =>
        cases targetView : new.phase.committed with
        | none => simp [committedAt, target, targetView] at after
        | some newView =>
          have sameComponent := (metadata name old new source target).1
          have sameView := views name old new oldView newView source target sourceView targetView
          simp [committedAt, source, target, sourceView, targetView, sameComponent, sameView]

variable [DecidableEq Name] [DecidableEq Key]

/-- Lemma 59, pp. 40–41. The selected state application, committed view,
installation boundaries and retirement origin are verified on every step
of an ordinary indexed trace. An inverse that retires an instantiated
child executes the O-Retire primitive inside the parent's L-Unload. -/
theorem lemma59 [Setoid Value] {program : Program} {last : Nat}
    {sem : PaperStateObservation.Semantics Name Key Value Code Error}
    (run : FrozenTrace program last sem) : PaperRemainingClaims.lemma59 run := by
  intro t bounded
  dsimp only
  have step := run.trace.step t bounded
  have ordinary := Labeled.Step.toCalculus step
  have metadata := Frame.step_stable program ordinary
  have scopes := TableFrame.reachable_scoped program
    (run.trace.prefixRun t (Nat.le_of_lt bounded))
  have appears (name : Name) :
      ControlFrame.viewAt (run.trace.state t) name = none →
      ControlFrame.viewAt (run.trace.state (t + 1)) name ≠ none →
      PaperRemainingClaims.isRuleAt run.trace t .begin name :=
    RuleEvaluation.appears_label program step name
  have disappears (name : Name) :
      ControlFrame.viewAt (run.trace.state t) name ≠ none →
      ControlFrame.viewAt (run.trace.state (t + 1)) name = none →
      PaperRemainingClaims.isRuleAt run.trace t .unload name :=
    RuleEvaluation.disappears_label program step name
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨edit, _, valid, applied⟩ := run.edited t bounded
    have factored := run.factored t bounded
    unfold PaperTraceEquations.Factors at factored
    have afterEdit := run.represented (t + 1) bounded
    rw [factored, applied] at afterEdit
    rw [← afterEdit]
    exact edit.preserves_tables _ valid
  · intro owner other acting later otherPresent actorPresent afterPresent different
    have frame := TableFrame.step_frame program step scopes acting actorPresent
      owner other later otherPresent afterPresent different
    exact ⟨fun changed => by
      obtain ⟨key, required, occupied, _⟩ := TableFrame.changed_key frame changed
      exact ⟨key, occupied, required⟩, frame⟩
  · intro name
    have fromEmpty := committedAt_eq_none_iff (run.trace.state t) name
    have toEmpty := committedAt_eq_none_iff (run.trace.state (t + 1)) name
    refine ⟨?_, ?_, committedAt_stable metadata (Ordering.step_views_stable program ordinary) name⟩
    · rintro ⟨before, after⟩
      exact appears name (fromEmpty.mp before) (fun empty => after (toEmpty.mpr empty))
    · rintro ⟨before, after⟩
      exact disappears name (fun empty => before (fromEmpty.mpr empty)) (toEmpty.mp after)
  · intro inverses permitted
    exact permitted.1
  · intro name old new before after
    constructor
    · rintro ⟨inactive, installed⟩
      apply appears name
      · simp [ControlFrame.viewAt, before, inactive, Phase.committed]
      · exact (ControlFrame.viewAt_present_iff _ _).mpr ⟨new, after, installed⟩
    · rintro ⟨installed, inactive⟩
      apply disappears name
      · exact (ControlFrame.viewAt_present_iff _ _).mpr ⟨old, before, installed⟩
      · simp [ControlFrame.viewAt, after, inactive, Phase.committed]
  · intro name old new before after
    obtain ⟨component, parent, monotone⟩ := metadata name old new before after
    refine ⟨component, parent, monotone, ?_⟩
    intro changed
    have retired : new.retired = true := by
      cases status : new.retired with
      | true => rfl
      | false =>
        cases previous : old.retired with
        | false => exact False.elim (changed (previous.trans status.symm))
        | true => exact status.symm.trans (monotone previous)
    refine ⟨retired, ?_⟩
    rcases RuleEvaluation.step_retirement_origin program step name old new before after changed with
      direct | ⟨unload, source, inverses, view, present, phase, inverse, member, retires⟩
    · exact .inl direct
    · refine .inr ⟨unload, source, present, ?_⟩
      have corresponding : inverse = .retire name := by
        cases inverse <;> simp_all [RuleEvaluation.Retires]
      simpa [phase, Phase.accumulator, ← corresponding] using member

/-- Convert the checked per-slot partial replay square to the union-table
observation used by the paper. -/
theorem partialReplayObservation {program : Program} (meaning : PartialReplayRegistry.Coeffects program)
    {rule : Labeled.Rule} {state middle : R} (reached : WellFormed.Run program (fun _ => none) state)
    (actor other : Name) (fiber foreign : F)
    (present : state actor = some fiber) (foreignPresent : state other = some foreign)
    (different : other ≠ actor)
    (separated : ∀ key, foreign.component.provides key = true → fiber.component.requires key = false)
    {use : RuleEvaluation.Use Name Key Value Code} {map : R → R}
    (frozen : EntangledApplications.FrozenApplication program other use state middle map)
    (allowed : use.allowed rule state other) (observation : Key → Setoid Value)
    (compatibility : ∀ key (v w : Value), (meaning.observe key).r v w → (observation key).r v w) :
    PaperStateObservation.TablesRelatedAt observation (fun _ => True)
      (discharge Stages.undo fiber.phase.accumulator (map state))
      (map (discharge Stages.undo fiber.phase.accumulator state)) := by
  have compared := PartialReplayRegistry.frozen_application_partial_square meaning reached actor other
    fiber foreign present foreignPresent different separated frozen allowed
  let left := discharge Stages.undo fiber.phase.accumulator (map state)
  let right := map (discharge Stages.undo fiber.phase.accumulator state)
  have sameSlot (owner : Name) (key : Key) : Iterators.OptionRel (meaning.observe key).r
      (StageRecovery.tableAt left owner key) (StageRecovery.tableAt right owner key) := by
    obtain ⟨a, b, _, _, first, second, observed⟩ := compared owner key
    have word : PartialReplayRegistry.saved state actor = fiber.phase.accumulator := by
      simp [PartialReplayRegistry.saved, present]
    rw [word] at first second
    change StageRecovery.tableAt left owner key = a at first
    change StageRecovery.tableAt right owner key = b at second
    rwa [first, second]
  intro key _
  constructor
  · intro owner value found
    have related := sameSlot owner key
    change StageRecovery.tableAt left owner key = some value at found
    rw [found] at related
    cases probe : StageRecovery.tableAt right owner key with
    | none => simp [probe, Iterators.OptionRel] at related
    | some result =>
      exact ⟨owner, result, probe, compatibility key value result
        (by simpa only [probe, Iterators.OptionRel] using related)⟩
  · intro owner value found
    have related := sameSlot owner key
    change StageRecovery.tableAt right owner key = some value at found
    rw [found] at related
    cases probe : StageRecovery.tableAt left owner key with
    | none => simp [probe, Iterators.OptionRel] at related
    | some result =>
      exact ⟨owner, result, probe, compatibility key result value
        (by simpa only [probe, Iterators.OptionRel] using related)⟩

end Cordis.Results
