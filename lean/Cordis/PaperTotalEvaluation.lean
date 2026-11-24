import Cordis.MediatedRegistryFrames

/-! Total triple evaluation for the paper-level lifecycle, kept separate from
the partial source stage relation. Successful primitive evaluations retain their
exact state, captured inverse and selected continuation. A failed primitive uses
identity forward/inverse maps and an explicitly supplied continuation completion.
The completion either stops or selects a named outcome of the original code.

This is a family of total interpretations, not a claim that p45 specifies the
failed triple uniquely. In particular a completed failed head is NOT a source
Land. Structural preservation below is derived from the primitive cases; the
auxiliary unit program is used only to reuse program-independent frame proofs.
-/
namespace Cordis.PaperTotal
noncomputable section
open Calculus Stages
universe u
variable {Name Key Value Code Error : Type u}
variable [DecidableEq Name] [DecidableEq Key]
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "I" => Inverse Name Key Value
set_option linter.unusedSectionVars false

def evaluate (program : Code → Instruction Name Key Value Code Error)
    (draw : R → Name) (failed : Code → R → Option (Outcome Name Value))
    (actor : Name) (code : Code) (before : R) : SemanticHead.Result Name Key Value Code Error :=
  match SemanticHead.evaluate program actor (draw before) code before with
  | some result => result
  | none => (before, .unit, (failed code before).bind (program code).next)

/-- The graph is total because it is a graph of an ordinary total function,
not because a successful partial primitive execution is assumed. -/
def Landing (program : Code → Instruction Name Key Value Code Error)
    (draw : R → Name) (failed : Code → R → Option (Outcome Name Value)) :
    Calculus.Landing (Name := Name) (Key := Key) (Value := Value)
      (Code := Code) (Undo := I) (Error := Error) :=
  fun actor code before after inverse next =>
    evaluate program draw failed actor code before = (after, inverse, next)

theorem landing_cases (program : Code → Instruction Name Key Value Code Error)
    (draw : R → Name) (failed : Code → R → Option (Outcome Name Value))
    {actor : Name} {code : Code} {before after : R} {inverse : I} {next : Option Code}
    (landed : Landing program draw failed actor code before after inverse next) :
    (Land program actor code before after inverse next ∧ SemanticHead.CapturedChoice (draw before) inverse) ∨
      (SemanticHead.evaluate program actor (draw before) code before = none ∧
        after = before ∧ inverse = .unit ∧ next = (failed code before).bind (program code).next) := by
  unfold Landing evaluate at landed
  cases evaluated : SemanticHead.evaluate program actor (draw before) code before with
  | none =>
    simp only [evaluated] at landed
    cases landed
    exact .inr ⟨rfl, rfl, rfl, rfl⟩
  | some result =>
    simp only [evaluated] at landed
    subst result
    exact .inl (SemanticHead.evaluate_sound program actor (draw before) code before after inverse next evaluated)

theorem ordinary_landing (program : Code → Instruction Name Key Value Code Error)
    (draw : R → Name) (failed : Code → R → Option (Outcome Name Value))
    {actor : Name} {code : Code} {before after : R} {inverse : I} {next : Option Code}
    (landed : Land program actor code before after inverse next)
    (choice : SemanticHead.CapturedChoice (draw before) inverse) :
    Landing program draw failed actor code before after inverse next := by
  simp [Landing, evaluate, SemanticHead.evaluate_complete program landed (draw before) choice]

/-- This witness describes the four allowed structural mutations, not a
simulation by the original source program. In the failed case the auxiliary
program is explicitly different and has an identity/unit head. -/
theorem landing_structural (program : Code → Instruction Name Key Value Code Error)
    (draw : R → Name) (failed : Code → R → Option (Outcome Name Value))
    {actor : Name} {code : Code} {before after : R} {inverse : I} {next : Option Code}
    (landed : Landing program draw failed actor code before after inverse next) :
    ∃ structuralProgram : Code → Instruction Name Key Value Code Error,
      Land structuralProgram actor code before after inverse next := by
  rcases landing_cases program draw failed landed with actual | ⟨_, rfl, rfl, _⟩
  · exact ⟨program, actual.1⟩
  · exact ⟨fun _ => ⟨.unit, fun _ => next⟩, .unit _ actor code rfl⟩

/-- All nine lifecycle/orchestration constructors are reused verbatim. A local
structural program witness is enough for invariant theorems uniform in programs;
it does not identify a completed failure with a successful original program. -/
theorem step_structural (program : Code → Instruction Name Key Value Code Error)
    (draw : R → Name) (failed : Code → R → Option (Outcome Name Value))
    {before after : R} (step : Step (Landing program draw failed) Stages.undo before after) :
    ∃ structuralProgram : Code → Instruction Name Key Value Code Error,
      Step (Land structuralProgram) Stages.undo before after := by
  cases step with
  | insert name component parent ready => exact ⟨program, .insert before name component parent ready⟩
  | retire name present => exact ⟨program, .retire before name present⟩
  | remove name ready => exact ⟨program, .remove before name ready⟩
  | begin name fiber view present phase clean target =>
    exact ⟨program, .begin before name fiber view present phase clean target⟩
  | iter middle name fiber code stack view inverse next present phase target landed =>
    obtain ⟨localProgram, actual⟩ := landing_structural program draw failed landed
    exact ⟨localProgram, .iter before middle name fiber code stack view inverse next present phase target actual⟩
  | finish middle name fiber code stack view inverse present phase target landed =>
    obtain ⟨localProgram, actual⟩ := landing_structural program draw failed landed
    exact ⟨localProgram, .finish before middle name fiber code stack view inverse present phase target actual⟩
  | divert middle name fiber code stack view tail present phase changed alternative =>
    rcases alternative with abort | ⟨inverse, next, landed, tailEq⟩
    · exact ⟨program, .divert before middle name fiber code stack view tail present phase changed (.inl abort)⟩
    · obtain ⟨localProgram, actual⟩ := landing_structural program draw failed landed
      exact ⟨localProgram, .divert before middle name fiber code stack view tail present phase changed
        (.inr ⟨inverse, next, actual, tailEq⟩)⟩
  | leave name fiber stack view present phase changed =>
    exact ⟨program, .leave before name fiber stack view present phase changed⟩
  | unload name fiber stack view present phase free =>
    exact ⟨program, .unload before name fiber stack view present phase free⟩

/-- Exact connection to the previously constructed total heads on the finite,
rooted, owned and disjoint Gamma. The inverse equality is on ALL Gamma inputs. -/
theorem gamma_triple (program : Code → Instruction Name Key Value Code Error)
    (draw : R → Name) (failed : Code → R → Option (Outcome Name Value))
    (actor : Name) (code : Code) (before : MediatedRegistry.Gamma Name Key Value Code Error) :
    let triple := evaluate program draw failed actor code before.val
    ((MediatedRegistry.head program actor (fun state => draw state.val) code).run before).1.val = triple.1 ∧
      (∀ input : MediatedRegistry.Gamma Name Key Value Code Error,
        (((MediatedRegistry.head program actor (fun state => draw state.val) code).run before).2 input).val =
          Stages.undo triple.2.1 input.val) ∧
      MediatedRegistry.completedSelected program actor (fun state => draw state.val)
        (fun selected state => failed selected state.val) code before = triple.2.2 := by
  cases evaluated : SemanticHead.evaluate program actor (draw before.val) code before.val with
  | none =>
    have absent := MediatedRegistry.head_none program actor (fun state => draw state.val) code before evaluated
    simp [evaluate, evaluated, absent, Stages.undo, MediatedRegistry.completedSelected]
  | some result =>
    have exactHead := MediatedRegistry.head_some program actor (fun state => draw state.val) code before result evaluated
    simp only [evaluate, evaluated]
    refine ⟨exactHead.1, ?_, ?_⟩
    · intro input
      rw [exactHead.2]
      rfl
    · simp [MediatedRegistry.completedSelected, evaluated]

end
end Cordis.PaperTotal
