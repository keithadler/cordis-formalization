import Cordis.PaperTotalEvaluation
import Cordis.TranspositionActivation

/-! The control-read seam in the paper's transposition argument.

Definition55's surrounding prose forbids reading lifecycle control fields.
For the concrete total interpretation family this is made explicit at the two
semantic choices left as parameters: the fresh draw depends only on presence,
and a failed head's selected outcome depends only on tables. These are data
dependence contracts, not assumed stage commutation or transition preservation.
Successful and failed primitive cases then derive exact foreign-phase
transport, including the captured inverse and selected continuation.

The arbitrary completion family in PaperTotalEvaluation does not satisfy these
contracts automatically. This module does not claim that p45 specifies a
unique failed triple or that its graph is the partial source Land relation. -/
namespace Cordis.PaperTransposition
noncomputable section
open Calculus Stages StageRecovery
universe u
variable {Name Key Value Code Error : Type u}
variable [DecidableEq Name] [DecidableEq Key]
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
local notation "I" => Inverse Name Key Value
local notation "Result" => SemanticHead.Result Name Key Value Code Error
set_option linter.unusedSectionVars false

def DrawByPresence (draw : R → Name) : Prop :=
  ∀ left right, (∀ name, left name = none ↔ right name = none) → draw left = draw right

def FailureByTables (failed : Code → R → Option (Outcome Name Value)) : Prop :=
  ∀ code left right, (∀ owner key, tableAt left owner key = tableAt right owner key) →
    failed code left = failed code right

def markResult (name : Name) (phase : Phase Name Key Code I) (result : Result) : Result :=
  (mark result.1 name phase, result.2.1, result.2.2)

theorem selected_evaluate_mark (program : Code → Instruction Name Key Value Code Error)
    (actor child name : Name) (code : Code) (before : R) (fiber : F)
    (phase : Phase Name Key Code I) (different : actor ≠ name) (present : before name = some fiber) :
    SemanticHead.evaluate program actor child code (mark before name phase) =
      (SemanticHead.evaluate program actor child code before).map (markResult name phase) := by
  cases evaluated : SemanticHead.evaluate program actor child code before with
  | some result =>
    obtain ⟨after, inverse, next⟩ := result
    obtain ⟨landed, chosen⟩ := SemanticHead.evaluate_sound program actor child code before after inverse next evaluated
    have moved := Transposition.land_mark program landed name phase different (by simp [present])
    exact SemanticHead.evaluate_complete program moved child chosen
  | none =>
    apply (SemanticHead.undefined_iff program actor child code (mark before name phase)).mpr
    rintro ⟨after, inverse, next, landed, chosen⟩
    have marked := Calculus.mark_self before name fiber phase present
    have restored := Transposition.land_mark program landed name fiber.phase different (by simp [marked])
    have restores : mark (mark before name phase) name fiber.phase = before := by
      rw [Transposition.mark_twice]
      exact Transposition.mark_existing before name fiber present
    rw [restores] at restored
    have success := SemanticHead.evaluate_complete program restored child chosen
    rw [evaluated] at success
    cases success

/-- Exact result equality, rather than a desired observational diamond. It is
derived for all five instruction constructors through the evaluator/Land iff. -/
theorem evaluate_mark (program : Code → Instruction Name Key Value Code Error)
    (draw : R → Name) (failed : Code → R → Option (Outcome Name Value))
    (draws : DrawByPresence draw) (failures : FailureByTables failed)
    (actor name : Name) (code : Code) (before : R) (fiber : F)
    (phase : Phase Name Key Code I) (different : actor ≠ name) (present : before name = some fiber) :
    PaperTotal.evaluate program draw failed actor code (mark before name phase) =
      markResult name phase (PaperTotal.evaluate program draw failed actor code before) := by
  have drawing : draw (mark before name phase) = draw before :=
    draws _ _ (fun other => Transposition.mark_presence before name other phase)
  have failure : failed code (mark before name phase) = failed code before :=
    failures code _ _ (fun owner key => by simp only [tableAt_mark])
  unfold PaperTotal.evaluate
  rw [drawing, selected_evaluate_mark program actor (draw before) name code before fiber phase different present]
  cases evaluated : SemanticHead.evaluate program actor (draw before) code before <;>
    simp [Option.map, markResult, failure]

theorem landing_mark (program : Code → Instruction Name Key Value Code Error)
    (draw : R → Name) (failed : Code → R → Option (Outcome Name Value))
    (draws : DrawByPresence draw) (failures : FailureByTables failed)
    {actor : Name} {code : Code} {before after : R} {inverse : I} {next : Option Code}
    (landed : PaperTotal.Landing program draw failed actor code before after inverse next)
    (name : Name) (fiber : F) (phase : Phase Name Key Code I)
    (different : actor ≠ name) (present : before name = some fiber) :
    PaperTotal.Landing program draw failed actor code (mark before name phase)
      (mark after name phase) inverse next := by
  change PaperTotal.evaluate program draw failed actor code _ = _
  rw [evaluate_mark program draw failed draws failures actor name code before fiber phase different present, landed]
  rfl

/-- The completed evaluation preserves each existing row's passive fields by
the same primitive cases as the source. A failed identity head needs no source
success assumption. -/
theorem landing_existing_table (program : Code → Instruction Name Key Value Code Error)
    (draw : R → Name) (failed : Code → R → Option (Outcome Name Value))
    {actor : Name} {code : Code} {before after : R} {inverse : I} {next : Option Code}
    (landed : PaperTotal.Landing program draw failed actor code before after inverse next)
    (name : Name) (fiber : F) (present : before name = some fiber) :
    ∃ table, after name = some {fiber with table := table} := by
  obtain ⟨localProgram, actual⟩ := PaperTotal.landing_structural program draw failed landed
  exact Transposition.land_existing_table localProgram actual name fiber present

theorem landing_target_forward (program : Code → Instruction Name Key Value Code Error)
    (draw : R → Name) (failed : Code → R → Option (Outcome Name Value))
    {actor : Name} {code : Code} {before after : R} {inverse : I} {next : Option Code}
    (landed : PaperTotal.Landing program draw failed actor code before after inverse next)
    (fiber : F) (present : before actor = some fiber) (unavailable : ¬ fiber.phase.available)
    (phase : Phase Name Key Code I) (name : Name) (view : View Name Key) (different : name ≠ actor)
    (target : Target before name view) : Target (mark after actor phase) name view := by
  obtain ⟨localProgram, actual⟩ := PaperTotal.landing_structural program draw failed landed
  exact Transposition.landing_mark_target localProgram actual fiber present unavailable phase name view different target

end
end Cordis.PaperTransposition
