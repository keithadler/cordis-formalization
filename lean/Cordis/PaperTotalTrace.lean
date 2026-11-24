import Cordis.PaperTotalLabeled

/-! Indexed total-model traces with arbitrary initial states. Empty-origin
prefixes derive admissibility and capture scope; lifecycle suffixes preserve
existing names and declaration edges, including real child births. -/
namespace Cordis.PaperTotal
noncomputable section
open Calculus Stages
universe u
variable {Name Key Value Code Error : Type u}
variable [DecidableEq Name] [DecidableEq Key]
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
set_option linter.unusedSectionVars false

structure Trace (model : Model Name Key Value Code Error) (initial : R) (last : Nat) where
  state : Nat → R
  rule : Nat → Cordis.Labeled.Rule
  actor : Nat → Name
  start : state 0 = initial
  step : ∀ t, t < last → Labeled.Step model (rule t) (actor t) (state t) (state (t + 1))

theorem Trace.run {model : Model Name Key Value Code Error} {initial : R} {last : Nat}
    (trace : Trace model initial last) (t : Nat) (bound : t ≤ last) :
    Run model.program model.draw model.failed initial (trace.state t) := by
  induction t with
  | zero => rw [trace.start]; exact .refl _
  | succ t ih => exact .tail (ih (by omega)) (trace.step t (by omega)).toCalculus

theorem Trace.invariant {model : Model Name Key Value Code Error} {initial : R} {last : Nat}
    (trace : Trace model initial last) (old : Invariant initial) (t : Nat) (bound : t ≤ last) :
    Invariant (trace.state t) := run_invariant model.program model.draw model.failed (trace.run t bound) old

theorem Trace.allowed {model : Model Name Key Value Code Error} {initial : R} {last : Nat}
    (trace : Trace model initial last) (old : MediatedRegistry.Allowed initial) (t : Nat) (bound : t ≤ last) :
    MediatedRegistry.Allowed (trace.state t) := by
  induction t with
  | zero => simpa [trace.start] using old
  | succ t ih =>
    obtain ⟨program, structural⟩ := (trace.step t (by omega)).structural
    have prior := ih (by omega)
    exact ⟨Safety.step_tree program structural.toCalculus prior.1,
      ordinary_step_finite program structural.toCalculus prior.2.1,
      Safety.step_owned program structural.toCalculus prior.2.2.1,
      WellFormed.step_disjoint program structural.toCalculus prior.2.2.2⟩

end
end Cordis.PaperTotal
