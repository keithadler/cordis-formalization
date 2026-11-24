import Cordis.PaperTranspositionHistory

/-! All-nine adjacent activation exchange from actual empty-origin history.
Initial field typing, current-head reach/representation and structural Gamma
membership are conclusions of the history induction. Child membership is
requested only for actual new rows in the original events, never for every
syntactic instantiate instruction. The existing p46 independence convention
and explicit total-constructor interpretation remain unchanged.

History admission does not establish that global independence assumption.
Over the full structural Gamma, finer independence compares untouched function
fields too; their global admissibility cannot be inferred from reachable-state
typing alone. The example proves the independence premise separately. -/
namespace Cordis.PaperTranspositionHistory
noncomputable section
open Calculus Stages Iterators PaperTransposition
universe u
variable {Name Key Value Code Error : Type u}
variable [DecidableEq Name] [DecidableEq Key] [Setoid Value]
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
variable (meaning : Name → Code → Iterator (MediatedRegistry.Gamma Name Key Value Code Error))
variable (model : PaperTotal.Model Name Key Value Code Error)
local notation "sem" => PaperStateObservation.structural meaning

/-- The final wrapper has no TypedFields, CurrentHeads, MarkClosed,
BirthEntries, initial structural invariant or final-witness premise. -/
theorem activation_diamond_from_history
    (draws : DrawByPresence model.draw) (failures : FailureByTables model.failed)
    {last : Nat} (history : PaperTotal.Trace model (fun _ => none : R) last)
    (admitted : ∀ t, t < last → Admissions sem model (history.state t) (history.state (t + 1)))
    {first second : Name} {firstRule secondRule : Labeled.Rule} {middle final : R}
    (firstStep : PaperTotal.Labeled.Step model firstRule first (history.state last) middle)
    (firstActive : Transposition.Activation firstRule)
    (secondStep : PaperTotal.Labeled.Step model secondRule second middle final)
    (secondActive : Transposition.Activation secondRule)
    (firstEntries : Admissions sem model (history.state last) middle)
    (secondEntries : Admissions sem model middle final)
    (applicable : ∃ initial, PaperTotal.Labeled.Step model secondRule second (history.state last) initial)
    (different : first ≠ second)
    (independent : ComponentsIndependent sem (history.state last) first second) :
    ∃ swappedMiddle swappedFinal,
      PaperTotal.Labeled.Step model secondRule second (history.state last) swappedMiddle ∧
      PaperTotal.Labeled.Step model firstRule first swappedMiddle swappedFinal ∧
      PaperStateObservation.Related sem swappedFinal final := by
  have invariant := history.invariant PaperTotal.empty_invariant last (Nat.le_refl _)
  let state : (PaperStateObservation.structural meaning).Gamma := ⟨history.state last, invariant.1⟩
  have fields := structural_trace_fields model meaning history admitted last (Nat.le_refl _)
  have middleFields := step_fields sem model state firstStep fields firstEntries
  have middleAllowed := (PaperTotal.step_invariant model.program model.draw model.failed
    firstStep.toCalculus invariant).1
  have finalFields := step_fields sem model ⟨middle, middleAllowed⟩ secondStep middleFields secondEntries
  exact PaperTransposition.activation_diamond sem model draws failures state firstStep firstActive
    secondStep secondActive applicable different invariant.1.2.2.1 invariant.1.2.2.2
    (fields.heads sem model) independent (finalFields.typed sem model)

end
end Cordis.PaperTranspositionHistory
