import Cordis.PaperStateObservation
import Cordis.TranspositionActivation
import Cordis.StageSimulation
import Cordis.EntangledApplications
import Cordis.Independence
import Cordis.Coeffects
import Cordis.GuardedApplications

/-! The literal Equation54 observation of the concrete activation diamond.

The structural diamond supplies same-input comparison of paired cleanup words.
Definition34 needs more: arbitrary union-equivalent inputs, even when a binding
changes owner. Here that extra clause comes from the actual stored word's
generator provenance in globally witnessed iterators. No per-owner restriction
is placed on those inputs, and no whole-word relation is assumed.

The landing-to-generator contract and the stored code denotations are explicit
semantic representation obligations. This is an observation bridge for the
concrete diamond, not yet the original Lemma78 from Definition65 alone. In
particular it does not identify checked off-domain maps with arbitrary paper
semantics or bypass the checked global-witness collapse theorem. -/
namespace Cordis.PaperTranspositionObservation
noncomputable section
open Calculus Stages Iterators Effects StageRecovery
universe u
variable {Name Key Value Code Error : Type u}
variable [DecidableEq Name] [DecidableEq Key] [Setoid Value]
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
local notation "I" => Inverse Name Key Value
variable (sem : PaperStateObservation.Semantics Name Key Value Code Error)
local instance : Setoid sem.Gamma := PaperStateObservation.base sem
set_option linter.unusedSectionVars false

/-- A captured token denotes an actual Def40 generator, on every admissible
input, of an independently witnessed iterator. This is not a respect premise. -/
def GeneratedInverse (token : I) : Prop :=
  ∃ iterator : Iterator sem.Gamma, WitnessedIterator iterator ∧
    Generator iterator (PaperStateObservation.inverse sem token)

theorem generated_inverse_respects {token : I} (generated : GeneratedInverse sem token) :
    Effects.Respects (PaperStateObservation.inverse sem token) := by
  obtain ⟨iterator, witnessed, generator⟩ := generated
  exact Iterators.generator_respects witnessed generator

end
end Cordis.PaperTranspositionObservation
