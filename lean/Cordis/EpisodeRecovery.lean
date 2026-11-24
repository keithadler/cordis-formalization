import Cordis.GuardedApplications

/-!
Theorem68's local recurrence on actual labeled transitions. The accumulator is
read from the actual current phase. Own landings push their actual returned
inverse; foreign applications are obtained by factoring the real rule. The
checked foreign map agrees at the actual and locally recovered inputs.

This module does not assert that this checked map respects table projection at
arbitrary distant counterfactual inputs. That additional replay-domain issue is
separate from deriving the local recurrence from the operational trace.
-/
namespace Cordis.EpisodeRecovery
open Calculus Stages StageRecovery InterleavedRecovery AccumulatorProvenance
  EntangledApplications
universe u
variable {Name Key Value Code Error : Type u}
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
variable [DecidableEq Name] [DecidableEq Key]
set_option linter.unusedSectionVars false

section Observation
variable [Setoid Value]

end Observation
end Cordis.EpisodeRecovery
