import Cordis.EntangledApplications

/-!
Legal-domain agreement for Lemma67. The paper's p45 identity extension is
explicit: a provision with an occupied key, an unresolved/raising operation,
or a disallowed instantiation is identity. Frozen maps agree with these guarded
maps at the two inputs of Lemma67, the actual state and its accumulated undo.
No claim about their agreement on all registries, or on the farther replay
states of Theorem68, is made.
-/
namespace Cordis.GuardedApplications
open Calculus Stages StageRecovery InterleavedRecovery AccumulatorProvenance EntangledApplications
universe u
variable {Name Key Value Code Error : Type u}
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
variable [DecidableEq Name] [DecidableEq Key]
set_option linter.unusedSectionVars false

abbrev routing := @Stages.bindingOwner

theorem location_routing (r : R) (actor : Name) (key : Key) :
    location r actor key = (routing r actor key).bind
      (fun owner => (tableAt r owner key).map (fun value => (owner, value))) := rfl

section Observation
variable [Setoid Value]

end Observation
end Cordis.GuardedApplications
