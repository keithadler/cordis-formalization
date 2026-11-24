import Cordis.StageRecovery

/-! An owner-domain obstruction to Definition51 congruence, independent of
finite-name encodings. Two related full registries may differ by an empty
actor. An ordinary table update cannot both leave an absent actor absent and
frame ALL other owners while agreeing with a real provision at the other input.
The proof uses no finite-name, callback, episode, or reachability assumption;
actual reachable witnesses are supplied separately. It also applies when the
two inputs and their outputs are restricted to an admissible Gamma subtype. -/
namespace Cordis.ReplayProjectionObstruction
open Calculus Stages StageRecovery
universe u
variable {Name Key Value Code Error : Type u}
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error

def EmptyAt (state : R) (key : Key) : Prop :=
  ∀ owner, tableAt state owner key = none

section Observation
variable [Setoid Value]

theorem binding_separates_empty (keys : Key → Prop) (key : Key) (selected : keys key)
    (emptyState providedState : R) (empty : EmptyAt emptyState key)
    (owner : Name) (value : Value) (binding : tableAt providedState owner key = some value) :
    ¬ ProjectedRelated keys emptyState providedState := by
  intro observed
  obtain ⟨other, foundValue, found, _⟩ := (observed key selected).2 owner value binding
  rw [empty other] at found
  cases found

end Observation
end Cordis.ReplayProjectionObstruction
