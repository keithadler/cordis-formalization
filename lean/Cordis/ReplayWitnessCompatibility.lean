import Cordis.ReplayProjectionObstruction
import Cordis.GuardedApplications
import Cordis.StageRecovery
import Cordis.EntangledApplications
import Cordis.IndexedTrace

/-! A trace-level consequence of interpreting the paper's global iterator
witnesses by the concrete, owner-framed provision map.

This is NOT an alternative proof of Theorem68. `ProvisionCompatible` is an
explicit semantic/source identification contract: the current code is a
reachable head of a globally witnessed iterator, and its forward map is the
actual checked provision on ALL inputs of an arbitrary admissible Gamma subtype. Neither recovery, transition
preservation, nor a replay equation is included in that contract.

Under that identification an empty-origin ordinary trace cannot acquire even
its first binding. Thus a nonempty table-recovery example cannot simultaneously
inhabit the global witness and this source-faithful interpretation. Dropping
the all-input identification requires specifying the off-domain semantic map;
Definition55's present-actor confinement alone does not do that. -/
namespace Cordis.ReplayWitnessCompatibility
open Calculus Stages StageRecovery Iterators
universe u
variable {Name Key Value Code Error : Type u}
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
variable [DecidableEq Name] [DecidableEq Key] [Setoid Value]

def projectedSetoid (keys : Key → Prop) : Setoid R where
  r := ProjectedRelated keys
  iseqv := by
    constructor
    · intro state key selected
      exact ⟨fun owner value bound => ⟨owner, value, bound, Setoid.refl value⟩,
        fun owner value bound => ⟨owner, value, bound, Setoid.refl value⟩⟩
    · intro left right related key selected
      obtain ⟨forward, backward⟩ := related key selected
      exact ⟨fun owner value bound => by
          obtain ⟨other, v, found, observed⟩ := backward owner value bound
          exact ⟨other, v, found, Setoid.symm observed⟩,
        fun owner value bound => by
          obtain ⟨other, v, found, observed⟩ := forward owner value bound
          exact ⟨other, v, found, Setoid.symm observed⟩⟩
    · intro left middle right first second key selected
      obtain ⟨firstForward, firstBackward⟩ := first key selected
      obtain ⟨secondForward, secondBackward⟩ := second key selected
      exact ⟨fun owner value bound => by
          obtain ⟨other, v, found, observed⟩ := firstForward owner value bound
          obtain ⟨last, w, lastFound, lastObserved⟩ := secondForward other v found
          exact ⟨last, w, lastFound, Setoid.trans observed lastObserved⟩,
        fun owner value bound => by
          obtain ⟨other, v, found, observed⟩ := secondBackward owner value bound
          obtain ⟨last, w, lastFound, lastObserved⟩ := firstBackward other v found
          exact ⟨last, w, lastFound, Setoid.trans lastObserved observed⟩⟩

def domainSetoid (domain : R → Prop) (keys : Key → Prop) : Setoid {state : R // domain state} where
  r left right := ProjectedRelated keys left.val right.val
  iseqv := ⟨fun state => (projectedSetoid keys).iseqv.refl state.val,
    fun related => (projectedSetoid keys).iseqv.symm related,
    fun first second => (projectedSetoid keys).iseqv.trans first second⟩

end Cordis.ReplayWitnessCompatibility
