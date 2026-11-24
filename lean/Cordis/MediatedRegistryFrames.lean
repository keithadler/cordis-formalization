import Cordis.MediatedRegistryDomain

/-! Constructor-derived complementary frames on the structural registry Gamma.
Every primitive head, including its failed-domain identity extension, and EVERY
input to every yielded inverse preserves keys outside the declaration set.
The finite Definition56 grammar propagates this result to all produced tails.
No frame or relation-preservation conclusion is supplied as a constructor.

An independent Definition48 global witness for the local table projection can
therefore be promoted to the full key projection. This is not a proof of the
refuted Lemma57 membership assertion. In particular, ordinary first provision
does not acquire an impossible global witness merely by satisfying this syntax.
-/
namespace Cordis.MediatedRegistry
noncomputable section
open Calculus Stages Iterators StageRecovery
universe u
variable {Name Key Value Code Error : Type u}
variable [DecidableEq Name] [DecidableEq Key] [Setoid Value]
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "G" => Gamma Name Key Value Code Error
set_option linter.unusedSectionVars false

def observation (keys : Key → Prop) : Setoid G := ReplayWitnessCompatibility.domainSetoid Allowed keys

/-- Literal finite named-continuation grammar. The declaration predicates can
be instantiated with d and p; operations use d∪p and provision uses p. Every
named continuation is another member, including outcomes not reached here. -/
inductive Mediated (program : Code → Instruction Name Key Value Code Error)
    (requires provides : Key → Prop) : Code → Prop
  | unit (code : Code) (action : (program code).action = .unit)
      (terminal : ∀ outcome, (program code).next outcome = none) : Mediated program requires provides code
  | operation (code : Code) (key : Key) (run : Value → Except Error (Value × (Value → Value) × Value))
      (action : (program code).action = .operate key run) (declared : requires key ∨ provides key)
      (tails : ∀ outcome following, (program code).next outcome = some following →
        Mediated program requires provides following) : Mediated program requires provides code
  | provision (code : Code) (key : Key) (value : Value)
      (action : (program code).action = .provide key value) (declared : provides key)
      (tails : ∀ outcome following, (program code).next outcome = some following →
        Mediated program requires provides following) : Mediated program requires provides code
  | birth (code : Code) (component : Component Key Code)
      (action : (program code).action = .instantiate component)
      (tails : ∀ outcome following, (program code).next outcome = some following →
        Mediated program requires provides following) : Mediated program requires provides code

end
end Cordis.MediatedRegistry
