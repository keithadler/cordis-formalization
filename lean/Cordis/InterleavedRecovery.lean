import Cordis.StageRecovery

/-! Binding-local maps used in the partial replay proof of Lemma 67. -/

namespace Cordis.InterleavedRecovery
open Calculus Stages StageRecovery
universe u
variable {Name Key Value Code Error : Type u}
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
variable [DecidableEq Name] [DecidableEq Key]

/-- A fixed captured owner/key map. Missing bindings remain missing, including
when the owning fiber itself is absent. The same map represents an operation's
forward value transformer and each concrete captured inverse. -/
def transform (owner : Name) (key : Key) (f : Value → Value) (r : R) : R :=
  Stages.undo (.operate owner key f) r

theorem tableAt_transform (r : R) (owner n : Name) (key k : Key) (f : Value → Value) :
    tableAt (transform owner key f r) n k =
      if n = owner ∧ k = key then (tableAt r n k).map f else tableAt r n k := by
  rw [transform, tableAt_operate]
  split
  · next h => rw [h.1, h.2]
  · rfl

/-- Errors are retained in `ResolvedResult`; this function names only the
state-map extension. Its identity error branch is not a successful transition. -/
def callbackMap (run : Value → Except Error (Value × (Value → Value) × Value))
    (v : Value) : Value :=
  match run v with
  | .error _ => v
  | .ok output => output.1

/-- A provision is independent only of inverses at other binding locations.
Unlike operations, provision and restriction at one key do not commute. -/
def Avoids (owner : Name) (key : Key) : Inverse Name Key Value → Prop
  | .operate n k _ | .restrict n k => ¬ (n = owner ∧ k = key)
  | _ => True

end Cordis.InterleavedRecovery
