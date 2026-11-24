import Cordis.TranspositionBegin
import Cordis.AccumulatorProvenance

/-! Local context facts for the landed-activation cases of Lemma78(1).
Simultaneously applicable activations cannot provide one another's required
bindings: they are not active yet, while every selected binding is active and
its declaration has a unique owner. These facts derive primitive separation
from the actual paper guards and ownership invariant. -/
namespace Cordis.Transposition
open Calculus Stages Labeled
universe u
variable {Name Key Value Code Error : Type u}
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
variable [DecidableEq Name] [DecidableEq Key]
set_option linter.unusedSectionVars false

theorem unavailable_provision_not_required (r : R) (provider consumer : Name)
    (supplier client : F) (supplierFound : r provider = some supplier) (clientFound : r consumer = some client)
    (owned : Safety.Owned r) (disjoint : WellFormed.Disjoint r)
    (unavailable : ¬ supplier.phase.available) (view : View Name Key) (target : Target r consumer view)
    (key : Key) (provided : supplier.component.provides key = true) : client.component.requires key = false := by
  cases required : client.component.requires key with
  | false => rfl
  | true =>
    simp only [Target, clientFound] at target
    have ready := target.2 key required
    cases selected : r (view key) with
    | none => simp [selected] at ready
    | some actual =>
      simp only [selected] at ready
      have actualProvides := owned (view key) actual key selected ready.2
      have sameOwner : provider = view key := by
        by_cases same : provider = view key
        · exact same
        · exact False.elim (disjoint provider (view key) supplier actual supplierFound selected same key
            ⟨provided, actualProvides⟩)
      have supplierSelected : r (view key) = some supplier := by simpa only [sameOwner] using supplierFound
      have sameEntry : supplier = actual := Option.some.inj (supplierSelected.symm.trans selected)
      exact False.elim (unavailable (sameEntry ▸ ready.1))

end Cordis.Transposition
