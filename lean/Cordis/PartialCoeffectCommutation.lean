import Cordis.PartialCoeffectLifting

/-! Distinct-key commutation with genuine partial maps. Equality compares
Option results, so both undefinedness and complete successful tables agree.
The theorem applies to arbitrary value maps, including forwards and inverses
captured at unrelated inputs. No failure is converted to identity.
These are necessary local results for45/47, not their full partial-iterator
independence/continuation theorem.
-/
namespace Cordis.PartialCoeffectLifting
open Coeffects Iterators PartialInverseObservation
universe u
variable {Key : Type u} {Value : Key → Type u} [DecidableEq Key]

def forward {S Outcome : Type u} (operation : Operation S Outcome) : PartialMap S :=
  fun input => (operation.run input).map Prod.fst

end Cordis.PartialCoeffectLifting
