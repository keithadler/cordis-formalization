import Cordis.PartialMediatedIterators
import Cordis.PartialMapClosure
import Cordis.PartialCoeffectCommutation
import Cordis.PartialCoeffectProvision

/-! All successful-probe reachable heads and their captured inverses generate
partial transformation words. For disjoint mediated supports, BOTH complete
word monoids commute, including failed executions, and every reachable local
yield is unchanged by each successful foreign word. Outcome-selected tails
are compared literally here. Shared-key primitive independence and the paper's
omitted domain convention remain separate obligations for original 45/47. -/
namespace Cordis.PartialMediatedIndependence
open Coeffects (update)
open PartialCoeffectLifting PartialMapClosure PartialMediatedIterators
open PartialIterators (Iterator stage Reach)
universe u
variable {S : Type u}

def forward (iterator : Iterator S) : PartialMap S :=
  fun input => (iterator.run input).map Prod.fst

inductive Generator (root : Iterator S) : PartialMap S → Prop
  | forward {current} : Reach root current → Generator root (forward current)
  | inverse {current} (reached : Reach root current) (input output : S)
      (inverse : PartialMap S) (tail : Option (Iterator S))
      (called : current.run input = some (output, inverse, tail)) : Generator root inverse

end Cordis.PartialMediatedIndependence
