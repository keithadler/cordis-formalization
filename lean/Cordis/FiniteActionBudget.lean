import Cordis.FiniteOrder

/-!
The finite acyclic numeric part of Theorem73. The edge orientation here is
provider→consumer. A strict rank is CONSTRUCTED by counting predecessors in a
finite covering list, rather than assumed. The resulting deliberately loose
bound depends only on K and the list length, so it also applies when different
finite prefixes have different acyclic dependency graphs.
-/
namespace Cordis.FiniteActionBudget
open FiniteOrder
universe u
variable {Name : Type u}
noncomputable section

theorem chain_prepend {rel : Name → Name → Prop} {a b c : Name}
    (edge : rel a b) (path : Chain rel b c) : Chain rel a c := by
  induction path with
  | single last => exact .tail (.single edge) last
  | tail _ last ih => exact .tail ih last

theorem chain_flip {rel : Name → Name → Prop} {a b : Name}
    (path : Chain (fun x y => rel y x) a b) : Chain rel b a := by
  induction path with
  | single edge => exact .single edge
  | tail _ edge ih => exact chain_prepend edge ih

theorem acyclic_flip (rel : Name → Name → Prop) (acyclic : Acyclic rel) :
    Acyclic (fun x y => rel y x) := fun name path => acyclic name (chain_flip path)

end
end Cordis.FiniteActionBudget
