import Cordis.PartialObservedIteratorIndependence

/-! Primitive obligations for Definitions44/46 at a fixed observation quotient.
Names include operation arguments. Contracts concern lifted primitive operations,
not context-mediated iterators. They quantify forwards and every inverse from
an actual successful call, and compare inverse maps observationally (not by
literal function equality). Outcomes remain literal, as Equation41 requires.
Foreign-success guards implement the separately documented partial reading. -/
namespace Cordis.PartialCoeffectIndependenceContracts
open PartialCoeffectLifting PartialMapClosure PartialObservedMapClosure PartialInverseObservation
open PartialMediatedIterators
open Iterators (OptionRel)
open PartialIterators (Iterator stage)
universe u
variable {S : Type u}

inductive OperationGenerator {Outcome : Type u} (operation : Operation S Outcome) : PartialMap S → Prop
  | forward : OperationGenerator operation (PartialCoeffectLifting.forward operation)
  | inverse (input output : S) (inverse : PartialMap S) (outcome : Outcome)
      (called : operation.run input = some (output, inverse, outcome)) : OperationGenerator operation inverse

variable {Key : Type u} {Value : Key → Type u} [DecidableEq Key]

def tableSetoid (relations : ∀ key, Setoid (Value key)) (keys : Key → Prop) : Setoid (Table Value) where
  r := TableRelated (fun k => (relations k).r) keys
  iseqv := ⟨fun _ key _ => PartialObservedMapClosure.option_refl (relations key) _,
    fun {x y} h key selected => by
      have pair := h key selected
      cases a : x key <;> cases b : y key <;> simp_all [OptionRel]
      exact (relations key).symm pair,
    fun first second key selected => Iterators.OptionRel.trans
      (R := (relations key).r) (fun _ _ _ a b => (relations key).trans a b)
      (first key selected) (second key selected)⟩

end Cordis.PartialCoeffectIndependenceContracts
