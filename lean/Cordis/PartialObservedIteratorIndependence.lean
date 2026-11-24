import Cordis.PartialMediatedIndependence
import Cordis.PartialIteratorRelationLaws

/-! The observed, genuinely partial generated-map clauses of Definition42.
This module is a closure lemma; its local generator hypotheses must still be
derived from primitive coeffect contracts in an application of Theorem47. -/
namespace Cordis.PartialObservedIteratorIndependence
open PartialCoeffectLifting PartialMapClosure PartialMediatedIndependence PartialObservedMapClosure
open PartialIterators (Iterator Reach Witnessed Related)
open PartialIteratorRelationLaws (YieldRel observe)
open Iterators (OptionRel)
universe u
variable {S : Type u}
variable (observation : Setoid S)

structure Independent (left right : Iterator S) : Prop where
  commute : ∀ f, Generated (Generator left) f → ∀ g, Generated (Generator right) g →
    Commutes observation f g
  left_yield : ∀ current, Reach left current → ∀ g, Generated (Generator right) g →
    Preserves (YieldRel observation) (observe current) g
  right_yield : ∀ current, Reach right current → ∀ f, Generated (Generator left) f →
    Preserves (YieldRel observation) (observe current) f

theorem generator_respects {iterator : Iterator S} (witness : Witnessed observation.r iterator)
    {map : PartialMap S} (generator : Generator iterator map) : Maps observation map map := by
  cases generator with
  | forward reached =>
    intro left right related
    have expanded := PartialIterators.related_unfold observation.r (witness _ reached).2 left right related
    unfold PartialMediatedIndependence.forward
    cases a : PartialIterators.Iterator.run _ left <;> cases b : PartialIterators.Iterator.run _ right <;>
      simp only [a, b, OptionRel, Option.map_some, Option.map_none] at expanded ⊢
    exact expanded.1
  | inverse reached input output _ tail called =>
    have expanded := PartialIterators.related_unfold observation.r (witness _ reached).2 input input (observation.refl input)
    rw [called] at expanded
    exact expanded.2.1

/-- Both clauses of Definition 42 lift from the reachable generators to
their entire mixed monoids. Reachability and iterator witnesses justify
respect and the identity word's yield. -/
theorem of_generators {left right : Iterator S}
    (leftWitness : Witnessed observation.r left) (rightWitness : Witnessed observation.r right)
    (commutes : ∀ f g, Generator left f → Generator right g → Commutes observation f g)
    (leftYield : ∀ current, Reach left current → ∀ g, Generator right g →
      Preserves (YieldRel observation) (observe current) g)
    (rightYield : ∀ current, Reach right current → ∀ f, Generator left f →
      Preserves (YieldRel observation) (observe current) f) : Independent observation left right := by
  constructor
  · intro f leftWord g rightWord
    exact generated_commutes observation (fun _ => generator_respects observation leftWitness)
      (fun _ => generator_respects observation rightWitness) commutes leftWord rightWord
  · intro current reached g word
    exact generated_preserves (PartialIteratorRelationLaws.yield_refl observation (leftWitness current reached).2)
      (PartialIteratorRelationLaws.yield_trans observation) (leftYield current reached) word
  · intro current reached f word
    exact generated_preserves (PartialIteratorRelationLaws.yield_refl observation (rightWitness current reached).2)
      (PartialIteratorRelationLaws.yield_trans observation) (rightYield current reached) word

end Cordis.PartialObservedIteratorIndependence
