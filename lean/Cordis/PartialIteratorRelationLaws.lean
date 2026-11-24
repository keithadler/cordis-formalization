import Cordis.PartialIterators
import Cordis.PartialObservedMapClosure

/-! Symmetry/transitivity of the genuine partial recursive relation and of
complete yielded inverse/tail observations. No reflexivity is asserted for
arbitrary unwitnessed iterators or arbitrary partial maps. -/
namespace Cordis.PartialIteratorRelationLaws
open PartialCoeffectLifting PartialInverseObservation PartialObservedMapClosure
open Iterators (OptionRel)
open PartialIterators
universe u
variable {S : Type u} (observation : Setoid S)

abbrev Yield := PartialMap S × Option (Iterator S)

def YieldRel (left right : Option (Yield (S := S))) : Prop :=
  OptionRel (fun a b => Maps observation a.1 b.1 ∧ OptionRel (Related observation.r) a.2 b.2) left right

def observe (iterator : Iterator S) : S → Option (Yield (S := S)) :=
  fun input => (iterator.run input).map Prod.snd

/-- Composition of two recursive observations uses the same center probe
at each head and the composed witness on the selected tails. -/
theorem related_trans {first middle last : Iterator S}
    (left : Related observation.r first middle) (right : Related observation.r middle last) :
    Related observation.r first last := by
  let through := fun a c => ∃ b, Related observation.r a b ∧ Related observation.r b c
  refine related_coinduction observation.r through ?_ ⟨middle, left, right⟩
  rintro a c ⟨b, ab, bc⟩ input output inputs
  have firstStep := related_unfold observation.r ab input input (observation.refl input)
  have secondStep := related_unfold observation.r bc input output inputs
  cases leftRun : a.run input <;> cases centerRun : b.run input <;> cases rightRun : c.run output <;>
    simp only [leftRun, centerRun, rightRun, OptionRel] at firstStep secondStep ⊢
  rename_i leftData centerData rightData
  refine ⟨observation.trans firstStep.1 secondStep.1, maps_trans observation firstStep.2.1 secondStep.2.1, ?_⟩
  have firstTail := firstStep.2.2
  have secondTail := secondStep.2.2
  cases leftTail : leftData.2.2 <;> cases centerTail : centerData.2.2 <;> cases rightTail : rightData.2.2 <;>
    simp only [leftTail, centerTail, rightTail] at firstTail secondTail ⊢
  exact ⟨_, firstTail, secondTail⟩

theorem yield_refl {iterator : Iterator S} (related : Related observation.r iterator iterator) (input : S) :
    YieldRel observation (observe iterator input) (observe iterator input) := by
  have expanded := related_unfold observation.r related input input (observation.refl input)
  cases called : iterator.run input <;> simp only [YieldRel, observe, called, Option.map_none, Option.map_some, OptionRel] at expanded ⊢
  exact expanded.2

theorem yield_trans {a b c : Option (Yield (S := S))}
    (first : YieldRel observation a b) (second : YieldRel observation b c) : YieldRel observation a c := by
  apply OptionRel.trans _ first second
  intro _ _ _ left right
  exact ⟨maps_trans observation left.1 right.1,
    OptionRel.trans (R := Related observation.r) (fun _ _ _ first second => related_trans observation first second)
      left.2 right.2⟩

end Cordis.PartialIteratorRelationLaws
