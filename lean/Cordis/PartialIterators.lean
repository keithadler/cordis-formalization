import Cordis.PartialCoeffectLifting

/-! A genuinely partial counterpart of the iterator functor in Definitions17,
30,34,37. A failed head has NO output, inverse, or selected tail. A successful
head may terminate (inner none) or select a continuation. Returned inverse maps
retain their own Option domains at arbitrary probes. This is an explicit
partial semantics, not an identification with the paper's total-function ℑ.
-/
namespace Cordis.PartialIterators
open Iterators PartialInverseObservation PartialCoeffectLifting
universe u
variable {S : Type u}
inductive Iterator (S : Type u) where
  | node (step : S → Option (S × (S → Option S) × Option (Iterator S)))

def Iterator.run : Iterator S → S → Option (S × PartialMap S × Option (Iterator S))
  | .node step => step

def unit : Iterator S := .node (fun input => some (input, some, none))

def stage {Outcome : Type u} (operation : Operation S Outcome)
    (next : Outcome → Option (Iterator S)) : Iterator S :=
  .node (fun input => (operation.run input).map (fun (output, inverse, result) => (output, inverse, next result)))

theorem stage_success_iff {Outcome : Type u} (operation : Operation S Outcome)
    (next : Outcome → Option (Iterator S)) (input output : S)
    (inverse : PartialMap S) (tail : Option (Iterator S)) :
    (stage operation next).run input = some (output, inverse, tail) ↔
      ∃ result, operation.run input = some (output, inverse, result) ∧ next result = tail := by
  constructor
  · intro success
    cases called : operation.run input with
    | none => simp [stage, Iterator.run, called] at success
    | some result =>
      obtain ⟨value, saved, result⟩ := result
      have same : value = output ∧ saved = inverse ∧ next result = tail := by
        simpa only [stage, Iterator.run, called, Option.map_some, Option.some.injEq, Prod.mk.injEq] using success
      obtain ⟨rfl, rfl, rfl⟩ := same
      exact ⟨result, rfl, rfl⟩
  · rintro ⟨result, called, rfl⟩
    simp [stage, Iterator.run, called]

/-- Reach is generated only by successful selected continuations, including
all possible input probes, not only one concrete execution. -/
inductive Reach (root : Iterator S) : Iterator S → Prop
  | root : Reach root root
  | continuation {current child : Iterator S} (prior : Reach root current)
      (input output : S) (inverse : PartialMap S)
      (selected : current.run input = some (output, inverse, some child)) : Reach root child

variable (observed : S → S → Prop)

def Unfold (relation : Iterator S → Iterator S → Prop) (left right : Iterator S) : Prop :=
  ∀ before other, observed before other →
    OptionRel (fun a b => observed a.1 b.1 ∧ MapRelated observed a.2.1 b.2.1 ∧
      OptionRel relation a.2.2 b.2.2) (left.run before) (right.run other)

/-- Greatest postfixed point, matching Definition34's coinductive reading.
The outer Option compares head definedness; the inner Option compares tails. -/
def Related (left right : Iterator S) : Prop :=
  ∃ relation : Iterator S → Iterator S → Prop,
    relation left right ∧ ∀ a b, relation a b → Unfold observed relation a b

theorem Unfold.mono {first second : Iterator S → Iterator S → Prop}
    (included : ∀ a b, first a b → second a b) {left right : Iterator S}
    (unfolded : Unfold observed first left right) : Unfold observed second left right := by
  intro a b inputs
  have result := unfolded a b inputs
  cases x : left.run a with
  | none => cases y : right.run b <;> simp_all [OptionRel]
  | some xValue =>
    cases y : right.run b with
    | none => simp_all [OptionRel]
    | some yValue =>
      obtain ⟨outputs, inverses, tails⟩ := (show observed xValue.1 yValue.1 ∧
        MapRelated observed xValue.2.1 yValue.2.1 ∧ OptionRel first xValue.2.2 yValue.2.2 by
          simpa only [x, y, OptionRel] using result)
      refine ⟨outputs, inverses, ?_⟩
      cases tx : xValue.2.2 <;> cases ty : yValue.2.2 <;> simp_all [OptionRel]

theorem related_unfold {left right : Iterator S} (related : Related observed left right) :
    Unfold observed (Related observed) left right := by
  obtain ⟨relation, pair, closed⟩ := related
  exact Unfold.mono observed (fun a b h => ⟨relation, h, closed⟩) (closed left right pair)

theorem related_coinduction (relation : Iterator S → Iterator S → Prop)
    (closed : ∀ a b, relation a b → Unfold observed relation a b)
    {left right : Iterator S} (pair : relation left right) : Related observed left right :=
  ⟨relation, pair, closed⟩

def ExactRecovery (iterator : Iterator S) : Prop :=
  ∀ input output inverse tail, iterator.run input = some (output, inverse, tail) →
    inverse output = some input

/-- Witness of the partial interpretation: every reachable stage has exact,
defined own-result recovery and full recursive logical self-relation. -/
def Witnessed (iterator : Iterator S) : Prop :=
  ∀ current, Reach iterator current → ExactRecovery current ∧ Related observed current current

end Cordis.PartialIterators
