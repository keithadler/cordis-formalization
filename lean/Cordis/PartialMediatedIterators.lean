import Cordis.PartialIterators
import Cordis.PartialCoeffectProvision

/-! Definition30's unit/operation/provision grammar with genuinely partial
triple evaluation and partial captured inverses. Primitive exact recovery and
cross-input triple contracts derive every reachable stage's recovery and the
full coinductive recursive logical relation; no iterator witness is a premise.
Provision and restriction retain Definitions19/20's original domain guards.

This establishes the partial counterpart of Lemma39. Definition37's displayed
total-function type is a distinct interpretation obligation, so this does not
promote the full original statement or assume Lemma32's ambiguous yield law.
-/
namespace Cordis.PartialMediatedIterators
open Coeffects PartialInverseObservation PartialCoeffectLifting
open Iterators (OptionRel)
open PartialIterators (Iterator stage)
universe u
variable {Key : Type u} {Value : Key → Type u} [DecidableEq Key]

structure Signature (Value : Key → Type u) where
  Name : Type u
  Outcome : Name → Type u
  key : Name → Key
  operation : (name : Name) → Operation (Value (key name)) (Outcome name)

def Signature.lifted (signature : Signature Value) (name : signature.Name) :=
  liftOperation (signature.key name) (signature.operation name)

structure Contracts (signature : Signature Value) (relations : ∀ key, Setoid (Value key)) : Prop where
  recovery : ∀ name input output inverse outcome,
    (signature.operation name).run input = some (output, inverse, outcome) → inverse output = some input
  respect : ∀ name left right, (relations (signature.key name)).r left right →
    OptionRel (fun a b => (relations (signature.key name)).r a.1 b.1 ∧
      MapRelated (relations (signature.key name)).r a.2.1 b.2.1 ∧ a.2.2 = b.2.2)
      ((signature.operation name).run left) ((signature.operation name).run right)

inductive Mediated (signature : Signature Value) (keys provided : Key → Prop) : Iterator (Table Value) → Prop
  | unit : Mediated signature keys provided PartialIterators.unit
  | operation (name : signature.Name) (selected : keys (signature.key name))
      (next : signature.Outcome name → Option (Iterator (Table Value)))
      (tails : ∀ outcome child, next outcome = some child → Mediated signature keys provided child) :
      Mediated signature keys provided (stage (signature.lifted name) next)
  | provision (key : Key) (selected : keys key) (allowed : provided key) (value : Value key)
      (next : Option (Iterator (Table Value)))
      (tail : ∀ child, next = some child → Mediated signature keys provided child) :
      Mediated signature keys provided (stage (PartialCoeffectProvision.provision key value) (fun _ => next))

theorem Mediated.continuation {signature : Signature Value} {keys provided : Key → Prop}
    {iterator child : Iterator (Table Value)} (member : Mediated signature keys provided iterator)
    (input output : Table Value) (inverse : PartialMap (Table Value))
    (selected : iterator.run input = some (output, inverse, some child)) :
    Mediated signature keys provided child := by
  cases member with
  | unit => simp [PartialIterators.unit, PartialIterators.Iterator.run] at selected
  | operation name _ next tails =>
    obtain ⟨result, _, branch⟩ := (PartialIterators.stage_success_iff _ next input output inverse (some child)).mp selected
    exact tails result child branch
  | provision key _ _ value next tail =>
    obtain ⟨_, _, branch⟩ := (PartialIterators.stage_success_iff _ (fun _ => next) input output inverse (some child)).mp selected
    exact tail child branch

theorem Mediated.reachable {signature : Signature Value} {keys provided : Key → Prop}
    {root current : Iterator (Table Value)} (member : Mediated signature keys provided root)
    (reached : PartialIterators.Reach root current) : Mediated signature keys provided current := by
  induction reached with
  | root => exact member
  | continuation _ input output inverse selected ih => exact ih.continuation input output inverse selected

theorem Mediated.exact_recovery {signature : Signature Value} {keys provided : Key → Prop}
    (exact : ∀ name input output inverse outcome,
      (signature.operation name).run input = some (output, inverse, outcome) → inverse output = some input)
    {iterator : Iterator (Table Value)} (member : Mediated signature keys provided iterator) :
    PartialIterators.ExactRecovery iterator := by
  intro input output inverse next called
  cases member with
  | unit =>
    have same : input = output ∧ some = inverse ∧ none = next := by
      simpa only [PartialIterators.unit, PartialIterators.Iterator.run, Option.some.injEq, Prod.mk.injEq] using called
    obtain ⟨rfl, rfl, rfl⟩ := same
    rfl
  | operation name _ branch _ =>
    obtain ⟨outcome, operation, _⟩ := (PartialIterators.stage_success_iff _ branch input output inverse next).mp called
    exact lift_exact (signature.key name) (signature.operation name) (exact name) input output inverse outcome operation
  | provision key _ _ value branch _ =>
    obtain ⟨outcome, operation, _⟩ := (PartialIterators.stage_success_iff _ (fun _ => branch) input output inverse next).mp called
    exact PartialCoeffectProvision.exact_recovery key value input output inverse outcome operation

end Cordis.PartialMediatedIterators
