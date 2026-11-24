import Cordis.Coeffects

/-! Partial-inverse extension of the explicit probe/capture repair. Definition29
allows both the forward and yielded inverse to be partial; every inverse letter
therefore observes its own definedness. Arbitrary probes and clearing the saved
store remain explicit extra commands, not a silent reading of Definition31.
The original Lemma32 ambiguity is not resolved by strengthening this grammar. -/
namespace Cordis.PartialInverseObservation
open Coeffects Iterators
universe u
variable {V A O : Type u}

structure Operation (V O : Type u) where
  run : V → Option (V × (V → Option V) × O)

def MapRelated (R : V → V → Prop) (left right : V → Option V) : Prop :=
  ∀ x y, R x y → OptionRel R (left x) (right y)

/-- Recovery explicitly requires the yielded inverse to be defined at its own
forward result. Respect separately compares its domain on all related probes. -/
structure Witnessed (operation : Operation V O) (R : V → V → Prop) : Prop where
  recover : ∀ input output inverse outcome,
    operation.run input = some (output, inverse, outcome) →
    ∃ restored, inverse output = some restored ∧ R restored input
  respect : ∀ left right, R left right →
    OptionRel (fun l r : V × (V → Option V) × O =>
      R l.1 r.1 ∧ MapRelated R l.2.1 r.2.1 ∧ l.2.2 = r.2.2)
      (operation.run left) (operation.run right)

end Cordis.PartialInverseObservation
