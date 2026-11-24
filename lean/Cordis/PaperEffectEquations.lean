import Cordis.PartialMediatedIterators

/-! Cordis v1, pp. 9–16 and 21–22. Total effects and iterators in §3.1
use exact equality. The operations and stages in §3.3.1 use the partial-map
reading offered on p. 17. Theorem statements below are propositions. -/
namespace Cordis.PaperEffectEquations

universe u
open Effects (Effect identity)
open Tracking (Context History diamond forward inverse lift recover track twistedMul twistedUnit uniform)
open Iterators (Iterator effectiter embed)

section TrackedPairs
variable {Γ : Type u}

end TrackedPairs

section TotalEffects
variable {Γ : Type u}

/-- Eq. (13), Definition 9, p. 13. The right operand runs first. -/
def eq13 : Prop :=
  ∀ (f g : Effect Γ) (γ : Γ), (diamond f g).run γ =
    let (δ, s) := g.run γ
    let (ε, t) := f.run δ
    (ε, s ∘ t)

/-- Eq. (17), Definition 17, pp. 15–16. `Iterator` splits each triple into
its effect pair and input-selected continuation. -/
def iterate (i : Iterator Γ) (γ : Γ) : Γ × (Γ → Γ) × Option (Iterator Γ) :=
  let (δ, g) := i.effect.run γ
  (δ, g, i.next γ)

end TotalEffects

section PartialStages
open PartialInverseObservation (Operation)
open PartialCoeffectLifting (Table liftMap liftOperation)
open PartialMediatedIterators (Signature Mediated)
variable {K : Type u} {V : K → Type u} [DecidableEq K]

/-- Eq. (30), Definition 29, pp. 21–22. A key has a family of operations,
each with its own argument and outcome type. Both maps are partial. -/
structure CoeffectOperations (V : K → Type u) where
  Name : K → Type u
  Argument : (k : K) → Name k → Type u
  Outcome : (k : K) → Name k → Type u
  operation : (k : K) → (a : Name k) → Argument k a → Operation (V k) (Outcome k a)

def ValueOperationWitness (operations : CoeffectOperations V) : Prop :=
  ∀ k a x v w g b, (operations.operation k a x).run v = some (w, g, b) → g w = some v

/-- The stage grammar indexes each operation application by its key, name,
and supplied argument. -/
def CoeffectOperations.stageSignature (operations : CoeffectOperations V) : Signature V where
  Name := (k : K) × (a : operations.Name k) × operations.Argument k a
  Outcome request := operations.Outcome request.1 request.2.1
  key := Sigma.fst
  operation request := operations.operation request.1 request.2.1 request.2.2

/-- The constructors of `Mediated` generate
the least class with a unit, an outcome-selected operation tail at a key in S,
and a provision with a fixed tail at a key in P. The paper assumes P ⊆ S. -/
abbrev ContextMediated (operations : CoeffectOperations V) (S P : K → Prop)
    (_subset : ∀ k, P k → S k) := Mediated operations.stageSignature S P

end PartialStages
end Cordis.PaperEffectEquations
