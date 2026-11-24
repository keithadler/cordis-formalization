import Cordis.ObservationLiftingExamples

/-! The exact accumulator-domain boundary of Lemma38.

Definition2 gives the unrestricted product Γ × (Γ → Γ). Theorem15 (pp14–15)
fixes an arbitrary member and asserts preservation of its Γ-valued recovery
target in every case. Reading its E* hypothesis by Definition36, as Lemma38
explicitly instructs, makes that unrestricted assertion false. This counterexample
does not weaken a separate premise of Theorem7 or depend on a choice of product
logical relation. All corrected reachable/admissible results remain unchanged.

Respect is exactly the missing condition: a fixed accumulator preserves recovery
targets for every witnessed effect at every state iff it respects the base
equivalence. Necessity is derived using a witnessed map within one equivalence
class, not assumed as a recovery or transition premise.
-/
namespace Cordis.ObservationLifting
open Effects Tracking Iterators
universe u
variable {S : Type u} [Setoid S]

def PreservesRecoveryTargets (accumulator : S → S) : Prop :=
  ∀ (effect : Effect S), Witnessed effect → ∀ state,
    accumulator (inverse effect state (forward effect state)) ≈ accumulator state

theorem respects_iff_preserves_recovery_targets (accumulator : S → S) :
    Respects accumulator ↔ PreservesRecoveryTargets accumulator := by
  constructor
  · intro respects effect witness state
    exact respects (witness.recover state)
  · intro preserves left right observed
    classical
    let effect : Effect S := ⟨fun state => (if state ≈ right then left else state, id)⟩
    have witness : Witnessed effect := by
      constructor
      · intro state
        change (if state ≈ right then left else state) ≈ state
        by_cases member : state ≈ right
        · simpa only [if_pos member] using Setoid.trans observed (Setoid.symm member)
        · simp only [if_neg member]; exact Setoid.refl _
      · intro a b inputs
        refine ⟨?_, fun {_ _} related => related⟩
        change (if a ≈ right then left else a) ≈ (if b ≈ right then left else b)
        by_cases member : a ≈ right
        · have other : b ≈ right := Setoid.trans (Setoid.symm inputs) member
          simp only [if_pos member, if_pos other]
          exact Setoid.refl _
        · have other : ¬ b ≈ right := fun contradiction => member (Setoid.trans inputs contradiction)
          simpa only [if_neg member, if_neg other] using inputs
    have recovered := preserves effect witness right
    change accumulator (if right ≈ right then left else right) ≈ accumulator right at recovered
    simpa only [if_pos (Setoid.refl right)] using recovered

/-- Theorem7's recovery equation for every witnessed pair has precisely the
same necessary and sufficient accumulator condition. The output accumulators
are identity; necessity therefore concerns the Γ-valued target itself. -/
theorem respects_iff_every_recovery_equation (accumulator : S → S) :
    Respects accumulator ↔
      ∀ (effect : Effect S), Witnessed effect → ∀ state,
        ContextRelated
          (recover (track (forward effect, inverse effect state) (state, accumulator)))
          (recover (state, accumulator)) := by
  rw [respects_iff_preserves_recovery_targets]
  constructor
  · intro preserves effect witness state
    exact ⟨preserves effect witness state, fun {_ _} related => related⟩
  · intro equations effect witness state
    exact (equations effect witness state).1

end Cordis.ObservationLifting

namespace Cordis.ObservationLiftingExamples
open Effects Tracking

/-- Directly contradicts the unrestricted Theorem15 recovery-target assertion
under Lemma38's prescribed Definition36 reading. The effect satisfies the full
witness and even the global observational inverse condition. The failure is a
Γ-valued relation, not non-reflexivity of a function/product relation. -/
theorem unrestricted_observed_theorem15_target_fails :
    Witnessed hiddenFlip ∧
    (∀ captured : State, Related (inverse hiddenFlip captured ∘ forward hiddenFlip) id) ∧
    let initial : State := (0, false)
    ¬ (badAccumulator (inverse hiddenFlip initial (forward hiddenFlip initial)) ≈
      badAccumulator initial) := by
  refine ⟨hiddenFlip_witnessed, ?_, ?_⟩
  · intro captured x y related
    exact related
  · dsimp only
    intro related
    have impossible : (0 : Nat) = 1 := related
    cases impossible

end Cordis.ObservationLiftingExamples
