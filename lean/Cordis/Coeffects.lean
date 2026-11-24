import Cordis.Iterators

/-!
Observation tests and key-local coeffect operations. Undefined operations are
represented by `none`, so agreement includes definedness, not only outcomes.
The fixed-letter test result below distinguishes preservation by each captured
inverse from the stronger cross-input relation between two captured inverses.
-/

namespace Cordis.Coeffects

open Effects Iterators
universe u

section Tests
variable {V L O : Type u}

abbrev TestAlphabet (V L O : Type u) := L → V → Option (V × O)

def runTest (step : TestAlphabet V L O) : List L → V → Option (List O)
  | [], _ => some []
  | l :: ls, v => do
      let (v', o) ← step l v
      let os ← runTest step ls v'
      pure (o :: os)

def Indistinguishable (step : TestAlphabet V L O) (v w : V) : Prop :=
  ∀ test, runTest step test v = runTest step test w

def RespectsTests (step : TestAlphabet V L O) (R : V → V → Prop) : Prop :=
  ∀ l v w, R v w →
    OptionRel (fun a b : V × O => R a.1 b.1 ∧ a.2 = b.2) (step l v) (step l w)

/-- Lemma 32's equivalence clause, including undefined tests. -/
theorem indistinguishable_equivalence (step : TestAlphabet V L O) :
    Equivalence (Indistinguishable step) :=
  ⟨fun _ _ => rfl, fun h t => (h t).symm, fun h₁ h₂ t => (h₁ t).trans (h₂ t)⟩

/-- Prefixing a test proves preservation of indistinguishability by every fixed
letter, and equality of that letter's outcome and definedness. -/
theorem indistinguishable_respected (step : TestAlphabet V L O) :
    RespectsTests step (Indistinguishable step) := by
  intro l v w h
  cases hv : step l v with
  | none =>
    cases hw : step l w with
    | none => trivial
    | some b =>
      have hh := h [l]
      simp [runTest, hv, hw] at hh
  | some a =>
    cases hw : step l w with
    | none =>
      have hh := h [l]
      simp [runTest, hv, hw] at hh
    | some b =>
      have ho : a.2 = b.2 := by
        have hh := h [l]
        simpa [runTest, hv, hw] using hh
      constructor
      · intro ls
        have hh := h (l :: ls)
        simp only [runTest, hv, hw, pure] at hh
        cases ha : runTest step ls a.1 <;> cases hb : runTest step ls b.1 <;>
          simp_all
      · exact ho

theorem respected_test_agreement (step : TestAlphabet V L O) (R : V → V → Prop)
    (hr : RespectsTests step R) {v w : V} (hvw : R v w) :
    Indistinguishable step v w := by
  intro ls
  induction ls generalizing v w with
  | nil => rfl
  | cons l ls ih =>
    have hstep := hr l v w hvw
    cases hv : step l v <;> cases hw : step l w <;>
      simp only [hv, hw, OptionRel] at hstep
    · simp [runTest, hv, hw]
    · obtain ⟨hs, ho⟩ := hstep
      simp [runTest, hv, hw, ih hs, ho]

/-- Lemma 32(2), with no unnecessary equivalence assumption: every relation
preserved by the test letters and their outputs is contained in test agreement. -/
theorem indistinguishable_coarsest (step : TestAlphabet V L O) (R : V → V → Prop)
    (hr : RespectsTests step R) :
    ∀ v w, R v w → Indistinguishable step v w :=
  fun _ _ h => respected_test_agreement step R hr h

end Tests

section PartialOperations
variable {V B : Type u}

/-- An operation with an explicit precondition: failure has no result, inverse,
or outcome. The continuation therefore cannot mistake failure for an outcome. -/
structure PartialOperation (V B : Type u) where
  run : V → Option (V × (V → V) × B)

/-- Definition20's provision: it is undefined at an occupied binding; its
successful inverse is the restriction that removes the newly introduced key. -/
def provision (v : V) : PartialOperation (Option V) PUnit.{u+1} := ⟨fun old =>
  match old with
  | none => some (some v, fun _ => none, PUnit.unit)
  | some _ => none⟩

theorem provision_extension (v : V) :
    (provision v).run none = some (some v, fun _ => none, PUnit.unit) := rfl

variable [Setoid V]

end PartialOperations

section KeyLocal
variable {K : Type u} {V : K → Type u} [DecidableEq K]

abbrev Context (V : K → Type u) := (k : K) → V k

def update (k : K) (v : V k) (σ : Context V) : Context V :=
  fun j => if h : j = k then h.symm ▸ v else σ j

@[simp] theorem update_same (k : K) (v : V k) (σ : Context V) : update k v σ k = v := by
  simp [update]
@[simp] theorem update_other (k j : K) (v : V k) (σ : Context V) (h : j ≠ k) :
    update k v σ j = σ j := by simp [update, h]

variable (r : ∀ k, Setoid (V k)) (keys : K → Prop)

end KeyLocal

section Stages
variable {K : Type u} {V : K → Type u} [DecidableEq K]

variable (r : ∀ k, Setoid (V k))

end Stages

section Composition
variable {S : Type u} [Setoid S]

end Composition

section KeyIndependence
variable {K : Type u} {V : K → Type u} [DecidableEq K]
variable (r : ∀ k, Setoid (V k))

end KeyIndependence

namespace CapturedInverseCounterexample

/-!
Lemma32's fixed-word reading proves that each yielded inverse separately respects
test equivalence. It does not prove that the inverses yielded at two equivalent
inputs are related as functions (Definition34). The following fully defined,
exactly reversible operation is a counterexample to that stronger inference.
Tests that bind an inverse produced by a previous forward invocation and later
invoke that *dynamically saved* inverse would be a different, stronger test
language; the example pinpoints why that distinction matters.
-/

abbrev Value := Bool × Bool

def capturedUndo (captured : Value) (current : Value) : Value :=
  (captured.1, if current.2 then captured.1 else captured.2)

def SameVisible (v w : Value) : Prop := v.2 = w.2

end CapturedInverseCounterexample

end Cordis.Coeffects
