import Cordis.PaperEffectEquations
import Cordis.PartialReachMediatedWitness

/-! Cordis v1, pp. 23–30. Equations (33)–(41) and associated claims.
Observation laws are propositions, including claims whose printed wording
admits more than one reading. -/
namespace Cordis.PaperObservationEquations

universe u
open Effects (Effect)
open Iterators (Iterator OptionRel Reach Generator Generated Closure embed)
open PaperEffectEquations (CoeffectOperations ContextMediated iterate)
open PartialCoeffectLifting (Table PartialMap liftOperation)
open PartialInverseObservation (MapRelated)

section Tests
variable {K : Type u} {V : K → Type u}
variable (operations : CoeffectOperations V) (k : K)

/-- Definition 31, p. 23. A fixed word selects a forward application or a
concrete inverse previously yielded by some application at this key. The
paper does not give a capture/probe grammar for comparing different inverses
yielded by two executions. This is the fixed-letter reading. -/
def Yielded (g : PartialMap (V k)) : Prop :=
  ∃ a x v w b, (operations.operation k a x).run v = some (w, g, b)

inductive Letter where
  | forward (a : operations.Name k) (x : operations.Argument k a)
  | inverse (g : PartialMap (V k)) (yielded : Yielded operations k g)

abbrev Outcome := (a : operations.Name k) × operations.Outcome k a

def testStep : Coeffects.TestAlphabet (V k) (Letter operations k) (Option (Outcome operations k))
  | .forward a x, v => do
    let (w, _, b) ← (operations.operation k a x).run v
    pure (w, some ⟨a, b⟩)
  | .inverse g _, v => (g v).map (fun w => (w, none))

/-- Eq. (33), Definition 31, p. 23. The test word determines the positions
of its forward letters. Empty inverse observations at the other positions
carry no outcome. `runTest` compares the definedness of the whole word. -/
abbrev KeyEquivalent : V k → V k → Prop := Coeffects.Indistinguishable (testStep operations k)

/-- Definition 31's respect clause compares the two inverses selected by
related executions, including both inverses' domains at related probes. -/
def OperationRespects (relation : V k → V k → Prop) : Prop :=
  ∀ a x v w, relation v w →
    OptionRel (fun l r => relation l.1 r.1 ∧ MapRelated relation l.2.1 r.2.1 ∧ l.2.2 = r.2.2)
      ((operations.operation k a x).run v) ((operations.operation k a x).run w)

/-- Lemma 32, p. 23. Under the fixed-letter reading, preservation by each
individual inverse and the full cross-input respect clause are distinct. -/
def lemma32 : Prop :=
  Equivalence (KeyEquivalent operations k) ∧ OperationRespects operations k (KeyEquivalent operations k) ∧
    ∀ relation : V k → V k → Prop, Equivalence relation → OperationRespects operations k relation →
      ∀ v w, relation v w → KeyEquivalent operations k v w

/-- Eq. (34), Definition 33, p. 24. Option matching equates the domains
restricted to S. Common bindings are compared by Eq. (33). -/
abbrev TableEquivalent (S : K → Prop) : Table V → Table V → Prop :=
  PartialCoeffectLifting.TableRelated (KeyEquivalent operations) S

end Tests

section LogicalRelation
variable {Γ X Y : Type u}

/-- Eq. (35), Definition 34, p. 24. The function clause compares at every
pair of related inputs. The base clause for any other base type is `Eq`. -/
def FunctionRelated (input : X → X → Prop) (output : Y → Y → Prop) (f g : X → Y) : Prop :=
  ∀ x y, input x y → output (f x) (g y)

def ProductRelated (left : X → X → Prop) (right : Y → Y → Prop) (a b : X × Y) : Prop :=
  left a.1 b.1 ∧ right a.2 b.2

variable [Setoid Γ]

/-- Eq. (35) on iterators is the greatest relation satisfying the recursive
unfolding. The state setoid supplies the fixed base from Eq. (34). -/
abbrev IteratorRelated : Iterator Γ → Iterator Γ → Prop := Iterators.RelatedIterator

/-- Lemma 35, p. 24. A partial equivalence is symmetric and transitive. -/
def PartialEquivalence {A : Type u} (relation : A → A → Prop) : Prop :=
  (∀ x y, relation x y → relation y x) ∧
    (∀ x y z, relation x y → relation y z → relation x z)

def lemma35 (input : X → X → Prop) (output : Y → Y → Prop) : Prop :=
  (Equivalence input → Equivalence output → PartialEquivalence (FunctionRelated input output)) ∧
    PartialEquivalence (IteratorRelated (Γ := Γ))

/-- Eq. (36), Definition 36, p. 25. The witness retains both self-respect
at distinct related inputs and exact selection of the inverse to check. -/
def EffectWitness (e : Effect Γ) : Prop :=
  FunctionRelated Setoid.r (ProductRelated Setoid.r (FunctionRelated Setoid.r Setoid.r)) e.run e.run ∧
    ∀ γ δ g, (δ, g) = e.run γ → g δ ≈ γ

/-- Lemma 38, p. 25, includes preservation of every Section 3.1 equality.
Theorem 15's recovery-target instance has an unrestricted accumulator in
the printed claim. This proposition records that instance, including its
original quantifiers. The existing counterexample applies to this clause. -/
def lemma38RecoveryTarget : Prop :=
  ∀ (e : Effect Γ), EffectWitness e → ∀ (γ : Γ) (φ : Γ → Γ),
    let (δ, g) := e.run γ
    φ (g δ) ≈ φ γ

/-- Lemma 38's reachable-accumulator clause starts from identity and applies
and reverts witnessed effects. It is independent of the unrestricted claim. -/
def lemma38ReachableAccumulator : Prop :=
  ∀ h : Tracking.History Γ, h.observedValid →
    let applied := h.applicationStates
    let reverted := Tracking.runMaps h.capturedReverts (h.state, h.accumulator)
    ∀ c ∈ applied ++ reverted, FunctionRelated Setoid.r Setoid.r c.2 c.2

end LogicalRelation

section PartialWitness
variable {K : Type u} {V : K → Type u} [DecidableEq K]

/-- Lemma 39, pp. 25–26, at the p. 17 partial-map interpretation of Eq. (32).
The primitive recovery witness is part of Definition 29. The original proof
uses Lemma 32 for respect without an added premise. The partial conclusion
states its recovery witness at exact equality on successful calls. Printed
Eq. (37) has total function types. -/
def lemma39Partial (operations : CoeffectOperations V) : Prop :=
  PaperEffectEquations.ValueOperationWitness operations →
  ∀ (declared provided S : K → Prop) (subset : ∀ k, provided k → declared k)
    (i : PartialIterators.Iterator (Table V)),
    ContextMediated operations declared provided subset i →
    (∀ j, PartialIterators.Reach i j → PartialReachMediatedWitness.HeadLocal operations.stageSignature S j) →
    PartialIterators.Witnessed (TableEquivalent operations S) i

end PartialWitness

section IteratorIndependence
variable {Γ : Type u}

/-- Eq. (39), Definition 42, p. 27. The literal equality uses every pair of
maps in the two generated monoids. -/
def eq39 (i j : Iterator Γ) : Prop :=
  ∀ f, Generated i f → ∀ g, Generated j g → f ∘ g = g ∘ f

/-- Lemma 41, p. 27. Generator commutation extends to the monoids, and the
composition of two effects draws its transformations from their union closure. -/
def lemma41 : Prop :=
  (∀ (e₁ e₂ : Effect Γ),
    (∀ f, Generator (embed e₁) f → ∀ g, Generator (embed e₂) g → f ∘ g = g ∘ f) →
    eq39 (embed e₁) (embed e₂)) ∧
  (∀ (e₁ e₂ : Effect Γ) (f : Γ → Γ), Generated (embed (Tracking.diamond e₁ e₂)) f →
    Closure (fun g => Generated (embed e₁) g ∨ Generated (embed e₂) g) f)

/-- Definition 42 as read in §3.4.2, p. 28. Function equality and the
returned inverse and continuation comparisons use Eq. (35). -/
def IndependentObserved [Setoid Γ] (i j : Iterator Γ) : Prop :=
  (∀ f, Generated i f → ∀ g, Generated j g → FunctionRelated Setoid.r Setoid.r (f ∘ g) (g ∘ f)) ∧
  (∀ a, Reach i a → ∀ g, Generated j g → ∀ γ, Iterators.YieldRelated a (g γ) γ) ∧
  (∀ a, Reach j a → ∀ f, Generated i f → ∀ γ, Iterators.YieldRelated a (f γ) γ)

end IteratorIndependence

section CoeffectCommutativity
variable {K : Type u} {V : K → Type u} [DecidableEq K]
variable (operations : CoeffectOperations V)

/-- Definition 44, p. 28. The generating set contains the lifted forward
and every inverse at every argument of one operation. -/
def OperationMonoid (k : K) (a : operations.Name k) : PartialMap (Table V) → Prop :=
  PartialMapClosure.Generated (fun map => ∃ x,
    PartialCoeffectIndependenceContracts.OperationGenerator (liftOperation k (operations.operation k a x)) map)

/-- Eq. (41), Definition 44, p. 28, under the partial-map reading on p. 17.
For each defined foreign transition, compare the local outcome including its
definedness. Outcome values are compared by equality. -/
def eq41 (k l : K) (a : operations.Name k) (b : operations.Name l) : Prop :=
  ∀ x g, OperationMonoid operations l b g → ∀ σ σ', g σ = some σ' →
    ((liftOperation k (operations.operation k a x)).run σ').map (fun result => result.2.2) =
      ((liftOperation k (operations.operation k a x)).run σ).map (fun result => result.2.2)

/-- Definition 44 also requires independence of the lifted effects at each
argument pair. Stage embedding drops the outcome and uses no continuation.
The partial comparison uses the explicit foreign-success guard for Eq. (40). -/
def IndependentOperations (related : Setoid (Table V)) (k l : K)
    (a : operations.Name k) (b : operations.Name l) : Prop :=
  (∀ x y, PartialObservedIteratorIndependence.Independent related
    (PartialIterators.stage (liftOperation k (operations.operation k a x)) (fun _ => none))
    (PartialIterators.stage (liftOperation l (operations.operation l b y)) (fun _ => none))) ∧
  eq41 operations k l a b ∧ eq41 operations l k b a

/-- Definitions 44 and 46, pp. 28–29. A provider's witness includes every
operation pair, including an operation paired with itself. -/
def CommutativeKey (related : Setoid (Table V)) (k : K) : Prop :=
  ∀ a b : operations.Name k, IndependentOperations operations related k k a b

/-- Equation (33) as a setoid on the value type at one key. -/
def keySetoid (key : K) : Setoid (V key) :=
  ⟨KeyEquivalent operations key, Coeffects.indistinguishable_equivalence (testStep operations key)⟩

/-- The full Eq. (34) observation uses every declared key type. The existing
test equality gives the equivalence on values independently of Lemma 32's
operation-respect claim. -/
def fullTableObservation : Setoid (Table V) :=
  PartialCoeffectIndependenceContracts.tableSetoid
    (keySetoid operations) (fun _ => True)

end CoeffectCommutativity
end Cordis.PaperObservationEquations
