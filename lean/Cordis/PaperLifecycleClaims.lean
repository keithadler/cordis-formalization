import Cordis.PaperCoeffectEquations
import Cordis.Iterators
import Cordis.IndexedTrace
import Cordis.SupportUniqueness
import Cordis.PaperTraceEquations
import Cordis.MediatedRegistryDomain
import Cordis.Independence
import Cordis.Coeffects
import Cordis.GuardedApplications
import Cordis.TranspositionActivation
import Cordis.StageSimulation
import Cordis.EntangledApplications
import Cordis.OrderingIntervals
import Cordis.ResolutionIntervals
import Cordis.Progress
import Cordis.MediatedRegistryFrames
import Cordis.PaperObservationEquations

/-! Lemmas 60, 67, 75 and 77, pp. 41–52. Each statement uses the nine-rule
trace. The frozen maps of Definition 58 have an explicit interpretation. -/
namespace Cordis.PaperLifecycleClaims
open Calculus Stages PaperTraceEquations
universe u

variable {Name Key Value Code Error : Type u} [DecidableEq Name] [DecidableEq Key]
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
local notation "Program" => Code → Instruction Name Key Value Code Error

/-- Definition 58's empty-origin indexed sequence. -/
abbrev Trace (program : Program) (last : Nat) :=
  Indexed.Trace program (fun _ => none : R) last

/-- Definition 74, p. 51, fixes root provenance for external insertions.
The instantiation primitive supplies a parent inside a lifecycle step. -/
def RootInsertions {program : Program} {last : Nat} (trace : Trace program last) : Prop :=
  ∀ t, t < last → trace.rule t = .insert →
    ∃ fiber, trace.state (t + 1) (trace.actor t) = some fiber ∧ fiber.parent = none

/-- The admitted interpretation of Definition 58's total frozen maps uses
one representation of all states in the trace. Its all-input map meanings
and the all-key value observations are semantic parameters. Local agreement
asserts the actual selected application and control edit of each rule. -/
structure FrozenTrace (program : Program) (last : Nat) [Setoid Value]
    (sem : PaperStateObservation.Semantics Name Key Value Code Error) where
  trace : Trace program last
  state : Nat → sem.Gamma
  represented : ∀ t, t ≤ last → (state t).val = trace.state t
  psi : Nat → sem.Gamma → sem.Gamma
  edit : Nat → sem.Gamma → sem.Gamma
  applied : ∀ t, t < last → ∃ use : RuleEvaluation.Use Name Key Value Code,
    RuleEvaluation.Application program (trace.actor t) use (trace.state t) (psi t (state t)).val ∧
    RuleEvaluation.Use.allowed (trace.rule t) (trace.state t) (trace.actor t) use ∧
    (∀ entry, use = .iteration entry → psi t = Tracking.forward (sem.iterator (trace.actor t) entry).effect) ∧
    (∀ inverses, use = .accumulator inverses → psi t = PaperStateObservation.accumulator sem inverses) ∧
    (use = .identity → psi t = id)
  edited : ∀ t, t < last → ∃ update : RuleEvaluation.Edit Name Key Value Code,
    RuleEvaluation.Edit.allowed (trace.rule t) (trace.actor t) update ∧
    update.valid (psi t (state t)).val ∧
    ∀ input, (edit t input).val = update.apply input.val
  factored : ∀ t, t < last → Factors state psi edit t

section Recovery
variable [Setoid Value]
variable {program : Code → Instruction Name Key Value Code Error} {last : Nat}
variable {sem : PaperStateObservation.Semantics Name Key Value Code Error}

def retainedTables (a b : sem.Gamma) : Prop :=
  (PaperStateObservation.base sem).r a b

def accumulatorAt (sem : PaperStateObservation.Semantics Name Key Value Code Error)
    (state : Nat → sem.Gamma) (name : Name) (t : Nat) : sem.Gamma → sem.Gamma :=
  match (state t).val name with
  | none => id
  | some fiber => PaperStateObservation.accumulator sem fiber.phase.accumulator

def provisionOverlap (r : R) (provider consumer : Name) : Prop :=
  ∃ supply demand : F, r provider = some supply ∧ r consumer = some demand ∧
    ∃ key, supply.component.provides key = true ∧
      (demand.component.requires key = true ∨ demand.component.provides key = true)

/-- Lemma 67, p. 45. The pinned provider case and its reloading counterpart
have the identity state map. For the other direction the two compositions
are compared on the actual input. Their meaning on missing bindings is the
particular total interpretation supplied by the frozen trace. -/
def lemma67 (run : FrozenTrace program last sem) : Prop :=
  ∀ (name : Name) (b t : Nat), Indexed.EpisodePrefix (program := program) run.trace name b t →
    t < last → (run.trace.actor t) ≠ name →
    let provider := provisionOverlap (run.trace.state t) (run.trace.actor t) name
    let consumer := provisionOverlap (run.trace.state t) name (run.trace.actor t)
    (provider ∨ consumer) →
    (provider → run.psi t = id) ∧
    (¬ provider →
      let undo := accumulatorAt sem run.state name t
      retainedTables (sem := sem) (undo (run.psi t (run.state t))) (run.psi t (undo (run.state t)))) ∧
    (ResolutionIntervals.Reloading (run.trace.state t) name → run.psi t = id)

end Recovery

/-- Lemma 60, pp. 41–42. Literal Eq. (54) observations are used at both
ends and the acting name and rule label stay fixed. Both directions of
applicability and successor matching are stated, without asserting them. -/
def lemma60 [Setoid Value] (program : Program)
    (sem : PaperStateObservation.Semantics Name Key Value Code Error) : Prop :=
  ∀ (γ δ : sem.Gamma) (rule : Labeled.Rule) (name : Name), StateEquivalent sem γ δ →
    (∀ γ' : sem.Gamma, Labeled.Step program rule name γ.val γ'.val →
      ∃ δ' : sem.Gamma, Labeled.Step program rule name δ.val δ'.val ∧ StateEquivalent sem γ' δ') ∧
    (∀ δ' : sem.Gamma, Labeled.Step program rule name δ.val δ'.val →
      ∃ γ' : sem.Gamma, Labeled.Step program rule name γ.val γ'.val ∧ StateEquivalent sem γ' δ')

section Ordering
variable {program : Code → Instruction Name Key Value Code Error} {last : Nat}

def committedAt (r : R) (name : Name) : Option (TargetView.PartialView Name Key) := do
  let fiber ← r name
  let view ← fiber.phase.committed
  pure (TargetView.mask fiber.component.requires view)

variable [Setoid Value]

end Ordering

section ProgressAndSupport

/-- Definitions 48 and 56 on the ordinary representation. The supplied
iterator is the component's denotation in the chosen Γ. Its relationship
to source and the choice of Γ are separate interpretation obligations. -/
def AdmittedComponent [Setoid Value] (program : Program)
    (sem : PaperStateObservation.Semantics Name Key Value Code Error) (name : Name)
    (component : Component Key Code) : Prop :=
  MediatedRegistry.Mediated program
    (fun key => component.requires key = true) (fun key => component.provides key = true) component.entry ∧
  @Iterators.WitnessedIterator _ (PaperStateObservation.observation sem
    (fun key => component.requires key = true ∨ component.provides key = true))
    (sem.iterator name component.entry) ∧
  (∀ code, Iterators.Reach (sem.iterator name component.entry) (sem.iterator name code) →
    ∀ next before after inverse, Land program name code before after inverse (some next) →
      ∃ state, (sem.iterator name code).next state = some (sem.iterator name next))

/-- Definition 46 supplies commutativity at every key. For this homogeneous
registry interpretation each key's value type is Value. -/
def AdmittedCoeffects [Setoid Value]
    (operations : PaperEffectEquations.CoeffectOperations (fun _ : Key => Value)) : Prop :=
  PaperEffectEquations.ValueOperationWitness operations ∧
    ∀ key, PaperObservationEquations.CommutativeKey operations
      (PaperObservationEquations.fullTableObservation operations) key

def precedence (r : R) : Name → Name → Prop :=
  Precedes (fun name key => ∃ f : F, r name = some f ∧ f.component.provides key = true)
    (fun name key => ∃ f : F, r name = some f ∧ f.component.requires key = true)

/-- Definition 74's combined support relation at an actual registry. -/
def supportEdge (r : R) : Name → Name → Prop :=
  SupportEdge (fun name => (r name).isSome = true) (precedence r)
    (fun name => (r name).bind (fun fiber => fiber.parent))

/-- Lemma 75, pp. 51–52. Root-only external insertion and component/coeffect
admission are inherited. Well-foundedness and uniqueness are conclusions. -/
def lemma75 [Setoid Value] (program : Program)
    (sem : PaperStateObservation.Semantics Name Key Value Code Error)
    (operations : PaperEffectEquations.CoeffectOperations (fun _ : Key => Value)) : Prop :=
  AdmittedCoeffects operations → ∀ last (trace : Trace program last), RootInsertions trace →
    (∀ t, t ≤ last → ∀ name fiber, trace.state t name = some fiber →
      AdmittedComponent program sem name fiber.component) →
    FiniteOrder.Acyclic (precedence (trace.state last)) →
    WellFounded (supportEdge (trace.state last)) ∧
      ∃ support, SupportSolution (trace.state last) support ∧
        ∀ other, SupportSolution (trace.state last) other → other = support

/-- Lemma 77, p. 52. Definition 76's totality is read through its stated
active-table consequence. Endpoint equality does not require a proof of the
full support relation's well-foundedness as a premise. -/
def lemma77 [Setoid Value] (program : Program)
    (sem : PaperStateObservation.Semantics Name Key Value Code Error)
    (operations : PaperEffectEquations.CoeffectOperations (fun _ : Key => Value)) : Prop :=
  AdmittedCoeffects operations → ∀ last (trace : Trace program last), RootInsertions trace →
    (∀ t, t ≤ last → ∀ name fiber, trace.state t name = some fiber →
      AdmittedComponent program sem name fiber.component) →
    FiniteOrder.Acyclic (precedence (trace.state last)) → Progress.Quiet (trace.state last) →
    SupportAtQuiescence.TotalProvision (trace.state last) →
    SupportSolution (trace.state last) (SupportAtQuiescence.Active (trace.state last)) ∧
      ∀ support, SupportSolution (trace.state last) support → SupportEquality (trace.state last) support

end ProgressAndSupport
end Cordis.PaperLifecycleClaims
