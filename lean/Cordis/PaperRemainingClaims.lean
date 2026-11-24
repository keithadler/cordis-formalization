import Cordis.PaperLifecycleClaims
import Cordis.OrchestrationSorting
import Cordis.Renaming
import Cordis.ObservationLifting

/-! Cordis v1, pp. 25 and 38–55. Propositions for the remaining metatheory.
The original claims use the admitted context and its frozen maps. No claim
below is assumed as an axiom, even where the paper's proof uses it later. -/
namespace Cordis.PaperRemainingClaims
open Calculus Stages PaperLifecycleClaims PaperTraceEquations
universe u

section ObservedRecovery
open Tracking PaperObservationEquations ObservationLifting
variable {Γ : Type u} [Setoid Γ]

def ObservedPairwiseRecovery : List (Twisted Γ) → Γ → Prop
  | [], _ => True
  | (forward, inverse) :: rest, γ => inverse (forward γ) ≈ γ ∧ ObservedPairwiseRecovery rest (forward γ)

/-- Lemma 38, p. 25. The explicit state-recovery claims of Section 3.1,
with the original accumulator quantifiers in Eqs. (10), (11), and (16).
Section 3.1's exact algebraic identities are covered by `PaperEffectEquations`.
The blanket claim already fails on `lemma38RecoveryTarget`. -/
def lemma38 : Prop :=
  (∀ (pair : Twisted Γ) (c : Context Γ), pair.2 (pair.1 c.1) ≈ c.1 →
    ContextRelated (recover (track pair c)) (recover c)) ∧
  (∀ (pairs : List (Twisted Γ)) (c : Context Γ), ObservedPairwiseRecovery pairs c.1 →
    ContextRelated (recover (pairs.foldl (fun current pair => track pair current) c)) (recover c)) ∧
  (∀ (effect : Effects.Effect Γ), EffectWitness effect → ∀ c : Context Γ,
    (inverse (lift effect) c (forward (lift effect) c)).1 ≈ c.1 ∧
    (inverse (lift effect) c (forward (lift effect) c)).2 = c.2 ∘ inverse effect c.1 ∘ forward effect) ∧
  lemma38RecoveryTarget (Γ := Γ) ∧ lemma38ReachableAccumulator (Γ := Γ) ∧
  (∀ history : History Γ, history.observedValid →
    let applied := history.applicationStates
    let reverted := runMaps history.capturedReverts (history.state, history.accumulator)
    ListRelated (fun a b : Context Γ => a.1 ≈ b.1) reverted applied.reverse ∧
      ∀ c ∈ applied ++ reverted, (recover c).1 ≈ history.start)

end ObservedRecovery

variable {Name Key Value Code Error : Type u} [DecidableEq Name] [DecidableEq Key]
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
local notation "Program" => Code → Instruction Name Key Value Code Error
local notation "Semantics" => PaperStateObservation.Semantics Name Key Value Code Error

def tablesAtInterface (state : R) (actor : Name) (declared : Key → Bool) : Name → Key → Option Value :=
  fun owner key => if owner = actor ∨ declared key = true then StageRecovery.tableAt state owner key else none

/-- Definition 55. The read test forgets all but the actor's table and every
other table restricted to the actor's requirements. The write clause compares
all fields and allows only the indicated table changes. -/
def Confined [Setoid Value] (sem : Semantics) (actor : Name) (change : sem.Gamma → sem.Gamma) : Prop :=
  (∀ input (own : F), input.val actor = some own →
    ∀ owner, (change input).val owner = none ↔ input.val owner = none) ∧
  (∀ input (own before after : F) owner, input.val actor = some own →
    input.val owner = some before → (change input).val owner = some after →
    {after with table := before.table} = before ∧
      (owner ≠ actor → ∀ key, own.component.requires key = false → after.table key = before.table key)) ∧
  (∀ left right (own : F), left.val actor = some own →
    tablesAtInterface left.val actor own.component.requires = tablesAtInterface right.val actor own.component.requires →
    tablesAtInterface (change left).val actor own.component.requires =
      tablesAtInterface (change right).val actor own.component.requires)

/-- Definition 52's exceptional frame where O-Insert is enabled. The
undefined-input extension is part of the supplied total interpretation. -/
def BirthFrame [Setoid Value] (sem : Semantics) (actor : Name)
    (head : Iterators.Iterator sem.Gamma) (component : Component Key Code) : Prop :=
  ∀ input, (∃ child, Insertable input.val child component (some actor)) → ∃ child,
    Insertable input.val child component (some actor) ∧
    (Tracking.forward head.effect input).val = put input.val child (fresh component (some actor)) ∧
    ∀ probe, (Tracking.inverse head.effect input probe).val = Calculus.retire probe.val child

/-- Lemma 57, pp. 38–39. Membership in the mediated grammar is the premise.
The global witness at d ∪ p and confinement of every head and its yielded
inverse are conclusions. `birthComponent` supplies the names of the
components in represented Definition 52 heads. -/
def lemma57 [Setoid Value] (program : Program) (sem : Semantics) (actor : Name)
    (birthComponent : Iterators.Iterator sem.Gamma → Option (Component Key Code))
    (requires provides : Key → Prop) : Prop :=
  ∀ code, MediatedRegistry.Mediated program requires provides code →
    let root := sem.iterator actor code
    (∀ head, Iterators.Reach root head →
      match birthComponent head with
      | some component => BirthFrame sem actor head component
      | none => Confined sem actor (Tracking.forward head.effect) ∧
        ∀ state, Confined sem actor (Tracking.inverse head.effect state)) ∧
    @Iterators.WitnessedIterator _ (PaperStateObservation.observation sem
      (fun k => requires k ∨ provides k)) root

def isRuleAt {program : Program} {last : Nat} (trace : Trace program last)
    (t : Nat) (rule : Labeled.Rule) (name : Name) : Prop :=
  trace.rule t = rule ∧ trace.actor t = name

/-- Lemma 59, pp. 40–41. The `Use` records the selected computation, since
an iterator or accumulator can happen to denote the identity function. -/
def lemma59 [Setoid Value] {program : Program} {last : Nat} {sem : Semantics}
    (run : FrozenTrace program last sem) : Prop :=
  ∀ t, t < last →
    let before := run.trace.state t
    let after := run.trace.state (t + 1)
    let actor := run.trace.actor t
    RuleEvaluation.TablesUnchanged (run.psi t (run.state t)).val after ∧
    (∀ owner (other acting later : F), before owner = some other → before actor = some acting →
      after owner = some later → owner ≠ actor →
      (other.table ≠ later.table → ∃ key, other.table key ≠ none ∧ acting.component.requires key = true) ∧
      ∀ key, (other.table key = none ↔ later.table key = none) ∧
        (acting.component.requires key = false → other.table key = later.table key)) ∧
    (∀ name, (committedAt before name = none ∧ committedAt after name ≠ none →
        isRuleAt run.trace t .begin name) ∧
      (committedAt before name ≠ none ∧ committedAt after name = none →
        isRuleAt run.trace t .unload name) ∧
      (committedAt before name ≠ none → committedAt after name ≠ none →
        committedAt before name = committedAt after name)) ∧
    (∀ stack, RuleEvaluation.Use.allowed (run.trace.rule t) before actor (.accumulator stack) →
      run.trace.rule t = .unload) ∧
    (∀ name (old new : F), before name = some old → after name = some new →
      (old.phase = .inactive ∧ new.phase ≠ .inactive → isRuleAt run.trace t .begin name) ∧
      (old.phase ≠ .inactive ∧ new.phase = .inactive → isRuleAt run.trace t .unload name)) ∧
    (∀ name (old new : F), before name = some old → after name = some new →
      old.component = new.component ∧ old.parent = new.parent ∧
      (old.retired = true → new.retired = true) ∧
      (old.retired ≠ new.retired → new.retired = true ∧
        (isRuleAt run.trace t .retire name ∨
          (run.trace.rule t = .unload ∧ ∃ source : F, before actor = some source ∧
            Inverse.retire name ∈ source.phase.accumulator))))

/-- The displayed action in Lemma 61 reindexes the registry and changes
parents and committed views. Captured maps and code are preserved verbatim. -/
def literalRename (χ : Renaming.Permutation Name) (registry : R) : R :=
  fun name => (registry (χ.invFun name)).map fun fiber =>
    {fiber with parent := fiber.parent.map χ.toFun, phase :=
      match fiber.phase with
      | .inactive => .inactive
      | .reloading iterator stack view => .reloading iterator stack (Renaming.view χ view)
      | .active stack view => .active stack (Renaming.view χ view)
      | .unloading stack view => .unloading stack (Renaming.view χ view)}

/-- Lemma 61, p. 42. The same program and rule are used after the literal
renaming. A fully nominal action on callbacks would be a different claim. -/
def lemma61 [Setoid Value] (program : Program) (sem : Semantics) : Prop :=
  ∀ χ : Renaming.Permutation Name,
    (∀ γ : sem.Gamma, sem.domain (literalRename χ γ.val) ∧
      (WellFormed.WellFormed γ.val → WellFormed.WellFormed (literalRename χ γ.val))) ∧
    ∀ (γ δ : sem.Gamma) rule name,
      Labeled.Step program rule name γ.val δ.val ↔
        Labeled.Step program rule (χ.toFun name) (literalRename χ γ.val) (literalRename χ δ.val)

def insertionConflict (state : R) (forgotten : Name) (rule : Labeled.Rule) (actor : Name) (after : R) : Prop :=
  rule = .insert ∧ (actor = forgotten ∨
    ∃ old new : F, state forgotten = some old ∧ after actor = some new ∧
      ∃ key, old.component.provides key = true ∧ new.component.provides key = true)

/-- Lemma 62, p. 42. `Removable` states exactly the vestigial-row test.
The printed converse exceptions here are restricted to O-Insert. -/
def lemma62 [Setoid Value] (program : Program) (sem : Semantics) : Prop :=
  ∀ (γ : sem.Gamma) name, Removable γ.val name →
    PaperStateObservation.TablesRelatedAt sem.keyObservation (fun _ => True) γ.val (erase γ.val name) ∧
    ∀ actor rule, actor ≠ name →
      (∀ after, Labeled.Step program rule actor γ.val after → Removable after name ∧
        Labeled.Step program rule actor (erase γ.val name) (erase after name)) ∧
      (∀ after, Labeled.Step program rule actor (erase γ.val name) after →
        ¬ insertionConflict γ.val name rule actor after →
        ∃ original, Labeled.Step program rule actor γ.val original ∧ erase original name = after)

section Sequence
variable [Setoid Value] {program : Code → Instruction Name Key Value Code Error} {last : Nat}
variable {sem : PaperStateObservation.Semantics Name Key Value Code Error}

def DeclaresInto (supply demand : Component Key Code) : Prop :=
  ∃ key, supply.provides key = true ∧ (demand.requires key = true ∨ demand.provides key = true)

/-- Definition 65 adds agreement of the component named by a birth to the
ordinary iterator relation. `IndependentEntries` supplies this interpretation,
including the recursive comparison of named component payloads. -/
def IndependentEntries (birthAgreement : Name → Code → Name → Code → Prop)
    (first : Name) (c : Code) (second : Name) (d : Code) : Prop :=
  @PaperObservationEquations.IndependentObserved _ (PaperStateObservation.base sem)
    (sem.iterator first c) (sem.iterator second d) ∧ birthAgreement first c second d

def ComponentsAdmitted (trace : Trace program last) : Prop :=
  ∀ t, t ≤ last → sem.domain (trace.state t) ∧
    ∀ name fiber, trace.state t name = some fiber → AdmittedComponent program sem name fiber.component

/-- Lemma 66, p. 44. Pairs range over all distinct names ever held,
including children and names that never coexist in a registry. -/
def lemma66 (trace : Trace program last)
    (birthAgreement : Name → Code → Name → Code → Prop)
    (operations : PaperEffectEquations.CoeffectOperations (fun _ : Key => Value))
    (operatesAt : Name → Code → Key → Prop) : Prop :=
  AdmittedCoeffects operations → ComponentsAdmitted (sem := sem) trace →
  ∀ s t, s ≤ last → t ≤ last → ∀ m n (first second : F), m ≠ n →
    trace.state s m = some first → trace.state t n = some second →
    IndependentEntries (sem := sem) birthAgreement m first.component.entry n second.component.entry ∨
      ((DeclaresInto first.component second.component ∨ DeclaresInto second.component first.component) ∧
        ∀ key, operatesAt m first.component.entry key → operatesAt n second.component.entry key →
          PaperObservationEquations.CommutativeKey operations
            (PaperObservationEquations.fullTableObservation operations) key)

def Activates : Labeled.Rule → Prop
  | .begin | .iter | .finish => True
  | _ => False

/-- Lemma 78, pp. 52–53. Activation endpoints are compared by Equation (54),
as specified in the use of this lemma on p. 55. Moving an orchestration
command preserves its exact payload and endpoint. -/
def lemma78 (trace : Trace program last) (birthAgreement : Name → Code → Name → Code → Prop) : Prop :=
  ∀ t, t + 1 < last →
    let before := trace.state t
    let middle := trace.state (t + 1)
    let after := trace.state (t + 2)
    let m := trace.actor t
    let n := trace.actor (t + 1)
    let r := trace.rule t
    let s := trace.rule (t + 1)
    WellFormed.WellFormed before → m ≠ n → Activates r →
    ((Activates s → ∀ first second : F, before m = some first → before n = some second →
      IndependentEntries (sem := sem) birthAgreement m first.component.entry n second.component.entry →
      (∃ target, Labeled.Step program s n before target) →
      ∃ target result, Labeled.Step program s n before target ∧
        Labeled.Step program r m target result ∧ PaperStateObservation.Related sem result after) ∧
    (∀ command : OrchestrationSorting.Command Name Key Code, command.actor = n →
      (match command with | .insert .. => s = .insert | .retire .. => s = .retire | .remove .. => s = .remove) →
      command.Step middle after → ¬ Transposition.CreatesChild program m before middle n →
      ∃ target, command.Step before target ∧ Labeled.Step program r m target after))

/-- The births contributed by a selected actor's steps in an episode. -/
def BornDuring (trace : Trace program last) (parent : Name) (b u : Nat) (child : Name) : Prop :=
  ∃ t, b ≤ t ∧ t ≤ u ∧ t < last ∧ trace.actor t = parent ∧
    Transposition.CreatesChild program parent (trace.state t) (trace.state (t + 1)) child

def Labels {program : Program} {last : Nat} (trace : Trace program last) : List (Labeled.Rule × Name) :=
  (List.range last).map fun t => (trace.rule t, trace.actor t)

/-- Clause (54) outside a set of withdrawn names. The functions and
iterators retain the same Definition 34 comparison inputs. -/
def EquivalentOutside (sem : Semantics) (withdrawn : Name → Prop) (left right : R) : Prop :=
  PaperStateObservation.TablesRelatedAt sem.keyObservation (fun _ => True) left right ∧
    ∀ name, ¬ withdrawn name → Iterators.OptionRel (PaperStateObservation.FiberRelated sem name)
      (left name) (right name)

/-- Definition 76 at every completed activation in this sequence. -/
def TotalProvisions (trace : Trace program last) : Prop :=
  ∀ t, t ≤ last → SupportAtQuiescence.TotalProvision (trace.state t)

def CommandAt (trace : Trace program last) (t : Nat) (command : OrchestrationSorting.Command Name Key Code) : Prop :=
  t < last ∧ trace.actor t = command.actor ∧
    (match command with
      | .insert .. => trace.rule t = .insert
      | .retire .. => trace.rule t = .retire
      | .remove .. => trace.rule t = .remove) ∧
    command.Step (trace.state t) (trace.state (t + 1))

/-- Lemma 79, pp. 53–54, deletes by the literal closed interval [b,u].
That interval retains the opening L-Begin at b-1, and a subject's external
O-Retire inside the interval is deleted. These are features of the printed
deletion, which this proposition deliberately keeps. -/
def lemma79 (trace : Trace program last)
    (operations : PaperEffectEquations.CoeffectOperations (fun _ : Key => Value)) : Prop :=
  AdmittedCoeffects operations → ComponentsAdmitted (sem := sem) trace →
  RootInsertions trace → TotalProvisions trace → Progress.Quiet (trace.state last) →
  ∀ (name : Name) (b u : Nat), Indexed.EpisodeAt (program := program) trace name b u →
    (∀ m b' u', Indexed.EpisodeAt (program := program) trace m b' u' →
      ¬ ∃ t, t ≤ last ∧ precedence (trace.state t) name m) →
    (∀ child, BornDuring trace name b u child →
      ∀ b' u', ¬ Indexed.EpisodePrefix (program := program) trace child b' u') →
    let withdrawn := BornDuring trace name b u
    (∃ (remainingLast : Nat) (remaining : Trace program remainingLast), RootInsertions remaining ∧
      ComponentsAdmitted (sem := sem) remaining ∧
      (∃ retained : List Nat, retained.Pairwise (· < ·) ∧
        (∀ t, t ∈ retained ↔ t < last ∧ ¬ withdrawn (trace.actor t) ∧
          ¬ (b ≤ t ∧ t ≤ u ∧ trace.actor t = name)) ∧
        Labels remaining = retained.map (fun t => (trace.rule t, trace.actor t)) ∧
        (∀ q old, retained[q]? = some old → ∀ command,
          CommandAt remaining q command ↔ CommandAt trace old command)) ∧
      EquivalentOutside sem withdrawn (trace.state last) (remaining.state remainingLast))

end Sequence
end Cordis.PaperRemainingClaims
