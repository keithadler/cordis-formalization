import Cordis.TypedRegistryTrace
import Cordis.Results.GlobalSupport

/-!
The support clauses and quiescence are read on the typed registry itself.
Their transport to the existing indexed proofs uses only table presence
and the unchanged component, parent, retirement, and lifecycle fields.
-/
namespace Cordis.TypedRegistry

open PaperEffectEquations (CoeffectOperations)
open TypedCoeffectReplay (pack)
universe u
variable {Name Key Code : Type u} {V : Key → Type u}
variable {ops : CoeffectOperations V} [DecidableEq Key]
local notation "R" => Registry Name V Code

/-- Equation (59), with the provider as the first endpoint. -/
def precedes (r : R) (provider consumer : Name) : Prop :=
  ∃ key, (∃ f, r provider = some f ∧ f.component.provides key = true) ∧
    (∃ f, r consumer = some f ∧ f.component.requires key = true)

/-- Declared provider edges consulted between names without installed views. -/
def uninstalledSupportDependencies (r : R) (provider consumer : Name) : Prop :=
  precedes r provider consumer ∧
    (∃ fiber, r consumer = some fiber ∧ fiber.retired = false) ∧
    ¬ (∃ fiber view, r provider = some fiber ∧ fiber.phase.committed = some view) ∧
    ¬ (∃ fiber view, r consumer = some fiber ∧ fiber.phase.committed = some view)

/-- Equation (61), restricted to names in the registry. -/
def supportEdge (r : R) : Name → Name → Prop :=
  PaperTraceEquations.SupportEdge (fun name => (r name).isSome = true) (precedes r)
    (fun name => (r name).bind fun f => f.parent)

/-- Equation (62), a support set on the actual typed registry. -/
def SupportSolution (r : R) (set : Name → Prop) : Prop :=
  ∀ name, set name ↔ ∃ f, r name = some f ∧ f.retired = false ∧
    (f.parent = none ∨ ∃ parent, f.parent = some parent ∧ set parent) ∧
    ∀ key, f.component.requires key = true →
      ∃ provider entry, r provider = some entry ∧ set provider ∧ entry.component.provides key = true

def Active (r : R) (name : Name) : Prop :=
  ∃ f, r name = some f ∧ f.phase.available

def TotalProvision (r : R) : Prop :=
  ∀ name f, r name = some f → f.phase.available →
    ∀ key, f.table key ≠ none ↔ f.component.provides key = true

def Quiet (r : R) : Prop :=
  ∀ name f, r name = some f →
    match f.phase with
    | .inactive => ∀ view, ¬ Target r name view
    | .active _ view => Target r name view
    | _ => False

@[simp] theorem encode_row {r : R} {name : Name} {fiber : Fiber Name V Code}
    (present : r name = some fiber) :
    encodeRegistry ops r name = some (encodeFiber ops fiber) := by
  simp [encodeRegistry, present]

@[simp] theorem encode_tableAt (r : R) (name : Name) (key : Key) :
    StageRecovery.tableAt (encodeRegistry ops r) name key = (tableAt r name key).map (pack key) := by
  cases present : r name <;> simp [StageRecovery.tableAt, tableAt, encodeRegistry, encodeFiber, present]

theorem precedes_encode (r : R) :
    PaperLifecycleClaims.precedence (encodeRegistry ops r) = precedes r := by
  funext provider consumer
  apply propext
  constructor
  · rintro ⟨key, ⟨supply, supplierAt, supplies⟩, ⟨demand, consumerAt, required⟩⟩
    obtain ⟨s, hs, rfl⟩ := encodeRegistry_some ops supplierAt
    obtain ⟨d, hd, rfl⟩ := encodeRegistry_some ops consumerAt
    exact ⟨key, ⟨s, hs, supplies⟩, ⟨d, hd, required⟩⟩
  · rintro ⟨key, ⟨s, hs, supplies⟩, ⟨d, hd, required⟩⟩
    exact ⟨key, ⟨_, encode_row hs, supplies⟩, ⟨_, encode_row hd, required⟩⟩

theorem uninstalledSupportDependencies_encode (r : R) :
    Results.UninstalledSupportDependencies (encodeRegistry ops r) =
      uninstalledSupportDependencies r := by
  have live (name : Name) :
      (∃ fiber, encodeRegistry ops r name = some fiber ∧ fiber.retired = false) ↔
        (∃ fiber, r name = some fiber ∧ fiber.retired = false) := by
    constructor
    · rintro ⟨fiber, found, current⟩
      obtain ⟨row, present, rfl⟩ := encodeRegistry_some ops found
      exact ⟨row, present, current⟩
    · rintro ⟨row, present, current⟩
      exact ⟨_, encode_row present, current⟩
  have installed (name : Name) :
      Results.SupportInstalled (encodeRegistry ops r) name ↔
        (∃ fiber view, r name = some fiber ∧ fiber.phase.committed = some view) := by
    constructor
    · rintro ⟨fiber, view, found, committed⟩
      obtain ⟨row, present, rfl⟩ := encodeRegistry_some ops found
      exact ⟨row, view, present, by simpa only [encodeFiber, encodePhase_committed] using committed⟩
    · rintro ⟨row, view, present, committed⟩
      exact ⟨_, view, encode_row present, by simpa only [encodeFiber, encodePhase_committed] using committed⟩
  funext provider consumer
  apply propext
  have dependency : Progress.Depends (encodeRegistry ops r) consumer provider ↔
      PaperLifecycleClaims.precedence (encodeRegistry ops r) provider consumer := by
    constructor
    · rintro ⟨c, p, key, hc, hp, requires, provides⟩
      exact ⟨key, ⟨p, hp, provides⟩, ⟨c, hc, requires⟩⟩
    · rintro ⟨key, ⟨p, hp, provides⟩, ⟨c, hc, requires⟩⟩
      exact ⟨c, p, key, hc, hp, requires, provides⟩
  simp only [Results.UninstalledSupportDependencies, uninstalledSupportDependencies,
    dependency, precedes_encode, live, installed]

theorem supportEdge_encode (r : R) :
    PaperLifecycleClaims.supportEdge (encodeRegistry ops r) = supportEdge r := by
  unfold PaperLifecycleClaims.supportEdge supportEdge
  rw [precedes_encode]
  have domain : (fun name => (encodeRegistry ops r name).isSome = true) =
      (fun name => (r name).isSome = true) := by
    funext name
    cases present : r name <;> simp [encodeRegistry, present]
  have parents : (fun name => (encodeRegistry ops r name).bind fun f => f.parent) =
      (fun name => (r name).bind fun f => f.parent) := by
    funext name
    cases present : r name <;> simp [encodeRegistry, encodeFiber, present]
  rw [domain, parents]

theorem supportSolution_encode_iff (r : R) (set : Name → Prop) :
    SupportAtQuiescence.Solution (encodeRegistry ops r) set ↔ SupportSolution r set := by
  have membership (name : Name) :
      (∃ f, encodeRegistry ops r name = some f ∧ f.retired = false ∧
        (f.parent = none ∨ ∃ parent, f.parent = some parent ∧ set parent) ∧
        ∀ key, f.component.requires key = true →
          ∃ provider entry, encodeRegistry ops r provider = some entry ∧ set provider ∧
            entry.component.provides key = true) ↔
      (∃ f, r name = some f ∧ f.retired = false ∧
        (f.parent = none ∨ ∃ parent, f.parent = some parent ∧ set parent) ∧
        ∀ key, f.component.requires key = true →
          ∃ provider entry, r provider = some entry ∧ set provider ∧ entry.component.provides key = true) := by
    constructor
    · rintro ⟨raw, found, live, parent, requirements⟩
      obtain ⟨f, earlier, rfl⟩ := encodeRegistry_some ops found
      refine ⟨f, earlier, live, parent, ?_⟩
      intro key required
      obtain ⟨provider, entry, found, supported, provides⟩ := requirements key required
      obtain ⟨typed, present, rfl⟩ := encodeRegistry_some ops found
      exact ⟨provider, typed, present, supported, provides⟩
    · rintro ⟨f, found, live, parent, requirements⟩
      refine ⟨encodeFiber ops f, encode_row found, live, parent, ?_⟩
      intro key required
      obtain ⟨provider, entry, found, supported, provides⟩ := requirements key required
      exact ⟨provider, encodeFiber ops entry, encode_row found, supported, provides⟩
  constructor
  · intro raw name
    exact (raw name).trans (membership name)
  · intro typed name
    exact (typed name).trans (membership name).symm

theorem active_encode (r : R) :
    SupportAtQuiescence.Active (encodeRegistry ops r) = Active r := by
  funext name
  apply propext
  constructor
  · rintro ⟨f, found, active⟩
    obtain ⟨typed, present, rfl⟩ := encodeRegistry_some ops found
    exact ⟨typed, present, (encodePhase_available ops typed.phase).mp active⟩
  · rintro ⟨f, present, active⟩
    exact ⟨_, encode_row present, (encodePhase_available ops f.phase).mpr active⟩

theorem quiet_encode_iff (r : R) : Progress.Quiet (encodeRegistry ops r) ↔ Quiet r := by
  constructor
  · intro h name f present
    have raw := h name (encodeFiber ops f) (encode_row present)
    cases phase : f.phase <;> simp [encodeFiber, encodePhase, phase] at raw ⊢ <;> exact raw
  · intro h name raw present
    obtain ⟨f, found, rfl⟩ := encodeRegistry_some ops present
    have typed := h name f found
    cases phase : f.phase <;> simp [encodeFiber, encodePhase, phase] at typed ⊢ <;> exact typed

theorem totalProvision_encode_iff (r : R) :
    SupportAtQuiescence.TotalProvision (encodeRegistry ops r) ↔ TotalProvision r := by
  constructor
  · intro raw name f present active key
    simpa [encodeFiber] using
      raw name (encodeFiber ops f) (encode_row present) ((encodePhase_available ops f.phase).mpr active) key
  · intro typed name f present active key
    obtain ⟨fiber, found, rfl⟩ := encodeRegistry_some ops present
    simpa [encodeFiber] using typed name fiber found ((encodePhase_available ops fiber.phase).mp active) key

variable [DecidableEq Name]

/-- External insertions have root provenance. Instantiation retains the
actual parent of the typed actor. -/
def Trace.RootInsertions {program : Code → Instruction Name ops Code} {last : Nat}
    (trace : Trace program (fun _ => none) last) : Prop :=
  ∀ t, t < last → trace.rule t = .insert →
    ∃ f, trace.state (t + 1) (trace.actor t) = some f ∧ f.parent = none

theorem Trace.encode_roots {program : Code → Instruction Name ops Code} {last : Nat}
    (trace : Trace program (fun _ => none) last) (roots : trace.RootInsertions) :
    PaperLifecycleClaims.RootInsertions trace.encode := by
  intro t bounded label
  obtain ⟨f, present, parent⟩ := roots t bounded label
  exact ⟨encodeFiber ops f, encode_row present, parent⟩

/-- The unique-solution conjunct of Lemma 75 on a heterogeneous registry. -/
theorem lemma75_typed_unique {program : Code → Instruction Name ops Code} {last : Nat}
    (trace : Trace program (fun _ => none) last) (roots : trace.RootInsertions)
    (acyclic : FiniteOrder.Acyclic (precedes (trace.state last))) :
    ∃ set, SupportSolution (trace.state last) set ∧
      ∀ other, SupportSolution (trace.state last) other → other = set := by
  have run := Results.rootTrace trace.encode (trace.encode_roots roots) last (Nat.le_refl _)
  have rawAcyclic : FiniteOrder.Acyclic (PaperLifecycleClaims.precedence (trace.encode.state last)) := by
    simpa only [Trace.encode, precedes_encode] using acyclic
  obtain ⟨set, solved, unique⟩ := Results.lemma75_unique_support (encodeProgram program) run
    (Results.depends_acyclic _ rawAcyclic)
  exact ⟨set, (supportSolution_encode_iff _ _).mp solved,
    fun other solution => unique other ((supportSolution_encode_iff _ _).mpr solution)⟩

theorem lemma75_typed_unique_of_uninstalled {program : Code → Instruction Name ops Code} {last : Nat}
    (trace : Trace program (fun _ => none) last) (roots : trace.RootInsertions)
    (acyclic : FiniteOrder.Acyclic (uninstalledSupportDependencies (trace.state last))) :
    ∃ set, SupportSolution (trace.state last) set ∧
      ∀ other, SupportSolution (trace.state last) other → other = set := by
  have run := Results.rootTrace trace.encode (trace.encode_roots roots) last (Nat.le_refl _)
  have rawAcyclic : FiniteOrder.Acyclic (Results.UninstalledSupportDependencies (trace.encode.state last)) := by
    simpa only [Trace.encode, uninstalledSupportDependencies_encode] using acyclic
  obtain ⟨set, solved, unique⟩ := Results.lemma75_unique_support_of_uninstalled (encodeProgram program) run rawAcyclic
  exact ⟨set, (supportSolution_encode_iff _ _).mp solved,
    fun other solution => unique other ((supportSolution_encode_iff _ _).mpr solution)⟩

/-- Equation (61) is well founded in the heterogeneous calculus under the
empty-table condition derived by the global provision interpretation. -/
theorem lemma75_typed_of_empty_tables {program : Code → Instruction Name ops Code} {last : Nat}
    (trace : Trace program (fun _ => none) last) (roots : trace.RootInsertions)
    (empty : ∀ t, t ≤ last → ∀ name key, tableAt (trace.state t) name key = none)
    (acyclic : FiniteOrder.Acyclic (precedes (trace.state last))) :
    WellFounded (supportEdge (trace.state last)) ∧
      ∃ set, SupportSolution (trace.state last) set ∧
        ∀ other, SupportSolution (trace.state last) other → other = set := by
  have noBinding : ∀ t, t ≤ last → Results.EmptyTables (trace.encode.state t) := by
    intro t bounded name key
    change StageRecovery.tableAt (encodeRegistry ops (trace.state t)) name key = none
    simp [empty t bounded name key]
  have rawAcyclic : FiniteOrder.Acyclic (PaperLifecycleClaims.precedence (trace.encode.state last)) := by
    simpa only [Trace.encode, precedes_encode] using acyclic
  have wf := (Results.lemma75_of_empty_tables trace.encode (trace.encode_roots roots) noBinding rawAcyclic).1
  refine ⟨?_, lemma75_typed_unique trace roots acyclic⟩
  simpa only [Trace.encode, supportEdge_encode] using wf

/-- Lemma 77 for the typed registry. Total provision checks the presence of a
value of the declared type at each key. -/
theorem lemma77_typed {program : Code → Instruction Name ops Code} {last : Nat}
    (trace : Trace program (fun _ => none) last) (roots : trace.RootInsertions)
    (acyclic : FiniteOrder.Acyclic (precedes (trace.state last)))
    (quiet : Quiet (trace.state last)) (total : TotalProvision (trace.state last)) :
    SupportSolution (trace.state last) (Active (trace.state last)) ∧
      ∀ support, SupportSolution (trace.state last) support → support = Active (trace.state last) := by
  have run := Results.rootTrace trace.encode (trace.encode_roots roots) last (Nat.le_refl _)
  have rawAcyclic : FiniteOrder.Acyclic (PaperLifecycleClaims.precedence (trace.encode.state last)) := by
    simpa only [Trace.encode, precedes_encode] using acyclic
  obtain ⟨solution, unique⟩ := Results.lemma77 (encodeProgram program) run
    (Results.depends_acyclic _ rawAcyclic) ((quiet_encode_iff _).mpr quiet) ((totalProvision_encode_iff _).mpr total)
  have activeMeaning : SupportAtQuiescence.Active (trace.encode.state last) = Active (trace.state last) :=
    active_encode _
  rw [activeMeaning] at solution unique
  exact ⟨(supportSolution_encode_iff _ _).mp solution,
    fun support solved => unique support ((supportSolution_encode_iff _ _).mpr solved)⟩

theorem lemma77_typed_of_uninstalled {program : Code → Instruction Name ops Code} {last : Nat}
    (trace : Trace program (fun _ => none) last) (roots : trace.RootInsertions)
    (acyclic : FiniteOrder.Acyclic (uninstalledSupportDependencies (trace.state last)))
    (quiet : Quiet (trace.state last)) (total : TotalProvision (trace.state last)) :
    SupportSolution (trace.state last) (Active (trace.state last)) ∧
      ∀ support, SupportSolution (trace.state last) support → support = Active (trace.state last) := by
  have run := Results.rootTrace trace.encode (trace.encode_roots roots) last (Nat.le_refl _)
  have rawAcyclic : FiniteOrder.Acyclic (Results.UninstalledSupportDependencies (trace.encode.state last)) := by
    simpa only [Trace.encode, uninstalledSupportDependencies_encode] using acyclic
  obtain ⟨solution, unique⟩ := Results.lemma77_of_uninstalled (encodeProgram program) run
    rawAcyclic ((quiet_encode_iff _).mpr quiet) ((totalProvision_encode_iff _).mpr total)
  have activeMeaning : SupportAtQuiescence.Active (trace.encode.state last) = Active (trace.state last) :=
    active_encode _
  rw [activeMeaning] at solution unique
  exact ⟨(supportSolution_encode_iff _ _).mp solution,
    fun support solved => unique support ((supportSolution_encode_iff _ _).mpr solved)⟩

end Cordis.TypedRegistry
