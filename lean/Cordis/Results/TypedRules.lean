import Cordis.Results.Rules
import Cordis.TypedRegistryTrace
import Cordis.TypedReplayContracts
import Cordis.TypedStateObservation

/-! A typed formulation of Lemma 67. Registry bindings and coeffect
outcomes keep their dependent types. The scalar encoding is used to reuse
the indexed lifecycle invariants and the checked partial replay proof. -/
namespace Cordis.TypedRegistry

open Calculus (Phase View)
open PaperEffectEquations (CoeffectOperations ValueOperationWitness)
open TypedStateObservation (Semantics TablesRelatedAt)
open PartialCoeffectIndependenceContracts (tableSetoid)
universe u
variable {Name Key Code : Type u} {V : Key → Type u} [DecidableEq Name] [DecidableEq Key]
local notation "R" => Registry Name V Code
local notation "F" => Fiber Name V Code
local notation "I" => Inverse Name V

def viewAt (state : R) (name : Name) : Option (View Name Key) :=
  (state name).bind fun fiber => fiber.phase.committed

omit [DecidableEq Name] in
private theorem viewAt_encode (ops : CoeffectOperations V) (state : R) (name : Name) :
    ControlFrame.viewAt (encodeRegistry ops state) name = viewAt state name := by
  cases found : state name with
  | none => simp [encodeRegistry, show state name = none from found, viewAt, ControlFrame.viewAt]
  | some fiber =>
    cases phase : fiber.phase <;> simp [encodeRegistry, encodeFiber, encodePhase, found, phase,
      Phase.committed, viewAt, ControlFrame.viewAt]

omit [DecidableEq Name] in
private theorem accumulator_encode (ops : CoeffectOperations V) (phase : Phase Name Key Code I) :
    (encodePhase ops phase).accumulator = phase.accumulator.map (encodeInverse ops) := by
  cases phase <;> rfl

private theorem transform_on_encoded (ops : CoeffectOperations V) (state : R) (owner : Name)
    (key : Key) (first second : Scalar ops → Scalar ops)
    (agrees : ∀ value : V key,
      first (TypedCoeffectReplay.pack key value) = second (TypedCoeffectReplay.pack key value)) :
    InterleavedRecovery.transform owner key first (encodeRegistry ops state) =
      InterleavedRecovery.transform owner key second (encodeRegistry ops state) := by
  funext name
  by_cases same : name = owner
  · subst name
    cases present : state owner with
    | none => simp [InterleavedRecovery.transform, Stages.undo, Calculus.modify, encodeRegistry, present]
    | some fiber =>
      simp only [InterleavedRecovery.transform, Stages.undo, Calculus.modify, eq_self, if_true, encodeRegistry,
        present, Option.map_some, Option.some.injEq]
      congr 1
      funext selected
      by_cases slot : selected = key
      · subst selected
        cases before : fiber.table key <;> simp [encodeFiber, before, agrees]
      · simp [slot]
  · simp [InterleavedRecovery.transform, Stages.undo, Calculus.modify, same]

private theorem encode_forward_at_key (ops : CoeffectOperations V) (key : Key)
    (operation : ops.Name key) (argument : ops.Argument key operation) (value : V key) :
    InterleavedRecovery.callbackMap (encodeOperation ops key operation argument)
        (TypedCoeffectReplay.pack key value) =
      TypedCoeffectReplay.encodeMap key (PartialCoeffectLifting.forward (ops.operation key operation argument))
        (TypedCoeffectReplay.pack key value) := by
  cases invoked : (ops.operation key operation argument).run value <;>
    simp [InterleavedRecovery.callbackMap, encodeOperation, invoked, PartialCoeffectLifting.forward]

omit [DecidableEq Name] in
private theorem encoded_provision_value {ops : CoeffectOperations V}
    (program : Code → Instruction Name ops Code) (code : Code) (key : Key) (value : Scalar ops)
    (selected : (encodeProgram program code).action = .provide key value) :
    ∃ typed : V key, value = TypedCoeffectReplay.pack key typed := by
  change encodeAction ops (program code).action = .provide key value at selected
  cases action : (program code).action with
  | unit | operate | instantiate => simp [action, encodeAction] at selected
  | provide key' typed =>
    rw [action] at selected
    change Stages.Action.provide key' (TypedCoeffectReplay.pack key' typed) =
      .provide key value at selected
    cases selected
    exact ⟨typed, rfl⟩

/-- A frozen state application from a typed source has a typed meaning at
every counterfactual input. The operation's owner stays the one selected in
the source. At an occupied but undefined input the ordinary map uses an
identity completion, which the partial replay square avoids on its probes. -/
theorem native_frozen_revision {ops : CoeffectOperations V}
    {program : Code → Instruction Name ops Code} (source : R) (actor : Name) (rule : Labeled.Rule)
    {use : RuleEvaluation.Use Name Key (Scalar ops) Code} {middle : RawRegistry Name ops Code}
    {map : RawRegistry Name ops Code → RawRegistry Name ops Code}
    (selected : EntangledApplications.FrozenApplication (encodeProgram program) actor use
      (encodeRegistry ops source) middle map)
    (allowed : use.allowed rule (encodeRegistry ops source) actor) :
    ∃ revision : R → R, ∀ input, encodeRegistry ops (revision input) = map (encodeRegistry ops input) := by
  cases selected with
  | identity => exact ⟨id, fun _ => rfl⟩
  | accumulator word =>
    obtain ⟨_, rawFiber, view, found, phase⟩ := allowed
    obtain ⟨fiber, _, rfl⟩ := Option.map_eq_some_iff.mp found
    have stackEq : fiber.phase.accumulator.map (encodeInverse ops) = word := by
      dsimp only [encodeFiber] at phase
      rw [← accumulator_encode, phase]
      rfl
    refine ⟨TypedRegistry.discharge fiber.phase.accumulator, ?_⟩
    intro input
    rw [encode_discharge, stackEq]
  | iteration landing =>
    cases landing with
    | unit => exact ⟨id, fun _ => rfl⟩
    | provide fiber key value action visible legal vacant =>
      obtain ⟨typed, rfl⟩ := encoded_provision_value program _ key value action
      exact ⟨fun input => TypedRegistry.write input actor key (some typed), fun input => encode_write ops input actor key _⟩
    | instantiate component child action eligible =>
      exact ⟨fun input => TypedRegistry.put input child (TypedRegistry.fresh component (some actor)),
        fun input => by simp only [encode_put, encode_fresh]⟩
    | operate key callback owner before after inverse result action located performed =>
      obtain ⟨operation, argument, rfl⟩ := encoded_operation_action ops program _ action
      let forward := PartialCoeffectLifting.forward (ops.operation key operation argument)
      refine ⟨TypedRegistry.undo (.operate owner key forward), ?_⟩
      intro input
      rw [encode_undo]
      change InterleavedRecovery.transform owner key (TypedCoeffectReplay.encodeMap key forward) (encodeRegistry ops input) =
        InterleavedRecovery.transform owner key (InterleavedRecovery.callbackMap
          (encodeOperation ops key operation argument)) (encodeRegistry ops input)
      exact transform_on_encoded ops input owner key _ _
        (fun value => (encode_forward_at_key ops key operation argument value).symm)

/-- The native meaning of a rule's selected state map, with its actual
source result separated from the rule's subsequent control edit. -/
def IsFrozenRevision {ops : CoeffectOperations V} (program : Code → Instruction Name ops Code)
    (rule : Labeled.Rule) (actor : Name) (before after : R) (revision : R → R) : Prop :=
  ∃ use middle raw edit,
    EntangledApplications.FrozenApplication (encodeProgram program) actor use
      (encodeRegistry ops before) middle raw ∧
    use.allowed rule (encodeRegistry ops before) actor ∧
    RuleEvaluation.Edit.allowed rule actor edit ∧ edit.valid middle ∧
    encodeRegistry ops after = edit.apply middle ∧
    ∀ input, encodeRegistry ops (revision input) = raw (encodeRegistry ops input)

theorem exists_frozen_revision {ops : CoeffectOperations V} {program : Code → Instruction Name ops Code}
    {rule : Labeled.Rule} {actor : Name} {before after : R}
    (step : Step program rule actor before after) :
    ∃ revision, IsFrozenRevision program rule actor before after revision := by
  obtain ⟨use, middle, edit, application, allowed, edits, valid, result, _⟩ :=
    RuleEvaluation.step_factorization (encodeProgram program) (encode_step step)
  obtain ⟨raw, selected⟩ := EntangledApplications.freeze_application (encodeProgram program) application
  obtain ⟨revision, native⟩ := native_frozen_revision before actor rule selected allowed
  exact ⟨revision, use, middle, raw, edit, selected, allowed, edits, valid, result, native⟩

/-- A prefix of an installed episode on a native typed trace. -/
structure EpisodePrefix {ops : CoeffectOperations V} {program : Code → Instruction Name ops Code} {last : Nat}
    (trace : Trace program (fun _ => none : R) last) (name : Name) (first stop : Nat) : Prop where
  positive : 0 < first
  ordered : first ≤ stop
  bounded : stop ≤ last
  installed : ∀ t, first ≤ t → t ≤ stop → viewAt (trace.state t) name ≠ none
  before : viewAt (trace.state (first - 1)) name = none

def provisionOverlap (state : R) (provider consumer : Name) : Prop :=
  ∃ supply demand : F, state provider = some supply ∧ state consumer = some demand ∧
    ∃ key, supply.component.provides key = true ∧
      (demand.component.requires key = true ∨ demand.component.provides key = true)

def Reloading (state : R) (actor : Name) : Prop :=
  ∃ (fiber : F) (code : Code) (word : List I) (view : View Name Key),
    state actor = some fiber ∧ fiber.phase = .reloading code word view

/-- An indexed trace interpreted on an admitted typed state domain.
The `applied` field identifies the frozen state map with the actual selected
rule application and separates the corresponding control edit. -/
structure FrozenTrace (ops : CoeffectOperations V) (program : Code → Instruction Name ops Code)
    (last : Nat) (sem : Semantics Name V Code) where
  trace : Trace program (fun _ => none : R) last
  state : Nat → sem.Gamma
  represented : ∀ t, t ≤ last → (state t).val = trace.state t
  psi : Nat → sem.Gamma → sem.Gamma
  applied : ∀ t, t < last →
    let before := encodeRegistry ops (trace.state t)
    let after := encodeRegistry ops (trace.state (t + 1))
    let actor := trace.actor t
    ∃ selected middle revision edit,
      EntangledApplications.FrozenApplication (encodeProgram program) actor selected before middle revision ∧
      selected.allowed (trace.rule t) before actor ∧
      RuleEvaluation.Edit.allowed (trace.rule t) actor edit ∧ edit.valid middle ∧
      after = edit.apply middle ∧
      ∀ input : sem.Gamma, encodeRegistry ops (psi t input).val = revision (encodeRegistry ops input.val)

/-- The state map selected at an actual native trace index. -/
noncomputable def Trace.frozenRevision {ops : CoeffectOperations V}
    {program : Code → Instruction Name ops Code} {last : Nat} (trace : Trace program (fun _ => none : R) last)
    (t : Nat) (bounded : t < last) : R → R :=
  Classical.choose (exists_frozen_revision (trace.step t bounded))

/-- Package the actual maps of a native trace on an admitted domain. The
only extra requirements are that the recorded states lie in the domain and
that the selected state maps preserve it. -/
noncomputable def FrozenTrace.ofTrace {ops : CoeffectOperations V}
    {program : Code → Instruction Name ops Code} {last : Nat} (trace : Trace program (fun _ => none : R) last)
    (sem : Semantics Name V Code)
    (admitted : ∀ t, t ≤ last → sem.domain (trace.state t))
    (closed : ∀ t (bounded : t < last) (input : sem.Gamma),
      sem.domain (trace.frozenRevision t bounded input.val)) : FrozenTrace ops program last sem where
  trace := trace
  state t := if bounded : t ≤ last then ⟨trace.state t, admitted t bounded⟩
    else ⟨trace.state 0, admitted 0 (Nat.zero_le _)⟩
  represented := by intro t bounded; simp [bounded]
  psi t input := if bounded : t < last then ⟨trace.frozenRevision t bounded input.val, closed t bounded input⟩ else input
  applied := by
    intro t bounded
    obtain ⟨use, middle, raw, edit, application, allowed, edits, valid, result, native⟩ :=
      Classical.choose_spec (exists_frozen_revision (trace.step t bounded))
    refine ⟨use, middle, raw, edit, application, allowed, edits, valid, result, ?_⟩
    intro input
    simp only [dif_pos bounded]
    exact native input.val

def FrozenTrace.accumulatorAt {ops : CoeffectOperations V} {program : Code → Instruction Name ops Code}
    {last : Nat} {sem : Semantics Name V Code} (run : FrozenTrace ops program last sem)
    (name : Name) (t : Nat) : sem.Gamma → sem.Gamma :=
  match (run.state t).val name with
  | none => id
  | some fiber => TypedStateObservation.accumulator sem fiber.phase.accumulator

/-- Lemma 67, all three clauses, on the native dependent registry and its
Definition 33 union-table observation. -/
def lemma67 {ops : CoeffectOperations V} {program : Code → Instruction Name ops Code}
    {last : Nat} {sem : Semantics Name V Code} (run : FrozenTrace ops program last sem) : Prop :=
  ∀ (name : Name) (first t : Nat), EpisodePrefix run.trace name first t → t < last →
    run.trace.actor t ≠ name →
    let provider := provisionOverlap (run.trace.state t) (run.trace.actor t) name
    let consumer := provisionOverlap (run.trace.state t) name (run.trace.actor t)
    (provider ∨ consumer) →
    (provider → run.psi t = id) ∧
    (¬ provider →
      let undo := run.accumulatorAt name t
      (TypedStateObservation.base ops sem).r
        (undo (run.psi t (run.state t))) (run.psi t (undo (run.state t)))) ∧
    (Reloading (run.trace.state t) name → run.psi t = id)

theorem lemma67_proved {ops : CoeffectOperations V} {program : Code → Instruction Name ops Code}
    {last : Nat} {sem : Semantics Name V Code} (run : FrozenTrace ops program last sem)
    (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops
      (tableSetoid sem.keyObservation (fun _ => True)) key) : lemma67 run := by
  intro name first t episode bounded different
  dsimp only
  intro entangled
  let source := run.trace.state t
  let other := run.trace.actor t
  let raw := encodeRegistry ops source
  let encoded : Indexed.Trace (encodeProgram program) (fun _ => none) last := run.trace.encode
  have rawStep := encoded.step t bounded
  have reached := encoded.prefixRun t (Nat.le_of_lt bounded)
  have invariants := WellFormed.run_invariants (encodeProgram program) reached Safety.empty_parentClosed
    WellFormed.disjoint_empty ⟨Ordering.supported_empty, Ordering.local_empty⟩
  have owned : Safety.Owned raw := by
    have preserves : ∀ {a b : RawRegistry Name ops Code},
        WellFormed.Run (encodeProgram program) a b → Safety.Owned a → Safety.Owned b := by
      intro a b steps
      induction steps with
      | refl => exact id
      | step _ next ih => exact fun old => Safety.step_owned (encodeProgram program) next (ih old)
    exact preserves reached Safety.empty_owned
  have viewPresent : ControlFrame.viewAt raw name ≠ none := by
    rw [viewAt_encode]
    exact episode.installed t episode.ordered (Nat.le_refl t)
  obtain ⟨rawFiber, view, rawPresent, committed⟩ := OrderingIntervals.installed_view raw name viewPresent
  have findTyped : ∃ fiber : F, source name = some fiber ∧ encodeFiber ops fiber = rawFiber :=
    Option.map_eq_some_iff.mp rawPresent
  obtain ⟨fiber, present, rfl⟩ := findTyped
  have foreignExists : ∃ foreign : F, source other = some foreign := by
    rcases entangled with ⟨supply, demand, found, _⟩ | ⟨supply, demand, _, found, _⟩
    · exact ⟨supply, found⟩
    · exact ⟨demand, found⟩
  obtain ⟨foreign, foreignPresent⟩ := foreignExists
  have rawForeign : raw other = some (encodeFiber ops foreign) := by
    simp [raw, encodeRegistry, foreignPresent]
  obtain ⟨use, middle, revision, edit, frozen, allowed, _, _, _, projected⟩ := run.applied t bounded
  have identityLift (equal : revision = id) : run.psi t = id := by
    funext input
    apply Subtype.ext
    apply encodeRegistry_injective ops
    simpa only [equal, id_eq] using projected input
  have overlap_iff :
      provisionOverlap source other name ↔ EntangledApplications.ProviderOverlap (encodeFiber ops fiber) (encodeFiber ops foreign) := by
    simp only [provisionOverlap, EntangledApplications.ProviderOverlap, encodeFiber, present, foreignPresent,
      Option.some.injEq]
    constructor
    · rintro ⟨supply, demand, rfl, rfl, key, provided, overlap⟩
      exact ⟨key, provided, overlap⟩
    · exact fun overlap => ⟨foreign, fiber, rfl, rfl, overlap⟩
  have pinned : provisionOverlap source other name → run.psi t = id := by
    intro overlap
    obtain ⟨key, provides, required⟩ := overlap_iff.mp overlap
    apply identityLift
    have rule := OrderingIntervals.entangled_provider_rule name other
      (encodeFiber ops fiber) (encodeFiber ops foreign) view key
      invariants.2.2.1 owned invariants.2.1 (Ne.symm different)
      rawPresent rawForeign committed provides required rawStep
    apply EntangledApplications.control_application_identity frozen allowed
    rcases rule with retire | leave
    · exact .inr (.inl retire)
    · exact .inr (.inr (.inr (.inr leave)))
  refine ⟨pinned, ?_, ?_⟩
  · intro separate
    have separated key (provided : foreign.component.provides key = true) :
        fiber.component.requires key = false := by
      cases required : fiber.component.requires key with
      | false => rfl
      | true => exact False.elim (separate (overlap_iff.mpr ⟨key, provided, .inl required⟩))
    let meaning := TypedReplayContracts.coeffects ops sem.keyObservation program recovery commutative
    have compared := Results.partialReplayObservation meaning reached name other (encodeFiber ops fiber)
      (encodeFiber ops foreign) rawPresent rawForeign different separated frozen allowed
      (fun _ => TypedCoeffectReplay.setoid sem.keyObservation) (fun _ _ _ same => same)
    have inputSource : (run.state t).val = source := run.represented t (Nat.le_of_lt bounded)
    have encodedAccumulator (input : sem.Gamma) :
        encodeRegistry ops (run.accumulatorAt name t input).val =
          Calculus.discharge Stages.undo (encodeFiber ops fiber).phase.accumulator (encodeRegistry ops input.val) := by
      simp only [FrozenTrace.accumulatorAt, inputSource, present, TypedStateObservation.accumulator_value,
        encode_discharge, encodeFiber, accumulator_encode]
    apply (TypedStateObservation.tables_related_encode_iff ops sem.keyObservation (fun _ => True) _ _).mp
    rw [encodedAccumulator, projected, projected, encodedAccumulator, inputSource]
    exact compared
  · intro reloading
    rcases entangled with provider | ⟨supply, demand, supplier, consumer, key, provides, overlap⟩
    · exact pinned provider
    · have supplyEq := Option.some.inj (supplier.symm.trans present)
      have demandEq := Option.some.inj (consumer.symm.trans foreignPresent)
      subst supply demand
      have requires : foreign.component.requires key = true := by
        rcases overlap with required | duplicate
        · exact required
        · exact False.elim (invariants.2.1 name other (encodeFiber ops fiber) (encodeFiber ops foreign)
            rawPresent rawForeign (Ne.symm different) key ⟨provides, duplicate⟩)
      obtain ⟨entry, code, inverses, committedView, found, phase⟩ := reloading
      have same := Option.some.inj (found.symm.trans present)
      subst entry
      have isReloading :
          (encodeFiber ops fiber).phase = .reloading code (inverses.map (encodeInverse ops)) committedView := by
        simp [encodeFiber, encodePhase, phase]
      have rule := OrderingIntervals.reloading_consumer_rule other name (encodeFiber ops foreign)
        (encodeFiber ops fiber) key code _ committedView invariants.2.2.1 owned
        invariants.2.1 rawForeign rawPresent isReloading requires provides rawStep
      apply identityLift
      apply EntangledApplications.control_application_identity frozen allowed
      rcases rule with retire | remove
      · exact .inr (.inl retire)
      · exact .inr (.inr (.inl remove))

/-- Specialize to Definition 31's fixed-word key tests and the native
state maps chosen from the actual indexed sequence. -/
theorem lemma67_on_trace {ops : CoeffectOperations V} {program : Code → Instruction Name ops Code}
    {last : Nat} (trace : Trace program (fun _ => none : R) last) (sem : Semantics Name V Code)
    (admitted : ∀ t, t ≤ last → sem.domain (trace.state t))
    (closed : ∀ t (bounded : t < last) (input : sem.Gamma),
      sem.domain (trace.frozenRevision t bounded input.val))
    (paperObservation : sem.keyObservation = PaperObservationEquations.keySetoid ops)
    (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops
      (PaperObservationEquations.fullTableObservation ops) key) :
    lemma67 (FrozenTrace.ofTrace trace sem admitted closed) := by
  apply lemma67_proved _ recovery
  rw [paperObservation]
  exact commutative

end Cordis.TypedRegistry
