import Cordis.TypedRegistry
import Cordis.IndexedTrace

/-!
# Typed registry transitions

The transition labels and nine calculus rules are the same as in the registry
calculus. The primitive stage at a key carries that key's value type.
Encoding preserves each rule label, actor, and captured continuation.
-/
namespace Cordis.TypedRegistry

open PaperEffectEquations (CoeffectOperations)
open Labeled (Rule)
universe u
variable {Name Key Code : Type u} {V : Key → Type u}
variable {ops : CoeffectOperations V} [DecidableEq Name] [DecidableEq Key]
local notation "R" => Registry Name V Code

/-- A typed step with the same rule and actor indices as the ordinary
nine-rule relation. -/
inductive Step (program : Code → Instruction Name ops Code) : Rule → Name → R → R → Prop
  | insert (r name component parent) : Insertable r name component parent →
      Step program .insert name r (put r name (fresh component parent))
  | retire (r name) : r name ≠ none → Step program .retire name r (retire r name)
  | remove (r name) : Removable r name → Step program .remove name r (erase r name)
  | begin (r name fiber view) : r name = some fiber → fiber.phase = .inactive →
      Target r name view →
      Step program .begin name r (mark r name (.reloading fiber.component.entry [] view))
  | iter (r s name fiber code accumulator view inverse next) :
      r name = some fiber → fiber.phase = .reloading code accumulator view →
      Target r name view → Land program name code r s inverse (some next) →
      Step program .iter name r (mark s name (.reloading next (inverse :: accumulator) view))
  | finish (r s name fiber code accumulator view inverse) :
      r name = some fiber → fiber.phase = .reloading code accumulator view →
      Target r name view → Land program name code r s inverse none →
      Step program .finish name r (mark s name (.active (inverse :: accumulator) view))
  | divert (r s name fiber code accumulator view tail) :
      r name = some fiber → fiber.phase = .reloading code accumulator view →
      ¬ Target r name view →
      ((s = r ∧ tail = []) ∨ ∃ inverse next, Land program name code r s inverse next ∧ tail = [inverse]) →
      Step program .divert name r (mark s name (.unloading (tail ++ accumulator) view))
  | leave (r name fiber accumulator view) :
      r name = some fiber → fiber.phase = .active accumulator view → ¬ Target r name view →
      Step program .leave name r (mark r name (.unloading accumulator view))
  | unload (r name fiber accumulator view) :
      r name = some fiber → fiber.phase = .unloading accumulator view → ¬ Relied r name →
      Step program .unload name r (mark (discharge accumulator r) name .inactive)

omit [DecidableEq Name] in
private theorem encoded_present {r : R} {name : Name} {fiber : Fiber Name V Code}
    (present : r name = some fiber) :
    encodeRegistry ops r name = some (encodeFiber ops fiber) := by
  simp [encodeRegistry, present]

omit [DecidableEq Name] in
private theorem encoded_absent_iff (r : R) (name : Name) :
    encodeRegistry ops r name = none ↔ r name = none := by
  cases atName : r name <;> simp [encodeRegistry, atName]

/-- Encoding a typed step retains its exact actor, label, and endpoints. -/
theorem encode_step {program : Code → Instruction Name ops Code}
    {rule : Rule} {actor : Name} {before after : R}
    (step : Step program rule actor before after) :
    Labeled.Step (encodeProgram program) rule actor (encodeRegistry ops before) (encodeRegistry ops after) := by
  cases step with
  | insert r name component parent ready =>
    simpa only [encode_put, encode_fresh] using Labeled.Step.insert
      (program := encodeProgram program) (encodeRegistry ops before) actor component parent
      ((insertable_encode_iff ops before actor component parent).mpr ready)
  | retire r name present =>
    simpa only [encode_retire] using Labeled.Step.retire
      (program := encodeProgram program) (encodeRegistry ops before) actor
      (fun missing => present ((encoded_absent_iff before actor).mp missing))
  | remove r name ready =>
    simpa only [encode_erase] using Labeled.Step.remove
      (program := encodeProgram program) (encodeRegistry ops before) actor
      ((removable_encode_iff ops before actor).mpr ready)
  | begin r name fiber view present inactive target =>
    have whereAt := encoded_present (ops := ops) present
    have encodedInactive : (encodeFiber ops fiber).phase = .inactive := by
      simp [encodeFiber, encodePhase, inactive]
    simpa only [encode_mark, encodePhase, List.map_nil] using Labeled.Step.begin
      (program := encodeProgram program) (encodeRegistry ops before) actor (encodeFiber ops fiber) view
      whereAt encodedInactive (by simp [whereAt]) ((target_encode_iff ops before actor view).mpr target)
  | iter r s name fiber code accumulator view inverse next present reloading target performed =>
    have encodedReloading : (encodeFiber ops fiber).phase =
        .reloading code (accumulator.map (encodeInverse ops)) view := by
      simp [encodeFiber, encodePhase, reloading]
    simpa only [encode_mark, encodePhase, List.map_cons] using Labeled.Step.iter
      (program := encodeProgram program) (encodeRegistry ops before) (encodeRegistry ops s) actor
      (encodeFiber ops fiber) code (accumulator.map (encodeInverse ops)) view (encodeInverse ops inverse) next
      (encoded_present present) encodedReloading ((target_encode_iff ops before actor view).mpr target)
      (land_encode ops performed)
  | finish r s name fiber code accumulator view inverse present reloading target performed =>
    have encodedReloading : (encodeFiber ops fiber).phase =
        .reloading code (accumulator.map (encodeInverse ops)) view := by
      simp [encodeFiber, encodePhase, reloading]
    simpa only [encode_mark, encodePhase, List.map_cons] using Labeled.Step.finish
      (program := encodeProgram program) (encodeRegistry ops before) (encodeRegistry ops s) actor
      (encodeFiber ops fiber) code (accumulator.map (encodeInverse ops)) view (encodeInverse ops inverse)
      (encoded_present present) encodedReloading ((target_encode_iff ops before actor view).mpr target)
      (land_encode ops performed)
  | divert r s name fiber code accumulator view tail present reloading target performed =>
    have encodedReloading : (encodeFiber ops fiber).phase =
        .reloading code (accumulator.map (encodeInverse ops)) view := by
      simp [encodeFiber, encodePhase, reloading]
    have rawCases :
        (encodeRegistry ops s = encodeRegistry ops before ∧ tail.map (encodeInverse ops) = []) ∨
        ∃ rawInverse next, Stages.Land (encodeProgram program) actor code
          (encodeRegistry ops before) (encodeRegistry ops s) rawInverse next ∧
          tail.map (encodeInverse ops) = [rawInverse] := by
      rcases performed with ⟨rfl, rfl⟩ | ⟨inverse, next, landed, rfl⟩
      · exact .inl ⟨rfl, rfl⟩
      · exact .inr ⟨encodeInverse ops inverse, next, land_encode ops landed, rfl⟩
    simpa only [encode_mark, encodePhase, List.map_append] using Labeled.Step.divert
      (program := encodeProgram program) (encodeRegistry ops before) (encodeRegistry ops s) actor
      (encodeFiber ops fiber) code (accumulator.map (encodeInverse ops)) view (tail.map (encodeInverse ops))
      (encoded_present present) encodedReloading
      (fun decided => target ((target_encode_iff ops before actor view).mp decided)) rawCases
  | leave r name fiber accumulator view present active target =>
    have encodedActive : (encodeFiber ops fiber).phase =
        .active (accumulator.map (encodeInverse ops)) view := by
      simp [encodeFiber, encodePhase, active]
    simpa only [encode_mark, encodePhase] using Labeled.Step.leave
      (program := encodeProgram program) (encodeRegistry ops before) actor (encodeFiber ops fiber)
      (accumulator.map (encodeInverse ops)) view (encoded_present present) encodedActive
      (fun decided => target ((target_encode_iff ops before actor view).mp decided))
  | unload r name fiber accumulator view present unloading guard =>
    have encodedUnloading : (encodeFiber ops fiber).phase =
        .unloading (accumulator.map (encodeInverse ops)) view := by
      simp [encodeFiber, encodePhase, unloading]
    simpa only [encode_mark, encode_discharge, encodePhase] using Labeled.Step.unload
      (program := encodeProgram program) (encodeRegistry ops before) actor (encodeFiber ops fiber)
      (accumulator.map (encodeInverse ops)) view (encoded_present present) encodedUnloading
      (fun relied => guard ((relied_encode_iff ops before actor).mp relied))

omit [DecidableEq Name] in
private theorem reflected_present {r : R} {name : Name} {raw : RawFiber Name ops Code}
    (present : encodeRegistry ops r name = some raw) :
    ∃ fiber, r name = some fiber ∧ encodeFiber ops fiber = raw := by
  cases atName : r name with
  | none => simp [encodeRegistry, atName] at present
  | some fiber =>
    exact ⟨fiber, rfl, by simpa [encodeRegistry, atName] using present⟩

omit [DecidableEq Name] in
private theorem decode_inactive {fiber : Fiber Name V Code}
    (state : (encodeFiber ops fiber).phase = .inactive) : fiber.phase = .inactive := by
  cases phase : fiber.phase <;> simp [encodeFiber, encodePhase, phase] at state ⊢

omit [DecidableEq Name] in
private theorem decode_reloading {fiber : Fiber Name V Code} {code : Code}
    {accumulator} {view : Calculus.View Name Key}
    (state : (encodeFiber ops fiber).phase = .reloading code accumulator view) :
    ∃ stack, fiber.phase = .reloading code stack view ∧ stack.map (encodeInverse ops) = accumulator := by
  cases phase : fiber.phase with
  | inactive => simp [encodeFiber, encodePhase, phase] at state
  | reloading saved stack committed =>
    have fields : saved = code ∧ stack.map (encodeInverse ops) = accumulator ∧ committed = view := by
      simpa [encodeFiber, encodePhase, phase] using state
    obtain ⟨rfl, word, rfl⟩ := fields
    exact ⟨stack, rfl, word⟩
  | active => simp [encodeFiber, encodePhase, phase] at state
  | unloading => simp [encodeFiber, encodePhase, phase] at state

omit [DecidableEq Name] in
private theorem decode_active {fiber : Fiber Name V Code}
    {accumulator} {view : Calculus.View Name Key}
    (state : (encodeFiber ops fiber).phase = .active accumulator view) :
    ∃ stack, fiber.phase = .active stack view ∧ stack.map (encodeInverse ops) = accumulator := by
  cases phase : fiber.phase with
  | inactive => simp [encodeFiber, encodePhase, phase] at state
  | reloading => simp [encodeFiber, encodePhase, phase] at state
  | active stack committed =>
    have fields : stack.map (encodeInverse ops) = accumulator ∧ committed = view := by
      simpa [encodeFiber, encodePhase, phase] using state
    obtain ⟨word, rfl⟩ := fields
    exact ⟨stack, rfl, word⟩
  | unloading => simp [encodeFiber, encodePhase, phase] at state

omit [DecidableEq Name] in
theorem decode_unloading {fiber : Fiber Name V Code}
    {accumulator} {view : Calculus.View Name Key}
    (state : (encodeFiber ops fiber).phase = .unloading accumulator view) :
    ∃ stack, fiber.phase = .unloading stack view ∧ stack.map (encodeInverse ops) = accumulator := by
  cases phase : fiber.phase with
  | inactive => simp [encodeFiber, encodePhase, phase] at state
  | reloading => simp [encodeFiber, encodePhase, phase] at state
  | active => simp [encodeFiber, encodePhase, phase] at state
  | unloading stack committed =>
    have fields : stack.map (encodeInverse ops) = accumulator ∧ committed = view := by
      simpa [encodeFiber, encodePhase, phase] using state
    obtain ⟨word, rfl⟩ := fields
    exact ⟨stack, rfl, word⟩

/-- Every ordinary step from the encoding of a typed source lifts to a typed
step. Inverse constructors and continuation codes stay attached to the same
stage, including the choice between the two L-Divert premises. -/
theorem decode_step {program : Code → Instruction Name ops Code}
    {rule : Rule} {actor : Name} {before : R} {after : RawRegistry Name ops Code}
    (step : Labeled.Step (encodeProgram program) rule actor (encodeRegistry ops before) after) :
    ∃ next : R, Step program rule actor before next ∧ encodeRegistry ops next = after := by
  generalize source : encodeRegistry ops before = raw at step
  cases step with
  | insert r name component parent ready =>
    subst raw
    refine ⟨_, Step.insert _ _ _ _ ((insertable_encode_iff ops before actor component parent).mp ready), ?_⟩
    simp only [encode_put, encode_fresh]
  | retire r name present =>
    subst raw
    refine ⟨_, Step.retire _ _ (fun missing => present ((encoded_absent_iff before actor).mpr missing)), ?_⟩
    simp only [encode_retire]
  | remove r name ready =>
    subst raw
    refine ⟨_, Step.remove _ _ ((removable_encode_iff ops before actor).mp ready), ?_⟩
    simp only [encode_erase]
  | begin r name rawFiber view found inactive _ target =>
    subst raw
    obtain ⟨fiber, present, rfl⟩ := reflected_present found
    refine ⟨_, Step.begin _ _ _ _ present (decode_inactive inactive)
      ((target_encode_iff ops before actor view).mp target), ?_⟩
    simp only [encode_mark, encodePhase, List.map_nil]
    rfl
  | iter r s name rawFiber code accumulator view rawInverse next found phase target performed =>
    subst raw
    obtain ⟨fiber, present, rfl⟩ := reflected_present found
    obtain ⟨stack, reloading, rfl⟩ := decode_reloading phase
    obtain ⟨mid, inverse, landed, rfl, rfl⟩ := land_decode ops performed
    refine ⟨_, Step.iter _ _ _ _ _ _ _ _ _ present reloading
      ((target_encode_iff ops before actor view).mp target) landed, ?_⟩
    simp only [encode_mark, encodePhase, List.map_cons]
  | finish r s name rawFiber code accumulator view rawInverse found phase target performed =>
    subst raw
    obtain ⟨fiber, present, rfl⟩ := reflected_present found
    obtain ⟨stack, reloading, rfl⟩ := decode_reloading phase
    obtain ⟨mid, inverse, landed, rfl, rfl⟩ := land_decode ops performed
    refine ⟨_, Step.finish _ _ _ _ _ _ _ _ present reloading
      ((target_encode_iff ops before actor view).mp target) landed, ?_⟩
    simp only [encode_mark, encodePhase, List.map_cons]
  | divert r s name rawFiber code accumulator view tail found phase target performed =>
    subst raw
    obtain ⟨fiber, present, rfl⟩ := reflected_present found
    obtain ⟨stack, reloading, rfl⟩ := decode_reloading phase
    have different : ¬ Target before actor view :=
      fun ready => target ((target_encode_iff ops before actor view).mpr ready)
    rcases performed with ⟨rfl, rfl⟩ | ⟨rawInverse, next, performed, rfl⟩
    · refine ⟨_, Step.divert _ _ _ _ _ _ _ [] present reloading different (.inl ⟨rfl, rfl⟩), ?_⟩
      simp only [encode_mark, encodePhase, List.nil_append]
    · obtain ⟨mid, inverse, landed, rfl, rfl⟩ := land_decode ops performed
      refine ⟨_, Step.divert _ _ _ _ _ _ _ [inverse] present reloading different
        (.inr ⟨inverse, next, landed, rfl⟩), ?_⟩
      simp only [encode_mark, encodePhase, List.map_append, List.map_cons, List.map_nil]
  | leave r name rawFiber accumulator view found phase target =>
    subst raw
    obtain ⟨fiber, present, rfl⟩ := reflected_present found
    obtain ⟨stack, active, rfl⟩ := decode_active phase
    refine ⟨_, Step.leave _ _ _ _ _ present active
      (fun ready => target ((target_encode_iff ops before actor view).mpr ready)), ?_⟩
    simp only [encode_mark, encodePhase]
  | unload r name rawFiber accumulator view found phase guard =>
    subst raw
    obtain ⟨fiber, present, rfl⟩ := reflected_present found
    obtain ⟨stack, unloading, rfl⟩ := decode_unloading phase
    refine ⟨_, Step.unload _ _ _ _ _ present unloading
      (fun relied => guard ((relied_encode_iff ops before actor).mpr relied)), ?_⟩
    simp only [encode_mark, encode_discharge, encodePhase]

/-- Encoding and reflection preserve steps between two named typed endpoints. -/
theorem step_encode_iff {program : Code → Instruction Name ops Code}
    {rule : Rule} {actor : Name} {before after : R} :
    Labeled.Step (encodeProgram program) rule actor (encodeRegistry ops before) (encodeRegistry ops after) ↔
      Step program rule actor before after := by
  constructor
  · intro step
    obtain ⟨next, typed, same⟩ := decode_step step
    have endpoint := encodeRegistry_injective ops same
    exact endpoint ▸ typed
  · exact encode_step

/-- An indexed trace with an arbitrary typed initial state. -/
structure Trace (program : Code → Instruction Name ops Code) (initial : R) (last : Nat) where
  state : Nat → R
  rule : Nat → Rule
  actor : Nat → Name
  start : state 0 = initial
  step : ∀ t, t < last → Step program (rule t) (actor t) (state t) (state (t + 1))

/-- The encoding transports every prefix with its original rule and actor
labels. -/
def Trace.encode {program : Code → Instruction Name ops Code}
    {initial : R} {last : Nat} (trace : Trace program initial last) :
    Indexed.Trace (encodeProgram program) (encodeRegistry ops initial) last where
  state t := encodeRegistry ops (trace.state t)
  rule := trace.rule
  actor := trace.actor
  start := congrArg (encodeRegistry ops) trace.start
  step t bound := encode_step (trace.step t bound)

end Cordis.TypedRegistry
