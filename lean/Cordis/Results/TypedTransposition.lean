import Cordis.TypedCallbackExchange
import Cordis.TypedRegistryTrace
import Cordis.TypedStateObservation
import Cordis.OrchestrationSorting

/-! Lemma 78(1) on the ordinary typed calculus. The encoded exchange is
reflected back to typed transitions with the same rules and actors. The
endpoint compares typed table values and the complete function fields. -/
namespace Cordis.TypedRegistry

open OrchestrationSorting (Command)
universe u
variable {Name Key Code : Type u} {Value : Key → Type u} [DecidableEq Name] [DecidableEq Key]
variable {ops : PaperEffectEquations.CoeffectOperations Value}
local notation "R" => Registry Name Value Code

def commandRule : Command Name Key Code → Labeled.Rule
  | .insert .. => .insert
  | .retire .. => .retire
  | .remove .. => .remove

def applyCommand (command : Command Name Key Code) (state : R) : R :=
  match command with
  | .insert name component => put state name (fresh component none)
  | .retire name => retire state name
  | .remove name => erase state name

omit [DecidableEq Name] [DecidableEq Key] in
def CommandEnabled (command : Command Name Key Code) (state : R) : Prop :=
  match command with
  | .insert name component => Insertable state name component none
  | .retire name => state name ≠ none
  | .remove name => Removable state name

def CommandStep (command : Command Name Key Code) (before after : R) : Prop :=
  CommandEnabled command before ∧ after = applyCommand command before

theorem command_toStep (program : Code → Instruction Name ops Code)
    (command : Command Name Key Code) {before after : R}
    (step : CommandStep command before after) :
    Step program (commandRule command) command.actor before after := by
  obtain ⟨enabled, rfl⟩ := step
  cases command with
  | insert name component => exact .insert _ name component none enabled
  | retire name => exact .retire _ name enabled
  | remove name => exact .remove _ name enabled

private theorem encode_applyCommand (ops : PaperEffectEquations.CoeffectOperations Value)
    (command : Command Name Key Code) (state : R) :
    encodeRegistry ops (applyCommand command state) = command.apply (encodeRegistry ops state) := by
  cases command <;> simp [applyCommand, Command.apply]

omit [DecidableEq Name] in
private theorem encode_commandEnabled (ops : PaperEffectEquations.CoeffectOperations Value)
    (command : Command Name Key Code) (state : R) :
    command.Enabled (encodeRegistry ops state) ↔ CommandEnabled command state := by
  cases command <;> simp [CommandEnabled, Command.Enabled]

/-- Lemma 78(2) under root-only external insertion. The command's payload
and the complete registry endpoint are preserved literally. -/
theorem activation_command_diamond (program : Code → Instruction Name ops Code)
    {rule : Labeled.Rule} {actor : Name} {before middle final : R} (command : Command Name Key Code)
    (activation : Step program rule actor before middle) (active : Transposition.Activation rule)
    (external : CommandStep command middle final) (different : actor ≠ command.actor)
    (notCreated : before command.actor = none → middle command.actor = none) :
    ∃ swapped, CommandStep command before swapped ∧ Step program rule actor swapped final := by
  obtain ⟨enabled, rfl⟩ := external
  obtain ⟨earlier, swapped⟩ := OrchestrationSorting.activation_command_diamond (encodeProgram program)
    command (encode_step activation) active ((encode_commandEnabled ops command middle).mpr enabled)
    different (fun absent => (encodeRegistry_none ops middle command.actor).mpr
      (notCreated ((encodeRegistry_none ops before command.actor).mp absent)))
  rw [← encode_applyCommand, ← encode_applyCommand] at swapped
  obtain ⟨actual, typed, encoded⟩ := decode_step swapped
  have same := encodeRegistry_injective ops encoded
  subst actual
  exact ⟨applyCommand command before, ⟨(encode_commandEnabled ops command before).mp earlier, rfl⟩, typed⟩

end Cordis.TypedRegistry

namespace Cordis.Results

open TypedRegistry TypedStateObservation Iterators PaperEffectEquations
universe u
variable {Name Key Code : Type u} {Value : Key → Type u} [DecidableEq Name] [DecidableEq Key]

local notation "R" => Registry Name Value Code

/-- The activation exchange for dependent coeffect tables, named operations
with dependent outcomes, and partial captured inverses. Applicability is
preserved with the original fresh choices. Definition 44 supplies respect
of the actual primitive inverse captures. The semantic admission premises
concern the actual endpoint's stored iterator fields and inverse captures. -/
theorem lemma78_typed_activation {ops : CoeffectOperations Value}
    (program : Code → Instruction Name ops Code) (sem : Semantics Name Value Code)
    (keys : sem.keyObservation = PaperObservationEquations.keySetoid ops)
    (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops
      (PaperObservationEquations.fullTableObservation ops) key)
    {last : Nat} (history : Trace program (fun _ => none : R) last)
    {first second : Name} {firstRule secondRule : Labeled.Rule} {middle final : R}
    (firstStep : Step program firstRule first (history.state last) middle)
    (firstActive : Transposition.Activation firstRule)
    (secondStep : Step program secondRule second middle final)
    (secondActive : Transposition.Activation secondRule)
    (applicable : ∃ next, Step program secondRule second (history.state last) next)
    (different : first ≠ second)
    (entries : ∀ actor fiber, final actor = some fiber →
      @WitnessedIterator sem.Gamma (base ops sem) (sem.iterator actor fiber.component.entry))
    (current : ∀ actor fiber, final actor = some fiber → ∀ code stack view,
      fiber.phase = .reloading code stack view →
      @WitnessedIterator sem.Gamma (base ops sem) (sem.iterator actor code))
    (captures : ∀ actor fiber, final actor = some fiber → ∀ token ∈ fiber.phase.accumulator,
      @Effects.Respects sem.Gamma (base ops sem) (inverse sem token)) :
    ∃ swappedMiddle swappedFinal,
      Step program secondRule second (history.state last) swappedMiddle ∧
      Step program firstRule first swappedMiddle swappedFinal ∧
      Related ops sem swappedFinal final := by
  letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid sem.keyObservation
  have localCommutative : ∀ key, PaperObservationEquations.CommutativeKey ops
      (PartialCoeffectIndependenceContracts.tableSetoid sem.keyObservation (fun _ => True)) key := by
    rw [keys]
    exact commutative
  have callbacks := encoded_program_callbacks ops sem.keyObservation program recovery localCommutative
  have independent := encoded_program_callback_pair ops sem.keyObservation program localCommutative
  have rawHistory := history.encode.prefixRun last (Nat.le_refl _)
  have rawApplicable : ∃ next, Labeled.Step (encodeProgram program) secondRule second
      (encodeRegistry ops (history.state last)) next := by
    obtain ⟨next, allowed⟩ := applicable
    exact ⟨encodeRegistry ops next, encode_step allowed⟩
  obtain ⟨rawMiddle, rawFinal, secondSwapped, firstSwapped, paired⟩ :=
    Transposition.activation_diamond (encodeProgram program) (encode_step firstStep) firstActive
      (encode_step secondStep) secondActive rawApplicable different rawHistory callbacks
      (fun _ _ firstCode secondCode _ _ _ _ _ _ _ _ => independent firstCode secondCode)
  obtain ⟨swappedMiddle, secondTyped, middleEncoded⟩ := decode_step secondSwapped
  rw [← middleEncoded] at firstSwapped
  obtain ⟨swappedFinal, firstTyped, finalEncoded⟩ := decode_step firstSwapped
  refine ⟨swappedMiddle, swappedFinal, secondTyped, firstTyped, ?_⟩
  rw [← finalEncoded] at paired
  exact related_of_encoded ops sem paired entries current captures

open OrchestrationSorting (Command)

/-- Definitions 37, 40, 49 and 56 for the stored functions of one fiber. -/
structure ActivationFields {ops : CoeffectOperations Value} (sem : Semantics Name Value Code)
    (actor : Name) (fiber : Fiber Name Value Code) : Prop where
  witnessed : @WitnessedIterator sem.Gamma (observation ops sem
    (fun key => fiber.component.requires key = true ∨ fiber.component.provides key = true))
    (sem.iterator actor fiber.component.entry)
  frame : IteratorFramesOutside sem
    (fun key => fiber.component.requires key = true ∨ fiber.component.provides key = true)
    (sem.iterator actor fiber.component.entry)
  current : ∀ code stack view, fiber.phase = .reloading code stack view →
    Reach (sem.iterator actor fiber.component.entry) (sem.iterator actor code)
  captured : ∀ token ∈ fiber.phase.accumulator,
    Generator (sem.iterator actor fiber.component.entry) (inverse sem token)

/-- The typed activation exchange at two adjacent indices of a single
empty-origin trace. The comparison of stored functions uses only their
witnesses at the declared interface and the frame of their actual generators. -/
theorem lemma78_typed_adjacent_activation {ops : CoeffectOperations Value}
    (program : Code → Instruction Name ops Code) (sem : Semantics Name Value Code)
    (keys : sem.keyObservation = PaperObservationEquations.keySetoid ops)
    (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops
      (PaperObservationEquations.fullTableObservation ops) key)
    {last : Nat} (history : Trace program (fun _ => none : R) last) (t : Nat)
    (indices : t + 1 < last)
    (firstActive : Transposition.Activation (history.rule t))
    (secondActive : Transposition.Activation (history.rule (t + 1)))
    (applicable : ∃ next, Step program (history.rule (t + 1)) (history.actor (t + 1)) (history.state t) next)
    (different : history.actor t ≠ history.actor (t + 1))
    (fields : ∀ actor fiber, history.state (t + 2) actor = some fiber →
      ActivationFields (ops := ops) sem actor fiber) :
    ∃ swappedMiddle swappedFinal,
      Step program (history.rule (t + 1)) (history.actor (t + 1)) (history.state t) swappedMiddle ∧
      Step program (history.rule t) (history.actor t) swappedMiddle swappedFinal ∧
      Related ops sem swappedFinal (history.state (t + 2)) := by
  letI : Setoid sem.Gamma := base ops sem
  let initialPrefix : Trace program (fun _ => none : R) t := {
    state := history.state
    actor := history.actor
    rule := history.rule
    start := history.start
    step := fun index bound => history.step index (by omega)
  }
  have entries actor fiber (found : history.state (t + 2) actor = some fiber) :=
    witnessed_on_all_keys ops sem _ (fields actor fiber found).witnessed (fields actor fiber found).frame
  exact lemma78_typed_activation program sem keys recovery commutative initialPrefix
    (history.step t (by omega)) firstActive (history.step (t + 1) indices) secondActive
    applicable different entries
    (fun actor fiber found code stack view phase => (entries actor fiber found).reachable
      ((fields actor fiber found).current code stack view phase))
    (fun actor fiber found token member =>
      generator_respects_on_all_keys ops sem _ (fields actor fiber found).witnessed
        (fields actor fiber found).frame ((fields actor fiber found).captured token member))

/-- The typed activation/command exchange at two adjacent trace indices.
The first swapped step retains the command's component payload. -/
theorem lemma78_typed_adjacent_orchestration {ops : CoeffectOperations Value}
    (program : Code → Instruction Name ops Code)
    {initial : R} {last : Nat} (history : Trace program initial last) (t : Nat)
    (indices : t + 1 < last) (command : Command Name Key Code)
    (firstActive : Transposition.Activation (history.rule t))
    (secondRule : history.rule (t + 1) = commandRule command)
    (secondActor : history.actor (t + 1) = command.actor)
    (external : CommandStep command (history.state (t + 1)) (history.state (t + 2)))
    (different : history.actor t ≠ history.actor (t + 1))
    (notCreated : history.state t command.actor = none → history.state (t + 1) command.actor = none) :
    ∃ swapped,
      CommandStep command (history.state t) swapped ∧
      Step program (history.rule (t + 1)) (history.actor (t + 1)) (history.state t) swapped ∧
      Step program (history.rule t) (history.actor t) swapped (history.state (t + 2)) := by
  obtain ⟨swapped, earlier, later⟩ := TypedRegistry.activation_command_diamond program command
    (history.step t (by omega)) firstActive external (by simpa only [secondActor] using different) notCreated
  exact ⟨swapped, earlier, by simpa only [secondRule, secondActor] using command_toStep program command earlier, later⟩

end Cordis.Results
