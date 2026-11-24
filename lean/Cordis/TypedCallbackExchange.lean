import Cordis.DependentCoeffectExchange
import Cordis.StageSimulation
import Cordis.TranspositionActivation
import Cordis.TypedRegistry

/-! Transport the local operation laws for Lemma 78 to the tagged carrier
used by the registry. Each call stays at its own key and returns the outcome
of its named operation and argument. -/
namespace Cordis.TypedRegistry
open Effects AccumulatorProvenance Transposition
open TypedCoeffectReplay (pack unpack encodeMap)
open Iterators (OptionRel)

universe u
variable {Key : Type u} {Value : Key → Type u} [DecidableEq Key]
variable (ops : PaperEffectEquations.CoeffectOperations Value)
variable (observe : ∀ key, Setoid (Value key))

private theorem encoded_call_success {key : Key} {name : ops.Name key}
    {arg : ops.Argument key name} {input after : Value key}
    {inverse : Value key → Option (Value key)} {outcome : ops.Outcome key name}
    (actual : (ops.operation key name arg).run input = some (after, inverse, outcome)) :
    encodeOperation ops key name arg (pack key input) =
      .ok (pack key after, encodeMap key inverse, packOutcome ops key name outcome) := by
  simp [encodeOperation, actual]

theorem encoded_call_sound {key : Key} {name : ops.Name key}
    {arg : ops.Argument key name} {input output : Scalar ops}
    {inverse : Scalar ops → Scalar ops} {outcome : Scalar ops}
    (called : encodeOperation ops key name arg input = .ok (output, inverse, outcome)) :
    ∃ before after saved result,
      input = pack key before ∧
      (ops.operation key name arg).run before = some (after, saved, result) ∧
      output = pack key after ∧ inverse = encodeMap key saved ∧
      outcome = packOutcome ops key name result := by
  cases decoded : unpack key input with
  | none => simp [encodeOperation, decoded] at called
  | some before =>
    have inputPack := TypedCoeffectReplay.unpack_recognizes key input before decoded
    cases actual : (ops.operation key name arg).run before with
    | none => simp [encodeOperation, decoded, actual] at called
    | some triple =>
      obtain ⟨after, saved, result⟩ := triple
      have fields : pack key after = output ∧ encodeMap key saved = inverse ∧
          packOutcome ops key name result = outcome := by
        simpa [encodeOperation, decoded, actual, Prod.mk.injEq] using called
      obtain ⟨rfl, rfl, rfl⟩ := fields
      exact ⟨before, after, saved, result, inputPack, actual, rfl, rfl, rfl⟩

/-- Definition 44 supplies the exact shared-key callback law used by the
registry proof. Each operation may have its own outcome type. -/
theorem encoded_callback_exchange (key : Key) (firstName secondName : ops.Name key)
    (firstArg : ops.Argument key firstName) (secondArg : ops.Argument key secondName)
    (laws : PaperObservationEquations.IndependentOperations ops
      (PartialCoeffectIndependenceContracts.tableSetoid observe (fun _ => True)) key key firstName secondName) :
    @CallbackExchange (Scalar ops) PUnit.{u+1} (TypedCoeffectReplay.setoid observe) (encodeOperation ops key firstName firstArg)
      (encodeOperation ops key secondName secondArg) := by
  intro before middle final firstInverse secondInverse firstOutcome secondOutcome firstCalled secondCalled
  obtain ⟨input, afterFirst, firstSaved, firstResult, rfl, firstActual, rfl, rfl, rfl⟩ :=
    encoded_call_sound ops firstCalled
  obtain ⟨inputSecond, finalOriginal, secondSaved, secondResult, joined, secondActual, rfl, rfl, rfl⟩ :=
    encoded_call_sound ops secondCalled
  have same : afterFirst = inputSecond := TypedCoeffectReplay.pack_injective _ joined
  subst inputSecond
  obtain ⟨afterSecond, secondBefore, finalReordered, firstAfter, secondReordered, firstReordered,
    finals, secondSavedRelated, firstSavedRelated⟩ :=
    DependentCoeffectExchange.exchange_same_key ops observe key firstName secondName firstArg secondArg
      laws firstActual secondActual
  exact ⟨pack key afterSecond, encodeMap key secondBefore, pack key finalReordered, encodeMap key firstAfter,
    encoded_call_success ops secondReordered, encoded_call_success ops firstReordered,
    (TypedCoeffectReplay.packed_related observe key _ _).mpr finals,
    fun {_ _} probes => TypedCoeffectReplay.encodeMap_related observe key secondSavedRelated _ _ probes,
    fun {_ _} probes => TypedCoeffectReplay.encodeMap_related observe key firstSavedRelated _ _ probes⟩

theorem encoded_operation_action {Name Code : Type u}
    (program : Code → Instruction Name ops Code) (code : Code)
    {key : Key} {callback : Scalar ops → Except PUnit.{u+1} (Scalar ops × (Scalar ops → Scalar ops) × Scalar ops)}
    (action : (encodeProgram program code).action = .operate key callback) :
    ∃ name argument, callback = encodeOperation ops key name argument := by
  change encodeAction ops (program code).action = .operate key callback at action
  cases selected : (program code).action with
  | unit | provide | instantiate => simp [selected, encodeAction] at action
  | operate key' name argument =>
    rw [selected] at action
    change Stages.Action.operate key' (encodeOperation ops key' name argument) = .operate key callback at action
    cases action
    exact ⟨name, argument, rfl⟩

/-- Cross-input operation respect transports the actual partial capture
and preserves the exact outcome tag used to select the continuation. -/
theorem encoded_call_respects {key : Key} {name : ops.Name key} {arg : ops.Argument key name}
    (respect : PaperObservationEquations.OperationRespects ops key (observe key).r)
    {input other output outcome : Scalar ops} {inverse : Scalar ops → Scalar ops}
    (inputs : TypedCoeffectReplay.ValueRelated observe input other)
    (called : encodeOperation ops key name arg input = .ok (output, inverse, outcome)) :
    ∃ output' inverse', encodeOperation ops key name arg other = .ok (output', inverse', outcome) ∧
      TypedCoeffectReplay.ValueRelated observe output output' ∧
      @Effects.Related (Scalar ops) (TypedCoeffectReplay.setoid observe) inverse inverse' := by
  obtain ⟨before, after, saved, result, rfl, actual, rfl, rfl, rfl⟩ := encoded_call_sound ops called
  have inputsAt := TypedCoeffectReplay.unpack_related observe key inputs
  rw [TypedCoeffectReplay.unpack_pack] at inputsAt
  cases decoded : unpack key other with
  | none => simp [decoded, OptionRel] at inputsAt
  | some before' =>
    rw [decoded] at inputsAt
    have compared := respect name arg before before' inputsAt
    rw [actual] at compared
    cases actual' : (ops.operation key name arg).run before' with
    | none => simp [actual', OptionRel] at compared
    | some triple =>
      obtain ⟨after', saved', result'⟩ := triple
      rw [actual'] at compared
      obtain ⟨states, maps, sameResult⟩ := compared
      change result = result' at sameResult
      subst result'
      rw [TypedCoeffectReplay.unpack_recognizes key other before' decoded]
      exact ⟨pack key after', encodeMap key saved', encoded_call_success ops actual',
        (TypedCoeffectReplay.packed_related observe key _ _).mpr states,
        fun {_ _} probes => TypedCoeffectReplay.encodeMap_related observe key maps _ _ probes⟩

section Simulation
open Calculus Stages
variable {Name Code : Type u} [DecidableEq Name]

/-- A paired landing of the same typed program selects the same code.
The provision and birth branches emit their original literal and draw. -/
theorem encoded_land_simulation (program : Code → Instruction Name ops Code)
    (respect : ∀ key, PaperObservationEquations.OperationRespects ops key (observe key).r)
    {actor : Name} {code : Code} {left middle right : RawRegistry Name ops Code}
    {inverse : Stages.Inverse Name Key (Scalar ops)} {next : Option Code}
    (sources : @StageSimulation.Related Name Key (Scalar ops) Code PUnit.{u + 1}
      (TypedCoeffectReplay.setoid observe) Eq left right)
    (landed : Stages.Land (encodeProgram program) actor code left middle inverse next) :
    ∃ middle' inverse', Stages.Land (encodeProgram program) actor code right middle' inverse' next ∧
      @StageSimulation.Related Name Key (Scalar ops) Code PUnit.{u + 1}
        (TypedCoeffectReplay.setoid observe) Eq middle middle' ∧
      @StageSimulation.InverseRelated Name Key (Scalar ops) (TypedCoeffectReplay.setoid observe) inverse inverse' := by
  letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
  cases landed with
  | unit _ _ _ action => exact ⟨_, _, .unit _ _ _ action, sources, .unit⟩
  | provide _ _ _ row key value action present declared absent =>
    obtain ⟨other, found, fields⟩ := StageSimulation.present_related sources actor row present
    exact ⟨_, _, .provide _ _ _ other key value action found
      (by simpa only [← fields.component.provides] using declared)
      ((GuardObservations.table_none_iff fields.observed key).mp absent),
      StageSimulation.write_related sources actor key (Setoid.refl value), .restrict actor key⟩
  | operate _ _ _ key call owner input output inverse outcome action located called =>
    obtain ⟨name, argument, rfl⟩ := encoded_operation_action ops program code action
    obtain ⟨input', located', inputs⟩ := GuardObservations.location_success sources.observed actor owner key input located
    obtain ⟨output', inverse', called', outputs, inverses⟩ := encoded_call_respects ops observe (respect key) inputs called
    exact ⟨_, _, .operate _ _ _ key _ owner input' output' inverse' outcome action located' called',
      StageSimulation.write_related sources owner key outputs, .operate owner key inverses⟩
  | instantiate _ _ _ component child action ready =>
    have fields : StageSimulation.ComponentRelated Eq component component := ⟨rfl, rfl, rfl⟩
    exact ⟨_, _, .instantiate _ _ _ component child action (StageSimulation.insertable_related sources child fields (some actor) ready),
      StageSimulation.put_related sources child (StageSimulation.fresh_related fields (some actor)), .retire child⟩

/-- Native steps of one typed program transport between structurally related
registries under the repaired cross-input operation contract. -/
theorem encoded_step_simulation (program : Code → Instruction Name ops Code)
    (respect : ∀ key, PaperObservationEquations.OperationRespects ops key (observe key).r)
    {rule : Labeled.Rule} {actor : Name} {left next right : RawRegistry Name ops Code}
    (sources : @StageSimulation.Related Name Key (Scalar ops) Code PUnit.{u + 1}
      (TypedCoeffectReplay.setoid observe) Eq left right)
    (step : Labeled.Step (encodeProgram program) rule actor left next) :
    ∃ next', Labeled.Step (encodeProgram program) rule actor right next' ∧
      @StageSimulation.Related Name Key (Scalar ops) Code PUnit.{u + 1}
        (TypedCoeffectReplay.setoid observe) Eq next next' := by
  letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
  refine StageSimulation.step_simulation_of_land ?_ (fun code => ⟨code, rfl⟩) sources step
  intro _ code code' _ _ _ _ selected same related landed
  subst code'
  obtain ⟨middle', inverse', native, states, inverses⟩ := encoded_land_simulation ops observe program respect related landed
  exact ⟨middle', inverse', selected, native, states, inverses, by cases selected <;> simp [OptionRel]⟩

end Simulation

/-- Actual inverse recovery comes from Definition 29. Respect of each
captured inverse comes from the identity foreign word in Definition 44. -/
theorem encoded_program_callbacks {Name Code : Type u}
    (program : Code → Instruction Name ops Code)
    (exactRecovery : PaperEffectEquations.ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops
      (PartialCoeffectIndependenceContracts.tableSetoid observe (fun _ => True)) key) :
    ∀ code, @CallbackWitness Name Key (Scalar ops) Code PUnit.{u+1} (TypedCoeffectReplay.setoid observe)
      (encodeProgram program) code := by
  intro code key callback action input output inverse outcome called
  obtain ⟨name, argument, rfl⟩ := encoded_operation_action ops program code action
  obtain ⟨before, after, saved, result, rfl, actual, rfl, rfl, rfl⟩ := encoded_call_sound ops called
  have recovered := exactRecovery key name argument before after saved result actual
  have respects := DependentCoeffectExchange.capture_respects ops observe key name argument
    (commutative key name name) actual
  refine ⟨?_, fun {_ _} probes => TypedCoeffectReplay.encodeMap_related observe key respects _ _ probes⟩
  rw [TypedCoeffectReplay.encodeMap_pack, recovered]
  exact (TypedCoeffectReplay.packed_related observe key _ _).mpr ((observe key).refl _)

/-- Definition 46 supplies the shared-key exchange for every pair of codes in
the encoded program. The two operations can return different outcome types. -/
theorem encoded_program_callback_pair {Name Code : Type u}
    (program : Code → Instruction Name ops Code)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops
      (PartialCoeffectIndependenceContracts.tableSetoid observe (fun _ => True)) key) :
    ∀ first second, @CallbackPair Name Key (Scalar ops) Code PUnit.{u+1} (TypedCoeffectReplay.setoid observe)
      (encodeProgram program) first second := by
  intro first second key left right leftAction rightAction
  obtain ⟨leftName, leftArg, rfl⟩ := encoded_operation_action ops program first leftAction
  obtain ⟨rightName, rightArg, rfl⟩ := encoded_operation_action ops program second rightAction
  exact encoded_callback_exchange ops observe key leftName rightName leftArg rightArg
    (commutative key leftName rightName)

end Cordis.TypedRegistry
