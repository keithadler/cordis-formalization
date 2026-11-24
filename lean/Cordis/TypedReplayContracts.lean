import Cordis.TypedCallbackExchange
import Cordis.PartialReplayRegistry

/-! Derive the partial replay contracts of Lemma 67 from Definitions 29, 44
and 46 with each key and operation's own types. -/
namespace Cordis.TypedReplayContracts

open PartialCoeffectLifting (PartialMap Table compose liftMap liftOperation forward)
open PartialInverseObservation (Operation MapRelated)
open PartialObservedMapClosure (Commutes)
open PartialCoeffectIndependenceContracts (OperationGenerator tableSetoid)
open PartialReplayHistory (KeyLaws)
open Iterators (OptionRel)
open Coeffects (update_same)
open TypedRegistry (Instruction Scalar encodeProgram encodeOperation)
open TypedCoeffectReplay (pack unpack encodeMap decodeInverse)
open PaperEffectEquations (CoeffectOperations ValueOperationWitness)

universe u
variable {Key : Type u} {Value : Key → Type u} [DecidableEq Key]

/-- Value-level forwards and every inverse produced by an actual successful
call, over all of the named coeffect's arguments. -/
def Generator (ops : CoeffectOperations Value) (key : Key) (map : PartialMap (Value key)) : Prop :=
  ∃ name argument, OperationGenerator (ops.operation key name argument) map

private theorem lift_compose (key : Key) (first second : PartialMap (Value key)) :
    liftMap key (compose second first) = compose (liftMap key second) (liftMap key first) := by
  funext table
  cases atKey : table key with
  | none => simp [liftMap, compose, atKey]
  | some value =>
    cases applied : first value with
    | none => simp [liftMap, compose, atKey, applied]
    | some output =>
      cases continued : second output <;>
        simp [liftMap, compose, atKey, applied, continued, PartialCoeffectLifting.update_overwrite]

private def head {Outcome : Type u} (key : Key) (operation : Operation (Value key) Outcome) :
    PartialIterators.Iterator (Table Value) :=
  PartialIterators.stage (liftOperation key operation) (fun _ => none)

private theorem lift_forward_eq {Outcome : Type u} (key : Key) (operation : Operation (Value key) Outcome) :
    forward (liftOperation key operation) = liftMap key (forward operation) := by
  funext table
  cases binding : table key with
  | none => simp [forward, liftOperation, liftMap, binding]
  | some value =>
    cases applied : operation.run value <;> simp [forward, liftOperation, liftMap, binding, applied]

private theorem lift_generator {Outcome : Type u} (key : Key)
    (operation : Operation (Value key) Outcome) {map : PartialMap (Value key)}
    (generator : OperationGenerator operation map) :
    PartialMapClosure.Generated (PartialMediatedIndependence.Generator (head key operation)) (liftMap key map) := by
  cases generator with
  | forward =>
    have forwardEq : PartialMediatedIndependence.forward (head key operation) = liftMap key (forward operation) := by
      funext table
      cases binding : table key with
      | none =>
        simp [PartialMediatedIndependence.forward, head, PartialIterators.stage, PartialIterators.Iterator.run,
          liftOperation, liftMap, binding]
      | some value =>
        cases applied : operation.run value <;>
          simp [PartialMediatedIndependence.forward, head, PartialIterators.stage, PartialIterators.Iterator.run,
            liftOperation, liftMap, forward, binding, applied]
    rw [← forwardEq]
    exact .generator (.forward .root)
  | inverse input output inverse result called =>
    exact .generator (.inverse .root (DependentCoeffectExchange.singleton key input)
      (DependentCoeffectExchange.singleton key output) _ none
      (DependentCoeffectExchange.stage_success key operation called))

private theorem compose_identity_left {S : Type u} (map : PartialMap S) : compose some map = map := by
  funext value
  cases after : map value <;> simp [compose, after]

private theorem compose_identity_right {S : Type u} (map : PartialMap S) : compose map some = map := rfl

/-- The stored key witness is a statement about lifted table maps. Testing
on singleton tables extracts both partial composition orderings at that
key. The monoid identity also extracts respect for each generator. -/
theorem key_laws (ops : CoeffectOperations Value) (observe : ∀ key, Setoid (Value key)) (key : Key)
    (witness : PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key) :
    KeyLaws (observe key) (Generator ops key) := by
  constructor
  · intro map
    rintro ⟨name, argument, generated⟩
    have independent := (witness name name).1 argument argument
    have related := independent.commute _ (lift_generator key _ generated) some .identity
    change MapRelated (tableSetoid observe (fun _ => True)).r
      (compose (liftMap key map) some) (compose some (liftMap key map)) at related
    rw [compose_identity_right, compose_identity_left] at related
    exact DependentCoeffectExchange.inverse_related_from_lift observe key related
  · intro first second
    rintro ⟨firstName, firstArg, firstGenerated⟩ ⟨secondName, secondArg, secondGenerated⟩
    have independent := (witness firstName secondName).1 firstArg secondArg
    have related := independent.commute _ (lift_generator key _ firstGenerated) _ (lift_generator key _ secondGenerated)
    change MapRelated (tableSetoid observe (fun _ => True)).r
      (compose (liftMap key first) (liftMap key second)) (compose (liftMap key second) (liftMap key first)) at related
    rw [← lift_compose, ← lift_compose] at related
    exact DependentCoeffectExchange.inverse_related_from_lift observe key related

/-- A defined forward or captured inverse cannot change another call's
outcome or the partial behavior of its saved inverse. This extracts the
two yield clauses of Definition 44 on the same dependent key. -/
theorem call_after_generator (ops : CoeffectOperations Value) (observe : ∀ key, Setoid (Value key))
    (key : Key) (witness : PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (name : ops.Name key) (argument : ops.Argument key name)
    {map : PartialMap (Value key)} (generated : Generator ops key map)
    {input changed output : Value key} {inverse : PartialMap (Value key)} {outcome : ops.Outcome key name}
    (moved : map input = some changed)
    (called : (ops.operation key name argument).run input = some (output, inverse, outcome)) :
    ∃ output' inverse',
      (ops.operation key name argument).run changed = some (output', inverse', outcome) ∧
      MapRelated (observe key).r inverse' inverse := by
  open DependentCoeffectExchange in
  {
    obtain ⟨foreignName, foreignArg, atom⟩ := generated
    let operation := ops.operation key name argument
    let foreignOp := ops.operation key foreignName foreignArg
    let singletonInput := singleton key input
    let singletonChanged := singleton key changed
    have movedTable : liftMap key map singletonInput = some singletonChanged := by
      simp [singletonInput, singletonChanged, DependentCoeffectExchange.singleton, liftMap, moved,
        PartialCoeffectLifting.update_overwrite]
    have foreignGenerator : OperationGenerator (liftOperation key foreignOp) (liftMap key map) := by
      cases atom with
      | forward =>
        rw [← lift_forward_eq]
        exact .forward
      | inverse before after saved result call =>
        exact .inverse (singleton key before) (singleton key after) _ result
          (lift_success key foreignOp call)
    have foreignMonoid : PaperObservationEquations.OperationMonoid ops key foreignName (liftMap key map) :=
      .generator ⟨foreignArg, foreignGenerator⟩
    have outcomeEq := (witness name foreignName).2.1 argument _ foreignMonoid _ _ movedTable
    rw [lift_success key operation called] at outcomeEq
    obtain ⟨output', inverse', replayed⟩ := lift_outcome key operation changed outcome outcomeEq
    have independent := (witness name foreignName).1 argument foreignArg
    change PartialObservedIteratorIndependence.Independent (tableSetoid observe (fun _ => True))
      (head key operation) (head key foreignOp) at independent
    have yielded := independent.left_yield (head key operation) .root _
      (lift_generator key foreignOp atom) _ _ movedTable
    have inverseEq : MapRelated (tableSetoid observe (fun _ => True)).r
        (liftMap key inverse') (liftMap key inverse) := by
      simpa [head, PartialIteratorRelationLaws.observe, PartialIteratorRelationLaws.YieldRel,
        OptionRel, singletonInput, singletonChanged, stage_success key operation called,
        stage_success key operation replayed] using yielded
    exact ⟨output', inverse', replayed, inverse_related_from_lift observe key inverseEq⟩
  }

/-- Defined replay of a word of same-key generators preserves the actual
operation outcome, and relates the two captured partial inverse maps. -/
theorem call_after_word (ops : CoeffectOperations Value) (observe : ∀ key, Setoid (Value key))
    (key : Key) (witness : PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (name : ops.Name key) (argument : ops.Argument key name)
    (word : List (PartialMap (Value key))) (valid : ∀ map ∈ word, Generator ops key map)
    {input changed output : Value key} {inverse : PartialMap (Value key)} {outcome : ops.Outcome key name}
    (moved : PartialReplayHistory.run word input = some changed)
    (called : (ops.operation key name argument).run input = some (output, inverse, outcome)) :
    ∃ output' inverse',
      (ops.operation key name argument).run changed = some (output', inverse', outcome) ∧
      MapRelated (observe key).r inverse' inverse := by
  induction word generalizing input output inverse with
  | nil =>
    have same : input = changed := Option.some.inj moved
    subst changed
    exact ⟨output, inverse, called,
      DependentCoeffectExchange.capture_respects ops observe key name argument (witness name name) called⟩
  | cons head tail ih =>
    rw [PartialReplayHistory.run_cons] at moved
    cases step : head input with
    | none => simp [step] at moved
    | some middle =>
      obtain ⟨value, saved, applied, first⟩ := call_after_generator ops observe key witness name argument
        (valid head List.mem_cons_self) step called
      obtain ⟨after, actual, replayed, later⟩ := ih
        (fun map member => valid map (List.mem_cons_of_mem _ member)) (by simpa only [step, Option.bind_some] using moved)
        applied
      refine ⟨after, actual, replayed, ?_⟩
      intro a b related
      exact OptionRel.trans (R := (observe key).r) (fun _ _ _ x y => (observe key).trans x y)
        (later a a ((observe key).refl _)) (first a b related)

private theorem packed_word_of_lifted (ops : CoeffectOperations Value) (key : Key)
    (word : List (PartialMap (Scalar ops)))
    (valid : ∀ map ∈ word, TypedCoeffectReplay.Lifted (Generator ops) key map)
    (input : Value key) {changed : Scalar ops}
    (moved : PartialReplayHistory.run word (pack key input) = some changed) :
    ∃ localWord adjusted, (∀ map ∈ localWord, Generator ops key map) ∧
      PartialReplayHistory.run localWord input = some adjusted ∧ changed = pack key adjusted := by
  induction word generalizing input with
  | nil => exact ⟨[], input, by simp, rfl, (Option.some.inj moved).symm⟩
  | cons head tail ih =>
    obtain ⟨valueMap, isGenerator, rfl⟩ := valid head List.mem_cons_self
    rw [PartialReplayHistory.run_cons, TypedCoeffectReplay.liftMap_pack] at moved
    cases stepped : valueMap input with
    | none => simp [stepped] at moved
    | some middle =>
      obtain ⟨localTail, adjusted, localValid, replayed, packed⟩ :=
        ih (fun map member => valid map (List.mem_cons_of_mem _ member)) middle
          (by simpa only [stepped, Option.map_some, Option.bind_some] using moved)
      exact ⟨valueMap :: localTail, adjusted, by
        intro map member
        rcases List.mem_cons.mp member with rfl | member
        · exact isGenerator
        · exact localValid map member,
        by simp only [PartialReplayHistory.run_cons, stepped, Option.bind_some, replayed], packed⟩

/-- Scalar encoding preserves the same-call replay result. The returned
inverse is compared as a partial function and as its registry representative. -/
theorem encoded_call_after_word (ops : CoeffectOperations Value) (observe : ∀ key, Setoid (Value key))
    {Name Code : Type u} (program : Code → Instruction Name ops Code)
    {key : Key} (witness : PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    {code : Code} {callback} (operation : (encodeProgram program code).action = .operate key callback)
    {word : List (PartialMap (Scalar ops))}
    (valid : ∀ map ∈ word, TypedCoeffectReplay.Lifted (Generator ops) key map)
    {input changed output outcome : Scalar ops} {inverse : Scalar ops → Scalar ops}
    (moved : PartialReplayHistory.run word input = some changed)
    (called : callback input = .ok (output, inverse, outcome)) :
    ∃ output' inverse', callback changed = .ok (output', inverse', outcome) ∧
      MapRelated (TypedCoeffectReplay.setoid (Yield := TypedRegistry.Yield ops) observe).r
        (decodeInverse key inverse') (decodeInverse key inverse) ∧
      @Effects.Related (Scalar ops) (TypedCoeffectReplay.setoid observe) inverse' inverse := by
  obtain ⟨name, argument, rfl⟩ := TypedRegistry.encoded_operation_action ops program code operation
  obtain ⟨value, after, original, result, rfl, actual, rfl, rfl, rfl⟩ :=
    TypedRegistry.encoded_call_sound ops called
  obtain ⟨localWord, adjusted, allowed, advanced, rfl⟩ := packed_word_of_lifted ops key word valid value moved
  obtain ⟨replayed, saved, call, related⟩ := call_after_word ops observe key witness name argument
    localWord allowed advanced actual
  refine ⟨pack key replayed, encodeMap key saved, by simp [encodeOperation, call], ?_, ?_⟩
  · rw [TypedCoeffectReplay.decode_encode, TypedCoeffectReplay.decode_encode]
    exact TypedCoeffectReplay.liftMap_related observe key related
  · intro a b observed
    exact TypedCoeffectReplay.encodeMap_related observe key related a b observed

private theorem forward_meaning (ops : CoeffectOperations Value) (key : Key) (name : ops.Name key)
    (argument : ops.Argument key name) :
    (fun input => (encodeOperation ops key name argument input).toOption.map Prod.fst) =
      TypedCoeffectReplay.liftMap key (forward (ops.operation key name argument)) := by
  funext input
  cases decoded : unpack key input with
  | none => simp [encodeOperation, TypedCoeffectReplay.liftMap, decoded, Except.toOption]
  | some value =>
    cases called : (ops.operation key name argument).run value <;>
      simp [encodeOperation, TypedCoeffectReplay.liftMap, decoded, called, Except.toOption, forward]

/-- Definitions 29 and 46 supply the entire scalar replay contract for the
encoded program. Its actual successful forwards and inverses retain their
dependent types and their genuine partial domains. -/
def coeffects (ops : CoeffectOperations Value) (observe : ∀ key, Setoid (Value key)) {Name Code : Type u}
    [DecidableEq Name] (program : Code → Instruction Name ops Code)
    (recovery : ValueOperationWitness ops)
    (witness : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key) :
    PartialReplayRegistry.Coeffects (encodeProgram program) where
  denote := decodeInverse
  agrees := TypedCoeffectReplay.decodeInverse_agrees
  admitted := TypedCoeffectReplay.Lifted (Generator ops)
  observe := fun _ => TypedCoeffectReplay.setoid observe
  laws := fun key => TypedCoeffectReplay.lift_key_laws observe (Generator ops) key (key_laws ops observe key (witness key))
  captured := by
    intro code key callback action before output inverse result called
    obtain ⟨name, argument, rfl⟩ := TypedRegistry.encoded_operation_action ops program code action
    obtain ⟨input, after, saved, outcome, rfl, performed, rfl, rfl, rfl⟩ :=
      TypedRegistry.encoded_call_sound ops called
    have recovered := recovery key name argument input after saved outcome performed
    constructor
    · exact ⟨saved, ⟨name, argument, .inverse input after saved outcome performed⟩, TypedCoeffectReplay.decode_encode key saved⟩
    · rw [TypedCoeffectReplay.decode_encode, TypedCoeffectReplay.liftMap_pack, recovered, Option.map_some]
  forward := by
    intro code key callback action
    obtain ⟨name, argument, rfl⟩ := TypedRegistry.encoded_operation_action ops program code action
    exact ⟨_, ⟨name, argument, .forward⟩, forward_meaning ops key name argument⟩

end Cordis.TypedReplayContracts
