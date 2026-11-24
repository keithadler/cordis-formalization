import Cordis.Repairs.CompatibleProvision
import Cordis.TypedRegistryFrame

/-!
Component- and interface-indexed operations for the amended Lemma 57. Both the
acting component and the provider selected by its bound interface are fixed.
The observable relation is still only the paper's coeffect-table relation.
The forward operation and its captured inverse retain their partial domains.
-/
namespace Cordis.Repairs.BoundOperation
open TypedRegistry
open PaperEffectEquations (CoeffectOperations)
open PartialInverseObservation (Operation Witnessed MapRelated)
open PartialCoeffectLifting (PartialMap)
open Iterators (OptionRel)
universe u
variable {Name Key Code : Type u} {V : Key → Type u}
variable [DecidableEq Name] [DecidableEq Key]
variable (ops : CoeffectOperations V)
local notation "R" => Registry Name V Code

def Compatible (actor : Name) (acting : Calculus.Component Key Code)
    (owner : Name) (providing : Calculus.Component Key Code) (key : Key) (state : R) : Prop :=
  CompatibleProvision.Compatible ops actor acting state ∧ CompatibleProvision.Compatible ops owner providing state ∧
    bindingOwner state actor key = some owner

abbrev Gamma (actor : Name) (acting : Calculus.Component Key Code)
    (owner : Name) (providing : Calculus.Component Key Code) (key : Key) :=
  {state : R // Compatible ops actor acting owner providing key state}

variable {ops} {actor owner : Name} {acting providing : Calculus.Component Key Code} {key : Key}
local notation "G" => Gamma ops actor acting owner providing key

def providerState (state : G) : CompatibleProvision.Gamma ops owner providing := ⟨state.val, state.property.2.1⟩

theorem write_bindingOwner (state : R) (target user : Name) (changed selected : Key)
    (value : Option (V changed)) :
    bindingOwner (write state target changed value) user selected = bindingOwner state user selected := by
  by_cases same : user = target
  · subst user
    cases present : state target <;> simp [bindingOwner, write, TypedRegistry.modify, present]
  · simp [bindingOwner, write, TypedRegistry.modify, same]

def setSlot (provided : providing.provides key = true) (value : Option (V key)) (state : G) : G := by
  let changed := CompatibleProvision.setSlot key provided value (providerState state)
  refine ⟨changed.val, ⟨?_, changed.property, ?_⟩⟩
  · refine ⟨changed.property.1, ?_⟩
    obtain ⟨fiber, present, component⟩ := state.property.1.2
    by_cases same : actor = owner
    · subst actor
      refine ⟨{fiber with table := fun k => if h : key = k then h ▸ value else fiber.table k}, ?_, component⟩
      simp [changed, CompatibleProvision.setSlot_value, providerState, write, TypedRegistry.modify, present]
    · exact ⟨fiber, by simpa [changed, CompatibleProvision.setSlot_value, providerState, write, TypedRegistry.modify, same]
          using present, component⟩
  · exact (write_bindingOwner state.val owner actor key key value).trans state.property.2.2

@[simp] theorem setSlot_value (provided : providing.provides key = true)
    (value : Option (V key)) (state : G) :
    (setSlot provided value state).val = write state.val owner key value := rfl

theorem slot_self (provided : providing.provides key = true)
    (value : Option (V key)) (state : G) :
    tableAt (setSlot provided value state).val owner key = value :=
  CompatibleProvision.slot_self key provided value (providerState state)

def Observed (observe : ∀ key, Setoid (V key)) (keys : Key → Prop) (left right : G) : Prop :=
  TypedStateObservation.TablesRelatedAt observe keys left.val right.val

theorem observed_slot (observe : ∀ key, Setoid (V key)) (keys : Key → Prop)
    (selected : keys key) (provided : providing.provides key = true)
    {left right : G} (related : Observed observe keys left right) :
    OptionRel (observe key).r (tableAt left.val owner key) (tableAt right.val owner key) :=
  CompatibleProvision.observed_slot observe keys key selected provided
    (left := providerState left) (right := providerState right) related

theorem setSlot_related (observe : ∀ key, Setoid (V key)) (keys : Key → Prop)
    (provided : providing.provides key = true) {left right : G}
    (related : Observed observe keys left right) {a b : Option (V key)}
    (values : OptionRel (observe key).r a b) :
    Observed observe keys (setSlot provided a left) (setSlot provided b right) :=
  CompatibleProvision.setSlot_related observe keys key provided
    (left := providerState left) (right := providerState right) related values

theorem setSlot_overwrite (provided : providing.provides key = true)
    (a b : Option (V key)) (state : G) :
    setSlot provided b (setSlot provided a state) = setSlot provided b state := by
  apply Subtype.ext
  exact congrArg (fun state : CompatibleProvision.Gamma ops owner providing => state.val)
    (CompatibleProvision.setSlot_overwrite key provided a b (providerState state))

theorem setSlot_current (provided : providing.provides key = true) (state : G) :
    setSlot provided (tableAt state.val owner key) state = state := by
  apply Subtype.ext
  exact congrArg (fun state : CompatibleProvision.Gamma ops owner providing => state.val)
    (CompatibleProvision.setSlot_current key provided (providerState state))

def liftMap (provided : providing.provides key = true) (transform : PartialMap (V key)) : PartialMap G :=
  fun state => do
    let value ← tableAt state.val owner key
    let changed ← transform value
    pure (setSlot provided (some changed) state)

def liftOperation {Outcome : Type u} (provided : providing.provides key = true)
    (operation : Operation (V key) Outcome) : Operation G Outcome where
  run state := do
    let value ← tableAt state.val owner key
    let (changed, inverse, outcome) ← operation.run value
    pure (setSlot provided (some changed) state, liftMap provided inverse, outcome)

theorem liftMap_related (observe : ∀ key, Setoid (V key)) (keys : Key → Prop)
    (selected : keys key) (provided : providing.provides key = true)
    {first second : PartialMap (V key)} (maps : MapRelated (observe key).r first second) :
    MapRelated (Observed (ops := ops) (actor := actor) (acting := acting) (owner := owner)
      observe keys) (liftMap provided first) (liftMap provided second) := by
  intro left right related
  have values := observed_slot observe keys selected provided related
  cases a : tableAt left.val owner key with
  | none => cases b : tableAt right.val owner key <;> simp_all [OptionRel, liftMap]
  | some av =>
    cases b : tableAt right.val owner key with
    | none => simp_all [OptionRel]
    | some bv =>
      have initial : (observe key).r av bv := by simpa only [a, b, OptionRel] using values
      have changed := maps av bv initial
      cases fa : first av with
      | none => cases fb : second bv <;> simp_all [OptionRel, liftMap]
      | some ac =>
        cases fb : second bv with
        | none => simp_all [OptionRel]
        | some bc =>
          have output : (observe key).r ac bc := by simpa only [fa, fb, OptionRel] using changed
          simpa [liftMap, a, b, fa, fb, OptionRel] using
            setSlot_related observe keys provided related (a := some ac) (b := some bc) output

theorem operation_success_iff {Outcome : Type u} (provided : providing.provides key = true)
    (operation : Operation (V key) Outcome) (input output : G) (inverse : PartialMap G) (outcome : Outcome) :
    (liftOperation provided operation).run input = some (output, inverse, outcome) ↔
      ∃ before after saved, tableAt input.val owner key = some before ∧
        operation.run before = some (after, saved, outcome) ∧
        output = setSlot provided (some after) input ∧ inverse = liftMap provided saved := by
  constructor
  · intro success
    cases binding : tableAt input.val owner key with
    | none => simp [liftOperation, binding] at success
    | some before =>
      cases called : operation.run before with
      | none => simp [liftOperation, binding, called] at success
      | some result =>
        obtain ⟨after, saved, result⟩ := result
        have same : setSlot provided (some after) input = output ∧
            liftMap provided saved = inverse ∧ result = outcome := by
          simpa [liftOperation, binding, called, Prod.mk.injEq] using success
        obtain ⟨rfl, rfl, rfl⟩ := same
        exact ⟨before, after, saved, rfl, called, rfl, rfl⟩
  · rintro ⟨before, after, saved, binding, called, rfl, rfl⟩
    simp [liftOperation, binding, called]

theorem operation_respects {Outcome : Type u} (observe : ∀ key, Setoid (V key)) (keys : Key → Prop)
    (selected : keys key) (provided : providing.provides key = true)
    (operation : Operation (V key) Outcome) (witness : Witnessed operation (observe key).r) :
    ∀ left right : G, Observed observe keys left right →
      OptionRel (fun a b => Observed observe keys a.1 b.1 ∧
        MapRelated (Observed observe keys) a.2.1 b.2.1 ∧ a.2.2 = b.2.2)
        ((liftOperation provided operation).run left) ((liftOperation provided operation).run right) := by
  intro left right related
  have values := observed_slot observe keys selected provided related
  cases a : tableAt left.val owner key with
  | none => cases b : tableAt right.val owner key <;> simp_all [OptionRel, liftOperation]
  | some av =>
    cases b : tableAt right.val owner key with
    | none => simp_all [OptionRel]
    | some bv =>
      have initial : (observe key).r av bv := by simpa only [a, b, OptionRel] using values
      have changed := witness.respect av bv initial
      cases fa : operation.run av with
      | none => cases fb : operation.run bv <;> simp_all [OptionRel, liftOperation]
      | some ac =>
        cases fb : operation.run bv with
        | none => simp_all [OptionRel]
        | some bc =>
          obtain ⟨outputs, inverses, outcomes⟩ := (show (observe key).r ac.1 bc.1 ∧
            MapRelated (observe key).r ac.2.1 bc.2.1 ∧ ac.2.2 = bc.2.2 by
              simpa only [fa, fb, OptionRel] using changed)
          simpa [liftOperation, a, b, fa, fb, OptionRel] using
            And.intro (setSlot_related observe keys provided related
              (a := some ac.1) (b := some bc.1) outputs)
              (And.intro (liftMap_related observe keys selected provided inverses) outcomes)

omit [DecidableEq Name] in
theorem observed_refl (observe : ∀ key, Setoid (V key)) (keys : Key → Prop) (state : G) :
    Observed observe keys state state := by
  intro other _
  exact ⟨fun n v found => ⟨n, v, found, (observe other).refl v⟩,
    fun n v found => ⟨n, v, found, (observe other).refl v⟩⟩

/-- No exact scalar recovery is assumed: the paper's observational scalar
witness suffices for observational recovery of the entire registry. -/
theorem operation_witnessed {Outcome : Type u} (observe : ∀ key, Setoid (V key)) (keys : Key → Prop)
    (selected : keys key) (provided : providing.provides key = true)
    (operation : Operation (V key) Outcome) (witness : Witnessed operation (observe key).r) :
    Witnessed (liftOperation (ops := ops) (actor := actor) (acting := acting) (owner := owner)
      provided operation) (Observed observe keys) := by
  refine ⟨?_, operation_respects observe keys selected provided operation witness⟩
  intro input output inverse outcome called
  obtain ⟨before, after, saved, binding, original, rfl, rfl⟩ :=
    (operation_success_iff provided operation input output inverse outcome).mp called
  obtain ⟨restored, recovered, values⟩ := witness.recover before after saved outcome original
  refine ⟨setSlot provided (some restored) input, ?_, ?_⟩
  · simp only [liftMap, slot_self]
    simp [recovered, setSlot_overwrite]
  · have related := setSlot_related observe keys provided (observed_refl observe keys input)
      (a := some restored) (b := some before) values
    rwa [← binding, setSlot_current] at related

theorem operation_exact_recovery {Outcome : Type u} (provided : providing.provides key = true)
    (operation : Operation (V key) Outcome)
    (exactRecovery : ∀ before after inverse outcome,
      operation.run before = some (after, inverse, outcome) → inverse after = some before)
    (input output : G) (inverse : PartialMap G) (outcome : Outcome)
    (called : (liftOperation provided operation).run input = some (output, inverse, outcome)) :
    inverse output = some input := by
  obtain ⟨before, after, saved, binding, original, rfl, rfl⟩ :=
    (operation_success_iff provided operation input output inverse outcome).mp called
  simp only [liftMap, slot_self]
  simp [exactRecovery before after saved outcome original, setSlot_overwrite]
  rw [← binding, setSlot_current]

/-- The scoped forward agrees with the actual registry primitive, including
the provider identity stored in the inverse and the outcome-selected tail. -/
theorem operation_is_land (provided : providing.provides key = true)
    (program : Code → Instruction Name ops Code) (code : Code)
    (operation : ops.Name key) (argument : ops.Argument key operation)
    (action : (program code).action = .operate key operation argument)
    (state : G) (before after : V key) (inverse : PartialMap (V key))
    (outcome : ops.Outcome key operation)
    (binding : tableAt state.val owner key = some before)
    (called : (ops.operation key operation argument).run before = some (after, inverse, outcome)) :
    Land program actor code state.val (setSlot provided (some after) state).val
      (.operate owner key inverse) ((program code).next (.operation key operation outcome)) := by
  apply Land.operate state.val actor code key operation argument owner before after inverse outcome action
  · simp [location, state.property.2.2, binding]
  · exact called

theorem undo_operate_success (state : R) (before after : V key) (inverse : PartialMap (V key))
    (binding : tableAt state owner key = some before) (called : inverse before = some after) :
    undo (.operate owner key inverse) state = write state owner key (some after) := by
  obtain ⟨fiber, present, binding⟩ := Option.bind_eq_some_iff.mp binding
  funext name
  by_cases same : name = owner
  · subst name
    simp [undo, write, TypedRegistry.modify, present, binding, called]
  · simp [undo, write, TypedRegistry.modify, same]

/-- Undefined inverse probes remain undefined. On every successful probe the
scoped inverse is the very same captured native token, not a reconstructed undo. -/
theorem liftMap_agrees_undo (provided : providing.provides key = true)
    (inverse : PartialMap (V key)) (input output : G)
    (called : liftMap provided inverse input = some output) :
    output.val = undo (.operate owner key inverse) input.val := by
  cases binding : tableAt input.val owner key with
  | none => simp [liftMap, binding] at called
  | some before =>
    cases applied : inverse before with
    | none => simp [liftMap, binding, applied] at called
    | some after =>
      have same : setSlot provided (some after) input = output := by
        simpa [liftMap, binding, applied] using called
      subst output
      exact (undo_operate_success input.val before after inverse binding applied).symm

theorem setSlot_frame (provided : providing.provides key = true)
    (value : Option (V key)) (state : G) :
    (∀ name, name ≠ owner → (setSlot provided value state).val name = state.val name) ∧
    ∀ fiber, state.val owner = some fiber →
      ∃ result, (setSlot provided value state).val owner = some result ∧
        result.component = fiber.component ∧ result.parent = fiber.parent ∧
        result.retired = fiber.retired ∧ result.phase = fiber.phase :=
  CompatibleProvision.setSlot_frame key provided value (providerState state)

private theorem step_route {program : Code → Instruction Name ops Code}
    {rule : Labeled.Rule} {byActor : Name} {before after : R}
    (step : Step program rule byActor before after)
    (old : Compatible ops actor acting owner providing key before)
    (new : CompatibleProvision.Compatible ops actor acting after)
    (installedBefore : viewAt before actor ≠ none) (installedAfter : viewAt after actor ≠ none) :
    bindingOwner after actor key = some owner := by
  obtain ⟨first, firstAt, firstComponent⟩ := old.1.2
  obtain ⟨second, secondAt, secondComponent⟩ := new.2
  have route := old.2.2
  cases firstView : first.phase.committed with
  | none => simp [viewAt, firstAt, firstView] at installedBefore
  | some v =>
    cases secondView : second.phase.committed with
    | none => simp [viewAt, secondAt, secondView] at installedAfter
    | some w =>
      have views := Ordering.step_views_stable (encodeProgram program) (encode_step step).toCalculus
        actor (encodeFiber ops first) (encodeFiber ops second) v w (encode_row firstAt) (encode_row secondAt)
        (by simpa [encodeFiber] using firstView) (by simpa [encodeFiber] using secondView)
      simpa [bindingOwner, firstAt, secondAt, firstComponent, secondComponent,
        firstView, secondView, views] using route


/-- During an installed interval native rules keep the bound route constant.
Continuous presence of the provider keeps the same component in scope. -/
theorem step_compatible {program : Code → Instruction Name ops Code}
    {rule : Labeled.Rule} {byActor : Name} {before after : R}
    (step : Step program rule byActor before after)
    (old : Compatible ops actor acting owner providing key before)
    (installedBefore : viewAt before actor ≠ none) (installedAfter : viewAt after actor ≠ none)
    (providerRetained : after owner ≠ none) :
    Compatible ops actor acting owner providing key after := by
  have actorRetained : after actor ≠ none := by
    intro absent
    simp [viewAt, absent] at installedAfter
  have actingAfter := CompatibleProvision.step_compatible step old.1 actorRetained
  exact ⟨actingAfter, CompatibleProvision.step_compatible step old.2.1 providerRetained,
    step_route step old actingAfter installedBefore installedAfter⟩

/-- An own provision only needs actor presence. A foreign dependency is
backed by the ordinary retained-provider invariant, including while its
consumer is unloading. -/
theorem route_retains_owner {state : R} (compatible : CompatibleProvision.Compatible ops actor acting state)
    (route : bindingOwner state actor key = some owner)
    (supported : Ordering.Supported (encodeRegistry ops state)) :
    state owner ≠ none := by
  obtain ⟨fiber, present, _⟩ := compatible.2
  by_cases own : fiber.component.provides key = true
  · have same : actor = owner := by simpa [bindingOwner, present, own] using route
    subst owner
    simp [present]
  · by_cases required : fiber.component.requires key = true
    · cases found : fiber.phase.committed with
      | none => simp [bindingOwner, present, own, required, found] at route
      | some view =>
        have selects : view key = owner := by simp [bindingOwner, present, own, required, found] at route; exact route
        obtain ⟨_, provider, foundProvider, _, _⟩ := Ordering.retained_provider
          (encodeRegistry ops state) actor (encodeFiber ops fiber) view key supported (encode_row present)
          (by simpa [encodeFiber] using found) required
        obtain ⟨_, native, _⟩ := encodeRegistry_some ops foundProvider
        rw [selects] at native
        simp [native]
    · simp [bindingOwner, present, own, required] at route

theorem trace_compatible {program : Code → Instruction Name ops Code} {initial : R} {last : Nat}
    (trace : Trace program initial last) (first final : Nat) (ordered : first ≤ final)
    (bounded : final ≤ last)
    (initialCompatible : Compatible ops actor acting owner providing key (trace.state first))
    (installed : ∀ time, first ≤ time → time ≤ final → viewAt (trace.state time) actor ≠ none)
    (retained : ∀ time, first ≤ time → time ≤ final → trace.state time owner ≠ none) :
    Compatible ops actor acting owner providing key (trace.state final) := by
  induction final with
  | zero =>
    have same : first = 0 := by omega
    simpa only [same] using initialCompatible
  | succ time ih =>
    by_cases same : first = time + 1
    · simpa only [same] using initialCompatible
    · have previous := ih (by omega) (by omega)
        (fun t lower upper => installed t lower (by omega))
        (fun t lower upper => retained t lower (by omega))
      exact step_compatible (trace.step time bounded) previous
        (installed time (by omega) (by omega)) (installed (time + 1) ordered (Nat.le_refl _))
        (retained (time + 1) ordered (Nat.le_refl _))

/-- On an empty-origin trace, the installed interval suffices to keep every
successive operation in the same bound domain. Provider presence follows
from retained-provider support on the actual trace. -/
theorem trace_compatible_from_installed {program : Code → Instruction Name ops Code} {last : Nat}
    (trace : Trace program (fun _ => none) last) (first final : Nat) (ordered : first ≤ final)
    (bounded : final ≤ last)
    (initialCompatible : Compatible ops actor acting owner providing key (trace.state first))
    (installed : ∀ time, first ≤ time → time ≤ final → viewAt (trace.state time) actor ≠ none) :
    Compatible ops actor acting owner providing key (trace.state final) := by
  induction final with
  | zero =>
    have same : first = 0 := by omega
    simpa only [same] using initialCompatible
  | succ time ih =>
    by_cases same : first = time + 1
    · simpa only [same] using initialCompatible
    · have old := ih (by omega) (by omega) (fun t lo hi => installed t lo (by omega))
      have step := trace.step time bounded
      have earlier := installed time (by omega) (by omega)
      have current := installed (time + 1) ordered (Nat.le_refl _)
      have actorPresent : trace.state (time + 1) actor ≠ none := by
        intro absent
        simp [viewAt, absent] at current
      have actingAfter := CompatibleProvision.step_compatible step old.1 actorPresent
      have route := step_route step old actingAfter earlier current
      have rawRun := trace.encode.prefixRun (time + 1) bounded
      have supported := (WellFormed.run_invariants (encodeProgram program) rawRun
        (by simp [encodeRegistry, Safety.ParentClosed])
        (show WellFormed.Disjoint (fun _ => none : RawRegistry Name ops Code) from WellFormed.disjoint_empty)
        (by simpa [encodeRegistry] using
          (And.intro Ordering.supported_empty Ordering.local_empty :
            Ordering.Invariant (fun _ => none : RawRegistry Name ops Code)))).2.2.1
      exact ⟨actingAfter, CompatibleProvision.step_compatible step old.2.1
        (route_retains_owner actingAfter route supported), route⟩

end Cordis.Repairs.BoundOperation
