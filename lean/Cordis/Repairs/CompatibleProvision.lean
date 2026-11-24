import Cordis.MediatedRegistryDomain
import Cordis.TypedRegistrySupport
import Cordis.TypedStateObservation
import Cordis.PartialCoeffectProvision
import Cordis.PartialReachMediatedWitness

/-!
The accepted domain repair of the global provision obstruction. A witness is
relative to a present actor and its fixed component. Other registry entries,
tables and phases remain variable. The domain contains finite rooted, owned,
disjoint registries; the relation still observes only Definition 51's tables.
Provision and its restriction inverse retain their actual partial domains.
-/
namespace Cordis.Repairs.CompatibleProvision
open TypedRegistry
open PaperEffectEquations (CoeffectOperations)
open TypedStateObservation (TablesRelatedAt)
open PartialInverseObservation (Operation Witnessed MapRelated)
open PartialCoeffectLifting (PartialMap)
open Iterators (OptionRel)
universe u
variable {Name Key Code : Type u} {V : Key → Type u}
variable [DecidableEq Name] [DecidableEq Key]
variable (ops : CoeffectOperations V)
local notation "R" => Registry Name V Code
local notation "F" => Fiber Name V Code

def Allowed (state : R) : Prop := MediatedRegistry.Allowed (encodeRegistry ops state)

def Compatible (actor : Name) (component : Calculus.Component Key Code) (state : R) : Prop :=
  Allowed ops state ∧ ∃ fiber, state actor = some fiber ∧ fiber.component = component

abbrev Gamma (actor : Name) (component : Calculus.Component Key Code) :=
  {state : R // Compatible ops actor component state}

variable {ops} {actor : Name} {component : Calculus.Component Key Code}

theorem empty_allowed : Allowed ops (fun _ => none : R) :=
  ⟨Safety.empty_tree, ⟨[], fun _ _ absent => by cases absent⟩,
    Safety.empty_owned, WellFormed.disjoint_empty⟩

theorem step_allowed {program : Code → Instruction Name ops Code}
    {rule : Labeled.Rule} {owner : Name} {before after : R}
    (step : Step program rule owner before after) (old : Allowed ops before) : Allowed ops after :=
  MediatedRegistry.step_allowed (encodeProgram program) (encode_step step).toCalculus old

/-- Compatibility is preserved by every actual rule while this actor remains
present. This does not freeze the other entries or the actor's lifecycle. -/
theorem step_compatible {program : Code → Instruction Name ops Code}
    {rule : Labeled.Rule} {owner : Name} {before after : R}
    (step : Step program rule owner before after) (old : Compatible ops actor component before)
    (retained : after actor ≠ none) : Compatible ops actor component after := by
  refine ⟨step_allowed step old.1, ?_⟩
  obtain ⟨fiber, found, same⟩ := old.2
  cases present : after actor with
  | none => exact False.elim (retained present)
  | some result =>
    have stable := Frame.step_stable (encodeProgram program) (encode_step step).toCalculus
      actor (encodeFiber ops fiber) (encodeFiber ops result) (encode_row found) (encode_row present)
    exact ⟨result, rfl, stable.1.symm.trans same⟩

/-- Every state in an actual finite execution has the structural invariants
used by the repaired domain, independently of any semantic witness. -/
theorem trace_allowed {program : Code → Instruction Name ops Code} {initial : R} {last : Nat}
    (trace : Trace program initial last) (initialAllowed : Allowed ops initial)
    (time : Nat) (bounded : time ≤ last) : Allowed ops (trace.state time) := by
  induction time with
  | zero => simpa only [trace.start] using initialAllowed
  | succ time ih => exact step_allowed (trace.step time bounded) (ih (by omega))

/-- A replay stays in the same component domain throughout a continuous
residency interval. This applies to arbitrary actors' intervening rules. A
removal and later reuse of the name must start a new interval. -/
theorem trace_compatible {program : Code → Instruction Name ops Code} {initial : R} {last : Nat}
    (trace : Trace program initial last) (first final : Nat) (ordered : first ≤ final)
    (bounded : final ≤ last) (initialCompatible : Compatible ops actor component (trace.state first))
    (retained : ∀ time, first ≤ time → time ≤ final → trace.state time actor ≠ none) :
    Compatible ops actor component (trace.state final) := by
  induction final with
  | zero =>
    have same : first = 0 := by omega
    simpa only [same] using initialCompatible
  | succ time ih =>
    by_cases same : first = time + 1
    · simpa only [same] using initialCompatible
    · have previous := ih (by omega) (by omega) (fun t lower upper => retained t lower (by omega))
      exact step_compatible (trace.step time bounded) previous (retained (time + 1) ordered (Nat.le_refl _))

theorem write_allowed {state : R} (old : Allowed ops state) (owner : Name) (key : Key)
    (value : Option (V key))
    (declared : ∀ fiber, state owner = some fiber → value ≠ none → fiber.component.provides key = true) :
    Allowed ops (write state owner key value) := by
  unfold Allowed MediatedRegistry.Allowed at old ⊢
  rw [encode_write]
  refine ⟨Safety.modify_tree _ owner _ (fun _ => rfl) old.1,
    SupportUniqueness.modify_finite _ owner _ old.2.1,
    Safety.write_owned _ owner key _ old.2.2.1 ?_,
    WellFormed.modify_disjoint _ owner _ (fun _ => rfl) old.2.2.2⟩
  intro raw found nonempty
  obtain ⟨fiber, present, rfl⟩ := encodeRegistry_some ops found
  exact declared fiber present (by intro absent; simp [absent] at nonempty)

def setSlot (key : Key) (provided : component.provides key = true)
    (value : Option (V key)) (state : Gamma ops actor component) : Gamma ops actor component := by
  refine ⟨write state.val actor key value, ?_⟩
  obtain ⟨fiber, present, same⟩ := state.property.2
  refine ⟨write_allowed state.property.1 actor key value ?_, ?_⟩
  · intro other found _
    have equal := Option.some.inj (found.symm.trans present)
    subst other
    simpa [same] using provided
  · refine ⟨{fiber with table := fun k => if h : key = k then h ▸ value else fiber.table k}, ?_, same⟩
    simp [write, TypedRegistry.modify, present]

@[simp] theorem setSlot_value (key : Key) (provided : component.provides key = true)
    (value : Option (V key)) (state : Gamma ops actor component) :
    (setSlot key provided value state).val = write state.val actor key value := rfl

theorem slot_self (key : Key) (provided : component.provides key = true)
    (value : Option (V key)) (state : Gamma ops actor component) :
    tableAt (setSlot key provided value state).val actor key = value := by
  obtain ⟨fiber, present, _⟩ := state.property.2
  simp [setSlot_value, tableAt, write, TypedRegistry.modify, present]

theorem slot_other (key other : Key) (different : key ≠ other)
    (provided : component.provides key = true) (value : Option (V key))
    (state : Gamma ops actor component) (owner : Name) :
    tableAt (setSlot key provided value state).val owner other = tableAt state.val owner other := by
  by_cases same : owner = actor
  · subst owner
    obtain ⟨fiber, present, _⟩ := state.property.2
    simp [setSlot_value, tableAt, write, TypedRegistry.modify, present, different]
  · simp [setSlot_value, tableAt, write, TypedRegistry.modify, same]

theorem binding_owner (state : Gamma ops actor component) (key : Key)
    (provided : component.provides key = true) (owner : Name) (value : V key)
    (bound : tableAt state.val owner key = some value) : owner = actor := by
  obtain ⟨fiber, present, bound⟩ := Option.bind_eq_some_iff.mp bound
  obtain ⟨acting, actorAt, same⟩ := state.property.2
  have owns : fiber.component.provides key = true := state.property.1.2.2.1
    owner (encodeFiber ops fiber) key (encode_row present) (by simp [encodeFiber, bound])
  by_cases equal : owner = actor
  · exact equal
  · exact False.elim (state.property.1.2.2.2 actor owner (encodeFiber ops acting) (encodeFiber ops fiber)
      (encode_row actorAt) (encode_row present) (Ne.symm equal) key
      ⟨by simpa [encodeFiber, same] using provided, owns⟩)

def Observed (observe : ∀ key, Setoid (V key)) (keys : Key → Prop)
    (left right : Gamma ops actor component) : Prop :=
  TablesRelatedAt observe keys left.val right.val

theorem observed_slot (observe : ∀ key, Setoid (V key)) (keys : Key → Prop)
    (key : Key) (selected : keys key) (provided : component.provides key = true)
    {left right : Gamma ops actor component} (related : Observed observe keys left right) :
    OptionRel (observe key).r (tableAt left.val actor key) (tableAt right.val actor key) := by
  obtain ⟨forward, backward⟩ := related key selected
  cases a : tableAt left.val actor key with
  | none =>
    cases b : tableAt right.val actor key with
    | none => trivial
    | some value =>
      obtain ⟨owner, other, bound, _⟩ := backward actor value b
      rw [binding_owner left key provided owner other bound, a] at bound
      cases bound
  | some value =>
    obtain ⟨owner, other, bound, values⟩ := forward actor value a
    rw [binding_owner right key provided owner other bound] at bound
    rw [bound]
    exact values

theorem setSlot_related (observe : ∀ key, Setoid (V key)) (keys : Key → Prop)
    (key : Key) (provided : component.provides key = true)
    {left right : Gamma ops actor component} (related : Observed observe keys left right)
    {a b : Option (V key)} (values : OptionRel (observe key).r a b) :
    Observed observe keys (setSlot key provided a left) (setSlot key provided b right) := by
  intro other selected
  by_cases same : key = other
  · subst other
    constructor
    · intro owner value bound
      rw [binding_owner _ key provided owner value bound, slot_self] at bound
      cases a with
      | none => cases bound
      | some av =>
        cases b with
        | none => exact False.elim values
        | some bv =>
          have equal := Option.some.inj bound
          subst value
          exact ⟨actor, bv, slot_self _ _ _ _, values⟩
    · intro owner value bound
      rw [binding_owner _ key provided owner value bound, slot_self] at bound
      cases b with
      | none => cases bound
      | some bv =>
        cases a with
        | none => exact False.elim values
        | some av =>
          have equal := Option.some.inj bound
          subst value
          exact ⟨actor, av, slot_self _ _ _ _, values⟩
  · have old := related other selected
    constructor
    · intro owner value bound
      rw [slot_other key other same] at bound
      obtain ⟨target, result, found, values⟩ := old.1 owner value bound
      exact ⟨target, result, (slot_other key other same _ _ _ _).trans found, values⟩
    · intro owner value bound
      rw [slot_other key other same] at bound
      obtain ⟨target, result, found, values⟩ := old.2 owner value bound
      exact ⟨target, result, (slot_other key other same _ _ _ _).trans found, values⟩

def restrict (key : Key) (provided : component.provides key = true) : PartialMap (Gamma ops actor component) :=
  fun state => match tableAt state.val actor key with
    | none => none
    | some _ => some (setSlot key provided none state)

def provision (key : Key) (provided : component.provides key = true) (value : V key) :
    Operation (Gamma ops actor component) PUnit.{u+1} where
  run state := match tableAt state.val actor key with
    | none => some (setSlot key provided (some value) state, restrict key provided, .unit)
    | some _ => none

/-- On its actual domain, the captured partial inverse is exactly the native
restriction token; outside that domain it retains the primitive's failure. -/
theorem restrict_agrees_undo (key : Key) (provided : component.provides key = true)
    (state : Gamma ops actor component) :
    (restrict key provided state).map Subtype.val =
      match tableAt state.val actor key with
      | none => none
      | some _ => some (undo (.restrict actor key) state.val) := by
  cases bound : tableAt state.val actor key <;> simp [restrict, bound, undo]

theorem restrict_respects (observe : ∀ key, Setoid (V key)) (keys : Key → Prop)
    (key : Key) (selected : keys key) (provided : component.provides key = true) :
    MapRelated (Observed observe keys) (restrict (ops := ops) (actor := actor) key provided) (restrict key provided) := by
  intro left right related
  have slots := observed_slot observe keys key selected provided related
  cases a : tableAt left.val actor key <;> cases b : tableAt right.val actor key <;>
    simp only [a, b, OptionRel] at slots
  · simp [restrict, a, b, OptionRel]
  · simpa only [restrict, a, b, OptionRel] using
      setSlot_related observe keys key provided related (show OptionRel (observe key).r none none from trivial)

theorem provision_respects (observe : ∀ key, Setoid (V key)) (keys : Key → Prop)
    (key : Key) (selected : keys key) (provided : component.provides key = true) (value : V key) :
    ∀ left right, Observed (ops := ops) (actor := actor) observe keys left right →
      OptionRel (fun a b => Observed observe keys a.1 b.1 ∧
        MapRelated (Observed observe keys) a.2.1 b.2.1 ∧ a.2.2 = b.2.2)
        ((provision key provided value).run left) ((provision key provided value).run right) := by
  intro left right related
  have slots := observed_slot observe keys key selected provided related
  cases a : tableAt left.val actor key <;> cases b : tableAt right.val actor key <;>
    simp only [a, b, OptionRel] at slots
  · simp only [provision, a, b, OptionRel]
    exact ⟨setSlot_related observe keys key provided related ((observe key).refl value),
      restrict_respects observe keys key selected provided, trivial⟩
  · simp [provision, a, b, OptionRel]

theorem setSlot_overwrite (key : Key) (provided : component.provides key = true)
    (a b : Option (V key)) (state : Gamma ops actor component) :
    setSlot key provided b (setSlot key provided a state) = setSlot key provided b state := by
  apply Subtype.ext
  simp only [setSlot_value]
  funext name
  by_cases same : name = actor
  · subst name
    obtain ⟨fiber, present, _⟩ := state.property.2
    simp only [write, TypedRegistry.modify, present, Option.map_some, ite_true]
    congr 2
    funext other
    by_cases same : key = other <;> simp [same]
  · simp [write, TypedRegistry.modify, same]

theorem setSlot_current (key : Key) (provided : component.provides key = true)
    (state : Gamma ops actor component) :
    setSlot key provided (tableAt state.val actor key) state = state := by
  apply Subtype.ext
  simp only [setSlot_value]
  funext name
  by_cases same : name = actor
  · subst name
    obtain ⟨fiber, present, _⟩ := state.property.2
    simp only [write, TypedRegistry.modify, present, Option.map_some,
      tableAt, Option.bind_some, ite_true]
    congr 2
    funext other
    by_cases same : key = other
    · subst other; simp
    · simp [same]
  · simp [write, TypedRegistry.modify, same]

theorem provision_exact_recovery (key : Key) (provided : component.provides key = true)
    (value : V key) (input output : Gamma ops actor component)
    (inverse : PartialMap (Gamma ops actor component)) (outcome : PUnit.{u+1})
    (called : (provision key provided value).run input = some (output, inverse, outcome)) :
    inverse output = some input := by
  cases bound : tableAt input.val actor key with
  | some old => simp [provision, bound] at called
  | none =>
    have same : setSlot key provided (some value) input = output ∧
        restrict key provided = inverse ∧ PUnit.unit = outcome := by
      simpa only [provision, bound, Option.some.injEq, Prod.mk.injEq] using called
    obtain ⟨rfl, rfl, rfl⟩ := same
    simp only [restrict, slot_self, setSlot_overwrite]
    rw [← bound, setSlot_current]

/-- A nontrivial provision now has the full cross-input partial witness:
success/failure agreement, related outputs, related captured inverse functions,
and exact defined recovery. No global provision witness is assumed. -/
theorem provision_witnessed (observe : ∀ key, Setoid (V key)) (keys : Key → Prop)
    (key : Key) (selected : keys key) (provided : component.provides key = true) (value : V key) :
    Witnessed (provision (ops := ops) (actor := actor) key provided value) (Observed observe keys) := by
  refine ⟨?_, provision_respects observe keys key selected provided value⟩
  intro input output inverse outcome called
  refine ⟨input, provision_exact_recovery key provided value input output inverse outcome called, ?_⟩
  intro other _
  exact ⟨fun owner v found => ⟨owner, v, found, (observe other).refl v⟩,
    fun owner v found => ⟨owner, v, found, (observe other).refl v⟩⟩

/-- Successful scoped provisioning is exactly the paper's native typed Land,
including its original captured restriction and selected continuation. -/
theorem provision_is_land (program : Code → Instruction Name ops Code) (code : Code)
    (key : Key) (provided : component.provides key = true) (value : V key)
    (action : (program code).action = .provide key value)
    (state : Gamma ops actor component) (vacant : tableAt state.val actor key = none) :
    Land program actor code state.val (setSlot key provided (some value) state).val
      (.restrict actor key) ((program code).next (.provision key value)) := by
  obtain ⟨fiber, present, same⟩ := state.property.2
  exact .provide state.val actor code fiber key value action present
    (same ▸ provided) (by simpa [tableAt, present] using vacant)

/-- The only state change of either successful operation is the actor's table.
In particular the registry domain, declarations, parent, flag and phase survive. -/
theorem setSlot_frame (key : Key) (provided : component.provides key = true)
    (value : Option (V key)) (state : Gamma ops actor component) :
    (∀ owner, owner ≠ actor → (setSlot key provided value state).val owner = state.val owner) ∧
    ∀ fiber, state.val actor = some fiber →
      ∃ result, (setSlot key provided value state).val actor = some result ∧
        result.component = fiber.component ∧ result.parent = fiber.parent ∧
        result.retired = fiber.retired ∧ result.phase = fiber.phase := by
  constructor
  · intro owner different
    simp [setSlot_value, write, TypedRegistry.modify, different]
  · intro fiber present
    exact ⟨{fiber with table := fun k => if h : key = k then h ▸ value else fiber.table k},
      by simp [setSlot_value, write, TypedRegistry.modify, present], rfl, rfl, rfl, rfl⟩

def terminal (key : Key) (provided : component.provides key = true) (value : V key) :
    PartialIterators.Iterator (Gamma ops actor component) :=
  PartialIterators.stage (provision key provided value) (fun _ => none)

/-- The terminal provision component, including its recursive iterator
relation and reachable-head witness, is admitted in the repaired semantics. -/
theorem terminal_witnessed (observe : ∀ key, Setoid (V key)) (keys : Key → Prop)
    (key : Key) (selected : keys key) (provided : component.provides key = true) (value : V key) :
    PartialIterators.Witnessed (Observed observe keys) (terminal (ops := ops) (actor := actor) key provided value) := by
  have rootOnly : ∀ current, PartialIterators.Reach (terminal (ops := ops) (actor := actor) key provided value) current →
      current = terminal key provided value := by
    intro current reached
    induction reached with
    | root => rfl
    | continuation _ input output inverse called ih =>
      rw [ih] at called
      obtain ⟨_, _, impossible⟩ := (PartialIterators.stage_success_iff _ _ _ _ _ _).mp called
      cases impossible
  intro current reached
  rw [rootOnly current reached]
  constructor
  · intro input output inverse next called
    obtain ⟨result, call, _⟩ := (PartialIterators.stage_success_iff _ _ _ _ _ _).mp called
    exact provision_exact_recovery key provided value input output inverse result call
  · apply PartialIterators.related_coinduction (Observed observe keys)
      (fun a b => a = terminal key provided value ∧ b = terminal key provided value) ?_ ⟨rfl, rfl⟩
    intro a b pair
    obtain ⟨rfl, rfl⟩ := pair
    apply PartialReachMediatedWitness.stage_unfold_selected _ _ _ _
      (provision_respects observe keys key selected provided value)
    intro input output inverse child called
    obtain ⟨_, _, impossible⟩ := (PartialIterators.stage_success_iff _ _ _ _ _ _).mp called
    cases impossible

end Cordis.Repairs.CompatibleProvision
