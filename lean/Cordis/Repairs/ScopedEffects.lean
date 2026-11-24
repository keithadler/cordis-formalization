import Cordis.Repairs.BoundOperation
import Cordis.Repairs.AllocationDomains

/-!
Scoped interpretation of the primitive heads of Definition 56. The input
domain and the forward result domain may differ. A saved inverse is partial
on the latter domain and need only recover the input's table observation.
These types carry applicability; the observation does not inspect them.
-/
namespace Cordis.Repairs.ScopedEffects
open TypedRegistry
open PaperEffectEquations (CoeffectOperations)
open TypedStateObservation (TablesRelatedAt)
open Iterators (OptionRel)
open PartialInverseObservation (MapRelated Operation Witnessed)
universe u
variable {Name Key Code : Type u} {V : Key → Type u}
local notation "R" => Registry Name V Code
local notation "Dom" => R → Prop

abbrev State (domain : Dom) := Subtype domain
abbrev Saved (domain : Dom) := State domain → Option (State domain)

structure Effect (source target : Dom) (Outcome : Type u) where
  run : State source → Option (State target × Saved target × Outcome)

def Observed (observe : ∀ key, Setoid (V key)) (keys : Key → Prop)
    {source target : Dom} (left : State source) (right : State target) : Prop :=
  TablesRelatedAt observe keys left.val right.val

variable {source target : Registry Name V Code → Prop} {O : Type u}

theorem observed_refl (observe : ∀ key, Setoid (V key)) (keys : Key → Prop) (input : State source) :
    Observed observe keys input input := by
  intro key _
  exact ⟨fun name v found => ⟨name, v, found, (observe key).refl v⟩,
    fun name v found => ⟨name, v, found, (observe key).refl v⟩⟩

structure Lawful {source target : Dom} {O : Type u} (observe : ∀ key, Setoid (V key)) (keys : Key → Prop)
    (effect : Effect source target O) : Prop where
  recover : ∀ input output saved outcome, effect.run input = some (output, saved, outcome) →
    ∃ restored, saved output = some restored ∧ Observed observe keys restored input
  respect : ∀ left right, Observed observe keys left right →
    OptionRel (fun a b => Observed observe keys a.1 b.1 ∧
      MapRelated (Observed observe keys) a.2.1 b.2.1 ∧ a.2.2 = b.2.2)
      (effect.run left) (effect.run right)

def ofOperation (op : Operation (State source) O) : Effect source source O :=
  ⟨op.run⟩

theorem lawful_ofOperation (observe : ∀ key, Setoid (V key)) (keys : Key → Prop)
    (op : Operation (State source) O) (witness : Witnessed op (Observed observe keys)) :
    Lawful observe keys (ofOperation op) :=
  ⟨witness.recover, witness.respect⟩

def unit (source : Dom) : Effect source source PUnit.{u+1} :=
  ⟨fun input => some (input, some, .unit)⟩

theorem unit_lawful (observe : ∀ key, Setoid (V key)) (keys : Key → Prop) (source : Dom) :
    Lawful observe keys (unit source) := by
  constructor
  · intro input output saved outcome called
    have same : input = output ∧ some = saved ∧ PUnit.unit = outcome := by
      simpa only [unit, Option.some.injEq, Prod.mk.injEq] using called
    obtain ⟨rfl, rfl, rfl⟩ := same
    exact ⟨input, rfl, observed_refl observe keys input⟩
  · intro left right related
    exact ⟨related, fun _ _ same => same, rfl⟩

variable [DecidableEq Name] [DecidableEq Key] {ops : CoeffectOperations V}
variable {actor owner newborn : Name} {acting providing child : Calculus.Component Key Code}

/-- The ordinary inverse's recorded provider is retained in its output
scope and declares the observed key. Control-only inverses need no slot. -/
def InverseScope (ops : CoeffectOperations V) (keys : Key → Prop) (token : Inverse Name V)
    (target : Dom) : Prop :=
  match token with
  | .restrict owner key | .operate owner key _ =>
    keys key ∧ ∃ provider : Calculus.Component Key Code, provider.provides key = true ∧
      ∀ state, target state → CompatibleProvision.Compatible ops owner provider state
  | .unit | .retire _ => True

omit [DecidableEq Name] in
theorem InverseScope.mono {keys wider : Key → Prop} {token : Inverse Name V} {target : Dom}
    (scope : InverseScope ops keys token target) (included : ∀ key, keys key → wider key) :
    InverseScope ops wider token target := by
  cases token with
  | unit | retire => trivial
  | restrict owner key | operate owner key =>
    exact ⟨included key scope.1, scope.2⟩

/-- Agreement of the returned partial inverse with its native token on the
output scope, including failure on admitted probes. -/
structure InverseAgrees {target : Dom} (saved : Saved target) (token : Inverse Name V) : Prop where
  value : ∀ probe restored, saved probe = some restored → restored.val = undo token probe.val
  defined : ∀ probe, (∃ restored, saved probe = some restored) ↔ InverseDefined probe.val token

/-- Each successful scoped call is the actual Land rule, with the native
selected continuation and a saved inverse on the head's output scope. -/
structure Realizes {source target : Dom} {O : Type u}
    (program : Code → Instruction Name ops Code) (actor : Name) (code : Code)
    (reply : O → Outcome Name ops) (effect : Effect source target O) (draw : Option Name) : Prop where
  sound : ∀ input output saved outcome, effect.run input = some (output, saved, outcome) →
    ∃ token, Land program actor code input.val output.val token ((program code).next (reply outcome)) ∧
      InverseAgrees saved token ∧ capturedChild token = draw ∧
      replyAt program actor draw code input.val = some (reply outcome)
  complete : ∀ (input : State source) {after token next},
    Land program actor code input.val after token next → capturedChild token = draw →
    ∃ result, effect.run input = some result

theorem unit_realizes (program : Code → Instruction Name ops Code) (actor : Name) (code : Code)
    (action : (program code).action = .unit) (source : Dom) :
    Realizes program actor code (fun _ => .unit) (unit source) none := by
  refine ⟨?_, by
    intro input _ _ _ _ _
    exact ⟨(input, some, .unit), rfl⟩⟩
  intro input output saved outcome called
  have same : input = output ∧ some = saved ∧ PUnit.unit = outcome := by
    simpa only [unit, Option.some.injEq, Prod.mk.injEq] using called
  obtain ⟨rfl, rfl, rfl⟩ := same
  exact ⟨.unit, .unit _ _ _ action, ⟨
    fun _ _ found => congrArg Subtype.val (Option.some.inj found).symm,
    fun probe => ⟨fun _ => trivial, fun _ => ⟨probe, rfl⟩⟩⟩, rfl, by simp [replyAt, action]⟩

def provision (key : Key) (provided : acting.provides key = true) (value : V key) :
    Effect (CompatibleProvision.Compatible ops actor acting)
      (CompatibleProvision.Compatible ops actor acting) PUnit.{u+1} :=
  ofOperation (CompatibleProvision.provision key provided value)

theorem provision_lawful (observe : ∀ key, Setoid (V key)) (keys : Key → Prop)
    (key : Key) (selected : keys key) (provided : acting.provides key = true) (value : V key) :
    Lawful observe keys (provision (ops := ops) (actor := actor) key provided value) :=
  lawful_ofOperation _ _ _ (CompatibleProvision.provision_witnessed observe keys key selected provided value)

theorem provision_realizes (program : Code → Instruction Name ops Code) (code : Code)
    (key : Key) (provided : acting.provides key = true) (value : V key)
    (action : (program code).action = .provide key value) :
    Realizes program actor code (fun _ => .provision key value)
      (provision (ops := ops) (actor := actor) key provided value) none := by
  constructor
  · intro input output saved outcome called
    cases binding : tableAt input.val actor key with
    | some existing => simp [provision, ofOperation, CompatibleProvision.provision, binding] at called
    | none =>
      have same : CompatibleProvision.setSlot key provided (some value) input = output ∧
          CompatibleProvision.restrict key provided = saved ∧ PUnit.unit = outcome := by
        simpa only [provision, ofOperation, CompatibleProvision.provision, binding,
          Option.some.injEq, Prod.mk.injEq] using called
      obtain ⟨rfl, rfl, rfl⟩ := same
      refine ⟨.restrict actor key,
        CompatibleProvision.provision_is_land program code key provided value action input binding,
        ⟨?_, ?_⟩, rfl, by simp [replyAt, action]⟩
      · intro probe restored found
        have agrees := CompatibleProvision.restrict_agrees_undo key provided probe
        rw [found] at agrees
        cases cell : tableAt probe.val actor key <;> simp_all
      · intro probe
        cases cell : tableAt probe.val actor key <;>
          simp [InverseDefined, CompatibleProvision.restrict, cell]
  · intro input after token next landed _
    cases landed with
    | provide _ _ _ row actual given instructed present declared absent =>
      cases action.symm.trans instructed
      have vacant : tableAt input.val actor key = none := by simp [tableAt, present, absent]
      simp [provision, ofOperation, CompatibleProvision.provision, vacant]
    | unit _ _ _ instructed | operate _ _ _ _ _ _ _ _ _ _ _ instructed _
      | instantiate _ _ _ _ _ instructed _ => cases action.symm.trans instructed

def operate {key : Key} (provided : providing.provides key = true)
    (name : ops.Name key) (argument : ops.Argument key name) :
    Effect (BoundOperation.Compatible ops actor acting owner providing key)
      (BoundOperation.Compatible ops actor acting owner providing key) (ops.Outcome key name) :=
  ofOperation (BoundOperation.liftOperation provided (ops.operation key name argument))

theorem operate_lawful (observe : ∀ key, Setoid (V key)) (keys : Key → Prop)
    {key : Key} (selected : keys key) (provided : providing.provides key = true)
    (name : ops.Name key) (argument : ops.Argument key name)
    (witness : Witnessed (ops.operation key name argument) (observe key).r) :
    Lawful observe keys (operate (actor := actor) (acting := acting) (owner := owner) provided name argument) :=
  lawful_ofOperation _ _ _ (BoundOperation.operation_witnessed observe keys selected provided _ witness)

theorem operate_realizes (program : Code → Instruction Name ops Code) (code : Code)
    {key : Key} (provided : providing.provides key = true)
    (name : ops.Name key) (argument : ops.Argument key name)
    (action : (program code).action = .operate key name argument) :
    Realizes program actor code (.operation key name)
      (operate (actor := actor) (acting := acting) (owner := owner) provided name argument) none := by
  constructor
  · intro input output saved outcome called
    obtain ⟨before, after, inverse, binding, applied, rfl, rfl⟩ :=
      (BoundOperation.operation_success_iff provided _ input output saved outcome).mp called
    refine ⟨.operate owner key inverse,
      BoundOperation.operation_is_land provided program code name argument action input before after
        inverse outcome binding applied,
      ⟨BoundOperation.liftMap_agrees_undo provided inverse, ?_⟩, rfl, ?_⟩
    case refine_2 =>
      simp [replyAt, action, location, input.property.2.2, binding, applied]
    intro probe
    cases cell : tableAt probe.val owner key with
    | none => simp [InverseDefined, BoundOperation.liftMap, cell]
    | some before =>
      cases applied : inverse before <;> simp [InverseDefined, BoundOperation.liftMap, cell, applied]
  · intro input after token next landed _
    cases landed with
    | operate _ _ _ actual calledWith arg actualOwner old new inverse reply instructed located called =>
      cases action.symm.trans instructed
      have binding : tableAt input.val owner key = some old := by
        simpa [location, input.property.2.2] using congrArg (Option.map Prod.snd) located
      simp [operate, ofOperation, BoundOperation.liftOperation, binding, called]
    | unit _ _ _ instructed | provide _ _ _ _ _ _ instructed _ _ _
      | instantiate _ _ _ _ _ instructed _ => cases action.symm.trans instructed

def allocate : Effect
    (fun state : R => CompatibleProvision.Compatible ops actor acting state ∧
      Insertable state newborn child (some actor))
    (fun state : R => CompatibleProvision.Compatible ops actor acting state ∧
      ∃ fiber, state newborn = some fiber ∧ fiber.component = child ∧ fiber.parent = some actor)
    PUnit.{u+1} :=
  ⟨fun input => some (AllocationDomains.allocate input, some ∘ AllocationDomains.inverse, .unit)⟩

theorem allocate_lawful (observe : ∀ key, Setoid (V key)) (keys : Key → Prop) :
    Lawful observe keys (allocate (ops := ops) (actor := actor) (newborn := newborn)
      (acting := acting) (child := child)) := by
  constructor
  · intro input output saved outcome called
    have same : AllocationDomains.allocate input = output ∧
        some ∘ AllocationDomains.inverse = saved ∧ PUnit.unit = outcome := by
      simpa only [allocate, Option.some.injEq, Prod.mk.injEq] using called
    obtain ⟨rfl, rfl, rfl⟩ := same
    exact ⟨_, rfl, AllocationDomains.observational_recovery observe keys input⟩
  · intro left right related
    exact ⟨AllocationDomains.allocate_respects observe keys related,
      fun _ _ same => AllocationDomains.inverse_respects observe keys same, rfl⟩

theorem allocate_realizes (program : Code → Instruction Name ops Code) (code : Code)
    (action : (program code).action = .instantiate child) :
    Realizes program actor code (fun _ => .child newborn)
      (allocate (ops := ops) (actor := actor) (newborn := newborn) (acting := acting) (child := child))
      (some newborn) := by
  refine ⟨?_, by
    intro input _ _ _ _ _
    exact ⟨(AllocationDomains.allocate input, some ∘ AllocationDomains.inverse, .unit), rfl⟩⟩
  intro input output saved outcome called
  have same : AllocationDomains.allocate input = output ∧
      some ∘ AllocationDomains.inverse = saved ∧ PUnit.unit = outcome := by
    simpa only [allocate, Option.some.injEq, Prod.mk.injEq] using called
  obtain ⟨rfl, rfl, rfl⟩ := same
  refine ⟨.retire newborn, AllocationDomains.native_landing program code action input, ⟨?_,
    fun probe => ⟨fun _ => trivial, fun _ => ⟨AllocationDomains.inverse probe, rfl⟩⟩⟩,
    rfl, by simp [replyAt, action]⟩
  intro probe restored found
  exact (congrArg Subtype.val (Option.some.inj found)).symm.trans (AllocationDomains.native_inverse probe)

end Cordis.Repairs.ScopedEffects
