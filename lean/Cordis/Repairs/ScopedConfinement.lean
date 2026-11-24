import Cordis.Repairs.ScopedAdmission
import Cordis.Repairs.OperationConfinement

/-! Definition 55 on scoped partial maps. Fixing a route is a condition on
the domain. Successful ordinary calls change only permitted slots, and
the read comparison tests both the forward call and its saved inverse.
Births instead satisfy the native insertion and retirement frame. -/
namespace Cordis.Repairs.ScopedConfinement
open TypedRegistry ScopedEffects ScopedProgram
open PaperEffectEquations (CoeffectOperations)
open Iterators (OptionRel)
open PartialInverseObservation (MapRelated)
universe u
variable {Name Key Code : Type u} {V : Key → Type u}
variable [DecidableEq Name] [DecidableEq Key] {ops : CoeffectOperations V}
local notation "R" => Registry Name V Code
local notation "F" => Fiber Name V Code
variable {actor owner : Name} {acting providing payload : Calculus.Component Key Code}
variable {source target : Registry Name V Code → Prop} {O : Type u}
variable {program : Code → Instruction Name ops Code} {code : Code}
variable {observe : ∀ key, Setoid (V key)} {keys : Key → Prop}

def Reads (actor : Name) (acting : Calculus.Component Key Code) (left right : R) : Prop :=
  ∀ owner key, owner = actor ∨ acting.requires key = true → tableAt left owner key = tableAt right owner key

def Writes (actor : Name) (acting : Calculus.Component Key Code) (before after : R) : Prop :=
  (∀ name, after name = none ↔ before name = none) ∧
  ∀ name old updated, before name = some old → after name = some updated →
    { updated with table := old.table } = old ∧
      (name ≠ actor → ∀ key, acting.requires key = false → updated.table key = old.table key)

omit [DecidableEq Name] [DecidableEq Key] in
private theorem writes_refl (state : R) : Writes actor acting state state := by
  refine ⟨fun _ => Iff.rfl, ?_⟩
  intro name old updated first second
  cases Option.some.inj (first.symm.trans second)
  exact ⟨rfl, fun _ _ _ => rfl⟩

private theorem update_writes (state : R) (owner : Name) (key : Key)
    (update : Option (V key) → Option (V key)) (allowed : owner = actor ∨ acting.requires key = true) :
    Writes actor acting state (TypedRegistry.modify state owner fun fiber => { fiber with
      table := fun other => if same : key = other then same ▸ update (fiber.table key) else fiber.table other }) := by
  constructor
  · intro name
    by_cases atOwner : name = owner
    · subst name
      simp [TypedRegistry.modify]
    · simp [TypedRegistry.modify, atOwner]
  · intro name old updated before after
    by_cases atOwner : name = owner
    · subst name
      simp [TypedRegistry.modify, before] at after
      cases after
      refine ⟨rfl, ?_⟩
      intro outside other notRequired
      have different : key ≠ other := by
        intro same
        subst other
        rcases allowed with equal | required
        · exact outside equal
        · simp [notRequired] at required
      simp [different]
    · rw [TypedRegistry.modify, if_neg atOwner, before] at after
      cases Option.some.inj after
      exact ⟨rfl, fun _ _ _ => rfl⟩

structure Ordinary (actor : Name) (acting : Calculus.Component Key Code)
    (effect : Effect source target O) : Prop where
  writes : ∀ input output saved reply, effect.run input = some (output, saved, reply) →
    Writes actor acting input.val output.val ∧
      ∀ probe restored, saved probe = some restored → Writes actor acting probe.val restored.val
  reads : ∀ left right, Reads actor acting left.val right.val →
    OptionRel (fun a b => Reads actor acting a.1.val b.1.val ∧
      MapRelated (fun first second => Reads actor acting first.val second.val) a.2.1 b.2.1 ∧ a.2.2 = b.2.2)
      (effect.run left) (effect.run right)

/-- The native exception to ordinary write confinement. Every success
inserts a particular empty child and captures its retirement. -/
def Birth (payload : Calculus.Component Key Code) (head : Head program actor observe keys code source target O) : Prop :=
  ∃ newborn, ∀ input output saved reply, head.effect.run input = some (output, saved, reply) →
    head.reply reply = .child newborn ∧ Insertable input.val newborn payload (some actor) ∧
    output.val = put input.val newborn (fresh payload (some actor)) ∧
    ∀ probe, ∃ restored, saved probe = some restored ∧ restored.val = TypedRegistry.retire probe.val newborn

def HeadConfined (acting : Calculus.Component Key Code)
    (head : Head program actor observe keys code source target O) : Prop :=
  match (program code).action with
  | .instantiate payload => Birth payload head
  | _ => Ordinary actor acting head.effect

omit [DecidableEq Name] [DecidableEq Key] in
theorem unit (domain : R → Prop) : Ordinary actor acting (ScopedEffects.unit domain) := by
  constructor
  · intro input output saved reply called
    have same : input = output ∧ some = saved ∧ PUnit.unit = reply := by
      simpa only [ScopedEffects.unit, Option.some.injEq, Prod.mk.injEq] using called
    obtain ⟨rfl, rfl, rfl⟩ := same
    refine ⟨writes_refl _, ?_⟩
    intro probe restored applied
    cases Option.some.inj applied
    exact writes_refl _
  · intro left right related
    exact ⟨related, fun _ _ same => same, rfl⟩

theorem provision (key : Key) (provided : acting.provides key = true) (value : V key) :
    Ordinary actor acting (ScopedEffects.provision (ops := ops) (actor := actor) key provided value) := by
  constructor
  · intro input output saved reply called
    cases binding : tableAt input.val actor key with
    | some existing => simp [ScopedEffects.provision, ofOperation, CompatibleProvision.provision, binding] at called
    | none =>
      have same : CompatibleProvision.setSlot key provided (some value) input = output ∧
          CompatibleProvision.restrict key provided = saved ∧ PUnit.unit = reply := by
        simpa only [ScopedEffects.provision, ofOperation, CompatibleProvision.provision, binding,
          Option.some.injEq, Prod.mk.injEq] using called
      obtain ⟨rfl, rfl, rfl⟩ := same
      refine ⟨update_writes _ actor key (fun _ => some value) (.inl rfl), ?_⟩
      intro probe restored applied
      have native := CompatibleProvision.restrict_agrees_undo key provided probe
      rw [applied] at native
      cases occupied : tableAt probe.val actor key with
      | none => simp [occupied] at native
      | some old =>
        have equal := Option.some.inj (by simpa only [occupied, Option.map_some] using native)
        rw [equal]
        exact update_writes _ actor key (fun _ => none) (.inl rfl)
  · intro left right related
    have same := related actor key (.inl rfl)
    cases binding : tableAt left.val actor key with
    | some old =>
      simp [ScopedEffects.provision, ofOperation, CompatibleProvision.provision, binding,
        same.symm.trans binding, OptionRel]
    | none =>
      have other := same.symm.trans binding
      simp only [ScopedEffects.provision, ofOperation, CompatibleProvision.provision, binding, other, OptionRel]
      exact ⟨CompatibleProvision.setSlot_reads key provided (some value) related,
        CompatibleProvision.restriction_reads key provided, trivial⟩

theorem operate (key : Key) (provided : providing.provides key = true)
    (name : ops.Name key) (argument : ops.Argument key name) :
    Ordinary actor acting (ScopedEffects.operate (actor := actor) (owner := owner) (acting := acting) provided name argument) := by
  constructor
  · intro input output saved reply called
    obtain ⟨before, after, inverse, read, applied, rfl, rfl⟩ :=
      (BoundOperation.operation_success_iff provided (ops.operation key name argument) input output saved reply).mp called
    refine ⟨update_writes _ owner key (fun _ => some after) (BoundOperation.route_authorized input).2, ?_⟩
    intro probe restored applied
    rw [BoundOperation.liftMap_agrees_undo provided inverse probe restored applied]
    exact update_writes _ owner key (fun old => old.map fun value => (inverse value).getD value)
      (BoundOperation.route_authorized probe).2
  · intro left right related
    have compared := BoundOperation.operation_reads provided (ops.operation key name argument) left right related
    cases leftCall : (BoundOperation.liftOperation provided (ops.operation key name argument)).run left with
    | none => cases rightCall : (BoundOperation.liftOperation provided (ops.operation key name argument)).run right <;>
        simp_all [ScopedEffects.operate, ofOperation, OptionRel]
    | some leftResult =>
      cases rightCall : (BoundOperation.liftOperation provided (ops.operation key name argument)).run right with
      | none => simp_all [OptionRel]
      | some rightResult =>
        obtain ⟨outA, savedA, replyA⟩ := leftResult
        obtain ⟨outB, savedB, replyB⟩ := rightResult
        rw [leftCall, rightCall] at compared
        obtain ⟨outputs, sameSaved, replies⟩ := compared
        obtain ⟨_, _, inverse, _, _, _, defSaved⟩ :=
          (BoundOperation.operation_success_iff provided _ _ _ _ _).mp leftCall
        simp only [ScopedEffects.operate, ofOperation, leftCall, rightCall, OptionRel]
        refine ⟨outputs, ?_, replies⟩
        change savedA = savedB at sameSaved
        rw [← sameSaved, defSaved]
        exact BoundOperation.inverse_reads provided inverse

theorem allocate (newborn : Name) (action : (program code).action = .instantiate payload) :
    Birth payload (Head.allocate (acting := acting) (program := program) (actor := actor)
      (observe := observe) (keys := keys) newborn action) := by
  refine ⟨newborn, ?_⟩
  intro input output saved reply called
  have same : AllocationDomains.allocate input = output ∧
      some ∘ AllocationDomains.inverse = saved ∧ PUnit.unit = reply := by
    simpa only [Head.allocate, ScopedEffects.allocate, Option.some.injEq, Prod.mk.injEq] using called
  obtain ⟨rfl, rfl, rfl⟩ := same
  exact ⟨rfl, input.property.2, rfl, fun probe => ⟨AllocationDomains.inverse probe, rfl, rfl⟩⟩

theorem head_narrow {smaller : R → Prop} {head : Head program actor observe keys code source target O}
    (included : ∀ state, smaller state → source state) (confined : HeadConfined acting head) :
    HeadConfined acting (head.narrow included) := by
  unfold HeadConfined at confined ⊢
  cases action : (program code).action <;> simp only [action] at confined ⊢
  case instantiate payload =>
    obtain ⟨child, native⟩ := confined
    exact ⟨child, fun input output saved reply called =>
      native ⟨input.val, included input.val input.property⟩ output saved reply called⟩
  case unit | provide | operate =>
    exact ⟨fun input output saved reply called =>
      confined.writes ⟨input.val, included input.val input.property⟩ output saved reply called,
      fun left right agrees =>
        confined.reads ⟨left.val, included left.val left.property⟩
          ⟨right.val, included right.val right.property⟩ agrees⟩

def RecipeConfined (acting : Calculus.Component Key Code) :
    {code : Code} → ScopedAdmission.Unlinked program actor observe keys code → Prop
  | _, .stage head tails =>
    HeadConfined acting head ∧ ∀ reply next selected, RecipeConfined acting (tails reply next selected)

def IteratorConfined (acting : Calculus.Component Key Code) :
    {code : Code} → {source : R → Prop} → ScopedProgram.Iterator program actor observe keys code source → Prop
  | _, _, .stage head _ tails _ =>
    HeadConfined acting head ∧ ∀ reply next selected, IteratorConfined acting (tails reply next selected)

theorem iterator_narrow {smaller : R → Prop}
    {it : ScopedProgram.Iterator program actor observe keys code source}
    (included : ∀ state, smaller state → source state) (confined : IteratorConfined acting it) :
    IteratorConfined acting (it.narrow included) := by
  cases it
  exact ⟨head_narrow included confined.1, confined.2⟩

/-- Synthesizing a domain changes only which inputs may be supplied.
The native read and write frame of every branch is retained. -/
theorem compile_confined {recipe : ScopedAdmission.Unlinked program actor observe keys code}
    (confined : RecipeConfined acting recipe) :
    IteratorConfined acting (ScopedAdmission.compile recipe).iterator := by
  induction recipe with
  | stage head tails ih =>
    refine ⟨head_narrow _ confined.1, ?_⟩
    intro reply next selected
    exact iterator_narrow _ (ih reply next selected (confined.2 reply next selected))

end Cordis.Repairs.ScopedConfinement
