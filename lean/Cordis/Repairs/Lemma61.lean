import Cordis.Repairs.CompatibleProvision
import Cordis.Repairs.FreshNameTransport
import Cordis.Repairs.GuardedRenaming

/-! Repaired Lemma 61. The name action maps parent and provider references,
saved inverse addresses, and the child outcomes passed to continuations.
The finite rooted registry domain and all labeled rule guards transport. -/
namespace Cordis.Repairs.Lemma61
open PaperEffectEquations (CoeffectOperations)

universe u
variable {Name Key Code : Type u} [DecidableEq Name] [DecidableEq Key]
local notation "P" => Renaming.Permutation Name

section Registry
open Calculus Stages
variable {Value Error : Type u}
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error

omit [DecidableEq Name] [DecidableEq Key] in
private theorem parent_source (p : P) {state : R} {child parent : Name} {row : F}
    (found : Renaming.registry p state child = some row) (parentOf : row.parent = some parent) :
    ∃ original, state (p.invFun child) = some original ∧ original.parent = some (p.invFun parent) := by
  obtain ⟨original, present, rfl⟩ := Option.map_eq_some_iff.mp found
  change original.parent.map p.toFun = some parent at parentOf
  obtain ⟨oldParent, edge, rfl⟩ := Option.map_eq_some_iff.mp parentOf
  exact ⟨original, present, by simpa using edge⟩

omit [DecidableEq Name] [DecidableEq Key] in
private theorem allowed_map (p : P) (state : R) (allowed : MediatedRegistry.Allowed state) :
    MediatedRegistry.Allowed (Renaming.registry p state) := by
  obtain ⟨⟨closed, rank, ranked⟩, ⟨names, finite⟩, owned, disjoint⟩ := allowed
  refine ⟨⟨?_, rank ∘ p.invFun, ?_⟩, ⟨names.map p.toFun, ?_⟩, ?_, ?_⟩
  · intro child row parent present edge missing
    obtain ⟨original, found, parentOf⟩ := parent_source p present edge
    exact closed _ original _ found parentOf (Option.map_eq_none_iff.mp missing)
  · intro child row parent present edge
    obtain ⟨original, found, parentOf⟩ := parent_source p present edge
    exact ranked _ original _ found parentOf
  · intro name row present
    obtain ⟨original, found, _⟩ := Option.map_eq_some_iff.mp present
    exact List.mem_map.mpr ⟨p.invFun name, finite _ original found, p.right_inv name⟩
  · intro name row key present occupied
    obtain ⟨original, found, rfl⟩ := Option.map_eq_some_iff.mp present
    exact owned _ original key found occupied
  · intro first second left right firstFound secondFound different key overlap
    obtain ⟨leftSource, leftFound, rfl⟩ := Option.map_eq_some_iff.mp firstFound
    obtain ⟨rightSource, rightFound, rfl⟩ := Option.map_eq_some_iff.mp secondFound
    exact disjoint _ _ leftSource rightSource leftFound rightFound
      (fun same => different (by simpa using congrArg p.toFun same)) key overlap

omit [DecidableEq Name] [DecidableEq Key] in
theorem allowed_equivariant (p : P) (state : R) :
    MediatedRegistry.Allowed state ↔ MediatedRegistry.Allowed (Renaming.registry p state) := by
  constructor
  · exact allowed_map p state
  · intro allowed
    simpa only [Renaming.registry_symm] using allowed_map p.symm (Renaming.registry p state) allowed

end Registry

section Typed
open TypedRegistry
variable {V : Key → Type u} {ops : CoeffectOperations V}
local notation "R" => Registry Name V Code
local notation "Program" => Code → Instruction Name ops Code

omit [DecidableEq Name] in
theorem allowed_iff (p : P) (state : R) :
    CompatibleProvision.Allowed ops state ↔ CompatibleProvision.Allowed ops (FreshNameTransport.registry p state) := by
  simpa only [CompatibleProvision.Allowed, FreshNameTransport.encode_registry] using
    allowed_equivariant p (encodeRegistry ops state)

omit [DecidableEq Name] in
theorem component_probe_iff (p : P) (actor : Name) (component : Calculus.Component Key Code) (state : R) :
    CompatibleProvision.Compatible ops actor component state ↔
      CompatibleProvision.Compatible ops (p.toFun actor) component (FreshNameTransport.registry p state) := by
  simp only [CompatibleProvision.Compatible, ← allowed_iff p state, FreshNameTransport.registry_at]
  refine and_congr_right (fun _ => ⟨?_, ?_⟩)
  · rintro ⟨row, found, payload⟩
    exact ⟨FreshNameTransport.fiber p row, by simp [found], payload⟩
  · rintro ⟨row, found, payload⟩
    obtain ⟨source, present, rfl⟩ := Option.map_eq_some_iff.mp found
    exact ⟨source, present, payload⟩

omit [DecidableEq Name] in
theorem wellFormed_iff (p : P) (state : R) :
    WellFormed.WellFormed (encodeRegistry ops state) ↔
      WellFormed.WellFormed (encodeRegistry ops (FreshNameTransport.registry p state)) := by
  rw [FreshNameTransport.encode_registry]
  exact Renaming.wellFormed_equivariant p (encodeRegistry ops state)

private theorem step_iff_encoded {prog : Program} {rule : Labeled.Rule} {actor : Name} {before after : R} :
    Step prog rule actor before after ↔
      Labeled.Step (encodeProgram prog) rule actor (encodeRegistry ops before) (encodeRegistry ops after) := by
  constructor
  · exact encode_step
  · intro encoded
    obtain ⟨output, actual, equation⟩ := decode_step encoded
    cases encodeRegistry_injective ops equation
    exact actual

theorem step_equivariant (p : P) {prog : Program} {rule : Labeled.Rule} {actor : Name} {before after : R} :
    Step prog rule actor before after ↔
      Step (FreshNameTransport.program p prog) rule (p.toFun actor)
        (FreshNameTransport.registry p before) (FreshNameTransport.registry p after) := by
  simpa only [step_iff_encoded, FreshNameTransport.encode_program, FreshNameTransport.encode_registry] using
    (Renaming.labeled_step_equivariant p (prog := encodeProgram prog) (rule := rule) (actor := actor)
      (before := encodeRegistry ops before) (after := encodeRegistry ops after))

/-- Fixing a program only constrains the child outcomes of instantiation
instructions. Dependent operation and provision continuations are arbitrary. -/
def ChildBranches (p : P) (prog : Program) : Prop :=
  ∀ code component, (prog code).action = .instantiate component → ∀ child,
    (prog code).next (.child (p.toFun child)) = (prog code).next (.child child)

omit [DecidableEq Name] in
theorem encoded_child_branches (p : P) {prog : Program} (stable : ChildBranches p prog) :
    Renaming.PreservesChildBranches p (encodeProgram prog) := by
  intro code component instruction child
  have actual : (prog code).action = .instantiate component := by
    cases action : (prog code).action <;> simp_all [encodeProgram, encodeInstruction, encodeAction]
  simpa [encodeProgram, encodeInstruction, decodeOutcome] using stable code component actual child

theorem step_equivariant_same (p : P) {prog : Program} (stable : ChildBranches p prog)
    {rule : Labeled.Rule} {actor : Name} {before after : R} :
    Step prog rule actor before after ↔
      Step prog rule (p.toFun actor) (FreshNameTransport.registry p before) (FreshNameTransport.registry p after) := by
  simpa only [step_iff_encoded, FreshNameTransport.encode_registry] using
    (Renaming.labeled_step_equivariant_same p (encoded_child_branches p stable) (rule := rule) (actor := actor)
      (before := encodeRegistry ops before) (after := encodeRegistry ops after))

/-- The admissible registry domain, the component-indexed probe domain,
well-formedness, and every labeled rule are equivariant. -/
theorem lemma61_scoped (p : P) (prog : Program) :
    (∀ state : R, CompatibleProvision.Allowed ops state ↔
      CompatibleProvision.Allowed ops (FreshNameTransport.registry p state)) ∧
    (∀ actor component (state : R), CompatibleProvision.Compatible ops actor component state ↔
      CompatibleProvision.Compatible ops (p.toFun actor) component (FreshNameTransport.registry p state)) ∧
    (∀ state : R, WellFormed.WellFormed (encodeRegistry ops state) ↔
      WellFormed.WellFormed (encodeRegistry ops (FreshNameTransport.registry p state))) ∧
    (∀ rule actor (before after : R), Step prog rule actor before after ↔
      Step (FreshNameTransport.program p prog) rule (p.toFun actor)
        (FreshNameTransport.registry p before) (FreshNameTransport.registry p after)) :=
  ⟨allowed_iff p, component_probe_iff p, wellFormed_iff p, fun _ _ _ _ => step_equivariant p⟩

end Typed
end Cordis.Repairs.Lemma61
