import Cordis.TranspositionBegin
import Cordis.StageSimulation

/-! Whole-state observation for the activation diamond. Equality of controls
is separate from value observation, and accumulator self-relatedness is derived
from actual captured inverse provenance and the primitive witness contracts.
No blanket reflexivity of arbitrary semantic function fields is assumed. -/
namespace Cordis.Transposition
open Calculus Stages Labeled StageRecovery AccumulatorProvenance Effects Iterators
universe u
variable {Name Key Value Code Error : Type u}
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
variable [DecidableEq Name] [DecidableEq Key]
set_option linter.unusedSectionVars false

structure SameFields (left right : F) : Prop where
  component : left.component = right.component
  parent : left.parent = right.parent
  retired : left.retired = right.retired
  phase : left.phase = right.phase

def SameControls (left right : R) : Prop := ∀ name, OptionRel SameFields (left name) (right name)

theorem controls_refl (r : R) : SameControls r r := by
  intro name
  cases r name
  · trivial
  · exact ⟨rfl, rfl, rfl, rfl⟩

theorem controls_symm {r s : R} (same : SameControls r s) : SameControls s r := by
  intro name
  have original := same name
  cases left : r name <;> cases right : s name <;> simp_all [OptionRel]
  exact ⟨original.component.symm, original.parent.symm, original.retired.symm,
    original.phase.symm⟩

theorem controls_trans {r s t : R} (first : SameControls r s) (second : SameControls s t) : SameControls r t := by
  intro name
  have left := first name
  have right := second name
  cases a : r name <;> cases b : s name <;> cases c : t name <;> simp_all [OptionRel]
  exact ⟨left.component.trans right.component, left.parent.trans right.parent,
    left.retired.trans right.retired, left.phase.trans right.phase⟩

theorem write_controls (r : R) (owner : Name) (key : Key) (value : Option Value) :
    SameControls r (write r owner key value) := by
  intro name
  by_cases same : name = owner
  · subst name
    cases found : r owner <;> simp [write, Calculus.modify, found, OptionRel]
    exact ⟨rfl, rfl, rfl, rfl⟩
  · simpa [write, Calculus.modify, same] using controls_refl r name

theorem operation_controls (program : Code → Instruction Name Key Value Code Error)
    {actor : Name} {code : Code} {r s : R} {inverse next}
    (land : Land program actor code r s inverse next)
    (key : Key) (run : Value → Except Error (Value × (Value → Value) × Value))
    (action : (program code).action = .operate key run) : SameControls r s := by
  cases land with
  | unit _ _ _ selected | provide _ _ _ _ _ _ selected _ _ _ | instantiate _ _ _ _ _ selected _ =>
    rw [action] at selected
    cases selected
  | operate => exact write_controls _ _ _ _

section Observation
variable [Setoid Value]

theorem inverse_self_related (inverse : Inverse Name Key Value) (respects : InverseRespects inverse) :
    StageSimulation.InverseRelated inverse inverse := by
  cases inverse with
  | unit => exact .unit
  | restrict owner key => exact .restrict owner key
  | operate owner key inverse => exact .operate owner key respects
  | retire child => exact .retire child

theorem stack_self_related (stack : List (Inverse Name Key Value))
    (respects : ∀ inverse ∈ stack, InverseRespects inverse) : StageSimulation.StackRelated stack stack := by
  induction stack with
  | nil => exact .nil
  | cons head tail ih =>
    exact .cons (inverse_self_related head (respects head (by simp)))
      (ih (fun inverse member => respects inverse (by simp [member])))

theorem phase_self_related (phase : Phase Name Key Code (Inverse Name Key Value))
    (respects : ∀ inverse ∈ phase.accumulator, InverseRespects inverse) : StageSimulation.PhaseRelated Eq phase phase := by
  cases phase with
  | inactive => exact .inactive
  | reloading code stack view => exact .reloading view rfl (stack_self_related stack respects)
  | active stack view => exact .active view (stack_self_related stack respects)
  | unloading stack view => exact .unloading view (stack_self_related stack respects)

theorem state_self_related (r : R)
    (respects : ∀ name fiber, r name = some fiber →
      ∀ inverse ∈ fiber.phase.accumulator, InverseRespects inverse) : StageSimulation.Related Eq r r := by
  intro name
  cases found : r name with
  | none => trivial
  | some fiber =>
    refine ⟨⟨rfl, rfl, rfl⟩, rfl, rfl,
      phase_self_related fiber.phase (respects name fiber found), ?_⟩
    intro key
    cases fiber.table key
    · trivial
    · exact Setoid.refl _

theorem reachable_self_related (program : Code → Instruction Name Key Value Code Error)
    (witnesses : OperationWitnesses program) {r : R}
    (reached : WellFormed.Run program (fun _ => none) r) : StageSimulation.Related Eq r r := by
  apply state_self_related r
  intro name fiber found inverse member
  exact captured_respects program witnesses inverse (reachable_captured program reached name fiber found inverse member)

theorem landing_self_related (program : Code → Instruction Name Key Value Code Error)
    {actor : Name} {code : Code} {r s : R} {inverse next}
    (land : Land program actor code r s inverse next) (self : StageSimulation.Related Eq r r) :
    StageSimulation.Related Eq s s := by
  cases land with
  | unit => exact self
  | provide _ _ _ fiber key value action found declared absent =>
    exact StageSimulation.write_related self actor key (Setoid.refl value)
  | operate _ _ _ key run owner before after inv result action located called =>
    exact StageSimulation.write_related self owner key (Setoid.refl after)
  | instantiate _ _ _ component child action ready =>
    exact StageSimulation.put_related self child (StageSimulation.fresh_related ⟨rfl, rfl, rfl⟩ (some actor))

/-- Exact controls plus observed tables imply the full structural semantic
relation when the reference state's actual captured maps respect observation. -/
theorem related_of_controls_tables {r s : R} (controls : SameControls r s)
    (tables : TablesRelated r s) (self : StageSimulation.Related Eq s s) : StageSimulation.Related Eq r s := by
  intro name
  have fields := controls name
  have original := self name
  cases left : r name <;> cases right : s name <;> simp_all [OptionRel]
  refine ⟨?_, fields.parent, fields.retired, ?_, ?_⟩
  · simpa only [fields.component] using original.component
  · simpa only [fields.phase] using original.phase
  · intro key
    simpa [tableAt, left, right] using tables name key

end Observation
end Cordis.Transposition
