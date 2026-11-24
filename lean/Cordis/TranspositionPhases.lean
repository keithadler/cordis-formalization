import Cordis.TranspositionOrchestration

/-! Exact control-only transposition facts used for the Begin subcase of
Lemma78(1). Every guard and selected primitive outcome is preserved by the
proved field frames; there is no assumption that arbitrary steps commute. -/
namespace Cordis.Transposition
open Calculus Stages Labeled
universe u
variable {Name Key Value Code Error : Type u}
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
variable [DecidableEq Name] [DecidableEq Key]
set_option linter.unusedSectionVars false

theorem mark_other (r : R) (actor name : Name) (phase) (different : actor ≠ name) :
    mark r name phase actor = r actor := by simp [mark, Calculus.modify, different]

theorem mark_presence (r : R) (name other : Name) (phase) :
    mark r name phase other = none ↔ r other = none := by
  by_cases same : other = name <;> simp [mark, Calculus.modify, same]

theorem mark_insertable (r : R) (name child : Name) (phase) (component : Component Key Code) (parent) :
    Insertable (mark r name phase) child component parent ↔ Insertable r child component parent := by
  unfold Insertable
  apply and_congr (mark_presence r name child phase)
  apply and_congr
  · apply forall_congr'; intro p
    exact imp_congr_right (fun _ => not_congr (mark_presence r name p phase))
  · apply forall_congr'; intro other
    apply forall_congr'; intro key
    by_cases same : other = name
    · subst other
      cases found : r name <;> simp [mark, Calculus.modify, found]
    · simp [mark_other r other name phase same]

theorem mark_location (r : R) (actor name : Name) (phase) (different : actor ≠ name) (key : Key) :
    location (mark r name phase) actor key = location r actor key := by
  have routing : GuardedApplications.routing (mark r name phase) actor key =
      GuardedApplications.routing r actor key := by
    simp [Stages.bindingOwner, mark_other r actor name phase different]
  rw [GuardedApplications.location_routing, GuardedApplications.location_routing, routing]
  congr 1
  funext owner
  rw [StageRecovery.tableAt_mark]

theorem mark_target (r : R) (name : Name) (fiber : F) (phase)
    (present : r name = some fiber) (availability : phase.available ↔ fiber.phase.available)
    (actor : Name) (view : View Name Key) :
    Target (mark r name phase) actor view ↔ Target r actor view := by
  have providers : ∀ owner key,
      (match mark r name phase owner with
        | none => False
        | some f => f.phase.available ∧ f.table key ≠ none) ↔
      (match r owner with
        | none => False
        | some f => f.phase.available ∧ f.table key ≠ none) := by
    intro owner key
    by_cases same : owner = name
    · subst owner
      simpa [mark, Calculus.modify, present] using and_congr availability (Iff.refl (fiber.table key ≠ none))
    · rw [mark_other r owner name phase same]
  by_cases same : actor = name
  · subst actor
    simp only [Target, mark_self r name fiber phase present, present]
    apply and_congr_right; intro _
    apply forall_congr'; intro key
    apply imp_congr_right; intro _
    have provider := providers (view key) key
    cases old : r (view key) <;> cases new : mark r name phase (view key) <;>
      (simp only [old, new] at provider ⊢ <;> exact provider)
  · simp only [Target, mark_other r actor name phase same]
    cases found : r actor with
    | none => simp
    | some entry =>
      apply and_congr_right; intro _
      apply forall_congr'; intro key
      apply imp_congr_right; intro _
      have provider := providers (view key) key
      cases old : r (view key) <;> cases new : mark r name phase (view key) <;>
        (simp only [old, new] at provider ⊢ <;> exact provider)

theorem write_mark (r : R) (owner name : Name) (phase) (key : Key) (value : Option Value) :
    write (mark r name phase) owner key value = mark (write r owner key value) name phase := by
  funext other
  by_cases atOwner : other = owner <;> by_cases atName : other = name <;>
    simp_all [write, mark, Calculus.modify, Option.map_map, Function.comp_def]

theorem marks_commute (r : R) (actor name : Name) (first second) (different : actor ≠ name) :
    mark (mark r name second) actor first = mark (mark r actor first) name second := by
  funext other
  by_cases atActor : other = actor <;> by_cases atName : other = name <;>
    simp_all [mark, Calculus.modify]

theorem land_mark (program : Code → Instruction Name Key Value Code Error)
    {actor : Name} {code : Code} {r s : R} {inverse next}
    (land : Land program actor code r s inverse next)
    (name : Name) (phase) (different : actor ≠ name) (present : r name ≠ none) :
    Land program actor code (mark r name phase) (mark s name phase) inverse next := by
  cases land with
  | unit _ _ _ action => exact .unit _ _ _ action
  | provide _ _ _ fiber key value action found declared absent =>
    rw [← write_mark]
    exact .provide _ _ _ fiber key value action
      ((mark_other r actor name phase different).trans found) declared absent
  | operate _ _ _ key run owner before after inv result action located called =>
    rw [← write_mark]
    exact .operate _ _ _ key run owner before after inv result action
      ((mark_location r actor name phase different key).trans located) called
  | instantiate _ _ _ component child action ready =>
    have freshName : name ≠ child := by
      intro same
      exact present (same ▸ ready.1)
    rw [mark_put r name child _ phase freshName]
    exact .instantiate _ _ _ component child action ((mark_insertable _ _ _ _ _ _).mpr ready)

theorem activation_after_phase (program : Code → Instruction Name Key Value Code Error)
    {rule : Rule} {actor : Name} {r s : R} (step : Labeled.Step program rule actor r s)
    (active : Activation rule) (name : Name) (fiber : F) (phase)
    (different : actor ≠ name) (present : r name = some fiber)
    (availability : phase.available ↔ fiber.phase.available) :
    Labeled.Step program rule actor (mark r name phase) (mark s name phase) := by
  have existsName : r name ≠ none := by simp [present]
  cases step with
  | begin _ _ entry view found inactive free target =>
    rw [← marks_commute _ _ _ _ _ different]
    exact .begin _ actor entry view ((mark_other r actor name phase different).trans found) inactive
      (by simpa only [ErrorFree, mark_other r actor name phase different] using free)
      ((mark_target r name fiber phase present availability actor view).mpr target)
  | iter _ middle _ entry code acc view inverse next found reloading target land =>
    rw [← marks_commute _ _ _ _ _ different]
    exact .iter _ _ actor entry code acc view inverse next
      ((mark_other r actor name phase different).trans found) reloading
      ((mark_target r name fiber phase present availability actor view).mpr target)
      (land_mark program land name phase different existsName)
  | finish _ middle _ entry code acc view inverse found reloading target land =>
    rw [← marks_commute _ _ _ _ _ different]
    exact .finish _ _ actor entry code acc view inverse
      ((mark_other r actor name phase different).trans found) reloading
      ((mark_target r name fiber phase present availability actor view).mpr target)
      (land_mark program land name phase different existsName)
  | _ => simp [Activation] at active

end Cordis.Transposition
