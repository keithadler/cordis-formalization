import Cordis.RuleEvaluation
import Cordis.GuardedApplications

/-! The retirement case of Lemma78(2). These are diamonds for the actual
labelled rules, with literal equality of their endpoints. Retirement changes
neither callback inputs nor fresh-name outcomes, so this case does not need
the observational independence assumptions of Lemma78(1). -/
namespace Cordis.Transposition
open Calculus Stages Labeled
universe u
variable {Name Key Value Code Error : Type u}
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
variable [DecidableEq Name] [DecidableEq Key]
set_option linter.unusedSectionVars false

def Activation (rule : Rule) : Prop :=
  rule = .begin ∨ rule = .iter ∨ rule = .finish

theorem retire_other (r : R) (actor name : Name) (different : actor ≠ name) :
    Calculus.retire r name actor = r actor := by
  simp [Calculus.retire, Calculus.modify, different]

theorem retire_presence (r : R) (name other : Name) :
    Calculus.retire r name other = none ↔ r other = none := by
  by_cases same : other = name <;> simp [Calculus.retire, Calculus.modify, same]

theorem retire_insertable (r : R) (name child : Name) (component : Component Key Code)
    (parent : Option Name) :
    Insertable (Calculus.retire r name) child component parent ↔
      Insertable r child component parent := by
  unfold Insertable
  apply and_congr (retire_presence r name child)
  apply and_congr
  · apply forall_congr'; intro p
    exact imp_congr_right (fun _ => not_congr (retire_presence r name p))
  · apply forall_congr'; intro other
    apply forall_congr'; intro key
    by_cases same : other = name
    · subst other
      cases found : r name <;> simp [Calculus.retire, Calculus.modify, found]
    · simp [retire_other r other name same]

theorem retire_target (r : R) (actor name : Name) (view : View Name Key)
    (different : actor ≠ name) :
    Target (Calculus.retire r name) actor view ↔ Target r actor view := by
  simp only [Target, retire_other r actor name different]
  cases found : r actor with
  | none => simp
  | some fiber =>
    apply and_congr_right; intro _
    apply forall_congr'; intro key
    apply imp_congr_right; intro _
    by_cases same : view key = name
    · rw [same]
      cases provider : r name <;> simp [Calculus.retire, Calculus.modify, provider]
    · simp [retire_other r (view key) name same]

theorem retire_location (r : R) (name actor : Name) (key : Key) :
    location (Calculus.retire r name) actor key = location r actor key := by
  have routing : GuardedApplications.routing (Calculus.retire r name) actor key =
      GuardedApplications.routing r actor key := by
    by_cases same : actor = name
    · subst actor
      cases found : r name <;>
        simp [Stages.bindingOwner, Calculus.retire, Calculus.modify, found]
    · simp [Stages.bindingOwner, retire_other r actor name same]
  rw [GuardedApplications.location_routing, GuardedApplications.location_routing, routing]
  congr 1
  funext owner
  rw [show StageRecovery.tableAt (Calculus.retire r name) owner key = StageRecovery.tableAt r owner key from retire_preserves_tables r name owner key]

theorem modify_retire (r : R) (owner name : Name) (change : F → F)
    (commutes : ∀ fiber, change { fiber with retired := true } =
      { (change fiber) with retired := true }) :
    Calculus.modify (Calculus.retire r name) owner change =
      Calculus.retire (Calculus.modify r owner change) name := by
  funext other
  by_cases atOwner : other = owner <;> by_cases atName : other = name <;>
    simp_all [Calculus.retire, Calculus.modify, Option.map_map, Function.comp_def]

theorem write_retire (r : R) (owner name : Name) (key : Key) (value : Option Value) :
    write (Calculus.retire r name) owner key value =
      Calculus.retire (write r owner key value) name :=
  modify_retire r owner name _ (fun _ => rfl)

theorem mark_retire (r : R) (actor name : Name) (phase) :
    mark (Calculus.retire r name) actor phase = Calculus.retire (mark r actor phase) name :=
  modify_retire r actor name _ (fun _ => rfl)

theorem put_retire (r : R) (child name : Name) (fiber : F) (different : child ≠ name) :
    put (Calculus.retire r name) child fiber = Calculus.retire (put r child fiber) name := by
  funext other
  by_cases atChild : other = child <;> by_cases atName : other = name <;>
    simp_all [put, Calculus.retire, Calculus.modify]

/-- The full selected landing is retained: inverse and `next` are identical,
including the branch selected by an operation result or a fresh child name. -/
theorem land_retire (program : Code → Instruction Name Key Value Code Error)
    {actor : Name} {code : Code} {r s : R} {inverse next}
    (land : Land program actor code r s inverse next)
    (name : Name) (present : r name ≠ none) :
    Land program actor code (Calculus.retire r name) (Calculus.retire s name) inverse next := by
  cases land with
  | unit _ _ _ action => exact .unit _ _ _ action
  | provide _ _ _ fiber key value action found declared absent =>
    rw [← write_retire]
    by_cases same : actor = name
    · subst name
      exact .provide _ _ _ { fiber with retired := true } key value action
        (by simp [Calculus.retire, Calculus.modify, found]) declared absent
    · exact .provide _ _ _ fiber key value action
        ((retire_other r actor name same).trans found) declared absent
  | operate _ _ _ key run owner before after inv result action located called =>
    rw [← write_retire]
    exact .operate _ _ _ key run owner before after inv result action
      ((retire_location r name actor key).trans located) called
  | instantiate _ _ _ component child action ready =>
    have freshName : child ≠ name := by
      intro same
      exact present (same ▸ ready.1)
    rw [← put_retire r child name _ freshName]
    exact .instantiate _ _ _ component child action ((retire_insertable _ _ _ _ _).mpr ready)

/-- No independence or postulated commuting-map premise is needed for foreign
retirement. The target's existence is the only extra requirement here; below it
is recovered from the paper's no-instantiation condition. -/
theorem activation_after_retirement (program : Code → Instruction Name Key Value Code Error)
    {rule : Rule} {actor : Name} {r s : R} (step : Labeled.Step program rule actor r s)
    (active : Activation rule) (name : Name) (different : actor ≠ name)
    (present : r name ≠ none) :
    Labeled.Step program rule actor (Calculus.retire r name) (Calculus.retire s name) := by
  cases step with
  | begin _ _ fiber view found phase free target =>
    rw [← mark_retire]
    exact .begin _ actor fiber view ((retire_other _ _ _ different).trans found) phase
      (by simpa only [ErrorFree, retire_other r actor name different] using free)
      ((retire_target _ _ _ _ different).mpr target)
  | iter _ middle _ fiber code acc view inverse next found phase target land =>
    rw [← mark_retire]
    exact .iter _ _ actor fiber code acc view inverse next
      ((retire_other _ _ _ different).trans found) phase
      ((retire_target _ _ _ _ different).mpr target)
      (land_retire program land name present)
  | finish _ middle _ fiber code acc view inverse found phase target land =>
    rw [← mark_retire]
    exact .finish _ _ actor fiber code acc view inverse
      ((retire_other _ _ _ different).trans found) phase
      ((retire_target _ _ _ _ different).mpr target)
      (land_retire program land name present)
  | _ => simp [Activation] at active

/-- The concrete child-creation event, retaining the selected component,
program instruction, fresh name, and parent pointer. On an actual activation,
`activation_creates_iff` identifies this with entry creation at that name. -/
def CreatesChild (program : Code → Instruction Name Key Value Code Error)
    (actor : Name) (r s : R) (child : Name) : Prop :=
  ∃ code component phase,
    (program code).action = .instantiate component ∧
    Insertable r child component (some actor) ∧
    s = mark (put r child (fresh component (some actor))) actor phase

theorem land_new_name_with_token (program : Code → Instruction Name Key Value Code Error)
    {actor : Name} {code : Code} {r s : R} {inverse next}
    (land : Land program actor code r s inverse next)
    (name : Name) (absent : r name = none) (present : s name ≠ none) :
    inverse = .retire name ∧ ∃ component, (program code).action = .instantiate component ∧
      Insertable r name component (some actor) ∧
      s = put r name (fresh component (some actor)) := by
  cases land with
  | unit => exact False.elim (present absent)
  | provide _ _ _ fiber key value action found declared empty =>
    simp [write, Calculus.modify, absent] at present
  | operate _ _ _ key run owner before after inv result action located called =>
    simp [write, Calculus.modify, absent] at present
  | instantiate _ _ _ component child action ready =>
    by_cases same : name = child
    · subst child
      exact ⟨rfl, component, action, ready, rfl⟩
    · simp [put, same, absent] at present

theorem land_new_name (program : Code → Instruction Name Key Value Code Error)
    {actor : Name} {code : Code} {r s : R} {inverse next}
    (land : Land program actor code r s inverse next)
    (name : Name) (absent : r name = none) (present : s name ≠ none) :
    ∃ component, (program code).action = .instantiate component ∧
      Insertable r name component (some actor) ∧
      s = put r name (fresh component (some actor)) :=
  (land_new_name_with_token program land name absent present).2

theorem activation_creates_iff (program : Code → Instruction Name Key Value Code Error)
    {rule : Rule} {actor : Name} {r s : R} (step : Labeled.Step program rule actor r s)
    (active : Activation rule) (name : Name) (different : actor ≠ name) :
    CreatesChild program actor r s name ↔ r name = none ∧ s name ≠ none := by
  constructor
  · rintro ⟨code, component, phase, _, ready, rfl⟩
    exact ⟨ready.1, by simp [mark, Calculus.modify, Ne.symm different, put]⟩
  · rintro ⟨absent, present⟩
    cases step with
    | begin _ _ fiber view found phase free target =>
      simp [mark, Calculus.modify, Ne.symm different, absent] at present
    | iter _ middle _ fiber code acc view inverse next found phase target land =>
      have middlePresent : middle name ≠ none := by
        simpa [mark, Calculus.modify, Ne.symm different] using present
      obtain ⟨component, action, ready, equal⟩ := land_new_name program land name absent middlePresent
      exact ⟨code, component, .reloading next (inverse :: acc) view, action, ready,
        congrArg (fun t => mark t actor (.reloading next (inverse :: acc) view)) equal⟩
    | finish _ middle _ fiber code acc view inverse found phase target land =>
      have middlePresent : middle name ≠ none := by
        simpa [mark, Calculus.modify, Ne.symm different] using present
      obtain ⟨component, action, ready, equal⟩ := land_new_name program land name absent middlePresent
      exact ⟨code, component, .active (inverse :: acc) view, action, ready,
        congrArg (fun t => mark t actor (.active (inverse :: acc) view)) equal⟩
    | _ => simp [Activation] at active

end Cordis.Transposition
