import Cordis.TranspositionRetirement

/-! The root-only external insertion case of Lemma78(2). Child instantiation
still uses its real parent and chosen fresh name. External provenance matters:
an arbitrary external parent could itself be the child just created. -/
namespace Cordis.Transposition
open Calculus Stages Labeled
universe u
variable {Name Key Value Code Error : Type u}
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
variable [DecidableEq Name] [DecidableEq Key]
set_option linter.unusedSectionVars false

theorem put_other (r : R) (actor name : Name) (fiber : F) (different : actor ≠ name) :
    put r name fiber actor = r actor := by simp [put, different]

theorem mark_put (r : R) (actor name : Name) (fiber : F) (phase)
    (different : actor ≠ name) :
    mark (put r name fiber) actor phase = put (mark r actor phase) name fiber := by
  funext other
  by_cases atActor : other = actor <;> by_cases atName : other = name <;>
    simp_all [mark, put, Calculus.modify]

theorem write_put (r : R) (owner name : Name) (fiber : F) (key : Key) (value : Option Value)
    (different : owner ≠ name) :
    write (put r name fiber) owner key value = put (write r owner key value) name fiber := by
  funext other
  by_cases atOwner : other = owner <;> by_cases atName : other = name <;>
    simp_all [write, put, Calculus.modify]

theorem put_put (r : R) (first second : Name) (left right : F) (different : first ≠ second) :
    put (put r second right) first left = put (put r first left) second right := by
  funext other
  by_cases atFirst : other = first <;> by_cases atSecond : other = second <;> simp_all [put]

theorem fresh_put_tables (r : R) (name : Name) (component : Component Key Code) (parent)
    (absent : r name = none) (owner : Name) (key : Key) :
    StageRecovery.tableAt (put r name (fresh component parent)) owner key =
      StageRecovery.tableAt r owner key := by
  by_cases same : owner = name
  · subst owner; simp [StageRecovery.tableAt, put, fresh, absent]
  · simp [StageRecovery.tableAt, put, same]

theorem fresh_put_location (r : R) (actor name : Name) (component : Component Key Code) (parent)
    (different : actor ≠ name) (absent : r name = none) (key : Key) :
    location (put r name (fresh component parent)) actor key = location r actor key := by
  have routing : GuardedApplications.routing (put r name (fresh component parent)) actor key =
      GuardedApplications.routing r actor key := by
    simp [Stages.bindingOwner, put_other r actor name _ different]
  rw [GuardedApplications.location_routing, GuardedApplications.location_routing, routing]
  congr 1
  funext owner
  rw [fresh_put_tables r name component parent absent]

theorem fresh_put_target (r : R) (actor name : Name) (component : Component Key Code) (parent)
    (different : actor ≠ name) (absent : r name = none) (view : View Name Key) :
    Target (put r name (fresh component parent)) actor view ↔ Target r actor view := by
  simp only [Target, put_other r actor name _ different]
  cases found : r actor with
  | none => simp
  | some fiber =>
    apply and_congr_right; intro _
    apply forall_congr'; intro key
    apply imp_congr_right; intro _
    by_cases same : view key = name
    · simp [same, put, fresh, absent, Phase.available]
    · simp [put_other r (view key) name _ same]

/-- A backwards declaration-frame lemma. Its frame is subsequently derived
from each actual primitive/rule, not assumed as a transposition contract. -/
theorem root_insertable_backwards {r s : R}
    (existing : ∀ name fiber, r name = some fiber →
      ∃ entry, s name = some entry ∧ entry.component = fiber.component)
    (name : Name) (component : Component Key Code) (ready : Insertable s name component none) :
    Insertable r name component none := by
  refine ⟨?_, ?_, ?_⟩
  · cases found : r name with
    | none => rfl
    | some fiber =>
      obtain ⟨entry, present, _⟩ := existing name fiber found
      simp [ready.1] at present
  · intro p impossible
    cases impossible
  · intro other key
    cases found : r other with
    | none => trivial
    | some fiber =>
      obtain ⟨entry, present, same⟩ := existing other fiber found
      have reserved := ready.2.2 other key
      simpa [present, same] using reserved

theorem land_root_insertable_backwards (program : Code → Instruction Name Key Value Code Error)
    {actor : Name} {code : Code} {r s : R} {inverse next}
    (land : Land program actor code r s inverse next)
    (name : Name) (component : Component Key Code) (ready : Insertable s name component none) :
    Insertable r name component none := by
  apply root_insertable_backwards ?_ name component ready
  intro n fiber present
  obtain ⟨entry, found, same, _⟩ := Ordering.land_existing_control program land n fiber present
  exact ⟨entry, found, same⟩

theorem mark_root_insertable_backwards (r : R) (actor : Name) (phase)
    (name : Name) (component : Component Key Code)
    (ready : Insertable (mark r actor phase) name component none) :
    Insertable r name component none := by
  apply root_insertable_backwards ?_ name component ready
  intro n fiber present
  by_cases same : n = actor
  · subst n
    exact ⟨{fiber with phase := phase}, by simp [mark, Calculus.modify, present], rfl⟩
  · exact ⟨fiber, by simp [mark, Calculus.modify, same, present], rfl⟩

theorem location_owner_present (r : R) (actor owner : Name) (key : Key) (value : Value)
    (located : location r actor key = some (owner, value)) : r owner ≠ none := by
  rw [GuardedApplications.location_routing] at located
  cases route : GuardedApplications.routing r actor key with
  | none => simp [route] at located
  | some selected =>
    cases bound : StageRecovery.tableAt r selected key with
    | none => simp [route, bound] at located
    | some before =>
      have pair : (selected, before) = (owner, value) := by simpa [route, bound] using located
      have owners : selected = owner := congrArg Prod.fst pair
      subst selected
      intro absent
      simp [StageRecovery.tableAt, absent] at bound

theorem insertable_swap (r : R) (actor child name : Name)
    (childComponent externalComponent : Component Key Code)
    (childReady : Insertable r child childComponent (some actor))
    (externalReady : Insertable (put r child (fresh childComponent (some actor))) name externalComponent none) :
    child ≠ name ∧ Insertable (put r name (fresh externalComponent none)) child childComponent (some actor) := by
  have different : child ≠ name := by
    intro same
    have absent := externalReady.1
    simp [← same, put] at absent
  refine ⟨different, ?_, ?_, ?_⟩
  · simpa [put, different] using childReady.1
  · intro p parent
    by_cases same : p = name
    · simp [put, same]
    · simpa [put, same] using childReady.2.1 p parent
  · intro other key
    by_cases same : other = name
    · subst other
      simp only [put, fresh]
      intro childProvides externalProvides
      have disjoint := externalReady.2.2 child key
      simp only [put, fresh] at disjoint
      exact disjoint externalProvides childProvides
    · simpa [put, same] using childReady.2.2 other key

/-- A valid root insertion after the chosen landing can be moved before it.
In particular the actual chosen child remains fresh and all outcome-selected
continuations are exactly the same. -/
theorem land_insert (program : Code → Instruction Name Key Value Code Error)
    {actor : Name} {code : Code} {r s : R} {inverse next}
    (land : Land program actor code r s inverse next)
    (name : Name) (component : Component Key Code) (different : actor ≠ name)
    (ready : Insertable s name component none) :
    Land program actor code (put r name (fresh component none))
      (put s name (fresh component none)) inverse next := by
  have before := land_root_insertable_backwards program land name component ready
  cases land with
  | unit _ _ _ action => exact .unit _ _ _ action
  | provide _ _ _ fiber key value action found declared absent =>
    rw [← write_put r actor name _ key _ different]
    exact .provide _ _ _ fiber key value action
      ((put_other r actor name _ different).trans found) declared absent
  | operate _ _ _ key run owner old after inv result action located called =>
    have ownerDifferent : owner ≠ name := by
      intro same
      exact location_owner_present r actor owner key old located (same ▸ before.1)
    rw [← write_put r owner name _ key _ ownerDifferent]
    exact .operate _ _ _ key run owner old after inv result action
      ((fresh_put_location r actor name component none different before.1 key).trans located) called
  | instantiate _ _ _ childComponent child action childReady =>
    obtain ⟨freshName, stillReady⟩ := insertable_swap r actor child name childComponent component childReady ready
    rw [← put_put r child name _ _ freshName]
    exact .instantiate _ _ _ childComponent child action stillReady

theorem activation_insert_diamond (program : Code → Instruction Name Key Value Code Error)
    {rule : Rule} {actor : Name} {r s : R}
    (activation : Labeled.Step program rule actor r s) (active : Activation rule)
    (name : Name) (component : Component Key Code) (different : actor ≠ name)
    (ready : Insertable s name component none) :
    Labeled.Step program .insert name r (put r name (fresh component none)) ∧
      Labeled.Step program rule actor (put r name (fresh component none)) (put s name (fresh component none)) := by
  cases activation with
  | begin _ _ fiber view found phase free target =>
    have before := mark_root_insertable_backwards _ _ _ name component ready
    refine ⟨.insert r name component none before, ?_⟩
    rw [← mark_put r actor name _ _ different]
    exact .begin _ actor fiber view ((put_other r actor name _ different).trans found) phase
      (by simpa only [ErrorFree, put_other r actor name _ different] using free)
      ((fresh_put_target r actor name component none different before.1 view).mpr target)
  | iter _ middle _ fiber code acc view inverse next found phase target land =>
    have afterLand := mark_root_insertable_backwards _ _ _ name component ready
    have before := land_root_insertable_backwards program land name component afterLand
    refine ⟨.insert r name component none before, ?_⟩
    rw [← mark_put middle actor name _ _ different]
    exact .iter _ _ actor fiber code acc view inverse next
      ((put_other r actor name _ different).trans found) phase
      ((fresh_put_target r actor name component none different before.1 view).mpr target)
      (land_insert program land name component different afterLand)
  | finish _ middle _ fiber code acc view inverse found phase target land =>
    have afterLand := mark_root_insertable_backwards _ _ _ name component ready
    have before := land_root_insertable_backwards program land name component afterLand
    refine ⟨.insert r name component none before, ?_⟩
    rw [← mark_put middle actor name _ _ different]
    exact .finish _ _ actor fiber code acc view inverse
      ((put_other r actor name _ different).trans found) phase
      ((fresh_put_target r actor name component none different before.1 view).mpr target)
      (land_insert program land name component different afterLand)
  | _ => simp [Activation] at active

end Cordis.Transposition
