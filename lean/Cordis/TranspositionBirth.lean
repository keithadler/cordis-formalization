import Cordis.TranspositionContexts

/-! The instantiation/landing rows of Lemma78(1)'s primitive diamond.
A just-created child has no bindings, so another already-present actor cannot
read it. Its exact fresh entry survives the other landing; the later reservation
guard is derived from actual disjointness preservation. No swapped landing or
composite commuting equation is a premise. -/
namespace Cordis.Transposition
open Calculus Stages Labeled
universe u
variable {Name Key Value Code Error : Type u}
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
variable [DecidableEq Name] [DecidableEq Key]
set_option linter.unusedSectionVars false

theorem erase_put_fresh (r : R) (name : Name) (fiber : F) (absent : r name = none) :
    erase (put r name fiber) name = r := by
  funext other
  by_cases same : other = name <;> simp_all [erase, put]

theorem put_erase_existing (r : R) (name : Name) (fiber : F) (present : r name = some fiber) :
    put (erase r name) name fiber = r := by
  funext other
  by_cases same : other = name <;> simp_all [erase, put]

theorem empty_erase_location (r : R) (actor name : Name) (different : actor ≠ name)
    (empty : ∀ key, StageRecovery.tableAt r name key = none) (key : Key) :
    location (erase r name) actor key = location r actor key := by
  have routing : GuardedApplications.routing (erase r name) actor key =
      GuardedApplications.routing r actor key := by
    simp [Stages.bindingOwner, erase_other r actor name different]
  rw [GuardedApplications.location_routing, GuardedApplications.location_routing, routing]
  congr 1
  funext owner
  by_cases same : owner = name
  · subst owner
    rw [empty]
    simp [StageRecovery.tableAt, erase]
  · simp [StageRecovery.tableAt, erase, same]

theorem land_erase_empty (program : Code → Instruction Name Key Value Code Error)
    {actor : Name} {code : Code} {r s : R} {inverse next}
    (land : Land program actor code r s inverse next)
    (name : Name) (different : actor ≠ name) (present : r name ≠ none)
    (empty : ∀ key, StageRecovery.tableAt r name key = none) :
    Land program actor code (erase r name) (erase s name) inverse next := by
  cases land with
  | unit _ _ _ action => exact .unit _ _ _ action
  | provide _ _ _ fiber key value action found declared absent =>
    rw [← write_erase r actor name _ _ different]
    exact .provide _ _ _ fiber key value action ((erase_other r actor name different).trans found) declared absent
  | operate _ _ _ key run owner before after inv result action located called =>
    have ownerDifferent : owner ≠ name := by
      intro same
      subst owner
      obtain ⟨entry, found, bound⟩ := Safety.location_binding r actor name key before located
      have absent := empty key
      simp [StageRecovery.tableAt, found, bound] at absent
    rw [← write_erase r owner name _ _ ownerDifferent]
    exact .operate _ _ _ key run owner before after inv result action
      ((empty_erase_location r actor name different empty key).trans located) called
  | instantiate _ _ _ component child action childReady =>
    have childDifferent : child ≠ name := by intro same; exact present (same ▸ childReady.1)
    rw [← put_erase r child name _ childDifferent]
    exact .instantiate _ _ _ component child action (erase_insertable _ _ _ _ _ different childReady)

/-- No successful primitive of a distinct actor can alter a present empty
entry: operations require an existing binding, and birth requires an absent
entry. This includes preservation of the child's nonretired flag. -/
theorem land_empty_entry (program : Code → Instruction Name Key Value Code Error)
    {actor : Name} {code : Code} {r s : R} {inverse next}
    (land : Land program actor code r s inverse next)
    (name : Name) (fiber : F) (different : actor ≠ name) (present : r name = some fiber)
    (empty : ∀ key, fiber.table key = none) : s name = some fiber := by
  cases land with
  | unit => exact present
  | provide => simpa [write, Calculus.modify, Ne.symm different] using present
  | operate _ _ _ key run owner before after inv result action located called =>
    have ownerDifferent : name ≠ owner := by
      intro same
      subst owner
      obtain ⟨entry, found, bound⟩ := Safety.location_binding r actor name key before located
      have sameEntry : fiber = entry := Option.some.inj (present.symm.trans found)
      have absent : entry.table key = none := sameEntry ▸ empty key
      simp [bound] at absent
    simpa [write, Calculus.modify, ownerDifferent] using present
  | instantiate _ _ _ component child action childReady =>
    have childDifferent : name ≠ child := by
      intro same
      have absent : r name = none := same ▸ childReady.1
      simp [present] at absent
    simpa [put, childDifferent] using present

/-- Move a real selected child creation past any successful primitive of an
already-present actor. This retains the exact other inverse/continuation and
the exact chosen child name, including a second fresh child instantiation. -/
theorem fresh_child_landing_exchange (program : Code → Instruction Name Key Value Code Error)
    (r : R) (parent child actor : Name) (component : Component Key Code)
    (code : Code) (actorFiber : F) (actorPresent : r actor = some actorFiber)
    (ready : Insertable r child component (some parent)) (disjoint : WellFormed.Disjoint r)
    {s : R} {inverse next}
    (landing : Land program actor code (put r child (fresh component (some parent))) s inverse next) :
    ∃ middle, Land program actor code r middle inverse next ∧
      Insertable middle child component (some parent) ∧
      s = put middle child (fresh component (some parent)) := by
  have actorDifferent : actor ≠ child := by
    intro same
    have absent : r actor = none := same ▸ ready.1
    simp [actorPresent] at absent
  have childPresent : put r child (fresh component (some parent)) child = some (fresh component (some parent)) := by
    simp [put]
  have retained := land_empty_entry program landing child (fresh component (some parent))
    actorDifferent childPresent (fun _ => rfl)
  have swapped := land_erase_empty program landing child actorDifferent
    (by simp [put]) (by intro key; simp [StageRecovery.tableAt, put, fresh])
  rw [erase_put_fresh r child _ ready.1] at swapped
  have afterDisjoint := WellFormed.land_disjoint program landing
    (WellFormed.insert_disjoint r child component (some parent) ready disjoint)
  refine ⟨erase s child, swapped, ?_, (put_erase_existing s child _ retained).symm⟩
  refine ⟨by simp [erase], ?_, ?_⟩
  · intro p same
    have parentEq : parent = p := Option.some.inj same
    subst p
    have parentPresent := ready.2.1 parent rfl
    have parentDifferent : parent ≠ child := by intro same; exact parentPresent (same ▸ ready.1)
    cases found : r parent with
    | none => exact False.elim (parentPresent found)
    | some entry =>
      have insertedPresent : put r child (fresh component (some parent)) parent = some entry :=
        (put_other r parent child _ parentDifferent).trans found
      obtain ⟨after, afterFound, _, _⟩ := Ordering.land_existing_control program landing parent entry insertedPresent
      simp [erase, parentDifferent, afterFound]
  · intro other key
    by_cases same : other = child
    · simp [erase, same]
    · simp only [erase, if_neg same]
      cases found : s other with
      | none => trivial
      | some entry =>
        intro provided otherProvided
        exact afterDisjoint child other (fresh component (some parent)) entry retained found (Ne.symm same) key
          ⟨provided, otherProvided⟩

/-- The first primitive is its actual instruction and selected continuation,
not a symbolic insertion. The result constructs both swapped Land derivations
and shares the exact original endpoint. -/
theorem instantiation_landing_diamond (program : Code → Instruction Name Key Value Code Error)
    (r : R) (parent child actor : Name) (component : Component Key Code)
    (firstCode secondCode : Code) (actorFiber : F) (actorPresent : r actor = some actorFiber)
    (action : (program firstCode).action = .instantiate component)
    (ready : Insertable r child component (some parent)) (disjoint : WellFormed.Disjoint r)
    {s : R} {inverse next}
    (landing : Land program actor secondCode (put r child (fresh component (some parent))) s inverse next) :
    ∃ middle, Land program actor secondCode r middle inverse next ∧
      Land program parent firstCode middle s (.retire child) ((program firstCode).next (.child child)) := by
  obtain ⟨middle, swapped, stillReady, result⟩ :=
    fresh_child_landing_exchange program r parent child actor component secondCode actorFiber actorPresent ready disjoint landing
  refine ⟨middle, swapped, ?_⟩
  rw [result]
  exact .instantiate middle parent firstCode component child action stillReady

theorem land_insertable_backwards (program : Code → Instruction Name Key Value Code Error)
    {actor : Name} {code : Code} {r s : R} {inverse next}
    (land : Land program actor code r s inverse next)
    (name : Name) (component : Component Key Code) (parent : Option Name)
    (parents : ∀ p, parent = some p → r p ≠ none) (ready : Insertable s name component parent) :
    Insertable r name component parent := by
  have rootReady : Insertable s name component none := by
    refine ⟨ready.1, ?_, ready.2.2⟩
    intro p impossible
    cases impossible
  have before := land_root_insertable_backwards program land name component rootReady
  exact ⟨before.1, parents, before.2.2⟩

theorem insertable_swap_parent (r : R) (actor child name : Name)
    (childComponent component : Component Key Code) (parent : Option Name)
    (childReady : Insertable r child childComponent (some actor))
    (ready : Insertable (put r child (fresh childComponent (some actor))) name component parent) :
    child ≠ name ∧ Insertable (put r name (fresh component parent)) child childComponent (some actor) := by
  have different : child ≠ name := by
    intro same
    have absent := ready.1
    simp [← same, put] at absent
  refine ⟨different, ?_, ?_, ?_⟩
  · simpa [put, different] using childReady.1
  · intro p ancestry
    by_cases same : p = name
    · simp [put, same]
    · simpa [put, same] using childReady.2.1 p ancestry
  · intro other key
    by_cases same : other = name
    · subst other
      simp only [put, fresh]
      intro childProvides provided
      have disjoint := ready.2.2 child key
      simp only [put, fresh] at disjoint
      exact disjoint provided childProvides
    · simpa [put, same] using childReady.2.2 other key

/-- The converse primitive order: an insertion allowed after a landing is
allowed before it when its parent already exists. Real activation actors meet
that condition; it excludes the unrelated unrestricted-external-parent case. -/
theorem land_insert_with_parent (program : Code → Instruction Name Key Value Code Error)
    {actor : Name} {code : Code} {r s : R} {inverse next}
    (land : Land program actor code r s inverse next)
    (name : Name) (component : Component Key Code) (parent : Option Name)
    (different : actor ≠ name) (parents : ∀ p, parent = some p → r p ≠ none)
    (ready : Insertable s name component parent) :
    Land program actor code (put r name (fresh component parent))
      (put s name (fresh component parent)) inverse next := by
  have before := land_insertable_backwards program land name component parent parents ready
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
      ((fresh_put_location r actor name component parent different before.1 key).trans located) called
  | instantiate _ _ _ childComponent child action childReady =>
    obtain ⟨freshName, stillReady⟩ := insertable_swap_parent r actor child name childComponent component parent childReady ready
    rw [← put_put r child name _ _ freshName]
    exact .instantiate _ _ _ childComponent child action stillReady

theorem landing_instantiation_diamond (program : Code → Instruction Name Key Value Code Error)
    {actor : Name} {firstCode : Code} {r s : R} {inverse next}
    (landing : Land program actor firstCode r s inverse next)
    (parent child : Name) (component : Component Key Code) (secondCode : Code)
    (actorFiber : F) (actorPresent : r actor = some actorFiber) (parentPresent : r parent ≠ none)
    (action : (program secondCode).action = .instantiate component)
    (ready : Insertable s child component (some parent)) :
    ∃ middle, Land program parent secondCode r middle (.retire child) ((program secondCode).next (.child child)) ∧
      Land program actor firstCode middle (put s child (fresh component (some parent))) inverse next := by
  have parents : ∀ p, (some parent : Option Name) = some p → r p ≠ none := by
    intro p same
    have equal : parent = p := Option.some.inj same
    simpa [← equal] using parentPresent
  have before := land_insertable_backwards program landing child component (some parent) parents ready
  have different : actor ≠ child := by
    intro same
    have absent : r actor = none := same ▸ before.1
    simp [actorPresent] at absent
  exact ⟨_, .instantiate r parent secondCode component child action before,
    land_insert_with_parent program landing child component (some parent) different parents ready⟩

end Cordis.Transposition
