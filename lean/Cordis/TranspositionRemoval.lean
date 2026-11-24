import Cordis.TranspositionInsertion

/-! Lemma78(2), O-Remove. Actual backwards frames derive all removal guards.
An empty removable table cannot be an operation's resolved input, so moving
removal before the activation preserves the exact callback and continuation. -/
namespace Cordis.Transposition
open Calculus Stages Labeled
universe u
variable {Name Key Value Code Error : Type u}
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
variable [DecidableEq Name] [DecidableEq Key]
set_option linter.unusedSectionVars false

theorem erase_other (r : R) (actor name : Name) (different : actor ≠ name) :
    erase r name actor = r actor := by simp [erase, different]

theorem mark_erase (r : R) (actor name : Name) (phase) (different : actor ≠ name) :
    mark (erase r name) actor phase = erase (mark r actor phase) name := by
  funext other
  by_cases atActor : other = actor <;> by_cases atName : other = name <;>
    simp_all [mark, erase, Calculus.modify]

theorem write_erase (r : R) (owner name : Name) (key : Key) (value : Option Value)
    (different : owner ≠ name) :
    write (erase r name) owner key value = erase (write r owner key value) name := by
  funext other
  by_cases atOwner : other = owner <;> by_cases atName : other = name <;>
    simp_all [write, erase, Calculus.modify]

theorem put_erase (r : R) (child name : Name) (fiber : F) (different : child ≠ name) :
    put (erase r name) child fiber = erase (put r child fiber) name := by
  funext other
  by_cases atChild : other = child <;> by_cases atName : other = name <;> simp_all [put, erase]

theorem removable_present (r : R) (name : Name) (ready : Removable r name) : r name ≠ none := by
  intro absent
  simp [Removable, absent] at ready

theorem removable_tables (r : R) (name : Name) (ready : Removable r name) (key : Key) :
    StageRecovery.tableAt r name key = none := by
  cases found : r name with
  | none => simp [StageRecovery.tableAt, found]
  | some fiber =>
    simp only [Removable, found] at ready
    simpa [StageRecovery.tableAt, found] using ready.2.2.1 key

theorem removable_erase_tables (r : R) (name : Name) (ready : Removable r name)
    (owner : Name) (key : Key) :
    StageRecovery.tableAt (erase r name) owner key = StageRecovery.tableAt r owner key := by
  by_cases same : owner = name
  · subst owner
    simpa [StageRecovery.tableAt, erase] using (removable_tables r name ready key).symm
  · simp [StageRecovery.tableAt, erase, same]

theorem removable_erase_location (r : R) (actor name : Name) (different : actor ≠ name)
    (ready : Removable r name) (key : Key) : location (erase r name) actor key = location r actor key := by
  have routing : GuardedApplications.routing (erase r name) actor key =
      GuardedApplications.routing r actor key := by
    simp [Stages.bindingOwner, erase_other r actor name different]
  rw [GuardedApplications.location_routing, GuardedApplications.location_routing, routing]
  congr 1
  funext owner
  rw [removable_erase_tables r name ready]

theorem removable_erase_target (r : R) (actor name : Name) (different : actor ≠ name)
    (ready : Removable r name) (view : View Name Key) :
    Target (erase r name) actor view ↔ Target r actor view := by
  simp only [Target, erase_other r actor name different]
  cases actorFound : r actor with
  | none => simp
  | some fiber =>
    apply and_congr_right; intro _
    apply forall_congr'; intro key
    apply imp_congr_right; intro _
    by_cases same : view key = name
    · rw [same]
      cases provider : r name with
      | none => simp [erase]
      | some entry =>
        simp only [Removable, provider] at ready
        simp [erase, ready.2.1, Phase.available]
    · simp [erase_other r (view key) name same]

theorem mark_removable_backwards (r : R) (actor name : Name) (phase) (different : actor ≠ name)
    (ready : Removable (mark r actor phase) name) : Removable r name := by
  have entrySame : mark r actor phase name = r name := by simp [mark, Calculus.modify, Ne.symm different]
  simp only [Removable, entrySame] at ready ⊢
  cases found : r name with
  | none => simp [found] at ready
  | some fiber =>
    simp only [found] at ready
    refine ⟨ready.1, ready.2.1, ready.2.2.1, ?_⟩
    intro child
    have noParent := ready.2.2.2 child
    by_cases same : child = actor
    · subst child
      cases parentFound : r actor with
      | none => trivial
      | some entry => simpa [mark, Calculus.modify, parentFound] using noParent
    · simpa [mark, Calculus.modify, same] using noParent

theorem land_removable_backwards (program : Code → Instruction Name Key Value Code Error)
    {actor : Name} {code : Code} {r s : R} {inverse next}
    (land : Land program actor code r s inverse next) (actorFiber : F) (actorFound : r actor = some actorFiber)
    (name : Name) (different : actor ≠ name) (ready : Removable s name) : Removable r name := by
  have earlier : r name ≠ none := by
    intro absent
    obtain ⟨component, _, _, result⟩ := land_new_name program land name absent (removable_present s name ready)
    simp [result, Removable, put, fresh] at ready
  cases found : r name with
  | none => exact False.elim (earlier found)
  | some fiber =>
    obtain ⟨entry, present, _, phase⟩ := Ordering.land_existing_control program land name fiber found
    have flags := RuleEvaluation.land_retirement program land name fiber entry found present
    have frame := TableFrame.land_frame program land actorFiber actorFound name fiber entry
      found present (Ne.symm different)
    simp only [Removable, present] at ready
    simp only [Removable, found]
    refine ⟨flags.trans ready.1, phase.symm.trans ready.2.1, ?_, ?_⟩
    · intro key
      exact (frame key).1.mpr (ready.2.2.1 key)
    · intro child
      cases parentFound : r child with
      | none => trivial
      | some old =>
        obtain ⟨current, currentFound, _, _⟩ := Ordering.land_existing_control program land child old parentFound
        have parentSame := (Frame.land_stable program land child old current parentFound currentFound).2.1
        have noParent := ready.2.2.2 child
        simpa [currentFound, ← parentSame] using noParent

theorem erase_insertable (r : R) (actor child name : Name) (component : Component Key Code)
    (different : actor ≠ name) (ready : Insertable r child component (some actor)) :
    Insertable (erase r name) child component (some actor) := by
  refine ⟨?_, ?_, ?_⟩
  · by_cases same : child = name <;> simp [erase, same, ready.1]
  · intro parent same
    have equal : actor = parent := Option.some.inj same
    subst parent
    simpa [erase, different] using ready.2.1 actor rfl
  · intro other key
    by_cases same : other = name
    · simp [erase, same]
    · simpa [erase, same] using ready.2.2 other key

theorem land_erase (program : Code → Instruction Name Key Value Code Error)
    {actor : Name} {code : Code} {r s : R} {inverse next}
    (land : Land program actor code r s inverse next)
    (name : Name) (different : actor ≠ name) (ready : Removable r name) :
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
      have empty := removable_tables r name ready key
      simp [StageRecovery.tableAt, found, bound] at empty
    rw [← write_erase r owner name _ _ ownerDifferent]
    exact .operate _ _ _ key run owner before after inv result action
      ((removable_erase_location r actor name different ready key).trans located) called
  | instantiate _ _ _ component child action childReady =>
    have childDifferent : child ≠ name := by
      intro same
      exact removable_present r name ready (same ▸ childReady.1)
    rw [← put_erase r child name _ childDifferent]
    exact .instantiate _ _ _ component child action (erase_insertable _ _ _ _ _ different childReady)

/-- Full O-Remove case of Lemma78(2). A newly instantiated child is not retired,
so legal removal already excludes creation of its target by this activation. -/
theorem activation_remove_diamond (program : Code → Instruction Name Key Value Code Error)
    {rule : Rule} {actor : Name} {r s : R}
    (activation : Labeled.Step program rule actor r s) (active : Activation rule)
    (name : Name) (different : actor ≠ name) (ready : Removable s name) :
    Labeled.Step program .remove name r (erase r name) ∧
      Labeled.Step program rule actor (erase r name) (erase s name) := by
  cases activation with
  | begin _ _ fiber view found phase free target =>
    have before := mark_removable_backwards _ _ _ _ different ready
    refine ⟨.remove r name before, ?_⟩
    rw [← mark_erase r actor name _ different]
    exact .begin _ actor fiber view ((erase_other r actor name different).trans found) phase
      (by simpa only [ErrorFree, erase_other r actor name different] using free)
      ((removable_erase_target r actor name different before view).mpr target)
  | iter _ middle _ fiber code acc view inverse next found phase target land =>
    have afterLand := mark_removable_backwards _ _ _ _ different ready
    have before := land_removable_backwards program land fiber found name different afterLand
    refine ⟨.remove r name before, ?_⟩
    rw [← mark_erase middle actor name _ different]
    exact .iter _ _ actor fiber code acc view inverse next ((erase_other r actor name different).trans found) phase
      ((removable_erase_target r actor name different before view).mpr target)
      (land_erase program land name different before)
  | finish _ middle _ fiber code acc view inverse found phase target land =>
    have afterLand := mark_removable_backwards _ _ _ _ different ready
    have before := land_removable_backwards program land fiber found name different afterLand
    refine ⟨.remove r name before, ?_⟩
    rw [← mark_erase middle actor name _ different]
    exact .finish _ _ actor fiber code acc view inverse ((erase_other r actor name different).trans found) phase
      ((removable_erase_target r actor name different before view).mpr target)
      (land_erase program land name different before)
  | _ => simp [Activation] at active

end Cordis.Transposition
