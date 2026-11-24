import Cordis.Repairs.Vestigial
import Cordis.PaperStateObservation

/-!
The converse of vestigial erasure under the two guards the projection can
relax. A restored row can reserve a name or provision, including for nested
allocation. Its parent pointer can also block removal of its parent.
-/
namespace Cordis.Repairs.Vestigial
open Calculus Stages StageRecovery Transposition LegalHistory OrchestrationSorting
universe u
variable {Name Key Value Code Error : Type u} [DecidableEq Name] [DecidableEq Key]
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
local notation "I" => Inverse Name Key Value
local notation "Program" => Code → Instruction Name Key Value Code Error

def CompatibleBirths (before after : R) (forgotten : Name) : Prop :=
  ∀ name row, erase before forgotten name = none → after name = some row →
    name ≠ forgotten ∧ ∀ old, before forgotten = some old →
      ∀ key, row.component.provides key = true → old.component.provides key ≠ true

omit [DecidableEq Key] in
private theorem insertable_restore (r : R) {forgotten name : Name} {component : Component Key Code}
    {parent : Option Name} (ready : Insertable (erase r forgotten) name component parent)
    (different : name ≠ forgotten)
    (disjoint : ∀ old, r forgotten = some old →
      ∀ key, component.provides key = true → old.component.provides key ≠ true) :
    Insertable r name component parent := by
  refine ⟨by simpa [erase, different] using ready.1, ?_, ?_⟩
  · intro name parent missing
    exact ready.2.1 name parent (by simp [erase, missing])
  · intro name key
    by_cases same : name = forgotten
    · subst name
      cases found : r forgotten with
      | none => trivial
      | some row => exact disjoint row found key
    · simpa [erase, same] using ready.2.2 name key

omit [DecidableEq Key] in
theorem removable_restore {before : R} {forgotten actor : Name} (different : actor ≠ forgotten)
    (ready : Removable (erase before forgotten) actor)
    (notChild : ∀ row, before forgotten = some row → row.parent ≠ some actor) :
    Removable before actor := by
  rw [Removable, show erase before forgotten actor = before actor by simp [erase, different]] at ready
  cases found : before actor with
  | none => simp [found] at ready
  | some row =>
    simp only [found] at ready
    simp only [Removable, found]
    refine ⟨ready.1, ready.2.1, ready.2.2.1, ?_⟩
    intro name
    by_cases same : name = forgotten
    · subst name
      cases other : before forgotten with
      | none => trivial
      | some child => exact notChild child other
    · simpa [erase, same] using ready.2.2.2 name

omit [DecidableEq Key] in
private theorem compatibleBirths_unmark {before middle : R} {forgotten actor : Name}
    {phase : Phase Name Key Code I} (actorPresent : erase before forgotten actor ≠ none)
    (guard : CompatibleBirths before (mark middle actor phase) forgotten) :
    CompatibleBirths before middle forgotten := by
  intro name row absent present
  by_cases same : name = actor
  · subst name
    exact False.elim (actorPresent absent)
  · apply guard name row absent
    simpa [mark, Calculus.modify, same] using present

private theorem land_restore (program : Program) {before after : R} {actor forgotten : Name}
    {code : Code} {token : I} {next : Option Code}
    (landed : Land program actor code (erase before forgotten) after token next)
    (different : actor ≠ forgotten) (ready : Removable before forgotten)
    (births : CompatibleBirths before after forgotten) :
    ∃ result, Land program actor code before result token next ∧ erase result forgotten = after := by
  generalize source : erase before forgotten = initial at landed
  cases landed with
  | unit _ _ _ action => exact ⟨before, .unit _ _ _ action, source⟩
  | provide _ _ _ row key value action found declared absent =>
    subst initial
    have present : before actor = some row := (erase_other before actor forgotten different).symm.trans found
    exact ⟨_, .provide _ _ _ row key value action present declared absent,
      (write_erase before actor forgotten key _ different).symm⟩
  | operate _ _ _ key call owner old new inv result action input output =>
    subst initial
    rw [removable_erase_location _ _ _ different ready] at input
    have stays : owner ≠ forgotten := by
      intro same
      subst owner
      obtain ⟨row, found, bound⟩ := Safety.location_binding before actor forgotten key old input
      have empty := removable_tables before forgotten ready key
      simp [tableAt, found, bound] at empty
    exact ⟨_, .operate _ _ _ key call owner old new inv result action input output,
      (write_erase before owner forgotten key _ stays).symm⟩
  | instantiate _ _ _ component name action allowed =>
    subst initial
    obtain ⟨freshName, disjoint⟩ := births name (fresh component (some actor)) allowed.1 (put_self _ _ _)
    exact ⟨_, .instantiate _ _ _ component name action
      (insertable_restore before allowed freshName disjoint), (put_erase _ _ _ _ freshName).symm⟩

variable {program : Code → Instruction Name Key Value Code Error}

theorem lifecycle_restore (kind : Lifecycle) {actor forgotten : Name} {before after : R}
    (step : Labeled.Step program kind.rule actor (erase before forgotten) after)
    (different : actor ≠ forgotten) (ready : Removable before forgotten)
    (births : CompatibleBirths before after forgotten) :
    ∃ full, Labeled.Step program kind.rule actor before full ∧ erase full forgotten = after := by
  generalize source : erase before forgotten = initial at step
  cases kind with
  | begin =>
    cases step with
    | begin _ _ row view found phase free target =>
      subst initial
      have present := (erase_other before actor forgotten different).symm.trans found
      exact ⟨_, .begin _ _ row _ present phase (by simp [present])
        ((removable_erase_target _ _ _ different ready _).mp target), (mark_erase _ _ _ _ different).symm⟩
  | iter =>
    cases step with
    | iter _ middle _ row code acc view inverse next found phase target landed =>
      subst initial
      obtain ⟨full, performed, rfl⟩ := land_restore program landed different ready
        (compatibleBirths_unmark (by simp [found]) births)
      exact ⟨_, .iter _ _ _ row _ _ _ _ _ ((erase_other _ _ _ different).symm.trans found) phase
        ((removable_erase_target _ _ _ different ready _).mp target) performed,
        (mark_erase _ _ _ _ different).symm⟩
  | finish =>
    cases step with
    | finish _ middle _ row code acc view inverse found phase target landed =>
      subst initial
      obtain ⟨full, performed, rfl⟩ := land_restore program landed different ready
        (compatibleBirths_unmark (by simp [found]) births)
      exact ⟨_, .finish _ _ _ row _ _ _ _ ((erase_other _ _ _ different).symm.trans found) phase
        ((removable_erase_target _ _ _ different ready _).mp target) performed,
        (mark_erase _ _ _ _ different).symm⟩
  | divert =>
    cases step with
    | divert _ middle _ row code acc view tail found phase target alternative =>
      subst initial
      have present := (erase_other before actor forgotten different).symm.trans found
      have noTarget : ¬ Target before actor view :=
        fun yes => target ((removable_erase_target _ _ _ different ready _).mpr yes)
      rcases alternative with ⟨rfl, rfl⟩ | ⟨inverse, next, landed, rfl⟩
      · exact ⟨_, .divert before before _ row _ _ _ [] present phase noTarget (.inl ⟨rfl, rfl⟩),
          (mark_erase _ _ _ _ different).symm⟩
      · obtain ⟨full, performed, rfl⟩ := land_restore program landed different ready
          (compatibleBirths_unmark (by simp [found]) births)
        exact ⟨_, .divert _ _ _ row _ _ _ _ present phase noTarget (.inr ⟨_, _, performed, rfl⟩),
          (mark_erase _ _ _ _ different).symm⟩
  | leave =>
    cases step with
    | leave _ _ row acc view found phase target =>
      subst initial
      exact ⟨_, .leave _ _ row _ _ ((erase_other _ _ _ different).symm.trans found) phase
        (fun yes => target ((removable_erase_target _ _ _ different ready _).mpr yes)),
        (mark_erase _ _ _ _ different).symm⟩
  | unload =>
    cases step with
    | unload _ _ row acc view found phase free =>
      subst initial
      refine ⟨_, .unload _ _ row _ _ ((erase_other _ _ _ different).symm.trans found) phase
        (fun yes => free ((erase_relied ready).mpr yes)), ?_⟩
      rw [← mark_erase _ _ _ _ different, ← discharge_erase]

def RestoredChildGuard (before : R) (forgotten : Name) : Event Name Key Code → Prop
  | .command (.remove actor) => ∀ row, before forgotten = some row → row.parent ≠ some actor
  | _ => True

/-- Converse for the repaired Lemma 62. Both sides use the same native
event. For nested allocation as for root insertion, the new row must remain
insertable with the omitted entry present. -/
theorem event_restore {event : Event Name Key Code} {forgotten : Name} {before after : R}
    (step : event.Step program (erase before forgotten) after)
    (different : eventActor event ≠ forgotten)
    (ready : Removable before forgotten) (births : CompatibleBirths before after forgotten)
    (noChild : RestoredChildGuard before forgotten event) :
    ∃ original, event.Step program before original ∧ erase original forgotten = after := by
  cases event with
  | lifecycle kind actor => exact lifecycle_restore kind step different ready births
  | command command =>
    obtain ⟨enabled, rfl⟩ := step
    cases command with
    | insert actor component =>
      obtain ⟨freshName, disjoint⟩ :=
        births actor (fresh component none) enabled.1 (put_self _ _ _)
      exact ⟨_, ⟨insertable_restore before enabled freshName disjoint, rfl⟩,
        (put_erase _ _ _ _ freshName).symm⟩
    | retire actor =>
      have present : before actor ≠ none := by
        intro absent
        exact enabled ((erase_other before actor forgotten different).trans absent)
      exact ⟨_, ⟨present, rfl⟩, (modify_erase before actor forgotten _).symm⟩
    | remove actor =>
      exact ⟨_, ⟨removable_restore different enabled noChild, rfl⟩, erase_erase before actor forgotten⟩

/-- On a disjoint registry, the two restoration guards are also necessary
for a lift of the same event with the same projected endpoint. -/
theorem event_restore_iff {event : Event Name Key Code} {forgotten : Name} {before after : R}
    (step : event.Step program (erase before forgotten) after)
    (different : eventActor event ≠ forgotten) (ready : Removable before forgotten)
    (disjoint : WellFormed.Disjoint before) :
    (∃ original, event.Step program before original ∧ erase original forgotten = after) ↔
      CompatibleBirths before after forgotten ∧ RestoredChildGuard before forgotten event := by
  constructor
  · rintro ⟨original, transition, rfl⟩
    refine ⟨?_, ?_⟩
    · intro name row _ found
      have distinct : name ≠ forgotten := by
        intro equal
        subst name
        simp [erase] at found
      refine ⟨distinct, ?_⟩
      intro old oldAt key provided overlaps
      have native := transition.toCalculus
      have still := (event_erase transition different ready).1
      cases restored : original forgotten with
      | none => simp [Removable, restored] at still
      | some current =>
        have same := (Frame.step_stable program native forgotten old current oldAt restored).1
        have present : original name = some row :=
          (erase_other original name forgotten distinct).symm.trans found
        exact WellFormed.step_disjoint program native disjoint name forgotten row current
          present restored distinct key ⟨provided, same ▸ overlaps⟩
    · cases event with
      | lifecycle => trivial
      | command command =>
        cases command with
        | insert | retire => trivial
        | remove actor =>
          intro row found
          have enabled := transition.1
          cases actorAt : before actor with
          | none => simp [Command.Enabled, Removable, actorAt] at enabled
          | some present =>
            simp only [Command.Enabled, Removable, actorAt] at enabled
            simpa only [found] using enabled.2.2.2 forgotten
  · intro guards
    exact event_restore step different ready guards.1 guards.2

/-- Erasure preserves the paper's table-only observation at every key. -/
theorem tables_related (observe : Key → Setoid Value)
    {before : R} {forgotten : Name} (ready : Removable before forgotten) :
    PaperStateObservation.TablesRelatedAt observe (fun _ => True) before (erase before forgotten) := by
  intro key _
  constructor
  · intro owner value found
    exact ⟨owner, value, (removable_erase_tables before forgotten ready owner key).trans found,
      (observe key).iseqv.refl value⟩
  · intro owner value found
    exact ⟨owner, value, (removable_erase_tables before forgotten ready owner key).symm.trans found,
      (observe key).iseqv.refl value⟩

end Cordis.Repairs.Vestigial
