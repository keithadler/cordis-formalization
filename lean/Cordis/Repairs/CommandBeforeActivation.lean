import Cordis.Repairs.Vestigial
import Cordis.TranspositionBegin

/-! Moving a subsequent activation before an insertion or retirement.
The actual selected landing, inverse and continuation are preserved. -/
namespace Cordis.Repairs.CausalCommands
open Calculus Stages Labeled Transposition OrchestrationSorting
universe u
variable {Name Key Value Code Error : Type u} [DecidableEq Name] [DecidableEq Key]
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "Cmd" => Command Name Key Code
variable {program : Code → Instruction Name Key Value Code Error}

private theorem land_before_retire {before after : R} {actor name : Name}
    {code : Code} {token : Inverse Name Key Value} {next : Option Code}
    (land : Land program actor code (Calculus.retire before name) after token next)
    (different : actor ≠ name) (present : before name ≠ none) :
    ∃ middle, Land program actor code before middle token next ∧ Calculus.retire middle name = after := by
  generalize source : Calculus.retire before name = initial at land
  cases land with
  | unit _ _ _ action => exact ⟨before, .unit _ _ _ action, source⟩
  | provide _ _ _ row key value action found declared absent =>
    subst initial
    rw [retire_other _ _ _ different] at found
    exact ⟨_, .provide _ _ _ row key value action found declared absent, (write_retire _ _ _ _ _).symm⟩
  | operate _ _ _ key run owner old new inv result action located called =>
    subst initial
    rw [retire_location] at located
    exact ⟨_, .operate _ _ _ key run owner old new inv result action located called, (write_retire _ _ _ _ _).symm⟩
  | instantiate _ _ _ component child action ready =>
    subst initial
    have freshName : child ≠ name := by
      intro same
      apply present
      exact (retire_presence _ _ _).mp (same ▸ ready.1)
    exact ⟨_, .instantiate _ _ _ component child action ((retire_insertable _ _ _ _ _).mp ready),
      (put_retire _ _ _ _ freshName).symm⟩

/-- Retirement cannot enable an actual activation of another actor. -/
theorem activation_before_retire {before after : R} {actor name : Name} {rule : Rule}
    (step : Labeled.Step program rule actor (Calculus.retire before name) after)
    (active : Activation rule) (different : actor ≠ name) (present : before name ≠ none) :
    ∃ middle, Labeled.Step program rule actor before middle ∧
      (Command.retire (Key := Key) (Code := Code) name).Step middle after := by
  have construct : ∃ middle, Labeled.Step program rule actor before middle ∧ Calculus.retire middle name = after := by
    generalize source : Calculus.retire before name = initial at step
    cases step with
    | begin _ _ row view found phase _ target =>
      subst initial
      rw [retire_other _ _ _ different] at found
      exact ⟨_, .begin _ _ row view found phase (by simp [found]) ((retire_target _ _ _ _ different).mp target),
        (mark_retire _ _ _ _).symm⟩
    | iter _ stage _ row code word view inverse next found phase target land =>
      subst initial
      rw [retire_other _ _ _ different] at found
      obtain ⟨middle, earlier, rfl⟩ := land_before_retire land different present
      exact ⟨_, .iter _ _ _ row code word view inverse next found phase
        ((retire_target _ _ _ _ different).mp target) earlier, (mark_retire _ _ _ _).symm⟩
    | finish _ stage _ row code word view inverse found phase target land =>
      subst initial
      rw [retire_other _ _ _ different] at found
      obtain ⟨middle, earlier, rfl⟩ := land_before_retire land different present
      exact ⟨_, .finish _ _ _ row code word view inverse found phase
        ((retire_target _ _ _ _ different).mp target) earlier, (mark_retire _ _ _ _).symm⟩
    | _ => simp [Activation] at active
  obtain ⟨middle, earlier, ends⟩ := construct
  have still : middle name ≠ none := by
    intro gone
    cases original : before name with
    | none => exact present original
    | some row =>
      obtain ⟨table, kept⟩ := activation_other_table program earlier active name row (Ne.symm different) original
      rw [gone] at kept
      cases kept
  exact ⟨middle, earlier, still, ends.symm⟩

omit [DecidableEq Key] in
private theorem erase_retire_self (state : R) (name : Name) :
    erase (Calculus.retire state name) name = erase state name := by
  funext other
  by_cases same : other = name <;> simp [erase, Calculus.retire, Calculus.modify, same]

/-- A fresh external insertion changes the activation's admissibility
only when it supplies the acting row. Its fresh empty row cannot be used as
a dependency or modified by a foreign activation. -/
theorem activation_before_insert {before after : R} {actor name : Name} (component : Component Key Code)
    {kind : LegalHistory.Lifecycle}
    (ready : Insertable before name component none)
    (step : Labeled.Step program kind.rule actor (put before name (fresh component none)) after)
    (active : Activation kind.rule) (different : actor ≠ name) (parents : Safety.ParentClosed before)
    (disjoint : WellFormed.Disjoint after) :
    ∃ middle, Labeled.Step program kind.rule actor before middle ∧
      (Command.insert name component).Step middle after := by
  let root := (fresh component none : Fiber Name Key Value Code (Inverse Name Key Value) Error)
  let inserted := put before name root
  have found : inserted name = some root := put_self _ _ _
  have still : after name = some root := by
    obtain ⟨table, present, domain⟩ :=
      activation_other_table_domains program step active name root (Ne.symm different) found
    have empty : table = fun _ => none := funext fun key => (domain key).mpr rfl
    rw [empty] at present
    exact present
  have removable : Removable (Calculus.retire inserted name) name := by
    have retired : Calculus.retire inserted name name = some {root with retired := true} := by
      simp [Calculus.retire, Calculus.modify, found]
    simp only [Removable, retired]
    refine ⟨trivial, rfl, fun _ => rfl, ?_⟩
    intro other
    by_cases same : other = name
    · subst other
      rw [retired]
      change (none : Option Name) ≠ some name
      simp
    · rw [retire_other _ _ _ same]
      unfold inserted
      rw [put_other _ _ _ _ same]
      cases old : before other with
      | none => trivial
      | some row =>
        exact fun parent => parents other row name old parent ready.1
  have present : inserted name ≠ none := by simp [found]
  have decorated := activation_after_retirement program step active name different present
  have earlier := (Vestigial.lifecycle_erase kind decorated different removable).2
  have cancelled : erase inserted name = before := by
    funext other
    by_cases same : other = name
    · subst other
      simp [erase, ready.1]
    · simp [inserted, erase, put, same]
  rw [erase_retire_self, erase_retire_self, cancelled] at earlier
  refine ⟨erase after name, earlier, ?_, ?_⟩
  · refine ⟨by simp [erase], by simp, ?_⟩
    intro other key
    by_cases same : other = name
    · simp [erase, same]
    · rw [erase_other _ _ _ same]
      cases atOther : after other with
      | none => trivial
      | some row =>
        exact fun required declared =>
          disjoint other name row root atOther still same key ⟨declared, required⟩
  · show after = put (erase after name) name root
    funext other
    by_cases same : other = name
    · subst other
      simpa [put] using still
    · simp [put, erase, same]

end Cordis.Repairs.CausalCommands
