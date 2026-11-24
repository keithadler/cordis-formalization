import Cordis.TableFrame
import Cordis.StageRecovery

/-! Definition58 and Lemma59's state-application/edit split. Application kinds
record syntax, not inequality between extensional functions: an iterator and an
accumulator can both denote the identity. No off-domain extension of a captured
iteration is chosen here; the relation records its actual application. -/
namespace Cordis.RuleEvaluation
open Calculus Stages Labeled
universe u
variable {Name Key Value Code Error : Type u}
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
variable [DecidableEq Name] [DecidableEq Key]
set_option linter.unusedSectionVars false

inductive Use (Name Key Value Code : Type u) where
  | identity
  | iteration (code : Code)
  | accumulator (inverses : List (Inverse Name Key Value))

inductive Application (program : Code → Instruction Name Key Value Code Error) (actor : Name) :
    Use Name Key Value Code → R → R → Prop
  | identity (r) : Application program actor .identity r r
  | iteration (code r s inverse next) : Land program actor code r s inverse next →
      Application program actor (.iteration code) r s
  | accumulator (inverses r) :
      Application program actor (.accumulator inverses) r (discharge Stages.undo inverses r)

inductive Edit (Name Key Value Code : Type u) where
  | insert (name : Name) (component : Component Key Code) (parent : Option Name)
  | retire (name : Name)
  | remove (name : Name)
  | phase (name : Name) (value : Phase Name Key Code (Inverse Name Key Value))

def Edit.apply (edit : Edit Name Key Value Code) (r : R) : R :=
  match edit with
  | .insert n c p => put r n (fresh c p)
  | .retire n => Calculus.retire r n
  | .remove n => erase r n
  | .phase n p => mark r n p

def Edit.valid (edit : Edit Name Key Value Code) (r : R) : Prop :=
  match edit with
  | .insert n _ _ => r n = none
  | .remove n => ∀ k, StageRecovery.tableAt r n k = none
  | _ => True

def TablesUnchanged (r s : R) : Prop :=
  ∀ n k, StageRecovery.tableAt r n k = StageRecovery.tableAt s n k

theorem Edit.preserves_tables (edit : Edit Name Key Value Code) (r : R)
    (valid : edit.valid r) : TablesUnchanged r (edit.apply r) := by
  intro n k
  cases edit with
  | insert actor c p =>
    by_cases same : n = actor
    · subst n
      simp [Edit.apply, StageRecovery.tableAt, put, fresh, show r actor = none from valid]
    · simp [Edit.apply, StageRecovery.tableAt, put, same]
  | retire actor => exact (retire_preserves_tables r actor n k).symm
  | remove actor =>
    by_cases same : n = actor
    · subst n
      simpa [Edit.apply, StageRecovery.tableAt, erase] using valid k
    · simp [Edit.apply, StageRecovery.tableAt, erase, same]
  | phase actor value => exact (StageRecovery.tableAt_mark r actor n k value).symm

def Use.allowed (rule : Rule) (r : R) (actor : Name) (use : Use Name Key Value Code) : Prop :=
  match use with
  | .identity => rule = .insert ∨ rule = .retire ∨ rule = .remove ∨
      rule = .begin ∨ rule = .divert ∨ rule = .leave
  | .iteration code => (rule = .iter ∨ rule = .finish ∨ rule = .divert) ∧
      ∃ f acc view, r actor = some f ∧ f.phase = .reloading code acc view
  | .accumulator acc => rule = .unload ∧
      ∃ f view, r actor = some f ∧ f.phase = .unloading acc view

def Edit.allowed (rule : Rule) (actor : Name) (edit : Edit Name Key Value Code) : Prop :=
  match edit with
  | .insert n _ _ => rule = .insert ∧ n = actor
  | .retire n => rule = .retire ∧ n = actor
  | .remove n => rule = .remove ∧ n = actor
  | .phase n _ => n = actor ∧
      (rule = .begin ∨ rule = .iter ∨ rule = .finish ∨ rule = .divert ∨ rule = .leave ∨ rule = .unload)

/-- Every one of the actual nine rules factors through a real state application
and a table-preserving control edit. A recovery application is the accumulator
in the acting fiber's source phase, and occurs only at L-Unload. -/
theorem step_factorization (program : Code → Instruction Name Key Value Code Error)
    {rule : Rule} {actor : Name} {r s : R} (step : Labeled.Step program rule actor r s) :
    ∃ (use : Use Name Key Value Code) (middle : R) (edit : Edit Name Key Value Code),
      Application program actor use r middle ∧ use.allowed rule r actor ∧
      edit.allowed rule actor ∧ edit.valid middle ∧ s = edit.apply middle ∧
      TablesUnchanged middle s := by
  suffices ∃ (use : Use Name Key Value Code) (middle : R) (edit : Edit Name Key Value Code),
      Application program actor use r middle ∧ use.allowed rule r actor ∧
      edit.allowed rule actor ∧ edit.valid middle ∧ s = edit.apply middle by
    obtain ⟨use, middle, edit, applied, permitted, rightEdit, valid, result⟩ := this
    exact ⟨use, middle, edit, applied, permitted, rightEdit, valid, result,
      by rw [result]; exact edit.preserves_tables middle valid⟩
  cases step with
  | insert _ _ c p ready =>
    exact ⟨.identity, r, .insert actor c p, .identity r, by simp [Use.allowed],
      ⟨rfl, rfl⟩, ready.1, rfl⟩
  | retire _ _ _ =>
    exact ⟨.identity, r, .retire actor, .identity r, by simp [Use.allowed],
      ⟨rfl, rfl⟩, trivial, rfl⟩
  | remove _ _ ready =>
    refine ⟨.identity, r, .remove actor, .identity r, by simp [Use.allowed], ⟨rfl, rfl⟩, ?_, rfl⟩
    cases present : r actor with
    | none => simp [Removable, present] at ready
    | some f =>
      have ready' := ready
      simp only [Removable, present] at ready'
      have empty := ready'.2.2.1
      simpa [Edit.valid, StageRecovery.tableAt, present] using empty
  | begin _ _ f view present phase _ _ =>
    exact ⟨.identity, r, .phase actor (.reloading f.component.entry [] view), .identity r,
      by simp [Use.allowed], by simp [Edit.allowed], trivial, rfl⟩
  | iter _ middle _ f code acc view inv next present phase _ land =>
    exact ⟨.iteration code, middle, .phase actor (.reloading next (inv :: acc) view),
      .iteration code r middle inv (some next) land,
      ⟨by simp, f, acc, view, present, phase⟩, by simp [Edit.allowed], trivial, rfl⟩
  | finish _ middle _ f code acc view inv present phase _ land =>
    exact ⟨.iteration code, middle, .phase actor (.active (inv :: acc) view),
      .iteration code r middle inv none land,
      ⟨by simp, f, acc, view, present, phase⟩, by simp [Edit.allowed], trivial, rfl⟩
  | divert _ middle _ f code acc view tail present phase _ alternative =>
    rcases alternative with ⟨same, nil⟩ | ⟨inv, next, land, single⟩
    · subst middle tail
      exact ⟨.identity, r, .phase actor (.unloading acc view), .identity r,
        by simp [Use.allowed], by simp [Edit.allowed], trivial, rfl⟩
    · subst tail
      exact ⟨.iteration code, middle, .phase actor (.unloading (inv :: acc) view),
        .iteration code r middle inv next land,
        ⟨by simp, f, acc, view, present, phase⟩, by simp [Edit.allowed], trivial, rfl⟩
  | leave _ _ f acc view present phase _ =>
    exact ⟨.identity, r, .phase actor (.unloading acc view), .identity r,
      by simp [Use.allowed], by simp [Edit.allowed], trivial, rfl⟩
  | unload _ _ f acc view present phase _ =>
    exact ⟨.accumulator acc, discharge Stages.undo acc r, .phase actor .inactive,
      .accumulator acc r, ⟨rfl, f, view, present, phase⟩,
      by simp [Edit.allowed], trivial, rfl⟩

def RetirementStable (r s : R) : Prop :=
  ∀ n f g, r n = some f → s n = some g → f.retired = g.retired

theorem modify_retirement (r : R) (owner : Name) (change : F → F)
    (same : ∀ f, (change f).retired = f.retired) : RetirementStable r (Calculus.modify r owner change) := by
  intro n f g hf hg
  by_cases eq : n = owner
  · subst n
    have h : change f = g := Option.some.inj (by simpa [Calculus.modify, hf] using hg)
    subst g
    exact (same f).symm
  · have h : f = g := Option.some.inj (by simpa [Calculus.modify, eq, hf] using hg)
    subst g
    rfl

theorem put_retirement (r : R) (owner : Name) (new : F) (absent : r owner = none) :
    RetirementStable r (put r owner new) := by
  intro n f g hf hg
  have different : n ≠ owner := by intro eq; subst n; simp [absent] at hf
  have eq : f = g := Option.some.inj (by simpa [put, different, hf] using hg)
  subst g
  rfl

theorem erase_retirement (r : R) (owner : Name) : RetirementStable r (erase r owner) := by
  intro n f g hf hg
  have different : n ≠ owner := by intro eq; subst n; simp [erase] at hg
  have eq : f = g := Option.some.inj (by simpa [erase, different, hf] using hg)
  subst g
  rfl

theorem mark_retirement (r : R) (owner : Name) (phase) : RetirementStable r (mark r owner phase) :=
  modify_retirement r owner (fun f => { f with phase := phase }) (fun _ => rfl)

theorem write_retirement (r : R) (owner : Name) (key : Key) (value : Option Value) :
    RetirementStable r (write r owner key value) :=
  modify_retirement r owner
    (fun f => { f with table := fun k => if k = key then value else f.table k }) (fun _ => rfl)

theorem retirement_after_mark {r s : R} (stable : RetirementStable r s) (owner : Name) (phase) :
    RetirementStable r (mark s owner phase) := by
  intro n f g hf hg
  obtain ⟨middle, hm, _⟩ := WellFormed.modify_origins s owner (fun f => { f with phase := phase }) (fun _ => rfl) n g hg
  exact (stable n f middle hf hm).trans (mark_retirement s owner phase n middle g hm hg)

theorem land_retirement (program : Code → Instruction Name Key Value Code Error)
    {actor : Name} {code : Code} {r s : R} {inverse : Inverse Name Key Value} {next : Option Code}
    (land : Land program actor code r s inverse next) : RetirementStable r s := by
  cases land with
  | unit => intro n f g hf hg; cases Option.some.inj (hf.symm.trans hg); rfl
  | provide => exact modify_retirement _ _ _ (fun _ => rfl)
  | operate => exact modify_retirement _ _ _ (fun _ => rfl)
  | instantiate r actor code component child _ ready => exact put_retirement _ _ _ ready.1

/-- The only primitive inverse that writes a retirement flag. -/
def Retires (inverse : Inverse Name Key Value) (name : Name) : Prop :=
  match inverse with
  | .retire child => child = name
  | _ => False

theorem undo_retirement (r : R) (inverse : Inverse Name Key Value) (name : Name)
    (untouched : ¬ Retires inverse name) (f g : F)
    (before : r name = some f) (after : Stages.undo inverse r name = some g) :
    f.retired = g.retired := by
  cases inverse with
  | unit => cases Option.some.inj (before.symm.trans after); rfl
  | restrict owner key => exact write_retirement r owner key none name f g before after
  | operate owner key inv =>
    exact modify_retirement r owner
      (fun f => { f with table := fun k => if k = key then (f.table key).map inv else f.table k })
      (fun _ => rfl) name f g before after
  | retire child =>
    have different : name ≠ child := fun eq => untouched eq.symm
    have eq : f = g := Option.some.inj (by simpa [Stages.undo, Calculus.retire, Calculus.modify, different, before] using after)
    subst g
    rfl

theorem discharge_retirement (r : R) (acc : List (Inverse Name Key Value)) (name : Name)
    (untouched : ∀ i ∈ acc, ¬ Retires i name) (f g : F)
    (before : r name = some f) (after : discharge Stages.undo acc r name = some g) :
    f.retired = g.retired := by
  induction acc generalizing r f with
  | nil => cases Option.some.inj (before.symm.trans after); rfl
  | cons i rest ih =>
    obtain ⟨middle, hm, _⟩ := Frame.discharge_origins (Stages.undo i r) rest name g after
    exact (undo_retirement r i name (untouched i (by simp)) f middle before hm).trans
      (ih (Stages.undo i r) (fun inv member => untouched inv (by simp [member])) middle hm after)

theorem discharge_retirement_origin (r : R) (acc : List (Inverse Name Key Value)) (name : Name)
    (f g : F) (before : r name = some f) (after : discharge Stages.undo acc r name = some g)
    (changed : f.retired ≠ g.retired) : ∃ i ∈ acc, Retires i name := by
  apply Classical.byContradiction
  intro absent
  apply changed
  exact discharge_retirement r acc name (fun i member touched => absent ⟨i, member, touched⟩) f g before after

/-- Lemma59(5)'s only-O-Retire clause includes the O-Retire primitive executed by
an actual captured instantiation inverse. Other actors' iterations cannot set it. -/
theorem step_retirement_origin (program : Code → Instruction Name Key Value Code Error)
    {rule : Rule} {actor : Name} {r s : R} (step : Labeled.Step program rule actor r s)
    (name : Name) (f g : F) (before : r name = some f) (after : s name = some g)
    (changed : f.retired ≠ g.retired) :
    (rule = .retire ∧ actor = name) ∨
      (rule = .unload ∧ ∃ entry acc view, r actor = some entry ∧
        entry.phase = .unloading acc view ∧ ∃ i ∈ acc, Retires i name) := by
  cases step with
  | insert _ _ c p ready => exact False.elim (changed (put_retirement r actor _ ready.1 name f g before after))
  | retire _ _ _ =>
    by_cases same : actor = name
    · exact .inl ⟨rfl, same⟩
    · have eq : f = g := Option.some.inj (by simpa [Calculus.retire, Calculus.modify, Ne.symm same, before] using after)
      exact False.elim (changed (congrArg Fiber.retired eq))
  | remove _ _ _ => exact False.elim (changed (erase_retirement r actor name f g before after))
  | begin _ _ entry view present phase free target =>
    exact False.elim (changed (mark_retirement r actor _ name f g before after))
  | iter _ middle _ entry code acc view inv next present phase target land =>
    exact False.elim (changed (retirement_after_mark (land_retirement program land) actor _ name f g before after))
  | finish _ middle _ entry code acc view inv present phase target land =>
    exact False.elim (changed (retirement_after_mark (land_retirement program land) actor _ name f g before after))
  | divert _ middle _ entry code acc view tail present phase target alternative =>
    rcases alternative with ⟨rfl, _⟩ | ⟨inv, next, land, _⟩
    · exact False.elim (changed (mark_retirement middle actor _ name f g before after))
    · exact False.elim (changed (retirement_after_mark (land_retirement program land) actor _ name f g before after))
  | leave _ _ entry acc view present phase target =>
    exact False.elim (changed (mark_retirement r actor _ name f g before after))
  | unload _ _ entry acc view present phase free =>
    obtain ⟨middle, hm, _⟩ := WellFormed.modify_origins (discharge Stages.undo acc r) actor
      (fun f => { f with phase := .inactive }) (fun _ => rfl) name g after
    have same := mark_retirement (discharge Stages.undo acc r) actor .inactive name middle g hm after
    exact .inr ⟨rfl, entry, acc, view, present, phase,
      discharge_retirement_origin r acc name f middle before hm (fun eq => changed (eq.trans same))⟩

theorem other_view (program : Code → Instruction Name Key Value Code Error)
    {rule : Rule} {actor : Name} {r s : R} (step : Labeled.Step program rule actor r s)
    (name : Name) (different : name ≠ actor) : ControlFrame.viewAt s name = ControlFrame.viewAt r name := by
  have marked : ∀ (t : R) phase,
      ControlFrame.viewAt (mark t actor phase) name = ControlFrame.viewAt t name := by
    intro t phase
    simp [ControlFrame.viewAt, mark, Calculus.modify, different]
  cases step with
  | insert _ _ _ _ _ => simp [ControlFrame.viewAt, put, different]
  | retire _ _ _ => simp [ControlFrame.viewAt, Calculus.retire, Calculus.modify, different]
  | remove _ _ _ => simp [ControlFrame.viewAt, erase, different]
  | begin _ _ _ _ _ _ _ _ => exact marked _ _
  | iter _ middle _ entry code acc view inv next present phase target land =>
    rw [marked, ControlFrame.land_views program land]
  | finish _ middle _ entry code acc view inv present phase target land =>
    rw [marked, ControlFrame.land_views program land]
  | divert _ middle _ entry code acc view tail present phase target alternative =>
    rcases alternative with ⟨rfl, _⟩ | ⟨inv, next, land, _⟩
    · exact marked _ _
    · rw [marked, ControlFrame.land_views program land]
  | leave _ _ _ _ _ _ _ _ => exact marked _ _
  | unload _ _ _ acc _ _ _ _ => rw [marked, ControlFrame.discharge_views]

theorem view_change_actor (program : Code → Instruction Name Key Value Code Error)
    {rule : Rule} {actor : Name} {r s : R} (step : Labeled.Step program rule actor r s)
    (name : Name) (changed : ControlFrame.viewAt s name ≠ ControlFrame.viewAt r name) : name = actor := by
  by_cases same : name = actor
  · exact same
  · exact False.elim (changed (other_view program step name same))

/-- Exact rule and actor labels, not just existence of a transition with the
same endpoints. This is the opening direction of Lemma59(2,4). -/
theorem appears_label (program : Code → Instruction Name Key Value Code Error)
    {rule : Rule} {actor : Name} {r s : R} (step : Labeled.Step program rule actor r s)
    (name : Name) (before : ControlFrame.viewAt r name = none)
    (after : ControlFrame.viewAt s name ≠ none) : rule = .begin ∧ actor = name := by
  have same : name = actor := view_change_actor program step name (fun eq => after (eq.trans before))
  subst name
  refine ⟨?_, rfl⟩
  cases step with
  | insert _ _ c p ready => simp [ControlFrame.viewAt, put, fresh, Phase.committed] at after
  | retire _ _ _ =>
    have equal := congrFun (ControlFrame.modify_views r actor (fun f => { f with retired := true }) (fun _ => rfl)) actor
    exact False.elim (after (equal.trans before))
  | remove _ _ ready => simp [ControlFrame.viewAt, erase] at after
  | begin => rfl
  | iter _ middle _ entry code acc view inv next present phase target land =>
    simp [ControlFrame.viewAt, present, phase, Phase.committed] at before
  | finish _ middle _ entry code acc view inv present phase target land =>
    simp [ControlFrame.viewAt, present, phase, Phase.committed] at before
  | divert _ middle _ entry code acc view tail present phase target alternative =>
    simp [ControlFrame.viewAt, present, phase, Phase.committed] at before
  | leave _ _ entry acc view present phase target =>
    simp [ControlFrame.viewAt, present, phase, Phase.committed] at before
  | unload _ _ entry acc view present phase free =>
    simp [ControlFrame.viewAt, present, phase, Phase.committed] at before

/-- Exact closing rule and actor labels for Lemma59(2,4). -/
theorem disappears_label (program : Code → Instruction Name Key Value Code Error)
    {rule : Rule} {actor : Name} {r s : R} (step : Labeled.Step program rule actor r s)
    (name : Name) (before : ControlFrame.viewAt r name ≠ none)
    (after : ControlFrame.viewAt s name = none) : rule = .unload ∧ actor = name := by
  have same : name = actor := view_change_actor program step name (fun eq => before (eq.symm.trans after))
  subst name
  refine ⟨?_, rfl⟩
  cases step with
  | insert _ _ c p ready => simp [ControlFrame.viewAt, ready.1] at before
  | retire _ _ _ =>
    have equal := congrFun (ControlFrame.modify_views r actor (fun f => { f with retired := true }) (fun _ => rfl)) actor
    exact False.elim (before (equal.symm.trans after))
  | remove _ _ ready =>
    have equal := congrFun (ControlFrame.remove_views r actor ready) actor
    exact False.elim (before (equal.symm.trans after))
  | begin _ _ entry view present phase free target =>
    simp [ControlFrame.viewAt, present, phase, Phase.committed] at before
  | iter _ middle _ entry code acc view inv next present phase target land =>
    obtain ⟨f, found, _⟩ := Ordering.land_existing_phases program land actor entry present
    simp [ControlFrame.viewAt, mark, Calculus.modify, found, Phase.committed] at after
  | finish _ middle _ entry code acc view inv present phase target land =>
    obtain ⟨f, found, _⟩ := Ordering.land_existing_phases program land actor entry present
    simp [ControlFrame.viewAt, mark, Calculus.modify, found, Phase.committed] at after
  | divert _ middle _ entry code acc view tail present phase target alternative =>
    rcases alternative with ⟨rfl, _⟩ | ⟨inv, next, land, _⟩
    · simp [ControlFrame.viewAt, mark, Calculus.modify, present, Phase.committed] at after
    · obtain ⟨f, found, _⟩ := Ordering.land_existing_phases program land actor entry present
      simp [ControlFrame.viewAt, mark, Calculus.modify, found, Phase.committed] at after
  | leave _ _ entry acc view present phase target =>
    simp [ControlFrame.viewAt, mark, Calculus.modify, present, Phase.committed] at after
  | unload => rfl

/-- A landed primitive can add a binding or change its value. Only accumulator
replay can remove an existing binding. -/
private theorem landing_preserves_binding (program : Code → Instruction Name Key Value Code Error)
    {actor : Name} {code : Code} {r s : R} {inverse next}
    (landing : Land program actor code r s inverse next)
    (owner : Name) (key : Key) (bound : StageRecovery.tableAt r owner key ≠ none) :
    StageRecovery.tableAt s owner key ≠ none := by
  have written (writer : Name) (writtenKey : Key) (value : Value) :
      StageRecovery.tableAt (write r writer writtenKey (some value)) owner key ≠ none := by
    by_cases same : owner = writer
    · subst writer
      cases present : r owner with
      | none => simp [StageRecovery.tableAt, present] at bound
      | some fiber =>
        by_cases atKey : key = writtenKey
        · simp [StageRecovery.tableAt, write, Calculus.modify, present, atKey]
        · simpa [StageRecovery.tableAt, write, Calculus.modify, present, atKey] using bound
    · simpa [StageRecovery.tableAt, write, Calculus.modify, same] using bound
  cases landing with
  | unit => exact bound
  | provide _ _ _ _ k value => exact written actor k value
  | operate _ _ _ k _ writer _ value => exact written writer k value
  | instantiate _ _ _ component child _ ready =>
    exact (Edit.preserves_tables (.insert child component (some actor)) r ready.1 owner key) ▸ bound

end Cordis.RuleEvaluation
