import Cordis.ControlFrame
import Cordis.Labeled

/-! Declaration-scoped captured inverses and the foreign-table frame of Lemma59.
The scope invariant is derived from actual landing and all nine rules. -/
namespace Cordis.TableFrame
open Calculus Stages
universe u
variable {Name Key Value Code Error : Type u}
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
variable [DecidableEq Name] [DecidableEq Key]
set_option linter.unusedSectionVars false

def Scoped (actor : Name) (requires : Key → Bool) : Inverse Name Key Value → Prop
  | .restrict owner _ => owner = actor
  | .operate owner key _ => owner = actor ∨ requires key = true
  | _ => True

def ScopedAccumulators (r : R) : Prop :=
  ∀ n f, r n = some f → ∀ i ∈ f.phase.accumulator, Scoped n f.component.requires i

theorem scoped_empty : ScopedAccumulators (fun _ => none : R) := by
  intro n f present
  contradiction

theorem modify_scoped (r : R) (actor : Name) (change : F → F)
    (component : ∀ f, (change f).component = f.component)
    (phase : ∀ f, (change f).phase = f.phase) (old : ScopedAccumulators r) :
    ScopedAccumulators (Calculus.modify r actor change) := by
  intro n f present i member
  by_cases eq : n = actor
  · subst n
    cases before : r actor with
    | none => simp [Calculus.modify, before] at present
    | some entry =>
      have same : change entry = f := Option.some.inj (by simpa [Calculus.modify, before] using present)
      subst f
      simpa [component] using old actor entry before i (by simpa [phase] using member)
  · exact old n f (by simpa [Calculus.modify, eq] using present) i member

theorem insert_scoped (r : R) (actor : Name) (component : Component Key Code) (parent : Option Name)
    (old : ScopedAccumulators r) : ScopedAccumulators (put r actor (fresh component parent)) := by
  intro n f present i member
  by_cases eq : n = actor
  · subst n
    have same : fresh component parent = f := Option.some.inj (by simpa [put] using present)
    simp [← same, fresh, Phase.accumulator] at member
  · exact old n f (by simpa [put, eq] using present) i member

theorem erase_scoped (r : R) (actor : Name) (old : ScopedAccumulators r) :
    ScopedAccumulators (erase r actor) := by
  intro n f present i member
  by_cases eq : n = actor
  · simp [erase, eq] at present
  · exact old n f (by simpa [erase, eq] using present) i member

theorem mark_scoped (r : R) (actor : Name) (phase)
    (scope : ∀ f, r actor = some f → ∀ i ∈ phase.accumulator, Scoped actor f.component.requires i)
    (old : ScopedAccumulators r) : ScopedAccumulators (mark r actor phase) := by
  intro n f present i member
  by_cases eq : n = actor
  · subst n
    cases before : r actor with
    | none => simp [mark, Calculus.modify, before] at present
    | some entry =>
      have same : { entry with phase := phase } = f :=
        Option.some.inj (by simpa [mark, Calculus.modify, before] using present)
      subst f
      exact scope entry before i member
  · exact old n f (by simpa [mark, Calculus.modify, eq] using present) i member

theorem location_scope (r : R) (actor owner : Name) (f : F) (key : Key) (value : Value)
    (present : r actor = some f) (located : location r actor key = some (owner, value)) :
    owner = actor ∨ f.component.requires key = true := by
  exact (Stages.location_scope present located).imp And.left (fun ⟨_, _, required, _⟩ => required)

theorem land_scoped (program : Code → Instruction Name Key Value Code Error)
    {actor : Name} {code : Code} {r s : R} {i : Inverse Name Key Value} {next : Option Code}
    (land : Land program actor code r s i next) (old : ScopedAccumulators r) :
    ScopedAccumulators s ∧ ∀ f, r actor = some f → Scoped actor f.component.requires i := by
  cases land with
  | unit => exact ⟨old, fun _ _ => trivial⟩
  | provide => exact ⟨modify_scoped _ _ _ (fun _ => rfl) (fun _ => rfl) old, fun _ _ => rfl⟩
  | operate r actor code key run owner before after inv result _ located _ =>
    exact ⟨modify_scoped _ _ _ (fun _ => rfl) (fun _ => rfl) old,
      fun f present => location_scope r actor owner f key before present located⟩
  | instantiate => exact ⟨insert_scoped _ _ _ _ old, fun _ _ => trivial⟩

theorem undo_scoped (r : R) (i : Inverse Name Key Value) (old : ScopedAccumulators r) :
    ScopedAccumulators (Stages.undo i r) := by
  cases i with
  | unit => exact old
  | restrict => exact modify_scoped _ _ _ (fun _ => rfl) (fun _ => rfl) old
  | operate => exact modify_scoped _ _ _ (fun _ => rfl) (fun _ => rfl) old
  | retire => exact modify_scoped _ _ _ (fun _ => rfl) (fun _ => rfl) old

theorem discharge_scoped (r : R) (a : List (Inverse Name Key Value)) (old : ScopedAccumulators r) :
    ScopedAccumulators (discharge Stages.undo a r) := by
  induction a generalizing r with
  | nil => exact old
  | cons i rest ih => exact ih _ (undo_scoped r i old)

theorem mark_known_scoped (r : R) (actor : Name) (f : F) (phase) (present : r actor = some f)
    (scope : ∀ i ∈ phase.accumulator, Scoped actor f.component.requires i)
    (old : ScopedAccumulators r) : ScopedAccumulators (mark r actor phase) := by
  apply mark_scoped r actor phase ?_ old
  intro entry found
  have eq := Option.some.inj (present.symm.trans found)
  simpa [eq] using scope

theorem landing_mark_scoped (program : Code → Instruction Name Key Value Code Error)
    {actor : Name} {code : Code} {r s : R} {i : Inverse Name Key Value} {next : Option Code}
    (land : Land program actor code r s i next) (f : F) (phase) (present : r actor = some f)
    (scope : ∀ inv ∈ phase.accumulator, Scoped actor f.component.requires inv)
    (old : ScopedAccumulators r) : ScopedAccumulators (mark s actor phase) := by
  obtain ⟨entry, found, component, _⟩ := Ordering.land_existing_control program land actor f present
  apply mark_known_scoped s actor entry phase found ?_ (land_scoped program land old).1
  simpa [component] using scope

theorem step_scoped (program : Code → Instruction Name Key Value Code Error)
    {r s : R} (step : Calculus.Step (Land program) Stages.undo r s) (old : ScopedAccumulators r) :
    ScopedAccumulators s := by
  cases step with
  | insert => exact insert_scoped _ _ _ _ old
  | retire => exact modify_scoped _ _ _ (fun _ => rfl) (fun _ => rfl) old
  | remove => exact erase_scoped _ _ old
  | begin n f v present _ _ _ =>
    exact mark_known_scoped r n f _ present (by simp [Phase.accumulator]) old
  | iter s n f c a v i next present phase _ land =>
    apply landing_mark_scoped program land f _ present ?_ old
    intro inv member
    rcases List.mem_cons.mp member with eq | prior
    · subst inv; exact (land_scoped program land old).2 f present
    · exact old n f present inv (by simpa [phase, Phase.accumulator] using prior)
  | finish s n f c a v i present phase _ land =>
    apply landing_mark_scoped program land f _ present ?_ old
    intro inv member
    rcases List.mem_cons.mp member with eq | prior
    · subst inv; exact (land_scoped program land old).2 f present
    · exact old n f present inv (by simpa [phase, Phase.accumulator] using prior)
  | divert s n f c a v tail present phase _ alternative =>
    rcases alternative with ⟨same, nil⟩ | ⟨i, next, land, single⟩
    · subst s tail
      apply mark_known_scoped r n f _ present ?_ old
      simpa [phase, Phase.accumulator] using old n f present
    · subst tail
      apply landing_mark_scoped program land f _ present ?_ old
      intro inv member
      rcases List.mem_cons.mp member with eq | prior
      · subst inv; exact (land_scoped program land old).2 f present
      · exact old n f present inv (by simpa [phase, Phase.accumulator] using prior)
  | leave n f a v present phase _ =>
    apply mark_known_scoped r n f _ present ?_ old
    simpa [phase, Phase.accumulator] using old n f present
  | unload n f a v present phase _ =>
    exact mark_scoped _ n _ (by simp [Phase.accumulator]) (discharge_scoped r a old)

theorem reachable_scoped (program : Code → Instruction Name Key Value Code Error)
    {r : R} (run : WellFormed.Run program (fun _ => none) r) : ScopedAccumulators r := by
  have preserves : ∀ {s t : R}, WellFormed.Run program s t → ScopedAccumulators s → ScopedAccumulators t := by
    intro s t steps
    induction steps with
    | refl => exact id
    | step _ step ih => exact fun h => step_scoped program step (ih h)
  exact preserves run scoped_empty

/-- Equal domains and equal values away from the acting fiber's requirements. -/
def Tables (requires : Key → Bool) (before after : Key → Option Value) : Prop :=
  ∀ k, (before k = none ↔ after k = none) ∧ (requires k = false → before k = after k)

def ForeignFrame (actor : Name) (requires : Key → Bool) (r s : R) : Prop :=
  ∀ n f g, r n = some f → s n = some g → n ≠ actor → Tables requires f.table g.table

theorem tables_refl (requires : Key → Bool) (table : Key → Option Value) : Tables requires table table :=
  fun _ => ⟨Iff.rfl, fun _ => rfl⟩

theorem tables_trans {requires : Key → Bool} {a b c : Key → Option Value}
    (first : Tables requires a b) (second : Tables requires b c) : Tables requires a c :=
  fun k => ⟨(first k).1.trans (second k).1, fun outside => ((first k).2 outside).trans ((second k).2 outside)⟩

theorem frame_refl (actor : Name) (requires : Key → Bool) (r : R) : ForeignFrame actor requires r r := by
  intro n f g hf hg _
  have eq := Option.some.inj (hf.symm.trans hg)
  subst g
  exact tables_refl _ _

theorem frame_trans {actor : Name} {requires : Key → Bool} {r s t : R}
    (first : ForeignFrame actor requires r s) (second : ForeignFrame actor requires s t)
    (origins : WellFormed.DeclarationOrigins s t) : ForeignFrame actor requires r t := by
  intro n f g hf hg different
  obtain ⟨middle, hm, _⟩ := origins n g hg
  exact tables_trans (first n f middle hf hm different) (second n middle g hm hg different)

theorem modify_frame (r : R) (actor owner : Name) (requires : Key → Bool) (change : F → F)
    (localFrame : ∀ f, r owner = some f → owner ≠ actor → Tables requires f.table (change f).table) :
    ForeignFrame actor requires r (Calculus.modify r owner change) := by
  intro n f g hf hg different
  by_cases same : n = owner
  · subst n
    have eq : change f = g := Option.some.inj (by simpa [Calculus.modify, hf] using hg)
    subst g
    exact localFrame f hf different
  · have eq : f = g := Option.some.inj (by simpa [Calculus.modify, same, hf] using hg)
    subst g
    exact tables_refl _ _

theorem mark_frame (r : R) (actor owner : Name) (requires : Key → Bool) (phase) :
    ForeignFrame actor requires r (mark r owner phase) :=
  modify_frame r actor owner requires _ (fun f _ _ => tables_refl requires f.table)

theorem retire_frame (r : R) (actor owner : Name) (requires : Key → Bool) :
    ForeignFrame actor requires r (Calculus.retire r owner) :=
  modify_frame r actor owner requires _ (fun f _ _ => tables_refl requires f.table)

theorem put_frame (r : R) (actor inserted : Name) (requires : Key → Bool) (new : F)
    (absent : r inserted = none) : ForeignFrame actor requires r (put r inserted new) := by
  intro n f g hf hg _
  have different : n ≠ inserted := by intro eq; subst n; simp [absent] at hf
  have eq : f = g := Option.some.inj (by simpa [put, different, hf] using hg)
  subst g
  exact tables_refl _ _

theorem erase_frame (r : R) (actor erased : Name) (requires : Key → Bool) :
    ForeignFrame actor requires r (erase r erased) := by
  intro n f g hf hg _
  have different : n ≠ erased := by intro eq; subst n; simp [erase] at hg
  have eq : f = g := Option.some.inj (by simpa [erase, different, hf] using hg)
  subst g
  exact tables_refl _ _

theorem write_foreign_frame (r : R) (actor owner : Name) (requires : Key → Bool)
    (key : Key) (before after : Value) (f : F) (present : r owner = some f)
    (bound : f.table key = some before) (scope : owner = actor ∨ requires key = true) :
    ForeignFrame actor requires r (write r owner key (some after)) := by
  apply modify_frame r actor owner requires _
  intro entry found different k
  have eq := Option.some.inj (present.symm.trans found)
  subst entry
  have required : requires key = true := scope.resolve_left different
  by_cases same : k = key
  · subst k
    simp [bound, required]
  · simp [same]

theorem undo_frame (r : R) (actor : Name) (requires : Key → Bool) (i : Inverse Name Key Value)
    (scope : Scoped actor requires i) : ForeignFrame actor requires r (Stages.undo i r) := by
  cases i with
  | unit => exact frame_refl _ _ _
  | restrict owner key =>
    apply modify_frame r actor owner requires _
    intro f _ different
    exact False.elim (different scope)
  | operate owner key inverse =>
    apply modify_frame r actor owner requires _
    intro f _ different k
    have required : requires key = true := scope.resolve_left different
    by_cases same : k = key
    · subst k
      simp [required]
    · simp [same]
  | retire child => exact retire_frame _ _ _ _

theorem discharge_frame (r : R) (actor : Name) (requires : Key → Bool)
    (a : List (Inverse Name Key Value)) (scope : ∀ i ∈ a, Scoped actor requires i) :
    ForeignFrame actor requires r (discharge Stages.undo a r) := by
  induction a generalizing r with
  | nil => exact frame_refl _ _ _
  | cons i rest ih =>
    exact frame_trans (undo_frame r actor requires i (scope i (by simp)))
      (ih (Stages.undo i r) (fun inv member => scope inv (by simp [member])))
      (Frame.discharge_origins _ rest)

theorem land_frame (program : Code → Instruction Name Key Value Code Error)
    {actor : Name} {code : Code} {r s : R} {i : Inverse Name Key Value} {next : Option Code}
    (land : Land program actor code r s i next) (f : F) (present : r actor = some f) :
    ForeignFrame actor f.component.requires r s := by
  cases land with
  | unit => exact frame_refl _ _ _
  | provide =>
    apply modify_frame _ _ _ _ _
    intro _ _ different
    exact False.elim (different rfl)
  | operate r actor code key run owner before after inv result _ located _ =>
    obtain ⟨provider, found, bound⟩ := Safety.location_binding r actor owner key before located
    exact write_foreign_frame r actor owner f.component.requires key before after provider found bound
      (location_scope r actor owner f key before present located)
  | instantiate r actor code component child _ ready => exact put_frame r actor child _ _ ready.1

theorem frame_after_mark {actor : Name} {requires : Key → Bool} {r s : R}
    (frame : ForeignFrame actor requires r s) (owner : Name) (phase) :
    ForeignFrame actor requires r (mark s owner phase) :=
  frame_trans frame (mark_frame s actor owner requires phase)
    (WellFormed.modify_origins s owner _ (fun _ => rfl))

/-- Lemma59(1), with the actual acting name supplied by Definition58's label. -/
theorem step_frame (program : Code → Instruction Name Key Value Code Error)
    {rule : Labeled.Rule} {actor : Name} {r s : R}
    (step : Labeled.Step program rule actor r s) (old : ScopedAccumulators r)
    (f : F) (present : r actor = some f) : ForeignFrame actor f.component.requires r s := by
  cases step with
  | insert _ _ component parent ready =>
    simp [Insertable, present] at ready
  | retire _ _ alive => exact retire_frame _ _ _ _
  | remove _ _ ready => exact erase_frame _ _ _ _
  | begin _ _ entry view found inactive free target => exact mark_frame _ _ _ _ _
  | iter _ middle _ entry code a view inv next found phase target land =>
    exact frame_after_mark (land_frame program land f present) _ _
  | finish _ middle _ entry code a view inv found phase target land =>
    exact frame_after_mark (land_frame program land f present) _ _
  | divert _ middle _ entry code a view tail found phase target alternative =>
    rcases alternative with ⟨rfl, _⟩ | ⟨inv, next, land, _⟩
    · exact mark_frame _ _ _ _ _
    · exact frame_after_mark (land_frame program land f present) _ _
  | leave _ _ entry a view found phase target => exact mark_frame _ _ _ _ _
  | unload _ _ entry a view found phase free =>
    apply frame_after_mark
    apply discharge_frame
    intro inv member
    have eq : entry = f := Option.some.inj (found.symm.trans present)
    subst entry
    exact old actor f present inv (by simpa [phase, Phase.accumulator] using member)

/-- A changed foreign table has an existing binding at a declared required key;
the domain-preservation clause rules out manufacturing a new binding there. -/
theorem changed_key {requires : Key → Bool} {before after : Key → Option Value}
    (frame : Tables requires before after) (changed : before ≠ after) :
    ∃ key, requires key = true ∧ before key ≠ none ∧ before key ≠ after key := by
  apply Classical.byContradiction
  intro absent
  apply changed
  funext key
  by_cases equal : before key = after key
  · exact equal
  · have required : requires key = true := by
      cases flag : requires key
      · exact False.elim (equal ((frame key).2 flag))
      · rfl
    have bound : before key ≠ none := by
      intro empty
      exact equal (empty.trans ((frame key).1.mp empty).symm)
    exact False.elim (absent ⟨key, required, bound, equal⟩)

end Cordis.TableFrame
