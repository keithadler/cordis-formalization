import Cordis.TableFrame

/-! Exact retained-owner provenance of captured ordinary inverses. Every
operation inverse names either its actor or the current committed provider of
that declared required key. The invariant is derived from actual location and
all nine rules; no lifetime or inverse-domain conclusion is a premise. -/
namespace Cordis.PartialReplayRouting
open Calculus Stages
universe u
variable {Name Key Value Code Error : Type u}
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
variable [DecidableEq Name] [DecidableEq Key]
set_option linter.unusedSectionVars false

def Scoped (actor : Name) (requires : Key → Bool) (committed : Option (View Name Key)) : Inverse Name Key Value → Prop
  | .restrict owner _ => owner = actor
  | .operate owner key _ => owner = actor ∨ ∃ view, committed = some view ∧ requires key = true ∧ view key = owner
  | _ => True

def ScopedAccumulators (r : R) : Prop :=
  ∀ n f, r n = some f → ∀ i ∈ f.phase.accumulator, Scoped n f.component.requires f.phase.committed i

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
      simpa [component, phase] using old actor entry before i (by simpa [phase] using member)
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
    (scope : ∀ f, r actor = some f → ∀ i ∈ phase.accumulator, Scoped actor f.component.requires phase.committed i)
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
    owner = actor ∨ ∃ view, f.phase.committed = some view ∧ f.component.requires key = true ∧ view key = owner := by
  exact (Stages.location_scope present located).imp And.left id

theorem land_scoped (program : Code → Instruction Name Key Value Code Error)
    {actor : Name} {code : Code} {r s : R} {i : Inverse Name Key Value} {next : Option Code}
    (land : Land program actor code r s i next) (old : ScopedAccumulators r) :
    ScopedAccumulators s ∧ ∀ f, r actor = some f → Scoped actor f.component.requires f.phase.committed i := by
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
    (scope : ∀ i ∈ phase.accumulator, Scoped actor f.component.requires phase.committed i)
    (old : ScopedAccumulators r) : ScopedAccumulators (mark r actor phase) := by
  apply mark_scoped r actor phase ?_ old
  intro entry found
  have eq := Option.some.inj (present.symm.trans found)
  simpa [eq] using scope

theorem landing_mark_scoped (program : Code → Instruction Name Key Value Code Error)
    {actor : Name} {code : Code} {r s : R} {i : Inverse Name Key Value} {next : Option Code}
    (land : Land program actor code r s i next) (f : F) (phase) (present : r actor = some f)
    (scope : ∀ inv ∈ phase.accumulator, Scoped actor f.component.requires phase.committed inv)
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
    · subst inv; simpa [phase, Phase.committed] using (land_scoped program land old).2 f present
    · simpa [phase, Phase.committed] using old n f present inv (by simpa [phase, Phase.accumulator] using prior)
  | finish s n f c a v i present phase _ land =>
    apply landing_mark_scoped program land f _ present ?_ old
    intro inv member
    rcases List.mem_cons.mp member with eq | prior
    · subst inv; simpa [phase, Phase.committed] using (land_scoped program land old).2 f present
    · simpa [phase, Phase.committed] using old n f present inv (by simpa [phase, Phase.accumulator] using prior)
  | divert s n f c a v tail present phase _ alternative =>
    rcases alternative with ⟨same, nil⟩ | ⟨i, next, land, single⟩
    · subst s tail
      apply mark_known_scoped r n f _ present ?_ old
      simpa [phase, Phase.accumulator, Phase.committed] using old n f present
    · subst tail
      apply landing_mark_scoped program land f _ present ?_ old
      intro inv member
      rcases List.mem_cons.mp member with eq | prior
      · subst inv; simpa [phase, Phase.committed] using (land_scoped program land old).2 f present
      · simpa [phase, Phase.committed] using old n f present inv (by simpa [phase, Phase.accumulator] using prior)
  | leave n f a v present phase _ =>
    apply mark_known_scoped r n f _ present ?_ old
    simpa [phase, Phase.accumulator, Phase.committed] using old n f present
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

theorem operation_owner (state : R) (routing : ScopedAccumulators state)
    (actor owner : Name) (key : Key) (inverse : Value → Value) (fiber : F)
    (present : state actor = some fiber) (member : .operate owner key inverse ∈ fiber.phase.accumulator) :
    owner = actor ∨ ∃ view, fiber.phase.committed = some view ∧ fiber.component.requires key = true ∧ view key = owner :=
  routing actor fiber present (.operate owner key inverse) member

theorem restriction_owner (state : R) (routing : ScopedAccumulators state)
    (actor owner : Name) (key : Key) (fiber : F)
    (present : state actor = some fiber) (member : .restrict owner key ∈ fiber.phase.accumulator) : owner = actor :=
  routing actor fiber present (.restrict owner key) member

end Cordis.PartialReplayRouting
