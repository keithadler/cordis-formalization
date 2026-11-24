import Cordis.Results.Support

/-! The well-foundedness argument in Lemma 75 when every prefix has empty
coeffect tables. The typed provision interpretation supplies this invariant. -/
namespace Cordis.Results
open Calculus Stages
universe u
variable {Name Key Value Code Error : Type u} [DecidableEq Name] [DecidableEq Key]
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
local notation "Program" => Code → Instruction Name Key Value Code Error

def EmptyTables (state : R) : Prop :=
  ∀ name key, StageRecovery.tableAt state name key = none

omit [DecidableEq Name] [DecidableEq Key] in
private theorem empty_fiber {state : R} (empty : EmptyTables state)
    {name : Name} {fiber : F} (found : state name = some fiber) (key : Key) :
    fiber.table key = none := by
  simpa only [StageRecovery.tableAt, found] using empty name key

omit [DecidableEq Name] [DecidableEq Key] in
private theorem no_requirements_of_committed {state : R} (empty : EmptyTables state)
    (supported : Ordering.Supported state) {actor : Name} {fiber : F} {view : View Name Key}
    (found : state actor = some fiber) (committed : fiber.phase.committed = some view) :
    ∀ key, fiber.component.requires key = false := by
  intro key
  cases h : fiber.component.requires key with
  | false => rfl
  | true =>
    obtain ⟨_, provider, present, _, bound⟩ :=
      supported actor (view key) key ⟨fiber, view, found, h, committed, rfl⟩
    exact False.elim (bound (empty_fiber empty present key))

private def ParentsWithoutRequirements (state : R) : Prop :=
  ∀ child entry parent fiber, state child = some entry → entry.parent = some parent →
    state parent = some fiber → ∀ key, fiber.component.requires key = false

private theorem new_child_actor {program : Program} {before after : R} {actor : Name}
    {code : Code} {inverse next} {phase : Phase Name Key Code (Inverse Name Key Value)}
    (land : Land program actor code before after inverse next)
    {child : Name} {entry : F} (missing : before child = none)
    (found : mark after actor phase child = some entry) (different : child ≠ actor) :
    entry.parent = some actor := by
  have row : after child = some entry := by
    simpa [mark, Calculus.modify, different] using found
  obtain ⟨component, _, _, rfl⟩ :=
    Transposition.land_new_name program land child missing (by rw [row]; simp)
  have equal : fresh component (some actor) = entry := Option.some.inj ((put_self _ _ _).symm.trans row)
  rw [← equal]
  rfl

private theorem new_child_committed {program : Program} {before after : R}
    (step : Orchestration.Step program before after) {child parent : Name} {entry : F}
    (missing : before child = none) (found : after child = some entry)
    (parentOf : entry.parent = some parent) :
    ∃ fiber view, before parent = some fiber ∧ fiber.phase.committed = some view := by
  have fromLanding {middle : R} {actor : Name} {code : Code} {inverse next}
      {result : Phase Name Key Code (Inverse Name Key Value)} {old : F} {view : View Name Key}
      (land : Land program actor code before middle inverse next)
      (present : before actor = some old) (committed : old.phase.committed = some view)
      (row : mark middle actor result child = some entry) :
      ∃ fiber view, before parent = some fiber ∧ fiber.phase.committed = some view := by
    have different : child ≠ actor := by
      intro same
      rw [same, present] at missing
      cases missing
    have actorParent := new_child_actor land missing row different
    have same := Option.some.inj (parentOf.symm.trans actorParent)
    exact ⟨old, view, by simpa only [same] using present, committed⟩
  cases step with
  | insert name component ready =>
    by_cases same : child = name
    · subst child
      have equal := Option.some.inj ((put_self before name (fresh component none)).symm.trans found)
      subst entry
      cases parentOf
    · simp [put, same, missing] at found
  | retire actor _ => simp [Calculus.retire, Calculus.modify, missing] at found
  | remove actor _ => simp [erase, missing] at found
  | begin actor fiber view present inactive free target =>
    simp [mark, Calculus.modify, missing] at found
  | iter middle actor fiber code acc view inverse next present phase target land =>
    exact fromLanding (view := view) land present (by simp [phase, Phase.committed]) found
  | finish middle actor fiber code acc view inverse present phase target land =>
    exact fromLanding (view := view) land present (by simp [phase, Phase.committed]) found
  | divert middle actor fiber code acc view tail present phase target alternatives =>
    rcases alternatives with ⟨rfl, _⟩ | ⟨_, _, land, _⟩
    · simp [mark, Calculus.modify, missing] at found
    · exact fromLanding (view := view) land present (by simp [phase, Phase.committed]) found
  | leave actor fiber acc view present phase target =>
    simp [mark, Calculus.modify, missing] at found
  | unload actor fiber acc view present phase free =>
    obtain ⟨middle, middleAt, _⟩ :=
      WellFormed.modify_origins (discharge Stages.undo acc before) actor
        (fun f => {f with phase := .inactive}) (fun _ => rfl) child entry found
    obtain ⟨old, oldAt, _⟩ := Frame.discharge_origins before acc child middle middleAt
    rw [missing] at oldAt
    cases oldAt

private theorem parent_requirements_step {program : Program} {before after : R}
    (step : Orchestration.Step program before after) (tree : Safety.Tree before)
    (supported : Ordering.Supported before) (empty : EmptyTables before)
    (old : ParentsWithoutRequirements before) : ParentsWithoutRequirements after := by
  intro child entry parent fiber found parentOf present key
  have stable := Frame.step_stable program step.toCalculus
  cases initial : before child with
  | none =>
    obtain ⟨owner, view, ownerAt, committed⟩ := new_child_committed step initial found parentOf
    rw [← (stable parent owner fiber ownerAt present).1]
    exact no_requirements_of_committed empty supported ownerAt committed key
  | some original =>
    have parentBefore : original.parent = some parent :=
      (stable child original entry initial found).2.1.trans parentOf
    have existed := tree.1 child original parent initial parentBefore
    cases ownerAt : before parent with
    | none => contradiction
    | some owner =>
      rw [← (stable parent owner fiber ownerAt present).1]
      exact old child original parent owner initial parentBefore ownerAt key

omit [DecidableEq Name] [DecidableEq Key] in
private theorem support_wellFounded_of_parents {state : R}
    (tree : Safety.Tree state) (parentRequires : ParentsWithoutRequirements state)
    (acyclic : WellFounded (fun provider consumer => Progress.Depends state consumer provider)) :
    WellFounded (SupportRelation state) := by
  obtain ⟨_, rank, ranked⟩ := tree
  have parentAccessible (name : Name) :
      (∃ child entry, state child = some entry ∧ entry.parent = some name) →
      Acc (SupportRelation state) name := by
    apply (measure rank).wf.induction name
    intro name useRank ⟨child, entry, found, parentOf⟩
    refine .intro name ?_
    intro predecessor edge
    rcases edge with ⟨consumer, supplier, key, consumerAt, _, required, _⟩ |
      ⟨fiber, row, prior⟩
    · rw [parentRequires child entry name consumer found parentOf consumerAt key] at required
      cases required
    · exact useRank predecessor (ranked name fiber predecessor row prior) ⟨name, fiber, row, prior⟩
  refine ⟨fun name => acyclic.induction name ?_⟩
  intro name ih
  refine .intro name (fun predecessor edge => ?_)
  rcases edge with dependency | ⟨entry, row, parentOf⟩
  · exact ih predecessor dependency
  · exact parentAccessible predecessor ⟨name, entry, row, parentOf⟩

private theorem parents_without_requirements {program : Program} {last : Nat}
    (trace : PaperLifecycleClaims.Trace program last) (roots : PaperLifecycleClaims.RootInsertions trace)
    (empty : ∀ index, index ≤ last → EmptyTables (trace.state index))
    (index : Nat) (bound : index ≤ last) :
    ParentsWithoutRequirements (trace.state index) := by
  induction index with
  | zero =>
    rw [trace.start]
    intro _ _ _ _ absent
    cases absent
  | succ index ih =>
    have prefixBound : index ≤ last := Nat.le_of_succ_le bound
    have initialRun := rootTrace trace roots index prefixBound
    have origin := initialRun.reachable_invariants
    -- Use the exact final root-only transition from the indexed trace.
    have rootOnly := rootRule program (trace.step index bound) (roots index bound)
    exact parent_requirements_step rootOnly origin.1 origin.2.2.1
      (empty index prefixBound) (ih prefixBound)

/-- If no prefix of a root-only trace introduces a table binding, the full
relation of Equation (61) is well founded and Equation (62) has one solution. -/
theorem lemma75_of_empty_tables {program : Program} {last : Nat}
    (trace : PaperLifecycleClaims.Trace program last)
    (roots : PaperLifecycleClaims.RootInsertions trace)
    (empty : ∀ index, index ≤ last → EmptyTables (trace.state index))
    (acyclic : FiniteOrder.Acyclic (PaperLifecycleClaims.precedence (trace.state last))) :
    WellFounded (PaperLifecycleClaims.supportEdge (trace.state last)) ∧
      ∃ support, SupportAtQuiescence.Solution (trace.state last) support ∧
        ∀ other, SupportAtQuiescence.Solution (trace.state last) other → other = support := by
  let state := trace.state last
  have run := rootTrace trace roots last (Nat.le_refl last)
  have parents := parents_without_requirements trace roots empty last (Nat.le_refl last)
  obtain ⟨names, covers⟩ := SupportUniqueness.reachable_finite program run
  have providers : WellFounded (fun provider consumer => Progress.Depends state consumer provider) := by
    refine FiniteOrder.wellFounded_of_finite_acyclic _ names ?_
      (FiniteActionBudget.acyclic_flip _ (depends_acyclic state acyclic))
    rintro provider consumer ⟨_, fiber, _, _, found, _⟩
    exact covers provider fiber found
  have order := support_wellFounded_of_parents run.reachable_invariants.1 parents providers
  refine ⟨Subrelation.wf ?_ order, lemma75_unique_support_of_wellFounded state order⟩
  intro predecessor name edge
  obtain ⟨_, _, dep | parent⟩ := edge
  · obtain ⟨key, ⟨provider, first, provided⟩, ⟨consumer, second, required⟩⟩ := dep
    exact .inl ⟨consumer, provider, key, second, first, required, provided⟩
  · cases row : state name with
    | none => simp [state, row] at parent
    | some fiber =>
      exact .inr ⟨fiber, row, by simpa only [state, row, Option.bind_some] using parent⟩

private theorem empty_undo {state : R} (empty : EmptyTables state) (token : Inverse Name Key Value) :
    EmptyTables (Stages.undo token state) := by
  intro name key
  cases token with
  | unit => exact empty name key
  | retire actor =>
    change StageRecovery.tableAt (Calculus.retire state actor) name key = none
    rw [StageRecovery.tableAt_retire]
    exact empty name key
  | restrict actor k =>
    rw [StageRecovery.tableAt_restrict]
    simp [empty name key]
  | operate actor k inverse =>
    rw [StageRecovery.tableAt_operate]
    simp [empty name key, empty actor k]

theorem empty_discharge {state : R} (empty : EmptyTables state)
    (tokens : List (Inverse Name Key Value)) : EmptyTables (discharge Stages.undo tokens state) := by
  induction tokens generalizing state with
  | nil => exact empty
  | cons token tail ih => exact ih (empty_undo empty token)

end Cordis.Results
