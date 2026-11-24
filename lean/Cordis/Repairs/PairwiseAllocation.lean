import Cordis.Repairs.IncarnationReplay
import Cordis.TranspositionLandings
import Cordis.PartialMapClosure

/-! Reservation guards for the allocating case of Definition 65 and Lemma 66.
A newly inserted row has an empty table but can change the applicability of
another actor's primitive. Saved inverses do not change reservations. -/
namespace Cordis.Repairs.PairwiseAllocation
open Calculus Stages
open IncarnationReplay (Capture)
open PartialCoeffectLifting (PartialMap compose)
open PartialMapClosure (Generated Preserves)

universe u
variable {Name Key Value Code Error : Type u} [DecidableEq Name] [DecidableEq Key]
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
local notation "Program" => Code → Instruction Name Key Value Code Error

/-- Two chosen births may coexist exactly when they use distinct names and
reserve disjoint provision declarations. Dependencies and table values do not
enter this guard. -/
def DrawCompatible (left right : Name) (first second : Component Key Code) : Prop :=
  left ≠ right ∧ ∀ key, first.provides key = true → second.provides key = false

omit [DecidableEq Name] [DecidableEq Key] in
theorem DrawCompatible.symm {left right : Name} {first second : Component Key Code}
    (compatible : DrawCompatible left right first second) :
    DrawCompatible right left second first := by
  refine ⟨Ne.symm compatible.1, ?_⟩
  intro key secondProvides
  cases firstProvides : first.provides key
  · rfl
  · simp [compatible.2 key firstProvides] at secondProvides

omit [DecidableEq Key] in
theorem insertable_after_birth_iff {state : R} {actor otherActor child otherChild : Name}
    {component otherComponent : Component Key Code} (present : state actor ≠ none)
    (otherReady : Insertable state otherChild otherComponent (some otherActor)) :
    Insertable (put state otherChild (fresh otherComponent (some otherActor))) child component (some actor) ↔
      Insertable state child component (some actor) ∧ DrawCompatible child otherChild component otherComponent := by
  have actorDifferent : actor ≠ otherChild := by
    intro same
    exact present (same ▸ otherReady.1)
  constructor
  · intro ready
    have different : child ≠ otherChild := by
      intro same
      have absent := ready.1
      simp [put, same] at absent
    refine ⟨⟨?_, ?_, ?_⟩, different, ?_⟩
    · simpa [put, different] using ready.1
    · intro parent isActor
      cases isActor
      exact present
    · intro owner key
      by_cases same : owner = otherChild
      · subst owner
        simp [otherReady.1]
      · simpa [put, same] using ready.2.2 owner key

    · intro key provides
      have reserved := ready.2.2 otherChild key
      simp [put, fresh, provides] at reserved
      exact reserved
  · rintro ⟨ready, different, disjoint⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa [put, different] using ready.1
    · intro parent isActor
      cases isActor
      simpa [put, actorDifferent] using present
    · intro owner key
      by_cases same : owner = otherChild
      · subst owner
        simp only [put, fresh]
        intro provided
        simp [disjoint key provided]
      · simpa [put, same] using ready.2.2 owner key

omit [DecidableEq Key] in
/-- Allowing a redraw removes the collision with the selected name when
another vacant name exists. The reservation condition is independent of
which fresh name is chosen. -/
theorem exists_draw_after_birth_iff {state : R} {actor otherActor otherChild : Name}
    {component otherComponent : Component Key Code} (present : state actor ≠ none)
    (otherReady : Insertable state otherChild otherComponent (some otherActor)) :
    (∃ child, Insertable (put state otherChild (fresh otherComponent (some otherActor))) child component (some actor)) ↔
      (∃ child, Insertable state child component (some actor) ∧ child ≠ otherChild) ∧
        (∀ key, component.provides key = true → otherComponent.provides key = false) := by
  constructor
  · rintro ⟨child, ready⟩
    obtain ⟨before, distinct, disjoint⟩ := (insertable_after_birth_iff present otherReady).mp ready
    exact ⟨⟨child, before, distinct⟩, disjoint⟩
  · rintro ⟨⟨child, ready, distinct⟩, disjoint⟩
    exact ⟨child, (insertable_after_birth_iff present otherReady).mpr ⟨ready, distinct, disjoint⟩⟩

/-- The new reservation imposed by an actual foreign primitive result. -/
def AllowsDraw (child : Name) (component : Component Key Code)
    (action : Action Name Key Value Code Error) (token : Inverse Name Key Value) : Prop :=
  match action, token with
  | .instantiate otherComponent, .retire otherChild => DrawCompatible child otherChild component otherComponent
  | _, _ => True

/-- Exact availability of a fixed child draw after any successful native
primitive. Unit, provision, and operation preserve the old allocation guard.
A birth adds exactly the two checks on the actual new name and component. -/
theorem insertable_after_landing_iff {program : Program}
    {before after : R} {actor foreignActor child : Name} {component : Component Key Code}
    {code : Code} {token : Inverse Name Key Value} {next : Option Code}
    (present : before actor ≠ none) (land : Land program foreignActor code before after token next) :
    Insertable after child component (some actor) ↔
      Insertable before child component (some actor) ∧
        AllowsDraw child component (program code).action token := by
  cases land with
  | unit _ _ _ action => simp [action, AllowsDraw]
  | provide _ _ _ _ key value action _ _ _ => simp [action, AllowsDraw, Transposition.write_insertable]
  | operate _ _ _ key _ owner _ output _ _ action _ _ => simp [action, AllowsDraw, Transposition.write_insertable]
  | instantiate _ _ _ otherComponent otherChild action ready =>
    simpa only [action, AllowsDraw] using insertable_after_birth_iff present ready

/-- Both independently enabled allocating instructions can run in either
order exactly when their chosen births can coexist. The same draws give
literal endpoint agreement and preserve both actual captures and branches. -/
theorem allocating_diamond_iff {program : Program} {state : R}
    {left right leftChild rightChild : Name} {leftCode rightCode : Code}
    {leftComponent rightComponent : Component Key Code}
    (leftAction : (program leftCode).action = .instantiate leftComponent)
    (rightAction : (program rightCode).action = .instantiate rightComponent)
    (leftReady : Insertable state leftChild leftComponent (some left))
    (rightReady : Insertable state rightChild rightComponent (some right)) :
    let afterLeft := put state leftChild (fresh leftComponent (some left))
    let afterRight := put state rightChild (fresh rightComponent (some right))
    DrawCompatible leftChild rightChild leftComponent rightComponent ↔
      ∃ final, Land program right rightCode afterLeft final (.retire rightChild)
        ((program rightCode).next (.child rightChild)) ∧
        Land program left leftCode afterRight final (.retire leftChild)
          ((program leftCode).next (.child leftChild)) := by
  have leftGuard := insertable_after_birth_iff (leftReady.2.1 left rfl) rightReady
    (child := leftChild) (component := leftComponent)
  have rightGuard := insertable_after_birth_iff (rightReady.2.1 right rfl) leftReady
    (child := rightChild) (component := rightComponent)
  dsimp only
  constructor
  · intro compatible
    refine ⟨_, .instantiate _ _ _ _ _ rightAction (rightGuard.mpr ⟨rightReady, compatible.symm⟩), ?_⟩
    rw [Transposition.put_put _ rightChild leftChild _ _ (Ne.symm compatible.1)]
    exact .instantiate _ _ _ _ _ leftAction (leftGuard.mpr ⟨leftReady, compatible⟩)
  · rintro ⟨_, _, leftLands⟩
    cases leftLands with
    | instantiate _ _ _ actual _ action ready =>
      have same := Stages.Action.instantiate.inj (action.symm.trans leftAction)
      subst actual
      exact (leftGuard.mp ready).2

omit [DecidableEq Key] in
/-- A control or value edit preserving the component preserves the whole
allocation guard. Presence is preserved even at the edited coordinate. -/
private theorem modify_insertable_iff (state : R) (name child : Name) (change : F → F)
    (keepsComponent : ∀ row, (change row).component = row.component)
    (component : Component Key Code) (parent : Option Name) :
    Insertable (Calculus.modify state name change) child component parent ↔ Insertable state child component parent := by
  have presence (owner : Name) : Calculus.modify state name change owner = none ↔ state owner = none := by
    by_cases same : owner = name <;> simp [Calculus.modify, same]
  unfold Insertable
  apply and_congr (presence child)
  apply and_congr
  · apply forall_congr'; intro owner
    exact imp_congr_right (fun _ => not_congr (presence owner))
  · apply forall_congr'; intro owner
    apply forall_congr'; intro key
    by_cases same : owner = name
    · subst owner
      cases found : state name <;> simp [Calculus.modify, found, keepsComponent]
    · simp [Calculus.modify, same]

theorem insertable_after_undo_iff (state : R) (token : Inverse Name Key Value)
    (child : Name) (component : Component Key Code) (parent : Option Name) :
    Insertable (Stages.undo token state) child component parent ↔ Insertable state child component parent := by
  cases token with
  | unit => rfl
  | restrict owner key => exact Transposition.write_insertable state owner child key none component parent
  | operate owner key inverse =>
    exact modify_insertable_iff state owner child
      (fun row => { row with table := fun other =>
        if other = key then Option.map inverse (row.table key) else row.table other })
      (fun _ => rfl) component parent
  | retire name => exact Transposition.retire_insertable state name child component parent

theorem insertable_after_capture_iff (state : R) (live : Name → Option Nat) (capture : Capture Name Key Value)
    (child : Name) (component : Component Key Code) (parent : Option Name) :
    Insertable (capture.apply live state) child component parent ↔ Insertable state child component parent := by
  unfold Capture.apply
  split
  · split
    · exact Transposition.retire_insertable state _ child component parent
    · rfl
  · exact insertable_after_undo_iff state _ child component parent

/-- Successful foreign forward applications realize native landings and
pass the extra reservation check. Successful saved inverse applications are
already evaluated on their own admissible inputs. The guard proof below
works even if the inverse word is supplied without capture provenance. -/
def ForeignGenerator (program : Program) (actor child : Name) (component : Component Key Code)
    (map : PartialMap R) : Prop :=
  ∀ before after, map before = some after →
    (∃ foreignActor code token next, foreignActor ≠ actor ∧
      Land program foreignActor code before after token next ∧ AllowsDraw child component (program code).action token) ∨
    (∃ live, ∃ capture : Capture Name Key Value, after = capture.apply live before)

/-- The successful part of any generated foreign word preserves both the
acting row and definedness of the selected allocation. The condition on
each successful foreign birth is precisely the additional guard proved above. -/
theorem generated_preserves_allocation_guard {program : Program} {actor child : Name}
    {component : Component Key Code} {map : PartialMap R}
    (generated : Generated (ForeignGenerator program actor child component) map) :
    ∀ before after, map before = some after → before actor ≠ none →
      after actor ≠ none ∧
        (Insertable after child component (some actor) ↔ Insertable before child component (some actor)) := by
  induction generated with
  | identity =>
    intro before after applied present
    cases Option.some.inj applied
    exact ⟨present, Iff.rfl⟩
  | generator native =>
    intro before after applied present
    rcases native before after applied with ⟨other, code, token, next, different, landed, allowed⟩ |
      ⟨live, capture, rfl⟩
    · have kept : after actor ≠ none := by
        cases found : before actor with
        | none => exact False.elim (present found)
        | some row =>
          obtain ⟨entry, stillPresent, _, _⟩ := Ordering.land_existing_control program landed actor row found
          rw [stillPresent]
          exact Option.noConfusion
      exact ⟨kept, (insertable_after_landing_iff present landed).trans (and_iff_left allowed)⟩
    · exact ⟨fun absent => present ((capture.presence live before actor).mp absent),
        insertable_after_capture_iff before live capture child component (some actor)⟩
  | composition _ _ afterIH beforeIH =>
    intro before after applied present
    obtain ⟨middle, first, second⟩ := Option.bind_eq_some_iff.mp applied
    obtain ⟨middlePresent, firstGuard⟩ := beforeIH before middle first present
    obtain ⟨finalPresent, secondGuard⟩ := afterIH middle after second middlePresent
    exact ⟨finalPresent, secondGuard.trans firstGuard⟩

/-- The selected allocating yield includes the actual capture, continuation
and inserted component. Each admissible forward or inverse generator, and
thus their composition, preserves the yield while keeping its tables out of
the allocation guard. -/
noncomputable def allocatingYield (program : Program) (actor child : Name) (code : Code)
    (component : Component Key Code) (before : R) :
    Option (Inverse Name Key Value × Option Code × Component Key Code) := by
  classical
  exact if (program code).action = .instantiate component ∧ Insertable before child component (some actor)
    then some (.retire child, (program code).next (.child child), component) else none

theorem allocatingYield_some_iff {program : Program} {actor child : Name} {code : Code}
    {component : Component Key Code} {before : R} {token : Inverse Name Key Value}
    {next : Option Code} {payload : Component Key Code} :
    allocatingYield program actor child code component before = some (token, next, payload) ↔
      payload = component ∧ token = .retire child ∧ ∃ after,
        Land program actor code before after token next ∧ after = put before child (fresh component (some actor)) := by
  classical
  unfold allocatingYield
  split
  · rename_i ready
    constructor
    · intro returned
      cases Option.some.inj returned
      exact ⟨rfl, rfl, _, .instantiate _ _ _ _ _ ready.1 ready.2, rfl⟩
    · rintro ⟨rfl, rfl, _, landed, equation⟩
      cases landed with
      | instantiate _ _ _ actual _ action allowed =>
        have same := Stages.Action.instantiate.inj (action.symm.trans ready.1)
        subst actual
        rfl
  · rename_i unavailable
    constructor
    · intro impossible
      contradiction
    · rintro ⟨rfl, rfl, _, landed, equation⟩
      cases landed with
      | instantiate _ _ _ actual _ action allowed =>
        have sameRow := congrFun equation child
        have same : actual = payload := by simpa [put, fresh] using sameRow
        subst actual
        exact False.elim (unavailable ⟨action, allowed⟩)

theorem generated_preserves_allocating_yield {program : Program} {actor child : Name}
    {code : Code} {component : Component Key Code} {map : PartialMap R}
    (generated : Generated (ForeignGenerator program actor child component) map)
    (admitted : ∀ before after, map before = some after → before actor ≠ none) :
    Preserves Eq (allocatingYield program actor child code component) map := by
  intro before after applied
  have guards := (generated_preserves_allocation_guard generated before after applied (admitted before after applied)).2
  change allocatingYield program actor child code component after = allocatingYield program actor child code component before
  unfold allocatingYield
  rw [propext guards]

end Cordis.Repairs.PairwiseAllocation
