import Cordis.Repairs.EpisodeReleaseBarrier
import Cordis.Repairs.GuardedLandingMatching
import Cordis.Repairs.PairwiseAllocation

/-! Two nonentangled roots, both ready to perform the same allocation. The
selected continuation is constant, and each root has its own fresh draw.
Either root's child reserves the key and disables the other allocation. -/
namespace Cordis.Repairs.PairwiseAllocationExample
open Calculus Stages
open EpisodeReleaseBarrier (Code R F program parent child view empty)
open PairwiseAllocation

def insertedLeft : R := put empty 0 (fresh parent none)
def insertedBoth : R := put insertedLeft 1 (fresh parent none)
def leftReady : R := mark insertedBoth 0 (.reloading .first [] view)
def ready : R := mark leftReady 1 (.reloading .first [] view)

private theorem target {state : R} {actor : Nat} {row : F}
    (found : state actor = some row) (live : row.retired = false) (component : row.component = parent) :
    Target state actor view := by
  simp only [Target, found, component]
  exact ⟨live, fun _ required => Bool.noConfusion required⟩

theorem reachable : Orchestration.Run program empty ready := by
  have addLeft : Orchestration.Step program empty insertedLeft :=
    .insert empty 0 parent ⟨rfl, by simp, fun _ _ => trivial⟩
  have addRight : Orchestration.Step program insertedLeft insertedBoth := by
    apply Orchestration.Step.insert
    exact ⟨rfl, by simp, fun other key => by
      by_cases atLeft : other = 0 <;> simp [insertedLeft, put, atLeft, empty, fresh, parent]⟩
  have beginLeft : Orchestration.Step program insertedBoth leftReady :=
    .begin insertedBoth 0 (fresh parent none) view rfl rfl Option.noConfusion (target rfl rfl rfl)
  have beginRight : Orchestration.Step program leftReady ready :=
    .begin leftReady 1 (fresh parent none) view rfl rfl Option.noConfusion (target rfl rfl rfl)
  exact .step (.step (.step (.step (.refl _) addLeft) addRight) beginLeft) beginRight

theorem separated : Transposition.Separated parent parent := by
  exact ⟨fun _ provides => Bool.noConfusion provides, fun _ _ => rfl, fun _ _ => rfl⟩

theorem draw_insensitive : GuardedLandingMatching.ChildContinuations program := by
  intro code component action left right
  cases code <;> rfl

private theorem allocation_ready {newborn actor : Nat} (notLeft : newborn ≠ 0) (notRight : newborn ≠ 1)
    (present : ready actor ≠ none) : Insertable ready newborn child (some actor) := by
  refine ⟨by simp [ready, leftReady, insertedBoth, insertedLeft, empty, mark, Calculus.modify, put,
    notLeft, notRight], ?_, ?_⟩
  · intro name isActor
    cases isActor
    exact present
  · intro owner key
    by_cases atLeft : owner = 0
    · subst owner
      change true = true → ¬ false = true
      simp
    by_cases atRight : owner = 1
    · subst owner
      change true = true → ¬ false = true
      simp
    simp [ready, leftReady, insertedBoth, insertedLeft, empty, mark, Calculus.modify, put, atLeft, atRight]

private theorem leftAlloc : Insertable ready 2 child (some 0) :=
  allocation_ready (by decide) (by decide) (by change some _ ≠ none; exact Option.noConfusion)

private theorem rightAlloc : Insertable ready 3 child (some 1) :=
  allocation_ready (by decide) (by decide) (by change some _ ≠ none; exact Option.noConfusion)

def landLeft : R := put ready 2 (fresh child (some 0))
def landRight : R := put ready 3 (fresh child (some 1))
def iterLeft : R := mark landLeft 0 (.reloading .second [.retire 2] view)
def iterRight : R := mark landRight 1 (.reloading .second [.retire 3] view)

theorem left_landing : Land program 0 .first ready landLeft (.retire 2) (some .second) :=
  .instantiate ready 0 .first child 2 rfl leftAlloc

theorem right_landing : Land program 1 .first ready landRight (.retire 3) (some .second) :=
  .instantiate ready 1 .first child 3 rfl rightAlloc

theorem left_iteration : Orchestration.Step program ready iterLeft :=
  .iter ready landLeft 0 { (fresh parent none : F) with phase := .reloading .first [] view }
    .first [] view (.retire 2) .second rfl rfl (target rfl rfl rfl) left_landing

theorem right_iteration : Orchestration.Step program ready iterRight :=
  .iter ready landRight 1 { (fresh parent none : F) with phase := .reloading .first [] view }
    .first [] view (.retire 3) .second rfl rfl (target rfl rfl rfl) right_landing

theorem left_preserves_tables (owner : Nat) (key : Unit) :
    StageRecovery.tableAt landLeft owner key = StageRecovery.tableAt ready owner key :=
  Transposition.fresh_put_tables ready 2 child (some 0) leftAlloc.1 owner key

theorem right_preserves_tables (owner : Nat) (key : Unit) :
    StageRecovery.tableAt landRight owner key = StageRecovery.tableAt ready owner key :=
  Transposition.fresh_put_tables ready 3 child (some 1) rightAlloc.1 owner key

private theorem no_landing_with_reservation {state : R} {actor blocker parentName : Nat}
    (reserved : state blocker = some (fresh child (some parentName))) :
    ¬ ∃ after inverse next, Land program actor .first state after inverse next := by
  rintro ⟨_, _, _, landed⟩
  cases landed with
  | unit _ _ _ action => contradiction
  | provide _ _ _ _ _ _ action _ _ _ => contradiction
  | operate _ _ _ _ _ _ _ _ _ _ action _ _ => contradiction
  | instantiate _ _ _ actual _ action allowed =>
    have same : child = actual := Stages.Action.instantiate.inj action
    subst actual
    have conflict := allowed.2.2 blocker ()
    rw [reserved] at conflict
    exact conflict rfl rfl

/-- The obstruction is independent of the second draw, even at the
primitive cut where the newly allocated row has changed no table. -/
theorem no_right_after_left : ¬ ∃ after inverse next, Land program 1 .first landLeft after inverse next :=
  no_landing_with_reservation (blocker := 2) (parentName := 0) rfl

theorem no_left_after_right : ¬ ∃ after inverse next, Land program 0 .first landRight after inverse next :=
  no_landing_with_reservation (blocker := 3) (parentName := 1) rfl

/-- The same obstruction holds after the corresponding actual L-Iter,
which stores the saved retirement and advances the first parent's code. -/
theorem no_right_after_left_iteration : ¬ ∃ after inverse next, Land program 1 .first iterLeft after inverse next :=
  no_landing_with_reservation (blocker := 2) (parentName := 0) rfl

theorem no_left_after_right_iteration : ¬ ∃ after inverse next, Land program 0 .first iterRight after inverse next :=
  no_landing_with_reservation (blocker := 3) (parentName := 1) rfl

noncomputable def leftForward (state : R) : Option R := by
  classical
  exact if Insertable state 2 child (some 0) then some (put state 2 (fresh child (some 0))) else none

theorem leftForward_native {state after : R} (applied : leftForward state = some after) :
    Land program 0 .first state after (.retire 2) (some .second) := by
  classical
  unfold leftForward at applied
  split at applied
  · rename_i enabled
    cases Option.some.inj applied
    exact .instantiate _ _ _ _ _ rfl enabled
  · contradiction

/-- Definition 42(2)'s yield comparison fails for a successful native
forward application if it omits the child reservation guard. -/
theorem unguarded_forward_changes_allocating_yield :
    ¬ PartialMapClosure.Preserves Eq (allocatingYield program 1 3 .first child) leftForward := by
  intro preserved
  have applied : leftForward ready = some landLeft := by
    simp [leftForward, leftAlloc, landLeft]
  have returned : allocatingYield program 1 3 .first child ready = some (.retire 3, some .second, child) :=
    allocatingYield_some_iff.mpr ⟨rfl, rfl, _, right_landing, rfl⟩
  have equal := preserved ready landLeft applied
  change allocatingYield program 1 3 .first child landLeft = allocatingYield program 1 3 .first child ready at equal
  rw [returned] at equal
  obtain ⟨_, _, after, landed, _⟩ := allocatingYield_some_iff.mp equal
  exact no_right_after_left ⟨after, _, _, landed⟩

end Cordis.Repairs.PairwiseAllocationExample
