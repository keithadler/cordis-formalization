import Cordis.Repairs.PairwiseRegistry

/-! The native control part of a mixed word. A birth tests its actual
reservation and records its stamp. A saved retirement tests the stamped
incarnation and otherwise leaves the registry alone. -/
namespace Cordis.Repairs.PairwiseControl
open TypedRegistry PairwiseSlots
open PaperEffectEquations (CoeffectOperations)
open PartialCoeffectLifting (PartialMap compose)
open PairwiseAllocation (DrawCompatible)

universe u
variable {Name Key Code : Type u} {V : Key → Type u}
variable [DecidableEq Name] [DecidableEq Key] {ops : CoeffectOperations V}
local notation "R" => Registry Name V Code
abbrev Stamped (Name : Type u) {Key : Type u} (V : Key → Type u) (Code : Type u) :=
  Registry Name V Code × (Name → Option Nat)
local notation "SR" => Stamped Name V Code

inductive Control (Name Key Code : Type u) where
  | birth (parent child : Name) (component : Calculus.Component Key Code) (stamp : Nat)
  | retire (child : Name) (stamp : Nat)

def addBirth (state : SR) (parent child : Name) (component : Calculus.Component Key Code) (stamp : Nat) : SR :=
  (put state.1 child (fresh component (some parent)), fun name => if name = child then some stamp else state.2 name)

def savedRetire (state : SR) (child : Name) (stamp : Nat) : SR :=
  if state.2 child = some stamp then (retire state.1 child, state.2) else state

/-- The actual allocation guard stays partial. A captured retirement is
defined even when its original incarnation is gone. -/
noncomputable def run (edit : Control Name Key Code) (state : SR) : Option SR := by
  classical
  exact match edit with
  | .birth parent child component stamp =>
    if Insertable state.1 child component (some parent) then some (addBirth state parent child component stamp) else none
  | .retire child stamp => some (savedRetire state child stamp)

/-- Adjacent births need their names, reservations and parents to coexist.
Across a captured retirement, the birth must not create that same captured
incarnation. The same raw name can be reused at a different stamp. -/
def Compatible : Control Name Key Code → Control Name Key Code → Prop
  | .birth lParent lChild lComponent _, .birth rParent rChild rComponent _ =>
    DrawCompatible lChild rChild lComponent rComponent ∧ lParent ≠ rChild ∧ rParent ≠ lChild
  | .birth _ newborn _ born, .retire child stamp | .retire child stamp, .birth _ newborn _ born =>
    newborn ≠ child ∨ born ≠ stamp
  | .retire .., .retire .. => True

omit [DecidableEq Name] [DecidableEq Key] in
theorem Compatible.symm {left right : Control Name Key Code} (pair : Compatible left right) : Compatible right left := by
  cases left <;> cases right
  · exact ⟨pair.1.symm, pair.2.2, pair.2.1⟩
  · exact pair
  · exact pair
  · exact True.intro

private theorem insertable_after_other_birth (ops : CoeffectOperations V) (state : SR)
    {parent otherParent child otherChild : Name} {component otherComponent : Calculus.Component Key Code}
    (stamp : Nat) (different : parent ≠ otherChild)
    (otherReady : Insertable state.1 otherChild otherComponent (some otherParent)) :
    Insertable (addBirth state otherParent otherChild otherComponent stamp).1 child component (some parent) ↔
      Insertable state.1 child component (some parent) ∧ DrawCompatible child otherChild component otherComponent := by
  by_cases present : state.1 parent = none
  · constructor
    · intro ready
      exact False.elim (ready.2.1 parent rfl (by simp [addBirth, put, different, present]))
    · intro ready
      exact False.elim (ready.1.2.1 parent rfl present)
  · have rawPresent : encodeRegistry ops state.1 parent ≠ none := (not_congr (encodeRegistry_none ops _ _)).mpr present
    have rawReady := (insertable_encode_iff ops _ _ _ _).mpr otherReady
    have same := PairwiseAllocation.insertable_after_birth_iff (child := child) (component := component) rawPresent rawReady
    rw [← TypedRegistry.encode_fresh ops, ← encode_put, insertable_encode_iff, insertable_encode_iff] at same
    exact same

private theorem addBirth_addBirth (ops : CoeffectOperations V) (state : SR)
    (lParent rParent lChild rChild : Name) (lComponent rComponent : Calculus.Component Key Code)
    (leftStamp rightStamp : Nat) (different : lChild ≠ rChild) :
    addBirth (addBirth state rParent rChild rComponent rightStamp) lParent lChild lComponent leftStamp =
      addBirth (addBirth state lParent lChild lComponent leftStamp) rParent rChild rComponent rightStamp := by
  apply Prod.ext
  · apply encodeRegistry_injective ops
    simp only [addBirth, encode_put]
    exact Transposition.put_put _ _ _ _ _ different
  · funext name
    by_cases left : name = lChild
    · subst name
      simp [addBirth, different]
    · by_cases right : name = rChild <;> simp [addBirth, left, right, Ne.symm different]

private theorem birth_birth_commutes (ops : CoeffectOperations V)
    (lParent rParent lChild rChild : Name) (lComponent rComponent : Calculus.Component Key Code)
    (leftStamp rightStamp : Nat) (compatible : DrawCompatible lChild rChild lComponent rComponent)
    (firstParent : lParent ≠ rChild) (secondParent : rParent ≠ lChild) :
    compose (run (.birth lParent lChild lComponent leftStamp)) (run (.birth rParent rChild rComponent rightStamp)) =
      (compose (run (.birth rParent rChild rComponent rightStamp)) (run (.birth lParent lChild lComponent leftStamp)) : PartialMap SR) := by
  classical
  funext state
  by_cases lReady : Insertable state.1 lChild lComponent (some lParent)
  · have afterLeft := insertable_after_other_birth ops state (child := rChild) (component := rComponent) leftStamp secondParent lReady
    by_cases rReady : Insertable state.1 rChild rComponent (some rParent)
    · have leftAfterRight := (insertable_after_other_birth ops state (child := lChild) (component := lComponent)
        rightStamp firstParent rReady).mpr ⟨lReady, compatible⟩
      have rightAfterLeft := afterLeft.mpr ⟨rReady, compatible.symm⟩
      simp only [compose, run, if_pos lReady, if_pos rReady, Option.bind_some, if_pos leftAfterRight, if_pos rightAfterLeft]
      exact congrArg some (addBirth_addBirth ops state _ _ _ _ _ _ _ _ compatible.1)
    · have blocked : ¬ Insertable (addBirth state lParent lChild lComponent leftStamp).1 rChild rComponent (some rParent) :=
        fun ready => rReady (afterLeft.mp ready).1
      simp [compose, run, lReady, rReady, blocked]
  · by_cases rReady : Insertable state.1 rChild rComponent (some rParent)
    · have afterRight := insertable_after_other_birth ops state (child := lChild) (component := lComponent)
        rightStamp firstParent rReady
      have blocked : ¬ Insertable (addBirth state rParent rChild rComponent rightStamp).1 lChild lComponent (some lParent) :=
        fun ready => lReady (afterRight.mp ready).1
      simp [compose, run, lReady, rReady, blocked]
    · simp [compose, run, lReady, rReady]

private theorem retire_preserves_guard (ops : CoeffectOperations V) (state : SR) (child newborn parent : Name)
    (stamp : Nat) (payload : Calculus.Component Key Code) :
    Insertable (savedRetire state child stamp).1 newborn payload (some parent) ↔
      Insertable state.1 newborn payload (some parent) := by
  by_cases fires : state.2 child = some stamp
  · have native := Transposition.retire_insertable (encodeRegistry ops state.1) child newborn payload (some parent)
    rw [← encode_retire, insertable_encode_iff, insertable_encode_iff] at native
    simpa only [savedRetire, if_pos fires] using native
  · simp [savedRetire, fires]

omit [DecidableEq Key] in
private theorem vacant_retire (state : R) (name : Name) (empty : state name = none) : retire state name = state := by
  funext query
  by_cases same : query = name <;> simp_all [retire, TypedRegistry.modify]

private theorem birth_retire_end (ops : CoeffectOperations V) (state : SR) {parent child captured : Name}
    {payload : Calculus.Component Key Code} {birthStamp captureStamp : Nat}
    (ready : Insertable state.1 child payload (some parent)) (compatible : child ≠ captured ∨ birthStamp ≠ captureStamp) :
    savedRetire (addBirth state parent child payload birthStamp) captured captureStamp =
      addBirth (savedRetire state captured captureStamp) parent child payload birthStamp := by
  by_cases same : child = captured
  · subst captured
    have different := compatible.resolve_left (fun no => no rfl)
    have unchanged : savedRetire state child captureStamp = state := by
      unfold savedRetire
      split
      · exact Prod.ext (vacant_retire state.1 child ready.1) rfl
      · rfl
    rw [unchanged]
    simp [savedRetire, addBirth, different]
  · have stamp : (addBirth state parent child payload birthStamp).2 captured = state.2 captured := by
      simp [addBirth, Ne.symm same]
    by_cases fires : state.2 captured = some captureStamp
    · simp only [savedRetire, stamp, if_pos fires]
      apply Prod.ext
      · apply encodeRegistry_injective ops
        simp only [addBirth, encode_put, encode_retire]
        exact (Transposition.put_retire _ _ _ _ same).symm
      · rfl
    · simp [savedRetire, stamp, fires]

private theorem birth_retire_commutes (ops : CoeffectOperations V) (parent child captured : Name)
    (payload : Calculus.Component Key Code) (birthStamp captureStamp : Nat)
    (compatible : child ≠ captured ∨ birthStamp ≠ captureStamp) :
    compose (run (.retire captured captureStamp)) (run (.birth parent child payload birthStamp)) =
      (compose (run (.birth parent child payload birthStamp)) (run (.retire captured captureStamp)) : PartialMap SR) := by
  classical
  funext state
  have guard := retire_preserves_guard ops state captured child parent captureStamp payload
  by_cases ready : Insertable state.1 child payload (some parent)
  · simp only [compose, run, if_pos ready, Option.bind_some, if_pos (guard.mpr ready)]
    exact congrArg some (birth_retire_end ops state ready compatible)
  · have blocked : ¬ Insertable (savedRetire state captured captureStamp).1 child payload (some parent) :=
      fun first => ready (guard.mp first)
    simp [compose, run, ready, blocked]

omit [DecidableEq Key] in
private theorem retire_retire_commutes (state : SR) (left right : Name) (a b : Nat) :
    savedRetire (savedRetire state right b) left a = savedRetire (savedRetire state left a) right b := by
  by_cases l : state.2 left = some a <;> by_cases r : state.2 right = some b
  · simp only [savedRetire, if_pos l, if_pos r]
    apply Prod.ext
    · funext name
      by_cases atLeft : name = left <;> by_cases atRight : name = right <;>
        simp_all [retire, TypedRegistry.modify, Option.map_map, Function.comp_def]
    · rfl
  · simp [savedRetire, l, r]
  · simp [savedRetire, l, r]
  · simp [savedRetire, l, r]

/-- Primitive control maps commute literally, with both domains and the
live birth indices retained. -/
theorem controls_commute (ops : CoeffectOperations V) {left right : Control Name Key Code}
    (allowed : Compatible left right) : compose (run left) (run right) =
      (compose (run right) (run left) : PartialMap SR) := by
  cases left with
  | birth parent child payload birthStamp =>
    cases right with
    | birth otherParent otherChild otherPayload otherStamp =>
      exact birth_birth_commutes ops parent otherParent child otherChild payload otherPayload birthStamp otherStamp
        allowed.1 allowed.2.1 allowed.2.2
    | retire captured stamp => exact (birth_retire_commutes ops parent child captured payload birthStamp stamp allowed).symm
  | retire captured stamp =>
    cases right with
    | birth parent child payload birthStamp => exact birth_retire_commutes ops parent child captured payload birthStamp stamp allowed
    | retire child otherStamp =>
      funext state
      exact congrArg some (retire_retire_commutes state captured child stamp otherStamp)

omit [DecidableEq Key] in
theorem successful_preserves_tables {edit : Control Name Key Code} {before after : SR}
    (called : run edit before = some after) : tablesOf after.1 = tablesOf before.1 := by
  classical
  cases edit with
  | birth parent child payload stamp =>
    simp only [run] at called
    split at called
    · rename_i ready
      cases Option.some.inj called
      exact tablesOf_birth before.1 child payload (some parent) ready.1
    · contradiction
  | retire child stamp =>
    have definition : after = savedRetire before child stamp := (Option.some.inj called).symm
    rw [definition]
    unfold savedRetire
    split
    · exact tablesOf_retire before.1 child
    · rfl

end Cordis.Repairs.PairwiseControl
