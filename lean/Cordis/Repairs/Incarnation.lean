import Cordis.IndexedTrace
import Cordis.Frame

/-!
An incarnation of a fiber is the uninterrupted presence of its name from
its birth. Its birth index is derived from the registry history. A captured
child retirement targets that incarnation and becomes a no-op after it
has been removed, including when the name has since been reissued.
-/
namespace Cordis.Repairs.Incarnation
open Calculus Stages
universe u
variable {Name Key Value Code Error : Type u}
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error

def birthAt (states : Nat → R) (name : Name) : Nat → Option Nat
  | 0 => (states 0 name).map (fun _ => 0)
  | time + 1 =>
    (states (time + 1) name).map (fun _ => (birthAt states name time).getD (time + 1))

structure Residency (states : Nat → R) (name : Name) (birth time : Nat) : Prop where
  ordered : birth ≤ time
  present : ∀ point, birth ≤ point → point ≤ time → states point name ≠ none
  boundary : birth = 0 ∨ states (birth - 1) name = none

variable {states : Nat → Registry Name Key Value Code (Inverse Name Key Value) Error} {name : Name} {birth time : Nat}

theorem birthAt_none : birthAt states name time = none ↔ states time name = none := by
  cases time with
  | zero => cases found : states 0 name <;> simp [birthAt, found]
  | succ time => cases found : states (time + 1) name <;> simp [birthAt, found]

theorem birth_stays (states : Nat → R) (name : Name) (time : Nat)
    (before : states time name ≠ none) (after : states (time + 1) name ≠ none) :
    birthAt states name (time + 1) = birthAt states name time := by
  cases present : states (time + 1) name with
  | none => exact False.elim (after present)
  | some row =>
    cases born : birthAt states name time with
    | none => exact False.elim (before (birthAt_none.mp born))
    | some birth => simp [birthAt, present, born]

theorem birthAt_of_created (fresh : states time name = none)
    (installed : states (time + 1) name ≠ none) :
    birthAt states name (time + 1) = some (time + 1) := by
  cases found : states (time + 1) name with
  | none => exact False.elim (installed found)
  | some row => simp [birthAt, found, birthAt_none.mpr fresh]

theorem resident_of_birthAt (found : birthAt states name time = some birth) :
    Residency states name birth time := by
  induction time generalizing birth with
  | zero =>
    cases row : states 0 name with
    | none => simp [birthAt, row] at found
    | some row =>
      have equal : 0 = birth := by simpa [birthAt, row] using found
      subst birth
      refine ⟨Nat.le_refl _, ?_, .inl rfl⟩
      intro point _ bounded absent
      have same : point = 0 := Nat.eq_zero_of_le_zero bounded
      rw [same, row] at absent
      cases absent
  | succ time ih =>
    cases current : states (time + 1) name with
    | none => simp [birthAt, current] at found
    | some row =>
      cases previous : birthAt states name time with
      | none =>
        have equal : time + 1 = birth := by simpa [birthAt, current, previous] using found
        subst birth
        refine ⟨Nat.le_refl _, ?_, .inr ?_⟩
        · intro point lower upper absent
          have same : point = time + 1 := Nat.le_antisymm upper lower
          rw [same, current] at absent
          cases absent
        · exact birthAt_none.mp previous
      | some earlier =>
        have equal : earlier = birth := by simpa [birthAt, current, previous] using found
        subst earlier
        have interval := ih previous
        have bound := interval.ordered
        refine ⟨by omega, ?_, interval.boundary⟩
        intro point lower upper absent
        by_cases same : point = time + 1
        · rw [same, current] at absent
          cases absent
        · exact interval.present point lower (by omega) absent

theorem Residency.unique {first second : Nat}
    (a : Residency states name first time) (b : Residency states name second time) : first = second := by
  have le_of (left right : Nat) (x : Residency states name left time) (y : Residency states name right time) :
      right ≤ left := by
    by_cases ordered : right ≤ left
    · exact ordered
    · have bounded := y.ordered
      have positive : right ≠ 0 := by omega
      have absent := y.boundary.resolve_left positive
      exact False.elim (x.present (right - 1) (by omega) (by omega) absent)
  exact Nat.le_antisymm (le_of second first b a) (le_of first second a b)

theorem birthAt_eq_some : birthAt states name time = some birth ↔ Residency states name birth time := by
  refine ⟨resident_of_birthAt, ?_⟩
  intro interval
  cases actual : birthAt states name time with
  | none => exact False.elim (interval.present time interval.ordered (Nat.le_refl _) (birthAt_none.mp actual))
  | some observed =>
    rw [(resident_of_birthAt actual).unique interval]

theorem Residency.prefix (interval : Residency states name birth time)
    (point : Nat) (later : birth ≤ point) (earlier : point ≤ time) :
    Residency states name birth point :=
  ⟨later, fun t lower upper => interval.present t lower (Nat.le_trans upper earlier), interval.boundary⟩

/-- A rule may modify a fiber within its lifetime without changing its
declaration or parent. The theorem uses every intervening native step. -/
theorem Residency.metadata_of_stable {last : Nat}
    {states : Nat → R} (stable : ∀ step, step < last → Frame.Stable (states step) (states (step + 1)))
    (bounded : time ≤ last)
    (interval : Residency states name birth time) {old current : F}
    (first : states birth name = some old) (found : states time name = some current) :
    old.component = current.component ∧ old.parent = current.parent := by
  induction time generalizing current with
  | zero =>
    have same : birth = 0 := Nat.eq_zero_of_le_zero interval.ordered
    rw [same, found] at first
    cases Option.some.inj first
    exact ⟨rfl, rfl⟩
  | succ time ih =>
    by_cases same : birth = time + 1
    · rw [same, found] at first
      cases Option.some.inj first
      exact ⟨rfl, rfl⟩
    · have order : birth ≤ time := by have := interval.ordered; omega
      cases previous : states time name with
      | none => exact False.elim (interval.present time order (by omega) previous)
      | some row =>
        have fromBirth := ih (Nat.le_trans (Nat.le_succ time) bounded) (interval.prefix time order (Nat.le_succ time)) previous
        have retained := stable time (by omega) name row current previous found
        exact ⟨fromBirth.1.trans retained.1, fromBirth.2.trans retained.2.1⟩

theorem Residency.metadata [DecidableEq Name] [DecidableEq Key]
    {program : Code → Instruction Name Key Value Code Error} {initial : R} {last : Nat}
    (trace : Indexed.Trace program initial last) (bounded : time ≤ last)
    (interval : Residency trace.state name birth time) {old current : F}
    (first : trace.state birth name = some old) (found : trace.state time name = some current) :
    old.component = current.component ∧ old.parent = current.parent :=
  interval.metadata_of_stable (fun step bound => Frame.step_stable program (trace.step step bound).toCalculus)
    bounded first found

variable [DecidableEq Name]

def retireCaptured (states : Nat → R) (name : Name) (birth time : Nat) : R :=
  if birthAt states name time = some birth then Calculus.retire (states time) name else states time

theorem retireCaptured_present [DecidableEq Key] (interval : Residency states name birth time) :
    retireCaptured states name birth time = Stages.undo (.retire name) (states time) := by
  simp [retireCaptured, birthAt_eq_some.mpr interval, Stages.undo]

theorem retireCaptured_absent (absent : states time name = none) :
    retireCaptured states name birth time = states time := by
  simp [retireCaptured, (birthAt_none (states := states) (name := name) (time := time)).mpr absent]

/-- Any intervening removal makes the original inverse inert, regardless of
the replacement's component, parent, or phase. -/
theorem retireCaptured_after_removal {gap : Nat} (afterBirth : birth ≤ gap) (byReplay : gap ≤ time)
    (removed : states gap name = none) :
    retireCaptured states name birth time = states time := by
  have stale : birthAt states name time ≠ some birth := fun same =>
    (resident_of_birthAt same).present gap afterBirth byReplay removed
  simp [retireCaptured, stale]

end Cordis.Repairs.Incarnation
