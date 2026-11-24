import Cordis.PartialReplayHistory
import Cordis.RuleEvaluation

/-! Projecting accumulator replay to the occupied binding it changes.
A failed partial callback and an absent slot have distinct outcomes. -/
namespace Cordis.PartialReplaySlots

open Calculus Stages StageRecovery
open PartialCoeffectLifting (PartialMap)
open PartialReplayHistory (run keepMissing eraseAfter)
universe u
variable {Name Key Value Code Error : Type u} [DecidableEq Name] [DecidableEq Key]
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "I" => Inverse Name Key Value

/-- An interpretation supplies the partial denotation of each saved value
callback. Its total representative is used only to compare defined results. -/
abbrev InverseMeaning (Key Value : Type u) := Key → (Value → Value) → PartialMap Value

def Agrees (denote : InverseMeaning Key Value) : Prop :=
  ∀ key inverse value output, denote key inverse value = some output → inverse value = output

def project (denote : InverseMeaning Key Value) (owner : Name) (key : Key) :
    I → PartialMap (Option Value)
  | .unit => some
  | .retire _ => some
  | .restrict src slot => if owner = src ∧ key = slot then fun _ => some none else some
  | .operate src slot inverse =>
    if owner = src ∧ key = slot then keepMissing (denote key inverse) else some

theorem project_atom (denote : InverseMeaning Key Value) (agrees : Agrees denote)
    (owner : Name) (key : Key) (inverse : I) (state : R) (output : Option Value)
    (replayed : project denote owner key inverse (tableAt state owner key) = some output) :
    tableAt (Stages.undo inverse state) owner key = output := by
  cases inverse with
  | unit => exact Option.some.inj replayed
  | retire child =>
    rw [Stages.undo, tableAt_retire]
    exact Option.some.inj replayed
  | restrict src slot =>
    rw [tableAt_restrict]
    by_cases same : owner = src ∧ key = slot
    · simpa [project, same] using replayed
    · simpa [project, same] using replayed
  | operate src slot inverse =>
    rw [tableAt_operate]
    by_cases same : owner = src ∧ key = slot
    · obtain ⟨rfl, rfl⟩ := same
      simp only [project, true_and, if_pos] at replayed ⊢
      cases present : tableAt state owner key with
      | none => simpa [keepMissing, present] using replayed
      | some value =>
        cases transformed : denote key inverse value with
        | none => simp [keepMissing, present, transformed] at replayed
        | some changed =>
          have described := agrees key inverse value changed transformed
          simp [keepMissing, present, transformed] at replayed
          simp [described, replayed]
    · simpa [project, same] using replayed

/-- Any successful partial projection gives the exact value in the ordinary
discharge. Success is kept as a premise of this correspondence so that the
ordinary total representation never licenses an undefined partial call. -/
theorem project_word (denote : InverseMeaning Key Value) (agrees : Agrees denote)
    (owner : Name) (key : Key) (word : List I) (state : R) (output : Option Value)
    (replayed : run (word.map (project denote owner key)) (tableAt state owner key) = some output) :
    tableAt (discharge Stages.undo word state) owner key = output := by
  induction word generalizing state with
  | nil => exact Option.some.inj replayed
  | cons inverse tail ih =>
    simp only [List.map_cons, PartialReplayHistory.run_cons] at replayed
    cases applied : project denote owner key inverse (tableAt state owner key) with
    | none => simp [applied] at replayed
    | some intermediate =>
      have represented := project_atom denote agrees owner key inverse state intermediate applied
      apply ih (Stages.undo inverse state)
      simpa only [represented, applied, Option.bind_some] using replayed

/-- The local word consists of every operation on the selected slot
before its first restriction, and whether that restriction occurs. -/
def slotWord (denote : InverseMeaning Key Value) (owner : Name) (key : Key) :
    List I → List (PartialMap Value) × Bool
  | [] => ([], false)
  | .operate src slot inverse :: tail =>
    let rest := slotWord denote owner key tail
    if owner = src ∧ key = slot then (denote key inverse :: rest.1, rest.2) else rest
  | .restrict src slot :: tail =>
    if owner = src ∧ key = slot then ([], true) else slotWord denote owner key tail
  | _ :: tail => slotWord denote owner key tail

/-- The operation captures at a slot, including any beyond the first
restriction. The latter are retained here for occurrence accounting. -/
def captures (denote : InverseMeaning Key Value) (owner : Name) (key : Key) (word : List I) :
    List (PartialMap Value) :=
  word.filterMap fun inverse => match inverse with
    | .operate src slot inverse => if owner = src ∧ key = slot then some (denote key inverse) else none
    | _ => none

theorem slotWord_captures (denote : InverseMeaning Key Value) (owner : Name) (key : Key) (word : List I) :
    List.Sublist (slotWord denote owner key word).1 (captures denote owner key word) := by
  induction word with
  | nil => exact .slnil
  | cons inverse tail earlier =>
    cases inverse with
    | unit => exact earlier
    | retire child => exact earlier
    | restrict src slot =>
      by_cases same : owner = src ∧ key = slot
      · simp [slotWord, same]
      · simpa only [slotWord, if_neg same, captures, List.filterMap_cons_none] using earlier
    | operate src slot inverse =>
      by_cases same : owner = src ∧ key = slot
      · simpa [captures, slotWord, same] using earlier.cons₂ (denote key inverse)
      · simpa [captures, slotWord, same] using earlier

theorem slotWord_erases_iff (denote : InverseMeaning Key Value) (owner : Name) (key : Key) (word : List I) :
    (slotWord denote owner key word).2 = true ↔ Inverse.restrict owner key ∈ word := by
  induction word with
  | nil => simp [slotWord]
  | cons inverse tail earlier =>
    cases inverse with
    | unit => simpa [slotWord] using earlier
    | retire child => simpa [slotWord] using earlier
    | operate src slot inverse =>
      by_cases same : owner = src ∧ key = slot <;> simpa [slotWord, same] using earlier
    | restrict src slot =>
      by_cases same : owner = src ∧ key = slot
      · obtain ⟨rfl, rfl⟩ := same
        simp [slotWord]
      · simp [slotWord, same, earlier]

theorem slotWord_unrestricted (denote : InverseMeaning Key Value) (owner : Name) (key : Key) (word : List I)
    (noRestriction : Inverse.restrict owner key ∉ word) :
    slotWord denote owner key word = (captures denote owner key word, false) := by
  induction word with
  | nil => rfl
  | cons inverse tail earlier =>
    have tailWithoutRestriction : Inverse.restrict owner key ∉ tail :=
      fun member => noRestriction (List.mem_cons_of_mem _ member)
    have result := earlier tailWithoutRestriction
    cases inverse with
    | unit => exact result
    | retire child => exact result
    | restrict src slot =>
      by_cases same : owner = src ∧ key = slot
      · obtain ⟨rfl, rfl⟩ := same
        exact False.elim (noRestriction List.mem_cons_self)
      · simpa [slotWord, captures, same] using result
    | operate src slot inverse =>
      by_cases same : owner = src ∧ key = slot
      · obtain ⟨rfl, rfl⟩ := same
        simp [slotWord, captures, result]
      · simpa [slotWord, captures, same] using result

def interpret (word : List (PartialMap Value) × Bool) : PartialMap (Option Value) :=
  if word.2 then eraseAfter word.1 else keepMissing (run word.1)

private theorem on_absent (denote : InverseMeaning Key Value) (owner : Name) (key : Key) (word : List I) :
    run (word.map (project denote owner key)) none = some none := by
  induction word with
  | nil => rfl
  | cons inverse tail earlier =>
    have atom : project denote owner key inverse none = some none := by
      cases inverse <;> simp only [project] <;> split <;> rfl
    simpa only [List.map_cons, PartialReplayHistory.run_cons, atom, Option.bind_some] using earlier

private theorem interpret_cons (head : PartialMap Value) (ops : List (PartialMap Value)) (erases : Bool)
    (input : Option Value) :
    (keepMissing head input).bind (interpret (ops, erases)) = interpret (head :: ops, erases) input := by
  cases erases <;> cases input with
  | none => rfl
  | some v => cases called : head v <;> simp [interpret, eraseAfter, keepMissing, called]

/-- Exact normalization of the replay word at a slot. A restriction cannot
leave a later operation looking at an occupied slot. -/
theorem slotWord_exact (denote : InverseMeaning Key Value) (owner : Name) (key : Key)
    (word : List I) (input : Option Value) :
    run (word.map (project denote owner key)) input = interpret (slotWord denote owner key word) input := by
  induction word generalizing input with
  | nil => cases input <;> rfl
  | cons inverse tail earlier =>
    simp only [List.map_cons, PartialReplayHistory.run_cons]
    cases inverse with
    | unit => exact earlier input
    | retire child => exact earlier input
    | restrict src slot =>
      by_cases same : owner = src ∧ key = slot
      · cases input <;> simp [project, slotWord, interpret, eraseAfter, keepMissing,
          same, on_absent]
      · simpa [project, slotWord, same] using earlier input
    | operate src slot inverse =>
      by_cases same : owner = src ∧ key = slot
      · simp only [project, slotWord, if_pos same]
        cases completed : keepMissing (denote key inverse) input with
        | none =>
          simpa only [completed, Option.bind_none] using
            interpret_cons (denote key inverse) (slotWord denote owner key tail).1
              (slotWord denote owner key tail).2 input
        | some middle =>
          have continues := interpret_cons (denote key inverse) (slotWord denote owner key tail).1
            (slotWord denote owner key tail).2 input
          rw [completed, Option.bind_some] at continues
          exact (earlier middle).trans continues
      · simpa [project, slotWord, same] using earlier input

end Cordis.PartialReplaySlots
