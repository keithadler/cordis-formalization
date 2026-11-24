import Cordis.Coeffects
import Cordis.Safety

/-!
Observable recovery for the actual registry-stage semantics. Primitive operation
callbacks must provide their value-level witnesses; these are not properties of
an arbitrary callback. This module proves the registry lift preserves those
witnesses, including instantiation whose inverse leaves a retired empty entry.
Successful executions use the ordinary landing relation.
-/

namespace Cordis.StageRecovery
open Calculus Stages Effects Iterators
universe u
variable {Name Key Value Code Error : Type u}
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
variable [DecidableEq Name] [DecidableEq Key]

def tableAt (r : R) (owner : Name) (key : Key) : Option Value :=
  (r owner).bind (fun fiber => fiber.table key)

omit [DecidableEq Key] in
theorem tableAt_retire (r : R) (child owner : Name) (key : Key) :
    tableAt (Calculus.retire r child) owner key = tableAt r owner key :=
  retire_preserves_tables r child owner key

omit [DecidableEq Key] in
theorem tableAt_mark (r : R) (actor owner : Name) (key : Key)
    (phase : Phase Name Key Code (Inverse Name Key Value)) :
    tableAt (mark r actor phase) owner key = tableAt r owner key := by
  by_cases h : owner = actor
  · subst owner
    cases hr : r actor <;> simp [tableAt, mark, Calculus.modify, hr]
  · simp [tableAt, mark, Calculus.modify, h]

theorem tableAt_restrict (r : R) (owner n : Name) (key k : Key) :
    tableAt (Stages.undo (.restrict owner key) r) n k =
      if n = owner ∧ k = key then none else tableAt r n k := by
  by_cases hn : n = owner
  · subst n
    cases hr : r owner <;> by_cases hk : k = key <;>
      simp [tableAt, Stages.undo, write, Calculus.modify, hr, hk]
  · simp [tableAt, Stages.undo, write, Calculus.modify, hn]

theorem tableAt_operate (r : R) (owner n : Name) (key k : Key) (inverse : Value → Value) :
    tableAt (Stages.undo (.operate owner key inverse) r) n k =
      if n = owner ∧ k = key then (tableAt r owner key).map inverse else tableAt r n k := by
  by_cases hn : n = owner
  · subst n
    cases hr : r owner <;> by_cases hk : k = key <;>
      simp [tableAt, Stages.undo, Calculus.modify, hr, hk]
  · simp [tableAt, Stages.undo, Calculus.modify, hn]

section Observation
variable [Setoid Value]

/-- Per-owner tables agree up to their value observation. This is stronger than
the paper's union-of-tables projection, and still ignores absent versus empty
fibers and all control fields. `projected` below states the implication. -/
def TablesRelated (r s : R) : Prop :=
  ∀ owner key, OptionRel (fun v w : Value => v ≈ w) (tableAt r owner key) (tableAt s owner key)

omit [DecidableEq Name] [DecidableEq Key] in
theorem tables_refl (r : R) : TablesRelated r r := by
  intro owner key
  cases tableAt r owner key with
  | none => trivial
  | some v => exact Setoid.refl v

omit [DecidableEq Name] [DecidableEq Key] in
theorem tables_symm {r s : R} (h : TablesRelated r s) : TablesRelated s r := by
  intro owner key
  exact @OptionRel.mono Value Value (fun x y => y ≈ x) (fun x y => x ≈ y)
    (fun _ _ h => Setoid.symm h) _ _ (OptionRel.symm (h owner key))

omit [DecidableEq Name] [DecidableEq Key] in
theorem tables_trans {r s t : R} (hrs : TablesRelated r s) (hst : TablesRelated s t) :
    TablesRelated r t := by
  intro owner key
  exact @OptionRel.trans Value (fun x y => x ≈ y)
    (fun _ _ _ h₁ h₂ => Setoid.trans h₁ h₂) _ _ _ (hrs owner key) (hst owner key)

/-- Def51's union projection: each binding has a related counterpart independent
of which owner stores it. Per-owner recovery therefore implies the paper's
coeffect-projection recovery at every restricted set of keys. -/
def ProjectedRelated (keys : Key → Prop) (r s : R) : Prop :=
  ∀ key, keys key →
    (∀ owner v, tableAt r owner key = some v →
      ∃ owner' w, tableAt s owner' key = some w ∧ v ≈ w) ∧
    (∀ owner w, tableAt s owner key = some w →
      ∃ owner' v, tableAt r owner' key = some v ∧ v ≈ w)

omit [DecidableEq Name] [DecidableEq Key] in
theorem TablesRelated.projected {r s : R} (h : TablesRelated r s) (keys : Key → Prop) :
    ProjectedRelated keys r s := by
  intro key _
  constructor
  · intro owner v hv
    have hh := h owner key
    rw [hv] at hh
    cases hs : tableAt s owner key with
    | none => simp [hs, OptionRel] at hh
    | some w => exact ⟨owner, w, hs, by simpa only [hs, OptionRel] using hh⟩
  · intro owner w hw
    have hh := h owner key
    rw [hw] at hh
    cases hr : tableAt r owner key with
    | none => simp [hr, OptionRel] at hh
    | some v => exact ⟨owner, v, hr, by simpa only [hr, OptionRel] using hh⟩

def InverseRespects : Inverse Name Key Value → Prop
  | .operate _ _ inverse => Effects.Respects inverse
  | _ => True

theorem inverse_respects {inverse : Inverse Name Key Value} (h : InverseRespects inverse)
    {r s : R} (hrs : TablesRelated r s) :
    TablesRelated (Stages.undo inverse r) (Stages.undo inverse s) := by
  intro owner key
  cases inverse with
  | unit => exact hrs owner key
  | restrict n k =>
    rw [tableAt_restrict, tableAt_restrict]
    split
    · trivial
    · exact hrs owner key
  | operate n k inverse =>
    rw [tableAt_operate, tableAt_operate]
    split
    · have hn := hrs n k
      cases hr : tableAt r n k <;> cases hs : tableAt s n k <;> simp_all [OptionRel]
      exact h hn
    · exact hrs owner key
  | retire child =>
    simpa only [Stages.undo, tableAt_retire] using hrs owner key

/-- The primitive witness is attached to each successful callback result; error
results have no returned inverse and do not satisfy a `Land` constructor. -/
def OperationWitnesses (program : Code → Instruction Name Key Value Code Error) : Prop :=
  ∀ code key run, (program code).action = .operate key run →
    ∀ before after inverse result, run before = .ok (after, inverse, result) →
      inverse after ≈ before ∧ Effects.Respects inverse

theorem discharge_respects (inverses : List (Inverse Name Key Value))
    (h : ∀ inverse ∈ inverses, InverseRespects inverse) {r s : R}
    (hrs : TablesRelated r s) :
    TablesRelated (discharge Stages.undo inverses r) (discharge Stages.undo inverses s) := by
  induction inverses generalizing r s with
  | nil => exact hrs
  | cons inverse rest ih =>
    exact ih (fun u hu => h u (by simp [hu]))
      (inverse_respects (h inverse (by simp)) hrs)

end Observation

end Cordis.StageRecovery
