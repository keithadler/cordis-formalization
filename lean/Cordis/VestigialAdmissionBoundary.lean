import Cordis.RenamingLiteralExamples
import Cordis.WellFormed

/-! Original Lemma62 admission certificate. Reuse the full finite-rooted Gamma
and globally witnessed unit/terminal-birth semantics of RenamingLiteralExamples,
not merely a primitive trace with uninterpreted component codes. The very same
six actual steps reach a retired inactive child whose parent pointer blocks
removal of its parent. Erasing that vestige enables O-Remove, neither of the
original converse's two O-Insert exceptions. No nonempty provision, missing
primitive domain, changed observation base or name reuse is involved. -/
namespace Cordis.VestigialAdmissionBoundary
noncomputable section
open Calculus Stages Effects Iterators RenamingLiteral RenamingLiteralExamples

theorem final_entries :
    r6 rootName = some { (fresh rootComponent none : F) with retired := true } ∧
    r6 childName = some { (fresh childComponent (some rootName) : F) with retired := true } := ⟨rfl, rfl⟩

theorem final_other (name : Name) (root : name ≠ rootName) (child : name ≠ childName) : r6 name = none := by
  simp [r6, r5, r4, r3, middle, r2, r1, r0, Calculus.discharge, Stages.undo,
    mark, Calculus.modify, Calculus.retire, put, root, child]

theorem child_vestigial : Removable r6 childName := by
  simp only [Removable, final_entries.2]
  refine ⟨trivial, rfl, (fun key => nomatch key), ?_⟩
  intro name
  by_cases root : name = rootName
  · subst name; simp [final_entries.1, fresh]
  · by_cases child : name = childName
    · subst name; simp only [final_entries.2, fresh]; decide
    · simp [final_other name root child]

theorem parent_blocked : ¬ Removable r6 rootName := by
  intro removable
  exact child_prevents_removal r6 rootName childName _ final_entries.2 rfl removable

theorem parent_enabled : Removable (erase r6 childName) rootName := by
  have present : erase r6 childName rootName = r6 rootName := rfl
  simp only [Removable, present, final_entries.1]
  refine ⟨trivial, rfl, (fun key => nomatch key), ?_⟩
  intro name
  by_cases child : name = childName
  · subst name; simp [erase]
  · by_cases root : name = rootName
    · subst name; simp only [erase, if_neg child, final_entries.1, fresh]; trivial
    · simp [erase, child, final_other name root child]

theorem remove_after_erasure : Labeled.Step program .remove rootName (erase r6 childName)
    (erase (erase r6 childName) rootName) := .remove _ _ parent_enabled

theorem no_remove_before (after : R) : ¬ Labeled.Step program .remove rootName r6 after := by
  intro step
  cases step with
  | remove _ _ allowed => exact parent_blocked allowed

theorem endpoint_admissible : Safety.Tree r6 ∧ FiniteDomain r6 := by
  refine ⟨endpoint_reachable.reachable_invariants.1, [rootName, childName], ?_⟩
  intro name present
  by_cases root : name = rootName
  · simp [root]
  · by_cases child : name = childName
    · simp [child]
    · exact False.elim (present (final_other name root child))

end
end Cordis.VestigialAdmissionBoundary
