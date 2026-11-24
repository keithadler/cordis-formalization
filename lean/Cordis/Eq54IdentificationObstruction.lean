import Cordis.Eq54FixedBaseExamples

/-! The remaining original Equation54 identification is impossible, rather
than an unproved equivalence with a stronger sufficient construction.

Definition34 fixes the Definition33 state base, and Definition51 specifies its
union-of-all-tables projection throughout Section4. Equation54 sends function
fields back to that relation. Terminal unit and terminal birth are therefore
related, with global Definition37 witnesses on all finite rooted Gamma.

ANY reflexive domain-preserving rebased relation separates the same functions
and recursive iterators. Rebasing cannot identify the original arrow relation.
Independently, ANY domain-preserving whole-state relation satisfying Lemma60's
even weaker reachable L-Finish simulation must separate the two actual input
states that literal Equation54 relates. This is not merely a comparison of two
arbitrarily selected fresh outcomes: every birth-side counterpart is excluded.

A successor simulation preserving the registry domain must change the
function observation in Equation (54). -/
namespace Cordis.Eq54IdentificationObstruction
noncomputable section
open Calculus Stages Effects Iterators RenamingLiteral Eq54FixedBase Eq54FixedBaseExamples

open RenamingLiteralExamples (rootName childName emptyView program rootComponent)

/-- Every legal birth-side Finish creates a domain element absent after the
unit-side Finish. The witness is obtained from the actual rule constructor,
not an assumed allocation or chosen counterpart result. -/
theorem every_birth_finish_changes_domain (after : R)
    (step : Labeled.Step program .finish rootName birthBefore after) :
    ∃ name, unitAfter name = none ∧ after name ≠ none := by
  cases step with
  | finish _ middle _ entry code accumulator view inverse present phase target land =>
    have sameEntry : entry = { (fresh rootComponent none : F) with phase := .reloading true [] emptyView } :=
      (Option.some.inj present).symm
    subst entry
    have selected : code = true ∧ accumulator = [] ∧ view = emptyView := by simpa using phase.symm
    obtain ⟨rfl, rfl, rfl⟩ := selected
    obtain ⟨name, absent, presentChild⟩ := born_child_present land
    have different : name ≠ rootName := by
      intro same
      subst name
      cases absent
    refine ⟨name, ?_, ?_⟩
    · simp [unitAfter, unitBefore, unitInserted, r0, RenamingLiteralExamples.r0, mark, Calculus.modify, put, different]
    · simp [mark, Calculus.modify, different, presentChild]

end
end Cordis.Eq54IdentificationObstruction
