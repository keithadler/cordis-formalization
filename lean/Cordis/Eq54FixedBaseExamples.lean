import Cordis.Eq54FixedBase
import Cordis.RenamingLiteralExamples

/-! A fixed-Definition33-base Eq54 countermodel for Lemma60's successor clause.
Two actual empty-origin prefixes install a unit component and a terminal child
instantiator. Their remaining iterators and component entries are globally
logically related over full finite rooted Gamma, as are their empty accumulators.
Both actual L-Finish rules apply. Every instantiating counterpart adds a fresh
name, whereas unit cannot; their outputs violate Eq54's explicit domain clause.
This result does not assert a counterexample to a recursively rebased arrow. -/
namespace Cordis.Eq54FixedBaseExamples
noncomputable section
open Calculus Stages Iterators RenamingLiteral Eq54FixedBase
open RenamingLiteralExamples (rootName childName emptyView program rootComponent)

abbrev r0 : R := RenamingLiteralExamples.r0
def unitInserted : R := put r0 rootName (fresh Eq54FixedBase.childComponent none)
def unitBefore : R := mark unitInserted rootName (.reloading false [] emptyView)
def unitAfter : R := mark unitBefore rootName (.active [.unit] emptyView)
abbrev birthBefore : R := RenamingLiteralExamples.r2

def draw : Gamma → Name := preferFresh childName

theorem unit_insert : Orchestration.Step program r0 unitInserted :=
  .insert r0 rootName Eq54FixedBase.childComponent ⟨rfl, by simp, by intro _ key; exact nomatch key⟩
theorem unit_begin : Orchestration.Step program unitInserted unitBefore :=
  .begin unitInserted rootName (fresh Eq54FixedBase.childComponent none : F) emptyView rfl rfl (by change some _ ≠ none; simp)
    ⟨rfl, by intro key; exact nomatch key⟩
theorem unit_before_reachable : Orchestration.Run program r0 unitBefore :=
  .step (.step (.refl _) unit_insert) unit_begin

theorem unit_finish : Labeled.Step program .finish rootName unitBefore unitAfter :=
  .finish unitBefore unitBefore rootName
    { (fresh Eq54FixedBase.childComponent none : F) with phase := .reloading false [] emptyView }
    false [] emptyView .unit rfl rfl ⟨rfl, by intro key; exact nomatch key⟩
    (.unit unitBefore rootName false rfl)

theorem unit_finite : FiniteDomain unitBefore :=
  modify_finite unitInserted rootName _ (put_finite r0 rootName _ RenamingLiteralExamples.r0_finite)
def unitGamma : Gamma := ⟨unitBefore, unit_before_reachable.reachable_invariants.1, unit_finite⟩
abbrev birthGamma : Gamma := RenamingLiteralExamples.birthGamma

/-- Inspecting actual primitive constructors proves every possible selected
fresh child is new, independently of a preferred allocation policy. -/
theorem born_child_present {actor : Name} {before after : R} {inverse : Inverse Name Empty Unit}
    {next : Option Code} (landed : Land program actor true before after inverse next) :
    ∃ child, before child = none ∧ after child = some (fresh Eq54FixedBase.childComponent (some actor)) := by
  cases landed with
  | unit _ _ _ impossible => cases impossible
  | provide _ _ _ _ key => exact nomatch key
  | operate _ _ _ key => exact nomatch key
  | instantiate before actor code component child action ready =>
    have equal : component = Eq54FixedBase.childComponent := by cases action; rfl
    subst component
    exact ⟨child, ready.1, by simp [put]⟩

end
end Cordis.Eq54FixedBaseExamples
