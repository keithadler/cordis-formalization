import Cordis.TypedRegistrySupport
import Cordis.TypedStateObservation

/-! Lemma 77 under the displayed O-Insert rule. An external child starts
independently of its retired parent because the target does not read the
parent pointer. Equation (62) still reads that pointer. -/
namespace Cordis.TypedRegistry.DisplayedSupport

open PaperEffectEquations (CoeffectOperations)
open TypedStateObservation (Semantics)

abbrev Values : Empty → Type := fun _ => Unit

def operations : CoeffectOperations Values where
  Name key := nomatch key
  Argument key := nomatch key
  Outcome key := nomatch key
  operation key := nomatch key

private abbrev State := Registry Bool Values Unit
private abbrev Row := Fiber Bool Values Unit

def program : Unit → Instruction Bool operations Unit := fun _ => ⟨.unit, fun _ => none⟩

private def component : Calculus.Component Empty Unit :=
  ⟨fun _ => false, fun _ => false, ()⟩
private def empty : State := fun _ => none
private def view : Calculus.View Bool Empty := fun key => nomatch key

private def parentEntry : Row := fresh component none
private def childEntry : Row := fresh component (some false)
private def parentInserted : State := put empty false parentEntry
private def bothInserted : State := put parentInserted true childEntry
private def parentRetired : State := retire bothInserted false
private def childReloading : Row := {childEntry with phase := .reloading () [] view}
private def childBegun : State := mark parentRetired true (.reloading () [] view)
private def retiredParent : Row := {parentEntry with retired := true}
private def activeChild : Row := {childEntry with phase := .active [.unit] view}
private def final : State := mark childBegun true (.active [.unit] view)

private theorem target_parentRetired : Target parentRetired true view := by
  exact ⟨rfl, fun key => nomatch key⟩

private theorem target_childBegun : Target childBegun true view := by
  exact ⟨rfl, fun key => nomatch key⟩

/-- Both insertions are external. The second names the first fiber as its
parent, which the displayed freshness and parent-existence premises allow. -/
def trace : Trace program empty 5 where
  state
    | 0 => empty
    | 1 => parentInserted
    | 2 => bothInserted
    | 3 => parentRetired
    | 4 => childBegun
    | _ => final
  rule
    | 0 | 1 => .insert
    | 2 => .retire
    | 3 => .begin
    | _ => .finish
  actor
    | 0 | 2 => false
    | _ => true
  start := rfl
  step := by
    intro t bounded
    have indices : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 := by omega
    rcases indices with rfl | rfl | rfl | rfl | rfl
    · exact .insert empty false component none ⟨rfl, by simp, fun _ key => nomatch key⟩
    · refine .insert parentInserted true component (some false) ⟨rfl, ?_, fun _ key => nomatch key⟩
      intro parent selected
      cases selected
      intro missing
      cases missing
    · exact .retire bothInserted false (fun absent => by cases absent)
    · exact .begin parentRetired true childEntry view rfl rfl target_parentRetired
    · exact .finish childBegun childBegun true childReloading () [] view .unit rfl rfl
        target_childBegun (.unit _ _ _ rfl)

/-- The stored unit program is admitted on rooted registries. With Boolean
names every registry has finite domain, and no inverse can change a parent. -/
def semantics : Semantics Bool Values Unit where
  domain state := Safety.Tree (encodeRegistry operations state)
  iterator _ _ := Iterators.embed Effects.identity
  undo_closed token state valid := by
    cases token with
    | unit => exact valid
    | restrict _ key | operate _ key => exact nomatch key
    | retire child =>
      rw [undo, encode_retire]
      exact Safety.modify_tree (encodeRegistry operations state) child _ (fun _ => rfl) valid
  keyObservation key := nomatch key

theorem states_admitted :
    ∀ t, t ≤ 5 → semantics.domain (trace.state t) := by
  intro t bounded
  induction t with
  | zero => exact Safety.empty_tree
  | succ t ih =>
    exact Safety.step_tree (encodeProgram program) (trace.encode.step t bounded).toCalculus
      (ih (Nat.le_of_succ_le bounded))

theorem unit_admitted (actor : Bool) (keys : Empty → Prop) :
    @Iterators.WitnessedIterator _ (TypedStateObservation.observation operations semantics keys)
      (semantics.iterator actor ()) :=
  @Iterators.witnessed_embed _ (TypedStateObservation.observation operations semantics keys)
    Effects.identity (@Effects.witnessed_identity _ (TypedStateObservation.observation operations semantics keys))

private theorem quiet : Quiet final := by
  intro name row found
  cases name
  · have same : retiredParent = row := Option.some.inj found
    subst row
    intro _ target
    have impossible : true = false := target.1
    cases impossible
  · have same : activeChild = row := Option.some.inj found
    subst row
    exact ⟨rfl, fun key => nomatch key⟩

private theorem acyclic : FiniteOrder.Acyclic (precedes final) := by
  intro name cycle
  cases cycle with
  | single edge =>
    obtain ⟨key, _⟩ := edge
    exact nomatch key
  | tail _ edge =>
    obtain ⟨key, _⟩ := edge
    exact nomatch key

private theorem support_wellFounded : WellFounded (supportEdge final) := by
  let rank : Bool → Nat := fun child => if child then 1 else 0
  apply Subrelation.wf _ (measure rank).wf
  rintro parent child ⟨_, _, dependency | ancestry⟩
  · obtain ⟨key, _⟩ := dependency
    exact nomatch key
  · cases child
    · change (none : Option Bool) = some parent at ancestry
      cases ancestry
    · have parentName : false = parent := Option.some.inj ancestry
      subst parent
      change 0 < 1
      decide

private theorem no_supported_parent (set : Bool → Prop) (solution : SupportSolution final set) :
    ¬ set false := by
  intro member
  obtain ⟨row, found, live, _⟩ := (solution false).mp member
  have same : retiredParent = row := Option.some.inj found
  subst row
  cases live

private theorem no_supported_child (set : Bool → Prop) (solution : SupportSolution final set) :
    ¬ set true := by
  intro member
  obtain ⟨row, found, _, ancestry, _⟩ := (solution true).mp member
  have same : activeChild = row := Option.some.inj found
  subst row
  rcases ancestry with root | ⟨parent, selected, supported⟩
  · cases root
  · have sameParent : false = parent := Option.some.inj selected
    subst parent
    exact no_supported_parent set solution supported

private theorem empty_solution : SupportSolution final (fun _ => False) := by
  intro name
  constructor
  · exact False.elim
  · rintro ⟨row, found, live, ancestry, _⟩
    cases name
    · have same : retiredParent = row := Option.some.inj found
      subst row
      cases live
    · have same : activeChild = row := Option.some.inj found
      subst row
      rcases ancestry with root | ⟨_, _, impossible⟩
      · cases root
      · exact impossible

end Cordis.TypedRegistry.DisplayedSupport

namespace Cordis.TypedRegistry
open DisplayedSupport

/-- The displayed-rule run refutes the support/active equality in Lemma 77
when external O-Insert may name a parent. The support equation has a solution,
and every solution excludes the active child. -/
theorem lemma77_displayed_insert_counterexample :
    ∃ history : Trace (ops := operations) program (fun _ => none) 5,
      FiniteOrder.Acyclic (precedes (history.state 5)) ∧
      WellFounded (supportEdge (history.state 5)) ∧
      Quiet (history.state 5) ∧
      TotalProvision (history.state 5) ∧
      Active (history.state 5) true ∧
      SupportSolution (history.state 5) (fun _ => False) ∧
      (∀ set, SupportSolution (history.state 5) set → ¬ set true) ∧
      ¬ history.RootInsertions := by
  refine ⟨trace, acyclic, support_wellFounded, quiet, (fun _ _ _ _ key => nomatch key), ⟨_, rfl, trivial⟩,
    empty_solution, no_supported_child, ?_⟩
  intro roots
  obtain ⟨row, found, root⟩ := roots 1 (by decide) rfl
  have same : childEntry = row := Option.some.inj found
  subst row
  cases root

end Cordis.TypedRegistry
