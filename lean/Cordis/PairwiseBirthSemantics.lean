import Cordis.SupportUniqueness
import Cordis.Iterators

/-! Full-Gamma semantics for auditing Lemma66. Every component and every
produced continuation has a global Definition37 witness. A fresh-name test
changes a subsequent child COMPONENT while preserving the parent iterator's
Maybe shape. The named child entries themselves have different Maybe shapes,
so semantic component agreement can still distinguish them.

All keys are empty but the registry, parenting, captures and iterator shapes
are real. Gamma contains every finite rooted registry of this syntax; the
freshness proof is global. Only equality with a captured atom is observed by
the program. The numerical construction below proves existence of fresh atoms,
not a language operation that inspects their representation. -/
namespace Cordis.PairwiseBirthSemantics
noncomputable section
open Calculus Stages Effects Iterators StageRecovery

inductive Code where
  | unit | twoBirths | foreign | parent | tailShort | tailLong
  deriving DecidableEq

abbrev R := Registry Nat Empty Unit Code (Inverse Nat Empty Unit) Empty
abbrev F := Fiber Nat Empty Unit Code (Inverse Nat Empty Unit) Empty
abbrev Gamma := {state : R // Safety.Tree state ∧ SupportUniqueness.FiniteDomain state}
local instance : Setoid Unit := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩

theorem projected_all (left right : R) : ProjectedRelated (fun _ => True) left right := by
  intro key; exact nomatch key

instance gammaSetoid : Setoid Gamma where
  r left right := ProjectedRelated (fun _ => True) left.val right.val
  iseqv := ⟨fun _ => projected_all _ _, fun _ => projected_all _ _, fun _ _ => projected_all _ _⟩

def component (entry : Code) : Component Empty Code := ⟨fun _ => false, fun _ => false, entry⟩

def program : Code → Instruction Nat Empty Unit Code Empty
  | .unit => { action := .unit, next := fun _ => none }
  | .twoBirths => { action := .instantiate (component .unit), next := fun _ => some .tailShort }
  | .foreign | .tailShort => { action := .instantiate (component .unit), next := fun _ => none }
  | .tailLong => { action := .instantiate (component .twoBirths), next := fun _ => none }
  | .parent => { action := .instantiate (component .unit), next := fun outcome =>
      match outcome with
      | .child name => some (if name = 2 then .tailShort else .tailLong)
      | _ => none }

theorem fresh_exists (state : Gamma) : ∃ name, state.val name = none := by
  classical
  obtain ⟨names, covers⟩ := state.property.2
  let candidate := names.max?.getD 0 + 1
  by_cases absent : state.val candidate = none
  · exact ⟨candidate, absent⟩
  · cases found : state.val candidate with
    | none => exact False.elim (absent found)
    | some fiber =>
      have bound := List.le_max?_getD_of_mem (k := 0) (covers candidate fiber found)
      dsimp [candidate] at bound
      omega

def freshAtom (state : Gamma) : Nat := Classical.choose (fresh_exists state)
theorem freshAtom_absent (state : Gamma) : state.val (freshAtom state) = none :=
  Classical.choose_spec (fresh_exists state)

def draw (state : Gamma) : Nat := by
  classical
  exact if state.val 2 = none then 2 else freshAtom state

theorem draw_absent (state : Gamma) : state.val (draw state) = none := by
  unfold draw
  split
  · assumption
  · exact freshAtom_absent state

theorem draw_preferred (state : Gamma) (absent : state.val 2 = none) : draw state = 2 := by
  simp [draw, absent]

theorem draw_other (state : Gamma) (present : state.val 2 ≠ none) : draw state ≠ 2 := by
  intro same
  exact present (same ▸ draw_absent state)

def retireGamma (child : Nat) (state : Gamma) : Gamma :=
  ⟨Calculus.retire state.val child,
    Safety.modify_tree state.val child _ (fun _ => rfl) state.property.1,
    SupportUniqueness.modify_finite state.val child _ state.property.2⟩

def birthEffect (actor : Nat) (payload : Component Empty Code) : Effect Gamma := by
  classical
  exact ⟨fun state => if ready : Insertable state.val (draw state) payload (some actor) then
    (⟨put state.val (draw state) (fresh payload (some actor)),
      Safety.insert_tree _ _ _ _ state.property.1 ready,
      SupportUniqueness.put_finite _ _ _ state.property.2⟩, retireGamma (draw state))
    else (state, id)⟩

def unitIterator : Iterator Gamma := embed Effects.identity
def terminalBirth (actor : Nat) (payload : Component Empty Code) : Iterator Gamma := embed (birthEffect actor payload)

def meaning (actor : Nat) : Code → Iterator Gamma
  | .unit => unitIterator
  | .foreign | .tailShort => terminalBirth actor (component .unit)
  | .tailLong => terminalBirth actor (component .twoBirths)
  | .twoBirths => .node (birthEffect actor (component .unit))
      (fun _ => some (terminalBirth actor (component .unit)))
  | .parent => .node (birthEffect actor (component .unit))
      (fun state => some (if draw state = 2 then terminalBirth actor (component .unit)
        else terminalBirth actor (component .twoBirths)))

theorem terminal_birth_related (actor other : Nat) (first second : Component Empty Code) :
    RelatedIterator (terminalBirth actor first) (terminalBirth other second) := by
  apply related_fold
  intro left right _
  exact ⟨projected_all _ _, fun {_ _} _ => projected_all _ _, True.intro⟩

theorem terminal_birth_witnessed (actor : Nat) (payload : Component Empty Code) :
    WitnessedIterator (terminalBirth actor payload) := by
  apply witnessed_embed
  exact ⟨fun _ => projected_all _ _, fun {_ _} _ =>
    ⟨projected_all _ _, fun {_ _} _ => projected_all _ _⟩⟩

theorem all_components_witnessed (actor : Nat) (code : Code) : WitnessedIterator (meaning actor code) := by
  cases code with
  | unit => exact witnessed_embed witnessed_identity
  | foreign | tailShort => exact terminal_birth_witnessed actor (component .unit)
  | tailLong => exact terminal_birth_witnessed actor (component .twoBirths)
  | twoBirths =>
    apply WitnessedIterator.node
    · apply related_fold
      intro left right _
      exact ⟨projected_all _ _, fun {_ _} _ => projected_all _ _, terminal_birth_related _ _ _ _⟩
    · intro _; exact projected_all _ _
    · intro state tail selected
      cases Option.some.inj selected
      exact terminal_birth_witnessed _ _
  | parent =>
    apply WitnessedIterator.node
    · apply related_fold
      intro left right _
      refine ⟨projected_all _ _, fun {_ _} _ => projected_all _ _, ?_⟩
      change RelatedIterator (if draw left = 2 then _ else _) (if draw right = 2 then _ else _)
      split <;> split <;> exact terminal_birth_related _ _ _ _
    · intro _; exact projected_all _ _
    · intro state tail selected
      have selected' := Option.some.inj selected
      split at selected' <;> cases selected' <;> exact terminal_birth_witnessed _ _

/-- Literal finite unit/birth constructor fragment of Definition56. It has no
respect, independence, payload-uniformity or desired transition premise. -/
inductive Mediated (actor : Nat) : Iterator Gamma → Prop
  | unit : Mediated actor unitIterator
  | birth (payload : Component Empty Code) (next : Nat → Option (Iterator Gamma))
      (tails : ∀ name tail, next name = some tail → Mediated actor tail) :
      Mediated actor (.node (birthEffect actor payload) (fun state => next (draw state)))

theorem terminal_birth_mediated (actor : Nat) (payload : Component Empty Code) :
    Mediated actor (terminalBirth actor payload) := .birth payload (fun _ => none) (by
      intro _ _ impossible; cases impossible)

theorem all_components_mediated (actor : Nat) (code : Code) : Mediated actor (meaning actor code) := by
  cases code with
  | unit => exact .unit
  | foreign | tailShort | tailLong => exact terminal_birth_mediated _ _
  | twoBirths =>
    exact .birth _ (fun _ => some (terminalBirth actor (component .unit))) (by
      intro name tail same
      cases Option.some.inj same
      exact terminal_birth_mediated _ _)
  | parent =>
    exact .birth _ (fun name => some (if name = 2 then terminalBirth actor (component .unit)
      else terminalBirth actor (component .twoBirths))) (by
      intro name tail same
      have selected := Option.some.inj same
      split at selected <;> cases selected <;> exact terminal_birth_mediated _ _)

theorem fresh_ready (actor : Nat) (payload : Component Empty Code) (state : Gamma)
    (present : state.val actor ≠ none) : Insertable state.val (draw state) payload (some actor) := by
  exact ⟨draw_absent state, fun parent same => by cases same; exact present,
    fun _ key => nomatch key⟩

theorem birth_actual (actor : Nat) (payload : Component Empty Code) (state : Gamma)
    (present : state.val actor ≠ none) :
    ((birthEffect actor payload).run state).1.val = put state.val (draw state) (fresh payload (some actor)) ∧
    ∀ input : Gamma, (((birthEffect actor payload).run state).2 input).val = Calculus.retire input.val (draw state) := by
  simp [birthEffect, fresh_ready actor payload state present, retireGamma]

/-- The named child components fail even the ordinary Definition34 semantic
entry comparison. This is stronger than merely unequal code/payload literals. -/
theorem child_entries_not_related (actor other : Nat) (state : Gamma) :
    ¬ RelatedIterator (meaning actor .unit) (meaning other .twoBirths) := by
  intro related
  have impossible := (related_unfold related (show state ≈ state from projected_all _ _)).2.2
  exact impossible

end
end Cordis.PairwiseBirthSemantics
