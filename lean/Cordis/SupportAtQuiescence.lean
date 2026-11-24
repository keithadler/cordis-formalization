import Cordis.ChildProvenance
import Cordis.FiniteActionBudget

/-! Lemma77's fixed-point clauses on actual provenance-correct quiet states.
The active set is shown to solve the exact retirement/parent/provision equation.
Uniqueness is deliberately separate: it cannot be inherited from the refuted
unrestricted support well-foundedness claim in Lemma75. -/
namespace Cordis.SupportAtQuiescence
open Calculus Stages
universe u
variable {Name Key Value Code Error : Type u}
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
variable [DecidableEq Name] [DecidableEq Key]
set_option linter.unusedSectionVars false

def Active (r : R) (name : Name) : Prop :=
  ∃ fiber, r name = some fiber ∧ fiber.phase.available

/-- Definition76's endpoint consequence. This is literal domain equality, not
an assumption that declarations already satisfy any consumer's requirements. -/
def TotalProvision (r : R) : Prop :=
  ∀ name fiber, r name = some fiber → fiber.phase.available →
    ∀ key, fiber.table key ≠ none ↔ fiber.component.provides key = true

/-- Equation62, with the support set confined to the registry's actual domain. -/
def Solution (r : R) (set : Name → Prop) : Prop :=
  ∀ name, set name ↔ ∃ fiber, r name = some fiber ∧ fiber.retired = false ∧
    (fiber.parent = none ∨ ∃ parent, fiber.parent = some parent ∧ set parent) ∧
    ∀ key, fiber.component.requires key = true →
      ∃ provider entry, r provider = some entry ∧ set provider ∧ entry.component.provides key = true

theorem active_has_target (r : R) (quiet : Progress.Quiet r) (name : Name) (active : Active r name) :
    ∃ view, Target r name view := by
  obtain ⟨fiber, present, available⟩ := active
  have condition := quiet name fiber present
  cases phase : fiber.phase with
  | inactive | reloading | unloading => simp [phase, Phase.available] at available
  | active acc view => exact ⟨view, by simpa [phase] using condition⟩

theorem target_implies_active (r : R) (quiet : Progress.Quiet r) (name : Name)
    (view : View Name Key) (target : Target r name view) : Active r name := by
  cases present : r name with
  | none => simp [Target, present] at target
  | some fiber =>
    have condition := quiet name fiber present
    cases phase : fiber.phase with
    | inactive =>
      have noTarget : ∀ v, ¬ Target r name v := by simpa [phase] using condition
      exact False.elim (noTarget view target)
    | reloading | unloading => simp [phase] at condition
    | active acc chosen => exact ⟨fiber, present, by simp [phase, Phase.available]⟩

/-- A view is constructed from actual active providers and their bound tables.
Unrequired coordinates use the consumer's name and do not add requirements. -/
theorem target_of_providers (r : R) (total : TotalProvision r)
    (name : Name) (fiber : F) (present : r name = some fiber) (live : fiber.retired = false)
    (providers : ∀ key, fiber.component.requires key = true →
      ∃ provider entry, r provider = some entry ∧ Active r provider ∧ entry.component.provides key = true) :
    ∃ view, Target r name view := by
  classical
  have chooseProvider : ∀ key, ∃ provider, fiber.component.requires key = true →
      ∃ entry, r provider = some entry ∧ entry.phase.available ∧ entry.table key ≠ none := by
    intro key
    by_cases required : fiber.component.requires key = true
    · obtain ⟨provider, entry, found, ⟨activeEntry, activeFound, active⟩, provided⟩ := providers key required
      have same : activeEntry = entry := Option.some.inj (activeFound.symm.trans found)
      subst activeEntry
      exact ⟨provider, fun _ => ⟨entry, found, active, (total provider entry found active key).mpr provided⟩⟩
    · exact ⟨name, fun h => False.elim (required h)⟩
  let view : View Name Key := fun key => Classical.choose (chooseProvider key)
  refine ⟨view, ?_⟩
  simp only [Target, present]
  refine ⟨live, ?_⟩
  intro key required
  obtain ⟨entry, found, active, bound⟩ := Classical.choose_spec (chooseProvider key) required
  have located : r (view key) = some entry := found
  simp only [located]
  exact ⟨active, bound⟩

/-- Provenance supplies the parent clause and the target supplies actual
providers. Totality of provision supplies the converse. -/
theorem active_solution_of_capture {r : R} (captured : ChildProvenance.Captured r)
    (quiet : Progress.Quiet r) (total : TotalProvision r) : Solution r (Active r) := by
  intro name
  constructor
  · intro active
    obtain ⟨fiber, present, available⟩ := active
    obtain ⟨view, target⟩ := active_has_target r quiet name ⟨fiber, present, available⟩
    simp only [Target, present] at target
    refine ⟨fiber, present, target.1, ?_, ?_⟩
    · cases parent : fiber.parent with
      | none => exact .inl rfl
      | some parentName => exact .inr ⟨parentName, rfl,
          ChildProvenance.captured_quiet_parent_active captured quiet name fiber parentName present parent target.1⟩
    · intro key required
      have binding := target.2 key required
      cases found : r (view key) with
      | none => simp [found] at binding
      | some provider =>
        simp only [found] at binding
        exact ⟨view key, provider, found, ⟨provider, found, binding.1⟩,
          (total (view key) provider found binding.1 key).mp binding.2⟩
  · rintro ⟨fiber, present, live, _, providers⟩
    obtain ⟨view, target⟩ := target_of_providers r total name fiber present live providers
    exact target_implies_active r quiet name view target

/-- Even before proving uniqueness of the full support recursion, any solution
is contained in the active set. Induction descends only through real provider
edges; finite acyclicity constructs this induction order. -/
theorem solution_subset_active (r : R) (quiet : Progress.Quiet r) (total : TotalProvision r)
    (names : List Name) (covered : ∀ name fiber, r name = some fiber → name ∈ names)
    (acyclic : FiniteOrder.Acyclic (Progress.Depends r))
    (set : Name → Prop) (solution : Solution r set) (name : Name) : set name → Active r name := by
  have wf : WellFounded (fun provider consumer => Progress.Depends r consumer provider) := by
    apply FiniteOrder.wellFounded_of_finite_acyclic _ names _ (FiniteActionBudget.acyclic_flip _ acyclic)
    intro provider consumer edge
    obtain ⟨c, p, key, cp, pp, _⟩ := edge
    exact covered provider p pp
  apply wf.induction name
  intro consumer ih supported
  obtain ⟨fiber, present, live, _, providers⟩ := (solution consumer).mp supported
  have actual : ∀ key, fiber.component.requires key = true →
      ∃ provider entry, r provider = some entry ∧ Active r provider ∧ entry.component.provides key = true := by
    intro key required
    obtain ⟨provider, entry, found, supported, provided⟩ := providers key required
    exact ⟨provider, entry, found,
      ih provider ⟨fiber, entry, key, present, found, required, provided⟩ supported, provided⟩
  obtain ⟨view, target⟩ := target_of_providers r total consumer fiber present live actual
  exact target_implies_active r quiet consumer view target

end Cordis.SupportAtQuiescence
