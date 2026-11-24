import Cordis.Repairs.CausalCommands

/-! A necessary limit on the ordering repair: removing a dormant child can
enable a root insertion that was previously blocked by its provisions. This
is a guard-level obstruction to unconditional sorting, not a new assertion
that all the semantic hypotheses of Theorem 80 hold for this example. -/
namespace Cordis.Repairs.CommandBarrier
open Calculus Stages OrchestrationSorting

abbrev R := Registry Nat Unit Unit Bool (Inverse Nat Unit Unit) Empty
abbrev F := Fiber Nat Unit Unit Bool (Inverse Nat Unit Unit) Empty
def parentComponent : Component Unit Bool := ⟨fun _ => false, fun _ => false, true⟩
def providerComponent : Component Unit Bool := ⟨fun _ => false, fun _ => true, false⟩
def program (code : Bool) : Instruction Nat Unit Unit Bool Empty :=
  ⟨if code then .instantiate providerComponent else .provide () (), fun _ => none⟩
def view : View Nat Unit := fun _ => 0
def empty : R := fun _ => none
def inserted : R := put empty 0 (fresh parentComponent none)
def begun : R := mark inserted 0 (.reloading true [] view)
def born : R := put begun 1 (fresh providerComponent (some 0))
def finished : R := mark born 0 (.active [.retire 1] view)
def before : R := Calculus.retire finished 1
def middle : R := erase before 1
def after : R := put middle 2 (fresh providerComponent none)
def removeChild : Command Nat Unit Bool := .remove 1
def insertRoot : Command Nat Unit Bool := .insert 2 providerComponent

theorem inserted_step : Labeled.Step program .insert 0 empty inserted :=
  .insert empty 0 parentComponent none ⟨rfl, by simp, fun _ _ => trivial⟩

theorem begin_step : Labeled.Step program .begin 0 inserted begun :=
  .begin inserted 0 (fresh parentComponent none) view rfl rfl
    (by change some _ ≠ none; simp) ⟨rfl, fun _ => by simp [fresh, parentComponent]⟩

theorem finish_step : Labeled.Step program .finish 0 begun finished := by
  have birthReady : Insertable begun 1 providerComponent (some 0) := by
    refine ⟨rfl, ?_, ?_⟩
    · intro name same
      have eq : 0 = name := Option.some.inj same
      subst name
      change some _ ≠ none
      simp
    · intro name key
      by_cases atParent : name = 0
      · subst name; simp [begun, inserted, mark, Calculus.modify, put, fresh, parentComponent]
      · simp [begun, inserted, empty, mark, Calculus.modify, put, atParent]
  exact .finish begun born 0 { (fresh parentComponent none : F) with phase := .reloading true [] view }
    true [] view (.retire 1) rfl rfl ⟨rfl, fun _ => by simp [fresh, parentComponent]⟩
    (.instantiate begun 0 true providerComponent 1 rfl birthReady)

theorem retire_step : Labeled.Step program .retire 1 finished before :=
  .retire finished 1 (by change some _ ≠ none; simp)

theorem reachable : WellFormed.Run program empty before :=
  .step (.step (.step (.step (.refl empty) inserted_step.toCalculus)
    begin_step.toCalculus) finish_step.toCalculus) retire_step.toCalculus

theorem removal_enabled : removeChild.Enabled before := by
  refine ⟨rfl, rfl, fun _ => rfl, ?_⟩
  intro name
  by_cases atParent : name = 0
  · subst name; change (none : Option Nat) ≠ some 1; simp
  by_cases atChild : name = 1
  · subst name; change (some 0 : Option Nat) ≠ some 1; decide
  simp [before, finished, born, begun, inserted, empty, Calculus.retire,
    mark, Calculus.modify, put, atParent, atChild]

theorem insertion_enabled_after : insertRoot.Enabled middle := by
  refine ⟨rfl, by simp, ?_⟩
  intro name key
  by_cases atParent : name = 0
  · subst name; simp [middle, before, finished, born, begun, inserted, Calculus.retire,
      erase, mark, Calculus.modify, put, fresh, parentComponent]
  by_cases atChild : name = 1
  · subst name; simp [middle, erase]
  simp [middle, before, finished, born, begun, inserted, empty, Calculus.retire,
    erase, mark, Calculus.modify, put, atParent, atChild]

theorem legal_pair : removeChild.Step before middle ∧ insertRoot.Step middle after :=
  ⟨⟨removal_enabled, rfl⟩, ⟨insertion_enabled_after, rfl⟩⟩

theorem insertion_blocked_before : ¬ insertRoot.Enabled before := by
  intro enabled
  have conflict := enabled.2.2 1 ()
  exact conflict rfl rfl

theorem distinct_actors : removeChild.actor ≠ insertRoot.actor := by decide

/-- Even with distinct actors and two legal original steps, there is no
legal reversed pair. The missing earlier-enabled premise is substantive. -/
theorem no_reversed_pair : ¬ ∃ swapped, insertRoot.Step before swapped ∧ removeChild.Step swapped after := by
  rintro ⟨swapped, insertedFirst, _⟩
  exact insertion_blocked_before insertedFirst.1

end Cordis.Repairs.CommandBarrier
