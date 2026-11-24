import Cordis.Repairs.CompatibleProvision

/-!
The fixed-component repair is not yet a witness for instantiation. Two native
reachable registries have the same actor, component, phase, bound interface
(empty), and empty observable tables. An unrelated dormant root reserves the
child's declared provision in one registry. After its removal the same child
can be inserted. This obstruction is independent of fresh-name branching.
-/
namespace Cordis.Repairs.AllocationBoundary
open TypedRegistry CompatibleProvision
open PaperEffectEquations (CoeffectOperations)

abbrev Values : Unit → Type := fun _ => Unit
abbrev State := Registry Nat Values Bool
abbrev Row := Fiber Nat Values Bool
def operations : CoeffectOperations Values where
  Name _ := Empty
  Argument _ op := nomatch op
  Outcome _ op := nomatch op
  operation _ op := nomatch op
def parent : Calculus.Component Unit Bool := ⟨fun _ => false, fun _ => false, true⟩
def child : Calculus.Component Unit Bool := ⟨fun _ => false, fun _ => true, false⟩
def program (code : Bool) : Instruction Nat operations Bool :=
  ⟨if code then .instantiate child else .provide () (), fun _ => none⟩
def view : Calculus.View Nat Unit := fun _ => 0
def empty : State := fun _ => none
def inserted : State := put empty 0 (fresh parent none)
def begun : State := mark inserted 0 (.reloading true [] view)
def occupied : State := put begun 1 (fresh child none)
def blocked : State := retire occupied 1
def cleared : State := erase blocked 1

theorem insert_parent : Step program .insert 0 empty inserted :=
  .insert empty 0 parent none ⟨rfl, by simp, fun _ _ => trivial⟩
theorem begin_parent : Step program .begin 0 inserted begun :=
  .begin inserted 0 (fresh parent none) view rfl rfl
    ⟨rfl, fun _ required => Bool.noConfusion required⟩
theorem insert_blocker : Step program .insert 1 begun occupied := by
  apply Step.insert begun 1 child none
  refine ⟨rfl, by simp, ?_⟩
  intro name key
  by_cases same : name = 0
  · subst name
    simp [begun, inserted, mark, TypedRegistry.modify, put, fresh, parent]
  · simp [begun, inserted, empty, mark, TypedRegistry.modify, put, same]
theorem retire_blocker : Step program .retire 1 occupied blocked :=
  .retire occupied 1 (by change some _ ≠ none; simp)
theorem remove_blocker : Step program .remove 1 blocked cleared := by
  apply Step.remove blocked 1
  refine ⟨rfl, rfl, fun _ => rfl, ?_⟩
  intro name
  by_cases atParent : name = 0
  · subst name; change (none : Option Nat) ≠ some 1; simp
  by_cases atBlocker : name = 1
  · subst name; change (none : Option Nat) ≠ some 1; simp
  simp [blocked, occupied, begun, inserted, empty, retire, mark,
    TypedRegistry.modify, put, atParent, atBlocker]

def blockedInput : Gamma operations 0 parent :=
  ⟨blocked, step_allowed retire_blocker (step_allowed insert_blocker
      (step_allowed begin_parent (step_allowed insert_parent empty_allowed))),
    ⟨{ (fresh parent none : Row) with phase := .reloading true [] view }, rfl, rfl⟩⟩
def clearInput : Gamma operations 0 parent :=
  ⟨cleared, step_allowed remove_blocker blockedInput.property.1,
    ⟨{ (fresh parent none : Row) with phase := .reloading true [] view }, rfl, rfl⟩⟩
def observation (_ : Unit) : Setoid Unit := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩

theorem blocked_tables_empty : ∀ name key, tableAt blocked name key = none := by
  intro name key
  by_cases atBlocker : name = 1
  · subst name; rfl
  by_cases atParent : name = 0
  · subst name; rfl
  simp [blocked, occupied, begun, inserted, empty, tableAt, retire, mark,
    TypedRegistry.modify, put, atParent, atBlocker]
theorem cleared_tables_empty : ∀ name key, tableAt cleared name key = none := by
  intro name key
  by_cases same : name = 1
  · simp [cleared, erase, tableAt, same]
  · simpa [cleared, erase, tableAt, same] using blocked_tables_empty name key

theorem inputs_related : Observed observation (fun _ => True) blockedInput clearInput := by
  intro key _
  constructor
  · intro name value found
    change tableAt blocked name key = some value at found
    rw [blocked_tables_empty name key] at found
    cases found
  · intro name value found
    change tableAt cleared name key = some value at found
    rw [cleared_tables_empty name key] at found
    cases found

/-- Changing the fresh-name draw cannot cure the occupied-provision guard. -/
theorem allocation_blocked (name : Nat) : ¬ Insertable blocked name child (some 0) := by
  intro enabled
  have conflict := enabled.2.2 1 ()
  exact conflict rfl rfl

theorem allocation_enabled : Insertable cleared 2 child (some 0) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro name same
    have equal : 0 = name := Option.some.inj same
    subst name
    change some _ ≠ none
    simp
  · intro name key
    by_cases atBlocker : name = 1
    · subst name; simp [cleared, erase]
    by_cases atParent : name = 0
    · subst name
      simp [cleared, blocked, occupied, begun, inserted, erase, retire, mark,
        TypedRegistry.modify, put, fresh, parent]
    · simp [cleared, blocked, occupied, begun, inserted, empty, erase, retire, mark,
        TypedRegistry.modify, put, atParent, atBlocker]

theorem same_fresh_draw : blocked 2 = none ∧ cleared 2 = none := ⟨rfl, rfl⟩

noncomputable def allocate (state : Gamma operations 0 parent) : Option (Gamma operations 0 parent) := by
  classical
  exact if permitted : Insertable state.val 2 child (some 0) then
    some ⟨put state.val 2 (fresh child (some 0)),
      step_compatible (Step.insert (program := program) state.val 2 child (some 0) permitted)
        state.property (by
          obtain ⟨fiber, present, _⟩ := state.property.2
          simp [put, present])⟩
  else none

theorem blocked_call : allocate blockedInput = none := by
  simp [allocate, blockedInput, allocation_blocked]
theorem clear_call : ∃ result, allocate clearInput = some result := by
  simp [allocate, clearInput, allocation_enabled]

/-- The problem persists within the accepted actor/component comparison
domain: definedness itself distinguishes two table-equivalent inputs. -/
theorem allocation_not_respecting : ¬ PartialInverseObservation.MapRelated
    (Observed observation (fun _ => True)) allocate allocate := by
  intro respects
  have related := respects blockedInput clearInput inputs_related
  obtain ⟨result, called⟩ := clear_call
  simp [blocked_call, called, Iterators.OptionRel] at related

theorem native_landing : Land program 0 true cleared
    (put cleared 2 (fresh child (some 0))) (.retire 2) none :=
  .instantiate cleared 0 true child 2 rfl allocation_enabled

end Cordis.Repairs.AllocationBoundary
