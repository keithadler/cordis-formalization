import Cordis.RenamingLiteral
import Cordis.Orchestration
import Cordis.GuardObservations

/-! A full empty-origin history with a terminal instantiation and its real
captured child-retirement inverse. Under the displayed index/parent/view-only
renaming, L-Unload retires the old atom, leaving the renamed child live. The
expected renamed endpoint retires the renamed atom. The discrepancy is a Bool
control field, so Definition58 Eq54 also distinguishes the endpoints.

All component witnesses below are global Definition37 witnesses on actual
finite rooted registry states (Gamma), with Definition51's exact projection.
There is no child-sensitive continuation or fixed-store approximation. -/
namespace Cordis.RenamingLiteralExamples
noncomputable section
open Calculus Stages Effects Iterators RenamingLiteral

def rootName : Name := 0
def childName : Name := 1
def replacementName : Name := 2
def swap (name : Name) : Name :=
  if name = childName then replacementName else if name = replacementName then childName else name

theorem swap_involution (name : Name) : swap (swap name) = name := by
  by_cases child : name = childName
  · subst name; rfl
  · by_cases replacement : name = replacementName
    · subst name; rfl
    · simp [swap, child, replacement]

def permutation : Renaming.Permutation Name := ⟨swap, swap, swap_involution, swap_involution⟩
def emptyView : View Name Empty := fun key => nomatch key
def childComponent : Component Empty Code := ⟨(fun _ => false), (fun _ => false), false⟩
def rootComponent : Component Empty Code := ⟨(fun _ => false), (fun _ => false), true⟩
def program (code : Code) : Instruction Name Empty Unit Code Empty :=
  ⟨if code then .instantiate childComponent else .unit, fun _ => none⟩

def r0 : R := fun _ => none
def r1 : R := put r0 rootName (fresh rootComponent none : F)
def r2 : R := mark r1 rootName (.reloading true [] emptyView)
def middle : R := put r2 childName (fresh childComponent (some rootName))
def r3 : R := mark middle rootName (.active [.retire childName] emptyView)
def r4 : R := Calculus.retire r3 rootName
def r5 : R := mark r4 rootName (.unloading [.retire childName] emptyView)
def r6 : R := mark (discharge Stages.undo [.retire childName] r5) rootName .inactive

theorem no_relied (state : R) (name : Name) : ¬ Relied state name := by
  rintro ⟨consumer, _, dependency⟩
  cases present : state consumer with
  | none => simp [present] at dependency
  | some entry =>
    cases committed : entry.phase.committed with
    | none => simp [present, committed] at dependency
    | some view =>
      have witness : ∃ key : Empty, entry.component.requires key ∧ view key = name := by
        simpa [present, committed] using dependency
      obtain ⟨key, _⟩ := witness
      exact nomatch key

theorem insert_step : Orchestration.Step program r0 r1 :=
  .insert r0 rootName rootComponent ⟨rfl, by simp, by intro _ key; exact nomatch key⟩
theorem begin_step : Orchestration.Step program r1 r2 :=
  .begin r1 rootName (fresh rootComponent none : F) emptyView rfl rfl (by change some _ ≠ none; simp)
    ⟨rfl, by intro key; exact nomatch key⟩
theorem birth_ready : Insertable r2 childName childComponent (some rootName) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro parent same
    cases same
    simp [r2, r1, mark, Calculus.modify, put]
  · intro _ key
    exact nomatch key

theorem actual_birth : Land program rootName true r2 middle (.retire childName) none :=
  .instantiate r2 rootName true childComponent childName rfl birth_ready

theorem finish_step : Orchestration.Step program r2 r3 :=
  .finish r2 middle rootName { (fresh rootComponent none : F) with phase := .reloading true [] emptyView }
    true [] emptyView (.retire childName) rfl rfl
    ⟨rfl, by intro key; exact nomatch key⟩ actual_birth

theorem retire_step : Orchestration.Step program r3 r4 := .retire r3 rootName (by
  simp [r3, middle, r2, r1, mark, Calculus.modify, put, rootName, childName])
theorem leave_step : Orchestration.Step program r4 r5 :=
  .leave r4 rootName
    { (fresh rootComponent none : F) with retired := true, phase := .active [.retire childName] emptyView }
    [.retire childName] emptyView rfl rfl (by intro target; cases target.1)
theorem unload_step : Labeled.Step program .unload rootName r5 r6 :=
  .unload r5 rootName
    { (fresh rootComponent none : F) with retired := true, phase := .unloading [.retire childName] emptyView }
    [.retire childName] emptyView rfl rfl (no_relied r5 rootName)

theorem before_reachable : Orchestration.Run program r0 r5 :=
  .step (.step (.step (.step (.step (.refl _) insert_step) begin_step) finish_step) retire_step) leave_step

theorem endpoint_reachable : Orchestration.Run program r0 r6 :=
  .step before_reachable (.unload r5 rootName
    { (fresh rootComponent none : F) with retired := true, phase := .unloading [.retire childName] emptyView }
    [.retire childName] emptyView rfl rfl (no_relied r5 rootName))

theorem before_tree : Safety.Tree r5 := before_reachable.reachable_invariants.1

theorem r0_finite : FiniteDomain r0 := ⟨[], fun _ present => False.elim (present rfl)⟩
theorem r1_finite : FiniteDomain r1 := put_finite r0 rootName _ r0_finite
theorem r2_finite : FiniteDomain r2 := modify_finite r1 rootName _ r1_finite
theorem middle_finite : FiniteDomain middle := put_finite r2 childName _ r2_finite
theorem r3_finite : FiniteDomain r3 := modify_finite middle rootName _ middle_finite
theorem r4_finite : FiniteDomain r4 := modify_finite r3 rootName _ r3_finite
theorem r5_finite : FiniteDomain r5 := modify_finite r4 rootName _ r4_finite

def beforeGamma : Gamma := ⟨r5, before_tree, r5_finite⟩
def birthGamma : Gamma := ⟨r2,
  ((Orchestration.Run.step (.step (.refl _) insert_step) begin_step).reachable_invariants).1, r2_finite⟩

def renamedBefore : R := RenamingLiteral.registry permutation r5
def expectedAfter : R := RenamingLiteral.registry permutation r6
def actualAfter : R := mark (discharge Stages.undo [.retire childName] renamedBefore) rootName .inactive

theorem unload_determined {state result : R} {name : Name} {entry : F}
    {accumulator : List (Inverse Name Empty Unit)} {view : View Name Empty}
    (present : state name = some entry) (phase : entry.phase = .unloading accumulator view)
    (step : Labeled.Step program .unload name state result) :
    result = mark (discharge Stages.undo accumulator state) name .inactive := by
  cases step with
  | unload _ _ other stack committed found control _ =>
    have same : other = entry := Option.some.inj (found.symm.trans present)
    subst other
    rw [phase] at control
    cases control
    rfl

theorem endpoints_differ : actualAfter ≠ expectedAfter := by
  intro same
  have impossible := congrArg (fun state : R => (state replacementName).map Fiber.retired) same
  cases impossible

/-- The literal displayed action fails the same-rule/same-actor conclusion,
even from an actual reachable state with full global component witnesses. -/
theorem literal_unload_transport_fails :
    ¬ Labeled.Step program .unload (permutation.toFun rootName) renamedBefore expectedAfter := by
  intro step
  have determined := unload_determined
    (state := renamedBefore) (name := rootName)
    (entry := { (fresh rootComponent none : F) with retired := true, phase := .unloading [.retire childName] (Renaming.view permutation emptyView) }) rfl rfl step
  exact endpoints_differ determined.symm

end
end Cordis.RenamingLiteralExamples
