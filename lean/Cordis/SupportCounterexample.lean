import Cordis.Orchestration

/-!
A primitive-calculus counterexample to the Lemma75 statement, including
Definition74's external-root provenance. Global Definition48 component witnesses
are not certified here; this is not an unconditional original-paper refutation.
No name is reused. A removed provider's key is later reassigned, while a retired
child remains in the registry. The relation (61) includes retired names.
-/
namespace Cordis.SupportCounterexample
open Calculus Stages

inductive Name where | old | parent | child | replacement deriving DecidableEq
inductive Code where | provideX | provideY | spawn | unit deriving DecidableEq
open Name Code
abbrev R := Registry Name Bool Unit Code (Inverse Name Bool Unit) Empty
abbrev F := Fiber Name Bool Unit Code (Inverse Name Bool Unit) Empty

def oldComponent : Component Bool Code := ⟨fun _ => false, fun k => !k, .provideX⟩
def parentComponent : Component Bool Code := ⟨fun k => !k, fun _ => false, .spawn⟩
def childComponent : Component Bool Code := ⟨fun _ => false, fun k => k, .provideY⟩
def replacementComponent : Component Bool Code := ⟨fun k => k, fun k => !k, .provideX⟩
def program : Code → Instruction Name Bool Unit Code Empty
  | .provideX => { action := .provide false (), next := fun _ => none }
  | .provideY => { action := .provide true (), next := fun _ => none }
  | .spawn => { action := .instantiate childComponent, next := fun _ => none }
  | .unit => { action := .unit, next := fun _ => none }
def view : View Name Bool := fun _ => .old

def s0 : R := fun _ => none
def s1 : R := put s0 .old (fresh oldComponent none)
def s2 : R := mark s1 .old (.reloading .provideX [] view)
def s3 : R := mark (write s2 .old false (some ())) .old (.active [.restrict .old false] view)
def s4 : R := put s3 .parent (fresh parentComponent none)
def s5 : R := mark s4 .parent (.reloading .spawn [] view)
def s6 : R := mark (put s5 .child (fresh childComponent (some .parent))) .parent
  (.active [.retire .child] view)
def s7 : R := Calculus.retire s6 .old
def s8 : R := mark s7 .old (.unloading [.restrict .old false] view)
def s9 : R := mark s8 .parent (.unloading [.retire .child] view)
def s10 : R := mark (Calculus.retire s9 .child) .parent .inactive
def s11 : R := mark (write s10 .old false none) .old .inactive
def s12 : R := erase s11 .old
def s13 : R := put s12 .replacement (fresh replacementComponent none)

abbrev Transition := Orchestration.Step program

-- The same finite simplifier expands only closed fixture data, never an invariant.
macro "fixture" : tactic => `(tactic| simp_all [s13, s12, s11, s10, s9, s8, s7,
  s6, s5, s4, s3, s2, s1, s0, mark, Calculus.modify, Calculus.retire, put, erase,
  write, fresh, oldComponent, parentComponent, childComponent, replacementComponent,
  view, Phase.available, Phase.committed])

theorem step1 : Transition s0 s1 := .insert _ _ _ (by simp [Insertable, s0])
theorem step2 : Transition s1 s2 :=
  .begin _ .old (fresh oldComponent none) view rfl rfl
    (by simp [ErrorFree, s1, put, fresh])
    (by simp [Target, s1, s0, put, fresh, oldComponent])

theorem step3 : Transition s2 s3 := by
  apply Orchestration.Step.finish s2 (write s2 .old false (some ())) .old
    { (fresh oldComponent none : F) with phase := .reloading .provideX [] view }
    .provideX [] view (.restrict .old false) rfl rfl
  · simp [Target]; fixture
  · exact .provide s2 .old .provideX
      { (fresh oldComponent none : F) with phase := .reloading .provideX [] view }
      false () rfl rfl rfl rfl

theorem step4 : Transition s3 s4 := by
  apply Orchestration.Step.insert
  refine ⟨rfl, ?_, ?_⟩
  · intro n hn; cases hn
  · intro n k; cases n <;> fixture

theorem step5 : Transition s4 s5 :=
  .begin _ .parent (fresh parentComponent none) view rfl rfl
    (by simp [ErrorFree]; fixture)
    (by simp [Target]; fixture)

theorem child_insertable : Insertable s5 .child childComponent (some .parent) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro n hn; cases hn; fixture
  · intro n k; cases n <;> cases k <;> fixture

theorem step6 : Transition s5 s6 := by
  apply Orchestration.Step.finish s5 (put s5 .child (fresh childComponent (some .parent))) .parent
    { (fresh parentComponent none : F) with phase := .reloading .spawn [] view }
    .spawn [] view (.retire .child) rfl rfl
  · simp [Target]; fixture
  · exact .instantiate s5 .parent .spawn childComponent .child rfl child_insertable

theorem step7 : Transition s6 s7 := .retire s6 .old (by fixture)

theorem step8 : Transition s7 s8 :=
  .leave _ .old
    { (fresh oldComponent none : F) with
      retired := true
      table := (fun k => if k = false then some () else none)
      phase := .active [.restrict .old false] view }
    [.restrict .old false] view rfl rfl (retirement_has_no_target s6 .old view)

theorem step9 : Transition s8 s9 := by
  apply Orchestration.Step.leave s8 .parent
    { (fresh parentComponent none : F) with phase := .active [.retire .child] view }
    [.retire .child] view rfl rfl
  intro ht
  have bad := ht.2 false rfl
  fixture

theorem step10 : Transition s9 s10 := by
  apply Orchestration.Step.unload s9 .parent
    { (fresh parentComponent none : F) with phase := .unloading [.retire .child] view }
    [.retire .child] view rfl rfl
  intro h
  obtain ⟨n, ne, f⟩ := h
  cases n <;> fixture

theorem step11 : Transition s10 s11 := by
  apply Orchestration.Step.unload s10 .old
    { (fresh oldComponent none : F) with
      retired := true
      table := (fun k => if k = false then some () else none)
      phase := .unloading [.restrict .old false] view }
    [.restrict .old false] view rfl rfl
  intro h
  obtain ⟨n, ne, f⟩ := h
  cases n <;> fixture

theorem step12 : Transition s11 s12 := by
  apply Orchestration.Step.remove
  simp only [Removable]
  change true = true ∧ Phase.inactive = (Phase.inactive : Phase Name Bool Code (Inverse Name Bool Unit)) ∧ _
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro k; cases k <;> rfl
  · intro n; cases n <;> fixture

theorem step13 : Transition s12 s13 := by
  apply Orchestration.Step.insert
  refine ⟨rfl, ?_, ?_⟩
  · intro n hn; cases hn
  · intro n k; cases n <;> cases k <;> fixture

theorem reachable : Orchestration.Run program s0 s13 :=
  .step (.step (.step (.step (.step (.step (.step (.step (.step (.step (.step (.step
    (.step (.refl _) step1) step2) step3) step4) step5) step6) step7) step8) step9)
    step10) step11) step12) step13

def Precedes (r : R) (a b : Name) : Prop :=
  ∃ fa fb k, r a = some fa ∧ r b = some fb ∧
    fa.component.provides k = true ∧ fb.component.requires k = true

def Supports (r : R) (a b : Name) : Prop :=
  Precedes r a b ∨ ∃ fb, r b = some fb ∧ fb.parent = some a

def rank : Name → Nat | .child => 0 | .old => 0 | .replacement => 1 | .parent => 2

theorem precedence_iff (a b : Name) : Precedes s13 a b ↔
    (a = .child ∧ b = .replacement) ∨ (a = .replacement ∧ b = .parent) := by
  cases a <;> cases b <;> simp [Precedes] <;> fixture

theorem precedence_ranked (a b : Name) (h : Precedes s13 a b) : rank a < rank b := by
  rcases (precedence_iff a b).mp h with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
    subst a <;> subst b <;> decide

theorem precedence_wellFounded : WellFounded (Precedes s13) :=
  Subrelation.wf (fun {_ _} h => precedence_ranked _ _ h) (InvImage.wf rank Nat.lt_wfRel.wf)

def states : List R := [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13]

/-- Even the union of dependency edges over the entire history is acyclic.
This is stronger than checking only Definition72's current-registry relation. -/
theorem all_prefix_edges_ranked (r : R) (hr : r ∈ states) (a b : Name)
    (h : Precedes r a b) : rank a < rank b := by
  simp only [states, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    cases a <;> cases b <;> simp_all [Precedes, rank] <;> fixture

/-- There are four names, each inserted at most once in the displayed trace. -/
def EverPrecedes (a b : Name) : Prop := ∃ r ∈ states, Precedes r a b

theorem entire_history_acyclic : WellFounded EverPrecedes := by
  apply Subrelation.wf (r := fun a b => rank a < rank b) ?_ (InvImage.wf rank Nat.lt_wfRel.wf)
  intro a b h
  obtain ⟨r, hr, edge⟩ := h
  exact all_prefix_edges_ranked r hr a b edge

theorem parent_child : Supports s13 .parent .child :=
  Or.inr ⟨{ (fresh childComponent (some .parent) : F) with retired := true }, rfl, rfl⟩

theorem child_replacement : Supports s13 .child .replacement := Or.inl
  ⟨{ (fresh childComponent (some .parent) : F) with retired := true },
    fresh replacementComponent none, true, rfl, rfl, rfl, rfl⟩

theorem replacement_parent : Supports s13 .replacement .parent := Or.inl
  ⟨fresh replacementComponent none, fresh parentComponent none, false, rfl, rfl, rfl, rfl⟩

private theorem no_three_cycle {α : Type} {rel : α → α → Prop} {a : α}
    (h : Acc rel a) : ∀ b c, rel a b → rel b c → rel c a → False := by
  induction h with
  | intro a _ ih =>
    intro b c hab hbc hca
    exact ih c hca a b hca hab hbc

/-- Lemma75's well-foundedness conclusion fails under the explicit provenance
convention too: all13 steps are admitted by Orchestration.Step, names are distinct,
and precedence is acyclic; the support cycle includes a retired child. -/
theorem lemma75_with_provenance_counterexample :
    Orchestration.Run program s0 s13 ∧ WellFounded (Precedes s13) ∧
    WellFounded EverPrecedes ∧ ¬ WellFounded (Supports s13) := by
  refine ⟨reachable, precedence_wellFounded, entire_history_acyclic, ?_⟩
  intro h
  exact no_three_cycle (h.apply .parent) .child .replacement
    parent_child child_replacement replacement_parent

end Cordis.SupportCounterexample
