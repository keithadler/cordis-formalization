import Cordis.Safety

/-!
Literal countermodels to arXiv:2608.25512v1, Lemmas 62, 75 and 77.
These use the actual nine-rule calculus, including its unrestricted parent premise
for external O-Insert. They identify missing hypotheses, rather than introducing
axioms that assert the paper's conclusions. `false` is A and `true` is B.
-/
namespace Cordis.Metatheory
open Calculus Stages

abbrev R := Registry Bool Unit Unit Unit (Inverse Bool Unit Unit) Empty

def unitProgram (_ : Unit) : Instruction Bool Unit Unit Unit Empty := { action := .unit, next := fun _ => none }
abbrev Transition := Step (Land unitProgram) Stages.undo

inductive Reachable : R → Prop where
  | empty : Reachable (fun _ => none)
  | step {r s : R} : Reachable r → Transition r s → Reachable s

/-- Definition 72: a declared provision meets a declared requirement. -/
def Precedes (r : R) (a b : Bool) : Prop :=
  ∃ fa fb key, r a = some fa ∧ r b = some fb ∧
    fa.component.provides key = true ∧ fb.component.requires key = true

/-- Definition 74: provider precedence or the parent edge. -/
def Supports (r : R) (a b : Bool) : Prop :=
  Precedes r a b ∨ ∃ fb, r b = some fb ∧ fb.parent = some a

/-- The recursive equation (61), including both retirement and parent support. -/
def SupportedSet (r : R) (s : Bool → Prop) : Prop :=
  ∀ n f, r n = some f →
    (s n ↔ f.retired = false ∧
      (f.parent = none ∨ ∃ p, f.parent = some p ∧ s p) ∧
      ∀ k, f.component.requires k = true →
        ∃ m provider, r m = some provider ∧ s m ∧ provider.component.provides k = true)

def demand : Component Unit Unit := ⟨fun _ => true, fun _ => false, ()⟩
def supply : Component Unit Unit := ⟨fun _ => false, fun _ => true, ()⟩

def first : R := put (fun _ => none) false (fresh demand none)
def cyclic : R := put first true (fresh supply (some false))

theorem first_insertable : Insertable (fun _ => none : R) false demand none := by
  simp [Insertable]

theorem first_reachable : Reachable first :=
  .step .empty (.insert _ _ _ _ first_insertable)

theorem cyclic_insertable : Insertable first true supply (some false) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro p hp; cases hp; simp [first, put]
  · intro other key; cases other <;> simp [first, put, fresh, demand, supply]

theorem cyclic_reachable : Reachable cyclic :=
  .step first_reachable (.insert _ _ _ _ cyclic_insertable)

theorem cyclic_precedence_iff (a b : Bool) :
    Precedes cyclic a b ↔ a = true ∧ b = false := by
  cases a <;> cases b <;> simp [Precedes, cyclic, first, put, fresh, demand, supply]

theorem cyclic_precedence_wellFounded : WellFounded (Precedes cyclic) := by
  constructor
  intro b
  cases b
  · constructor
    intro a ha
    have h := (cyclic_precedence_iff a false).mp ha
    have eq := h.1
    subst a
    constructor
    intro a ha
    have h := (cyclic_precedence_iff a true).mp ha
    cases h.2
  · constructor
    intro a ha
    have h := (cyclic_precedence_iff a true).mp ha
    cases h.2

theorem cyclic_parent_edge : Supports cyclic false true := by
  right
  exact ⟨fresh supply (some false), rfl, rfl⟩

theorem cyclic_provider_edge : Supports cyclic true false := by
  left
  exact (cyclic_precedence_iff true false).mpr ⟨rfl, rfl⟩

private theorem no_two_cycle {α : Type} {rel : α → α → Prop} {a : α}
    (ha : Acc rel a) : ∀ b, rel a b → rel b a → False := by
  induction ha with
  | intro a _ ih =>
    intro b hab hba
    exact ih b hba a hba hab

/-- Refutes Lemma 75: acyclic precedence does not make combined support well-founded. -/
theorem lemma75_counterexample : Reachable cyclic ∧
    WellFounded (Precedes cyclic) ∧ ¬ WellFounded (Supports cyclic) := by
  refine ⟨cyclic_reachable, cyclic_precedence_wellFounded, ?_⟩
  intro h
  exact no_two_cycle (h.apply false) true cyclic_parent_edge cyclic_provider_edge

/-- Both the empty and full sets solve Definition 74 on the same reachable state:
Lemma 75's uniqueness conclusion fails as well as its well-foundedness conclusion. -/
theorem cyclic_support_empty : SupportedSet cyclic (fun _ => False) := by
  intro n f hf
  cases n <;> simp [cyclic, first, put] at hf <;> subst f <;>
    simp [fresh, demand, supply]

theorem cyclic_support_full : SupportedSet cyclic (fun _ => True) := by
  intro n f hf
  cases n <;> simp [cyclic, first, put] at hf <;> subst f
  · constructor
    · intro _
      refine ⟨rfl, Or.inl rfl, ?_⟩
      intro k _
      exact ⟨true, fresh supply (some false), rfl, trivial, rfl⟩
    · intro _; trivial
  · simp [fresh, supply]

/-- A retired empty root can still be used as O-Insert's parent. -/
def vestigial : R := retire first false

theorem vestigial_removable : Removable vestigial false := by
  simp only [Removable, vestigial, retire, Calculus.modify, first, put, fresh]
  simp

/-! Lemma79 has a separate defect even when external insertions are restricted
to root: it deletes O-Retire and, literally, does not delete the opening Begin. -/

end Cordis.Metatheory
