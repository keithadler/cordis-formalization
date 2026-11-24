import Cordis.Safety
import Cordis.Ordering

/-! Definition63 / Theorem64 for the actual iterator calculus. The declaration
invariant is proved from O-Insert freshness; it is never assumed as a property of
transitions. Installed-provider support uses actual captured-inverse provenance
proved by Ordering. Reachable states satisfy all four published clauses. -/
namespace Cordis.WellFormed
open Calculus Stages
universe u
variable {Name Key Value Code Error : Type u}
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
variable [DecidableEq Name] [DecidableEq Key]
set_option linter.unusedSectionVars false

def Disjoint (r : R) : Prop :=
  ∀ a b fa fb, r a = some fa → r b = some fb → a ≠ b →
    ∀ k, ¬ (fa.component.provides k = true ∧ fb.component.provides k = true)

def DeclarationOrigins (r s : R) : Prop :=
  ∀ n f, s n = some f → ∃ old, r n = some old ∧ old.component = f.component

theorem disjoint_empty : Disjoint (fun _ => none : R) := by
  intro a b fa fb present
  contradiction

theorem disjoint_of_origins {r s : R} (origins : DeclarationOrigins r s)
    (old : Disjoint r) : Disjoint s := by
  intro a b fa fb ha hb ne k hp
  obtain ⟨oa, hoa, ca⟩ := origins a fa ha
  obtain ⟨ob, hob, cb⟩ := origins b fb hb
  exact old a b oa ob hoa hob ne k (by simpa [ca, cb] using hp)

theorem modify_origins (r : R) (name : Name) (change : F → F)
    (unchanged : ∀ f, (change f).component = f.component) :
    DeclarationOrigins r (Calculus.modify r name change) := by
  intro n f present
  by_cases same : n = name
  · subst n
    cases old : r name with
    | none => simp [Calculus.modify, old] at present
    | some entry =>
      have eq : change entry = f := Option.some.inj (by simpa [Calculus.modify, old] using present)
      exact ⟨entry, rfl, by rw [← eq, unchanged]⟩
  · exact ⟨f, by simpa [Calculus.modify, same] using present, rfl⟩

theorem modify_disjoint (r : R) (name : Name) (change : F → F)
    (unchanged : ∀ f, (change f).component = f.component) (old : Disjoint r) :
    Disjoint (Calculus.modify r name change) :=
  disjoint_of_origins (modify_origins r name change unchanged) old

theorem erase_disjoint (r : R) (name : Name) (old : Disjoint r) :
    Disjoint (erase r name) := by
  apply disjoint_of_origins ?_ old
  intro n f present
  by_cases same : n = name
  · simp [erase, same] at present
  · exact ⟨f, by simpa [erase, same] using present, rfl⟩

theorem put_disjoint (r : R) (name : Name) (freshFiber : F) (old : Disjoint r)
    (separate : ∀ other entry, r other = some entry →
      ∀ k, ¬ (freshFiber.component.provides k = true ∧ entry.component.provides k = true)) :
    Disjoint (put r name freshFiber) := by
  intro a b fa fb ha hb ne k hp
  by_cases an : a = name
  · subst a
    have bn : b ≠ name := Ne.symm ne
    have ca : freshFiber = fa := Option.some.inj (by simpa [put] using ha)
    have ob : r b = some fb := by simpa [put, bn] using hb
    subst fa
    exact separate b fb ob k hp
  · by_cases bn : b = name
    · subst b
      have cb : freshFiber = fb := Option.some.inj (by simpa [put] using hb)
      have oa : r a = some fa := by simpa [put, an] using ha
      subst fb
      exact separate a fa oa k ⟨hp.2, hp.1⟩
    · exact old a b fa fb (by simpa [put, an] using ha)
        (by simpa [put, bn] using hb) ne k hp

theorem insert_disjoint (r : R) (name : Name) (component : Component Key Code)
    (parent : Option Name) (ready : Insertable r name component parent) (old : Disjoint r) :
    Disjoint (put r name (fresh component parent)) := by
  apply put_disjoint r name _ old
  intro other entry present k hp
  have separated := ready.2.2 other k
  simp only [present] at separated
  exact separated hp.1 hp.2

theorem mark_disjoint (r : R) (name : Name) (phase) (old : Disjoint r) :
    Disjoint (mark r name phase) := modify_disjoint r name _ (fun _ => rfl) old

theorem write_disjoint (r : R) (name : Name) (key : Key) (value : Option Value)
    (old : Disjoint r) : Disjoint (write r name key value) :=
  modify_disjoint r name _ (fun _ => rfl) old

theorem retire_disjoint (r : R) (name : Name) (old : Disjoint r) :
    Disjoint (Calculus.retire r name) := modify_disjoint r name _ (fun _ => rfl) old

theorem undo_disjoint (r : R) (inverse : Inverse Name Key Value) (old : Disjoint r) :
    Disjoint (Stages.undo inverse r) := by
  cases inverse with
  | unit => exact old
  | restrict name key => exact write_disjoint r name key none old
  | operate name key inverse => exact modify_disjoint r name _ (fun _ => rfl) old
  | retire name => exact retire_disjoint r name old

theorem discharge_disjoint (r : R) (accumulator : List (Inverse Name Key Value))
    (old : Disjoint r) : Disjoint (discharge Stages.undo accumulator r) := by
  induction accumulator generalizing r with
  | nil => exact old
  | cons inverse rest ih => exact ih _ (undo_disjoint r inverse old)

theorem land_disjoint (program : Code → Instruction Name Key Value Code Error)
    {n : Name} {c : Code} {r s : R} {inverse : Inverse Name Key Value} {next : Option Code}
    (h : Land program n c r s inverse next) (old : Disjoint r) : Disjoint s := by
  cases h with
  | unit => exact old
  | provide r n c fiber key value _ _ _ _ => exact write_disjoint r n key (some value) old
  | operate r n c key run owner before after inverse result _ _ _ =>
    exact write_disjoint r owner key (some after) old
  | instantiate r n c component child _ ready =>
    exact insert_disjoint r child component (some n) ready old

theorem step_disjoint (program : Code → Instruction Name Key Value Code Error)
    {r s : R} (h : Calculus.Step (Land program) Stages.undo r s) (old : Disjoint r) :
    Disjoint s := by
  cases h with
  | insert name component parent ready => exact insert_disjoint r name component parent ready old
  | retire name _ => exact retire_disjoint r name old
  | remove name _ => exact erase_disjoint r name old
  | begin name fiber view _ _ _ _ => exact mark_disjoint r name _ old
  | iter s name fiber code accumulator view inverse next _ _ _ land =>
    exact mark_disjoint s name _ (land_disjoint program land old)
  | finish s name fiber code accumulator view inverse _ _ _ land =>
    exact mark_disjoint s name _ (land_disjoint program land old)
  | divert s name fiber code accumulator view tail _ _ _ alternative =>
    rcases alternative with ⟨same, _⟩ | ⟨inverse, next, land, _⟩
    · subst s; exact mark_disjoint r name _ old
    · exact mark_disjoint s name _ (land_disjoint program land old)
  | leave name fiber accumulator view _ _ _ => exact mark_disjoint r name _ old
  | unload name fiber accumulator view _ _ _ =>
    exact mark_disjoint _ name _ (discharge_disjoint r accumulator old)

/-- Definition63. Totality on declared keys is represented by the View function;
clauses3 and4 jointly demand an existing installed provider for every required key. -/
def WellFormed (r : R) : Prop :=
  Safety.ParentClosed r ∧ Disjoint r ∧
  ∀ n f view k, r n = some f → f.phase.committed = some view →
    f.component.requires k = true →
    ∃ provider, r (view k) = some provider ∧ provider.phase.committed ≠ none

theorem wellFormed_of_invariants (r : R) (parents : Safety.ParentClosed r)
    (disjoint : Disjoint r) (supported : Ordering.Supported r) : WellFormed r := by
  refine ⟨parents, disjoint, ?_⟩
  intro n f view k present committed required
  obtain ⟨_, provider, hp, retained, _⟩ :=
    supported n (view k) k ⟨f, view, present, required, committed, rfl⟩
  refine ⟨provider, hp, ?_⟩
  cases ph : provider.phase <;> simp [Ordering.Retained, ph] at retained <;>
    simp [Phase.committed]

inductive Run (program : Code → Instruction Name Key Value Code Error) : R → R → Prop
  | refl (r) : Run program r r
  | step {r s t} : Run program r s → Calculus.Step (Land program) Stages.undo s t → Run program r t

theorem run_invariants (program : Code → Instruction Name Key Value Code Error)
    {r s : R} (h : Run program r s) (parents : Safety.ParentClosed r)
    (disjoint : Disjoint r) (supported : Ordering.Invariant r) :
    Safety.ParentClosed s ∧ Disjoint s ∧ Ordering.Invariant s := by
  induction h with
  | refl => exact ⟨parents, disjoint, supported⟩
  | step _ transition ih =>
    exact ⟨Safety.step_parentClosed program transition ih.1,
      step_disjoint program transition ih.2.1, Ordering.step_invariant program transition ih.2.2⟩

end Cordis.WellFormed
