import Cordis.WellFormed

/-! Lemma59(5): all actual rules preserve existing declarations and parentage;
retirement is monotone. The proof covers nested instantiation and actual inverse
application, rather than assuming a frame condition on arbitrary landing maps. -/
namespace Cordis.Frame
open Calculus Stages
universe u
variable {Name Key Value Code Error : Type u}
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
variable [DecidableEq Name] [DecidableEq Key]
set_option linter.unusedSectionVars false

def Stable (r s : R) : Prop :=
  ∀ n f g, r n = some f → s n = some g →
    f.component = g.component ∧ f.parent = g.parent ∧ (f.retired = true → g.retired = true)

theorem stable_refl (r : R) : Stable r r := by
  intro n f g hf hg
  have eq := Option.some.inj (hf.symm.trans hg)
  subst g
  exact ⟨rfl, rfl, id⟩

theorem stable_compose {r s t : R} (first : Stable r s) (second : Stable s t)
    (origin : WellFormed.DeclarationOrigins s t) : Stable r t := by
  intro n f g hf hg
  obtain ⟨middle, hm, _⟩ := origin n g hg
  have h₁ := first n f middle hf hm
  have h₂ := second n middle g hm hg
  exact ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1, h₂.2.2 ∘ h₁.2.2⟩

theorem modify_stable (r : R) (name : Name) (change : F → F)
    (component : ∀ f, (change f).component = f.component)
    (parent : ∀ f, (change f).parent = f.parent)
    (retired : ∀ f, f.retired = true → (change f).retired = true) :
    Stable r (Calculus.modify r name change) := by
  intro n f g hf hg
  by_cases same : n = name
  · subst n
    have eq : change f = g := Option.some.inj (by simpa [Calculus.modify, hf] using hg)
    subst g
    exact ⟨(component f).symm, (parent f).symm, retired f⟩
  · have eq : f = g := Option.some.inj (by simpa [Calculus.modify, same, hf] using hg)
    subst g
    exact ⟨rfl, rfl, id⟩

theorem put_stable (r : R) (name : Name) (fiber : F) (absent : r name = none) :
    Stable r (put r name fiber) := by
  intro n f g hf hg
  have different : n ≠ name := by intro eq; subst n; simp [absent] at hf
  have eq : f = g := Option.some.inj (by simpa [put, different, hf] using hg)
  subst g
  exact ⟨rfl, rfl, id⟩

theorem erase_stable (r : R) (name : Name) : Stable r (erase r name) := by
  intro n f g hf hg
  have different : n ≠ name := by intro eq; subst n; simp [erase] at hg
  have eq : f = g := Option.some.inj (by simpa [erase, different, hf] using hg)
  subst g
  exact ⟨rfl, rfl, id⟩

theorem mark_stable (r : R) (name : Name) (phase) : Stable r (mark r name phase) :=
  modify_stable r name _ (fun _ => rfl) (fun _ => rfl) (fun _ h => h)

theorem mark_after {r s : R} (first : Stable r s) (name : Name) (phase) :
    Stable r (mark s name phase) :=
  stable_compose first (mark_stable s name phase)
    (WellFormed.modify_origins s name _ (fun _ => rfl))

theorem write_stable (r : R) (name : Name) (key : Key) (value : Option Value) :
    Stable r (write r name key value) :=
  modify_stable r name _ (fun _ => rfl) (fun _ => rfl) (fun _ h => h)

theorem retire_stable (r : R) (name : Name) : Stable r (Calculus.retire r name) :=
  modify_stable r name _ (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl)

theorem undo_stable (r : R) (inverse : Inverse Name Key Value) :
    Stable r (Stages.undo inverse r) := by
  cases inverse with
  | unit => exact stable_refl r
  | restrict n k => exact write_stable r n k none
  | operate n k inv =>
    exact modify_stable r n _ (fun _ => rfl) (fun _ => rfl) (fun _ h => h)
  | retire n => exact retire_stable r n

theorem undo_origins (r : R) (inverse : Inverse Name Key Value) :
    WellFormed.DeclarationOrigins r (Stages.undo inverse r) := by
  cases inverse with
  | unit => intro n f hf; exact ⟨f, hf, rfl⟩
  | restrict n k => exact WellFormed.modify_origins r n _ (fun _ => rfl)
  | operate n k inv => exact WellFormed.modify_origins r n _ (fun _ => rfl)
  | retire n => exact WellFormed.modify_origins r n _ (fun _ => rfl)

theorem discharge_origins (r : R) (accumulator : List (Inverse Name Key Value)) :
    WellFormed.DeclarationOrigins r (discharge Stages.undo accumulator r) := by
  induction accumulator generalizing r with
  | nil => intro n f hf; exact ⟨f, hf, rfl⟩
  | cons inverse rest ih =>
    intro n f hf
    obtain ⟨middle, hm, cm⟩ := ih (Stages.undo inverse r) n f hf
    obtain ⟨old, ho, co⟩ := undo_origins r inverse n middle hm
    exact ⟨old, ho, co.trans cm⟩

theorem discharge_stable (r : R) (accumulator : List (Inverse Name Key Value)) :
    Stable r (discharge Stages.undo accumulator r) := by
  induction accumulator generalizing r with
  | nil => exact stable_refl r
  | cons inverse rest ih =>
    exact stable_compose (undo_stable r inverse) (ih (Stages.undo inverse r))
      (discharge_origins (Stages.undo inverse r) rest)

theorem land_stable (program : Code → Instruction Name Key Value Code Error)
    {n : Name} {c : Code} {r s : R} {inverse : Inverse Name Key Value} {next : Option Code}
    (h : Land program n c r s inverse next) : Stable r s := by
  cases h with
  | unit => exact stable_refl _
  | provide r n c fiber key value _ _ _ _ => exact write_stable r n key (some value)
  | operate r n c key run owner before after inverse result _ _ _ =>
    exact write_stable r owner key (some after)
  | instantiate r n c component child _ ready => exact put_stable r child _ ready.1

theorem step_stable (program : Code → Instruction Name Key Value Code Error)
    {r s : R} (h : Calculus.Step (Land program) Stages.undo r s) : Stable r s := by
  cases h with
  | insert name component parent ready => exact put_stable r name _ ready.1
  | retire name _ => exact retire_stable r name
  | remove name _ => exact erase_stable r name
  | begin name fiber view _ _ _ _ => exact mark_stable r name _
  | iter s name fiber code accumulator view inverse next _ _ _ land =>
    exact mark_after (land_stable program land) name _
  | finish s name fiber code accumulator view inverse _ _ _ land =>
    exact mark_after (land_stable program land) name _
  | divert s name fiber code accumulator view tail _ _ _ alternative =>
    rcases alternative with ⟨same, _⟩ | ⟨inverse, next, land, _⟩
    · subst s; exact mark_stable r name _
    · exact mark_after (land_stable program land) name _
  | leave name fiber accumulator view _ _ _ => exact mark_stable r name _
  | unload name fiber accumulator view _ _ _ => exact mark_after (discharge_stable r accumulator) name _

end Cordis.Frame
