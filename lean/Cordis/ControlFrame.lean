import Cordis.Frame
import Cordis.Labeled

/-! Lemma59(2,4): committed views appear exactly through L-Begin and disappear
exactly through L-Unload. The proof inspects all nine rules and every actual
stage/inverse, including newly instantiated entries rather than only entries
already present. -/
namespace Cordis.ControlFrame
open Calculus Stages
universe u
variable {Name Key Value Code Error : Type u}
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
variable [DecidableEq Name] [DecidableEq Key]
set_option linter.unusedSectionVars false

def viewAt (r : R) (n : Name) : Option (View Name Key) :=
  (r n).bind fun f => f.phase.committed

theorem modify_views (r : R) (actor : Name) (change : F → F)
    (same : ∀ f, (change f).phase.committed = f.phase.committed) :
    viewAt (Calculus.modify r actor change) = viewAt r := by
  funext n
  by_cases eq : n = actor
  · subst n
    cases h : r actor <;> simp [viewAt, Calculus.modify, h, same]
  · simp [viewAt, Calculus.modify, eq]

theorem mark_viewAt (r : R) (actor : Name) (f : F) (phase) (present : r actor = some f)
    (n : Name) : viewAt (mark r actor phase) n =
      if n = actor then phase.committed else viewAt r n := by
  by_cases eq : n = actor
  · subst n; simp [viewAt, mark, Calculus.modify, present]
  · simp [viewAt, mark, Calculus.modify, eq]

theorem mark_same_views (r : R) (actor : Name) (f : F) (phase)
    (present : r actor = some f) (same : phase.committed = f.phase.committed) :
    viewAt (mark r actor phase) = viewAt r := by
  funext n
  rw [mark_viewAt r actor f phase present]
  by_cases eq : n = actor
  · subst n; simp [viewAt, present, same]
  · simp [eq]

theorem insert_views (r : R) (actor : Name) (component : Component Key Code) (parent : Option Name)
    (absent : r actor = none) : viewAt (put r actor (fresh component parent)) = viewAt r := by
  funext n
  by_cases eq : n = actor
  · subst n; simp [viewAt, put, fresh, Phase.committed, absent]
  · simp [viewAt, put, eq]

theorem remove_views (r : R) (actor : Name) (ready : Removable r actor) :
    viewAt (erase r actor) = viewAt r := by
  cases present : r actor with
  | none => simp [Removable, present] at ready
  | some f =>
    have inactive := (show f.retired = true ∧ f.phase = .inactive ∧ _ from
      by simpa [Removable, present] using ready).2.1
    funext n
    by_cases eq : n = actor
    · subst n; simp [viewAt, erase, present, inactive, Phase.committed]
    · simp [viewAt, erase, eq]

theorem land_views (program : Code → Instruction Name Key Value Code Error)
    {actor : Name} {code : Code} {r s : R} {inverse : Inverse Name Key Value} {next : Option Code}
    (land : Land program actor code r s inverse next) : viewAt s = viewAt r := by
  cases land with
  | unit => rfl
  | provide => exact modify_views _ _ _ (fun _ => rfl)
  | operate => exact modify_views _ _ _ (fun _ => rfl)
  | instantiate r actor code component child _ ready =>
    exact insert_views r child component (some actor) ready.1

theorem undo_views (r : R) (inverse : Inverse Name Key Value) :
    viewAt (Stages.undo inverse r) = viewAt r := by
  cases inverse with
  | unit => rfl
  | restrict => exact modify_views _ _ _ (fun _ => rfl)
  | operate => exact modify_views _ _ _ (fun _ => rfl)
  | retire => exact modify_views _ _ _ (fun _ => rfl)

theorem discharge_views (r : R) (accumulator : List (Inverse Name Key Value)) :
    viewAt (discharge Stages.undo accumulator r) = viewAt r := by
  induction accumulator generalizing r with
  | nil => rfl
  | cons inverse rest ih =>
    exact (ih (Stages.undo inverse r)).trans (undo_views r inverse)

def BeginsAt (r s : R) (name : Name) : Prop :=
  ∃ f v, r name = some f ∧ f.phase = .inactive ∧ ErrorFree r name ∧ Target r name v ∧
    s = mark r name (.reloading f.component.entry [] v)

def UnloadsAt (r s : R) (name : Name) : Prop :=
  ∃ f a v, r name = some f ∧ f.phase = .unloading a v ∧ ¬ Relied r name ∧
    s = mark (discharge Stages.undo a r) name .inactive

/-- The committed-view observation records which actual labeled rule
opens or closes an episode. Every other rule preserves it pointwise. -/
theorem labeled_view_cases (program : Code → Instruction Name Key Value Code Error)
    {r s : R} {rule : Labeled.Rule} {actor : Name} (h : Labeled.Step program rule actor r s) :
    match rule with
    | .begin => BeginsAt r s actor
    | .unload => UnloadsAt r s actor
    | _ => viewAt s = viewAt r := by
  cases h with
  | insert _ n c p ready => exact insert_views r actor c p ready.1
  | retire _ n _ => exact modify_views r actor _ (fun _ => rfl)
  | remove _ n ready => exact remove_views r actor ready
  | begin _ n f v present inactive free target =>
    exact ⟨f, v, present, inactive, free, target, rfl⟩
  | iter _ s n f c a v i next present reloading _ land =>
    obtain ⟨g, retained, phase⟩ := Ordering.land_existing_phases program land actor f present
    exact (mark_same_views s actor g _ retained (by simp [phase, reloading, Phase.committed])).trans
      (land_views program land)
  | finish _ s n f c a v i present reloading _ land =>
    obtain ⟨g, retained, phase⟩ := Ordering.land_existing_phases program land actor f present
    exact (mark_same_views s actor g _ retained (by simp [phase, reloading, Phase.committed])).trans
      (land_views program land)
  | divert _ s n f c a v tail present reloading _ alternative =>
    rcases alternative with ⟨rfl, _⟩ | ⟨i, next, land, _⟩
    · exact mark_same_views s actor f _ present (by simp [reloading, Phase.committed])
    · obtain ⟨g, retained, phase⟩ := Ordering.land_existing_phases program land actor f present
      exact (mark_same_views s actor g _ retained (by simp [phase, reloading, Phase.committed])).trans
        (land_views program land)
  | leave _ n f a v present active _ =>
    exact mark_same_views r actor f _ present (by simp [active, Phase.committed])
  | unload _ n f a v present unloading free =>
    exact ⟨f, a, v, present, unloading, free, rfl⟩

theorem step_view_cases (program : Code → Instruction Name Key Value Code Error)
    {r s : R} (h : Calculus.Step (Land program) Stages.undo r s) :
    viewAt s = viewAt r ∨ (∃ n, BeginsAt r s n) ∨ (∃ n, UnloadsAt r s n) := by
  obtain ⟨rule, actor, native⟩ := Labeled.Step.ofCalculus h
  have frame := labeled_view_cases program native
  cases rule with
  | begin => exact .inr (.inl ⟨actor, frame⟩)
  | unload => exact .inr (.inr ⟨actor, frame⟩)
  | _ => exact .inl frame

theorem viewAt_present_iff (r : R) (n : Name) : viewAt r n ≠ none ↔
    ∃ f, r n = some f ∧ f.phase ≠ .inactive := by
  cases present : r n with
  | none => simp [viewAt, present]
  | some f => cases phase : f.phase <;> simp [viewAt, present, phase, Phase.committed]

end Cordis.ControlFrame
