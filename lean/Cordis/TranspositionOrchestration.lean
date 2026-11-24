import Cordis.TranspositionRemoval
import Cordis.Orchestration

/-! Lemma78(2) for the actual provenance-qualified orchestration rules. The
root-only insertion restriction is Definition74's external-root convention,
already used by `Orchestration.Step`. The endpoint equality here is literal;
the observational independence issue of Lemma78(1) is not used or hidden. -/
namespace Cordis.Transposition
open Calculus Stages Labeled
universe u
variable {Name Key Value Code Error : Type u}
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
variable [DecidableEq Name] [DecidableEq Key]
set_option linter.unusedSectionVars false

inductive ExternalStep : Rule → Name → R → R → Prop
  | insert (r name component) : Insertable r name component none →
      ExternalStep .insert name r (put r name (fresh component none))
  | retire (r name) : r name ≠ none → ExternalStep .retire name r (Calculus.retire r name)
  | remove (r name) : Removable r name → ExternalStep .remove name r (erase r name)

/-- The complete second clause of Lemma78. Neither swapped applicability nor
commuting composite maps are premises. Both swapped labelled transitions and
their common literal endpoint are constructed from the original steps. -/
theorem activation_orchestration_diamond (program : Code → Instruction Name Key Value Code Error)
    {activationRule orchestrationRule : Rule} {actor name : Name} {r s t : R}
    (activation : Labeled.Step program activationRule actor r s) (active : Activation activationRule)
    (external : ExternalStep orchestrationRule name s t)
    (different : actor ≠ name) (notCreated : ¬ CreatesChild program actor r s name) :
    ∃ middle, ExternalStep orchestrationRule name r middle ∧
      Labeled.Step program activationRule actor middle t := by
  cases external with
  | insert _ _ component ready =>
    obtain ⟨_, after⟩ := activation_insert_diamond program activation active name component different ready
    have allowed : Insertable r name component none := by
      cases activation with
      | begin _ _ fiber view found phase free target =>
        exact mark_root_insertable_backwards _ _ _ name component ready
      | iter _ middle _ fiber code acc view inverse next found phase target land =>
        exact land_root_insertable_backwards program land name component
          (mark_root_insertable_backwards _ _ _ name component ready)
      | finish _ middle _ fiber code acc view inverse found phase target land =>
        exact land_root_insertable_backwards program land name component
          (mark_root_insertable_backwards _ _ _ name component ready)
      | _ => simp [Activation] at active
    exact ⟨_, .insert r name component allowed, after⟩
  | retire _ _ present =>
    have earlier : r name ≠ none := by
      intro absent
      exact notCreated ((activation_creates_iff program activation active name different).mpr ⟨absent, present⟩)
    exact ⟨_, .retire r name earlier,
      activation_after_retirement program activation active name different earlier⟩
  | remove _ _ ready =>
    obtain ⟨before, after⟩ := activation_remove_diamond program activation active name different ready
    cases before with
    | remove _ _ allowed => exact ⟨_, .remove r name allowed, after⟩

end Cordis.Transposition
