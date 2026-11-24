import Cordis.Stages

/-! Exact semantic heads for the ordinary paper calculus. The success tag is
retained: missing bindings, illegal provision/instantiation and raising callbacks
produce no ordinary Land, rather than a successful identity stage. A selected
fresh name is an explicit parameter, so no allocator policy is built into the
program interpretation. The callback's actual inverse and selected continuation
are returned unchanged.

Successful evaluation follows the continuation selected by the operation outcome. -/
namespace Cordis.SemanticHead
noncomputable section
open Calculus Stages
universe u
variable {Name Key Value Code Error : Type u}
variable [DecidableEq Name] [DecidableEq Key]
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
abbrev Result (Name Key Value Code Error : Type u) :=
  Registry Name Key Value Code (Inverse Name Key Value) Error × Inverse Name Key Value × Option Code

def evaluate (program : Code → Instruction Name Key Value Code Error)
    (actor child : Name) (code : Code) (state : R) : Option (Result Name Key Value Code Error) := by
  classical
  exact match (program code).action with
  | .unit => some (state, .unit, (program code).next .unit)
  | .provide key value => match state actor with
    | none => none
    | some fiber => if fiber.component.provides key = true ∧ fiber.table key = none then
        some (write state actor key (some value), .restrict actor key, (program code).next (.value value)) else none
  | .operate key run => match location state actor key with
    | none => none
    | some (owner, before) => match run before with
      | .error _ => none
      | .ok (after, inverse, result) =>
          some (write state owner key (some after), .operate owner key inverse, (program code).next (.value result))
  | .instantiate component => if Insertable state child component (some actor) then
      some (put state child (fresh component (some actor)), .retire child, (program code).next (.child child)) else none

def CapturedChoice (child : Name) : Inverse Name Key Value → Prop
  | .retire selected => child = selected
  | _ => True

theorem evaluate_sound (program : Code → Instruction Name Key Value Code Error)
    (actor child : Name) (code : Code) (before after : R) (inverse : Inverse Name Key Value) (next : Option Code)
    (evaluated : evaluate program actor child code before = some (after, inverse, next)) :
    Land program actor code before after inverse next ∧ CapturedChoice child inverse := by
  unfold evaluate at evaluated
  cases action : (program code).action with
  | unit =>
    simp only [action, Option.some.injEq] at evaluated
    cases evaluated
    exact ⟨.unit before actor code action, True.intro⟩
  | provide key value =>
    simp only [action] at evaluated
    cases present : before actor with
    | none => simp [present] at evaluated
    | some fiber =>
      simp only [present] at evaluated
      split at evaluated
      · rename_i legal
        cases Option.some.inj evaluated
        exact ⟨.provide before actor code fiber key value action present legal.1 legal.2, True.intro⟩
      · cases evaluated
  | operate key run =>
    simp only [action] at evaluated
    cases located : location before actor key with
    | none => simp [located] at evaluated
    | some location =>
      obtain ⟨owner, value⟩ := location
      simp only [located] at evaluated
      cases called : run value with
      | error error => simp [called] at evaluated
      | ok result =>
        obtain ⟨result, undo, outcome⟩ := result
        simp only [called] at evaluated
        cases Option.some.inj evaluated
        exact ⟨.operate before actor code key run owner value result undo outcome action located called, True.intro⟩
  | instantiate component =>
    simp only [action] at evaluated
    split at evaluated
    · rename_i legal
      cases Option.some.inj evaluated
      exact ⟨.instantiate before actor code component child action legal, rfl⟩
    · cases evaluated

theorem evaluate_complete (program : Code → Instruction Name Key Value Code Error)
    {actor : Name} {code : Code} {before after : R} {inverse : Inverse Name Key Value} {next : Option Code}
    (landed : Land program actor code before after inverse next) (child : Name)
    (selected : CapturedChoice child inverse) :
    evaluate program actor child code before = some (after, inverse, next) := by
  cases landed with
  | unit state actor code action => simp [evaluate, action]
  | provide state actor code fiber key value action present declared absent =>
    simp [evaluate, action, present, declared, absent]
  | operate state actor code key run owner before after inverse outcome action located called =>
    simp [evaluate, action, located, called]
  | instantiate state actor code component selectedChild action ready =>
    have same : child = selectedChild := selected
    subst child
    simp [evaluate, action, ready]

/-- No successful head exists at this selected allocation input exactly when
no ordinary landing with that captured allocation exists. -/
theorem undefined_iff (program : Code → Instruction Name Key Value Code Error)
    (actor child : Name) (code : Code) (before : R) :
    evaluate program actor child code before = none ↔
      ¬ ∃ after inverse next, Land program actor code before after inverse next ∧ CapturedChoice child inverse := by
  constructor
  · intro absent ⟨after, inverse, next, landed, selected⟩
    have success := evaluate_complete program landed child selected
    rw [absent] at success
    cases success
  · intro noLanding
    cases evaluated : evaluate program actor child code before with
    | none => rfl
    | some result =>
      obtain ⟨after, inverse, next⟩ := result
      exact False.elim (noLanding ⟨after, inverse, next, evaluate_sound program actor child code before after inverse next evaluated⟩)

end
end Cordis.SemanticHead
