import Cordis.AccumulatorProvenance
import Cordis.OrderingIntervals
import Cordis.RuleEvaluation

/-!
Lemma67's actual-application bridge. A frozen map keeps the owner/key resolved
by its real landing; it never recomputes a committed view on the counterfactual
input. This gives the partial replay proof the actual application and the
exact state map selected by Table 1.
-/
namespace Cordis.EntangledApplications
open Calculus Stages StageRecovery InterleavedRecovery AccumulatorProvenance
universe u
variable {Name Key Value Code Error : Type u}
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
variable [DecidableEq Name] [DecidableEq Key]
set_option linter.unusedSectionVars false

theorem undo_preserves_absence (i : Inverse Name Key Value) (r : R) (name : Name)
    (absent : r name = none) : Stages.undo i r name = none := by
  cases i with
  | unit => exact absent
  | restrict owner key =>
    by_cases same : name = owner <;> simp_all [Stages.undo, write, Calculus.modify]
  | operate owner key inverse =>
    by_cases same : name = owner <;> simp_all [Stages.undo, Calculus.modify]
  | retire child =>
    by_cases same : name = child <;> simp_all [Stages.undo, Calculus.retire, Calculus.modify]

theorem discharge_preserves_absence (inverses : List (Inverse Name Key Value))
    (r : R) (name : Name) (absent : r name = none) :
    discharge Stages.undo inverses r name = none := by
  induction inverses generalizing r with
  | nil => exact absent
  | cons i rest ih => exact ih _ (undo_preserves_absence i r name absent)

/-- The exact fixed map associated with a successful landing. Its actual input
and output are part of the relation, as are the callback and captured owner.
`callbackMap` evaluates the recorded operation at a replay input. -/
inductive LandingMap (program : Code → Instruction Name Key Value Code Error) (actor : Name) :
    Code → R → R → (R → R) → Prop
  | unit (code r) : (program code).action = .unit → LandingMap program actor code r r id
  | provide (code r fiber key value) :
      (program code).action = .provide key value → r actor = some fiber →
      fiber.component.provides key = true → fiber.table key = none →
      LandingMap program actor code r (write r actor key (some value))
        (fun input => write input actor key (some value))
  | operate (code r key run owner before after inverse result) :
      (program code).action = .operate key run → location r actor key = some (owner, before) →
      run before = .ok (after, inverse, result) →
      LandingMap program actor code r (write r owner key (some after))
        (transform owner key (callbackMap run))
  | instantiate (code r component child) :
      (program code).action = .instantiate component → Insertable r child component (some actor) →
      LandingMap program actor code r (put r child (fresh component (some actor)))
        (fun input => put input child (fresh component (some actor)))

theorem land_freezes (program : Code → Instruction Name Key Value Code Error)
    {actor : Name} {code : Code} {r s : R} {i : Inverse Name Key Value} {next : Option Code}
    (land : Land program actor code r s i next) : ∃ map, LandingMap program actor code r s map := by
  cases land with
  | unit _ _ code action => exact ⟨id, .unit code r action⟩
  | provide _ _ code fiber key value action present allowed absent =>
    exact ⟨_, .provide code r fiber key value action present allowed absent⟩
  | operate _ _ code key run owner before after inverse result action located returned =>
    exact ⟨_, .operate code r key run owner before after inverse result action located returned⟩
  | instantiate _ _ code component child action ready =>
    exact ⟨_, .instantiate code r component child action ready⟩

inductive FrozenApplication (program : Code → Instruction Name Key Value Code Error) (actor : Name) :
    RuleEvaluation.Use Name Key Value Code → R → R → (R → R) → Prop
  | identity (r) : FrozenApplication program actor .identity r r id
  | iteration {code r s map} : LandingMap program actor code r s map →
      FrozenApplication program actor (.iteration code) r s map
  | accumulator (inverses r) : FrozenApplication program actor (.accumulator inverses)
      r (discharge Stages.undo inverses r) (discharge Stages.undo inverses)

theorem freeze_application (program : Code → Instruction Name Key Value Code Error)
    {actor : Name} {use : RuleEvaluation.Use Name Key Value Code} {r s : R}
    (application : RuleEvaluation.Application program actor use r s) :
    ∃ map, FrozenApplication program actor use r s map := by
  cases application with
  | identity => exact ⟨id, .identity r⟩
  | iteration _ _ _ _ _ land =>
    obtain ⟨map, frozen⟩ := land_freezes program land
    exact ⟨map, .iteration frozen⟩
  | accumulator => exact ⟨_, .accumulator _ _⟩

theorem scoped_avoids (actor owner : Name) (requires : Key → Bool) (key : Key)
    (different : owner ≠ actor) (unrequired : requires key = false)
    (i : Inverse Name Key Value) (scope : TableFrame.Scoped actor requires i) : Avoids owner key i := by
  cases i with
  | unit => trivial
  | retire => trivial
  | restrict n k =>
    intro both
    exact different (both.1.symm.trans scope)
  | operate n k inverse =>
    intro both
    rcases scope with own | required
    · exact different (both.1.symm.trans own)
    · rw [both.2, unrequired] at required
      contradiction

def ProviderOverlap (fiber foreign : F) : Prop :=
  ∃ key, foreign.component.provides key = true ∧
    (fiber.component.requires key = true ∨ fiber.component.provides key = true)

theorem control_application_identity
    {program : Code → Instruction Name Key Value Code Error} {rule : Labeled.Rule}
    {actor : Name} {use : RuleEvaluation.Use Name Key Value Code} {r s : R} {map : R → R}
    (frozen : FrozenApplication program actor use r s map) (allowed : use.allowed rule r actor)
    (control : rule = .insert ∨ rule = .retire ∨ rule = .remove ∨ rule = .begin ∨ rule = .leave) :
    map = id := by
  cases frozen with
  | identity => rfl
  | iteration landing =>
    have impossible := allowed.1
    rcases control with eq | eq | eq | eq | eq <;> simp [eq] at impossible
  | accumulator inverses r =>
    have impossible := allowed.1
    rcases control with eq | eq | eq | eq | eq <;> simp [eq] at impossible

end Cordis.EntangledApplications
