import Cordis.Repairs.BoundOperation

/-! Recursive, outcome-selected operation programs on a fixed bound key.
Scalar coeffect contracts are the only semantic assumptions. Every registry
head and captured inverse is the native lifting proved in BoundOperation.
This closes the operation-only grammar; it does not yet compose changing
allocation domains or different bound keys into the complete Lemma 57.
-/
namespace Cordis.Repairs.BoundOperationIterators
open TypedRegistry BoundOperation
open PaperEffectEquations (CoeffectOperations)
open PartialInverseObservation (Witnessed)
open PartialIterators (Iterator stage Reach)
universe u
variable {Name Key Code : Type u} {V : Key → Type u}
variable [DecidableEq Name] [DecidableEq Key]
variable {ops : CoeffectOperations V} {actor owner : Name}
variable {acting providing : Calculus.Component Key Code} {key : Key}
local notation "G" => Gamma ops actor acting owner providing key

inductive Mediated (provided : providing.provides key = true) : Iterator G → Prop
  | unit : Mediated provided PartialIterators.unit
  | operation (name : ops.Name key) (argument : ops.Argument key name)
      (next : ops.Outcome key name → Option (Iterator G))
      (tails : ∀ outcome tail, next outcome = some tail → Mediated provided tail) :
      Mediated provided (stage (liftOperation provided (ops.operation key name argument)) next)

variable {provided : providing.provides key = true}

theorem Mediated.continuation {current child : Iterator G} (member : Mediated provided current)
    {input output : G} {inverse : G → Option G}
    (called : current.run input = some (output, inverse, some child)) : Mediated provided child := by
  cases member with
  | unit => simp [PartialIterators.unit, Iterator.run] at called
  | operation name argument next tails =>
    obtain ⟨outcome, _, selected⟩ := (PartialIterators.stage_success_iff _ _ _ _ _ _).mp called
    exact tails outcome child selected

theorem Mediated.reachable {root current : Iterator G} (member : Mediated provided root)
    (reached : Reach root current) : Mediated provided current := by
  induction reached with
  | root => exact member
  | continuation _ _ _ _ called ih => exact ih.continuation called

theorem Mediated.exact_recovery
    (recovery : ∀ name argument before after inverse outcome,
      (ops.operation key name argument).run before = some (after, inverse, outcome) → inverse after = some before)
    {current : Iterator G} (member : Mediated provided current) : PartialIterators.ExactRecovery current := by
  intro input output inverse tail called
  cases member with
  | unit =>
    have same : input = output ∧ some = inverse ∧ none = tail := by
      simpa [PartialIterators.unit, Iterator.run] using called
    obtain ⟨rfl, rfl, rfl⟩ := same
    rfl
  | operation name argument next _ =>
    obtain ⟨outcome, applied, _⟩ := (PartialIterators.stage_success_iff _ _ _ _ _ _).mp called
    exact operation_exact_recovery provided (ops.operation key name argument)
      (recovery name argument) input output inverse outcome applied

/-- The full recursive witness holds for every actually reachable head, with
the continuation selected by the operation's genuine typed result. -/
theorem witnessed (observe : ∀ key, Setoid (V key)) (keys : Key → Prop) (selected : keys key)
    (contracts : ∀ name argument, Witnessed (ops.operation key name argument) (observe key).r)
    (recovery : ∀ name argument before after inverse outcome,
      (ops.operation key name argument).run before = some (after, inverse, outcome) → inverse after = some before)
    {root : Iterator G} (member : Mediated provided root) :
    PartialIterators.Witnessed (Observed observe keys) root := by
  intro current reached
  refine ⟨(member.reachable reached).exact_recovery recovery, ?_⟩
  apply PartialIterators.related_coinduction _ (fun a b => a = b ∧ Reach root a) ?_ ⟨rfl, reached⟩
  intro left right pair
  obtain ⟨rfl, prior⟩ := pair
  cases member.reachable prior with
  | unit =>
    intro a b related
    exact ⟨related, (fun _ _ same => same), trivial⟩
  | operation name argument next _ =>
    apply PartialReachMediatedWitness.stage_unfold_selected _ _ _ _
      (operation_respects observe keys selected provided (ops.operation key name argument) (contracts name argument))
    intro input output inverse child called
    exact ⟨rfl, .continuation prior input output inverse called⟩

end Cordis.Repairs.BoundOperationIterators
