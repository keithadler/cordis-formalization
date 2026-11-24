import Cordis.PartialCoeffectIndependenceContracts

/-! Lemma39 with support required only at actually reachable heads. Definition30
still requires every named branch to belong to the broader grammar. Definition40
reachability selects a continuation only through an actual successful call.
No assumption constrains impossible named branches to the observation key set.
The result remains in the explicitly partial interpretation of Definition37. -/
namespace Cordis.PartialReachMediatedWitness
open PartialCoeffectLifting PartialInverseObservation PartialMediatedIterators
open PartialCoeffectIndependenceContracts
open Iterators (OptionRel)
open PartialIterators (Iterator stage Reach)
universe u
variable {S : Type u}

/-- A head's actual successful tail, rather than every outcome in the codomain,
is sufficient for the coinductive unfolding. -/
theorem stage_unfold_selected (observed : S → S → Prop) {Outcome : Type u}
    (operation : Operation S Outcome) (next : Outcome → Option (Iterator S))
    (relation : Iterator S → Iterator S → Prop)
    (respect : ∀ left right, observed left right →
      OptionRel (fun a b => observed a.1 b.1 ∧ MapRelated observed a.2.1 b.2.1 ∧ a.2.2 = b.2.2)
        (operation.run left) (operation.run right))
    (tails : ∀ input output inverse child,
      (stage operation next).run input = some (output, inverse, some child) → relation child child) :
    PartialIterators.Unfold observed relation (stage operation next) (stage operation next) := by
  intro before after inputs
  have compared := respect before after inputs
  cases a : operation.run before with
  | none => cases b : operation.run after <;> simp_all [OptionRel, stage, Iterator.run]
  | some first =>
    cases b : operation.run after with
    | none => simp_all [OptionRel]
    | some second =>
      have triple : observed first.1 second.1 ∧ MapRelated observed first.2.1 second.2.1 ∧
          first.2.2 = second.2.2 := by simpa [a, b, OptionRel] using compared
      simp only [stage, Iterator.run, a, b, Option.map_some, OptionRel]
      refine ⟨triple.1, triple.2.1, ?_⟩
      rw [triple.2.2]
      cases selected : next second.2.2 with
      | none => trivial
      | some child =>
        apply tails after second.1 second.2.1 child
        simp [stage, Iterator.run, b, selected]

variable {Key : Type u} {Value : Key → Type u} [DecidableEq Key]

/-- Locality of this head only; continuations carry no locality/witness premise. -/
inductive HeadLocal (signature : Signature Value) (keys : Key → Prop) : Iterator (Table Value) → Prop
  | unit : HeadLocal signature keys PartialIterators.unit
  | operation (name : signature.Name) (selected : keys (signature.key name))
      (next : signature.Outcome name → Option (Iterator (Table Value))) :
      HeadLocal signature keys (stage (signature.lifted name) next)
  | provision (key : Key) (selected : keys key) (value : Value key)
      (next : Option (Iterator (Table Value))) :
      HeadLocal signature keys (stage (PartialCoeffectProvision.provision key value) (fun _ => next))

theorem head_unfold {signature : Signature Value} (relations : ∀ key, Setoid (Value key))
    (contracts : Contracts signature relations) (keys : Key → Prop)
    (relation : Iterator (Table Value) → Iterator (Table Value) → Prop)
    {current : Iterator (Table Value)} (head : HeadLocal signature keys current)
    (tails : ∀ input output inverse child, current.run input = some (output, inverse, some child) →
      relation child child) :
    PartialIterators.Unfold (TableRelated (fun key => (relations key).r) keys) relation current current := by
  cases head with
  | unit =>
    intro before after inputs
    exact ⟨inputs, (fun _ _ related => related), trivial⟩
  | operation name selected next =>
    exact stage_unfold_selected _ (signature.lifted name) next relation
      (lift_respect (fun key => (relations key).r) keys (signature.key name) selected
        (signature.operation name) (contracts.respect name)) tails
  | provision key selected value next =>
    exact stage_unfold_selected _ (PartialCoeffectProvision.provision key value) (fun _ => next) relation
      (PartialCoeffectProvision.witnessed relations keys key selected value).respect tails

/-- The broader grammar supplies exact recovery. Observational support concerns
only heads actually reached through successful input probes. -/
theorem reachable_witnessed {signature : Signature Value} (relations : ∀ key, Setoid (Value key))
    (contracts : Contracts signature relations) {declared provided observedKeys : Key → Prop}
    {root : Iterator (Table Value)} (member : Mediated signature declared provided root)
    (support : ∀ current, Reach root current → HeadLocal signature observedKeys current) :
    PartialIterators.Witnessed (TableRelated (fun key => (relations key).r) observedKeys) root := by
  intro current reached
  refine ⟨(member.reachable reached).exact_recovery contracts.recovery, ?_⟩
  apply PartialIterators.related_coinduction _ (fun a b => a = b ∧ Reach root a) ?_ ⟨rfl, reached⟩
  intro left right pair
  obtain ⟨rfl, prior⟩ := pair
  apply head_unfold relations contracts observedKeys _ (support left prior)
  intro input output inverse child called
  exact ⟨rfl, .continuation prior input output inverse called⟩

end Cordis.PartialReachMediatedWitness
