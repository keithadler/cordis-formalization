import Cordis.PartialMapClosure

/-! Quotient-sensitive partial-map algebra. Related maps compare both domains
at related inputs; no failure completion and no literal-output commutation
assumption. This is the relational reading of Eq39 used by Definitions34/44. -/
namespace Cordis.PartialObservedMapClosure
open Iterators (OptionRel)
open PartialCoeffectLifting PartialInverseObservation PartialMapClosure
universe u v
variable {S : Type u} (observation : Setoid S)

abbrev Maps := MapRelated observation.r

theorem option_refl (value : Option S) : OptionRel observation.r value value := by
  cases value with
  | none => trivial
  | some value => exact observation.refl value

abbrev Commutes (f g : PartialMap S) := Maps observation (compose f g) (compose g f)

private theorem compose_assoc (after middle before : PartialMap S) :
    compose after (compose middle before) = compose (compose after middle) before := by
  funext input
  exact Option.bind_assoc _ _ _

private theorem compose_left_identity (map : PartialMap S) : compose some map = map := by
  funext input
  cases called : map input <;> simp [compose, called]

theorem maps_symm {f g : PartialMap S} (related : Maps observation f g) : Maps observation g f := by
  intro left right inputs
  exact OptionRel.mono (fun _ _ values => observation.symm values)
    (OptionRel.symm (related right left (observation.symm inputs)))

theorem maps_trans {f g h : PartialMap S}
    (first : Maps observation f g) (second : Maps observation g h) : Maps observation f h := by
  intro left right inputs
  exact OptionRel.trans (R := observation.r) (fun _ _ _ => observation.trans)
    (first left left (observation.refl left)) (second left right inputs)

theorem maps_compose {f f' g g' : PartialMap S}
    (outer : Maps observation f f') (inner : Maps observation g g') :
    Maps observation (compose f g) (compose f' g') := by
  intro left right inputs
  have intermediate := inner left right inputs
  cases first : g left <;> cases second : g' right <;>
    simp only [first, second, OptionRel, compose, Option.bind_none, Option.bind_some] at intermediate ⊢
  exact outer _ _ intermediate

/-- Distributive step for a cross pair. The foreign maps can fail or change
the same state within their own word. Only cross-pair commutation is used. -/
theorem commutes_compose_right {f g h : PartialMap S}
    (first : Commutes observation f g) (second : Commutes observation f h)
    (gRespects : Maps observation g g) (hRespects : Maps observation h h) :
    Commutes observation f (compose g h) := by
  have swappedG : Maps observation (compose f (compose g h)) (compose g (compose f h)) := by
    rw [compose_assoc f g h, compose_assoc g f h]
    exact maps_compose observation first hRespects
  have swappedH : Maps observation (compose g (compose f h)) (compose (compose g h) f) := by
    rw [← compose_assoc g h f]
    exact maps_compose observation gRespects second
  exact maps_trans observation swappedG swappedH

theorem generated_respects {generators : PartialMap S → Prop}
    (respects : ∀ f, generators f → Maps observation f f) {f : PartialMap S}
    (generated : Generated generators f) : Maps observation f f := by
  induction generated with
  | identity => exact fun _ _ related => related
  | generator admitted => exact respects _ admitted
  | composition _ _ outer inner => exact maps_compose observation outer inner

theorem commutes_generated_right {generators : PartialMap S → Prop} {f g : PartialMap S}
    (self : Maps observation f f) (respects : ∀ h, generators h → Maps observation h h)
    (commutes : ∀ h, generators h → Commutes observation f h) (generated : Generated generators g) :
    Commutes observation f g := by
  induction generated with
  | identity =>
    change Maps observation f (compose some f)
    rw [compose_left_identity]
    exact self
  | generator admitted => exact commutes _ admitted
  | composition after before outer inner =>
    exact commutes_compose_right observation outer inner
      (generated_respects observation respects after) (generated_respects observation respects before)

/-- Partial counterpart of Lemma 41(1). Every left word commutes with
every right word, including both orders' joint definedness on related
inputs. Each side only needs its own generators to respect observation. -/
theorem generated_commutes {left right : PartialMap S → Prop} {f g : PartialMap S}
    (respectsLeft : ∀ map, left map → Maps observation map map)
    (respectsRight : ∀ map, right map → Maps observation map map)
    (commutes : ∀ before after, left before → right after → Commutes observation before after)
    (first : Generated left f) (second : Generated right g) : Commutes observation f g := by
  have rightRespect := generated_respects observation respectsRight second
  have opposite : Commutes observation g f := commutes_generated_right observation rightRespect respectsLeft
    (fun map valid => maps_symm observation
      (commutes_generated_right observation (respectsLeft map valid) respectsRight (fun _ other => commutes _ _ valid other) second)) first
  exact maps_symm observation opposite

end Cordis.PartialObservedMapClosure
