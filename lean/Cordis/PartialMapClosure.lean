import Cordis.PartialCoeffectLifting

/-! Genuine partial generated maps use Kleisli composition and compare joint
definedness. Guarded observation preservation is the explicit domain-restricted
reading of Equations 40/41, not their unconditional Maybe lift. -/
namespace Cordis.PartialMapClosure
open PartialCoeffectLifting
universe u v
variable {S : Type u}

inductive Generated (generators : PartialMap S → Prop) : PartialMap S → Prop
  | identity : Generated generators some
  | generator {map} : generators map → Generated generators map
  | composition {after before} : Generated generators after → Generated generators before →
      Generated generators (compose after before)

/-- Successful foreign transitions preserve the entire observation, which
may itself be Option-valued. Local definedness is not an extra premise. -/
def Preserves {Observation : Type v} (relation : Observation → Observation → Prop)
    (observe : S → Observation) (map : PartialMap S) : Prop :=
  ∀ before after, map before = some after → relation (observe after) (observe before)

/-- The partial form of Lemma 41's closure argument for yielded data.
Only successfully applied foreign words compare observations. -/
theorem generated_preserves {Observation : Type v} {relation : Observation → Observation → Prop}
    {observe : S → Observation} (identity : ∀ s, relation (observe s) (observe s))
    (transitive : ∀ {a b c}, relation a b → relation b c → relation a c)
    {generators : PartialMap S → Prop} (stable : ∀ map, generators map → Preserves relation observe map)
    {map : PartialMap S} (generated : Generated generators map) : Preserves relation observe map := by
  induction generated with
  | identity =>
    intro before after applied
    cases Option.some.inj applied
    exact identity before
  | generator valid => exact stable _ valid
  | composition _ _ outer inner =>
    intro before after applied
    obtain ⟨middle, first, second⟩ := Option.bind_eq_some_iff.mp applied
    exact transitive (outer middle after second) (inner before middle first)

end Cordis.PartialMapClosure
