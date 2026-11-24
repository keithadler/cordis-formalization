import Cordis.PartialCoeffectLifting

/-! Definitions19/20 with both original preconditions retained. Provision is
undefined at an occupied key; its captured restriction is undefined at an
absent key. Neither failure is an identity transition. -/
namespace Cordis.PartialCoeffectProvision
open Coeffects Iterators PartialInverseObservation PartialCoeffectLifting
universe u
variable {Key : Type u} {Value : Key → Type u} [DecidableEq Key]

def restrict (key : Key) : PartialMap (Table Value) := fun table =>
  match table key with
  | none => none
  | some _ => some (update key none table)

def provision (key : Key) (value : Value key) : Operation (Table Value) PUnit.{u+1} where
  run table := match table key with
    | none => some (update key (some value) table, restrict key, PUnit.unit)
    | some _ => none

theorem update_options_related (relations : ∀ key, Value key → Value key → Prop) (keys : Key → Prop)
    (key : Key) {left right : Table Value} (related : TableRelated relations keys left right)
    {a b : Option (Value key)} (values : OptionRel (relations key) a b) :
    TableRelated relations keys (update key a left) (update key b right) := by
  intro other selected
  by_cases same : other = key
  · subst other; simpa only [update_same] using values
  · simpa only [update_other key other _ _ same] using related other selected

theorem restriction_related (relations : ∀ key, Value key → Value key → Prop) (keys : Key → Prop)
    (key : Key) (selected : keys key) :
    MapRelated (TableRelated relations keys) (restrict key) (restrict key) := by
  intro left right related
  have values := related key selected
  cases a : left key <;> cases b : right key <;> simp only [a, b, OptionRel] at values
  · simp [restrict, a, b, OptionRel]
  · simpa only [restrict, a, b, OptionRel] using
      update_options_related relations keys key related (show OptionRel (relations key) none none from trivial)

theorem exact_recovery (key : Key) (value : Value key) (input output : Table Value)
    (inverse : PartialMap (Table Value)) (outcome : PUnit.{u+1})
    (called : (provision key value).run input = some (output, inverse, outcome)) :
    inverse output = some input := by
  cases binding : input key with
  | some old => simp [provision, binding] at called
  | none =>
    have same : update key (some value) input = output ∧ restrict key = inverse ∧ PUnit.unit = outcome := by
      simpa only [provision, binding, Option.some.injEq, Prod.mk.injEq] using called
    obtain ⟨rfl, rfl, rfl⟩ := same
    simp only [restrict, update_same, update_overwrite]
    rw [← binding, update_current]

theorem witnessed (relations : ∀ key, Setoid (Value key)) (keys : Key → Prop)
    (key : Key) (selected : keys key) (value : Value key) :
    Witnessed (provision key value) (TableRelated (fun k => (relations k).r) keys) := by
  constructor
  · intro input output inverse outcome called
    refine ⟨input, exact_recovery key value input output inverse outcome called, ?_⟩
    intro other _
    cases input other with
    | none => trivial
    | some value => exact (relations other).refl value
  · intro left right related
    have values := related key selected
    cases a : left key <;> cases b : right key <;> simp only [a, b, OptionRel] at values
    · simp only [provision, a, b, OptionRel]
      exact ⟨update_related (fun k => (relations k).r) keys key related ((relations key).refl value),
        restriction_related (fun k => (relations k).r) keys key selected, trivial⟩
    · simp [provision, a, b, OptionRel]

end Cordis.PartialCoeffectProvision
