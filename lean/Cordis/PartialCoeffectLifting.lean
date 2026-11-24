import Cordis.PartialInverseObservation

/-! Exact Definition29 Equation31 lifting with partial forwards AND partial
returned inverses. A missing binding or failed value operation returns none;
no identity completion is introduced. The captured inverse reads the current
binding at its later probe, preserving its own definedness. This is groundwork
for partial context-mediated iterators, not a proof of their recursive closure.
-/
namespace Cordis.PartialCoeffectLifting
open Coeffects Iterators PartialInverseObservation
universe u
variable {Key : Type u} {Value : Key → Type u} [DecidableEq Key]
abbrev Table (Value : Key → Type u) := (key : Key) → Option (Value key)
abbrev PartialMap (S : Type u) := S → Option S

def compose {S : Type u} (after before : PartialMap S) : PartialMap S :=
  fun input => (before input).bind after

def liftMap (key : Key) (transform : PartialMap (Value key)) : PartialMap (Table Value) :=
  fun table => do
    let value ← table key
    let changed ← transform value
    pure (update key (some changed) table)

def liftOperation {Outcome : Type u} (key : Key) (operation : Operation (Value key) Outcome) :
    Operation (Table Value) Outcome where
  run table := do
    let value ← table key
    let (changed, inverse, outcome) ← operation.run value
    pure (update key (some changed) table, liftMap key inverse, outcome)

def TableRelated (relations : ∀ key, Value key → Value key → Prop) (keys : Key → Prop)
    (left right : Table Value) : Prop :=
  ∀ key, keys key → OptionRel (relations key) (left key) (right key)

theorem update_related (relations : ∀ key, Value key → Value key → Prop) (keys : Key → Prop)
    (key : Key) {left right : Table Value} (related : TableRelated relations keys left right)
    {a b : Value key} (values : relations key a b) :
    TableRelated relations keys (update key (some a) left) (update key (some b) right) := by
  intro other selected
  by_cases same : other = key
  · subst other; simpa only [update_same, OptionRel] using values
  · simpa only [update_other key other _ _ same] using related other selected

theorem liftMap_related (relations : ∀ key, Value key → Value key → Prop) (keys : Key → Prop)
    (key : Key) (selected : keys key) {first second : PartialMap (Value key)}
    (maps : MapRelated (relations key) first second) :
    MapRelated (TableRelated relations keys) (liftMap key first) (liftMap key second) := by
  intro left right related
  have values := related key selected
  cases a : left key with
  | none =>
    cases b : right key <;> simp_all [OptionRel, liftMap]
  | some aValue =>
    cases b : right key with
    | none => simp_all [OptionRel]
    | some bValue =>
      have initial : relations key aValue bValue := by simpa only [a, b, OptionRel] using values
      have changed := maps aValue bValue initial
      cases fa : first aValue with
      | none => cases fb : second bValue <;> simp_all [OptionRel, liftMap]
      | some aChanged =>
        cases fb : second bValue with
        | none => simp_all [OptionRel]
        | some bChanged =>
          have output : relations key aChanged bChanged := by simpa only [fa, fb, OptionRel] using changed
          simpa [liftMap, a, b, fa, fb, OptionRel] using
            update_related relations keys key related output

theorem operation_success {Outcome : Type u} (key : Key) (operation : Operation (Value key) Outcome)
    (table : Table Value) (before after : Value key) (inverse : PartialMap (Value key)) (outcome : Outcome)
    (binding : table key = some before) (called : operation.run before = some (after, inverse, outcome)) :
    (liftOperation key operation).run table =
      some (update key (some after) table, liftMap key inverse, outcome) := by
  simp [liftOperation, binding, called]

/-- Complete graph characterization: success cannot discard a failed forward
or replace a partial inverse by a completed function. -/
theorem operation_success_iff {Outcome : Type u} (key : Key) (operation : Operation (Value key) Outcome)
    (table output : Table Value) (inverse : PartialMap (Table Value)) (outcome : Outcome) :
    (liftOperation key operation).run table = some (output, inverse, outcome) ↔
      ∃ before after saved, table key = some before ∧ operation.run before = some (after, saved, outcome) ∧
        output = update key (some after) table ∧ inverse = liftMap key saved := by
  constructor
  · intro success
    cases binding : table key with
    | none => simp [liftOperation, binding] at success
    | some before =>
      cases called : operation.run before with
      | none => simp [liftOperation, binding, called] at success
      | some result =>
        obtain ⟨after, saved, result⟩ := result
        have same : update key (some after) table = output ∧ liftMap key saved = inverse ∧ result = outcome := by
          simpa [liftOperation, binding, called, Prod.mk.injEq] using success
        obtain ⟨rfl, rfl, rfl⟩ := same
        exact ⟨before, after, saved, rfl, called, rfl, rfl⟩
  · rintro ⟨before, after, saved, binding, called, rfl, rfl⟩
    exact operation_success key operation table before after saved outcome binding called

theorem lift_respect {Outcome : Type u} (relations : ∀ key, Value key → Value key → Prop)
    (keys : Key → Prop) (key : Key) (selected : keys key) (operation : Operation (Value key) Outcome)
    (respect : ∀ left right, relations key left right →
      OptionRel (fun a b => relations key a.1 b.1 ∧ MapRelated (relations key) a.2.1 b.2.1 ∧ a.2.2 = b.2.2)
        (operation.run left) (operation.run right)) :
    ∀ left right, TableRelated relations keys left right →
      OptionRel (fun a b => TableRelated relations keys a.1 b.1 ∧
        MapRelated (TableRelated relations keys) a.2.1 b.2.1 ∧ a.2.2 = b.2.2)
        ((liftOperation key operation).run left) ((liftOperation key operation).run right) := by
  intro left right related
  have values := related key selected
  cases a : left key with
  | none => cases b : right key <;> simp_all [OptionRel, liftOperation]
  | some aValue =>
    cases b : right key with
    | none => simp_all [OptionRel]
    | some bValue =>
      have initial : relations key aValue bValue := by simpa only [a, b, OptionRel] using values
      have changed := respect aValue bValue initial
      cases fa : operation.run aValue with
      | none => cases fb : operation.run bValue <;> simp_all [OptionRel, liftOperation]
      | some aChanged =>
        cases fb : operation.run bValue with
        | none => simp_all [OptionRel]
        | some bChanged =>
          obtain ⟨outputs, inverses, outcomes⟩ := (show relations key aChanged.1 bChanged.1 ∧
            MapRelated (relations key) aChanged.2.1 bChanged.2.1 ∧ aChanged.2.2 = bChanged.2.2 by
              simpa only [fa, fb, OptionRel] using changed)
          simpa [liftOperation, a, b, fa, fb, OptionRel] using
            And.intro (update_related relations keys key related outputs)
              (And.intro (liftMap_related relations keys key selected inverses) outcomes)

theorem update_overwrite (key : Key) (first second : Option (Value key)) (table : Table Value) :
    update key first (update key second table) = update key first table := by
  funext other
  by_cases same : other = key
  · subst other; simp
  · simp [same]

theorem update_current (key : Key) (table : Table Value) : update key (table key) table = table := by
  funext other
  by_cases same : other = key
  · subst other; simp
  · simp [same]

/-- A successful value-level recovery lifts to literal restoration of the
whole table, and the inverse is proved defined at this actual forward result. -/
theorem lift_exact {Outcome : Type u} (key : Key) (operation : Operation (Value key) Outcome)
    (exactRecovery : ∀ before after inverse outcome,
      operation.run before = some (after, inverse, outcome) → inverse after = some before)
    (table output : Table Value) (inverse : PartialMap (Table Value)) (outcome : Outcome)
    (called : (liftOperation key operation).run table = some (output, inverse, outcome)) :
    inverse output = some table := by
  obtain ⟨before, after, saved, binding, original, rfl, rfl⟩ :=
    (operation_success_iff key operation table output inverse outcome).mp called
  simp only [liftMap, update_same]
  simp [exactRecovery before after saved outcome original, update_overwrite]
  rw [← binding, update_current]

end Cordis.PartialCoeffectLifting
