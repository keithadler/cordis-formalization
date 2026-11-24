import Cordis.PartialObservedMapClosure

/-! Definedness under interleaved acquisition and discharge at one occupied
binding. Pending inverses can be discharged in any order up to observation. -/
namespace Cordis.PartialReplayHistory

open Iterators (OptionRel)
open PartialCoeffectLifting (PartialMap compose)
open PartialInverseObservation (MapRelated Operation)
open PartialObservedMapClosure (Commutes)
universe u
variable {Value : Type u}

def run : List (PartialMap Value) → Value → Option Value
  | [], input => some input
  | map :: word, input => (map input).bind (run word)

@[simp] theorem run_nil (input : Value) : run [] input = some input := rfl

@[simp] theorem run_cons (map : PartialMap Value) (word : List (PartialMap Value)) (input : Value) :
    run (map :: word) input = (map input).bind (run word) := rfl

theorem run_append (first second : List (PartialMap Value)) (input : Value) :
    run (first ++ second) input = (run first input).bind (run second) := by
  induction first generalizing input with
  | nil => rfl
  | cons map first ih =>
    simp only [List.cons_append, run_cons]
    cases call : map input with
    | none => rfl
    | some value => exact ih value

private theorem bind_related (observe : Setoid Value) {left right : Option Value}
    (values : OptionRel observe.r left right) {f g : PartialMap Value}
    (maps : MapRelated observe.r f g) :
    OptionRel observe.r (left.bind f) (right.bind g) := by
  cases left with
  | none =>
    cases right with
    | none => trivial
    | some _ => exact values.elim
  | some left =>
    cases right with
    | none => exact values.elim
    | some right => exact maps left right values

variable (observe : Setoid Value) (admitted : PartialMap Value → Prop)

/-- Definition 44 on the value at one fixed key, read using Eq. (35) with
partial outputs. Self-independence permits the same map twice. -/
structure KeyLaws : Prop where
  respects : ∀ map, admitted map → MapRelated observe.r map map
  commutes : ∀ first second, admitted first → admitted second → Commutes observe first second

variable {observe admitted}

theorem run_respects (laws : KeyLaws observe admitted) (word : List (PartialMap Value))
    (valid : ∀ map ∈ word, admitted map) : MapRelated observe.r (run word) (run word) := by
  induction word with
  | nil => exact fun _ _ related => related
  | cons head tail ih =>
    intro first second inputs
    simp only [run_cons]
    exact bind_related observe (laws.respects head (valid head List.mem_cons_self) _ _ inputs)
      (ih (fun map member => valid map (List.mem_cons_of_mem _ member)))

/-- Two orderings of the same captured occurrences agree in definedness and
return related values whenever they succeed. -/
theorem perm_related (laws : KeyLaws observe admitted)
    {left right : List (PartialMap Value)} (perm : left.Perm right)
    (valid : ∀ map ∈ left, admitted map) : MapRelated observe.r (run left) (run right) := by
  induction perm with
  | nil => exact fun _ _ related => related
  | cons head _ ih =>
    intro first second inputs
    simp only [run_cons]
    exact bind_related observe (laws.respects head (valid head List.mem_cons_self) _ _ inputs)
      (ih (fun map member => valid map (List.mem_cons_of_mem _ member)))
  | swap first second tail =>
    intro input probe related
    have headSwap := laws.commutes first second
      (valid first (by simp)) (valid second (by simp)) input probe related
    have suffix := run_respects laws tail (fun map member => valid map (by simp [member]))
    have result := bind_related observe headSwap suffix
    simpa only [compose, run_cons, Option.bind_assoc] using result
  | trans earlier later ihEarlier ihLater =>
    intro input probe related
    have validMiddle : ∀ map, map ∈ _ → admitted map := fun map member =>
      valid map (earlier.mem_iff.mpr member)
    exact OptionRel.trans (R := observe.r) (fun _ _ _ a b => observe.trans a b)
      (ihEarlier valid input probe related) (ihLater validMiddle probe probe (observe.refl probe))

/-- A successful prefix of the actual activity at one occupied slot.
Acquisition records the inverse returned on the actual input. Discharge
uses one subword of pending captures, with occurrences tracked by permutation.
The lifetime starts at a provision and ends before the binding is removed. -/
inductive History (admitted : PartialMap Value → Prop) : Value → List (PartialMap Value) → Prop where
  | provide (initial : Value) : History admitted initial []
  | acquire {Outcome : Type u} (operation : Operation Value Outcome)
      {before after : Value} {pending : List (PartialMap Value)} {inverse : PartialMap Value} {outcome : Outcome} :
      History admitted before pending →
      operation.run before = some (after, inverse, outcome) →
      admitted inverse → inverse after = some before →
      History admitted after (inverse :: pending)
  | discharge {before after : Value} {pending exiting remaining : List (PartialMap Value)} :
      History admitted before pending → (exiting ++ remaining).Perm pending →
      run exiting before = some after →
      History admitted after remaining

/-- Inverse provenance and permutation-independent replay definedness. The
proof transports partial domains rather than assuming total inverse maps. -/
theorem replay_ready (laws : KeyLaws observe admitted) {input : Value}
    {pending : List (PartialMap Value)} (history : History admitted input pending) :
    (∀ map ∈ pending, admitted map) ∧
    ∀ word, word.Perm pending → ∃ output, run word input = some output := by
  induction history with
  | provide initial =>
    refine ⟨by simp, ?_⟩
    intro word permutation
    cases word with
    | nil => exact ⟨initial, rfl⟩
    | cons head tail => simpa using permutation.length_eq
  | @acquire _ operation before after pending inverse outcome prior called valid recovered ih =>
    have all : ∀ map ∈ inverse :: pending, admitted map := by
      intro map member
      rcases List.mem_cons.mp member with equal | earlier
      · simpa [equal] using valid
      · exact ih.1 map earlier
    refine ⟨all, ?_⟩
    intro word permutation
    obtain ⟨original, replayed⟩ := ih.2 pending .rfl
    have same := perm_related laws permutation.symm all after after (observe.refl after)
    rw [run_cons, recovered, Option.bind_some, replayed] at same
    cases performed : run word after with
    | none => simp [performed, OptionRel] at same
    | some result => exact ⟨result, rfl⟩
  | @discharge before after pending exiting remaining prior selected performed ih =>
    refine ⟨fun map inside => ih.1 map (selected.mem_iff.mp (List.mem_append_right _ inside)), ?_⟩
    intro word permutation
    have pair : (exiting ++ word).Perm pending := (List.Perm.append_left exiting permutation).trans selected
    have ⟨result, replayed⟩ := ih.2 _ pair
    rw [run_append, performed, Option.bind_some] at replayed
    exact ⟨result, replayed⟩

theorem subword_ready (laws : KeyLaws observe admitted) {input : Value}
    {pending earlier later : List (PartialMap Value)} (history : History admitted input pending)
    (selection : (earlier ++ later).Perm pending) : ∃ output, run earlier input = some output := by
  obtain ⟨_, completed⟩ := (replay_ready laws history).2 _ selection
  rw [run_append] at completed
  cases first : run earlier input with
  | none => simp [first] at completed
  | some output => exact ⟨output, rfl⟩

/-- At an absent binding, every operation in the replay word is identity.
At a present binding, the word retains its actual success domain. -/
def keepMissing (word : PartialMap Value) : PartialMap (Option Value)
  | none => some none
  | some value => (word value).map some

/-- The provider's word at one key has a prefix of operation inverses before
its provision restriction. The erased slot is recorded as `some none`. -/
def eraseAfter (word : List (PartialMap Value)) : PartialMap (Option Value) :=
  fun slot => (keepMissing (run word) slot).map fun _ => none

theorem subwords_ready (laws : KeyLaws observe admitted) {input : Value}
    {pending first second rest : List (PartialMap Value)} (history : History admitted input pending)
    (selection : (first ++ second ++ rest).Perm pending) :
    ∃ middle final, run first input = some middle ∧ run second middle = some final := by
  obtain ⟨final, completed⟩ := subword_ready laws history selection
  rw [run_append] at completed
  cases called : run first input with
  | none => simp [called] at completed
  | some middle => exact ⟨middle, final, rfl, by simpa [called] using completed⟩

/-- At a retained occupied key where neither replay erases the binding,
both selected pending words can run, and reversing them preserves the
value observation. -/
theorem pending_commute (laws : KeyLaws observe admitted) {input : Value}
    {pending first second rest : List (PartialMap Value)}
    (history : History admitted input pending) (selection : (first ++ second ++ rest).Perm pending) :
    ∃ left right,
      run (first ++ second) input = some left ∧
      run (second ++ first) input = some right ∧ observe.r left right := by
  obtain ⟨firstOutput, left, firstCalled, secondCalled⟩ := subwords_ready laws history selection
  have combined : run (first ++ second) input = some left := by simp [run_append, firstCalled, secondCalled]
  have valid : ∀ map ∈ first ++ second, admitted map := fun map member =>
    (replay_ready laws history).1 map (selection.mem_iff.mp (List.mem_append_left _ member))
  have agreement := perm_related laws List.perm_append_comm valid input input (observe.refl input)
  rw [combined] at agreement
  cases pendingOrder : run (second ++ first) input with
  | none => simp [pendingOrder, OptionRel] at agreement
  | some right => exact ⟨left, right, combined, rfl, by simpa only [pendingOrder, OptionRel] using agreement⟩

/-- When a consumer unloads, its operation inverses and the provider's
operation inverses are jointly pending. Their partial domains are preserved
through either replay order, including the provider's final restriction. -/
theorem erase_commutes_with_pending (laws : KeyLaws observe admitted) {input : Value}
    {pending provider consumer rest : List (PartialMap Value)}
    (history : History admitted input pending)
    (selection : (provider ++ consumer ++ rest).Perm pending) :
    compose (eraseAfter provider) (keepMissing (run consumer)) (some input) = some none ∧
      compose (keepMissing (run consumer)) (eraseAfter provider) (some input) = some none := by
  have reversed : (consumer ++ provider ++ rest).Perm pending :=
    (List.Perm.append_right rest List.perm_append_comm).trans selection
  obtain ⟨afterConsumer, afterProvider, consumerCalled, providerCalled⟩ :=
    subwords_ready laws history reversed
  obtain ⟨afterProvider', providerCalled'⟩ := subword_ready laws history
    (by simpa only [List.append_assoc] using selection)
  exact ⟨by simp [compose, eraseAfter, keepMissing, consumerCalled, providerCalled],
    by simp [compose, eraseAfter, keepMissing, providerCalled']⟩

/-- A consumer's successful forward call records an additional pending
inverse. The provider's word can run at both its original and updated value
by replay readiness. The forward call after the final restriction reads an
absent binding and is identity. -/
theorem erase_commutes_with_forward (laws : KeyLaws observe admitted) {Outcome : Type u}
    {input output : Value} {pending provider rest : List (PartialMap Value)}
    (history : History admitted input pending) (selection : (provider ++ rest).Perm pending)
    (operation : Operation Value Outcome) (result : Outcome) (inverse : PartialMap Value)
    (called : operation.run input = some (output, inverse, result))
    (valid : admitted inverse) (recovers : inverse output = some input) :
    let forward := keepMissing fun value => (operation.run value).map Prod.fst
    compose (eraseAfter provider) forward (some input) = some none ∧
      compose forward (eraseAfter provider) (some input) = some none := by
  have updated : History admitted output (inverse :: pending) :=
    .acquire operation history called valid recovers
  have afterSelection : (provider ++ inverse :: rest).Perm (inverse :: pending) :=
    (List.perm_middle (a := inverse) (l₁ := provider) (l₂ := rest)).trans
      (List.Perm.cons inverse selection)
  obtain ⟨afterProvider, providerCalled⟩ := subword_ready laws updated afterSelection
  obtain ⟨beforeProvider, providerCalled'⟩ := subword_ready laws history selection
  exact ⟨by simp [compose, eraseAfter, keepMissing, called, providerCalled],
    by simp [compose, eraseAfter, keepMissing, providerCalled']⟩

/-- At a retained occupied key, the actual foreign forward call and relevant
saved inverse word commute with matching success. Replaying in the alternate
order needs no extra callback-domain hypothesis. -/
theorem forward_commutes_with_pending (laws : KeyLaws observe admitted) {Outcome : Type u}
    {input output : Value} {pending saved rest : List (PartialMap Value)}
    (history : History admitted input pending) (selection : (saved ++ rest).Perm pending)
    (operation : Operation Value Outcome) (result : Outcome) (inverse : PartialMap Value)
    (called : operation.run input = some (output, inverse, result))
    (inverseValid : admitted inverse) (recovers : inverse output = some input)
    (forwardValid : admitted fun value => (operation.run value).map Prod.fst) :
    let forward : PartialMap Value := fun value => (operation.run value).map Prod.fst
    ∃ left right, compose (run saved) forward input = some left ∧
      compose forward (run saved) input = some right ∧ observe.r left right := by
  let forward : PartialMap Value := fun value => (operation.run value).map Prod.fst
  have updated : History admitted output (inverse :: pending) :=
    .acquire operation history called inverseValid recovers
  have afterSelection : (saved ++ inverse :: rest).Perm (inverse :: pending) :=
    (List.perm_middle (a := inverse) (l₁ := saved) (l₂ := rest)).trans (List.Perm.cons inverse selection)
  obtain ⟨left, savedCalled⟩ := subword_ready laws updated afterSelection
  have forwardCalled : forward input = some output := by simp [forward, called]
  have valid : ∀ map ∈ forward :: saved, admitted map := by
    intro map member
    rcases List.mem_cons.mp member with eq | earlier
    · simpa only [eq] using forwardValid
    · exact (replay_ready laws history).1 map (selection.mem_iff.mp (List.mem_append_left _ earlier))
  have swap : (forward :: saved).Perm (saved ++ [forward]) :=
    by simpa only [List.append_nil] using
      (List.perm_middle (a := forward) (l₁ := saved) (l₂ := [])).symm
  have related := perm_related laws swap valid input input (observe.refl input)
  rw [run_cons, forwardCalled, Option.bind_some, savedCalled, run_append] at related
  have singleton : run [forward] = forward := by
    funext value
    cases call : forward value <;> simp [call]
  rw [singleton] at related
  change OptionRel observe.r (some left) (compose forward (run saved) input) at related
  change ∃ a b, compose (run saved) forward input = some a ∧
    compose forward (run saved) input = some b ∧ observe.r a b
  have inOrder : compose (run saved) forward input = some left := by
    simp only [compose, forwardCalled, Option.bind_some, savedCalled]
  cases alternate : compose forward (run saved) input with
  | none => simp [alternate, OptionRel] at related
  | some right => exact ⟨left, right, inOrder, rfl, by simpa only [alternate, OptionRel] using related⟩

end Cordis.PartialReplayHistory
