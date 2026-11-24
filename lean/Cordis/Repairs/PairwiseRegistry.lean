import Cordis.Repairs.PairwiseSlots
import Cordis.Repairs.PairwisePrograms

/-! Reflection of the addressed table maps into the full native registry on
their ordinary scoped domains. Every edit uses the actual typed write, and
definedness of each intermediate write is preserved by projection. -/
namespace Cordis.Repairs.PairwiseRegistry
open TypedRegistry PairwiseSlots
open PaperEffectEquations (CoeffectOperations ValueOperationWitness)
open PartialCoeffectLifting (PartialMap compose)
open PartialCoeffectIndependenceContracts (tableSetoid)
open PartialMapClosure (Generated)
open Iterators (OptionRel)

universe u
variable {Name Key Code : Type u} {V : Key → Type u}
variable [DecidableEq Name] [DecidableEq Key] {ops : CoeffectOperations V}
local notation "R" => Registry Name V Code
local notation "ST" => Tables Name V

/-- The physical edit is a partial native write. A missing owner cannot
accept a provision even when the projected table coordinate is empty. -/
def runEdit (edit : Edit Name V) (state : R) : Option R :=
  (state edit.slot.1).bind fun _ =>
    (edit.apply (tablesOf state edit.slot)).map (write state edit.slot.1 edit.slot.2)

def runWord (word : List (Edit Name V)) : PartialMap R :=
  PartialReplayHistory.run (word.map runEdit)

def tableWord (word : List (Edit Name V)) : PartialMap ST :=
  PartialReplayHistory.run (word.map Edit.run)

def OwnersPresent (state : R) (word : List (Edit Name V)) : Prop :=
  ∀ edit ∈ word, state edit.slot.1 ≠ none

theorem edit_success {edit : Edit Name V} {before after : R}
    (called : runEdit edit before = some after) :
    ∃ row output, before edit.slot.1 = some row ∧ edit.apply (tablesOf before edit.slot) = some output ∧
      after = write before edit.slot.1 edit.slot.2 output := by
  unfold runEdit at called
  obtain ⟨row, found, body⟩ := Option.bind_eq_some_iff.mp called
  obtain ⟨output, changed, equal⟩ := Option.map_eq_some_iff.mp body
  exact ⟨row, output, found, changed, equal.symm⟩

private theorem edit_controls (ops : CoeffectOperations V) {before after : R} {edit : Edit Name V}
    (called : runEdit edit before = some after) :
    Transposition.SameControls (encodeRegistry ops before) (encodeRegistry ops after) := by
  obtain ⟨row, output, found, changed, rfl⟩ := edit_success called
  rw [encode_write]
  exact Transposition.write_controls _ _ _ _

omit [DecidableEq Name] in
private theorem controls_presence (ops : CoeffectOperations V) {before after : R}
    (controls : Transposition.SameControls (encodeRegistry ops before) (encodeRegistry ops after)) (name : Name) :
    after name = none ↔ before name = none := by
  have same := controls name
  cases first : before name <;> cases second : after name <;> simp_all [encodeRegistry, OptionRel]

private theorem edit_projection (edit : Edit Name V) (state : R) (present : state edit.slot.1 ≠ none) :
    (runEdit edit state).map tablesOf = edit.run (tablesOf state) := by
  cases found : state edit.slot.1 with
  | none => exact False.elim (present found)
  | some row =>
    cases result : edit.apply (tablesOf state edit.slot) with
    | none => simp [runEdit, Edit.run, found, result]
    | some value =>
      simp only [runEdit, Edit.run, found, result, Option.bind_some, Option.map_some, Option.some.injEq]
      exact tablesOf_write state edit.slot.1 edit.slot.2 value present

private theorem word_controls (ops : CoeffectOperations V) (word : List (Edit Name V)) {before after : R}
    (called : runWord word before = some after) :
    Transposition.SameControls (encodeRegistry ops before) (encodeRegistry ops after) := by
  induction word generalizing before with
  | nil =>
    change some before = some after at called
    cases Option.some.inj called
    exact Transposition.controls_refl _
  | cons head tail ih =>
    obtain ⟨middle, applied, rest⟩ := Option.bind_eq_some_iff.mp called
    exact Transposition.controls_trans (edit_controls ops applied) (ih rest)

/-- Successful evaluation itself proves all target owners present at the
initial cut. Ordinary writes never introduce or remove a row. -/
theorem owners_present_of_run (ops : CoeffectOperations V) (word : List (Edit Name V)) {before after : R}
    (called : runWord word before = some after) : OwnersPresent before word := by
  induction word generalizing before with
  | nil => simp [OwnersPresent]
  | cons head tail ih =>
    obtain ⟨middle, applied, rest⟩ := Option.bind_eq_some_iff.mp called
    obtain ⟨row, output, found, changed, same⟩ := edit_success applied
    intro edit member
    rcases List.mem_cons.mp member with rfl | inTail
    · rw [found]
      exact Option.noConfusion
    · intro absent
      exact ih rest edit inTail ((controls_presence ops (edit_controls ops applied) edit.slot.1).mpr absent)

/-- On a probe retaining the selected owners, the projection reflects
failure as well as success and yields exactly the complete output tables. -/
theorem word_projection (ops : CoeffectOperations V) (word : List (Edit Name V)) (state : R)
    (present : OwnersPresent state word) : (runWord word state).map tablesOf = tableWord word (tablesOf state) := by
  induction word generalizing state with
  | nil => rfl
  | cons head tail ih =>
    have projected := edit_projection head state (present head List.mem_cons_self)
    change ((runEdit head state).bind (runWord tail)).map tablesOf =
      (head.run (tablesOf state)).bind (tableWord tail)
    rw [← projected]
    cases applied : runEdit head state with
    | none => rfl
    | some middle =>
      have remains : OwnersPresent middle tail := by
        intro edit member absent
        exact present edit (List.mem_cons_of_mem _ member)
          ((controls_presence ops (edit_controls ops applied) edit.slot.1).mp absent)
      exact ih middle remains

private theorem table_word_generated (ops : CoeffectOperations V) (actor : Name)
    (component : Calculus.Component Key Code) (word : List (Edit Name V))
    (allowed : ∀ edit ∈ word, Admitted ops actor component edit) :
    Generated (Generator ops actor component) (tableWord word) := by
  induction word with
  | nil => exact .identity
  | cons head tail ih =>
    exact .composition (ih (fun edit member => allowed edit (List.mem_cons_of_mem _ member)))
      (.generator ⟨head, allowed head List.mem_cons_self, rfl⟩)

private theorem table_word_append (first second : List (Edit Name V)) :
    tableWord (first ++ second) = compose (tableWord second) (tableWord first) := by
  funext tables
  unfold tableWord
  rw [List.map_append, PartialReplayHistory.run_append]
  rfl

omit [DecidableEq Name] in
private theorem encoded_table_owner (ops : CoeffectOperations V) (state : R) (owner : Name) (key : Key) :
    StageRecovery.tableAt (encodeRegistry ops state) owner key = (tablesOf state (owner, key)).map (TypedCoeffectReplay.pack key) := by
  cases found : state owner <;> simp [tablesOf, tableAt, StageRecovery.tableAt, encodeRegistry, encodeFiber, found]

omit [DecidableEq Name] in
private theorem raw_slot_related (observe : ∀ key, Setoid (V key)) {left right : R}
    (related : PairwisePrograms.Related (ops := ops) observe left right) (owner : Name) (key : Key) :
    letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
    OptionRel (· ≈ ·) (StageRecovery.tableAt (encodeRegistry ops left) owner key)
      (StageRecovery.tableAt (encodeRegistry ops right) owner key) := by
  letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
  have rows := related owner
  cases first : encodeRegistry ops left owner <;> cases second : encodeRegistry ops right owner <;>
    simp only [first, second, StageRecovery.tableAt, Option.bind_none, Option.bind_some, OptionRel] at rows ⊢
  exact rows.table key

omit [DecidableEq Name] in
theorem slot_related (observe : ∀ key, Setoid (V key)) {left right : R}
    (related : PairwisePrograms.Related (ops := ops) observe left right) (owner : Name) (key : Key) :
    OptionRel (observe key).r (tableAt left owner key) (tableAt right owner key) := by
  have slot := raw_slot_related observe related owner key
  rw [encoded_table_owner, encoded_table_owner] at slot
  change OptionRel _ ((tableAt left owner key).map _) ((tableAt right owner key).map _) at slot
  cases a : tableAt left owner key <;> cases b : tableAt right owner key <;>
    simp only [a, b, Option.map_none, Option.map_some, OptionRel] at slot ⊢
  exact (TypedCoeffectReplay.packed_related (Yield := Yield ops) observe key _ _).mp slot

/-- Ordinary fixed edits respect the whole compatible native state
relation. Row presence agrees and the typed partial callback is compared
only at its recorded owner and key. -/
theorem edit_respects_registry (ops : CoeffectOperations V) (observe : ∀ key, Setoid (V key))
    (laws : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    {actor : Name} {component : Calculus.Component Key Code} {edit : Edit Name V}
    (allowed : Admitted ops actor component edit) {left right : R}
    (related : PairwisePrograms.Related (ops := ops) observe left right) :
    OptionRel (PairwisePrograms.Related (ops := ops) observe)
      (runEdit edit left) (runEdit edit right) := by
  letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
  let owner := edit.slot.1
  let key := edit.slot.2
  have values : OptionRel (observe key).r (tablesOf left edit.slot) (tablesOf right edit.slot) :=
    slot_related observe related owner key
  have writes := apply_respects ops observe laws allowed _ _ values
  have owners := related owner
  unfold runEdit
  change OptionRel _ ((left owner).bind _) ((right owner).bind _)
  cases l : left owner <;> cases r : right owner <;>
    simp only [encodeRegistry, l, r, Option.map_none, Option.map_some, OptionRel] at owners
  · exact True.intro
  · simp only [Option.bind_some]
    cases a : edit.apply (tablesOf left edit.slot) <;> cases b : edit.apply (tablesOf right edit.slot) <;>
      simp only [a, b, Option.map_none, Option.map_some, OptionRel] at writes ⊢
    simp only [PairwisePrograms.Related, encode_write]
    apply StageSimulation.write_related related owner key
    rename_i first second
    cases first <;> cases second <;> simp only [OptionRel, Option.map_none, Option.map_some] at writes ⊢
    exact (TypedCoeffectReplay.packed_related (Yield := Yield ops) observe key _ _).mpr writes

private theorem word_self_related (observe : ∀ key, Setoid (V key)) (word : List (Edit Name V))
    {before after : R} (called : runWord word before = some after)
    (self : PairwisePrograms.Related (ops := ops) observe before before) :
    PairwisePrograms.Related (ops := ops) observe after after := by
  letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
  induction word generalizing before with
  | nil =>
    change some before = some after at called
    cases Option.some.inj called
    exact self
  | cons head tail ih =>
    obtain ⟨middle, applied, rest⟩ := Option.bind_eq_some_iff.mp called
    obtain ⟨_, output, _, _, rfl⟩ := edit_success applied
    apply ih rest
    simp only [PairwisePrograms.Related, encode_write]
    exact StageSimulation.write_related self _ _ (PartialObservedMapClosure.option_refl _ _)

private theorem related_after_words (observe : ∀ key, Setoid (V key)) {before left right : R}
    {first second : List (Edit Name V)} (leftRun : runWord first before = some left)
    (rightRun : runWord second before = some right)
    (related : (observation observe).r (tablesOf left) (tablesOf right))
    (self : PairwisePrograms.Related (ops := ops) observe before before) : PairwisePrograms.Related (ops := ops) observe left right := by
  letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
  have leftFields := word_controls ops first leftRun
  have rightFields := word_controls ops second rightRun
  have rightSelf := word_self_related observe second rightRun self
  apply Transposition.related_of_controls_tables (Transposition.controls_trans (Transposition.controls_symm leftFields) rightFields) _ rightSelf
  intro owner key
  rw [encoded_table_owner, encoded_table_owner]
  have values := related (owner, key) trivial
  cases a : tablesOf left (owner, key) <;> cases b : tablesOf right (owner, key) <;>
    simp only [a, b, OptionRel, Option.map_none, Option.map_some] at values ⊢
  exact (TypedCoeffectReplay.packed_related (Yield := Yield ops) observe key _ _).mpr values

/-- Two independently executable words of ordinary partial registry edits
have matching definedness in their composed orders. Their successful
compositions preserve the whole native control and compare actual tables.
The initial executions justify the required retained-owner scope. -/
theorem ordinary_words_commute_on_scope (ops : CoeffectOperations V) (observe : ∀ key, Setoid (V key))
    (laws : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    {first second : Name} {firstComponent secondComponent : Calculus.Component Key Code}
    (different : first ≠ second) (separate : Transposition.Separated firstComponent secondComponent)
    {before : R} {firstWord secondWord : List (Edit Name V)}
    (leftAllowed : ∀ edit ∈ firstWord, Admitted ops first firstComponent edit)
    (rightAllowed : ∀ edit ∈ secondWord, Admitted ops second secondComponent edit)
    (leftPresent : OwnersPresent before firstWord) (rightPresent : OwnersPresent before secondWord)
    (self : PairwisePrograms.Related (ops := ops) observe before before) :
    OptionRel (PairwisePrograms.Related (ops := ops) observe)
      (runWord (secondWord ++ firstWord) before) (runWord (firstWord ++ secondWord) before) := by
  have allPresent (a b : List (Edit Name V)) (firstPresent : OwnersPresent before a)
      (secondPresent : OwnersPresent before b) : OwnersPresent before (a ++ b) := by
    intro edit member
    rcases List.mem_append.mp member with left | right
    · exact firstPresent edit left
    · exact secondPresent edit right
  have commute := generated_words_commute ops observe laws different separate
    (table_word_generated ops first firstComponent firstWord leftAllowed)
    (table_word_generated ops second secondComponent secondWord rightAllowed)
  have compared := commute (tablesOf before) (tablesOf before) ((observation observe).refl _)
  change OptionRel (observation observe).r
    (compose (tableWord firstWord) (tableWord secondWord) (tablesOf before))
    (compose (tableWord secondWord) (tableWord firstWord) (tablesOf before)) at compared
  rw [← table_word_append, ← table_word_append,
    ← word_projection ops _ _ (allPresent _ _ rightPresent leftPresent),
    ← word_projection ops _ _ (allPresent _ _ leftPresent rightPresent)] at compared
  cases a : runWord (secondWord ++ firstWord) before <;> cases b : runWord (firstWord ++ secondWord) before <;>
    simp only [a, b, Option.map_none, Option.map_some, OptionRel] at compared ⊢
  exact related_after_words observe a b compared self

theorem ordinary_words_commute (ops : CoeffectOperations V) (observe : ∀ key, Setoid (V key))
    (laws : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    {first second : Name} {firstComponent secondComponent : Calculus.Component Key Code}
    (different : first ≠ second) (separate : Transposition.Separated firstComponent secondComponent)
    {before left right : R} {firstWord secondWord : List (Edit Name V)}
    (leftAllowed : ∀ edit ∈ firstWord, Admitted ops first firstComponent edit)
    (rightAllowed : ∀ edit ∈ secondWord, Admitted ops second secondComponent edit)
    (originalLeft : runWord firstWord before = some left) (originalRight : runWord secondWord before = some right)
    (self : PairwisePrograms.Related (ops := ops) observe before before) :
    OptionRel (PairwisePrograms.Related (ops := ops) observe)
      (runWord (secondWord ++ firstWord) before) (runWord (firstWord ++ secondWord) before) :=
  ordinary_words_commute_on_scope ops observe laws different separate leftAllowed rightAllowed
    (owners_present_of_run ops firstWord originalLeft) (owners_present_of_run ops secondWord originalRight) self

section NativeGraph
open PairwiseOperations (table_and_route undo_operate_eq_write)

/-- On the declared owner's row a successful frozen provision reevaluates
the actual primitive with its native continuation and saved restriction. -/
theorem provision_of_run {program : Code → Instruction Name ops Code} {actor : Name} {code : Code}
    {before after : R} {key : Key} {value : V key} {row : Fiber Name V Code}
    (action : (program code).action = .provide key value) (found : before actor = some row)
    (declared : row.component.provides key = true) (called : runEdit (.provide actor key value) before = some after) :
    Land program actor code before after (.restrict actor key) ((program code).next (.provision key value)) := by
  cases binding : row.table key with
  | none =>
    have output : after = write before actor key (some value) := by
      simpa [runEdit, Edit.apply, Edit.slot, tablesOf, tableAt, found, binding] using called.symm
    rw [output]
    exact .provide _ _ _ _ _ _ action found declared binding
  | some _ => simp [runEdit, Edit.apply, Edit.slot, tablesOf, tableAt, found, binding] at called

/-- A successful forward coeffect edit at the fixed route reevaluates the
actual typed callback. The native rule yields the newly captured inverse
and selects the continuation from the actual returned outcome. -/
theorem operation_of_run {program : Code → Instruction Name ops Code} {actor owner : Name} {code : Code}
    {before after : R} {key : Key} {name : ops.Name key} {argument : ops.Argument key name}
    (action : (program code).action = .operate key name argument) (route : bindingOwner before actor key = some owner)
    (called : runEdit (.operate owner key (PartialCoeffectLifting.forward (ops.operation key name argument))) before = some after) :
    ∃ inverse outcome, Land program actor code before after (.operate owner key inverse)
      ((program code).next (.operation key name outcome)) := by
  obtain ⟨row, newBinding, found, applied, rfl⟩ := edit_success called
  cases binding : tableAt before owner key with
  | none => simp [Edit.apply, Edit.slot, tablesOf, binding] at applied
  | some input =>
    cases call : (ops.operation key name argument).run input with
    | none => simp [Edit.apply, Edit.slot, tablesOf, binding, PartialCoeffectLifting.forward, call] at applied
    | some result =>
      obtain ⟨value, captured, reply⟩ := result
      have same : some value = newBinding := by
        simpa [Edit.apply, Edit.slot, tablesOf, binding, PartialCoeffectLifting.forward, call] using applied
      subst newBinding
      exact ⟨captured, reply, .operate _ _ _ _ _ _ _ _ _ _ _ action (by simp [Edit.slot, location, route, binding]) call⟩

/-- The ordinary restriction descriptor is exactly the saved restriction's
strict native application. -/
theorem restriction_of_run {before after : R} {owner : Name} {key : Key}
    (called : runEdit (.restrict owner key) before = some after) :
    InverseDefined before (.restrict owner key) ∧ after = undo (.restrict owner key) before := by
  obtain ⟨row, value, found, applied, rfl⟩ := edit_success called
  cases binding : tableAt before owner key with
  | none => simp [Edit.apply, Edit.slot, tablesOf, binding] at applied
  | some old =>
    have same : (none : Option (V key)) = value := by
      simpa [Edit.apply, Edit.slot, tablesOf, binding] using applied
    subst value
    exact ⟨by simp [InverseDefined, binding], rfl⟩

theorem operation_inverse_of_run {before after : R} {owner : Name} {key : Key} {inverse : PartialMap (V key)}
    (called : runEdit (.operate owner key inverse) before = some after) :
    InverseDefined before (.operate owner key inverse) ∧ after = undo (.operate owner key inverse) before := by
  obtain ⟨row, value, found, applied, rfl⟩ := edit_success called
  cases binding : tableAt before owner key with
  | none => simp [Edit.apply, Edit.slot, tablesOf, binding] at applied
  | some input =>
    cases call : inverse input with
    | none => simp [Edit.apply, Edit.slot, tablesOf, binding, call] at applied
    | some output =>
      have same : some output = value := by simpa [Edit.apply, Edit.slot, tablesOf, binding, call] using applied
      subst value
      exact ⟨⟨input, output, binding, call⟩, (undo_operate_eq_write binding call).symm⟩

end NativeGraph

end Cordis.Repairs.PairwiseRegistry
