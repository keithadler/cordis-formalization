import Cordis.Repairs.PairwiseOperations
import Cordis.Repairs.PairwiseAllocation
import Cordis.Repairs.PairwiseForward
import Cordis.Repairs.IncarnationReplay
import Cordis.TypedReplayContracts

/-! The table part of mixed native words. Addressed slots are the coordinates
of actual retained registry tables. Provision and restriction keep their
opposite domains, and operation inverses keep each callback's partial domain. -/
namespace Cordis.Repairs.PairwiseSlots
open PartialCoeffectLifting (PartialMap compose Table)
open PartialInverseObservation (MapRelated)
open PartialObservedMapClosure (Maps Commutes)
open PartialMapClosure (Generated)
open PartialCoeffectIndependenceContracts (tableSetoid)
open PaperEffectEquations (CoeffectOperations)
open Iterators (OptionRel)
open Coeffects (update update_same update_other)

universe u
variable {Name Key Code : Type u} {V : Key → Type u}
variable [DecidableEq Name] [DecidableEq Key]
local notation "Slot" => Name × Key
abbrev Tables (Name : Type u) {Key : Type u} (V : Key → Type u) := Table (fun slot : Name × Key => V slot.2)
local notation "ST" => Tables Name V

def observation (observe : ∀ key, Setoid (V key)) : Setoid ST :=
  tableSetoid (fun slot => observe slot.2) (fun _ => True)

/-- One native table edit, with the partial domain at its actual coordinate. -/
inductive Edit (Name : Type u) {Key : Type u} (V : Key → Type u) where
  | provide (owner : Name) (key : Key) (value : V key)
  | restrict (owner : Name) (key : Key)
  | operate (owner : Name) (key : Key) (operation : PartialMap (V key))

def Edit.slot : Edit Name V → Slot
  | .provide owner key _ | .restrict owner key | .operate owner key _ => (owner, key)

def Edit.apply : (edit : Edit Name V) → PartialMap (Option (V edit.slot.2))
  | .provide _ _ value => fun
    | none => some (some value)
    | some _ => none
  | .restrict _ _ => fun
    | none => none
    | some _ => some none
  | .operate _ _ operation => fun slot => (slot.bind operation).map some

def Edit.run (edit : Edit Name V) : PartialMap ST :=
  fun tables => (edit.apply (tables edit.slot)).map (fun result => update edit.slot result tables)

def Admitted (ops : CoeffectOperations V) (actor : Name) (component : Calculus.Component Key Code) :
    Edit Name V → Prop
  | .provide owner key _ | .restrict owner key => owner = actor ∧ component.provides key = true
  | .operate _ key operation => (component.provides key = true ∨ component.requires key = true) ∧
    TypedReplayContracts.Generator ops key operation

abbrev Generator (ops : CoeffectOperations V) (actor : Name) (component : Calculus.Component Key Code)
    (map : PartialMap ST) := ∃ edit, Admitted ops actor component edit ∧ map = edit.run

omit [DecidableEq Name] in
theorem apply_respects (ops : CoeffectOperations V) (observe : ∀ key, Setoid (V key))
    (laws : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    {actor : Name} {component : Calculus.Component Key Code} {edit : Edit Name V}
    (allowed : Admitted ops actor component edit) :
    MapRelated (OptionRel (observe edit.slot.2).r) edit.apply edit.apply := by
  intro before after related
  cases edit with
  | provide owner key value =>
    cases before <;> cases after <;> simp only [OptionRel] at related ⊢
    · exact (observe key).refl value
    · exact True.intro
  | restrict => cases before <;> cases after <;> simp_all [OptionRel, Edit.apply]
  | operate owner key operation =>
    cases before with
    | none => cases after <;> simp_all [OptionRel, Edit.apply]
    | some input =>
      cases after with
      | none => simp [OptionRel] at related
      | some probe =>
        have prior := (TypedReplayContracts.key_laws ops observe key (laws key)).respects operation allowed.2
          input probe related
        change OptionRel (OptionRel (observe key).r) ((operation input).map some) ((operation probe).map some)
        cases a : operation input <;> cases b : operation probe <;> simp_all [OptionRel]

theorem run_respects (ops : CoeffectOperations V) (observe : ∀ key, Setoid (V key))
    (laws : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    {actor : Name} {component : Calculus.Component Key Code} {edit : Edit Name V}
    (allowed : Admitted ops actor component edit) : Maps (observation observe) edit.run edit.run := by
  intro before after related
  have moves := apply_respects ops observe laws allowed (before edit.slot) (after edit.slot) (related edit.slot trivial)
  unfold Edit.run
  cases left : edit.apply (before edit.slot) <;> cases right : edit.apply (after edit.slot) <;>
    simp only [left, right, Option.map_none, Option.map_some, OptionRel] at moves ⊢
  exact PartialCoeffectProvision.update_options_related (Value := fun slot : Slot => V slot.2)
    (fun slot => (observe slot.2).r) (fun _ => True) _ related moves

private theorem different_slots {first second : Edit Name V} (different : first.slot ≠ second.slot) :
    compose first.run second.run = compose second.run first.run := by
  funext tables
  unfold compose Edit.run
  have reverse : second.slot ≠ first.slot := Ne.symm different
  cases l : first.apply (tables first.slot) <;> cases r : second.apply (tables second.slot) <;>
    simp only [l, r, Option.map_none, Option.map_some, Option.bind_none, Option.bind_some,
      update_other _ _ _ _ different, update_other _ _ _ _ reverse]
  congr 1
  funext slot
  by_cases leftSlot : slot = first.slot
  · subst slot
    simp [update_same, update_other, different]
  · by_cases rightSlot : slot = second.slot
    · subst slot
      simp [update_same, update_other, reverse]
    · simp [update_other, leftSlot, rightSlot]

private theorem same_slot_run (owner : Name) (key : Key) (first second : PartialMap (V key)) (tables : ST) :
    compose (Edit.operate owner key first).run (Edit.operate owner key second).run tables =
      ((tables (owner, key)).bind (fun input => (second input).bind first)).map
        (fun final => update (owner, key) (some final) tables) := by
  cases binding : tables (owner, key) with
  | none => simp [compose, Edit.run, Edit.slot, Edit.apply, binding]
  | some input =>
    cases step : second input <;>
      simp [compose, Edit.run, Edit.slot, Edit.apply, binding, step,
        PartialCoeffectLifting.update_overwrite (Value := fun slot : Slot => V slot.2),
        Option.map_map, Function.comp_def]

private theorem operations_same_slot (ops : CoeffectOperations V) (observe : ∀ key, Setoid (V key))
    {owner : Name} {key : Key} {first second : PartialMap (V key)}
    (laws : PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (left : TypedReplayContracts.Generator ops key first) (right : TypedReplayContracts.Generator ops key second) :
    Commutes (observation observe) (Edit.operate owner key first).run (Edit.operate owner key second).run := by
  intro before after related
  let slot : Slot := (owner, key)
  have slotRelated := related slot trivial
  rw [same_slot_run, same_slot_run]
  change OptionRel (observation observe).r
    (((before slot).bind (fun input => (second input).bind first)).map (fun final => update slot (some final) before))
    (((after slot).bind (fun input => (first input).bind second)).map (fun final => update slot (some final) after))
  cases old : before slot with
  | none =>
    cases new : after slot with
    | none => exact True.intro
    | some value => simp [old, new, OptionRel] at slotRelated
  | some input =>
    cases new : after slot with
    | none => simp [old, new, OptionRel] at slotRelated
    | some probe =>
      have values : (observe key).r input probe := by simpa only [old, new, OptionRel] using slotRelated
      have moved := (TypedReplayContracts.key_laws ops observe key laws).commutes first second left right input probe values
      change OptionRel (observe key).r ((second input).bind first) ((first probe).bind second) at moved
      cases l : (second input).bind first <;> cases r : (first probe).bind second <;>
        simp only [l, r, Option.bind_some, Option.map_none, Option.map_some, OptionRel] at moved ⊢
      exact PartialCoeffectLifting.update_related (Value := fun slot : Slot => V slot.2)
        (fun slot => (observe slot.2).r) (fun _ => True) slot related moved

omit [DecidableEq Name] [DecidableEq Key] in
private theorem own_slot_separated (ops : CoeffectOperations V) {firstActor secondActor owner : Name}
    {firstComponent secondComponent : Calculus.Component Key Code} {key : Key} {other : Edit Name V}
    (different : firstActor ≠ secondActor) (separate : Transposition.Separated firstComponent secondComponent)
    (own : owner = firstActor) (provides : firstComponent.provides key = true)
    (allowed : Admitted ops secondActor secondComponent other) : (owner, key) ≠ other.slot := by
  intro same
  cases other with
  | provide secondOwner secondKey _ | restrict secondOwner secondKey =>
    have sameOwner : owner = secondOwner := congrArg Prod.fst same
    exact different (own.symm.trans (sameOwner.trans allowed.1))
  | operate secondOwner secondKey operation =>
    have sameKey : key = secondKey := congrArg Prod.snd same
    subst secondKey
    rcases allowed.1 with provided | required
    · rw [separate.provisions key provides] at provided
      contradiction
    · rw [separate.left_provision key provides] at required
      contradiction

private theorem commutes_of_other_slot (ops : CoeffectOperations V) (observe : ∀ key, Setoid (V key))
    (laws : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    {firstActor secondActor : Name} {firstComponent secondComponent : Calculus.Component Key Code}
    {first second : Edit Name V} (left : Admitted ops firstActor firstComponent first)
    (right : Admitted ops secondActor secondComponent second) (different : first.slot ≠ second.slot) :
    Commutes (observation observe) first.run second.run := by
  unfold Commutes
  rw [different_slots different]
  exact PartialObservedMapClosure.maps_compose _ (run_respects ops observe laws right) (run_respects ops observe laws left)

/-- At different physical slots the two edits commute literally. At one
shared slot actor separation excludes both provisions and restrictions,
leaving only the laws for actual coeffect forwards and captures. -/
theorem edits_commute (ops : CoeffectOperations V) (observe : ∀ key, Setoid (V key))
    (laws : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    {firstActor secondActor : Name} {firstComponent secondComponent : Calculus.Component Key Code}
    (different : firstActor ≠ secondActor) (separate : Transposition.Separated firstComponent secondComponent)
    {first second : Edit Name V} (left : Admitted ops firstActor firstComponent first)
    (right : Admitted ops secondActor secondComponent second) : Commutes (observation observe) first.run second.run := by
  apply Classical.byCases (p := first.slot = second.slot)
  · intro same
    cases first with
    | provide _ _ _ | restrict _ _ =>
      exact False.elim (own_slot_separated ops different separate left.1 left.2 right same)
    | operate leftOwner leftKey first =>
      cases second with
      | provide _ _ _ | restrict _ _ =>
        exact False.elim (own_slot_separated ops (Ne.symm different) separate.symm right.1 right.2 left same.symm)
      | operate rightOwner rightKey second =>
        have owner : leftOwner = rightOwner := congrArg Prod.fst same
        have key : leftKey = rightKey := congrArg Prod.snd same
        subst rightOwner rightKey
        exact operations_same_slot ops observe (laws leftKey) left.2 right.2
  · exact commutes_of_other_slot ops observe laws left right

/-- Arbitrarily interleaved partial table words commute across separated
actors. Each word may mix provision, operation and their saved inverses.
The result compares both orders on related inputs, including failures. -/
theorem generated_words_commute (ops : CoeffectOperations V) (observe : ∀ key, Setoid (V key))
    (laws : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    {firstActor secondActor : Name} {firstComponent secondComponent : Calculus.Component Key Code}
    (different : firstActor ≠ secondActor) (separate : Transposition.Separated firstComponent secondComponent)
    {first second : PartialMap ST} (left : Generated (Generator ops firstActor firstComponent) first)
    (right : Generated (Generator ops secondActor secondComponent) second) :
    Commutes (observation observe) first second := by
  have respects (actor : Name) (component : Calculus.Component Key Code) (map : PartialMap ST)
      (generator : Generator ops actor component map) : Maps (observation observe) map map := by
    obtain ⟨edit, allowed, rfl⟩ := generator
    exact run_respects ops observe laws allowed
  apply PartialObservedMapClosure.generated_commutes _ (respects _ _) (respects _ _) _ left right
  rintro _ _ ⟨first, eligible, rfl⟩ ⟨second, ready, rfl⟩
  exact edits_commute ops observe laws different separate eligible ready

/-- A successful foreign table word retains the local binding and induces
a word of actual coeffect generators at that binding. Other coordinates
contribute identity. A foreign provision or restriction is excluded from
the local declared keys by the actors' separated interfaces. -/
theorem generated_at_retained_slot (ops : CoeffectOperations V)
    {foreignActor owner : Name} {localComponent foreignComponent : Calculus.Component Key Code}
    {key : Key} (declared : localComponent.provides key = true ∨ localComponent.requires key = true)
    (separate : Transposition.Separated localComponent foreignComponent) {map : PartialMap ST}
    (generated : Generated (Generator ops foreignActor foreignComponent) map) :
    ∀ before after, map before = some after → ∀ input, before (owner, key) = some input →
      ∃ output, after (owner, key) = some output ∧ ∃ word : PartialMap (V key),
        Generated (TypedReplayContracts.Generator ops key) word ∧ word input = some output := by
  induction generated with
  | identity =>
    intro before after applied input occupied
    cases Option.some.inj applied
    exact ⟨input, occupied, some, .identity, rfl⟩
  | generator admitted =>
    obtain ⟨edit, allowed, rfl⟩ := admitted
    intro before after applied input occupied
    obtain ⟨changed, called, rfl⟩ := Option.map_eq_some_iff.mp applied
    by_cases same : (owner, key) = edit.slot
    · cases edit with
      | provide foreignOwner foreignKey value | restrict foreignOwner foreignKey =>
        have keyEq : key = foreignKey := congrArg Prod.snd same
        subst foreignKey
        have provides : foreignComponent.provides key = true := allowed.2
        rcases declared with localProvided | localRequired
        · rw [separate.provisions key localProvided] at provides
          contradiction
        · rw [separate.right_provision key provides] at localRequired
          contradiction
      | operate foreignOwner foreignKey modify =>
        have keyEq : key = foreignKey := congrArg Prod.snd same
        have ownerEq : owner = foreignOwner := congrArg Prod.fst same
        subst foreignKey foreignOwner
        simp only [Edit.apply, Edit.slot, occupied, Option.bind_some] at called
        obtain ⟨output, success, rfl⟩ := Option.map_eq_some_iff.mp called
        exact ⟨output, update_same _ _ _, modify, .generator allowed.2, success⟩
    · exact ⟨input, (update_other _ _ _ _ same).trans occupied, some, .identity, rfl⟩
  | composition _ _ outer inner =>
    intro before after applied input occupied
    obtain ⟨middle, first, second⟩ := Option.bind_eq_some_iff.mp applied
    obtain ⟨middleValue, middleBound, earlier, earlierWord, earlierCall⟩ := inner before middle first input occupied
    obtain ⟨finalValue, finalBound, later, laterWord, laterCall⟩ := outer middle after second middleValue middleBound
    exact ⟨finalValue, finalBound, compose later earlier, .composition laterWord earlierWord,
      by simp [compose, earlierCall, laterCall]⟩

/-- The full foreign table word preserves an operation's yield at its
retained route. A failed local callback remains failed. A successful one
preserves the exact outcome and the partial behavior of its saved inverse. -/
theorem operation_yield_after_generated (ops : CoeffectOperations V) (observe : ∀ key, Setoid (V key))
    {foreignActor owner : Name} {localComponent foreignComponent : Calculus.Component Key Code}
    {key : Key} (declared : localComponent.provides key = true ∨ localComponent.requires key = true)
    (separate : Transposition.Separated localComponent foreignComponent)
    (laws : PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (name : ops.Name key) (argument : ops.Argument key name) {map : PartialMap ST}
    (generated : Generated (Generator ops foreignActor foreignComponent) map)
    {before after : ST} {input : V key} (applied : map before = some after) (retained : before (owner, key) = some input) :
    ∃ output, after (owner, key) = some output ∧
      OptionRel (fun new old => MapRelated (observe key).r new.2.1 old.2.1 ∧ new.2.2 = old.2.2)
        ((ops.operation key name argument).run output) ((ops.operation key name argument).run input) := by
  obtain ⟨output, bound, word, generatedAt, called⟩ :=
    generated_at_retained_slot ops declared separate generated before after applied input retained
  exact ⟨output, bound, DependentCoeffectExchange.yield_after_generated_at_key ops observe key name argument laws generatedAt called⟩

theorem generated_keeps_own_slot (ops : CoeffectOperations V)
    {localActor foreignActor : Name} {localComponent foreignComponent : Calculus.Component Key Code}
    {key : Key} (provided : localComponent.provides key = true) (different : localActor ≠ foreignActor)
    (separate : Transposition.Separated localComponent foreignComponent) {map : PartialMap ST}
    (generated : Generated (Generator ops foreignActor foreignComponent) map) :
    ∀ before after, map before = some after → after (localActor, key) = before (localActor, key) := by
  induction generated with
  | identity => intro before after applied; cases Option.some.inj applied; rfl
  | generator valid =>
    obtain ⟨edit, allowed, rfl⟩ := valid
    intro before after applied
    obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp applied
    exact update_other _ _ _ _ (own_slot_separated ops different separate rfl provided allowed)
  | composition _ _ outer inner =>
    intro before after applied
    obtain ⟨middle, first, second⟩ := Option.bind_eq_some_iff.mp applied
    exact (outer middle after second).trans (inner before middle first)

/-- A separated word cannot fill an empty slot at a key of the local
interface. Provision is excluded by separation, and a scalar operation
requires an existing binding at its own slot. -/
theorem generated_keeps_empty_slot (ops : CoeffectOperations V)
    {foreignActor owner : Name} {localComponent foreignComponent : Calculus.Component Key Code}
    {key : Key} (declared : localComponent.provides key = true ∨ localComponent.requires key = true)
    (separate : Transposition.Separated localComponent foreignComponent) {map : PartialMap ST}
    (generated : Generated (Generator ops foreignActor foreignComponent) map) :
    ∀ before after, map before = some after → before (owner, key) = none → after (owner, key) = none := by
  induction generated with
  | identity =>
    intro before after applied vacant
    cases Option.some.inj applied
    exact vacant
  | generator admitted =>
    obtain ⟨edit, allowed, rfl⟩ := admitted
    intro before after applied vacant
    obtain ⟨changed, called, rfl⟩ := Option.map_eq_some_iff.mp applied
    by_cases same : (owner, key) = edit.slot
    · have empty : before edit.slot = none := same ▸ vacant
      cases edit with
      | provide foreignOwner foreignKey value =>
        have eq : key = foreignKey := congrArg Prod.snd same
        subst foreignKey
        have provides : foreignComponent.provides key = true := allowed.2
        rcases declared with own | required
        · rw [separate.provisions key own] at provides
          contradiction
        · rw [separate.right_provision key provides] at required
          contradiction
      | restrict | operate => simp [Edit.apply, empty] at called
    · exact (update_other _ _ _ _ same).trans vacant
  | composition _ _ outer inner =>
    intro before after applied vacant
    obtain ⟨middle, first, second⟩ := Option.bind_eq_some_iff.mp applied
    exact outer middle after second (inner before middle first vacant)

section Native
open TypedRegistry
open PairwiseOperations (declared_key table_and_route undo_operate_eq_write)
variable {ops : CoeffectOperations V}
local notation "R" => Registry Name V Code
local notation "I" => Inverse Name V
local notation "Program" => Code → Instruction Name ops Code

def tablesOf (state : R) : ST := fun slot => tableAt state slot.1 slot.2

theorem tableAt_write_other_key (state : R) (owner reader : Name) (key other : Key) (distinct : key ≠ other)
    (value : Option (V key)) : tableAt (write state owner key value) reader other = tableAt state reader other := by
  by_cases same : reader = owner
  · subst reader
    cases found : state owner <;> simp [tableAt, write, TypedRegistry.modify, found, distinct]
  · simp [tableAt, write, TypedRegistry.modify, same]

theorem tablesOf_write (state : R) (owner : Name) (key : Key) (value : Option (V key))
    (present : state owner ≠ none) : tablesOf (write state owner key value) = update (owner, key) value (tablesOf state) := by
  funext slot
  obtain ⟨other, query⟩ := slot
  by_cases sameOwner : other = owner
  · subst other
    cases found : state owner with
    | none => exact False.elim (present found)
    | some row =>
      by_cases sameKey : query = key
      · subst query
        simp [tablesOf, tableAt, write, TypedRegistry.modify, found]
      · simp [tablesOf, tableAt, write, TypedRegistry.modify, found, update, sameKey, Ne.symm sameKey]
  · simp [tablesOf, tableAt, write, TypedRegistry.modify, update, sameOwner]

omit [DecidableEq Key] in
theorem tablesOf_birth (state : R) (child : Name) (component : Calculus.Component Key Code)
    (parent : Option Name) (vacant : state child = none) :
    tablesOf (put state child (fresh component parent)) = tablesOf state := by
  funext slot
  obtain ⟨owner, key⟩ := slot
  by_cases same : owner = child
  · subst owner
    simp [tablesOf, tableAt, put, fresh, vacant]
  · simp [tablesOf, tableAt, put, same]

omit [DecidableEq Key] in
theorem tablesOf_retire (state : R) (child : Name) : tablesOf (retire state child) = tablesOf state := by
  funext slot
  obtain ⟨owner, key⟩ := slot
  by_cases same : owner = child
  · subst owner
    cases found : state child <;> simp [tablesOf, tableAt, retire, TypedRegistry.modify, found]
  · simp [tablesOf, tableAt, retire, TypedRegistry.modify, same]

/-- The actual typed landing supplies its slot and actor interface. The
forward generator is derived from that landing's actual operation. -/
theorem projects_landing {program : Program} {actor : Name} {code : Code} {before after : R}
    {token : I} {next : Option Code} {row : Fiber Name V Code} (present : before actor = some row)
    (landed : Land program actor code before after token next) :
    ∃ map, Generated (Generator ops actor row.component) map ∧ map (tablesOf before) = some (tablesOf after) := by
  cases landed with
  | unit => exact ⟨some, .identity, rfl⟩
  | instantiate _ _ _ component child _ ready =>
    exact ⟨some, .identity, congrArg some (tablesOf_birth before child component (some actor) ready.1).symm⟩
  | provide _ _ _ own key value _ found declared absent =>
    have same := Option.some.inj (found.symm.trans present)
    subst own
    refine ⟨(Edit.provide actor key value).run, .generator ⟨.provide actor key value, ⟨rfl, declared⟩, rfl⟩, ?_⟩
    rw [tablesOf_write before actor key _ (by simp [present])]
    simp [Edit.run, Edit.apply, Edit.slot, tablesOf, tableAt, present, absent]
  | operate _ _ _ key name argument owner input output inverse result _ located returned =>
    let op := ops.operation key name argument
    have bound := (table_and_route located).2
    have retained : before owner ≠ none := by
      intro missing
      simp [tableAt, missing] at bound
    refine ⟨(Edit.operate owner key (PartialCoeffectLifting.forward op)).run,
      .generator ⟨.operate owner key (PartialCoeffectLifting.forward op),
        ⟨declared_key present located, name, argument, .forward⟩, rfl⟩, ?_⟩
    rw [tablesOf_write before owner key _ retained]
    simp [Edit.run, Edit.apply, Edit.slot, tablesOf, bound, PartialCoeffectLifting.forward, op, returned]

/-- Project an inverse from its real capturing landing, on a probe where it
is genuinely applicable. The operation family and the actor's access come
from its native origin, with no inference from the total completed undo. -/
theorem projects_capture {program : Program} {actor : Name} {code : Code} {origin captured probe : R}
    {token : I} {next : Option Code} {row : Fiber Name V Code} (present : origin actor = some row)
    (landed : Land program actor code origin captured token next) (defined : InverseDefined probe token) :
    ∃ map, Generated (Generator ops actor row.component) map ∧ map (tablesOf probe) = some (tablesOf (undo token probe)) := by
  cases landed with
  | unit => exact ⟨some, .identity, rfl⟩
  | instantiate _ _ _ _ child _ _ => exact ⟨some, .identity, congrArg some (tablesOf_retire probe child).symm⟩
  | provide _ _ _ own key value _ found declared absent =>
    have same := Option.some.inj (found.symm.trans present)
    subst own
    cases existing : tableAt probe actor key with
    | none => exact False.elim (defined existing)
    | some input =>
      have retained : probe actor ≠ none := by
        intro missing
        simp [tableAt, missing] at existing
      refine ⟨(Edit.restrict actor key).run, .generator ⟨.restrict actor key, ⟨rfl, declared⟩, rfl⟩, ?_⟩
      change _ = some (tablesOf (write probe actor key none))
      rw [tablesOf_write probe actor key _ retained]
      simp [Edit.run, Edit.apply, Edit.slot, tablesOf, existing]
  | operate _ _ _ key name argument owner input output inverse result _ located returned =>
    obtain ⟨probeInput, probeOutput, bound, called⟩ := defined
    have retained : probe owner ≠ none := by
      intro missing
      simp [tableAt, missing] at bound
    refine ⟨(Edit.operate owner key inverse).run,
      .generator ⟨.operate owner key inverse,
        ⟨declared_key present located, name, argument, .inverse input output inverse result returned⟩, rfl⟩, ?_⟩
    rw [undo_operate_eq_write bound called, tablesOf_write probe owner key _ retained]
    simp [Edit.run, Edit.apply, Edit.slot, tablesOf, bound, called]

private theorem guarded_capture_tables (ops : CoeffectOperations V) {token : I} {before after : R}
    {live : Name → Option Nat} {index : Nat}
    (applied : encodeRegistry ops after =
      (IncarnationReplay.Capture.mk (encodeInverse ops token) index).apply live (encodeRegistry ops before)) :
    tablesOf after = tablesOf (undo token before) := by
  cases token with
  | unit | restrict _ _ | operate _ _ _ =>
    exact congrArg tablesOf (encodeRegistry_injective ops (by
      simpa [IncarnationReplay.Capture.apply, encodeInverse] using applied))
  | retire child =>
    by_cases sameBirth : live child = some index
    · exact congrArg tablesOf (encodeRegistry_injective ops (by
        simpa [IncarnationReplay.Capture.apply, encodeInverse, sameBirth, undo] using applied))
    · have unchanged : after = before := encodeRegistry_injective ops (by
        simpa [IncarnationReplay.Capture.apply, encodeInverse, sameBirth] using applied)
      rw [unchanged]
      exact (tablesOf_retire before child).symm

/-- The forward witnesses and genuinely applicable incarnation-checked
inverse witnesses of an actor's mixed words. For a saved token the access
interface is taken at its native capturing landing. -/
inductive NativeMove (program : Program) (actor : Name) (component : Calculus.Component Key Code) : R → R → Prop where
  | forward {code before after token next row} : before actor = some row → row.component = component →
    Land program actor code before after token next → NativeMove program actor component before after
  | inverse {code origin captured before after token next row} (live : Name → Option Nat) (index : Nat) :
    origin actor = some row → row.component = component → Land program actor code origin captured token next →
    InverseDefined before token → encodeRegistry ops after =
      (IncarnationReplay.Capture.mk (encodeInverse ops token) index).apply live (encodeRegistry ops before) →
    NativeMove program actor component before after

theorem projects_move {program : Program} {actor : Name} {component : Calculus.Component Key Code} {before after : R}
    (move : NativeMove program actor component before after) :
    ∃ map, Generated (Generator ops actor component) map ∧ map (tablesOf before) = some (tablesOf after) := by
  cases move with
  | forward found same landed =>
    rw [← same]
    exact projects_landing found landed
  | inverse _ _ found same landed defined applied =>
    rw [← same]
    obtain ⟨map, generated, projection⟩ := projects_capture found landed defined
    exact ⟨map, generated, projection.trans (congrArg some (guarded_capture_tables ops applied).symm)⟩

/-- Successful registry executions of finite generated words. The native
preconditions at intermediate states come from each successful move. -/
inductive NativeWord (program : Program) (actor : Name) (component : Calculus.Component Key Code) : R → R → Prop where
  | nil (state) : NativeWord program actor component state state
  | cons {before middle after} : NativeMove program actor component before middle →
    NativeWord program actor component middle after → NativeWord program actor component before after

/-- Mixed native moves retain the structural domains of already present
actors and providers. Guarded retirements either apply the native token
or act as identity when its recorded child is stale. -/
theorem NativeMove.keeps {program : Program} {actor : Name} {component : Calculus.Component Key Code}
    {before after : R} (move : NativeMove program actor component before after) :
    ScopedRollback.Keeps ops before after := by
  cases move with
  | forward _ _ landed => exact .land landed
  | @inverse code origin captured before after token next row live stamp _ _ _ _ applied =>
    cases selected : token with
    | unit | restrict | operate =>
      have same : after = undo token before := encodeRegistry_injective ops (by
        simpa [selected, IncarnationReplay.Capture.apply, encode_undo, encodeInverse] using applied)
      rw [same]
      exact .undo _ _ _
    | retire child =>
      by_cases actual : live child = some stamp
      · have same : after = undo (.retire child) before := encodeRegistry_injective ops (by
          simpa [selected, IncarnationReplay.Capture.apply, encode_undo, encodeInverse, actual] using applied)
        rw [same]
        exact .undo _ _ _
      · have same : after = before := encodeRegistry_injective ops (by
          simpa [selected, IncarnationReplay.Capture.apply, encodeInverse, actual] using applied)
        rw [same]
        exact .refl _ _

theorem NativeWord.keeps {program : Program} {actor : Name} {component : Calculus.Component Key Code}
    {before after : R} (word : NativeWord program actor component before after) :
    ScopedRollback.Keeps ops before after := by
  induction word with
  | nil => exact .refl _ _
  | cons first _ ih => exact first.keeps.trans ih

theorem projects_native_word {program : Program} {actor : Name} {component : Calculus.Component Key Code} {before after : R}
    (word : NativeWord program actor component before after) :
    ∃ map, Generated (Generator ops actor component) map ∧ map (tablesOf before) = some (tablesOf after) := by
  induction word with
  | nil => exact ⟨some, .identity, rfl⟩
  | cons head _ ih =>
    obtain ⟨first, generated, realized⟩ := projects_move head
    obtain ⟨remaining, valid, finished⟩ := ih
    exact ⟨compose remaining first, .composition valid generated, by simp [compose, realized, finished]⟩

private theorem word_keeps_row {program : Program} {actor reader : Name} {component : Calculus.Component Key Code}
    {before after : R} {row : Fiber Name V Code} (word : NativeWord program actor component before after)
    (found : before reader = some row) : ∃ other, after reader = some other ∧
      other.component = row.component ∧ other.phase.committed = row.phase.committed := by
  obtain ⟨other, present, declarations, _, phase⟩ := word.keeps.row reader row found
  exact ⟨other, present, declarations, phase⟩

/-- Actual foreign words preserve the local operation's routed owner, and
the local partial yield at the new binding. Both results follow from the
native frame and the typed generators rather than an assumed fixed route. -/
theorem operation_yield_after_native_word (observe : ∀ key, Setoid (V key))
    (laws : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    {program : Program} {actor owner foreignActor : Name} {foreignComponent : Calculus.Component Key Code}
    {readRow : Fiber Name V Code} {before after : R} {key : Key} {input : V key}
    (name : ops.Name key) (argument : ops.Argument key name) (reader : before actor = some readRow)
    (separate : Transposition.Separated readRow.component foreignComponent)
    (located : location before actor key = some (owner, input)) (word : NativeWord program foreignActor foreignComponent before after) :
    ∃ output, location after actor key = some (owner, output) ∧
      OptionRel (fun new old => MapRelated (observe key).r new.2.1 old.2.1 ∧ new.2.2 = old.2.2)
        ((ops.operation key name argument).run output) ((ops.operation key name argument).run input) := by
  obtain ⟨finalRow, found, same, phase⟩ := word_keeps_row word reader
  obtain ⟨route, bound⟩ := table_and_route located
  have routed : bindingOwner after actor key = some owner := by
    simpa [bindingOwner, found, same, phase] using (show
      (if readRow.component.provides key then some actor else if readRow.component.requires key then
        readRow.phase.committed.map (fun view => view key) else none) = some owner from by
          simpa [bindingOwner, reader] using route)
  obtain ⟨map, generated, projected⟩ := projects_native_word word
  obtain ⟨output, binding, yields⟩ := operation_yield_after_generated ops observe
    (declared_key reader located) separate (laws key) name argument generated projected bound
  exact ⟨output, by simp [location, routed, show tableAt after owner key = some output from binding], yields⟩

/-- A genuinely failed operation remains failed under a separated mixed
word, whether its routed slot is empty or a bound callback rejects its input. -/
theorem operation_failure_after_native_word (observe : ∀ key, Setoid (V key))
    (laws : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    {program : Program} {actor owner foreignActor : Name} {foreignComponent : Calculus.Component Key Code}
    {row : Fiber Name V Code} {before after : R} {key : Key} {code : Code}
    {name : ops.Name key} {argument : ops.Argument key name}
    (action : (program code).action = .operate key name argument) (found : before actor = some row)
    (declared : row.component.provides key = true ∨ row.component.requires key = true)
    (separate : Transposition.Separated row.component foreignComponent)
    (route : bindingOwner before actor key = some owner)
    (failed : replyAt program actor none code before = none)
    (word : NativeWord program foreignActor foreignComponent before after) :
    replyAt program actor none code after = none := by
  have keptRoute : bindingOwner after actor key = some owner :=
    (word.keeps.bindingOwner found key).trans route
  cases binding : tableAt before owner key with
  | none =>
    obtain ⟨map, generated, applied⟩ := projects_native_word word
    have empty : tableAt after owner key = none :=
      generated_keeps_empty_slot ops declared separate generated _ _ applied binding
    simp [replyAt, action, location, keptRoute, empty]
  | some input =>
    have located : location before actor key = some (owner, input) := by simp [location, route, binding]
    have notReturned : (ops.operation key name argument).run input = none := by
      cases called : (ops.operation key name argument).run input with
      | none => rfl
      | some data =>
        obtain ⟨output, saved, outcome⟩ := data
        simp [replyAt, action, located, called] at failed
    obtain ⟨output, otherLocated, yields⟩ := operation_yield_after_native_word observe laws name argument
      found separate located word
    rw [notReturned] at yields
    cases called : (ops.operation key name argument).run output with
    | none => simp [replyAt, action, otherLocated, called]
    | some _ => simp [OptionRel, called] at yields

/-- A provision retains its actual empty-slot guard after a foreign mixed
word. The selected continuation and restriction are therefore unchanged. -/
theorem rerun_provision_after_native_word {program : Program} {actor foreignActor : Name}
    {foreignComponent : Calculus.Component Key Code} {row : Fiber Name V Code} {before after : R}
    {code : Code} {key : Key} {value : V key} (different : actor ≠ foreignActor)
    (action : (program code).action = .provide key value) (reader : before actor = some row)
    (separate : Transposition.Separated row.component foreignComponent) (provided : row.component.provides key = true)
    (empty : row.table key = none) (word : NativeWord program foreignActor foreignComponent before after) :
    Land program actor code after (write after actor key (some value)) (.restrict actor key)
      ((program code).next (.provision key value)) := by
  obtain ⟨map, generated, projected⟩ := projects_native_word word
  obtain ⟨entry, found, same, _⟩ := word_keeps_row word reader
  have kept := generated_keeps_own_slot ops provided different separate generated _ _ projected
  have absent : entry.table key = none := by simpa [tablesOf, tableAt, found, reader, empty] using kept
  exact .provide _ _ _ entry _ _ action found (by simpa [same] using provided) absent

/-- The exact guard for a fixed allocation after an arbitrary native mixed
word. Only names drawn and provision declarations actually installed by
that word can add obstructions. Retiring a child leaves its reservation. -/
theorem allocation_guard_after_native_word {program : Program} {parent foreignActor draw : Name}
    {foreignComponent childComponent : Calculus.Component Key Code} {parentRow : Fiber Name V Code}
    {before after : R} (parentFound : before parent = some parentRow)
    (word : NativeWord program foreignActor foreignComponent before after) :
    Insertable after draw childComponent (some parent) ↔
      Insertable before draw childComponent (some parent) ∧
      ∀ name row, before name = none → after name = some row →
        PairwiseAllocation.DrawCompatible draw name childComponent row.component := by
  obtain ⟨retainedParent, parentAtEnd, _, _⟩ := word_keeps_row word parentFound
  constructor
  · intro ready
    have vacant : before draw = none := by
      cases found : before draw with
      | none => rfl
      | some row =>
        obtain ⟨_, existsAfter, _, _⟩ := word_keeps_row word found
        rw [ready.1] at existsAfter
        cases existsAfter
    refine ⟨⟨vacant, ?_, ?_⟩, ?_⟩
    · intro name eq
      cases eq
      rw [parentFound]
      exact Option.noConfusion
    · intro name key
      cases found : before name with
      | none => trivial
      | some old =>
        obtain ⟨current, currentFound, component, _⟩ := word_keeps_row word found
        simpa only [currentFound, component] using ready.2.2 name key
    · intro name row _ born
      refine ⟨?_, ?_⟩
      · intro same
        subst name
        rw [ready.1] at born
        cases born
      · intro key provided
        have disjoint := ready.2.2 name key
        rw [born] at disjoint
        exact Bool.eq_false_iff.mpr (disjoint provided)
  · rintro ⟨ready, compatible⟩
    refine ⟨?_, ?_, ?_⟩
    · cases born : after draw with
      | none => rfl
      | some entry => exact False.elim ((compatible draw entry ready.1 born).1 rfl)
    · intro name eq
      cases eq
      rw [parentAtEnd]
      exact Option.noConfusion
    · intro name key
      cases final : after name with
      | none => trivial
      | some row =>
        cases prior : before name with
        | none =>
          intro provided
          rw [(compatible name row prior final).2 key provided]
          exact Bool.noConfusion
        | some old =>
          obtain ⟨other, present, component, _⟩ := word_keeps_row word prior
          have same := Option.some.inj (present.symm.trans final)
          subst row
          simpa only [prior, component] using ready.2.2 name key

/-- The mixed-word guard supplies an actual landing of the original child
at the original draw and keeps the exact saved retirement and next code. -/
theorem rerun_allocation_after_native_word {program : Program} {actor foreignActor draw : Name}
    {row : Fiber Name V Code} {before after allotted : R} {childComponent foreignComponent : Calculus.Component Key Code}
    {code : Code} {next : Option Code} (actorFound : before actor = some row)
    (chosen : (program code).action = .instantiate childComponent)
    (landed : Land program actor code before allotted (.retire draw) next)
    (word : NativeWord program foreignActor foreignComponent before after)
    (compatible : ∀ name entry, before name = none → after name = some entry →
      PairwiseAllocation.DrawCompatible draw name childComponent entry.component) :
    Land program actor code after (put after draw (fresh childComponent (some actor))) (.retire draw) next := by
  cases landed with
  | instantiate _ _ _ actual _ action ready =>
    have same := Action.instantiate.inj (action.symm.trans chosen)
    subst childComponent
    exact .instantiate _ _ _ _ _ action ((allocation_guard_after_native_word actorFound word).mpr ⟨ready, compatible⟩)

/-- All four native primitive yields survive a genuinely executed foreign
mixed word at separated interfaces. The allocating case uses only the
additional name and provision guards of the actual foreign births. -/
theorem rerun_after_native_word (observe : ∀ key, Setoid (V key))
    (laws : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    {program : Program} {actor foreignActor : Name} {foreignComponent : Calculus.Component Key Code}
    {row : Fiber Name V Code} {before after result : R} {code : Code} {token : I} {next : Option Code}
    (found : before actor = some row) (different : actor ≠ foreignActor)
    (separate : Transposition.Separated row.component foreignComponent)
    (localLand : Land program actor code before result token next)
    (foreign : NativeWord program foreignActor foreignComponent before after)
    (compatible : ∀ draw child, token = .retire draw → (program code).action = .instantiate child →
      ∀ name entry, before name = none → after name = some entry →
        PairwiseAllocation.DrawCompatible draw name child entry.component) :
    ∃ moved saved, Land program actor code after moved saved next ∧ PairwiseForward.CaptureRelated observe saved token ∧
      replyAt program actor (capturedChild token) code before =
        replyAt program actor (capturedChild saved) code after := by
  cases localLand with
  | unit _ _ _ action => exact ⟨_, .unit, .unit _ _ _ action, .unit, by simp [replyAt, action]⟩
  | provide _ _ _ source key value action present declared empty =>
    have same := Option.some.inj (present.symm.trans found)
    subst source
    exact ⟨_, .restrict actor key,
      rerun_provision_after_native_word different action found separate declared empty foreign, .restrict actor key,
      by simp [replyAt, action]⟩
  | operate _ _ _ key name argument owner input output inverse outcome action located returned =>
    obtain ⟨movedInput, movedRoute, yields⟩ := operation_yield_after_native_word observe laws name argument
      found separate located foreign
    rw [returned] at yields
    cases called : (ops.operation key name argument).run movedInput with
    | none => simp [called, OptionRel] at yields
    | some result =>
      obtain ⟨movedOutput, saved, reply⟩ := result
      rw [called] at yields
      have sameReply : reply = outcome := yields.2
      subst reply
      exact ⟨_, .operate owner key saved, .operate _ _ _ _ _ _ _ _ _ _ _ action movedRoute called,
        .operate owner key yields.1, by simp [replyAt, action, located, movedRoute, returned, called]⟩
  | instantiate _ _ _ child draw action ready =>
    exact ⟨_, .retire draw, .instantiate _ _ _ _ _ action
      ((allocation_guard_after_native_word found foreign).mpr ⟨ready, compatible draw child rfl action⟩), .retire draw,
      by simp [replyAt, action]⟩

/-- The table projections of actual mixed native words commute for
separated actors. Their registry guards have been realized in the given
executions. The paired projection keeps the genuine domains of all table
edits in both composed orders. -/
theorem native_word_projections_commute (observe : ∀ key, Setoid (V key))
    (laws : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    {program : Program} {first second : Name} {firstComponent secondComponent : Calculus.Component Key Code}
    {before leftAfter rightAfter : R} (different : first ≠ second)
    (separate : Transposition.Separated firstComponent secondComponent)
    (left : NativeWord program first firstComponent before leftAfter)
    (right : NativeWord program second secondComponent before rightAfter) :
    ∃ firstMap secondMap : PartialMap ST,
      firstMap (tablesOf before) = some (tablesOf leftAfter) ∧
      secondMap (tablesOf before) = some (tablesOf rightAfter) ∧
      Commutes (observation observe) firstMap secondMap := by
  obtain ⟨firstMap, firstWord, firstProjection⟩ := projects_native_word left
  obtain ⟨secondMap, secondWord, secondProjection⟩ := projects_native_word right
  exact ⟨firstMap, secondMap, firstProjection, secondProjection,
    generated_words_commute ops observe laws different separate firstWord secondWord⟩

end Native

end Cordis.Repairs.PairwiseSlots
