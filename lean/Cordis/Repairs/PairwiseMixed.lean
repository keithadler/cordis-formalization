import Cordis.Repairs.PairwiseControl

/-! Factorization of native mixed words. Table edits carry their genuine
partial domains. Control edits carry allocation guards and birth stamps.
Their exchange is literal, allowing comparison of the complete words. -/
namespace Cordis.Repairs.PairwiseMixed
open TypedRegistry PairwiseSlots PairwiseRegistry PairwiseControl
open PaperEffectEquations (CoeffectOperations)
open PartialCoeffectLifting (PartialMap compose)
open PartialCoeffectIndependenceContracts (tableSetoid)
open Iterators (OptionRel)

universe u
variable {Name Key Code : Type u} {V : Key → Type u}
variable [DecidableEq Name] [DecidableEq Key] {ops : CoeffectOperations V}
local notation "R" => Registry Name V Code
local notation "SR" => Stamped Name V Code
local notation "E" => Edit Name V
local notation "C" => Control Name Key Code

def runOrdinary (edit : E) (state : SR) : Option SR :=
  (runEdit edit state.1).map (fun output => (output, state.2))

private theorem ordinary_after_birth (ops : CoeffectOperations V) (state : SR) (edit : E)
    {parent child : Name} {payload : Calculus.Component Key Code} {stamp : Nat}
    (different : edit.slot.1 ≠ child) (vacant : state.1 child = none) :
    runOrdinary edit (addBirth state parent child payload stamp) =
      (runOrdinary edit state).map (fun output => addBirth output parent child payload stamp) := by
  have tables := tablesOf_birth state.1 child payload (some parent) vacant
  have atOwner : (addBirth state parent child payload stamp).1 edit.slot.1 = state.1 edit.slot.1 := by
    simp [addBirth, put, different]
  unfold runOrdinary runEdit
  simp only [atOwner]
  change (((state.1 edit.slot.1).bind fun _ =>
      (edit.apply (tablesOf (put state.1 child (fresh payload (some parent))) edit.slot)).map
        (write (put state.1 child (fresh payload (some parent))) edit.slot.1 edit.slot.2)).map
          (fun output => (output, (addBirth state parent child payload stamp).2))) = _
  rw [tables]
  cases found : state.1 edit.slot.1 with
  | none => rfl
  | some row =>
    cases result : edit.apply (tablesOf state.1 edit.slot) with
    | none => rfl
    | some value =>
      have commute : write (put state.1 child (fresh payload (some parent))) edit.slot.1 edit.slot.2 value =
          put (write state.1 edit.slot.1 edit.slot.2 value) child (fresh payload (some parent)) := by
        apply encodeRegistry_injective ops
        simp only [encode_write, encode_put]
        exact Transposition.write_put _ _ _ _ _ _ different
      simp only [Option.bind_some, Option.map_some]
      simp [addBirth, commute]

private theorem ordinary_after_retire (ops : CoeffectOperations V) (state : R) (edit : E) (child : Name) :
    runEdit edit (retire state child) = (runEdit edit state).map (fun out => retire out child) := by
  unfold runEdit
  rw [tablesOf_retire]
  cases found : state edit.slot.1 with
  | none =>
    have absent : retire state child edit.slot.1 = none := by
      by_cases same : edit.slot.1 = child
      · rw [same] at found
        simp [retire, TypedRegistry.modify, same, found]
      · simp [retire, TypedRegistry.modify, same, found]
    simp [absent]
  | some row =>
    obtain ⟨changed, retained⟩ : ∃ changed, retire state child edit.slot.1 = some changed := by
      by_cases same : edit.slot.1 = child
      · rw [same] at found
        simp [retire, TypedRegistry.modify, same, found]
      · simp [retire, TypedRegistry.modify, same, found]
    rw [retained]
    cases result : edit.apply (tablesOf state edit.slot) with
    | none => rfl
    | some value =>
      have commute : write (retire state child) edit.slot.1 edit.slot.2 value =
          retire (write state edit.slot.1 edit.slot.2 value) child := by
        apply encodeRegistry_injective ops
        simp only [encode_write, encode_retire]
        exact Transposition.write_retire _ _ _ _ _
      simp [commute]

private theorem ordinary_after_saved_retire (ops : CoeffectOperations V) (state : SR) (edit : E) (child : Name) (stamp : Nat) :
    runOrdinary edit (savedRetire state child stamp) =
      (runOrdinary edit state).map (fun output => savedRetire output child stamp) := by
  by_cases fires : state.2 child = some stamp
  · simp only [savedRetire, if_pos fires, runOrdinary, ordinary_after_retire ops]
    cases result : runEdit edit state.1 <;> simp [fires]
  · simp only [savedRetire, if_neg fires, runOrdinary]
    cases result : runEdit edit state.1 <;> simp [fires]

private theorem edit_guard (ops : CoeffectOperations V) {edit : E} {before after : R}
    (called : runEdit edit before = some after) (parent child : Name) (payload : Calculus.Component Key Code) :
    Insertable after child payload (some parent) ↔ Insertable before child payload (some parent) := by
  obtain ⟨_, value, _, _, rfl⟩ := edit_success called
  have guarded := Transposition.write_insertable (encodeRegistry ops before) edit.slot.1 child edit.slot.2
    (value.map (TypedCoeffectReplay.pack edit.slot.2)) payload (some parent)
  simpa only [← encode_write, insertable_encode_iff] using guarded

def OrdinaryCompatible (edit : E) : C → Prop
  | .birth _ child _ _ => edit.slot.1 ≠ child
  | .retire .. => True

/-- A control edit exchanges exactly with an ordinary edit when a birth
does not supply that ordinary edit's owner. Vacancy, provision reservations,
callback domains and the saved retirement's stamp test are all preserved. -/
theorem ordinary_control_commute (ops : CoeffectOperations V) (edit : E) (control : C)
    (compatible : OrdinaryCompatible edit control) :
    compose (runOrdinary edit) (PairwiseControl.run control) =
      (compose (PairwiseControl.run control) (runOrdinary edit) : PartialMap SR) := by
  classical
  funext state
  cases control with
  | retire child stamp =>
    simp only [compose, PairwiseControl.run, Option.bind_some, ordinary_after_saved_retire ops]
    cases result : runOrdinary edit state <;> rfl
  | birth parent child payload stamp =>
    by_cases ready : Insertable state.1 child payload (some parent)
    · simp only [compose, PairwiseControl.run, if_pos ready, Option.bind_some,
        ordinary_after_birth ops state edit compatible ready.1]
      cases result : runEdit edit state.1 with
      | none => simp [runOrdinary, result]
      | some after =>
        have stillReady := (edit_guard ops result parent child payload).mpr ready
        simp [runOrdinary, PairwiseControl.run, result, stillReady]
    · simp only [compose, PairwiseControl.run, if_neg ready, Option.bind_none]
      cases result : runEdit edit state.1 with
      | none => simp [runOrdinary, result]
      | some after =>
        have blocked : ¬ Insertable after child payload (some parent) := fun later =>
          ready ((edit_guard ops result parent child payload).mp later)
        simp [runOrdinary, PairwiseControl.run, result, blocked]

abbrev MixedEdit (Name : Type u) {Key : Type u} (V : Key → Type u) (Code : Type u) :=
  Control Name Key Code ⊕ Edit Name V
local notation "M" => MixedEdit Name V Code

def controlPart (word : List M) : List C := word.filterMap fun
  | .inl control => some control
  | .inr _ => none

def ordinaryPart (word : List M) : List E := word.filterMap fun
  | .inl _ => none
  | .inr edit => some edit

@[simp] noncomputable def runLetter : M → PartialMap SR
  | .inl control => PairwiseControl.run control
  | .inr edit => runOrdinary edit

noncomputable def runMixed (word : List M) : PartialMap SR :=
  PartialReplayHistory.run (word.map runLetter)

noncomputable def runControls (word : List C) : PartialMap SR :=
  PartialReplayHistory.run (word.map PairwiseControl.run)

def runOrdinaries (word : List E) (state : SR) : Option SR :=
  (runWord word state.1).map (fun output => (output, state.2))

def Scoped (word : List M) : Prop :=
  ∀ edit ∈ ordinaryPart word, ∀ control ∈ controlPart word, OrdinaryCompatible edit control

omit [DecidableEq Name] [DecidableEq Key] in
theorem scoped_of_vacant_births (word : List M) (state : R)
    (owners : OwnersPresent state (ordinaryPart word))
    (vacant : ∀ parent child component stamp, Control.birth parent child component stamp ∈ controlPart word →
      state child = none) : Scoped word := by
  intro edit member control inWord
  cases control with
  | retire => trivial
  | birth parent child component stamp =>
    exact fun same => owners edit member (same.symm ▸ vacant parent child component stamp inWord)

private theorem compose_assoc {S : Type u} (a b c : PartialMap S) :
    compose a (compose b c) = compose (compose a b) c := by
  funext input
  exact Option.bind_assoc _ _ _

private theorem exact_exchange {S : Type u} (left right : List (PartialMap S))
    (pairs : ∀ f ∈ left, ∀ g ∈ right, compose f g = compose g f) :
    compose (PartialReplayHistory.run left) (PartialReplayHistory.run right) =
      compose (PartialReplayHistory.run right) (PartialReplayHistory.run left) := by
  let observation : Setoid S := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  have generated (allowed : PartialMap S → Prop) (word : List (PartialMap S))
      (scope : ∀ map ∈ word, allowed map) :
      PartialMapClosure.Generated allowed (PartialReplayHistory.run word) := by
    induction word with
    | nil => exact .identity
    | cons head tail ih =>
      exact .composition (ih (fun map member => scope map (List.mem_cons_of_mem _ member)))
        (.generator (scope head List.mem_cons_self))
  have respects (map : PartialMap S) : PartialObservedMapClosure.Maps observation map map := by
    intro first second same
    cases same
    exact PartialObservedMapClosure.option_refl _ _
  have commute := PartialObservedMapClosure.generated_commutes observation (fun f _ => respects f) (fun g _ => respects g)
    (fun f g inLeft inRight => by
      unfold PartialObservedMapClosure.Commutes
      rw [pairs f inLeft g inRight]
      exact respects _)
    (generated (fun map => map ∈ left) left (fun _ h => h))
    (generated (fun map => map ∈ right) right (fun _ h => h))
  funext input
  have compared := commute input input rfl
  cases first : compose (PartialReplayHistory.run left) (PartialReplayHistory.run right) input <;>
    cases second : compose (PartialReplayHistory.run right) (PartialReplayHistory.run left) input <;>
    simp only [first, second, OptionRel, Option.some.injEq] at compared ⊢
  exact compared

private theorem runOrdinaries_cons (edit : E) (word : List E) :
    runOrdinaries (edit :: word) = (compose (runOrdinaries word) (runOrdinary edit) : PartialMap SR) := by
  funext state
  cases first : runEdit edit state.1 <;> simp [runOrdinaries, runOrdinary, runWord, compose, first]

/-- Extract the control word in its original order. Every exchanged table
edit has an owner independent of the crossed births. This is an equality
of partial full-registry evaluations, including intermediate failures. -/
theorem factor_word (ops : CoeffectOperations V) (word : List M) (scope : Scoped word) :
    runMixed word = (compose (runOrdinaries (ordinaryPart word)) (runControls (controlPart word)) : PartialMap SR) := by
  induction word with
  | nil => rfl
  | cons head tail ih =>
    cases head with
    | inl control =>
      have scopedTail : Scoped tail := by
        intro edit member other controlMember
        exact scope edit member other (List.mem_cons_of_mem _ controlMember)
      change compose (runMixed tail) (PairwiseControl.run control) =
        compose (runOrdinaries (ordinaryPart tail)) (compose (runControls (controlPart tail)) (PairwiseControl.run control))
      rw [ih scopedTail, compose_assoc]
    | inr edit =>
      have scopedTail : Scoped tail := by
        intro later member control controlMember
        exact scope later (List.mem_cons_of_mem _ member) control controlMember
      have exchange : compose (runControls (controlPart tail)) (runOrdinary edit) =
          compose (runOrdinary edit) (runControls (controlPart tail)) := by
        have singleton : PartialReplayHistory.run [runOrdinary edit] = (runOrdinary edit : PartialMap SR) := by
          funext state
          cases called : runOrdinary edit state <;> simp [called]
        rw [← singleton]
        apply exact_exchange ((controlPart tail).map PairwiseControl.run) [runOrdinary edit]
        intro f first g second
        obtain ⟨control, member, rfl⟩ := List.mem_map.mp first
        have eq := List.mem_singleton.mp second
        subst g
        exact (ordinary_control_commute ops edit control (scope edit List.mem_cons_self control member)).symm
      change compose (runMixed tail) (runOrdinary edit) =
        compose (runOrdinaries (edit :: ordinaryPart tail)) (runControls (controlPart tail))
      rw [ih scopedTail, runOrdinaries_cons, ← compose_assoc, exchange, compose_assoc]

omit [DecidableEq Key] in
private theorem control_keeps_owner {before after : SR} {control : C} {owner : Name}
    (called : PairwiseControl.run control before = some after) (present : before.1 owner ≠ none) :
    after.1 owner ≠ none := by
  classical
  cases control with
  | birth parent child payload stamp =>
    simp only [PairwiseControl.run] at called
    split at called
    · cases Option.some.inj called
      by_cases same : owner = child <;> simp [addBirth, put, same, present]
    · contradiction
  | retire child stamp =>
    have output := (Option.some.inj called).symm
    rw [output]
    unfold savedRetire
    split
    · by_cases same : owner = child
      · subst owner
        simpa [retire, TypedRegistry.modify] using present
      · simp [retire, TypedRegistry.modify, same, present]
    · exact present

omit [DecidableEq Key] in
private theorem controls_keep_owner {before after : SR} (word : List C) {owner : Name}
    (called : runControls word before = some after) (present : before.1 owner ≠ none) :
    after.1 owner ≠ none := by
  induction word generalizing before with
  | nil =>
    change some before = some after at called
    cases Option.some.inj called
    exact present
  | cons head tail ih =>
    obtain ⟨middle, applied, rest⟩ := Option.bind_eq_some_iff.mp called
    exact ih rest (control_keeps_owner (control := head) applied present)

private theorem control_self (observe : ∀ key, Setoid (V key)) {before after : SR} {edit : C}
    (called : PairwiseControl.run edit before = some after)
    (self : PairwisePrograms.Related (ops := ops) observe before.1 before.1) :
    PairwisePrograms.Related (ops := ops) observe after.1 after.1 := by
  letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
  classical
  cases edit with
  | birth parent child payload stamp =>
    simp only [PairwiseControl.run] at called
    split at called
    · cases Option.some.inj called
      simp only [PairwisePrograms.Related, addBirth, encode_put, encode_fresh]
      exact StageSimulation.put_related self child (StageSimulation.fresh_related ⟨rfl, rfl, rfl⟩ (some parent))
    · contradiction
  | retire child stamp =>
    have output := (Option.some.inj called).symm
    rw [output]
    unfold savedRetire
    split
    · simp only [PairwisePrograms.Related, encode_retire]
      exact StageSimulation.retire_related self child
    · exact self

private theorem controls_self (observe : ∀ key, Setoid (V key)) (word : List C) {before after : SR}
    (called : runControls word before = some after)
    (self : PairwisePrograms.Related (ops := ops) observe before.1 before.1) :
    PairwisePrograms.Related (ops := ops) observe after.1 after.1 := by
  induction word generalizing before with
  | nil =>
    change some before = some after at called
    cases Option.some.inj called
    exact self
  | cons head tail ih =>
    obtain ⟨middle, applied, rest⟩ := Option.bind_eq_some_iff.mp called
    exact ih rest (control_self observe (edit := head) applied self)

/-- The complete two orders of the fixed mixed words have the same partial
domain at the common probe. If they succeed they agree on live birth stamps
and have related full native registries. Binding domains are checked by
the actual partial callbacks and reservation and retirement guards are
checked in the stamped registry throughout each word. -/
theorem mixed_words_commute (ops : CoeffectOperations V) (observe : ∀ key, Setoid (V key))
    (laws : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    {first second : Name} {firstComponent secondComponent : Calculus.Component Key Code}
    (different : first ≠ second) (separate : Transposition.Separated firstComponent secondComponent)
    (before : SR) (left right : List M)
    (leftAllowed : ∀ edit ∈ ordinaryPart left, Admitted ops first firstComponent edit)
    (rightAllowed : ∀ edit ∈ ordinaryPart right, Admitted ops second secondComponent edit)
    (leftOwners : OwnersPresent before.1 (ordinaryPart left))
    (rightOwners : OwnersPresent before.1 (ordinaryPart right))
    (scope : Scoped (left ++ right))
    (births : ∀ edit ∈ controlPart left, ∀ other ∈ controlPart right, Compatible edit other)
    (self : PairwisePrograms.Related (ops := ops) observe before.1 before.1) :
    OptionRel (fun a b : SR => a.2 = b.2 ∧ PairwisePrograms.Related (ops := ops) observe a.1 b.1)
      (runMixed (right ++ left) before) (runMixed (left ++ right) before) := by
  have reverseScope : Scoped (right ++ left) := by
    intro edit member control controlMember
    have inOrdinary : edit ∈ ordinaryPart (left ++ right) := by
      simpa only [ordinaryPart, List.filterMap_append, List.mem_append, or_comm] using member
    have inControl : control ∈ controlPart (left ++ right) := by
      simpa only [controlPart, List.filterMap_append, List.mem_append, or_comm] using controlMember
    exact scope edit inOrdinary control inControl
  have exchange := exact_exchange ((controlPart left).map PairwiseControl.run) ((controlPart right).map PairwiseControl.run)
    (fun a leftMember b rightMember => by
      obtain ⟨edit, member, rfl⟩ := List.mem_map.mp leftMember
      obtain ⟨other, otherMember, rfl⟩ := List.mem_map.mp rightMember
      exact controls_commute ops (births edit member other otherMember))
  have sameControls : runControls (controlPart right ++ controlPart left) before =
      runControls (controlPart left ++ controlPart right) before := by
    simpa only [runControls, List.map_append, PartialReplayHistory.run_append, compose] using congrFun exchange before
  rw [factor_word ops _ reverseScope, factor_word ops _ scope]
  simp only [ordinaryPart, controlPart, List.filterMap_append] at sameControls ⊢
  unfold compose
  rw [sameControls]
  change OptionRel _
    ((runControls (controlPart left ++ controlPart right) before).bind (runOrdinaries (ordinaryPart right ++ ordinaryPart left)))
    ((runControls (controlPart left ++ controlPart right) before).bind (runOrdinaries (ordinaryPart left ++ ordinaryPart right)))
  cases controls : runControls (controlPart left ++ controlPart right) before with
  | none => exact True.intro
  | some middle =>
    have leftRemain : OwnersPresent middle.1 (ordinaryPart left) := fun edit member =>
      controls_keep_owner _ controls (leftOwners edit member)
    have rightRemain : OwnersPresent middle.1 (ordinaryPart right) := fun edit member =>
      controls_keep_owner _ controls (rightOwners edit member)
    have observed := ordinary_words_commute_on_scope ops observe laws different separate leftAllowed rightAllowed
      leftRemain rightRemain (controls_self observe _ controls self)
    change OptionRel _ (runOrdinaries (ordinaryPart right ++ ordinaryPart left) middle)
      (runOrdinaries (ordinaryPart left ++ ordinaryPart right) middle)
    unfold runOrdinaries
    cases a : runWord (ordinaryPart right ++ ordinaryPart left) middle.1 <;>
      cases b : runWord (ordinaryPart left ++ ordinaryPart right) middle.1 <;>
      simp only [a, b, Option.map_none, Option.map_some, OptionRel] at observed ⊢
    exact ⟨True.intro, observed⟩

section Recording
open PairwiseOperations (declared_key table_and_route undo_operate_eq_write)

/-- A successful native landing supplies one fixed mixed letter, or the
identity for unit. A selected child retains its actual payload and draw,
and the fresh stamp associated with that landing travels with it. -/
theorem record_landing {program : Code → Instruction Name ops Code} {actor : Name} {code : Code}
    {before : SR} {after : R} {token : Inverse Name V} {next : Option Code} {row : Fiber Name V Code}
    (present : before.1 actor = some row) (landed : Land program actor code before.1 after token next) (stamp : Nat) :
    ∃ word : List M, runMixed word before = some (after, fun name =>
      match token with
      | .retire child => if name = child then some stamp else before.2 name
      | _ => before.2 name) ∧ ∀ edit ∈ ordinaryPart word, Admitted ops actor row.component edit := by
  classical
  cases landed with
  | unit => exact ⟨[], rfl, by simp [ordinaryPart]⟩
  | provide registry name code own key value action found declared absent =>
    have same := Option.some.inj (found.symm.trans present)
    subst own
    refine ⟨[.inr (.provide actor key value)], ?_, ?_⟩
    · simp [runMixed, runOrdinary, runEdit, tablesOf, tableAt, Edit.slot, Edit.apply, found, absent]
    · intro edit member
      have same := List.mem_singleton.mp member
      subst edit
      exact ⟨rfl, declared⟩
  | operate registry name code key operation argument owner input output inverse result action located returned =>
    let forward := PartialCoeffectLifting.forward (ops.operation key operation argument)
    have bound := (table_and_route located).2
    obtain ⟨provider, found⟩ : ∃ provider, before.1 owner = some provider := by
      cases held : before.1 owner with
      | none => simp [tableAt, held] at bound
      | some provider => exact ⟨provider, rfl⟩
    refine ⟨[.inr (.operate owner key forward)], ?_, ?_⟩
    · simp [runMixed, runOrdinary, runEdit, tablesOf, Edit.slot, Edit.apply, found, bound, forward,
        PartialCoeffectLifting.forward, returned]
    · intro edit member
      have same := List.mem_singleton.mp member
      subst edit
      exact ⟨declared_key present located, operation, argument, .forward⟩
  | instantiate registry name code component child action ready =>
    exact ⟨[.inl (.birth actor child component stamp)], by simp [runMixed, PairwiseControl.run, ready, addBirth],
      by simp [ordinaryPart]⟩

/-- A strict guarded inverse has the matching fixed letter given its
actual native capturing landing. In the child case this is exactly the
recorded stamp test even across reuse of the raw name. -/
theorem record_capture {program : Code → Instruction Name ops Code} {actor : Name} {code : Code}
    {origin captured : R} {before : SR} {after : R} {token : Inverse Name V} {next : Option Code}
    {row : Fiber Name V Code} (present : origin actor = some row) (landed : Land program actor code origin captured token next)
    (index : Nat) (defined : InverseDefined before.1 token)
    (applied : encodeRegistry ops after =
      (IncarnationReplay.Capture.mk (encodeInverse ops token) index).apply before.2 (encodeRegistry ops before.1)) :
    ∃ word : List M, runMixed word before = some (after, before.2) ∧
      ∀ edit ∈ ordinaryPart word, Admitted ops actor row.component edit := by
  cases landed with
  | unit =>
    have same : after = before.1 := encodeRegistry_injective ops (by simpa [IncarnationReplay.Capture.apply, encodeInverse] using applied)
    exact ⟨[], by simp [runMixed, same], by simp [ordinaryPart]⟩
  | provide _ _ _ own key value _ found declared _ =>
    have same := Option.some.inj (found.symm.trans present)
    subst own
    have afterWrite : after = write before.1 actor key none := encodeRegistry_injective ops (by
      simpa [IncarnationReplay.Capture.apply, encodeInverse, Stages.undo] using applied)
    have hasBinding : tableAt before.1 actor key ≠ none := defined
    cases binding : tableAt before.1 actor key with
    | none => exact False.elim (hasBinding binding)
    | some old =>
      obtain ⟨owner, present⟩ : ∃ owner, before.1 actor = some owner := by
        cases held : before.1 actor with
        | none => simp [tableAt, held] at binding
        | some owner => exact ⟨owner, rfl⟩
      refine ⟨[.inr (.restrict actor key)], ?_, ?_⟩
      · simp [runMixed, runOrdinary, runEdit, Edit.slot, Edit.apply, tablesOf, present, binding, afterWrite]
      · intro edit member
        have same := List.mem_singleton.mp member
        subst edit
        exact ⟨rfl, declared⟩
  | operate _ _ _ key operation argument owner input output inverse result _ located returned =>
    obtain ⟨probeInput, probeOutput, bound, called⟩ := defined
    have afterWrite : after = write before.1 owner key (some probeOutput) := by
      have saved : after = undo (.operate owner key inverse) before.1 := encodeRegistry_injective ops (by
        simpa [IncarnationReplay.Capture.apply, encodeInverse] using applied)
      exact saved.trans (undo_operate_eq_write bound called)
    obtain ⟨provider, found⟩ : ∃ provider, before.1 owner = some provider := by
      cases held : before.1 owner with
      | none => simp [tableAt, held] at bound
      | some provider => exact ⟨provider, rfl⟩
    refine ⟨[.inr (.operate owner key inverse)], ?_, ?_⟩
    · simp [runMixed, runOrdinary, runEdit, Edit.slot, Edit.apply, tablesOf, found, bound, called, afterWrite]
    · intro edit member
      have same := List.mem_singleton.mp member
      subst edit
      exact ⟨declared_key present located, operation, argument, .inverse input output inverse result returned⟩
  | instantiate _ _ _ _ child _ _ =>
    have state : (after, before.2) = savedRetire before child index := by
      by_cases fires : before.2 child = some index
      · simp only [savedRetire, if_pos fires, Prod.mk.injEq, and_true]
        exact encodeRegistry_injective ops (by
          simpa [IncarnationReplay.Capture.apply, encodeInverse, fires] using applied)
      · simp only [savedRetire, if_neg fires]
        have unchanged : after = before.1 := encodeRegistry_injective ops (by
          simpa [IncarnationReplay.Capture.apply, encodeInverse, fires] using applied)
        rw [unchanged]
    exact ⟨[.inl (.retire child index)], by simp [runMixed, PairwiseControl.run, state], by simp [ordinaryPart]⟩

end Recording

private theorem letter_keeps_owner {before after : SR} {letter : M} {owner : Name}
    (called : runLetter letter before = some after) (present : before.1 owner ≠ none) : after.1 owner ≠ none := by
  cases letter with
  | inl control => exact control_keeps_owner (control := control) called present
  | inr edit =>
    obtain ⟨output, applied, rfl⟩ := Option.map_eq_some_iff.mp
      (show runOrdinary edit before = some after from called)
    obtain ⟨_, _, _, _, rfl⟩ := edit_success applied
    by_cases same : owner = edit.slot.1
    · subst owner
      cases found : before.1 edit.slot.1 <;> simp_all [write, TypedRegistry.modify]
    · simpa [write, TypedRegistry.modify, same] using present

/-- Each recorded birth used a name vacant at the common source. Earlier
mixed edits cannot remove a row that was already present there. -/
theorem birth_vacant_at_source {before after : SR} (word : List M)
    (called : runMixed word before = some after) (parent child : Name)
    (payload : Calculus.Component Key Code) (stamp : Nat)
    (member : Control.birth parent child payload stamp ∈ controlPart word) : before.1 child = none := by
  classical
  induction word generalizing before with
  | nil => simp [controlPart] at member
  | cons head tail ih =>
    obtain ⟨middle, first, rest⟩ := Option.bind_eq_some_iff.mp called
    have fromTail (tailMember : Control.birth parent child payload stamp ∈ controlPart tail) : before.1 child = none := by
      have atCut := ih rest tailMember
      by_cases vacant : before.1 child = none
      · exact vacant
      · exact False.elim (letter_keeps_owner first vacant atCut)
    cases head with
    | inl control =>
      change _ ∈ control :: controlPart tail at member
      rcases List.mem_cons.mp member with rfl | tailMember
      · simp only [runLetter, PairwiseControl.run] at first
        split at first
        · rename_i ready
          exact ready.1
        · contradiction
      · exact fromTail tailMember
    | inr edit => exact fromTail member

private theorem empty_owner_untouched (ops : CoeffectOperations V) {actor owner : Name}
    {component : Calculus.Component Key Code} (different : owner ≠ actor) {before after : SR} (word : List M)
    (called : runMixed word before = some after) (allowed : ∀ edit ∈ ordinaryPart word, Admitted ops actor component edit)
    (empty : ∀ key, tableAt before.1 owner key = none) : ∀ edit ∈ ordinaryPart word, edit.slot.1 ≠ owner := by
  induction word generalizing before with
  | nil => simp [ordinaryPart]
  | cons head tail ih =>
    obtain ⟨middle, first, rest⟩ := Option.bind_eq_some_iff.mp called
    cases head with
    | inl control =>
      have unchanged := successful_preserves_tables (edit := control) first
      exact ih rest allowed (fun key => (congrFun unchanged (owner, key)).trans (empty key))
    | inr edit =>
      obtain ⟨written, applied, rfl⟩ := Option.map_eq_some_iff.mp
        (show runOrdinary edit before = some middle from first)
      obtain ⟨_, result, present, value, rfl⟩ := edit_success applied
      have admitted := allowed edit (show edit ∈ edit :: ordinaryPart tail from List.mem_cons_self)
      have away : edit.slot.1 ≠ owner := by
        intro same
        cases edit with
        | provide holder key payload =>
          exact different (same.symm.trans admitted.1)
        | restrict holder key =>
          change holder = owner at same
          subst holder
          simp [tablesOf, Edit.slot, Edit.apply, empty key] at value
        | operate holder key inverse =>
          change holder = owner at same
          subst holder
          simp [tablesOf, Edit.slot, Edit.apply, empty key] at value
      have retainedEmpty (key : Key) : tableAt (write before.1 edit.slot.1 edit.slot.2 result) owner key = none := by
        have tables := tablesOf_write before.1 edit.slot.1 edit.slot.2 result (by rw [present]; exact Option.noConfusion)
        have distinct : (owner, key) ≠ edit.slot := fun same => away ((congrArg Prod.fst same).symm)
        exact (congrFun tables (owner, key)).trans ((Coeffects.update_other _ _ _ _ distinct).trans (empty key))
      intro later member
      change later ∈ edit :: ordinaryPart tail at member
      rcases List.mem_cons.mp member with rfl | retained
      · exact away
      · exact ih rest (fun item h => allowed item (List.mem_cons_of_mem _ h)) retainedEmpty later retained

/-- Only the acting fiber can provision in an actor's word. An initially
absent row cannot acquire a binding even if that word creates a child there.
This derives the retained-owner scope for all of the recorded ordinary edits. -/
theorem mixed_owners_present (ops : CoeffectOperations V) {before after : SR} (word : List M)
    {actor : Name} {component : Calculus.Component Key Code} (present : before.1 actor ≠ none)
    (allowed : ∀ edit ∈ ordinaryPart word, Admitted ops actor component edit)
    (called : runMixed word before = some after) : OwnersPresent before.1 (ordinaryPart word) := by
  intro edit member vacant
  have different : edit.slot.1 ≠ actor := by
    intro same
    exact present (same ▸ vacant)
  exact empty_owner_untouched ops different word called allowed (fun key => by simp [tableAt, vacant]) edit member rfl

/-- Pairwise registry commutation for two successfully recorded mixed
words. The original executions derive the ordinary owner and birth
vacancy checks needed by the factorization. The cross-word guard retains
the chosen birth reservations and incarnation stamps. -/
theorem recorded_mixed_words_commute (ops : CoeffectOperations V) (observe : ∀ key, Setoid (V key))
    (laws : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    {first second : Name} {firstComponent secondComponent : Calculus.Component Key Code}
    (different : first ≠ second) (separate : Transposition.Separated firstComponent secondComponent)
    {before leftAfter rightAfter : SR} {left right : List M}
    (firstPresent : before.1 first ≠ none) (secondPresent : before.1 second ≠ none)
    (leftAllowed : ∀ edit ∈ ordinaryPart left, Admitted ops first firstComponent edit)
    (rightAllowed : ∀ edit ∈ ordinaryPart right, Admitted ops second secondComponent edit)
    (leftRun : runMixed left before = some leftAfter) (rightRun : runMixed right before = some rightAfter)
    (births : ∀ edit ∈ controlPart left, ∀ other ∈ controlPart right, Compatible edit other)
    (self : PairwisePrograms.Related (ops := ops) observe before.1 before.1) :
    OptionRel (fun a b : SR => a.2 = b.2 ∧ PairwisePrograms.Related (ops := ops) observe a.1 b.1)
      (runMixed (right ++ left) before) (runMixed (left ++ right) before) := by
  have leftOwners := mixed_owners_present ops left firstPresent leftAllowed leftRun
  have rightOwners := mixed_owners_present ops right secondPresent rightAllowed rightRun
  have scope : Scoped (left ++ right) := by
    intro edit member ctl inControls
    have atOwner : before.1 edit.slot.1 ≠ none := by
      have sides : edit ∈ ordinaryPart left ++ ordinaryPart right := by
        simpa only [ordinaryPart, List.filterMap_append] using member
      exact (List.mem_append.mp sides).elim (leftOwners edit) (rightOwners edit)
    cases ctl with
    | retire => exact True.intro
    | birth parent child payload stamp =>
      have sides : Control.birth parent child payload stamp ∈ controlPart left ++ controlPart right := by
        simpa only [controlPart, List.filterMap_append] using inControls
      have vacant : before.1 child = none := (List.mem_append.mp sides).elim
        (birth_vacant_at_source left leftRun parent child payload stamp)
        (birth_vacant_at_source right rightRun parent child payload stamp)
      exact fun same => atOwner (same.symm ▸ vacant)
  exact mixed_words_commute ops observe laws different separate before left right leftAllowed rightAllowed
    leftOwners rightOwners scope births self

abbrev StampedRelated (ops : CoeffectOperations V) (observe : ∀ key, Setoid (V key)) (left right : SR) : Prop :=
  left.2 = right.2 ∧ PairwisePrograms.Related (ops := ops) observe left.1 right.1

private theorem control_respects (ops : CoeffectOperations V) (observe : ∀ key, Setoid (V key)) (edit : C)
    {left right : SR} (related : StampedRelated ops observe left right) :
    OptionRel (StampedRelated ops observe) (PairwiseControl.run edit left) (PairwiseControl.run edit right) := by
  letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
  classical
  cases edit with
  | birth parent child component stamp =>
    have same : StageSimulation.ComponentRelated Eq component component := ⟨rfl, rfl, rfl⟩
    have ready : Insertable left.1 child component (some parent) ↔ Insertable right.1 child component (some parent) := by
      rw [← insertable_encode_iff ops left.1, ← insertable_encode_iff ops right.1]
      exact ⟨StageSimulation.insertable_related related.2 child same (some parent),
        StageSimulation.insertable_related related.2.symm child same (some parent)⟩
    by_cases permitted : Insertable left.1 child component (some parent)
    · simp only [PairwiseControl.run, if_pos permitted, if_pos (ready.mp permitted), OptionRel]
      refine ⟨by simp [addBirth, related.1], ?_⟩
      simp only [PairwisePrograms.Related, addBirth, encode_put, encode_fresh]
      exact StageSimulation.put_related related.2 child (StageSimulation.fresh_related same (some parent))
    · have denied : ¬ Insertable right.1 child component (some parent) := fun enabled => permitted (ready.mpr enabled)
      simp [PairwiseControl.run, permitted, denied, OptionRel]
  | retire child stamp =>
    by_cases fires : left.2 child = some stamp
    · have other : right.2 child = some stamp := by rw [← related.1]; exact fires
      simp only [PairwiseControl.run, savedRetire, if_pos fires, if_pos other, OptionRel]
      refine ⟨related.1, ?_⟩
      simp only [PairwisePrograms.Related, encode_retire]
      exact StageSimulation.retire_related related.2 child
    · have other : right.2 child ≠ some stamp := by rw [← related.1]; exact fires
      simpa only [PairwiseControl.run, savedRetire, if_neg fires, if_neg other, OptionRel] using related

/-- Fixed mixed words respect related registry probes with the same live
stamps. This compares actual failures as well as successful compositions. -/
theorem mixed_respects (ops : CoeffectOperations V) (observe : ∀ key, Setoid (V key))
    (laws : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    {actor : Name} {component : Calculus.Component Key Code} (word : List M)
    (allowed : ∀ edit ∈ ordinaryPart word, Admitted ops actor component edit)
    {left right : SR} (related : StampedRelated ops observe left right) :
    OptionRel (StampedRelated ops observe) (runMixed word left) (runMixed word right) := by
  induction word generalizing left right with
  | nil => exact related
  | cons head tail ih =>
    have headMoves : OptionRel (StampedRelated ops observe) (runLetter head left) (runLetter head right) := by
      cases head with
      | inl ctl => exact control_respects ops observe ctl related
      | inr edit =>
        have edits := edit_respects_registry ops observe laws (allowed edit List.mem_cons_self) related.2
        simp only [runLetter, runOrdinary]
        cases a : runEdit edit left.1 <;> cases b : runEdit edit right.1 <;>
          simp only [a, b, OptionRel, Option.map_none, Option.map_some] at edits ⊢
        exact ⟨related.1, edits⟩
    have restAllowed : ∀ edit ∈ ordinaryPart tail, Admitted ops actor component edit := by
      intro edit member
      apply allowed edit
      cases head with
      | inl => exact member
      | inr _ => exact List.mem_cons_of_mem _ member
    change OptionRel _ ((runLetter head left).bind (runMixed tail)) ((runLetter head right).bind (runMixed tail))
    cases a : runLetter head left <;> cases b : runLetter head right <;>
      simp only [a, b, OptionRel, Option.bind_none, Option.bind_some] at headMoves ⊢
    exact ih restAllowed headMoves

/-- Cross-word commutation on related compatible probes. The same state
comparison is used for both definedness and the whole resulting registry. -/
theorem recorded_mixed_words_commute_related (ops : CoeffectOperations V) (observe : ∀ key, Setoid (V key))
    (laws : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    {first second : Name} {firstComponent secondComponent : Calculus.Component Key Code}
    (different : first ≠ second) (separate : Transposition.Separated firstComponent secondComponent)
    {before alternate leftAfter rightAfter : SR} {left right : List M}
    (firstPresent : before.1 first ≠ none) (secondPresent : before.1 second ≠ none)
    (leftAllowed : ∀ edit ∈ ordinaryPart left, Admitted ops first firstComponent edit)
    (rightAllowed : ∀ edit ∈ ordinaryPart right, Admitted ops second secondComponent edit)
    (leftRun : runMixed left before = some leftAfter) (rightRun : runMixed right before = some rightAfter)
    (births : ∀ edit ∈ controlPart left, ∀ other ∈ controlPart right, Compatible edit other)
    (sources : StampedRelated ops observe before alternate) :
    OptionRel (StampedRelated ops observe) (runMixed (right ++ left) before) (runMixed (left ++ right) alternate) := by
  have switched := recorded_mixed_words_commute ops observe laws different separate firstPresent secondPresent
    leftAllowed rightAllowed leftRun rightRun births (sources.2.trans sources.2.symm)
  have continued : OptionRel (StampedRelated ops observe) (runMixed (left ++ right) before)
      (runMixed (left ++ right) alternate) := by
    simp only [runMixed, List.map_append, PartialReplayHistory.run_append]
    change OptionRel _ ((runMixed left before).bind (runMixed right)) ((runMixed left alternate).bind (runMixed right))
    have paired := mixed_respects ops observe laws left leftAllowed sources
    cases a : runMixed left before <;> cases b : runMixed left alternate <;>
      simp only [a, b, OptionRel, Option.bind_none, Option.bind_some] at paired ⊢
    exact mixed_respects ops observe laws right rightAllowed paired
  exact @OptionRel.trans SR (StampedRelated ops observe) (fun _ _ _ a b => ⟨a.1.trans b.1, a.2.trans b.2⟩)
    _ _ _ switched continued

end Cordis.Repairs.PairwiseMixed
