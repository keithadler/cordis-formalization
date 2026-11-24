import Cordis.Repairs.GuardedBirthMatching
import Cordis.Repairs.GuardedReindex

/-! Identify orchestration targets across different event orders. A root
has its insertion ordinal. A child has its parent's birth address and
the ordinal of the parent's allocating stage within that incarnation. -/
namespace Cordis.Repairs.GuardedBirthAddresses
open Calculus Stages LegalHistory GuardedHistory GuardedBirthMatching Incarnation IncarnationReplay
open ExchangeReplay (exchangedCut exchangedIndex exchanged_stamp)

universe u
variable {Name Key Value Code Error : Type u} [DecidableEq Name] [DecidableEq Key]
variable {program : Code → Instruction Name Key Value Code Error} {last : Nat}
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error

inductive Address where
  | root (insertion : Nat)
  | child (parent : Address) (stage : Nat)
  deriving DecidableEq

def occurrencesBefore (tests : Nat → Bool) : Nat → Nat
  | 0 => 0
  | time + 1 => occurrencesBefore tests time + if tests time then 1 else 0

private theorem count_le (tests : Nat → Bool) {i j : Nat} (order : i ≤ j) :
    occurrencesBefore tests i ≤ occurrencesBefore tests j := by
  induction j with
  | zero =>
    have same : i = 0 := by omega
    subst i
    exact Nat.le_refl _
  | succ j ih =>
    by_cases same : i = j + 1
    · subst i; exact Nat.le_refl _
    have previous := ih (by omega)
    rw [occurrencesBefore]
    omega

private theorem count_lt (tests : Nat → Bool) {i j : Nat} (order : i < j) (hit : tests i = true) :
    occurrencesBefore tests i < occurrencesBefore tests j := by
  have through := count_le tests (show i + 1 ≤ j by omega)
  rw [occurrencesBefore, hit, if_pos rfl] at through
  omega

theorem occurrence_unique (tests : Nat → Bool) {i j : Nat} (left : tests i = true) (right : tests j = true)
    (same : occurrencesBefore tests i = occurrencesBefore tests j) : i = j := by
  rcases Nat.lt_trichotomy i j with earlier | equal | later
  · have strict := count_lt tests earlier left
    omega
  · exact equal
  · have strict := count_lt tests later right
    omega

private theorem occurrence_exchanged {before after : Nat → Bool} {point limit cut : Nat}
    (layout : ∀ i, i < limit → after i = before (exchangedCut point i))
    (bounded : point + 1 < limit) (inside : cut < limit) (selected : after cut = true)
    (distinct : ¬ (before point = true ∧ before (point + 1) = true)) :
    occurrencesBefore after cut = occurrencesBefore before (exchangedCut point cut) := by
  have head : ∀ i, i ≤ point → occurrencesBefore after i = occurrencesBefore before i := by
    intro i
    induction i with
    | zero => intro _; rfl
    | succ i ih =>
      intro early
      rw [occurrencesBefore, occurrencesBefore, ih (by omega), layout i (by omega)]
      simp [exchangedCut, show i ≠ point by omega, show i ≠ point + 1 by omega]
  have pair : occurrencesBefore after (point + 2) = occurrencesBefore before (point + 2) := by
    have first : after point = before (point + 1) := by simpa [exchangedCut] using layout point (by omega)
    have second : after (point + 1) = before point := by simpa [exchangedCut] using layout (point + 1) bounded
    simp only [occurrencesBefore, head point (Nat.le_refl _), first, second]
    omega
  have tail : ∀ i, point + 2 ≤ i → i ≤ limit → occurrencesBefore after i = occurrencesBefore before i := by
    intro i
    induction i with
    | zero => omega
    | succ i ih =>
      intro late valid
      by_cases ends : i + 1 = point + 2
      · rw [ends]; exact pair
      · rw [occurrencesBefore, occurrencesBefore, ih (by omega) (by omega), layout i (by omega)]
        simp [exchangedCut, show i ≠ point by omega, show i ≠ point + 1 by omega]
  by_cases first : cut = point
  · subst cut
    have hit : before (point + 1) = true := by simpa [layout point inside, exchangedCut] using selected
    have misses : before point = false := Bool.eq_false_iff.mpr (fun yes => distinct ⟨yes, hit⟩)
    simp [exchangedCut, occurrencesBefore, head point (Nat.le_refl _), misses]
  by_cases second : cut = point + 1
  · subst cut
    have hit : before point = true := by simpa [layout (point + 1) inside, exchangedCut] using selected
    have misses : before (point + 1) = false := Bool.eq_false_iff.mpr (fun yes => distinct ⟨hit, yes⟩)
    simp [exchangedCut, occurrencesBefore, head point (Nat.le_refl _), layout point (by omega), misses]
  have same : exchangedCut point cut = cut := by simp [exchangedCut, first, second]
  rw [same]
  by_cases earlier : cut ≤ point
  · exact head cut earlier
  · exact tail cut (by omega) (Nat.le_of_lt inside)

def isRootInsertion (trace : Trace program last) (time : Nat) : Bool :=
  match trace.event time with
  | .command (.insert _ _) => true
  | _ => false

/-- Count each stage at which that parent could allocate. Iter, Finish and
Divert count as stages. A later incarnation with the same name starts its
own count, and intervening events of other actors are irrelevant. -/
def isParentStage (trace : Trace program last) (parentBirth : Nat) (time : Nat) : Bool :=
  EpisodeSelection.canBirth (trace.rule time) &&
    ((trace.notes time).1 (trace.actor time) == some parentBirth)

private theorem mapped_birth_test {expand : Nat → Nat} (injective : Function.Injective expand)
    (birth : Nat) (tag : Option Nat) : (tag == some birth) = (tag.map expand == some (expand birth)) := by
  cases tag with
  | none => rfl
  | some other =>
    by_cases equal : other = birth
    · subst other; simp
    · have different : expand other ≠ expand birth := fun same => equal (injective same)
      simp [beq_eq_false_iff_ne.mpr equal, beq_eq_false_iff_ne.mpr different]

private theorem mapped_parent_stage {first second : Nat} {original : Trace program first}
    {moved : Trace program second} {expand : Nat → Nat}
    (retained : RetainedEvents original moved expand) (birth : Nat) {i : Nat} (inside : i < second) :
    isParentStage moved birth i = isParentStage original (expand birth) (expand (i + 1) - 1) := by
  unfold isParentStage
  have rules : moved.rule i = original.rule (expand (i + 1) - 1) := by rw [Trace.rule, Trace.rule, retained.label i inside]
  rw [rules, ← retained.actor_birth inside, mapped_birth_test retained.injective]

inductive Addressed (trace : Trace program last) : Nat → Address → Prop
  | root {time : Nat} {name : Name} {component : Component Key Code} :
      time < last → trace.event time = .command (.insert name component) →
      Addressed trace (time + 1) (.root (occurrencesBefore (isRootInsertion trace) time))
  | child {time parentBirth : Nat} {name : Name} {parent : Address} :
      time < last → EpisodeSelection.canBirth (trace.rule time) = true →
      trace.state time name = none → trace.state (time + 1) name ≠ none →
      (trace.notes time).1 (trace.actor time) = some parentBirth →
      Addressed trace parentBirth parent →
      Addressed trace (time + 1) (.child parent (occurrencesBefore (isParentStage trace parentBirth) time))

/-- A recursive birth address contains its own address and all of its
allocating ancestors' addresses. -/
inductive Address.DescendsFrom : Address → Address → Prop
  | self (address : Address) : DescendsFrom address address
  | child {parent ancestor : Address} (ordinal : Nat) :
      DescendsFrom parent ancestor → DescendsFrom (.child parent ordinal) ancestor

/-- An ancestor address in the recursive path is backed by an actual
birth no later than the descendant's birth. -/
theorem Addressed.ancestor_birth {trace : Trace program last}
    {birth : Nat} {address ancestor : Address}
    (born : Addressed trace birth address) (lineage : address.DescendsFrom ancestor) :
    ∃ stamp, stamp ≤ birth ∧ Addressed trace stamp ancestor := by
  induction lineage generalizing birth with
  | self =>
    exact ⟨birth, Nat.le_refl _, born⟩
  | child ordinal lineage ih =>
    cases born with
    | child bounded _ _ _ tag parent =>
      have parentEarlier := (recorded_birth trace (Nat.le_of_lt bounded) tag).2
      obtain ⟨stamp, before, actual⟩ := ih parent
      exact ⟨stamp, by omega, actual⟩

theorem Addressed.child_born {trace : Trace program last}
    {birth ordinal : Nat} {parent : Address}
    (born : Addressed trace birth (.child parent ordinal)) :
    ∃ name, BornAt trace name birth := by
  cases born with
  | child bounded _ vacant present _ _ =>
    exact ⟨_, by omega, by omega, by simpa only [Nat.add_sub_cancel] using vacant, present⟩

/-- A child address identifies the actual allocating event and its
parent at the cut immediately before the birth. -/
theorem Addressed.allocating_event {trace : Trace program last}
    {birth ordinal : Nat} {parent : Address}
    (born : Addressed trace birth (.child parent ordinal)) :
    ∃ cut parentBirth kind actor, birth = cut + 1 ∧ cut < last ∧
      trace.event cut = .lifecycle kind actor ∧
      (trace.notes cut).1 actor = some parentBirth ∧ Addressed trace parentBirth parent := by
  cases born with
  | @child cut parentBirth _ _ bounded rule _ _ tag parent =>
    cases event : trace.event cut with
    | lifecycle kind actor =>
      exact ⟨cut, parentBirth, kind, actor, rfl, bounded, event,
        by simpa [Trace.actor, Vestigial.eventActor, event] using tag, parent⟩
    | command command =>
      cases command <;> simp [Trace.rule, event, eventRule, ExchangeReplay.commandRule, EpisodeSelection.canBirth] at rule

/-- The address of a birth at a lifecycle event records that event's
actual parent incarnation and its allocating-stage ordinal. -/
theorem Addressed.parent_of_lifecycle {trace : Trace program last}
    {cut : Nat} {address : Address} (birth : Addressed trace (cut + 1) address)
    {kind : Lifecycle} {actor : Name} (event : trace.event cut = .lifecycle kind actor) :
    ∃ parentBirth parent,
      (trace.notes cut).1 actor = some parentBirth ∧ Addressed trace parentBirth parent ∧
      address = .child parent (occurrencesBefore (isParentStage trace parentBirth) cut) := by
  cases birth with
  | root _ inserted =>
    rw [inserted] at event
    cases event
  | child _ _ _ _ tag addressed =>
    exact ⟨_, _, by simpa [Trace.actor, Vestigial.eventActor, event] using tag, addressed, rfl⟩

/-- A birth address is already determined in any prefix that contains it. -/
theorem Addressed.transport_prefix {OtherValue OtherError : Type u}
    {otherProgram : Code → Instruction Name Key OtherValue Code OtherError}
    {targetLength through : Nat} {source : Trace program last} {target : Trace otherProgram targetLength}
    (targetBound : through ≤ targetLength)
    (events : ∀ i, i < through → source.event i = target.event i)
    (presence : ∀ i, i ≤ through → ∀ name, source.state i name = none ↔ target.state i name = none)
    (stamps : ∀ i, i ≤ through → (source.notes i).1 = (target.notes i).1)
    {birth : Nat} {address : Address} (known : Addressed source birth address) (inside : birth ≤ through) :
    Addressed target birth address := by
  have count {first second : Nat → Bool} {cut : Nat}
      (same : ∀ i, i < cut → first i = second i) :
      occurrencesBefore first cut = occurrencesBefore second cut := by
    induction cut with
    | zero => rfl
    | succ i ih =>
      rw [occurrencesBefore, occurrencesBefore, same i (by omega), ih (fun j earlier => same j (by omega))]
  induction known with
  | root bounded label =>
    rename_i time name component
    have ranks : occurrencesBefore (isRootInsertion source) time =
        occurrencesBefore (isRootInsertion target) time :=
      count fun i earlier => by simp only [isRootInsertion, events i (by omega)]
    rw [ranks]
    exact .root (by omega) ((events time (by omega)).symm.trans label)
  | @child time parentBirth name parent bounded stage absent present parentTag _ ih =>
    have ranks : occurrencesBefore (isParentStage source parentBirth) time =
        occurrencesBefore (isParentStage target parentBirth) time :=
      count fun i earlier => by
        simp only [isParentStage, Trace.rule, Trace.actor, events i (by omega), stamps i (by omega)]
    rw [ranks]
    refine .child (by omega) ?_ ((presence time (by omega) name).mp absent)
      (fun empty => present ((presence (time + 1) (by omega) name).mpr empty)) ?_ (ih ?_)
    · simpa only [Trace.rule, events time (by omega : time < through)] using stage
    · simpa only [Trace.actor, events time (by omega : time < through), stamps time (by omega)] using parentTag
    · have stampBound := (recorded_birth source (Nat.le_of_lt bounded) parentTag).2
      omega

/-- Birth addresses depend on event labels, name presence and live stamps.
They are invariant under a change of value representation. -/
theorem Addressed.transport_representation {OtherValue OtherError : Type u}
    {otherProgram : Code → Instruction Name Key OtherValue Code OtherError}
    {source : Trace program last} {target : Trace otherProgram last}
    (events : ∀ i, i < last → source.event i = target.event i)
    (presence : ∀ i, i ≤ last → ∀ name, source.state i name = none ↔ target.state i name = none)
    (stamps : ∀ i, i ≤ last → (source.notes i).1 = (target.notes i).1)
    {birth : Nat} {address : Address} (known : Addressed source birth address) :
    Addressed target birth address := by
  apply known.transport_prefix (Nat.le_refl _) events presence stamps
  cases known <;> omega

private theorem insertion_at_rule (trace : Trace program last) {time : Nat} (rule : trace.rule time = .insert) :
    ∃ component, trace.event time = .command (.insert (trace.actor time) component) := by
  cases event : trace.event time with
  | command command =>
    cases command with
    | insert name component => exact ⟨component, by simp [Trace.actor, event, Vestigial.eventActor,
        OrchestrationSorting.Command.actor]⟩
    | retire | remove => simp [Trace.rule, event, eventRule, ExchangeReplay.commandRule] at rule
  | lifecycle kind actor =>
    cases kind <;> simp [Trace.rule, event, eventRule, Lifecycle.rule] at rule

private theorem new_entry (trace : Trace program last) {time : Nat} {name : Name} (bound : time < last)
    (vacant : trace.state time name = none) (born : trace.state (time + 1) name ≠ none) :
    (∃ component, trace.event time = .command (.insert name component)) ∨
      (EpisodeSelection.canBirth (trace.rule time) = true ∧ ∃ parentBirth,
        (trace.notes time).1 (trace.actor time) = some parentBirth ∧ parentBirth ≤ time) := by
  rcases transition_cases (trace.step time bound).1 with native | ⟨actor, event, unload⟩
  · rcases EpisodeBoundary.new_entry_rule native vacant born with ⟨inserted, rfl⟩ | rule
    · exact .inl (insertion_at_rule trace inserted)
    · refine .inr ⟨rule, ?_⟩
      obtain ⟨_, _, _, _, ready, _⟩ := (trace.actual_child_birth bound rule vacant born).1
      have live := ready.2.1 (trace.actor time) rfl
      cases stamp : (trace.notes time).1 (trace.actor time) with
      | none => exact False.elim (live ((trace.births_agree time (by omega) _).mp stamp))
      | some parent => exact ⟨parent, rfl, (recorded_birth trace (by omega) stamp).2⟩
  · obtain ⟨_, _, _, _, _, endpoint⟩ := unload
    rw [endpoint] at born
    exact False.elim (born ((Transposition.mark_presence _ _ _ _).mpr ((replay_presence _ _ _ _).mpr vacant)))

/-- Every actual root or child birth has an address. Child ancestry
terminates because the allocating parent already held a live stamp. -/
theorem exists_address (trace : Trace program last) {name : Name} {birth : Nat}
    (actual : BornAt trace name birth) : ∃ address, Addressed trace birth address := by
  induction birth using Nat.strongRecOn generalizing name with
  | ind birth ih =>
    obtain ⟨positive, bounded, vacant, born⟩ := actual
    cases birth with
    | zero => omega
    | succ time =>
      have bound : time < last := by omega
      rcases new_entry trace bound vacant born with ⟨component, event⟩ | ⟨rule, parentBirth, parentLive, earlier⟩
      · exact ⟨_, .root bound event⟩
      · obtain ⟨parent, addressed⟩ := ih parentBirth (by omega) (recorded_birth trace (by omega) parentLive).1
        exact ⟨_, .child bound rule vacant born parentLive addressed⟩

/-- The same birth stamp cannot refer to two different addresses. -/
theorem Addressed.unique {trace : Trace program last} {birth : Nat} {a b : Address}
    (first : Addressed trace birth a) (second : Addressed trace birth b) : a = b := by
  induction first generalizing b with
  | root bounded event =>
    cases second with
    | root => rfl
    | child _ rule _ _ _ _ =>
      simp [Trace.rule, event, eventRule, ExchangeReplay.commandRule, EpisodeSelection.canBirth] at rule
  | child bounded rule vacant born stamp parent ih =>
    cases second with
    | root _ event =>
      simp [Trace.rule, event, eventRule, ExchangeReplay.commandRule, EpisodeSelection.canBirth] at rule
    | child _ _ _ _ otherStamp otherParent =>
      have equal := Option.some.inj (stamp.symm.trans otherStamp)
      subst equal
      rw [ih otherParent]

/-- Within a trace, the same address cannot refer to two different actual
birth stamps, even if a raw name was used for both births. -/
theorem Addressed.injective {trace : Trace program last} {birth otherBirth : Nat} {a b : Address}
    (first : Addressed trace birth a) (second : Addressed trace otherBirth b) (same : a = b) :
    birth = otherBirth := by
  induction first generalizing otherBirth b with
  | @root i name component bounded event =>
    cases second with
    | @root j otherName otherComponent _ otherEvent =>
      have ordered := occurrence_unique (isRootInsertion trace)
        (by simp [isRootInsertion, event]) (by simp [isRootInsertion, otherEvent]) (Address.root.inj same)
      exact congrArg Nat.succ ordered
    | child => cases same
  | @child i parentBirth name parentAddress bounded rule vacant born stamp parent ih =>
    cases second with
    | root => cases same
    | @child j otherParentBirth otherName otherParentAddress _ otherRule _ _ otherStamp otherParent =>
      obtain ⟨sameParent, sameOrdinal⟩ := Address.child.inj same
      have equal := ih otherParent sameParent
      subst otherParentBirth
      have ordered := occurrence_unique (isParentStage trace parentBirth)
        (by simp [isParentStage, rule, stamp]) (by simp [isParentStage, otherRule, otherStamp]) sameOrdinal
      exact congrArg Nat.succ ordered

/-- Corresponding actors retain their recursive birth addresses when
the event permutation preserves root-insertion order and parent stages. -/
structure StableActorAddresses {first second : Nat} (original : Trace program first)
    (moved : Trace program second) (expand : Nat → Nat) : Prop where
  retained : RetainedEvents original moved expand
  address : ∀ {i birth path}, i < second → (moved.notes i).1 (moved.actor i) = some birth →
    Addressed moved birth path → Addressed original (expand birth) path
  stage : ∀ {i birth}, i < second → isParentStage moved birth i = true →
    occurrencesBefore (isParentStage moved birth) i =
      occurrencesBefore (isParentStage original (expand birth)) (expand (i + 1) - 1)

theorem StableActorAddresses.refl (trace : Trace program last) : StableActorAddresses trace trace id :=
  ⟨.refl trace, fun _ _ path => path, fun _ _ => rfl⟩

theorem StableActorAddresses.trans {first middle final : Nat}
    {original : Trace program first} {intermediate : Trace program middle} {moved : Trace program final}
    {expand embed : Nat → Nat} (outer : StableActorAddresses original intermediate expand)
    (inner : StableActorAddresses intermediate moved embed) : StableActorAddresses original moved (expand ∘ embed) := by
  have inside {i : Nat} (bounded : i < final) : embed (i + 1) - 1 < middle := by
    have := inner.retained.stamp i bounded
    omega
  refine ⟨outer.retained.trans inner.retained, ?_, ?_⟩
  · intro i birth path bounded known addressed
    have tag := (inner.retained.actor_birth bounded).symm.trans (by rw [known])
    exact outer.address (inside bounded) tag (inner.address bounded known addressed)
  · intro i birth bounded selected
    have middleStage := (mapped_parent_stage inner.retained birth bounded).symm.trans selected
    have ordinal := (inner.stage bounded selected).trans (outer.stage (inside bounded) middleStage)
    have close : embed (i + 1) - 1 + 1 = embed (i + 1) := by
      have := inner.retained.stamp i bounded
      omega
    simpa only [Function.comp_apply, close] using ordinal

theorem StableActorAddresses.adjacent {original moved : Trace program last} {point : Nat}
    (bounded : point + 1 < last)
    (retained : RetainedEvents original moved (exchangedIndex point))
    (insertions : ¬ (isRootInsertion original point = true ∧ isRootInsertion original (point + 1) = true))
    (stages : EpisodeSelection.canBirth (original.rule point) = true →
      EpisodeSelection.canBirth (original.rule (point + 1)) = true → original.actor point ≠ original.actor (point + 1)) :
    StableActorAddresses original moved (exchangedIndex point) := by
  let source := exchangedCut point
  let stamp := exchangedIndex point
  have stampLayout (i : Nat) : stamp (i + 1) = source i + 1 := exchanged_stamp point i
  have sourceBound {i : Nat} (inside : i < last) : source i < last := by
    have keys := (retained.stamp i inside).2
    rw [exchanged_stamp] at keys
    exact keys
  have labels (i : Nat) (inside : i < last) : moved.event i = original.event (source i) := by
    simpa only [exchanged_stamp, Nat.add_sub_cancel] using retained.label i inside
  have actorTags (i : Nat) (inside : i < last) :
      ((moved.notes i).1 (moved.actor i)).map stamp = (original.notes (source i)).1 (original.actor (source i)) := by
    simpa only [exchanged_stamp, Nat.add_sub_cancel] using retained.actor_birth inside
  have rules (i : Nat) (inside : i < last) : moved.rule i = original.rule (source i) := by
    simp only [Trace.rule, labels i inside]
  have rootTests (i : Nat) (inside : i < last) : isRootInsertion moved i = isRootInsertion original (source i) := by
    simp only [isRootInsertion, labels i inside]
  have parentTests (birth : Nat) (i : Nat) (inside : i < last) :
      isParentStage moved birth i = isParentStage original (stamp birth) (source i) := by
    simpa only [exchanged_stamp, Nat.add_sub_cancel] using mapped_parent_stage retained birth inside
  have parentSeparate (birth : Nat) :
      ¬ (isParentStage original birth point = true ∧ isParentStage original birth (point + 1) = true) := by
    rintro ⟨a, b⟩
    simp only [isParentStage, Bool.and_eq_true, beq_iff_eq] at a b
    exact stages a.1 b.1 (born_unique original (recorded_birth original (by omega) a.2).1
      (recorded_birth original (by omega) b.2).1)
  have transport {birth path} (addressed : Addressed moved birth path) {name : Name}
      (born : BornAt original name (stamp birth)) : Addressed original (stamp birth) path := by
    induction addressed generalizing name with
    | @root i actor component inside event =>
      have oldEvent : original.event (source i) = .command (.insert actor component) := (labels i inside).symm.trans event
      have ordinal := occurrence_exchanged rootTests bounded inside (by simp [isRootInsertion, event]) insertions
      rw [stampLayout, ordinal]
      exact .root (sourceBound inside) oldEvent
    | @child i parentBirth actor parent inside rule _ _ tag _ ih =>
      have parentTag : (original.notes (source i)).1 (original.actor (source i)) = some (stamp parentBirth) :=
        (actorTags i inside).symm.trans (by simp only [tag, Option.map_some])
      have parentBorn := (recorded_birth original (Nat.le_of_lt (sourceBound inside)) parentTag).1
      have earlier : BornAt original name (source i + 1) := stampLayout i ▸ born
      have ordinal := occurrence_exchanged (parentTests parentBirth) bounded inside
        (by simp [isParentStage, rule, tag]) (parentSeparate (stamp parentBirth))
      rw [stampLayout, ordinal]
      exact .child (sourceBound inside) ((rules i inside).symm ▸ rule) earlier.2.2.1 earlier.2.2.2 parentTag (ih parentBorn)
  refine ⟨retained, ?_, ?_⟩
  · intro i birth path inside tag address
    have sourceTag : (original.notes (source i)).1 (original.actor (source i)) = some (stamp birth) :=
      (actorTags i inside).symm.trans (by simp only [tag, Option.map_some])
    exact transport address (recorded_birth original (Nat.le_of_lt (sourceBound inside)) sourceTag).1
  · intro i birth inside selected
    simpa only [exchanged_stamp, Nat.add_sub_cancel] using
      occurrence_exchanged (parentTests birth) bounded inside selected (parentSeparate (stamp birth))

/-- The target of an actual retirement or removal has a unique address
derived from its pre-command birth stamp. -/
theorem command_has_address (trace : Trace program last) {time : Nat} (bound : time < last)
    {target : Name} (event : trace.event time = .command (.retire target) ∨
      trace.event time = .command (.remove target)) :
    ∃ birth address, (trace.notes time).1 target = some birth ∧ Addressed trace birth address ∧
      ∀ other, Addressed trace birth other → address = other := by
  obtain ⟨birth, _, _, _, _, tag, _⟩ := trace.retire_remove_birth bound event
  obtain ⟨address, found⟩ := exists_address trace (recorded_birth trace (Nat.le_of_lt bound) tag).1
  exact ⟨_, address, tag, found, fun _ other => found.unique other⟩

noncomputable def addressOf (trace : Trace program last) (birth : Nat) : Option Address := by
  classical
  exact if found : ∃ address, Addressed trace birth address then some (Classical.choose found) else none

theorem addressOf_eq_some (trace : Trace program last) {birth : Nat} {address : Address} :
    addressOf trace birth = some address ↔ Addressed trace birth address := by
  classical
  unfold addressOf
  split
  · rename_i found
    constructor
    · intro same
      exact Option.some.inj same ▸ Classical.choose_spec found
    · intro known
      exact congrArg some ((Classical.choose_spec found).unique known)
  · rename_i impossible
    constructor
    · intro wrong
      cases wrong
    · intro known
      exact False.elim (impossible ⟨_, known⟩)

inductive AddressedCommand (Name Key Code : Type u) where
  | insert (name : Name) (component : Component Key Code)
  | retire (target : Address) (component : Component Key Code)
  | remove (target : Address) (component : Component Key Code)

/-- Components are read from the row actually targeted by the command.
Retirement and removal carry the recursive birth address. -/
noncomputable def targetAt (trace : Trace program last) (time : Nat) (name : Name) :
    Option (Address × Component Key Code) :=
  ((trace.notes time).1 name).bind fun birth =>
    (addressOf trace birth).bind fun address =>
      (trace.state time name).bind fun row => some (address, row.component)

theorem targetAt_eq_some (trace : Trace program last) {time : Nat} {name : Name}
    {address : Address} {component : Component Key Code} :
    targetAt trace time name = some (address, component) ↔
      ∃ birth row, (trace.notes time).1 name = some birth ∧ Addressed trace birth address ∧
        trace.state time name = some row ∧ row.component = component := by
  classical
  unfold targetAt
  simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq, ← addressOf_eq_some trace]
  constructor
  · rintro ⟨birth, born, path, known, row, found, rfl, rfl⟩
    exact ⟨birth, row, born, known, found, rfl⟩
  · rintro ⟨birth, row, born, known, found, rfl⟩
    exact ⟨birth, born, address, known, row, found, rfl, rfl⟩

theorem targetAt_command (trace : Trace program last) {time : Nat} (bound : time < last)
    {name : Name} (event : trace.event time = .command (.retire name) ∨
      trace.event time = .command (.remove name)) :
    ∃ address component, targetAt trace time name = some (address, component) := by
  obtain ⟨birth, row, _, _, present, recorded, _⟩ := trace.retire_remove_birth bound event
  obtain ⟨address, known⟩ := exists_address trace (recorded_birth trace (Nat.le_of_lt bound) recorded).1
  exact ⟨address, row.component, (targetAt_eq_some trace).mpr ⟨birth + 1, row, recorded, known, present, rfl⟩⟩

/-- A retained retirement or removal targets the same birth and component.
Its two addresses can use different ordinals after the history changes. -/
theorem retained_command_target {length : Nat} {original : Trace program last} {compact : Trace program length}
    {expand : Nat → Nat} (retained : RetainedEvents original compact expand) {i : Nat} (bound : i < length)
    {name : Name} (command : compact.event i = .command (.retire name) ∨ compact.event i = .command (.remove name)) :
    let cut := expand (i + 1) - 1
    ∃ birth newAddress oldAddress component,
      Addressed compact birth newAddress ∧ Addressed original (expand birth) oldAddress ∧
      targetAt compact i name = some (newAddress, component) ∧
      targetAt original cut name = some (oldAddress, component) := by
  let cut := expand (i + 1) - 1
  have bounded : cut < last := by
    have := retained.stamp i bound
    dsimp only [cut]
    omega
  have oldCommand : original.event cut = .command (.retire name) ∨ original.event cut = .command (.remove name) := by
    rw [← retained.label i bound]
    exact command
  have actor {event : Event Name Key Code}
      (known : event = .command (.retire name) ∨ event = .command (.remove name)) : Vestigial.eventActor event = name := by
    rcases known with rfl | rfl <;> rfl
  obtain ⟨birth, row, _, _, present, tag, _⟩ := compact.retire_remove_birth bound command
  obtain ⟨old, previous, _, _, oldPresent, oldTag, _⟩ := original.retire_remove_birth bounded oldCommand
  have same := retained.actor i bound
  change GuardedSuffix.actorSource (compact.state i) (reindexNotes expand (compact.notes i)) (compact.event i) =
    GuardedSuffix.actorSource (original.state cut) (original.notes cut) (original.event cut) at same
  simp only [GuardedSuffix.actorSource, actor command, actor oldCommand, reindexNotes, tag, oldTag, present, oldPresent,
    Option.map_some, Prod.mk.injEq, Option.some.injEq] at same
  obtain ⟨newAddress, addressed⟩ := exists_address compact (recorded_birth compact (Nat.le_of_lt bound) tag).1
  obtain ⟨oldAddress, oldAddressed⟩ := exists_address original (recorded_birth original (Nat.le_of_lt bounded) oldTag).1
  exact ⟨birth + 1, newAddress, oldAddress, row.component, addressed, same.1.symm ▸ oldAddressed,
    (targetAt_eq_some compact).mpr ⟨_, row, tag, addressed, present, rfl⟩,
    (targetAt_eq_some original).mpr ⟨_, previous, oldTag, oldAddressed, oldPresent, same.2.symm⟩⟩

noncomputable def commandAt (trace : Trace program last) (time : Nat) : Option (AddressedCommand Name Key Code) :=
  match trace.event time with
  | .command (.insert name component) => some (.insert name component)
  | .command (.retire name) => (targetAt trace time name).map fun target => .retire target.1 target.2
  | .command (.remove name) => (targetAt trace time name).map fun target => .remove target.1 target.2
  | .lifecycle _ _ => none

/-- A legal command contributes exactly one addressed input even after
deletion and reuse of earlier names. -/
theorem commandAt_none (trace : Trace program last) {time : Nat} (bound : time < last) :
    commandAt trace time = none ↔ ∃ kind actor, trace.event time = .lifecycle kind actor := by
  cases event : trace.event time with
  | lifecycle kind actor => simp [commandAt, event]
  | command command =>
    cases command with
    | insert => simp [commandAt, event]
    | retire =>
      obtain ⟨_, _, found⟩ := targetAt_command trace bound (.inl event)
      simp [commandAt, event, found]
    | remove =>
      obtain ⟨_, _, found⟩ := targetAt_command trace bound (.inr event)
      simp [commandAt, event, found]

noncomputable def orchestrationInput (trace : Trace program last) : List (AddressedCommand Name Key Code) :=
  (List.range last).filterMap (commandAt trace)

/-- A value interpretation preserves the addressed orchestration input
when it preserves the labels, live stamps and component declarations. -/
theorem orchestrationInput_of_representation {OtherValue OtherError : Type u}
    {otherProgram : Code → Instruction Name Key OtherValue Code OtherError}
    (source : Trace program last) (target : Trace otherProgram last)
    (events : ∀ i, i < last → source.event i = target.event i)
    (stamps : ∀ i, i ≤ last → (source.notes i).1 = (target.notes i).1)
    (components : ∀ i, i ≤ last → ∀ name,
      (source.state i name).map Fiber.component = (target.state i name).map Fiber.component) :
    orchestrationInput source = orchestrationInput target := by
  have presence (i : Nat) (bounded : i ≤ last) (name : Name) :
      source.state i name = none ↔ target.state i name = none := by
    have same := components i bounded name
    cases left : source.state i name <;> cases right : target.state i name <;> simp_all
  have addresses (birth : Nat) : addressOf source birth = addressOf target birth := by
    cases left : addressOf source birth with
    | some path =>
      exact ((addressOf_eq_some target).mpr ((addressOf_eq_some source).mp left
        |>.transport_representation events presence stamps)).symm
    | none =>
      cases right : addressOf target birth with
      | none => rfl
      | some path =>
        have known := ((addressOf_eq_some target).mp right).transport_representation
          (fun i bounded => (events i bounded).symm)
          (fun i bounded name => (presence i bounded name).symm)
          (fun i bounded => (stamps i bounded).symm)
        exact False.elim (Option.noConfusion (left.symm.trans ((addressOf_eq_some source).mpr known)))
  unfold orchestrationInput
  change (List.range last).filterMap (id ∘ commandAt source) =
    (List.range last).filterMap (id ∘ commandAt target)
  rw [← List.filterMap_map, ← List.filterMap_map]
  congr 1
  apply List.map_congr_left
  intro cut member
  have bounded := List.mem_range.mp member
  have targetSame (name : Name) : targetAt source cut name = targetAt target cut name := by
    unfold targetAt
    rw [stamps cut (by omega)]
    simp only [addresses]
    congr 1
    funext birth
    congr 1
    funext path
    have mapped {Row : Type u} (row : Option Row) (component : Row → Component Key Code) :
        (row.bind fun value => some (path, component value)) =
          (row.map component).map (fun payload => (path, payload)) := by
      cases row <;> rfl
    rw [mapped, mapped, components cut (by omega)]
  unfold commandAt
  rw [events cut bounded]
  cases target.event cut with
  | lifecycle => rfl
  | command cmd => cases cmd <;> simp only [targetSame]

private theorem root_insert_renamed (p : Renaming.Permutation Name) (trace : Trace program last) :
    isRootInsertion (GuardedRenaming.trace p trace) = isRootInsertion trace := by
  funext time
  unfold isRootInsertion
  change (match GuardedRenaming.event p (trace.event time) with
    | .command (.insert _ _) => true
    | _ => false) = _
  cases trace.event time with
  | lifecycle => rfl
  | command command => cases command <;> rfl

private theorem stage_renamed (p : Renaming.Permutation Name) (trace : Trace program last) (parent : Nat) :
    isParentStage (GuardedRenaming.trace p trace) parent = isParentStage trace parent := by
  funext time
  have rule : (GuardedRenaming.trace p trace).rule time = trace.rule time := by
    change eventRule (GuardedRenaming.event p (trace.event time)) = eventRule (trace.event time)
    cases trace.event time with
    | lifecycle => rfl
    | command command => cases command <;> rfl
  have born : ((GuardedRenaming.trace p trace).notes time).1
      ((GuardedRenaming.trace p trace).actor time) = (trace.notes time).1 (trace.actor time) := by
    change (GuardedRenaming.notes p (trace.notes time)).1 (Vestigial.eventActor
      (GuardedRenaming.event p (trace.event time))) = _
    rw [GuardedRenaming.actor_event, GuardedRenaming.note_birth]
    rfl
  simp only [isParentStage, rule, born]

/-- Moving all raw names through a permutation keeps the birth addresses
and every parent-relative stage ordinal. -/
theorem Addressed.renamed {trace : Trace program last} {birth : Nat} {path : Address}
    (addressed : Addressed trace birth path) (p : Renaming.Permutation Name) :
    Addressed (GuardedRenaming.trace p trace) birth path := by
  induction addressed with
  | @root time name component bounded event =>
    have moved : (GuardedRenaming.trace p trace).event time = .command (.insert (p.toFun name) component) := by
      change GuardedRenaming.event p (trace.event time) = _
      rw [event]
      rfl
    simpa only [root_insert_renamed p trace] using (Addressed.root bounded moved)
  | @child time parentBirth name parent bounded rule vacant born stamp addressed ih =>
    let moved := GuardedRenaming.trace p trace
    have newRule : EpisodeSelection.canBirth (moved.rule time) = true := by
      change EpisodeSelection.canBirth (eventRule (GuardedRenaming.event p (trace.event time))) = true
      cases event : trace.event time with
      | lifecycle kind actor => simpa [Trace.rule, event, GuardedRenaming.event] using rule
      | command command =>
        cases command <;> simp [Trace.rule, event, eventRule, ExchangeReplay.commandRule, EpisodeSelection.canBirth] at rule
    have newStamp : (moved.notes time).1 (moved.actor time) = some parentBirth := by
      change (GuardedRenaming.notes p (trace.notes time)).1
        (Vestigial.eventActor (GuardedRenaming.event p (trace.event time))) = _
      rw [GuardedRenaming.actor_event, GuardedRenaming.note_birth]
      exact stamp
    have newVacant : moved.state time (p.toFun name) = none := by
      change Renaming.registry p (trace.state time) (p.toFun name) = none
      simp [vacant]
    have newBorn : moved.state (time + 1) (p.toFun name) ≠ none := by
      change Renaming.registry p (trace.state (time + 1)) (p.toFun name) ≠ none
      simpa using born
    simpa only [moved, stage_renamed p trace parentBirth] using
      (Addressed.child bounded newRule newVacant newBorn newStamp ih)

theorem targetAt_renamed (trace : Trace program last) (p : Renaming.Permutation Name)
    {time : Nat} {name : Name} {path : Address} {component : Component Key Code}
    (target : targetAt trace time name = some (path, component)) :
    targetAt (GuardedRenaming.trace p trace) time (p.toFun name) = some (path, component) := by
  obtain ⟨birth, row, tagged, pathFound, found, payload⟩ := (targetAt_eq_some trace).mp target
  refine (targetAt_eq_some _).mpr ⟨birth, Renaming.fiber p row, ?_, pathFound.renamed p, ?_, payload⟩
  · change (GuardedRenaming.notes p (trace.notes time)).1 (p.toFun name) = _
    rwa [GuardedRenaming.note_birth]
  · change Renaming.registry p (trace.state time) (p.toFun name) = _
    simp [found]

def AddressedCommand.renameInsertions (p : Renaming.Permutation Name) :
    AddressedCommand Name Key Code → AddressedCommand Name Key Code
  | .insert name component => .insert (p.toFun name) component
  | .retire target component => .retire target component
  | .remove target component => .remove target component

theorem commandAt_renamed (trace : Trace program last) (p : Renaming.Permutation Name) {time : Nat}
    (bounded : time < last) :
    commandAt (GuardedRenaming.trace p trace) time = (commandAt trace time).map (AddressedCommand.renameInsertions p) := by
  have eventAt : (GuardedRenaming.trace p trace).event time = GuardedRenaming.event p (trace.event time) := rfl
  cases event : trace.event time with
  | lifecycle => simp [commandAt, event, eventAt, GuardedRenaming.event]
  | command command =>
    cases command with
    | insert => simp [commandAt, event, eventAt, GuardedRenaming.event, GuardedRenaming.command,
        AddressedCommand.renameInsertions]
    | retire =>
      obtain ⟨_, _, target⟩ := targetAt_command trace bounded (.inl event)
      have moved := targetAt_renamed trace p target
      simp [commandAt, event, eventAt, GuardedRenaming.event, GuardedRenaming.command,
        AddressedCommand.renameInsertions, target, moved]
    | remove =>
      obtain ⟨_, _, target⟩ := targetAt_command trace bounded (.inr event)
      have moved := targetAt_renamed trace p target
      simp [commandAt, event, eventAt, GuardedRenaming.event, GuardedRenaming.command,
        AddressedCommand.renameInsertions, target, moved]

/-- A raw renaming only changes the external insertion payload's name.
Each later command is still addressed to the same birth. -/
theorem orchestrationInput_renamed (trace : Trace program last) (p : Renaming.Permutation Name) :
    orchestrationInput (GuardedRenaming.trace p trace) =
      (orchestrationInput trace).map (AddressedCommand.renameInsertions p) := by
  unfold orchestrationInput
  rw [List.map_filterMap]
  have terms (cuts : List Nat) (bounded : ∀ time ∈ cuts, time < last) :
      cuts.filterMap (commandAt (GuardedRenaming.trace p trace)) =
        cuts.filterMap (fun time => (commandAt trace time).map (AddressedCommand.renameInsertions p)) := by
    induction cuts with
    | nil => rfl
    | cons time tail ih =>
      simp only [List.filterMap_cons, commandAt_renamed trace p (bounded time List.mem_cons_self)]
      rw [ih (fun cut member => bounded cut (List.mem_cons_of_mem _ member))]
  exact terms _ (fun _ member => List.mem_range.mp member)

end Cordis.Repairs.GuardedBirthAddresses
