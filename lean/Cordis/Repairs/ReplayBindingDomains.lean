import Cordis.Repairs.GuardedHistory

/-! A saved ordinary inverse requires the binding it captured. The
occupancy invariant accounts for actual LIFO replay and proves that a
restriction cannot leave a later ordinary inverse looking at an empty slot.
-/
namespace Cordis.Repairs.ReplayBindingDomains
open Calculus Stages StageRecovery GuardedHistory IncarnationReplay
open PartialReplayRegistry (ReplayEvent Coeffects SlotHistory saved)
open PartialReplayHistory (run)
open InterleavedRecovery (Avoids)

universe u
variable {Name Key Value Code Error : Type u} [DecidableEq Name] [DecidableEq Key]
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "I" => Inverse Name Key Value
local notation "C" => Capture Name Key Value

private def nextOccupancy (owner : Name) (key : Key) (inverse : I) (occupied : Bool) : Bool :=
  match inverse with
  | .restrict src slot => if owner = src ∧ key = slot then false else occupied
  | _ => occupied

/-- At a single slot, every ordinary inverse that addresses it must find
a binding before making its edit. Other inverses leave occupancy alone. -/
def Ready (owner : Name) (key : Key) : List I → Bool → Prop
  | [], _ => True
  | token :: remaining, occupied =>
    (¬ Avoids owner key token → occupied = true) ∧
    Ready owner key remaining (nextOccupancy owner key token occupied)

private theorem occupancy_mono (owner : Name) (key : Key) (token : I) {before after : Bool}
    (kept : before = true → after = true) :
    nextOccupancy owner key token before = true → nextOccupancy owner key token after = true := by
  cases token <;> simp only [nextOccupancy]
  case restrict =>
    split
    · simp
    · exact kept
  all_goals exact kept

private theorem ready_mono (owner : Name) (key : Key) (word : List I) {before after : Bool}
    (kept : before = true → after = true) (ready : Ready owner key word before) :
    Ready owner key word after := by
  induction word generalizing before after with
  | nil => trivial
  | cons head rest ih =>
    exact ⟨fun touched => kept (ready.1 touched), ih (occupancy_mono owner key head kept) ready.2⟩

private theorem ready_subword (owner : Name) (key : Key) {word original : List I}
    (chosen : word.Sublist original) {occupied : Bool} (ready : Ready owner key original occupied) :
    Ready owner key word occupied := by
  induction chosen generalizing occupied with
  | slnil => trivial
  | cons head _ ih =>
    have keeps : nextOccupancy owner key head occupied = true → occupied = true := by
      cases head <;> simp only [nextOccupancy]
      case restrict => split <;> simp
      all_goals exact id
    exact ready_mono owner key _ keeps (ih ready.2)
  | cons₂ head _ ih => exact ⟨ready.1, ih ready.2⟩

private theorem ready_avoiding (owner : Name) (key : Key) (word : List I)
    (avoids : ∀ token ∈ word, Avoids owner key token) (occupied : Bool) :
    Ready owner key word occupied := by
  induction word generalizing occupied with
  | nil => trivial
  | cons head rest ih =>
    exact ⟨fun touches => False.elim (touches (avoids head List.mem_cons_self)),
      ih (fun token member => avoids token (List.mem_cons_of_mem _ member)) _⟩

private theorem undo_occupancy (state : R) (owner : Name) (key : Key) (token : I) :
    (tableAt (Stages.undo token state) owner key).isSome =
      nextOccupancy owner key token (tableAt state owner key).isSome := by
  cases token with
  | unit => rfl
  | retire => apply congrArg Option.isSome; exact tableAt_retire _ _ _ _
  | restrict => simp only [tableAt_restrict, nextOccupancy]; split <;> rfl
  | operate =>
    rw [tableAt_operate]
    split
    · rename_i selected
      simp [nextOccupancy, selected.1, selected.2]
    · rfl

private theorem discharge_occupancy (state : R) (owner : Name) (key : Key) (word : List I)
    (keepsSlot : Inverse.restrict owner key ∉ word) :
    (tableAt (discharge Stages.undo word state) owner key).isSome = (tableAt state owner key).isSome := by
  induction word generalizing state with
  | nil => rfl
  | cons head rest ih =>
    change (tableAt (discharge Stages.undo rest (Stages.undo head state)) owner key).isSome = _
    rw [ih _ (fun found => keepsSlot (List.mem_cons_of_mem _ found)), undo_occupancy]
    cases head with
    | restrict src slot =>
      have other : ¬ (owner = src ∧ key = slot) := by
        rintro ⟨rfl, rfl⟩
        exact keepsSlot List.mem_cons_self
      rw [nextOccupancy, if_neg other]
    | _ => rfl

variable {program : Code → Instruction Name Key Value Code Error}

private theorem landing_occupancy (owner : Name) (key : Key) {actor : Name} {code : Code}
    {before after : R} {token : I} {next : Option Code} (land : Land program actor code before after token next) :
    let was := (tableAt before owner key).isSome
    let now := (tableAt after owner key).isSome
    (was = true → now = true) ∧ (¬ Avoids owner key token → now = true) ∧
      nextOccupancy owner key token now = was := by
  dsimp only
  cases land with
  | unit => simp [Avoids, nextOccupancy]
  | instantiate _ _ _ component child _ ready =>
    have equal := (RuleEvaluation.Edit.insert child component (some actor)).preserves_tables before ready.1 owner key
    change tableAt before owner key = tableAt (put before child (fresh component (some actor))) owner key at equal
    rw [← equal]
    simp [Avoids, nextOccupancy]
  | provide _ _ _ row slot value _ found _ absent =>
    rw [PartialReplayRegistry.tableAt_write _ _ _ _ _ _ (by simp [found])]
    by_cases selected : owner = actor ∧ key = slot
    · obtain ⟨rfl, rfl⟩ := selected
      simp [tableAt, found, absent, nextOccupancy]
    · have other : ¬ (actor = owner ∧ slot = key) := fun same => selected ⟨same.1.symm, same.2.symm⟩
      simp [Avoids, nextOccupancy, selected, other]
  | operate _ _ _ slot call src input output inverse reply _ located called =>
    have bound := PartialReplayRegistry.located_value located
    have present : before src ≠ none := by
      intro absent
      simp [tableAt, absent] at bound
    rw [PartialReplayRegistry.tableAt_write _ _ _ _ _ _ present]
    by_cases selected : owner = src ∧ key = slot
    · obtain ⟨rfl, rfl⟩ := selected
      simp [bound, nextOccupancy]
    · have other : ¬ (src = owner ∧ slot = key) := fun same => selected ⟨same.1.symm, same.2.symm⟩
      simp [Avoids, nextOccupancy, selected, other]

private theorem step_ready {actor : Name} {before after : R}
    (step : ReplayEvent program actor before after)
    (routed : PartialReplayRouting.ScopedAccumulators before)
    (owner : Name) (key : Key)
    (old : ∀ name, Ready owner key (saved before name) (tableAt before owner key).isSome) :
    ∀ name, Ready owner key (saved after name) (tableAt after owner key).isSome := by
  intro name
  cases step with
  | control tables words =>
    rw [words, ← tables owner key]
    exact old name
  | capture land tables pushed presence =>
    rw [pushed name, ← tables owner key]
    obtain ⟨preserved, bound, restored⟩ := landing_occupancy owner key land
    by_cases acts : name = actor
    · rw [if_pos acts]
      exact ⟨bound, by rw [restored]; exact old name⟩
    · rw [if_neg acts]
      exact ready_mono owner key (saved before name) preserved (old name)
  | cleanup selected free tables cleared closed =>
    rw [cleared name]
    by_cases self : name = actor
    · rw [if_pos self]
      trivial
    rw [if_neg self]
    by_cases ownerUnloads : owner = actor
    · subst owner
      exact ready_avoiding actor key _ (PartialReplayRegistry.saved_avoids_unloader before actor key routed free name self) _
    · rw [← tables owner key, discharge_occupancy before owner key _
        (fun member => ownerUnloads (PartialReplayRegistry.saved_restriction_owner routed (selected.symm ▸ member)))]
      exact old name

/-- Every actually recorded word starts in the strict binding domain at
its cut. This includes an actor's own operation inverses. -/
theorem saved_ready {last : Nat} (trace : Trace program last) (time : Nat) (bounded : time ≤ last)
    (owner : Name) (key : Key) (actor : Name) :
    Ready owner key ((trace.notes time).2 actor |>.map Capture.token)
      (tableAt (trace.state time) owner key).isSome := by
  rw [trace.projects time bounded actor]
  revert actor
  induction time with
  | zero =>
    intro actor
    rw [trace.start]
    simp [saved, Ready]
  | succ time ih =>
    exact step_ready (trace.replayEvent (by omega : time < last))
      (trace.invariants time (by omega)).2 owner key (ih (by omega))

private theorem apply_occupancy (live : Name → Option Nat) (state : R) (owner : Name) (key : Key) (head : C) :
    (tableAt (head.apply live state) owner key).isSome =
      nextOccupancy owner key head.token (tableAt state owner key).isSome := by
  have equal := replay_tables live [head] (left := state) (right := state) (fun _ _ => rfl) owner key
  change tableAt (Stages.undo head.token state) owner key = tableAt (head.apply live state) owner key at equal
  rw [← equal, undo_occupancy]

private theorem suffix_ready (live : Name → Option Nat) (state : R) (owner : Name) (key : Key)
    (prefixWord suffixWord : List C)
    (ready : Ready owner key ((prefixWord ++ suffixWord).map Capture.token) (tableAt state owner key).isSome) :
    Ready owner key (suffixWord.map Capture.token) (tableAt (replay live prefixWord state) owner key).isSome := by
  induction prefixWord generalizing state with
  | nil => exact ready
  | cons head rest ih =>
    apply ih (head.apply live state)
    rw [apply_occupancy]
    exact ready.2

/-- The actual domain of an ordinary saved map includes the binding and,
for operations, a successful return from the partial inverse. Retirements
can be applied whether their captured incarnation is live or gone. -/
def InverseDefined (meaning : Coeffects program) (state : R) : I → Prop
  | .unit | .retire _ => True
  | .restrict owner key => tableAt state owner key ≠ none
  | .operate owner key inverse => ∃ input output,
      tableAt state owner key = some input ∧ meaning.denote key inverse input = some output

def WordDefined (meaning : Coeffects program) (live : Name → Option Nat) (word : List C) (state : R) : Prop :=
  ∀ prefixWord head suffixWord, word = prefixWord ++ head :: suffixWord →
    InverseDefined meaning (replay live prefixWord state) head.token

/-- A defined saved word remains defined when stopped after any prefix. -/
theorem WordDefined.take (meaning : Coeffects program) {live : Name → Option Nat} {word : List C} {state : R}
    (defined : WordDefined meaning live word state) (count : Nat) :
    WordDefined meaning live (word.take count) state := by
  intro earlier head later split
  apply defined earlier head (later ++ word.drop count)
  calc
    word = word.take count ++ word.drop count := (List.take_append_drop count word).symm
    _ = earlier ++ head :: (later ++ word.drop count) := by rw [split, List.append_assoc]; rfl

/-- Every selected subword has a defined slot projection. Missing slots
in an unselected coordinate are the identity in the slot projection. -/
theorem saved_subword_slot {last : Nat} (trace : Trace program last) (time : Nat) (bounded : time ≤ last)
    (meaning : Coeffects program) (actor owner : Name) (key : Key) {word : List C}
    (selected : word.Sublist ((trace.notes time).2 actor)) :
    run ((word.map Capture.token).map (PartialReplaySlots.project meaning.denote owner key))
      (tableAt (trace.state time) owner key) =
      some (tableAt (replay (trace.notes time).1 word (trace.state time)) owner key) := by
  have contained : (word.map Capture.token).Sublist (saved (trace.state time) actor) := by
    rw [← trace.projects time bounded actor]
    exact selected.map Capture.token
  obtain ⟨output, performed⟩ := PartialReplayRegistry.saved_subword_defined_of_history meaning actor owner key
    (trace.slot_history meaning time bounded owner key) contained
  rw [performed, replay_partial_slot meaning.denote meaning.agrees owner key _ _ _ output performed]

private theorem operate_at_prefix (meaning : Coeffects program) (live : Name → Option Nat) (state : R)
    (owner : Name) (key : Key) (inverse : Value → Value) {word prefixWord suffixWord : List C} {head : C}
    (splitWord : word = prefixWord ++ head :: suffixWord)
    (isOperation : head.token = .operate owner key inverse)
    (bound : (tableAt (replay live prefixWord state) owner key).isSome = true) {result : Option Value}
    (total : run ((word.map Capture.token).map (PartialReplaySlots.project meaning.denote owner key))
      (tableAt state owner key) = some result) :
    InverseDefined meaning (replay live prefixWord state) (.operate owner key inverse) := by
  let localMap := PartialReplaySlots.project meaning.denote owner key
  let initial := tableAt state owner key
  change run (word.map Capture.token |>.map localMap) initial = _ at total
  rw [splitWord, List.map_append, List.map_append, PartialReplayHistory.run_append] at total
  obtain ⟨value, prefixSuccess, tailSuccess⟩ := Option.bind_eq_some_iff.mp total
  have valueEq := replay_partial_slot meaning.denote meaning.agrees owner key live prefixWord state value prefixSuccess
  rw [valueEq] at bound
  cases value with
  | none => cases bound
  | some input =>
    simp only [List.map_cons, PartialReplayHistory.run_cons] at tailSuccess
    obtain ⟨output, called, _⟩ := Option.bind_eq_some_iff.mp tailSuccess
    change PartialReplaySlots.project meaning.denote owner key head.token (some input) = some output at called
    rw [isOperation] at called
    change ∃ input output, _ ∧ _
    cases result : meaning.denote key inverse input with
    | none => simp [PartialReplaySlots.project, PartialReplayHistory.keepMissing, result] at called
    | some final => exact ⟨input, final, valueEq, result⟩

private theorem word_defined_of_slots (meaning : Coeffects program) (live : Name → Option Nat)
    (state : R) (word : List C)
    (initial : ∀ owner key, Ready owner key (word.map Capture.token) (tableAt state owner key).isSome)
    (slots : ∀ owner key, ∃ value, run ((word.map Capture.token).map
      (PartialReplaySlots.project meaning.denote owner key)) (tableAt state owner key) = some value) :
    WordDefined meaning live word state := by
  intro prefixWord head suffixWord splitWord
  have ready (owner : Name) (key : Key) (touches : ¬ Avoids owner key head.token) :
      (tableAt (replay live prefixWord state) owner key).isSome = true := by
    have full := initial owner key
    rw [splitWord] at full
    exact (suffix_ready _ _ owner key prefixWord (head :: suffixWord) full).1 touches
  cases kind : head.token with
  | unit | retire => trivial
  | restrict owner key =>
    rw [InverseDefined]
    have occupied := ready owner key (by simp [kind, Avoids])
    intro unbound
    simp [unbound] at occupied
  | operate owner key inverse =>
    obtain ⟨value, performed⟩ := slots owner key
    exact operate_at_prefix meaning live state owner key inverse splitWord kind
      (ready owner key (by simp [kind, Avoids])) performed

/-- An in-order selection from one actual saved word stays in the strict
binding and partial callback domains at every replay prefix. -/
theorem saved_subword_defined {last : Nat} (trace : Trace program last) (time : Nat) (bounded : time ≤ last)
    (meaning : Coeffects program) (actor : Name) {word : List C}
    (chosen : word.Sublist ((trace.notes time).2 actor)) :
    WordDefined meaning (trace.notes time).1 word (trace.state time) :=
  word_defined_of_slots meaning (trace.notes time).1 (trace.state time) word
    (fun owner key => ready_subword owner key (chosen.map Capture.token) (saved_ready trace time bounded owner key actor))
    (fun owner key => ⟨_, saved_subword_slot trace time bounded meaning actor owner key chosen⟩)

/-- Every intermediate cut of the actual saved word satisfies the strict
binding domain and the partial callback domain for its next inverse. -/
theorem saved_word_defined {last : Nat} (trace : Trace program last) (time : Nat) (bounded : time ≤ last)
    (meaning : Coeffects program) (actor : Name) :
    WordDefined meaning (trace.notes time).1 ((trace.notes time).2 actor) (trace.state time) :=
  saved_subword_defined trace time bounded meaning actor (List.Sublist.refl _)

/-- Ordinary applications depend on the table at the captured coordinate.
Changing a retirement test only affects control, so table equivalence
suffices for transporting the domain of each following inverse. -/
theorem WordDefined.of_same_tables (meaning : Coeffects program) {before after : R}
    {live otherLive : Name → Option Nat} {word : List C}
    (defined : WordDefined meaning live word before) (tables : RuleEvaluation.TablesUnchanged before after) :
    WordDefined meaning otherLive word after := by
  intro prefixWord head suffixWord splitWord
  have valid := defined prefixWord head suffixWord splitWord
  have same (owner : Name) (key : Key) :
      tableAt (replay live prefixWord before) owner key = tableAt (replay otherLive prefixWord after) owner key := by
    exact ((replay_tables live prefixWord (left := before) (right := before) (fun _ _ => rfl)) owner key).symm.trans
      (replay_tables otherLive prefixWord tables owner key)
  cases kind : head.token with
  | unit | retire => trivial
  | restrict owner key =>
    rw [kind, InverseDefined] at valid
    simpa only [InverseDefined, ← same] using valid
  | operate owner key inverse =>
    rw [kind, InverseDefined] at valid
    simpa only [InverseDefined, ← same] using valid

private theorem atom_projection (meaning : Coeffects program) (live : Name → Option Nat)
    (state : R) (head : C) (defined : InverseDefined meaning state head.token) (owner : Name) (key : Key) :
    PartialReplaySlots.project meaning.denote owner key head.token (tableAt state owner key) =
      some (tableAt (head.apply live state) owner key) := by
  have equal := replay_tables live [head] (left := state) (right := state) (fun _ _ => rfl) owner key
  change tableAt (Stages.undo head.token state) owner key = tableAt (head.apply live state) owner key at equal
  rw [← equal]
  cases kind : head.token with
  | unit => rfl
  | retire => simp [PartialReplaySlots.project, Stages.undo, tableAt_retire]
  | restrict =>
    rw [tableAt_restrict]
    simp only [PartialReplaySlots.project]
    split <;> rfl
  | operate src slot inverse =>
    rw [tableAt_operate]
    by_cases touches : owner = src ∧ key = slot
    · obtain ⟨rfl, rfl⟩ := touches
      rw [kind, InverseDefined] at defined
      obtain ⟨input, output, bound, returned⟩ := defined
      simp [PartialReplaySlots.project, PartialReplayHistory.keepMissing, bound, returned,
        meaning.agrees key inverse input output returned]
    · simp [PartialReplaySlots.project, touches]

/-- An admitted word has a successful partial projection at each slot
and the projections describe the guarded result exactly. -/
theorem WordDefined.slot_projection (meaning : Coeffects program) (live : Name → Option Nat)
    (word : List C) (state : R) (defined : WordDefined meaning live word state) (owner : Name) (key : Key) :
    run ((word.map Capture.token).map (PartialReplaySlots.project meaning.denote owner key))
      (tableAt state owner key) = some (tableAt (replay live word state) owner key) := by
  induction word generalizing state with
  | nil => rfl
  | cons head tail ih =>
    have ready := defined [] head tail rfl
    have rest : WordDefined meaning live tail (head.apply live state) := by
      intro prefixWord capture suffixWord splitWord
      exact defined (head :: prefixWord) capture suffixWord (by rw [List.cons_append, ← splitWord])
    simp only [List.map_cons, PartialReplayHistory.run_cons, atom_projection meaning live state head ready owner key,
      Option.bind_some, replay]
    exact ih _ rest

/-- When the first actor is free to unload, the other actor's actual saved
word stays in domain even after replaying the first word. Without the
unload guard a restriction could erase another inverse's binding. -/
theorem second_word_defined {last : Nat} (trace : Trace program last) (time : Nat) (bounded : time ≤ last)
    (meaning : Coeffects program) {first second : Name} (different : first ≠ second)
    (free : ¬ Relied (trace.state time) first) :
    WordDefined meaning (trace.notes time).1 ((trace.notes time).2 second)
      (replay (trace.notes time).1 ((trace.notes time).2 first) (trace.state time)) := by
  let notes := trace.notes time
  let state := trace.state time
  let after := replay notes.1 (notes.2 first) state
  apply word_defined_of_slots meaning notes.1 after (notes.2 second)
  · intro owner key
    have routed := (trace.invariants time bounded).2
    by_cases clears : owner = first
    · subst owner
      apply ready_avoiding
      rw [trace.projects time bounded second]
      exact PartialReplayRegistry.saved_avoids_unloader state first key routed free second (Ne.symm different)
    · have onlyOwn : Inverse.restrict owner key ∉ (notes.2 first).map Capture.token := by
        rw [trace.projects time bounded first]
        exact fun member => clears (PartialReplayRegistry.saved_restriction_owner routed member)
      have result := replay_tables notes.1 (notes.2 first) (left := state) (right := state)
        (fun _ _ => rfl) owner key
      change tableAt (discharge Stages.undo ((notes.2 first).map Capture.token) state) owner key =
        tableAt after owner key at result
      rw [← result, discharge_occupancy state owner key _ onlyOwn]
      exact saved_ready trace time bounded owner key second
  · intro owner key
    obtain ⟨result, _, performed, _, _⟩ := PartialReplayRegistry.saved_words_commute_of_history meaning
      first second owner different key (trace.slot_history meaning time bounded owner key)
    dsimp only at performed
    rw [← trace.projects time bounded first, ← trace.projects time bounded second, List.map_append,
      PartialReplayHistory.run_append,
      saved_subword_slot trace time bounded meaning first owner key (List.Sublist.refl _),
      Option.bind_some] at performed
    exact ⟨result, performed⟩

end Cordis.Repairs.ReplayBindingDomains
