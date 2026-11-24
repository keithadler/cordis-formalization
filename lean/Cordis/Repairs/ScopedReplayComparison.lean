import Cordis.Repairs.ReplayBindingDomains
import Cordis.PaperStateObservation
import Cordis.TypedReplayContracts
import Cordis.Repairs.EpisodeAnnotations

/-! The accumulator in Equations (52) and (54) is a strict partial map.
Its probe scope retains the declaration at each captured ordinary slot.
Values and occupancy are read from the probe, and retirements use its
live birth stamps. -/
namespace Cordis.Repairs.ScopedReplayComparison
open Calculus Stages StageRecovery IncarnationReplay ReplayBindingDomains
open PartialReplayRegistry (Coeffects)
open PartialInverseObservation (MapRelated)
open Iterators (OptionRel)

universe u
variable {Name Key Value Code Error : Type u} [DecidableEq Name] [DecidableEq Key]
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "I" => Inverse Name Key Value
local notation "C" => Capture Name Key Value
local notation "Program" => Code → Instruction Name Key Value Code Error
variable {program : Code → Instruction Name Key Value Code Error}

def runCapture (meaning : Coeffects program) (live : Name → Option Nat) (capture : C) (state : R) : Option R :=
  match capture.token with
  | .unit | .retire _ => some (capture.apply live state)
  | .restrict owner key => (tableAt state owner key).map (fun _ => capture.apply live state)
  | .operate owner key inverse => ((tableAt state owner key).bind (meaning.denote key inverse)).map
      (fun _ => capture.apply live state)

def run (meaning : Coeffects program) (live : Name → Option Nat) (word : List C) : R → Option R :=
  PartialReplayHistory.run (word.map (runCapture meaning live))

theorem capture_success_iff (meaning : Coeffects program) (live : Name → Option Nat) (capture : C)
    (state output : R) : runCapture meaning live capture state = some output ↔
      InverseDefined meaning state capture.token ∧ capture.apply live state = output := by
  cases token : capture.token with
  | unit | retire => simp [runCapture, token, InverseDefined]
  | restrict owner key =>
    cases occupied : tableAt state owner key <;> simp [runCapture, token, InverseDefined, occupied]
  | operate owner key inverse =>
    simp only [runCapture, token, InverseDefined, Option.map_eq_some_iff, Option.bind_eq_some_iff]
    constructor
    · rintro ⟨value, ⟨input, bound, called⟩, result⟩
      exact ⟨⟨input, value, bound, called⟩, result⟩
    · rintro ⟨⟨input, value, bound, called⟩, result⟩
      exact ⟨value, ⟨input, bound, called⟩, result⟩

private theorem word_defined_cons (meaning : Coeffects program) (live : Name → Option Nat)
    (head : C) (tail : List C) (state : R) : WordDefined meaning live (head :: tail) state ↔
      InverseDefined meaning state head.token ∧ WordDefined meaning live tail (head.apply live state) := by
  constructor
  · intro defined
    exact ⟨defined [] head tail rfl, fun prefixWord capture suffixWord splitWord =>
      defined (head :: prefixWord) capture suffixWord (by rw [List.cons_append, ← splitWord])⟩
  · rintro ⟨first, rest⟩ prefixWord capture suffixWord splitWord
    cases prefixWord with
    | nil =>
      obtain ⟨rfl, _⟩ := List.cons.inj splitWord
      exact first
    | cons previous prefixWord =>
      obtain ⟨rfl, tailEq⟩ := List.cons.inj splitWord
      exact rest prefixWord capture suffixWord tailEq

/-- Success checks exactly the prefix domains of the actual guarded word,
and the endpoint is the paper's guarded accumulator application. -/
theorem success_iff (meaning : Coeffects program) (live : Name → Option Nat) (word : List C)
    (state output : R) : run meaning live word state = some output ↔
      WordDefined meaning live word state ∧ replay live word state = output := by
  induction word generalizing state with
  | nil => simp [run, WordDefined, replay]
  | cons head tail ih =>
    change ((runCapture meaning live head state).bind (run meaning live tail)) = some output ↔ _
    rw [Option.bind_eq_some_iff, word_defined_cons]
    constructor
    · rintro ⟨middle, first, rest⟩
      obtain ⟨ready, rfl⟩ := (capture_success_iff meaning live head state middle).mp first
      obtain ⟨defined, reached⟩ := (ih (head.apply live state)).mp rest
      exact ⟨⟨ready, defined⟩, reached⟩
    · rintro ⟨⟨ready, defined⟩, reached⟩
      exact ⟨head.apply live state, (capture_success_iff meaning live head state _).mpr ⟨ready, rfl⟩,
        (ih (head.apply live state)).mpr ⟨defined, reached⟩⟩

private def ProvidesAt (state : R) (owner : Name) (key : Key) : Prop :=
  ∃ row, state owner = some row ∧ row.component.provides key = true

private def CaptureScope (state : R) (capture : C) : Prop :=
  match capture.token with
  | .restrict owner key | .operate owner key _ => ProvidesAt state owner key
  | _ => True

/-- Probe admission fixes the declarations needed by the captured ordinary
slots. Whether their bindings exist is tested by the partial replay itself. -/
def Scope (word : List C) (state : R) : Prop :=
  MediatedRegistry.Allowed state ∧ ∀ capture ∈ word, CaptureScope state capture

private theorem capture_allowed (live : Name → Option Nat) (capture : C) {state : R}
    (allowed : MediatedRegistry.Allowed state) : MediatedRegistry.Allowed (capture.apply live state) := by
  rcases capture with ⟨token, stamp⟩
  cases token with
  | unit => exact allowed
  | restrict owner key => exact MediatedRegistry.inverse_allowed (.restrict owner key) allowed
  | operate owner key inverse => exact MediatedRegistry.inverse_allowed (.operate owner key inverse) allowed
  | retire child =>
    simp only [Capture.apply]
    split
    · exact MediatedRegistry.inverse_allowed (.retire child) allowed
    · exact allowed

theorem replay_allowed (live : Name → Option Nat) (word : List C) {state : R}
    (allowed : MediatedRegistry.Allowed state) : MediatedRegistry.Allowed (replay live word state) := by
  induction word generalizing state with
  | nil => exact allowed
  | cons head tail ih => exact ih (capture_allowed live head allowed)

theorem trace_allowed {last : Nat} (trace : GuardedHistory.Trace program last) (time : Nat) (bounded : time ≤ last) :
    MediatedRegistry.Allowed (trace.state time) := by
  induction time with
  | zero =>
    rw [trace.start]
    exact ⟨Safety.empty_tree, ⟨[], fun _ _ impossible => by cases impossible⟩, Safety.empty_owned, WellFormed.disjoint_empty⟩
  | succ time ih =>
    have earlier := ih (by omega)
    rcases GuardedHistory.transition_cases (trace.step time (by omega : time < last)).1 with
      native | ⟨actor, event, unloading⟩
    · exact MediatedRegistry.step_allowed program native.toCalculus earlier
    · obtain ⟨_, _, _, _, _, endpoint⟩ := unloading
      rw [endpoint]
      exact MediatedRegistry.mark_allowed actor .inactive (replay_allowed _ _ earlier)

private theorem provides_after_capture (live : Name → Option Nat) (capture : C) {state : R}
    {owner : Name} {key : Key} (declared : ProvidesAt state owner key) :
    ProvidesAt (capture.apply live state) owner key := by
  obtain ⟨row, found, provides⟩ := declared
  obtain ⟨entry, retained, same, _, _⟩ := replay_keeps_control live [capture] state owner row found
  exact ⟨entry, retained, by simpa only [same] using provides⟩

private theorem scope_tail (live : Name → Option Nat) (head : C) (tail : List C) {state : R}
    (compatible : Scope (head :: tail) state) : Scope tail (head.apply live state) := by
  refine ⟨capture_allowed live head compatible.1, fun capture member => ?_⟩
  have source := compatible.2 capture (List.mem_cons_of_mem head member)
  cases token : capture.token with
  | unit | retire => simp [CaptureScope, token]
  | restrict owner key | operate owner key _ =>
    simp only [CaptureScope, token] at source ⊢
    exact provides_after_capture live head source

/-- The unconsumed captures retain their compatible probe domains after
each prefix of the guarded word. -/
theorem scope_after_prefix (live : Name → Option Nat) (prefixWord rest : List C) {state : R}
    (compatible : Scope (prefixWord ++ rest) state) : Scope rest (replay live prefixWord state) := by
  induction prefixWord generalizing state with
  | nil => exact compatible
  | cons head tail ih => exact ih (scope_tail live head _ compatible)

private theorem scope_before_capture (live : Name → Option Nat) (earlier capture : C) {state : R}
    (later : CaptureScope (earlier.apply live state) capture) : CaptureScope state capture := by
  have restore (owner : Name) (key : Key) (provides : ProvidesAt (earlier.apply live state) owner key) :
      ProvidesAt state owner key := by
    obtain ⟨row, present, declared⟩ := provides
    cases original : state owner with
    | none =>
      rw [(earlier.presence live state owner).mpr original] at present
      cases present
    | some previous =>
      obtain ⟨retained, found, same, _, _⟩ := replay_keeps_control live [earlier] state owner previous original
      change earlier.apply live state owner = some retained at found
      cases Option.some.inj (found.symm.trans present)
      exact ⟨previous, original, by simpa only [same] using declared⟩
  cases token : capture.token with
  | restrict owner key | operate owner key _ =>
    simp only [CaptureScope, token] at later ⊢
    exact restore owner key later
  | unit | retire => simp [CaptureScope, token]

omit [DecidableEq Name] [DecidableEq Key] in
private theorem capture_scope_of_defined (meaning : Coeffects program) (capture : C) {state : R}
    (allowed : MediatedRegistry.Allowed state) (ready : InverseDefined meaning state capture.token) :
    CaptureScope state capture := by
  have declared (owner : Name) (key : Key) (binding : tableAt state owner key ≠ none) : ProvidesAt state owner key := by
    cases found : state owner with
    | none => simp [tableAt, found] at binding
    | some row =>
      exact ⟨row, found, allowed.2.2.1 owner row key found (by simpa only [tableAt, found, Option.bind_some] using binding)⟩
  cases token : capture.token with
  | unit | retire => simp [CaptureScope, token]
  | restrict owner key =>
    simp only [CaptureScope, token, InverseDefined] at ready ⊢
    exact declared owner key ready
  | operate owner key inverse =>
    simp only [CaptureScope, token, InverseDefined] at ready ⊢
    obtain ⟨input, output, bound, _⟩ := ready
    exact declared owner key (by rw [bound]; exact Option.some_ne_none input)

/-- Actual definedness supplies every declaration in the replay scope.
Undo never removes a provider or changes its component, so a declaration
found at a replay prefix already existed at the initial probe. -/
theorem scope_of_defined (meaning : Coeffects program) (live : Name → Option Nat) (word : List C) {state : R}
    (allowed : MediatedRegistry.Allowed state) (defined : WordDefined meaning live word state) : Scope word state := by
  induction word generalizing state with
  | nil => exact ⟨allowed, by simp⟩
  | cons head tail ih =>
    obtain ⟨first, rest⟩ := (word_defined_cons meaning live head tail state).mp defined
    have later := ih (capture_allowed live head allowed) rest
    refine ⟨allowed, fun capture member => ?_⟩
    rcases List.mem_cons.mp member with rfl | inTail
    · exact capture_scope_of_defined meaning capture allowed first
    · exact scope_before_capture live head capture (later.2 capture inTail)

section Comparison
variable [Setoid Value]
local notation "Observed" => PaperStateObservation.TablesRelatedAt (fun _ : Key => (inferInstance : Setoid Value))
  (fun _ => True)

omit [DecidableEq Key] [Setoid Value] in
private theorem binding_at_owner {state : R} (allowed : MediatedRegistry.Allowed state)
    {owner address : Name} {key : Key} {value : Value} (declared : ProvidesAt state owner key)
    (binding : tableAt state address key = some value) : address = owner := by
  obtain ⟨provider, present, provides⟩ := declared
  cases entry : state address with
  | none => simp [tableAt, entry] at binding
  | some row =>
    have bound : row.table key = some value := by simpa only [tableAt, entry, Option.bind_some] using binding
    have occupied : row.table key ≠ none := by rw [bound]; exact Option.some_ne_none value
    by_cases same : address = owner
    · exact same
    · exact False.elim (allowed.2.2.2 _ _ row provider entry present same key
        ⟨allowed.2.2.1 address row key entry occupied, provides⟩)

omit [DecidableEq Key] in
private theorem observed_slot {left right : R} (observed : Observed left right)
    (allowedLeft : MediatedRegistry.Allowed left) (allowedRight : MediatedRegistry.Allowed right)
    {owner : Name} {key : Key} (leftProvider : ProvidesAt left owner key) (rightProvider : ProvidesAt right owner key) :
    OptionRel (· ≈ ·) (tableAt left owner key) (tableAt right owner key) := by
  obtain ⟨forward, backward⟩ := observed key trivial
  cases l : tableAt left owner key with
  | none =>
    cases r : tableAt right owner key with
    | none => trivial
    | some b =>
      obtain ⟨name, value, found, _⟩ := backward owner b r
      have same := binding_at_owner allowedLeft leftProvider found
      subst name
      rw [l] at found
      cases found
  | some a =>
    obtain ⟨name, value, found, related⟩ := forward owner a l
    have same := binding_at_owner allowedRight rightProvider found
    subst name
    rw [found]
    exact related

private theorem observed_after_slot {left right leftAfter rightAfter : R} (observed : Observed left right)
    (allowedLeft : MediatedRegistry.Allowed leftAfter) (allowedRight : MediatedRegistry.Allowed rightAfter)
    {owner : Name} {key : Key} (leftProvider : ProvidesAt leftAfter owner key) (rightProvider : ProvidesAt rightAfter owner key)
    (leftFrame : ∀ name other, other ≠ key → tableAt leftAfter name other = tableAt left name other)
    (rightFrame : ∀ name other, other ≠ key → tableAt rightAfter name other = tableAt right name other)
    (slot : OptionRel (· ≈ ·) (tableAt leftAfter owner key) (tableAt rightAfter owner key)) :
    Observed leftAfter rightAfter := by
  intro other _
  by_cases same : other = key
  · subst other
    constructor
    · intro name value bound
      cases binding_at_owner allowedLeft leftProvider bound
      rw [bound] at slot
      cases first : tableAt rightAfter owner key with
      | none => simp [first, OptionRel] at slot
      | some other => exact ⟨owner, other, first, by simpa only [first, OptionRel] using slot⟩
    · intro name value bound
      cases binding_at_owner allowedRight rightProvider bound
      rw [bound] at slot
      cases first : tableAt leftAfter owner key with
      | none => simp [first, OptionRel] at slot
      | some other => exact ⟨owner, other, first, by simpa only [first, OptionRel] using slot⟩
  · simpa only [leftFrame _ _ same, rightFrame _ _ same] using observed other trivial

/-- Matching inverse representatives must also agree as partial functions.
For the typed encoding this follows from its domain probes. -/
def DecodeRespects (meaning : Coeffects program) : Prop :=
  ∀ key {f g : Value → Value}, Effects.Related f g →
    MapRelated (fun a b : Value => a ≈ b) (meaning.denote key f) (meaning.denote key g)

private theorem capture_respects (meaning : Coeffects program) (decodes : DecodeRespects meaning)
    (leftLive rightLive : Name → Option Nat) (left right : R) (first second : C)
    (allowedLeft : MediatedRegistry.Allowed left) (allowedRight : MediatedRegistry.Allowed right)
    (leftScope : CaptureScope left first) (rightScope : CaptureScope right second)
    (tokens : StageSimulation.InverseRelated first.token second.token) (observed : Observed left right) :
    OptionRel Observed (runCapture meaning leftLive first left) (runCapture meaning rightLive second right) := by
  rcases first with ⟨first, index⟩
  rcases second with ⟨second, nextIndex⟩
  change StageSimulation.InverseRelated first second at tokens
  cases tokens with
  | unit => exact observed
  | retire child =>
    have same (state : R) (live : Name → Option Nat) (stamp : Nat) (owner : Name) (key : Key) :
        tableAt ((Capture.mk (.retire child) stamp).apply live state) owner key = tableAt state owner key := by
      by_cases active : live child = some stamp <;> simp [Capture.apply, active, tableAt_retire]
    change Observed ((Capture.mk (.retire child) index).apply leftLive left)
      ((Capture.mk (.retire child) nextIndex).apply rightLive right)
    simpa only [PaperStateObservation.TablesRelatedAt, same] using observed
  | restrict owner key =>
    have slots := observed_slot observed allowedLeft allowedRight leftScope rightScope
    cases l : tableAt left owner key <;> cases r : tableAt right owner key <;> simp only [l, r, OptionRel] at slots
    · simp [runCapture, l, r, OptionRel]
    · simp only [runCapture, l, r, Option.map_some, OptionRel]
      change Observed (undo (.restrict owner key) left) (undo (.restrict owner key) right)
      refine observed_after_slot observed (MediatedRegistry.inverse_allowed (.restrict owner key) allowedLeft)
        (MediatedRegistry.inverse_allowed (.restrict owner key) allowedRight)
        (provides_after_capture leftLive ⟨.restrict owner key, index⟩ leftScope)
        (provides_after_capture rightLive ⟨.restrict owner key, nextIndex⟩ rightScope) ?_ ?_ ?_
      · intro name other different; simp [tableAt_restrict, different]
      · intro name other different; simp [tableAt_restrict, different]
      · simp [tableAt_restrict, OptionRel]
  | operate owner key functions =>
    rename_i f g
    have slots := observed_slot observed allowedLeft allowedRight leftScope rightScope
    cases l : tableAt left owner key <;> cases r : tableAt right owner key <;> simp only [l, r, OptionRel] at slots
    · simp [runCapture, l, r, OptionRel]
    · rename_i a b
      have outputs := decodes key functions a b slots
      cases applied : meaning.denote key f a <;> cases paired : meaning.denote key g b <;>
        simp only [applied, paired, OptionRel] at outputs
      · simp [runCapture, l, r, applied, paired, OptionRel]
      · simp only [runCapture, l, r, Option.bind_some, applied, paired, Option.map_some, OptionRel]
        change Observed (undo (.operate owner key f) left) (undo (.operate owner key g) right)
        refine observed_after_slot observed (MediatedRegistry.inverse_allowed (.operate owner key f) allowedLeft)
          (MediatedRegistry.inverse_allowed (.operate owner key g) allowedRight)
          (provides_after_capture leftLive ⟨.operate owner key f, index⟩ leftScope)
          (provides_after_capture rightLive ⟨.operate owner key g, nextIndex⟩ rightScope) ?_ ?_ ?_
        · intro name other different; simp [tableAt_operate, different]
        · intro name other different; simp [tableAt_operate, different]
        · simpa only [tableAt_operate, and_self, if_pos rfl, l, r, Option.map_some, OptionRel,
            meaning.agrees key f a _ applied, meaning.agrees key g b _ paired] using outputs

/-- The paired frozen accumulator maps agree on every pair of compatible
probes. The composition returns failure as soon as any saved member fails. -/
theorem run_respects (meaning : Coeffects program) (decodes : DecodeRespects meaning)
    (leftLive rightLive : Name → Option Nat) {leftWord rightWord : List C}
    (tokens : StageSimulation.StackRelated (leftWord.map Capture.token) (rightWord.map Capture.token))
    {left right : R} (leftScope : Scope leftWord left) (rightScope : Scope rightWord right)
    (observed : Observed left right) :
    OptionRel Observed (run meaning leftLive leftWord left) (run meaning rightLive rightWord right) := by
  induction leftWord generalizing rightWord left right with
  | nil =>
    cases rightWord with
    | nil => exact observed
    | cons => cases tokens
  | cons first rest ih =>
    cases rightWord with
    | nil => cases tokens
    | cons second tail =>
      cases tokens with
      | cons headPair tailPair =>
        have head := capture_respects meaning decodes leftLive rightLive left right first second leftScope.1 rightScope.1
          (leftScope.2 first List.mem_cons_self) (rightScope.2 second List.mem_cons_self) headPair observed
        change OptionRel Observed ((runCapture meaning leftLive first left).bind (run meaning leftLive rest))
          ((runCapture meaning rightLive second right).bind (run meaning rightLive tail))
        cases a : runCapture meaning leftLive first left <;> cases b : runCapture meaning rightLive second right <;>
          simp only [a, b, Option.bind_none, Option.bind_some, OptionRel] at head ⊢
        obtain ⟨_, rfl⟩ := (capture_success_iff meaning leftLive first _ _).mp a
        obtain ⟨_, rfl⟩ := (capture_success_iff meaning rightLive second _ _).mp b
        exact ih tailPair (scope_tail leftLive first rest leftScope) (scope_tail rightLive second tail rightScope) head

omit [Setoid Value] in
theorem trace_word {last : Nat} (trace : GuardedHistory.Trace program last) (time : Nat) (bounded : time ≤ last)
    (meaning : Coeffects program) (actor : Name) :
    Scope ((trace.notes time).2 actor) (trace.state time) ∧
      run meaning (trace.notes time).1 ((trace.notes time).2 actor) (trace.state time) =
        some (replay (trace.notes time).1 ((trace.notes time).2 actor) (trace.state time)) := by
  have defined := saved_word_defined trace time bounded meaning actor
  exact ⟨scope_of_defined meaning _ _ (trace_allowed trace time bounded) defined,
    (success_iff meaning _ _ _ _).mpr ⟨defined, rfl⟩⟩

/-- Agreement of the frozen accumulator with the structural comparison.
The semantic comparison supplies joint definedness. Once defined, replay
also compares the unaffected control fields and the guarded retirements. -/
theorem run_respects_states (meaning : Coeffects program) (decodes : DecodeRespects meaning)
    {first second : Vestigial.CutNotes Name Key Value} (notes : EpisodeAnnotations.NotesRelated first second)
    (actor : Name) {left right : R} (states : StageSimulation.Related Eq left right)
    (leftScope : Scope (first.2 actor) left) (rightScope : Scope (second.2 actor) right) :
    OptionRel (StageSimulation.Related Eq) (run meaning first.1 (first.2 actor) left)
      (run meaning second.1 (second.2 actor) right) := by
  have comparison := run_respects meaning decodes first.1 second.1 (notes.words actor)
    leftScope rightScope (PaperStateObservation.tables_of_homogeneous (states.tables.projected (fun _ => True)) (fun _ _ _ eq => eq))
  cases firstRun : run meaning first.1 (first.2 actor) left <;>
    cases secondRun : run meaning second.1 (second.2 actor) right <;>
    simp only [firstRun, secondRun, OptionRel] at comparison ⊢
  obtain ⟨_, rfl⟩ := (success_iff meaning _ _ _ _).mp firstRun
  obtain ⟨_, rfl⟩ := (success_iff meaning _ _ _ _).mp secondRun
  exact EpisodeAnnotations.replay_related_of_notes states notes actor

end Comparison

section Typed
open TypedRegistry (Instruction Scalar)
open PaperEffectEquations (CoeffectOperations ValueOperationWitness)
open PartialCoeffectIndependenceContracts (tableSetoid)
variable {V : Key → Type u} (ops : CoeffectOperations V) (observe : ∀ key, Setoid (V key))

theorem typed_decode_respects (prog : Code → Instruction Name ops Code) (recovery : ValueOperationWitness ops)
    (laws : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key) :
    letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
    DecodeRespects (TypedReplayContracts.coeffects ops observe prog recovery laws) := by
  letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
  intro key f g related
  exact TypedCoeffectReplay.decodeInverse_related observe key (fun _ _ inputs => related inputs)

end Typed

end Cordis.Repairs.ScopedReplayComparison
