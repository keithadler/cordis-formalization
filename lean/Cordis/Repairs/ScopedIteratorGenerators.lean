import Cordis.Repairs.ScopedIteratorObservation
import Cordis.Repairs.PairwiseNativeWords

/-! Native provenance for the forward and saved generators of scoped
iterators. A saved generator carries the output scope of its actual yield.
Its guarded application retains partiality and checks the captured birth. -/
namespace Cordis.Repairs.ScopedIteratorGenerators
open TypedRegistry
open ScopedIteratorObservation
open PairwiseNativeWords
open PairwiseSlots (tablesOf tablesOf_retire)
open PairwiseMixed (runMixed controlPart StampedRelated)
open PaperEffectEquations (CoeffectOperations)
open PartialCoeffectIndependenceContracts (tableSetoid)
open Iterators (OptionRel)

universe u
variable {Name Key Code : Type u} {V : Key → Type u}
variable [DecidableEq Name] [DecidableEq Key] {ops : CoeffectOperations V}
variable {program : Code → Instruction Name ops Code} {actor : Name}
variable {observe : ∀ key, Setoid (V key)} {keys : Key → Prop}
local notation "R" => Registry Name V Code
local notation "SR" => PairwiseControl.Stamped Name V Code
local notation "N" => Node program actor observe keys
local notation "Y" => Yield program actor observe keys

/-- The guard can change the control effect of a saved retirement. The
ordinary inverse is exactly the captured native token on its domain. -/
private def guardedResult (saved : Saved program actor) (probe : SR) : SR :=
  match saved.token with
  | .retire child => PairwiseControl.savedRetire probe child saved.stamp
  | token => (undo token probe.1, probe.2)

private theorem guardedResult_native (saved : Saved program actor) (probe : SR)
    (defined : InverseDefined probe.1 saved.token) : saved.native probe (guardedResult saved probe) := by
  cases token : saved.token with
  | unit | restrict | operate =>
    exact ⟨defined, by simp [guardedResult, token], by
      simp [guardedResult, token, IncarnationReplay.Capture.apply, encode_undo, encodeInverse]⟩
  | retire child =>
    by_cases sameBirth : probe.2 child = some saved.stamp <;>
      exact ⟨defined, by simp [guardedResult, token, PairwiseControl.savedRetire, sameBirth], by
        simp [guardedResult, token, PairwiseControl.savedRetire, sameBirth, encodeInverse,
          IncarnationReplay.Capture.apply]⟩

private theorem guardedResult_tables (saved : Saved program actor) (probe : SR) :
    tablesOf (guardedResult saved probe).1 = tablesOf (undo saved.token probe.1) := by
  cases token : saved.token with
  | unit | restrict | operate => simp [guardedResult, token]
  | retire child =>
    by_cases sameBirth : probe.2 child = some saved.stamp <;>
      simp [guardedResult, token, PairwiseControl.savedRetire, sameBirth, undo, tablesOf_retire]

/-- For a saved generator, the native replay and the scoped inverse have
exactly the same domain on admitted probes. Their table results agree,
including when the retirement finds a different child incarnation. -/
theorem saved_application (saved : Saved program actor) (result : Y)
    (agrees : ScopedEffects.InverseAgrees result.inverse saved.token)
    (probe : ScopedEffects.State result.domain) (live : Name → Option Nat) :
    (runMixed saved.word (probe.val, live)).map (fun after => tablesOf after.1) =
      (result.inverse probe).map (fun after => tablesOf after.val) := by
  cases returned : result.inverse probe with
  | none =>
    cases replayed : runMixed saved.word (probe.val, live) with
    | none => rfl
    | some after =>
      obtain ⟨_, impossible⟩ := (agrees.defined probe).mpr (saved.reify replayed).1
      rw [returned] at impossible
      cases impossible
  | some restored =>
    have defined := (agrees.defined probe).mp ⟨restored, returned⟩
    have applied := saved.record (guardedResult_native saved (probe.val, live) defined)
    rw [applied]
    simp only [Option.map_some, agrees.value probe restored returned]
    exact congrArg some (guardedResult_tables saved (probe.val, live))

omit [DecidableEq Name] in
private theorem capture_defined {first second : Inverse Name V} {left right : R}
    (captures : PairwiseForward.CaptureRelated observe first second)
    (related : PairwisePrograms.Related (ops := ops) observe left right) :
    InverseDefined left first ↔ InverseDefined right second := by
  cases captures with
  | unit | retire => exact Iff.rfl
  | restrict owner key =>
    have values := PairwiseRegistry.slot_related observe related owner key
    cases a : tableAt left owner key <;> cases b : tableAt right owner key <;>
      simp_all [OptionRel, InverseDefined]
  | @operate owner key before after paired =>
    have values := PairwiseRegistry.slot_related observe related owner key
    cases a : tableAt left owner key with
    | none => cases b : tableAt right owner key <;> simp_all [OptionRel, InverseDefined]
    | some input =>
      cases b : tableAt right owner key with
      | none => simp_all [OptionRel]
      | some other =>
        have same : (observe key).r input other := by simpa only [a, b, OptionRel] using values
        have applied := paired input other same
        cases firstCall : before input <;> cases secondCall : after other <;>
          simp_all [OptionRel, InverseDefined]

private theorem compare_inverse_graphs {left right : Y} {first second : Inverse Name V}
    {selected : Key → Prop}
    (leftAgrees : ScopedEffects.InverseAgrees left.inverse first)
    (rightAgrees : ScopedEffects.InverseAgrees right.inverse second)
    (a : ScopedEffects.State left.domain) (b : ScopedEffects.State right.domain)
    (defined : InverseDefined a.val first ↔ InverseDefined b.val second)
    (observed : InverseDefined a.val first → InverseDefined b.val second →
      TypedStateObservation.TablesRelatedAt observe selected (undo first a.val) (undo second b.val)) :
    OptionRel (ScopedEffects.Observed observe selected) (left.inverse a) (right.inverse b) := by
  have domain := (leftAgrees.defined a).trans (defined.trans (rightAgrees.defined b).symm)
  cases ran : left.inverse a <;> cases other : right.inverse b
  · exact True.intro
  · obtain ⟨_, impossible⟩ := domain.mpr ⟨_, other⟩
    rw [ran] at impossible
    cases impossible
  · obtain ⟨_, impossible⟩ := domain.mp ⟨_, ran⟩
    rw [other] at impossible
    cases impossible
  · rename_i restored alternate
    change TypedStateObservation.TablesRelatedAt observe selected restored.val alternate.val
    rw [leftAgrees.value a restored ran, rightAgrees.value b alternate other]
    exact observed ((leftAgrees.defined a).mp ⟨restored, ran⟩) ((rightAgrees.defined b).mp ⟨alternate, other⟩)

/-- Related native captures compare the entire returned scoped inverse
functions on their respective structurally related probes. -/
theorem inverse_observation {left right : Y} {first second : Inverse Name V}
    (leftAgrees : ScopedEffects.InverseAgrees left.inverse first)
    (rightAgrees : ScopedEffects.InverseAgrees right.inverse second)
    (captures : PairwiseForward.CaptureRelated observe first second)
    (a : ScopedEffects.State left.domain) (b : ScopedEffects.State right.domain)
    (related : PairwisePrograms.Related (ops := ops) observe a.val b.val) :
    OptionRel (ScopedEffects.Observed observe keys) (left.inverse a) (right.inverse b) := by
    apply compare_inverse_graphs leftAgrees rightAgrees a b (capture_defined captures related)
    intro _ _
    letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
    have encoded : StageSimulation.InverseRelated (encodeInverse ops first) (encodeInverse ops second) := by
      cases captures with
      | unit => exact .unit
      | restrict owner key => exact .restrict owner key
      | retire child => exact .retire child
      | operate owner key maps =>
        exact .operate owner key (fun _ _ values => TypedCoeffectReplay.encodeMap_related observe key maps _ _ values)
    have undone := StageSimulation.undo_related related encoded
    apply (TypedStateObservation.tables_related_encode_iff ops observe keys _ _).mp
    rw [encode_undo, encode_undo]
    exact PaperStateObservation.tables_of_homogeneous (undone.tables.projected keys) (fun _ _ _ same => same)

/-- Compare actual saved inverses on arbitrary table-related probes from
the head's output domain. Only the captured owner and key are fixed by
the scope; unrelated rows and control fields may differ. -/
theorem inverse_observation_on_tables {left right : Y} {first second : Inverse Name V} {projection : Key → Prop}
    (leftAgrees : ScopedEffects.InverseAgrees left.inverse first)
    (rightAgrees : ScopedEffects.InverseAgrees right.inverse second)
    (captures : PairwiseForward.CaptureRelated observe first second)
    (sameScope : left.domain = right.domain) (slotScope : ScopedEffects.InverseScope ops projection first left.domain)
    (a : ScopedEffects.State left.domain) (b : ScopedEffects.State right.domain)
    (related : ScopedEffects.Observed observe projection a b) :
    OptionRel (ScopedEffects.Observed observe projection) (left.inverse a) (right.inverse b) := by
  have bScope : left.domain b.val := by rw [sameScope]; exact b.property
  apply compare_inverse_graphs leftAgrees rightAgrees a b
  · cases captures with
    | unit | retire => exact Iff.rfl
    | restrict owner key =>
      obtain ⟨selected, provider, declared, contains⟩ := slotScope
      have slots := CompatibleProvision.observed_slot observe projection key selected declared
        (left := ⟨a.val, contains _ a.property⟩) (right := ⟨b.val, contains _ bScope⟩) related
      cases leftSlot : tableAt a.val owner key <;> cases rightSlot : tableAt b.val owner key <;>
        simp_all [OptionRel, InverseDefined]
    | @operate owner key firstMap secondMap maps =>
      obtain ⟨selected, provider, declared, contains⟩ := slotScope
      have slots := CompatibleProvision.observed_slot observe projection key selected declared
        (left := ⟨a.val, contains _ a.property⟩) (right := ⟨b.val, contains _ bScope⟩) related
      cases leftSlot : tableAt a.val owner key <;> cases rightSlot : tableAt b.val owner key <;>
        simp only [leftSlot, rightSlot, OptionRel] at slots
      · simp [InverseDefined, leftSlot, rightSlot]
      · rename_i firstValue secondValue
        have results := maps firstValue secondValue slots
        cases firstCall : firstMap firstValue <;> cases secondCall : secondMap secondValue <;>
          simp_all [OptionRel, InverseDefined]
  · intro leftDefined rightDefined
    cases captures with
    | unit => exact related
    | retire child =>
      apply AllocationDomains.tables_transfer observe projection _ _ related
      · intro owner key
        exact congrFun (tablesOf_retire a.val child) (owner, key)
      · intro owner key
        exact congrFun (tablesOf_retire b.val child) (owner, key)
    | restrict owner key =>
      obtain ⟨_, provider, declared, contains⟩ := slotScope
      exact CompatibleProvision.setSlot_related observe projection key declared
        (left := ⟨a.val, contains _ a.property⟩) (right := ⟨b.val, contains _ bScope⟩) related
        (a := none) (b := none) trivial
    | @operate owner key firstMap secondMap maps =>
      obtain ⟨selected, provider, declared, contains⟩ := slotScope
      let firstProbe : CompatibleProvision.Gamma ops owner provider := ⟨a.val, contains _ a.property⟩
      let secondProbe : CompatibleProvision.Gamma ops owner provider := ⟨b.val, contains _ bScope⟩
      have slots := CompatibleProvision.observed_slot observe projection key selected declared
        (left := firstProbe) (right := secondProbe) related
      obtain ⟨firstInput, firstOutput, firstBound, firstCall⟩ := leftDefined
      obtain ⟨secondInput, secondOutput, secondBound, secondCall⟩ := rightDefined
      change OptionRel (observe key).r (tableAt a.val owner key) (tableAt b.val owner key) at slots
      rw [firstBound, secondBound] at slots
      have changed := maps firstInput secondInput slots
      rw [firstCall, secondCall] at changed
      rw [PairwiseOperations.undo_operate_eq_write firstBound firstCall,
        PairwiseOperations.undo_operate_eq_write secondBound secondCall]
      exact CompatibleProvision.setSlot_related observe projection key declared
        (left := firstProbe) (right := secondProbe) related changed

/-- Each successful scoped head supplies its exact native advance and the
saved generator produced by that advance. Both use the same chosen birth
stamp. The saved generator reflects all probes of this yield's own scope. -/
theorem record_head (node : N) (input : ScopedEffects.State node.domain) (result : Y)
    (called : node.evaluate input = some result) (live : Name → Option Nat) (stamp : Nat) :
    ∃ (head : Forward program actor node.code) (saved : Saved program actor),
      saved.origin = input.val ∧ saved.output = result.output.val ∧ saved.code = node.code ∧
      saved.next = result.next.map Node.code ∧ saved.stamp = stamp ∧
      (Letter.advance node.code head).Native (input.val, live)
        (result.output.val, head.stamps live) (.advance saved.token saved.next result.reply) ∧
      ScopedEffects.InverseAgrees result.inverse saved.token ∧ head.draw = node.draw := by
  obtain ⟨token, landed, agrees, chosen, actualReply⟩ := node.evaluate_native input result called
  obtain ⟨head, ready, draw, _⟩ := Forward.record (before := (input.val, live)) landed stamp
  have sameDraw := draw.symm.trans chosen
  exact ⟨head, ⟨input.val, result.output.val, node.code, token, result.next.map Node.code, stamp, landed⟩,
    rfl, rfl, rfl, rfl, rfl, ⟨landed, draw, rfl, ready, by simpa only [sameDraw] using actualReply⟩,
    agrees, sameDraw⟩

/-- A fixed forward generator reflects to a scoped yield on each probe
admitted by the node and its provider route. The original draw, complete
output, selected code and entire returned partial inverse are retained. -/
theorem reify_head (node : N) (head : Forward program actor node.code)
    (drawn : head.draw = node.draw) (input : ScopedEffects.State node.domain)
    {live : Name → Option Nat} {after : SR} {token : Inverse Name V} {next : Option Code}
    {outcome : Outcome Name ops}
    (native : (Letter.advance node.code head).Native (input.val, live) after (.advance token next outcome)) :
    ∃ result, node.evaluate input = some result ∧ result.output.val = after.1 ∧
      result.next.map Node.code = next ∧ ScopedEffects.InverseAgrees result.inverse token ∧ result.reply = outcome := by
  obtain ⟨landed, selected, _, _, exactReply⟩ := native
  obtain ⟨result, called⟩ := node.evaluate_of_native input landed (selected.trans drawn)
  obtain ⟨actual, executed, agrees, actualDraw, replied⟩ := node.evaluate_native input result called
  obtain ⟨output, rfl, branch⟩ := typed_landing_deterministic executed landed
    (actualDraw.trans (selected.trans drawn).symm)
  rw [drawn] at exactReply
  exact ⟨result, called, output, branch, agrees, Option.some.inj (replied.symm.trans exactReply)⟩

/-- Reify the two yields of a moved native head. The equal outcomes
select the same scoped continuation. Each closure realizes its own
actual native capture on its admitted probes. -/
theorem reify_paired_heads (node : N) (head : Forward program actor node.code)
    (drawn : head.draw = node.draw) (first second : ScopedEffects.State node.domain)
    {live otherLive : Name → Option Nat} {after otherAfter : SR}
    {token otherToken : Inverse Name V} {next otherNext : Option Code}
    {outcome otherOutcome : Outcome Name ops}
    (left : (Letter.advance node.code head).Native (first.val, live) after (.advance token next outcome))
    (right : (Letter.advance node.code head).Native (second.val, otherLive) otherAfter
      (.advance otherToken otherNext otherOutcome))
    (paired : Reply.Related observe (.advance token next outcome) (.advance otherToken otherNext otherOutcome)) :
    ∃ a b, node.evaluate first = some a ∧ node.evaluate second = some b ∧
      a.output.val = after.1 ∧ b.output.val = otherAfter.1 ∧ a.reply = outcome ∧ a.reply = b.reply ∧
      a.next = b.next ∧ ScopedEffects.InverseAgrees a.inverse token ∧ ScopedEffects.InverseAgrees b.inverse otherToken := by
  obtain ⟨a, called, output, _, inverse, replied⟩ := reify_head node head drawn first left
  obtain ⟨b, otherCalled, otherOutput, _, otherInverse, otherReplied⟩ := reify_head node head drawn second right
  have sameReply := replied.trans (paired.2.2.trans otherReplied.symm)
  exact ⟨a, b, called, otherCalled, output, otherOutput, replied, sameReply,
    node.next_eq_of_reply first second a b called otherCalled sameReply, inverse, otherInverse⟩

/-- The allocation clause of the paired yield also identifies the
immutable child component in both actual outputs. -/
theorem paired_child_payload (node : N) (head : Forward program actor node.code)
    {before foreignBefore after otherAfter : SR} {token otherToken : Inverse Name V} {next otherNext : Option Code}
    {child : Name} {otherOutcome : Outcome Name ops}
    (left : (Letter.advance node.code head).Native before after (.advance token next (.child child)))
    (right : (Letter.advance node.code head).Native foreignBefore otherAfter
      (.advance otherToken otherNext otherOutcome))
    (paired : Reply.Related observe (.advance token next (.child child)) (.advance otherToken otherNext otherOutcome)) :
    ∃ component, (program node.code).action = .instantiate component ∧
      after.1 child = some (fresh component (some actor)) ∧
      otherAfter.1 child = some (fresh component (some actor)) := by
  have same := paired.2.2
  subst otherOutcome
  obtain ⟨component, action, born⟩ := Letter.child_payload head left
  obtain ⟨otherComponent, otherAction, otherBorn⟩ := Letter.child_payload head right
  cases Action.instantiate.inj (action.symm.trans otherAction)
  exact ⟨component, action, born, otherBorn⟩

/-- On a common admissible probe, the recorded forward and scoped head
either both fail or produce exactly the same updated registry. -/
theorem forward_application (node : N) (head : Forward program actor node.code)
    (drawn : head.draw = node.draw) (input : ScopedEffects.State node.domain)
    (ready : head.ready input.val) (live : Name → Option Nat) :
    runMixed head.word (input.val, live) =
      (node.evaluate input).map (fun result => (result.output.val, head.stamps live)) := by
  cases called : node.evaluate input with
  | none =>
    cases executed : runMixed head.word (input.val, live) with
    | none => rfl
    | some after =>
      have run : runMixed (Letter.advance node.code head).word (input.val, live) = some after := executed
      obtain ⟨reply, native⟩ := (Letter.advance node.code head).reify
        (before := (input.val, live)) ready run
      cases reply with
      | replay => exact False.elim native
      | advance token next outcome =>
        obtain ⟨_, impossible, _⟩ := reify_head node head drawn input native
        rw [called] at impossible
        cases impossible
  | some result =>
    obtain ⟨token, landed, _, chosen, _⟩ := node.evaluate_native input result called
    exact head.run_of_landing landed ready (chosen.trans drawn.symm) rfl

/-- The recorded representatives of the two generator rules in Definition
42. The replay rule remembers the actual yield and its inverse scope. -/
inductive Generator (root : N) : Letter program actor → Type (u + 1) where
  | advance (node : N) (reached : Reach root node) (head : Forward program actor node.code)
      (drawn : head.draw = node.draw) : Generator root (.advance node.code head)
  | replay (node : N) (reached : Reach root node) (input : ScopedEffects.State node.domain)
      (result : Y) (called : node.evaluate input = some result) (saved : Saved program actor)
      (origin : saved.origin = input.val) (output : saved.output = result.output.val)
      (code : saved.code = node.code) (next : saved.next = result.next.map Node.code)
      (agrees : ScopedEffects.InverseAgrees result.inverse saved.token)
      (drawn : capturedChild saved.token = node.draw) : Generator root (.replay saved)

def Generator.scope {root : N} {letter : Letter program actor} (generator : Generator root letter) : R → Prop :=
  match generator with
  | .advance node .. => node.domain
  | .replay _ _ _ result .. => result.domain

/-- Record both generators of a reachable successful yield. Any selected
continuation is reachable using exactly this observation. -/
theorem generated_head {root node : N} (reached : Reach root node)
    (input : ScopedEffects.State node.domain) (result : Y)
    (called : node.evaluate input = some result) (live : Name → Option Nat) (stamp : Nat) :
    ∃ (head : Forward program actor node.code) (saved : Saved program actor),
      Nonempty (Generator root (.advance node.code head)) ∧ Nonempty (Generator root (.replay saved)) ∧
      saved.stamp = stamp ∧ (Letter.advance node.code head).Native (input.val, live)
        (result.output.val, head.stamps live) (.advance saved.token saved.next result.reply) ∧
      ∀ following, result.next = some following → Reach root following := by
  obtain ⟨head, saved, origin, output, code, next, age, native, agrees, draw⟩ :=
    record_head node input result called live stamp
  exact ⟨head, saved, ⟨.advance node reached head draw⟩, ⟨.replay node reached input result called saved
    origin output code next agrees (native.2.1.trans draw)⟩, age, native,
    fun _ selected => .next reached input result called selected⟩

/-- Reflect an already recorded source landing into a generator without
recapturing it at the replay probe. This keeps the stamp attached to the
actual event in the guarded history. -/
theorem replay_of_landing {root node : N} (reached : Reach root node) (saved : Saved program actor)
    (admitted : node.domain saved.origin) (code : saved.code = node.code)
    (drawn : capturedChild saved.token = node.draw) :
    Nonempty (Generator root (.replay saved)) := by
  let input : ScopedEffects.State node.domain := ⟨saved.origin, admitted⟩
  have landed := saved.landed
  rw [code] at landed
  obtain ⟨result, called⟩ := node.evaluate_of_native input landed drawn
  obtain ⟨token, evaluated, agrees, selected, _⟩ := node.evaluate_native input result called
  obtain ⟨output, tokenEq, next⟩ := typed_landing_deterministic evaluated landed (selected.trans drawn.symm)
  exact ⟨.replay node reached input result called saved rfl output.symm code next.symm (tokenEq ▸ agrees) drawn⟩

/-- Read the observable table map directly from the generator's scoped
closure. The two clauses use respectively a forward head and its saved
output-domain inverse. -/
def Generator.tables {root : N} {letter : Letter program actor} (generator : Generator root letter) :
    ScopedEffects.State generator.scope → Option (PairwiseSlots.Tables Name V) :=
  match generator with
  | .advance node .. => fun input => (node.evaluate input).map (fun result => tablesOf result.output.val)
  | .replay _ _ _ result .. => fun input => (result.inverse input).map (fun restored => tablesOf restored.val)

/-- Running a recorded generator at a compatible cut has precisely the
definedness and table observation of the scoped forward or inverse map. -/
theorem Generator.application {root : N} {letter : Letter program actor} (generator : Generator root letter)
    (input : ScopedEffects.State generator.scope) (ready : letter.ready input.val) (live : Name → Option Nat) :
    (runMixed letter.word (input.val, live)).map (fun after => tablesOf after.1) = generator.tables input := by
  cases generator with
  | advance node reached head drawn =>
    change (runMixed head.word (input.val, live)).map _ = _
    rw [forward_application node head drawn input ready live, Option.map_map]
    rfl
  | replay node reached origin result called saved originEq output code next agrees drawn =>
    exact saved_application saved result agrees input live

/-- Any native application of a recorded generator reflects a successful
call to that generator on its admitted source scope. -/
theorem Generator.tables_of_native {root : N} {letter : Letter program actor} (generator : Generator root letter)
    {before after : SR} {reply : Reply Name ops Code} (admitted : generator.scope before.1)
    (native : letter.Native before after reply) :
    generator.tables ⟨before.1, admitted⟩ = some (tablesOf after.1) := by
  rw [← generator.application ⟨before.1, admitted⟩ (letter.ready_of_native native) before.2]
  have record := letter.record_native native
  simpa using congrArg (Option.map fun state : SR => tablesOf state.1) record

/-- Finite compositions of the two generator rules. Letters remember the
discrete realization choices, with scope evidence supplied at each cut. -/
inductive Word (root : N) : List (Letter program actor) → Type (u + 1) where
  | nil : Word root []
  | cons {letter script} (head : Generator root letter) (tail : Word root script) :
    Word root (letter :: script)

def Word.Admitted {root : N} : {script : List (Letter program actor)} → Word root script → SR → Prop
  | [], .nil, _ => True
  | letter :: _, .cons head tail, before => head.scope before.1 ∧ letter.ready before.1 ∧
    ∀ middle, runMixed letter.word before = some middle → tail.Admitted middle

noncomputable def Word.run {root : N} {script : List (Letter program actor)} (word : Word root script)
    (before : SR) : Option SR := by
  classical
  exact if word.Admitted before then runMixed (words script) before else none

theorem Word.run_eq {root : N} {script : List (Letter program actor)} (word : Word root script)
    {before : SR} (admitted : word.Admitted before) : word.run before = runMixed (words script) before := by
  simp [Word.run, admitted]

private theorem Word.native {root : N} {script : List (Letter program actor)} (word : Word root script)
    {before after : SR} (admitted : word.Admitted before) (executed : runMixed (words script) before = some after) :
    ∃ replies, NativePath program actor script before after replies := by
  induction word generalizing before after with
  | nil =>
    change some before = some after at executed
    cases Option.some.inj executed
    exact ⟨[], .nil before⟩
  | @cons letter script head tail ih =>
    obtain ⟨_, ready, restAdmitted⟩ := admitted
    change runMixed (letter.word ++ words script) before = some after at executed
    rw [split_word] at executed
    obtain ⟨middle, first, later⟩ := Option.bind_eq_some_iff.mp executed
    obtain ⟨reply, native⟩ := letter.reify ready first
    obtain ⟨replies, remaining⟩ := ih (restAdmitted middle first) later
    exact ⟨reply :: replies, .cons native remaining⟩

theorem Word.run_iff {root : N} {script : List (Letter program actor)} (word : Word root script)
    {before after : SR} :
    word.run before = some after ↔ word.Admitted before ∧
      ∃ replies, NativePath program actor script before after replies := by
  classical
  by_cases admitted : word.Admitted before
  · rw [word.run_eq admitted]
    exact ⟨fun executed => ⟨admitted, word.native admitted executed⟩,
      fun ⟨_, _, path⟩ => path.record⟩
  · simp [Word.run, admitted]

/-- Both orders of the actual scoped generated maps agree on definedness
and on the observed endpoint. The scopes are tested at every executable
prefix, including in each reordered word. -/
theorem Word.commute_on_scopes (observe : ∀ key, Setoid (V key))
    (laws : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    {leftActor rightActor : Name} {leftRow rightRow : Fiber Name V Code}
    {leftKeys rightKeys : Key → Prop}
    {leftRoot : Node program leftActor observe leftKeys} {rightRoot : Node program rightActor observe rightKeys}
    {leftScript : List (Letter program leftActor)} {rightScript : List (Letter program rightActor)}
    (leftWord : Word leftRoot leftScript) (rightWord : Word rightRoot rightScript)
    {before leftEnd rightEnd : SR}
    (different : leftActor ≠ rightActor) (separate : Transposition.Separated leftRow.component rightRow.component)
    (leftFound : before.1 leftActor = some leftRow) (rightFound : before.1 rightActor = some rightRow)
    (leftOrigins : ∀ letter ∈ leftScript, Letter.origin_has letter leftRow.component)
    (rightOrigins : ∀ letter ∈ rightScript, Letter.origin_has letter rightRow.component)
    (leftRun : leftWord.run before = some leftEnd) (rightRun : rightWord.run before = some rightEnd)
    (leftMoved : leftWord.Admitted rightEnd) (rightMoved : rightWord.Admitted leftEnd)
    (births : ∀ edit ∈ controlPart (words leftScript), ∀ other ∈ controlPart (words rightScript),
      PairwiseControl.Compatible edit other)
    (source : PairwisePrograms.Related (ops := ops) observe before.1 before.1) :
    Iterators.OptionRel (StampedRelated ops observe) (leftWord.run rightEnd) (rightWord.run leftEnd) := by
  obtain ⟨_, _, leftPath⟩ := leftWord.run_iff.mp leftRun
  obtain ⟨_, _, rightPath⟩ := rightWord.run_iff.mp rightRun
  have leftAllowed := script_admitted leftScript leftFound rfl (leftPath.ready leftFound) leftOrigins
  have rightAllowed := script_admitted rightScript rightFound rfl (rightPath.ready rightFound) rightOrigins
  have leftPresent : before.1 leftActor ≠ none := by rw [leftFound]; exact Option.noConfusion
  have rightPresent : before.1 rightActor ≠ none := by rw [rightFound]; exact Option.noConfusion
  have comparison := PairwiseMixed.recorded_mixed_words_commute ops observe laws different separate
    leftPresent rightPresent leftAllowed rightAllowed leftPath.record rightPath.record births source
  rw [split_word, split_word, leftPath.record, rightPath.record] at comparison
  rw [leftWord.run_eq leftMoved, rightWord.run_eq rightMoved]
  exact comparison

end Cordis.Repairs.ScopedIteratorGenerators
