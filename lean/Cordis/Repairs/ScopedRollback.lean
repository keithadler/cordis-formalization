import Cordis.Repairs.ScopedNameTransport
import Cordis.Repairs.IncarnationReplay

/-! Record a composed inverse for a scoped iterator. A successful branch
keeps the preceding inverse domains in its final probe domain. Tail cleanup
returns to those domains before applying the earlier saved inverses. -/
namespace Cordis.Repairs.ScopedRollback
open TypedRegistry ScopedEffects ScopedProgram
open PaperEffectEquations (CoeffectOperations)
open Iterators (OptionRel)
open PartialInverseObservation (MapRelated)
universe u
variable {Name Key Code : Type u} {V : Key → Type u}
variable [DecidableEq Name] [DecidableEq Key] {ops : CoeffectOperations V}
local notation "R" => Registry Name V Code
local notation "Dom" => R → Prop
variable {frame source target : Registry Name V Code → Prop}
variable {observe : ∀ key, Setoid (V key)} {keys : Key → Prop}
variable {program : Code → Instruction Name ops Code} {actor : Name} {code : Code}
local notation "Plan" => ScopedProgram.Iterator program actor observe keys

structure Result (frame : Dom) where
  domain : Dom
  output : State domain
  restore : State domain → Option (State frame)

def Result.ObservationallyRelated {other : Registry Name V Code → Prop}
    (observe : ∀ key, Setoid (V key)) (keys : Key → Prop) (left : Result frame) (right : Result other) : Prop :=
  Observed observe keys left.output right.output ∧
    ∀ first second, Observed observe keys first second →
      OptionRel (Observed observe keys) (left.restore first) (right.restore second)

def Result.Related (observe : ∀ key, Setoid (V key)) (keys : Key → Prop) (left right : Result frame) : Prop :=
  left.domain = right.domain ∧ left.ObservationallyRelated observe keys right

private theorem undoKeeps (stable : Stable ops frame) {before after : R}
    (native : ∃ token : Inverse Name V, after = undo token before) (inFrame : frame before) :
    frame after := by
  obtain ⟨token, rfl⟩ := native
  exact stable.undo token before inFrame

private def applySaved (stable : Stable ops frame) (saved : Saved target)
    (preserves : ∀ before after, saved before = some after → ∃ token : Inverse Name V, after.val = undo token before.val)
    (probe : State (fun state => frame state ∧ target state)) : Option (State frame) :=
  (saved ⟨probe.val, probe.property.2⟩).pmap (fun restored inFrame => ⟨restored.val, inFrame⟩)
    (fun restored applied => undoKeeps stable (preserves _ restored applied) probe.property.1)

private theorem applySaved_values (stable : Stable ops frame) (saved : Saved target)
    (preserves : ∀ before after, saved before = some after → ∃ token : Inverse Name V, after.val = undo token before.val)
    (probe : State (fun state => frame state ∧ target state)) :
    (applySaved stable saved preserves probe).map Subtype.val =
      (saved ⟨probe.val, probe.property.2⟩).map Subtype.val := by
  unfold applySaved
  rw [Option.map_pmap]
  exact Option.pmap_eq_map _ _ _ _

omit [DecidableEq Name] [DecidableEq Key] in
private theorem observed_values {first second : Registry Name V Code → Prop}
    (left : Option (State first)) (right : Option (State second)) :
    OptionRel (Observed observe keys) left right ↔
      OptionRel (TypedStateObservation.TablesRelatedAt observe keys)
        (left.map Subtype.val) (right.map Subtype.val) := by
  cases left <;> cases right <;> rfl

private theorem applySaved_respects (stable : Stable ops frame) {a b : Saved target}
    (keepA : ∀ first last, a first = some last → ∃ token : Inverse Name V, last.val = undo token first.val)
    (keepB : ∀ first last, b first = some last → ∃ token : Inverse Name V, last.val = undo token first.val)
    (related : MapRelated (Observed observe keys) a b)
    {left right : State (fun state => frame state ∧ target state)}
    (probes : Observed observe keys left right) :
    OptionRel (Observed observe keys) (applySaved stable a keepA left) (applySaved stable b keepB right) := by
  rw [observed_values, applySaved_values, applySaved_values, ← observed_values]
  exact related _ _ probes

private theorem savedKeeps {O : Type u} (head : Head program actor observe keys code source target O)
    {input : State source} {output : State target} {saved : Saved target} {reply : O}
    (called : head.effect.run input = some (output, saved, reply)) :
    ∀ before after, saved before = some after → ∃ token : Inverse Name V, after.val = undo token before.val := by
  obtain ⟨token, _, native, _, _⟩ := head.realizes.sound _ _ _ _ called
  intro before after applied
  exact ⟨token, native.value before after applied⟩

private theorem outputKeeps {O : Type u} (head : Head program actor observe keys code source target O)
    {input : State source} {output : State target} {saved : Saved target} {reply : O}
    (called : head.effect.run input = some (output, saved, reply))
    (stable : Stable ops frame) (inside : frame input.val) : frame output.val := by
  obtain ⟨_, landed, _⟩ := head.realizes.sound _ _ _ _ called
  exact stable.land landed inside

private def finish (stable : Stable ops frame) (output : State target) (inFrame : frame output.val)
    (saved : Saved target) (preserves : ∀ before after, saved before = some after → ∃ token : Inverse Name V, after.val = undo token before.val) :
    Result frame where
  domain := fun state => frame state ∧ target state
  output := ⟨output.val, inFrame, output.property⟩
  restore := applySaved stable saved preserves

private def prepend (stable : Stable ops frame) (saved : Saved target)
    (preserves : ∀ before after, saved before = some after → ∃ token : Inverse Name V, after.val = undo token before.val)
    (rest : Result (fun state => frame state ∧ target state)) : Result frame where
  domain := rest.domain
  output := rest.output
  restore probe := (rest.restore probe).bind (applySaved stable saved preserves)

/-- The frame records preceding inverse domains. The actual selected reply
determines the final domain and the exact order of inverse calls. -/
def evaluate : {code : Code} → {source : Dom} → (it : Plan code source) →
    {frame : Dom} → Stable ops frame → (input : State source) → frame input.val → Option (Result frame)
  | code, _, .stage head _ tail link, _, stable, input, inFrame =>
    match called : head.effect.run input with
    | none => none
    | some (output, saved, reply) =>
      let kept := outputKeeps head called stable inFrame
      let preserves := savedKeeps head called
      match selected : (program code).next (head.reply reply) with
      | none => some (finish stable output kept saved preserves)
      | some next =>
        let nextFrame := Stable.and stable (head.outputStable reply next selected)
        (evaluate (tail reply next selected) nextFrame
          ⟨output.val, link input output saved reply next called selected⟩ ⟨kept, output.property⟩).map
          (prepend stable saved preserves)

theorem evaluate_output (it : Plan code source)
    (stable : Stable ops frame) (input : State source) (inFrame : frame input.val) :
    (evaluate it stable input inFrame).map (fun result => result.output.val) = it.execute input := by
  induction it generalizing frame with
  | stage head entry tail link ih =>
    simp only [evaluate, ScopedProgram.Iterator.execute]
    split
    next missed =>
      split
      · rfl
      next _ _ _ called =>
        rw [missed] at called
        cases called
    next output saved reply called =>
      split
      next terminal =>
        split
        next missed =>
          rw [missed] at called
          cases called
        next _ _ _ called' =>
          cases Option.some.inj (called.symm.trans called')
          split
          · rfl
          next _ continues =>
            rw [terminal] at continues
            cases continues
      next next selected =>
        split
        next missed =>
          rw [missed] at called
          cases called
        next _ _ _ called' =>
          cases Option.some.inj (called.symm.trans called')
          split
          next terminal =>
            rw [terminal] at selected
            cases selected
          next following picked =>
            have sameCode := Option.some.inj (selected.symm.trans picked)
            subst following
            rw [Option.map_map]
            exact ih reply next selected _ _ _

private theorem prepend_related (stable : Stable ops frame) {a b : Saved target}
    (keepA : ∀ first last, a first = some last → ∃ token : Inverse Name V, last.val = undo token first.val)
    (keepB : ∀ first last, b first = some last → ∃ token : Inverse Name V, last.val = undo token first.val)
    (saved : MapRelated (Observed observe keys) a b)
    {left right : Result (fun state => frame state ∧ target state)}
    (related : Result.Related observe keys left right) :
    Result.Related observe keys (prepend stable a keepA left) (prepend stable b keepB right) := by
  refine ⟨related.1, related.2.1, ?_⟩
  intro first second probes
  have tails := related.2.2 first second probes
  change OptionRel (Observed observe keys)
    ((left.restore first).bind (applySaved stable a keepA))
    ((right.restore second).bind (applySaved stable b keepB))
  cases appliedA : left.restore first <;> cases appliedB : right.restore second <;> simp_all [OptionRel]
  exact applySaved_respects stable keepA keepB saved tails

private theorem prepend_map_related (stable : Stable ops frame) {a b : Saved target}
    (keepA : ∀ first last, a first = some last → ∃ token : Inverse Name V, last.val = undo token first.val)
    (keepB : ∀ first last, b first = some last → ∃ token : Inverse Name V, last.val = undo token first.val)
    (saved : MapRelated (Observed observe keys) a b)
    {left right : Option (Result (fun state => frame state ∧ target state))}
    (related : OptionRel (Result.Related observe keys) left right) :
    OptionRel (Result.Related observe keys) (left.map (prepend stable a keepA)) (right.map (prepend stable b keepB)) := by
  cases left <;> cases right <;> simp_all [OptionRel]
  exact prepend_related stable keepA keepB saved related

/-- Related forward probes also yield observationally related whole saved
maps. Both inverse calls follow the same selected branch and compare at
every pair of related probes in their witnessed final domains. -/
theorem evaluate_respects (it : Plan code source) (stable : Stable ops frame)
    (left right : State source) (leftFrame : frame left.val) (rightFrame : frame right.val)
    (related : Observed observe keys left right) :
    OptionRel (Result.Related observe keys)
      (evaluate it stable left leftFrame) (evaluate it stable right rightFrame) := by
  induction it generalizing frame with
  | stage head entry tail link ih =>
    have compared := head.lawful.respect left right related
    simp only [evaluate]
    split
    next missed =>
      split
      · trivial
      next _ _ _ called =>
        rw [missed, called] at compared
        exact False.elim compared
    next outA savedA replyA calledA =>
      split
      next terminal =>
        split
        next missed =>
          rw [calledA, missed] at compared
          exact False.elim compared
        next outB savedB replyB calledB =>
          rw [calledA, calledB] at compared
          obtain ⟨outputs, inverses, replies⟩ := compared
          change replyA = replyB at replies
          subst replyB
          split
          · exact ⟨rfl, outputs, fun _ _ probes =>
              applySaved_respects stable (savedKeeps head calledA) (savedKeeps head calledB) inverses probes⟩
          next _ selected =>
            rw [terminal] at selected
            cases selected
      next next selected =>
        split
        next missed =>
          rw [calledA, missed] at compared
          exact False.elim compared
        next outB savedB replyB calledB =>
          rw [calledA, calledB] at compared
          obtain ⟨outputs, inverses, replies⟩ := compared
          change replyA = replyB at replies
          subst replyB
          split
          next terminal =>
            rw [terminal] at selected
            cases selected
          next next' selected' =>
            have same := Option.some.inj (selected.symm.trans selected')
            subst next'
            exact prepend_map_related stable _ _ inverses
              (ih replyA next selected _ _ _ _ _ outputs)

omit [DecidableEq Name] [DecidableEq Key] in
private theorem observed_trans {first second third : Registry Name V Code → Prop}
    {a : State first} {b : State second} {c : State third}
    (left : Observed observe keys a b) (right : Observed observe keys b c) :
    Observed observe keys a c := by
  intro key selected
  obtain ⟨forward, backward⟩ := left key selected
  obtain ⟨forward', backward'⟩ := right key selected
  constructor
  · intro owner value found
    obtain ⟨middle, before, bound, compared⟩ := forward owner value found
    obtain ⟨other, after, witness, compared'⟩ := forward' middle before bound
    exact ⟨other, after, witness, (observe key).trans compared compared'⟩
  · intro owner value found
    obtain ⟨middle, before, bound, compared'⟩ := backward' owner value found
    obtain ⟨other, after, witness, compared⟩ := backward middle before bound
    exact ⟨other, after, witness, (observe key).trans compared compared'⟩

private theorem applySaved_recovers {O : Type u} (head : Head program actor observe keys code source target O)
    {input : State source} {output : State target} {saved : Saved target} {reply : O}
    (called : head.effect.run input = some (output, saved, reply))
    (stable : Stable ops frame) (probe : State (fun state => frame state ∧ target state))
    (same : Observed observe keys probe output) :
    ∃ restored, applySaved stable saved (savedKeeps head called) probe = some restored ∧
      Observed observe keys restored input := by
  obtain ⟨recovered, returned, relates⟩ := head.lawful.recover _ _ _ _ called
  have paired := head.lawful.respect input input (observed_refl observe keys input)
  rw [called] at paired
  have inverse : MapRelated (Observed observe keys) saved saved := paired.2.1
  have onProbe := inverse ⟨probe.val, probe.property.2⟩ output same
  rw [returned] at onProbe
  cases eq : saved ⟨probe.val, probe.property.2⟩ with
  | none =>
    rw [eq] at onProbe
    contradiction
  | some result =>
    rw [eq] at onProbe
    have frameResult := undoKeeps stable (savedKeeps head called _ _ eq) probe.property.1
    refine ⟨⟨result.val, frameResult⟩, ?_, ?_⟩
    · exact Option.pmap_eq_some_iff.mpr ⟨result, frameResult, eq, rfl⟩
    · exact observed_trans (show Observed observe keys result recovered from onProbe) relates

/-- The saved composite succeeds on its own result. When a tail restores
the preceding output only observationally, respect of the actual captured
head inverse supplies both its definedness and the recovery comparison. -/
theorem evaluate_recovers (it : Plan code source) (stable : Stable ops frame)
    (input : State source) (inFrame : frame input.val) {result : Result frame}
    (called : evaluate it stable input inFrame = some result) :
    ∃ restored, result.restore result.output = some restored ∧ Observed observe keys restored input := by
  induction it generalizing frame with
  | stage head entry tail link ih =>
    simp only [evaluate] at called
    split at called
    · cases called
    next output saved reply landed =>
      split at called
      next _ =>
        cases called
        exact applySaved_recovers head landed stable _ (observed_refl observe keys output)
      next next selected =>
        obtain ⟨rest, evaluated, rfl⟩ := Option.map_eq_some_iff.mp called
        obtain ⟨intermediate, undone, observed⟩ := ih reply next selected _ _ _ evaluated
        obtain ⟨restored, applied, recovered⟩ := applySaved_recovers head landed stable intermediate observed
        exact ⟨restored, Option.bind_eq_some_iff.mpr ⟨intermediate, undone, applied⟩, recovered⟩

private theorem applySaved_native (stable : Stable ops frame) {saved : Saved target} {token : Inverse Name V}
    (preserves : ∀ before after, saved before = some after → ∃ token : Inverse Name V, after.val = undo token before.val)
    (native : ∀ before after, saved before = some after → after.val = undo token before.val)
    {probe : State (fun state => frame state ∧ target state)} {restored : State frame}
    (applied : applySaved stable saved preserves probe = some restored) :
    restored.val = undo token probe.val := by
  obtain ⟨result, _, found, rfl⟩ := Option.pmap_eq_some_iff.mp applied
  exact native _ _ found

private theorem discharge_last (state : R) (tokens : List (Inverse Name V)) (token : Inverse Name V) :
    discharge (tokens ++ [token]) state = undo token (discharge tokens state) := by
  induction tokens generalizing state with
  | nil => rfl
  | cons first rest ih => exact ih (undo first state)

/-- A successful calculation selects an actual native word. On every
admitted probe where the composed inverse succeeds, it discharges that
word in reverse landing order using the original tokens. -/
theorem evaluate_native (it : Plan code source) (stable : Stable ops frame)
    (input : State source) (inFrame : frame input.val) {result : Result frame}
    (called : evaluate it stable input inFrame = some result) :
    ∃ tokens, Landings program actor code input.val result.output.val tokens ∧
      ∀ probe restored, result.restore probe = some restored →
        restored.val = discharge tokens.reverse probe.val := by
  induction it generalizing frame with
  | stage head entry tail link ih =>
    simp only [evaluate] at called
    split at called
    · cases called
    next output saved reply landed =>
      obtain ⟨token, primitive, native, _, _⟩ := head.realizes.sound _ _ _ _ landed
      split at called
      next terminal =>
        cases called
        rw [terminal] at primitive
        exact ⟨[token], .last primitive,
          fun _ _ applied => applySaved_native stable (savedKeeps head landed) native.value applied⟩
      next next selected =>
        obtain ⟨rest, evaluated, rfl⟩ := Option.map_eq_some_iff.mp called
        obtain ⟨tokens, tailLands, tailUndo⟩ := ih reply next selected _ _ _ evaluated
        rw [selected] at primitive
        refine ⟨token :: tokens, .next primitive tailLands, ?_⟩
        intro probe restored applied
        obtain ⟨intermediate, returned, undone⟩ := Option.bind_eq_some_iff.mp applied
        rw [List.reverse_cons, discharge_last, ← tailUndo _ _ returned]
        exact applySaved_native stable (savedKeeps head landed) native.value undone

/-- Compare the scoped inverse with a birth-annotated instance of its native
word. Incarnation tests preserve the table result. Exact registry agreement
holds when every retirement addresses its original child or an absent row. -/
theorem evaluate_guarded_replay (it : Plan code source) (stable : Stable ops frame)
    (input : State source) (inFrame : frame input.val) {result : Result frame}
    (called : evaluate it stable input inFrame = some result) :
    ∃ tokens, Landings program actor code input.val result.output.val tokens ∧
      ∀ (word : List (IncarnationReplay.Capture Name Key (Scalar ops))) (live : Name → Option Nat)
        (probe : State result.domain) (restored : State frame),
        word.map IncarnationReplay.Capture.token = tokens.reverse.map (encodeInverse ops) →
        result.restore probe = some restored →
        let guarded := IncarnationReplay.replay live word (encodeRegistry ops probe.val)
        RuleEvaluation.TablesUnchanged (encodeRegistry ops restored.val) guarded ∧
          ((∀ capture ∈ word, ∀ child, capture.token = .retire child →
            probe.val child = none ∨ live child = some capture.index) →
            encodeRegistry ops restored.val = guarded) := by
  obtain ⟨tokens, landed, native⟩ := evaluate_native it stable input inFrame called
  refine ⟨tokens, landed, ?_⟩
  intro word live probe restored projects succeeds
  dsimp only
  rw [native probe restored succeeds, encode_discharge, ← projects]
  refine ⟨IncarnationReplay.replay_tables live word (fun _ _ => rfl), ?_⟩
  intro matching
  symm
  apply IncarnationReplay.replay_eq_native
  intro capture member child retired
  rcases matching capture member child retired with absent | current
  · exact .inl (by simp [encodeRegistry, absent])
  · exact .inr current

section Renaming
open ScopedNameTransport (domain moveState originalState moveSaved stable_domain)
open FreshNameTransport (registry)
local notation "P" => Renaming.Permutation Name

def Result.rename (ops : CoeffectOperations V) (p : P) (result : Result frame) : Result (ScopedNameTransport.domain p frame) where
  domain := ScopedNameTransport.domain p result.domain
  output := moveState ops p result.output
  restore probe := (result.restore (originalState p probe)).map (moveState ops p)

private theorem saved_rename (p : P) (stable : Stable ops frame) (saved : Saved target)
    (native : ∀ before after, saved before = some after → ∃ token : Inverse Name V, after.val = undo token before.val)
    (renamed : ∀ before after, moveSaved ops p saved before = some after →
      ∃ token : Inverse Name V, after.val = undo token before.val)
    (probe : State (fun state => frame state ∧ target state)) :
    applySaved (stable_domain p stable) (moveSaved ops p saved) renamed (moveState ops p probe) =
      (applySaved stable saved native probe).map (moveState ops p) := by
  apply (Option.map_inj_right (fun _ _ equal => Subtype.ext equal)).mp
  have originalProbe : (⟨(moveState ops p probe).val, (moveState ops p probe).property.2⟩ :
      State (domain p target)) = moveState ops p ⟨probe.val, probe.property.2⟩ := rfl
  rw [applySaved_values, originalProbe]
  simp only [moveSaved, ScopedNameTransport.original_move, Option.map_map]
  have values := applySaved_values stable saved native probe
  simpa only [Option.map_map, Function.comp_def] using congrArg (Option.map (registry p)) values.symm

private theorem finish_rename (p : P) (stable : Stable ops frame) (output : State target)
    (valid : frame output.val) (saved : Saved target)
    (native : ∀ before after, saved before = some after → ∃ token : Inverse Name V, after.val = undo token before.val)
    (movedValid : domain p frame (moveState ops p output).val)
    (renamed : ∀ before after, moveSaved ops p saved before = some after →
      ∃ token : Inverse Name V, after.val = undo token before.val) :
    finish (stable_domain p stable) (moveState ops p output) movedValid (moveSaved ops p saved) renamed =
      (finish stable output valid saved native).rename ops p := by
  unfold finish Result.rename
  congr 1
  funext probe
  change applySaved (stable_domain p stable) (moveSaved ops p saved) renamed probe =
    (applySaved stable saved native (originalState p probe)).map (moveState ops p)
  let original := originalState (source := fun state => frame state ∧ target state) p probe
  have roundTrip : moveState ops p original = probe :=
    ScopedNameTransport.move_original (source := fun state => frame state ∧ target state) p probe
  calc
    _ = applySaved (stable_domain p stable) (moveSaved ops p saved) renamed (moveState ops p original) :=
      congrArg (applySaved (stable_domain p stable) (moveSaved ops p saved) renamed) roundTrip.symm
    _ = _ := saved_rename p stable saved native renamed original

private theorem prepend_rename (p : P) (stable : Stable ops frame) (saved : Saved target)
    (native : ∀ before after, saved before = some after → ∃ token : Inverse Name V, after.val = undo token before.val)
    (renamed : ∀ before after, moveSaved ops p saved before = some after →
      ∃ token : Inverse Name V, after.val = undo token before.val)
    (rest : Result (fun state => frame state ∧ target state)) :
    prepend (stable_domain p stable) (moveSaved ops p saved) renamed (rest.rename ops p) =
      (prepend stable saved native rest).rename ops p := by
  unfold prepend Result.rename
  congr 1
  funext probe
  change ((rest.restore (originalState p probe)).map (moveState ops p)).bind
      (applySaved (stable_domain p stable) (moveSaved ops p saved) renamed) =
    ((rest.restore (originalState p probe)).bind (applySaved stable saved native)).map (moveState ops p)
  cases rest.restore (originalState p probe) with
  | none => rfl
  | some restored => exact saved_rename p stable saved native renamed restored

/-- The output and the entire partial inverse are conjugated by the same
bijection. The selected path retains its forward and backward domain proofs. -/
theorem evaluate_rename (p : P) (it : Plan code source) (stable : Stable ops frame)
    (input : State source) (inFrame : frame input.val) :
    evaluate (ScopedNameTransport.iterator p it) (stable_domain p stable) (moveState ops p input)
      (by simpa only [domain, moveState, FreshNameTransport.registry_symm ops] using inFrame) =
    (evaluate it stable input inFrame).map (Result.rename ops p) := by
  induction it generalizing frame with
  | stage head entry tail link ih =>
    simp only [ScopedNameTransport.iterator, evaluate, ScopedNameTransport.head]
    split
    next missed =>
      rw [ScopedNameTransport.effect_run, Option.map_eq_none_iff] at missed
      split
      · rfl
      next _ _ _ called =>
        rw [missed] at called
        cases called
    next _ _ _ movedCalled =>
      rw [ScopedNameTransport.effect_run] at movedCalled
      obtain ⟨⟨output, saved, reply⟩, called, same⟩ := Option.map_eq_some_iff.mp movedCalled
      cases same
      simp only [Function.comp_apply]
      split
      next terminal =>
        rw [FreshNameTransport.program_next] at terminal
        split
        next missed =>
          rw [missed] at called
          cases called
        next _ _ _ called' =>
          cases Option.some.inj (called.symm.trans called')
          split
          · congr 1
            apply finish_rename
          next _ continues =>
            rw [terminal] at continues
            cases continues
      next next selected =>
        rw [FreshNameTransport.program_next] at selected
        split
        next missed =>
          rw [missed] at called
          cases called
        next _ _ _ called' =>
          cases Option.some.inj (called.symm.trans called')
          split
          next terminal =>
            rw [terminal] at selected
            cases selected
          next following picked =>
            have sameCode := Option.some.inj (selected.symm.trans picked)
            subst following
            have tailMoved := ih reply next picked (Stable.and stable (head.outputStable reply next picked))
              ⟨output.val, link _ _ _ _ _ called picked⟩ ⟨outputKeeps head called stable inFrame, output.property⟩
            refine (congrArg (Option.map _) tailMoved).trans ?_
            rw [Option.map_map, Option.map_map]
            congr 1
            funext result
            apply prepend_rename

omit [DecidableEq Name] in

private theorem related_rename_right (p : P) {left right : Result frame}
    (related : Result.Related observe keys left right) :
    (right.rename ops p).domain = domain p left.domain ∧
      left.ObservationallyRelated observe keys (right.rename ops p) := by
  refine ⟨congrArg (domain p) related.1.symm, ?_, ?_⟩
  · exact (FreshNameTransport.tables_related_rename_right p observe keys left.output.val right.output.val).mpr
      related.2.1
  · intro first second probes
    let original := originalState (source := right.domain) p second
    have roundTrip : moveState ops p original = second := ScopedNameTransport.move_original (source := right.domain) p second
    have originalProbes : Observed observe keys first original := by
      apply (FreshNameTransport.tables_related_rename_right p observe keys first.val original.val).mp
      change Observed observe keys first (moveState ops p original)
      rwa [roundTrip]
    have restored := related.2.2 first original originalProbes
    change OptionRel (Observed observe keys) (left.restore first) ((right.restore original).map (moveState ops p))
    cases leftResult : left.restore first <;> cases rightResult : right.restore original <;>
      simp_all only [Option.map_none, Option.map_some, OptionRel]
    exact (FreshNameTransport.tables_related_rename_right p observe keys _ _).mpr restored

/-- Compare two admitted evaluations under a coherent change of draws.
Forward failure and inverse failure agree on related probes, and the
right final probe domain is the transported left domain. -/
theorem evaluate_respects_renamed (p : P) (it : Plan code source) (stable : Stable ops frame)
    (left : State source) (right : State (domain p source)) (leftFrame : frame left.val)
    (rightFrame : domain p frame right.val) (related : Observed observe keys left right) :
    OptionRel (fun a b => b.domain = domain p a.domain ∧ a.ObservationallyRelated observe keys b)
      (evaluate it stable left leftFrame)
      (evaluate (ScopedNameTransport.iterator p it) (stable_domain p stable) right rightFrame) := by
  obtain ⟨original, rfl⟩ : ∃ original, moveState ops p original = right :=
    ⟨originalState p right, ScopedNameTransport.move_original p right⟩
  have originalFrame : frame original.val := by
    simpa only [domain, moveState, FreshNameTransport.registry_symm ops] using rightFrame
  have originalRelated : Observed observe keys left original :=
    (FreshNameTransport.tables_related_rename_right p observe keys left.val original.val).mp related
  have evaluated := evaluate_respects it stable left original leftFrame originalFrame originalRelated
  rw [evaluate_rename p it stable original originalFrame]
  cases leftCall : evaluate it stable left leftFrame <;>
    cases rightCall : evaluate it stable original originalFrame <;>
    simp_all only [Option.map_none, Option.map_some, OptionRel]
  exact related_rename_right p evaluated

end Renaming

end Cordis.Repairs.ScopedRollback
