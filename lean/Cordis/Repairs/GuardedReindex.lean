import Cordis.Repairs.GuardedHistory

/-! Compact a stamped guarded execution into an indexed trace. A retained
stamp identifies the same birth and capture before and after compaction. -/
namespace Cordis.Repairs.GuardedHistory
open Calculus Stages IncarnationReplay LegalHistory
open Vestigial (CutNotes eventActor noteStep)
open OrchestrationSorting (Command)
universe u
variable {Name Key Value Code Error : Type u} [DecidableEq Name] [DecidableEq Key]
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "C" => Capture Name Key Value
local notation "Notes" => CutNotes Name Key Value
local notation "Ev" => Event Name Key Code
local notation "Cmd" => Command Name Key Code
local notation "Program" => Code → Instruction Name Key Value Code Error
variable {program : Code → Instruction Name Key Value Code Error}

omit [DecidableEq Name] [DecidableEq Key] in
def reindexNotes (stamp : Nat → Nat) (notes : Notes) : Notes :=
  (fun name => (notes.1 name).map stamp, fun name => (notes.2 name).map (Capture.reindex stamp))

omit [DecidableEq Name] [DecidableEq Key] in
theorem reindexNotes_involutive (stamp : Nat → Nat) (undo : ∀ index, stamp (stamp index) = index)
    (notes : Notes) : reindexNotes stamp (reindexNotes stamp notes) = notes := by
  apply Prod.ext
  · funext name
    cases found : notes.1 name <;> simp [reindexNotes, found, undo]
  · funext name
    change (((notes.2 name).map (Capture.reindex stamp)).map (Capture.reindex stamp)) = _
    rw [List.map_map]
    have restore : (Capture.reindex stamp ∘ Capture.reindex stamp : C → C) = id := by
      funext entry
      rcases entry with ⟨token, index⟩
      simp [Capture.reindex, undo]
    rw [restore, List.map_id]

omit [DecidableEq Key] in
theorem noteStep_reindex (stamp : Nat → Nat) (before after : R) (actor : Name) (index : Nat) (notes : Notes) :
    noteStep before after actor (stamp index) (reindexNotes stamp notes) =
      reindexNotes stamp (noteStep before after actor index notes) := by
  apply Prod.ext
  · funext name
    cases found : after name <;> cases live : notes.1 name <;> simp [noteStep, reindexNotes, found, live]
  · exact funext (advance_annotate stamp (before := before) (after := after)
      (actor := actor) (time := index) (fun _ => rfl) rfl rfl)

/-- Run exactly the same event with a compact stamp. Every guarded
retirement has the same answer under the embedding of stamps. -/
theorem step_of_reindexed (stamp : Nat → Nat) (injective : Function.Injective stamp)
    {before after : R} {event : Ev} {index : Nat} {notes : Notes}
    (old : GuardedSuffix.Transition program (reindexNotes stamp notes) event before after) :
    GuardedSuffix.Step program event index before notes after (noteStep before after (eventActor event) index notes) := by
  refine ⟨?_, rfl⟩
  cases event with
  | command => exact old
  | lifecycle kind actor =>
    cases kind
    case unload =>
      obtain ⟨row, view, found, phase, free, ended⟩ := old
      refine ⟨row, view, found, ?_, free, ?_⟩
      · simpa [reindexNotes, List.map_map, Function.comp_def, Capture.reindex] using phase
      · have replayed := replay_reindex injective (live := notes.1) (other := (reindexNotes stamp notes).1)
          (fun _ => rfl) (notes.2 actor) before
        change after = mark (replay (reindexNotes stamp notes).1 ((notes.2 actor).map (Capture.reindex stamp)) before)
          actor .inactive at ended
        rw [replayed] at ended
        exact ended
    all_goals exact old

private def expandStamp (stamps : List Nat) (limit : Nat) (index : Nat) : Nat :=
  ((0 :: stamps)[index]?).getD (limit + index + 1)

private theorem expandStamp_injective (stamps : List Nat) (limit : Nat)
    (unique : stamps.Nodup) (positive : 0 ∉ stamps) (bounded : ∀ stamp ∈ stamps, stamp ≤ limit) :
    Function.Injective (expandStamp stamps limit) := by
  have extended : (0 :: stamps).Nodup := List.nodup_cons.mpr ⟨positive, unique⟩
  have within {index value : Nat} (found : (0 :: stamps)[index]? = some value) : value ≤ limit := by
    rcases List.mem_cons.mp (List.mem_of_getElem? found) with rfl | present
    · exact Nat.zero_le _
    · exact bounded _ present
  intro i j same
  unfold expandStamp at same
  cases first : (0 :: stamps)[i]? <;> cases second : (0 :: stamps)[j]? <;> rw [first, second] at same
  · simp only [Option.getD_none] at same
    omega
  · have smaller := within second
    simp only [Option.getD_none, Option.getD_some] at same
    omega
  · have smaller := within first
    simp only [Option.getD_none, Option.getD_some] at same
    omega
  · simp only [Option.getD_some] at same
    have fits : i < (0 :: stamps).length := by
      by_cases inside : i < (0 :: stamps).length
      · exact inside
      · rw [List.getElem?_eq_none_iff.mpr (Nat.le_of_not_gt inside)] at first
        cases first
    exact List.getElem?_inj fits extended (first.trans ((congrArg some same).trans second.symm))

/-- Index successive cuts of a run with possibly gapped stamps. The
embedding relates each recorded final stamp to the original run. -/
private theorem index_segment {events : List (Nat × Ev)} {before final : R}
    {original finalNotes : Notes} {roots : List Cmd}
    {sources : Nat → Option (GuardedSuffix.ActorSource Key Code)}
    (run : GuardedSuffix.ExecWith program sources events before original final finalNotes roots)
    (expand : Nat → Nat) (injective : Function.Injective expand)
    (offset : Nat) (notes : Notes) (agrees : original = reindexNotes expand notes)
    (stamps : ∀ i (bound : i < events.length), events[i].1 = expand (offset + i + 1))
    (fallback : Ev) :
    ∃ (states : Nat → R) (recorded : Nat → Notes) (event : Nat → Ev),
      states 0 = before ∧ recorded 0 = notes ∧ states events.length = final ∧
      reindexNotes expand (recorded events.length) = finalNotes ∧
      (∀ i (bound : i < events.length), event i = events[i].2 ∧
        GuardedSuffix.Step program (event i) (offset + i + 1) (states i) (recorded i) (states (i + 1)) (recorded (i + 1)) ∧
        GuardedSuffix.CheckedSource sources events[i].1 (states i) (reindexNotes expand (recorded i)) (event i)) ∧
      (List.range events.length).flatMap (fun i => eventRoots (states i) (event i)) = roots := by
  induction run generalizing offset notes with
  | nil =>
    exact ⟨fun _ => _, fun _ => notes, fun _ => fallback, rfl, rfl, rfl, agrees.symm,
      fun _ impossible => False.elim (Nat.not_lt_zero _ impossible), rfl⟩
  | @cons stamp event rest before original middle oldMiddle final finalNotes roots step suffix checked ih =>
    have headStamp : stamp = expand (offset + 1) := stamps 0 (by simp)
    let newMiddle := noteStep before middle (eventActor event) (offset + 1) notes
    have transition : GuardedSuffix.Transition program (reindexNotes expand notes) event before middle := agrees ▸ step.1
    have headStep := step_of_reindexed expand injective (index := offset + 1) transition
    have headNotes : oldMiddle = reindexNotes expand newMiddle := by
      rw [step.2, agrees, headStamp, noteStep_reindex]
    have restStamps (i : Nat) (bound : i < rest.length) : rest[i].1 = expand (offset + 1 + i + 1) := by
      have same : offset + (i + 1) + 1 = offset + 1 + i + 1 := by omega
      simpa only [List.getElem_cons_succ, same] using stamps (i + 1) (by simp; omega)
    obtain ⟨tailStates, tailNotes, tailEvents, start, seed, endpoint, noteEndpoint, later, rootOrder⟩ :=
      ih (offset + 1) newMiddle headNotes restStamps
    let states : Nat → R
      | 0 => before
      | i + 1 => tailStates i
    let recorded : Nat → Notes
      | 0 => notes
      | i + 1 => tailNotes i
    let events : Nat → Ev
      | 0 => event
      | i + 1 => tailEvents i
    refine ⟨states, recorded, events, rfl, rfl, endpoint, noteEndpoint, ?_, ?_⟩
    · intro i bound
      cases i with
      | zero =>
        refine ⟨rfl, ?_, agrees ▸ checked⟩
        change GuardedSuffix.Step program event (offset + 1) before notes (tailStates 0) (tailNotes 0)
        rw [start, seed]
        exact headStep
      | succ i =>
        obtain ⟨eventEq, laterStep, laterSource⟩ := later i (by simpa using bound)
        refine ⟨eventEq, ?_, laterSource⟩
        change GuardedSuffix.Step program (tailEvents i) (offset + (i + 1) + 1)
          (tailStates i) (tailNotes i) (tailStates (i + 1)) (tailNotes (i + 1))
        rw [show offset + (i + 1) + 1 = offset + 1 + i + 1 by omega]
        exact laterStep
    · simp only [List.length_cons, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map,
        states, events, rootOrder]

/-- Convert an empty-origin run retaining distinct source stamps into a
compact source trace. Its ordered event labels, exact endpoint, and root
provenance agree with the stamped run. -/
theorem trace_with_sources {events : List (Nat × Ev)} {final : R} {finalNotes : Notes} {roots : List Cmd}
    {sources : Nat → Option (GuardedSuffix.ActorSource Key Code)}
    (run : GuardedSuffix.ExecWith program sources events (fun _ => none) (fun _ => none, fun _ => []) final finalNotes roots)
    (unique : (events.map Prod.fst).Nodup) (positive : 0 ∉ events.map Prod.fst)
    (limit : Nat) (bounded : ∀ stamp ∈ events.map Prod.fst, stamp ≤ limit) (fallback : Ev) :
    ∃ (trace : Trace program events.length) (expand : Nat → Nat),
      Function.Injective expand ∧ trace.state events.length = final ∧
      reindexNotes expand (trace.notes events.length) = finalNotes ∧
      (∀ i (bound : i < events.length), trace.event i = events[i].2 ∧ expand (i + 1) = events[i].1 ∧
        GuardedSuffix.CheckedSource sources events[i].1 (trace.state i) (reindexNotes expand (trace.notes i)) (trace.event i)) ∧
      (List.range events.length).flatMap (fun i => eventRoots (trace.state i) (trace.event i)) = roots := by
  let expand := expandStamp (events.map Prod.fst) limit
  have injective := expandStamp_injective (events.map Prod.fst) limit unique positive bounded
  have stamps (i : Nat) (bound : i < events.length) : events[i].1 = expand (0 + i + 1) := by
    unfold expand expandStamp
    simp [bound]
  obtain ⟨states, notes, event, start, seed, endpoint, mapped, steps, rootOrder⟩ :=
    index_segment run expand injective 0 (fun _ => none, fun _ => []) rfl stamps fallback
  let compact : Trace program events.length := ⟨states, notes, event, start, seed, fun i bound => by
    simpa only [Nat.zero_add] using (steps i bound).2.1⟩
  exact ⟨compact, expand, injective, endpoint, mapped,
    fun i bound => ⟨(steps i bound).1, by simpa only [Nat.zero_add] using (stamps i bound).symm, (steps i bound).2.2⟩,
    rootOrder⟩

theorem trace_of_exec {events : List (Nat × Ev)} {final : R} {finalNotes : Notes} {roots : List Cmd}
    (run : GuardedSuffix.Exec program events (fun _ => none) (fun _ => none, fun _ => []) final finalNotes roots)
    (unique : (events.map Prod.fst).Nodup) (positive : 0 ∉ events.map Prod.fst)
    (limit : Nat) (bounded : ∀ stamp ∈ events.map Prod.fst, stamp ≤ limit) (fallback : Ev) :
    ∃ (trace : Trace program events.length) (expand : Nat → Nat),
      Function.Injective expand ∧ trace.state events.length = final ∧
      reindexNotes expand (trace.notes events.length) = finalNotes ∧
      (∀ i (bound : i < events.length), trace.event i = events[i].2 ∧ expand (i + 1) = events[i].1) ∧
      (List.range events.length).flatMap (fun i => eventRoots (trace.state i) (trace.event i)) = roots := by
  obtain ⟨trace, expand, injective, endpoint, notes, stamps, rootOrder⟩ :=
    trace_with_sources run unique positive limit bounded fallback
  exact ⟨trace, expand, injective, endpoint, notes, fun i bound => ⟨(stamps i bound).1, (stamps i bound).2.1⟩, rootOrder⟩

/-- A surviving event retains its label, actor incarnation and component.
`expand` maps both its compact stamp and any live actor's compact birth
stamp to stamps in the source trace. -/
structure RetainedEvents {originalLength compactLength : Nat}
    (original : Trace program originalLength) (compact : Trace program compactLength) (expand : Nat → Nat) : Prop where
  injective : Function.Injective expand
  stamp : ∀ i, i < compactLength → 0 < expand (i + 1) ∧ expand (i + 1) ≤ originalLength
  label : ∀ i, i < compactLength → compact.event i = original.event (expand (i + 1) - 1)
  actor : ∀ i, i < compactLength →
    GuardedSuffix.actorSource (compact.state i) (reindexNotes expand (compact.notes i)) (compact.event i) =
      GuardedSuffix.actorSource (original.state (expand (i + 1) - 1)) (original.notes (expand (i + 1) - 1))
        (original.event (expand (i + 1) - 1))

theorem RetainedEvents.actor_birth {originalLength compactLength : Nat}
    {original : Trace program originalLength} {compact : Trace program compactLength} {expand : Nat → Nat}
    (retained : RetainedEvents original compact expand) {cut : Nat} (bound : cut < compactLength) :
    ((compact.notes cut).1 (compact.actor cut)).map expand =
      (original.notes (expand (cut + 1) - 1)).1 (original.actor (expand (cut + 1) - 1)) :=
  congrArg Prod.fst (retained.actor cut bound)

omit [DecidableEq Name] [DecidableEq Key] in
theorem actorSource_reindex (expand : Nat → Nat) (state : R) (notes : Notes) (event : Ev) :
    GuardedSuffix.actorSource state (reindexNotes expand notes) event =
      Prod.map (Option.map expand) id (GuardedSuffix.actorSource state notes event) := rfl

theorem RetainedEvents.refl {length : Nat} (trace : Trace program length) : RetainedEvents trace trace id := by
  refine ⟨fun _ _ equal => equal, fun i bound => ⟨Nat.zero_lt_succ i, bound⟩, fun _ _ => rfl, ?_⟩
  intro i _
  rw [actorSource_reindex]
  simp

theorem RetainedEvents.trans {first middle final : Nat}
    {original : Trace program first} {intermediate : Trace program middle} {compact : Trace program final}
    {expand embed : Nat → Nat} (outer : RetainedEvents original intermediate expand)
    (inner : RetainedEvents intermediate compact embed) : RetainedEvents original compact (expand ∘ embed) := by
  have cut (i : Nat) (bounded : i < final) : embed (i + 1) - 1 + 1 = embed (i + 1) := by
    have := (inner.stamp i bounded).1
    omega
  have inside (i : Nat) (bounded : i < final) : embed (i + 1) - 1 < middle := by
    have := inner.stamp i bounded
    omega
  refine ⟨outer.injective.comp inner.injective, ?_, ?_, ?_⟩
  · intro i bounded
    simpa only [Function.comp_apply, cut i bounded] using outer.stamp _ (inside i bounded)
  · intro i bounded
    refine (inner.label i bounded).trans ?_
    simpa only [Function.comp_apply, cut i bounded] using outer.label _ (inside i bounded)
  · intro i bounded
    have old := outer.actor _ (inside i bounded)
    have recent := congrArg (Prod.map (Option.map expand) id) (inner.actor i bounded)
    rw [actorSource_reindex] at old recent
    have composed (fields : GuardedSuffix.ActorSource Key Code) :
        Prod.map (Option.map expand) id (Prod.map (Option.map embed) id fields) =
          Prod.map (Option.map (expand ∘ embed)) id fields := by
      rcases fields with ⟨tag, component⟩
      cases tag <;> rfl
    rw [composed] at recent
    rw [actorSource_reindex]
    simpa only [Function.comp_apply, cut i bounded] using recent.trans old

theorem Trace.reindexNotes_fixed {last cut : Nat} (trace : Trace program last) (bounded : cut ≤ last)
    (stamp : Nat → Nat) (fixed : ∀ old, old ≤ cut → stamp old = old) :
    reindexNotes stamp (trace.notes cut) = trace.notes cut := by
  apply Prod.ext
  · funext name
    change ((trace.notes cut).1 name).map stamp = (trace.notes cut).1 name
    cases birth : (trace.notes cut).1 name with
    | none => rfl
    | some old =>
      have recorded := birth
      rw [trace.notes_eq cut bounded] at recorded
      exact congrArg some (fixed old (Incarnation.resident_of_birthAt recorded).ordered)
  · funext name
    change ((trace.notes cut).2 name).map (Capture.reindex stamp) = _
    calc
      _ = ((trace.notes cut).2 name).map id := by
        apply List.map_congr_left
        intro entry member
        have within := (trace.capture_origin cut bounded name entry member).1
        cases entry
        simp [Capture.reindex, fixed _ within]
      _ = _ := List.map_id _

end Cordis.Repairs.GuardedHistory
