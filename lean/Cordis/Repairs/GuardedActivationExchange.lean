import Cordis.Repairs.ActivationAnnotations
import Cordis.Repairs.GuardedEpisodeExcision
import Cordis.Repairs.GuardedOpenExchange
import Cordis.Repairs.GuardedReindex

/-! Replay the suffix after exchanging two adjacent open activations. -/
namespace Cordis.Repairs.GuardedHistory
open Calculus Stages LegalHistory
open EpisodeAnnotations (NotesRelated exchanged_activation_notes)
open PaperEffectEquations (CoeffectOperations ValueOperationWitness)
open PaperObservationEquations (OperationRespects)
open PartialCoeffectIndependenceContracts (tableSetoid)
open TypedRegistry (encodeProgram Scalar RawRegistry)
open Vestigial (noteStep CutNotes eventActor)
open ExchangeReplay (exchangedIndex)
universe u
variable {Name Key Code : Type u} {V : Key → Type u} {ops : CoeffectOperations V}
variable [DecidableEq Name] [DecidableEq Key]
variable {program : Code → TypedRegistry.Instruction Name ops Code} {last : Nat}
local notation "A" => Scalar ops
local notation "R" => RawRegistry Name ops Code
local notation "Notes" => CutNotes Name Key A
local notation "Source" => Trace (encodeProgram program) last

/-- Replay from a related guarded cut, retaining the comparison at every
intermediate cut as well as the actual original suffix events. -/
theorem Trace.replay_from_related_cut (trace : Source)
    (observe : ∀ key, Setoid (V key)) (respect : ∀ key, OperationRespects ops key (observe key).r)
    {start : Nat} (bounded : start ≤ last) {state : R} {notes : Notes}
    (compared : @StageSimulation.Related Name Key A Code PUnit.{u + 1} (TypedCoeffectReplay.setoid observe) Eq
      (trace.state start) state)
    (aligned : @NotesRelated Name Key A (TypedCoeffectReplay.setoid observe) (trace.notes start) notes)
    (projects : GuardedSuffix.SavedWordsAgree state notes) :
    letI : Setoid A := TypedCoeffectReplay.setoid observe
    ∃ cuts : Nat → R × Notes,
      cuts start = (state, notes) ∧
      (∀ cut, start ≤ cut → cut < last →
        GuardedSuffix.Step (encodeProgram program) (trace.event cut) (cut + 1)
          (cuts cut).1 (cuts cut).2 (cuts (cut + 1)).1 (cuts (cut + 1)).2) ∧
      ∀ cut, start ≤ cut → cut ≤ last →
        StageSimulation.Related Eq (trace.state cut) (cuts cut).1 ∧
        NotesRelated (trace.notes cut) (cuts cut).2 ∧ GuardedSuffix.SavedWordsAgree (cuts cut).1 (cuts cut).2 := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  have through (span : Nat) (within : start + span ≤ last) :
      ∃ cuts : Nat → R × Notes,
        cuts start = (state, notes) ∧
        (∀ cut, start ≤ cut → cut < start + span →
          GuardedSuffix.Step (encodeProgram program) (trace.event cut) (cut + 1)
            (cuts cut).1 (cuts cut).2 (cuts (cut + 1)).1 (cuts (cut + 1)).2) ∧
        ∀ cut, start ≤ cut → cut ≤ start + span →
          StageSimulation.Related Eq (trace.state cut) (cuts cut).1 ∧
          NotesRelated (trace.notes cut) (cuts cut).2 ∧ GuardedSuffix.SavedWordsAgree (cuts cut).1 (cuts cut).2 := by
    induction span with
    | zero =>
      refine ⟨fun _ => (state, notes), rfl, ?_, ?_⟩
      · intro cut lower upper
        omega
      · intro cut lower upper
        have same : cut = start := by omega
        subst cut
        exact ⟨compared, aligned, projects⟩
    | succ span ih =>
      obtain ⟨cuts, initial, steps, paired⟩ := ih (by omega)
      have atEnd := paired (start + span) (by omega) (Nat.le_refl _)
      obtain ⟨next, recorded, advanced, related, comparedNotes, nextProjects, _⟩ :=
        GuardedSuffix.transport_step observe program respect (trace.step (start + span) (by omega))
          atEnd.1 atEnd.2.1 atEnd.2.2
      let extended (cut : Nat) := if cut = start + span + 1 then (next, recorded) else cuts cut
      have unchanged (cut : Nat) (earlier : cut ≤ start + span) : extended cut = cuts cut := by
        simp [extended, show cut ≠ start + span + 1 by omega]
      have atNext : extended (start + span + 1) = (next, recorded) := by simp [extended]
      refine ⟨extended, (unchanged start (by omega)).trans initial, ?_, ?_⟩
      · intro cut lower upper
        by_cases lastStep : cut = start + span
        · subst cut
          rw [unchanged _ (Nat.le_refl _), atNext]
          exact advanced
        · rw [unchanged cut (by omega), unchanged (cut + 1) (by omega)]
          exact steps cut lower (by omega)
      · intro cut lower upper
        by_cases finalCut : cut = start + span + 1
        · subst cut
          rw [atNext]
          exact ⟨related, comparedNotes, nextProjects⟩
        · rw [unchanged cut (by omega)]
          exact paired cut lower (by omega)
  have actual := through (last - start) (by omega)
  simpa only [show start + (last - start) = last by omega] using actual

/-- The repaired activation exchange within a complete quiet open history.
The prefix is kept literally. The swapped pair retains both actual events,
replay preserves the exact root sequence, and the endpoint notes identify the same births and captures
by their original stamps. Each retained suffix cut keeps its related
registry, annotations, and root classification. -/
theorem Trace.swap_activations (trace : Source)
    (openOnly : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    {time : Nat} (bounded : time + 1 < last) {firstKind secondKind : Lifecycle} {first second : Name}
    (firstEvent : trace.event time = .lifecycle firstKind first)
    (secondEvent : trace.event (time + 1) = .lifecycle secondKind second) (different : first ≠ second)
    (beginTarget : secondKind = .begin → ∃ view, Target (trace.state time) second view)
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r) :
    letI : Setoid A := TypedCoeffectReplay.setoid observe
    let events := fun cut => if cut = time then trace.event (time + 1)
      else if cut = time + 1 then trace.event time else trace.event cut
    ∃ moved : Source,
      (∀ cut, cut ≤ time → moved.state cut = trace.state cut ∧ moved.notes cut = trace.notes cut) ∧
      (∀ cut, cut < last → moved.event cut = events cut) ∧
      (∀ cut, cut < last →
        eventRoots (moved.state cut) (moved.event cut) = eventRoots (trace.state cut) (trace.event cut)) ∧
      (∀ cut, time + 2 ≤ cut → cut ≤ last →
        StageSimulation.Related Eq (trace.state cut) (moved.state cut) ∧
        NotesRelated (trace.notes cut) (reindexNotes (exchangedIndex time) (moved.notes cut))) ∧
      RetainedEvents trace moved (exchangedIndex time) ∧
      originalRoots moved = originalRoots trace ∧
      (¬ Nonempty (ClosedEpisode moved)) ∧ Progress.Quiet (moved.state last) := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  dsimp only
  have exchange := trace.exchange_activations openOnly quiet bounded firstEvent secondEvent different beginTarget
    (TypedRegistry.encoded_program_callbacks ops observe program recovery commutative)
    (fun _ _ left right _ _ _ _ _ _ _ _ =>
      TypedRegistry.encoded_program_callback_pair ops observe program commutative left right)
  obtain ⟨middle, after, earlier, later, endpoint⟩ := exchange
  have related : StageSimulation.Related Eq (trace.state (time + 2)) after :=
    endpoint.symm (fun _ _ same => same.symm)
  have firstOrdinary : firstKind ≠ .unload := by
    intro same
    subst firstKind
    exact trace.no_unload openOnly (by omega) firstEvent
  have secondOrdinary : secondKind ≠ .unload := by
    intro same
    subst secondKind
    exact trace.no_unload openOnly bounded secondEvent
  let firstNotes := noteStep (trace.state time) middle second (time + 2) (trace.notes time)
  let nextNotes := noteStep middle after first (time + 1) firstNotes
  have firstStep : GuardedSuffix.Step (encodeProgram program) (trace.event (time + 1)) (time + 2)
      (trace.state time) (trace.notes time) middle firstNotes := by
    rw [secondEvent]
    exact ⟨lifecycle_transition secondOrdinary earlier, rfl⟩
  have secondStep : GuardedSuffix.Step (encodeProgram program) (trace.event time) (time + 1)
      middle firstNotes after nextNotes := by
    rw [firstEvent]
    exact ⟨lifecycle_transition firstOrdinary later, rfl⟩
  have projects := trace.projects time (by omega)
  have nextProjects := GuardedSuffix.step_projects secondStep (GuardedSuffix.step_projects firstStep projects)
  obtain ⟨firstActive, oldFirst⟩ := trace.activation_at openOnly quiet (by omega) firstEvent
  obtain ⟨secondActive, oldSecond⟩ := trace.activation_at openOnly quiet bounded secondEvent
  have notesPair : NotesRelated (trace.notes (time + 2)) nextNotes := by
    have recordOne := (trace.step time (by omega)).2
    have recordTwo := (trace.step (time + 1) bounded).2
    rw [firstEvent] at recordOne
    rw [secondEvent] at recordTwo
    rw [show time + 2 = time + 1 + 1 by omega, recordTwo, recordOne]
    exact exchanged_activation_notes oldFirst firstActive oldSecond secondActive earlier later different related
      (trace.notes time) (trace.births_agree time (by omega)) projects (time + 1) (time + 2)
  obtain ⟨cuts, initial, replayed, comparisons⟩ :=
    trace.replay_from_related_cut observe respect (start := time + 2) (by omega) related notesPair nextProjects
  let events (cut : Nat) := if cut = time then trace.event (time + 1)
    else if cut = time + 1 then trace.event time else trace.event cut
  let stamp := exchangedIndex time
  let states (cut : Nat) := if cut ≤ time then trace.state cut
    else if cut = time + 1 then middle else (cuts cut).1
  let recorded (cut : Nat) := if cut ≤ time then trace.notes cut
    else if cut = time + 1 then firstNotes else (cuts cut).2
  let notes (cut : Nat) := reindexNotes stamp (recorded cut)
  have prefixNotes (cut : Nat) (before : cut ≤ time) : notes cut = trace.notes cut := by
    change reindexNotes stamp (if cut ≤ time then trace.notes cut else _) = trace.notes cut
    rw [if_pos before]
    exact trace.reindexNotes_fixed (by omega) stamp (fun index earlier =>
      ExchangeReplay.exchangedIndex_other (by omega) (by omega))
  have suffixState (cut : Nat) (later : time + 2 ≤ cut) : states cut = (cuts cut).1 := by
    simp [states, show ¬ cut ≤ time by omega, show cut ≠ time + 1 by omega]
  have suffixNotes (cut : Nat) (later : time + 2 ≤ cut) :
      reindexNotes stamp (notes cut) = (cuts cut).2 := by
    unfold notes
    rw [reindexNotes_involutive stamp (ExchangeReplay.exchangedIndex_involutive time)]
    simp [recorded, show ¬ cut ≤ time by omega, show cut ≠ time + 1 by omega]
  have restamps (cut : Nat) (later : time + 2 ≤ cut) : stamp (cut + 1) = cut + 1 :=
    ExchangeReplay.exchangedIndex_other (by omega) (by omega)
  have rawStep (cut : Nat) (lower : time ≤ cut) (valid : cut < last) :
      GuardedSuffix.Step (encodeProgram program) (events cut) (stamp (cut + 1))
        (states cut) (recorded cut) (states (cut + 1)) (recorded (cut + 1)) := by
    by_cases atPair : cut = time
    · subst cut
      simpa [events, stamp, states, recorded, show ¬ time + 1 ≤ time by omega] using firstStep
    by_cases atSecond : cut = time + 1
    · subst cut
      simp [events, stamp, states, recorded,
        show ¬ time + 1 ≤ time by omega, show ¬ time + 1 + 1 ≤ time by omega, initial]
      exact secondStep
    · have afterPair : time + 2 ≤ cut := by omega
      rw [suffixState cut afterPair, suffixState (cut + 1) (by omega), restamps cut afterPair]
      simpa [events, recorded, atPair, atSecond, show ¬ cut ≤ time by omega,
        show ¬ cut + 1 ≤ time by omega, show cut + 1 ≠ time + 1 by omega] using replayed cut afterPair valid
  have stepAt (cut : Nat) (valid : cut < last) :
      GuardedSuffix.Step (encodeProgram program) (events cut) (cut + 1)
        (states cut) (notes cut) (states (cut + 1)) (notes (cut + 1)) := by
    by_cases before : cut < time
    · rw [prefixNotes cut (by omega), prefixNotes (cut + 1) (by omega)]
      simpa [events, states, show cut ≠ time by omega, show cut ≠ time + 1 by omega,
        show cut ≤ time by omega, show cut + 1 ≤ time by omega] using trace.step cut valid
    · have actual := rawStep cut (by omega) valid
      have earlier : GuardedSuffix.Transition (encodeProgram program) (reindexNotes stamp (notes cut))
          (events cut) (states cut) (states (cut + 1)) := by
        unfold notes
        rw [reindexNotes_involutive stamp (ExchangeReplay.exchangedIndex_involutive time)]
        exact actual.1
      refine ⟨(step_of_reindexed stamp (ExchangeReplay.exchangedIndex_injective time) (index := cut + 1) earlier).1, ?_⟩
      change reindexNotes stamp (recorded (cut + 1)) = _
      rw [actual.2, ← noteStep_reindex, show stamp (stamp (cut + 1)) = cut + 1 from
        ExchangeReplay.exchangedIndex_involutive time (cut + 1)]
  let result : Source :=
    ⟨states, notes, events, by simpa [states] using trace.start, (prefixNotes 0 (by omega)).trans trace.seed, stepAt⟩
  have suffixRelated (cut : Nat) (later : time + 2 ≤ cut) (valid : cut ≤ last) :
      StageSimulation.Related Eq (trace.state cut) (result.state cut) ∧
      NotesRelated (trace.notes cut) (reindexNotes stamp (result.notes cut)) := by
    change StageSimulation.Related Eq (trace.state cut) (states cut) ∧
      NotesRelated (trace.notes cut) (reindexNotes stamp (notes cut))
    rw [suffixState cut later, suffixNotes cut later]
    exact ⟨(comparisons cut later valid).1, (comparisons cut later valid).2.1⟩
  have prefixEq (cut : Nat) (before : cut ≤ time) :
      result.state cut = trace.state cut ∧ result.notes cut = trace.notes cut :=
    ⟨by simp [result, states, before], prefixNotes cut before⟩
  have firstLabel : result.event time = trace.event (time + 1) := by simp [result, events]
  have secondLabel : result.event (time + 1) = trace.event time := by simp [result, events]
  have retained : RetainedEvents trace result stamp := by
    obtain ⟨other, _, present, _, _⟩ := Transposition.activation_source _ earlier secondActive
    obtain ⟨acting, _, found, _, _⟩ := Transposition.activation_source _ oldFirst firstActive
    have movedFirst : Labeled.Step (encodeProgram program) secondKind.rule second
        (result.state time) (result.state (time + 1)) := by
      simpa [result, states, show ¬ time + 1 ≤ time by omega] using earlier
    refine RetainedEvents.of_adjacent_exchange bounded (fun _ _ => rfl) prefixEq ?_ ?_ ?_
    · rw [firstLabel, (prefixEq time (Nat.le_refl _)).1, (prefixEq time (Nat.le_refl _)).2]
      exact (trace.actorSource_across_activation (by omega) oldFirst firstActive (trace.event (time + 1))
        (by simpa [secondEvent, eventActor] using different.symm) (by simpa [secondEvent, eventActor] using present)).symm
    · rw [secondLabel, ← (prefixEq time (Nat.le_refl _)).1, ← (prefixEq time (Nat.le_refl _)).2]
      exact result.actorSource_across_activation (by omega) movedFirst secondActive (trace.event time)
        (by simpa [firstEvent, eventActor] using different)
        (by simpa [firstEvent, eventActor, (prefixEq time (Nat.le_refl _)).1] using found)
    · intro cut later valid
      have compared := suffixRelated cut later (Nat.le_of_lt valid)
      have label : result.event cut = trace.event cut := by
        simp [result, events, show cut ≠ time by omega, show cut ≠ time + 1 by omega]
      rw [label]
      exact (GuardedSuffix.actorSource_related observe _ compared.1 compared.2).symm
  have rootsAt (cut : Nat) (valid : cut < last) :
      eventRoots (result.state cut) (result.event cut) = eventRoots (trace.state cut) (trace.event cut) := by
    change eventRoots (states cut) (events cut) = _
    by_cases first : cut = time
    · subst cut; simp [events, firstEvent, secondEvent, eventRoots]
    by_cases second : cut = time + 1
    · subst cut; simp [events, firstEvent, secondEvent, eventRoots]
    by_cases beforePair : cut ≤ time
    · simp [events, states, first, second, beforePair]
    · rw [show events cut = trace.event cut by simp [events, first, second]]
      exact eventRoots_agree _ (fun name => (GuardedSuffix.related_roots observe (suffixRelated cut (by omega) (by omega)).1 name).symm)
  have roots : originalRoots result = originalRoots trace := by
    unfold originalRoots
    rw [List.flatMap_def, List.flatMap_def]
    apply congrArg List.flatten
    apply List.map_congr_left
    intro cut member
    exact rootsAt cut (List.mem_range.mp member)
  refine ⟨result, prefixEq, fun _ _ => rfl, rootsAt, suffixRelated, retained, roots, ?_, ?_⟩
  · rintro ⟨closed⟩
    obtain ⟨unload, _⟩ := unload_boundary result closed.interval
    change events closed.closed = _ at unload
    by_cases firstCut : closed.closed = time
    · exact trace.no_unload openOnly bounded (by simpa [events, firstCut] using unload)
    by_cases secondCut : closed.closed = time + 1
    · exact trace.no_unload openOnly (time := time) (by omega) (by simpa [events, firstCut, secondCut] using unload)
    · exact trace.no_unload openOnly closed.interval.bounded (by simpa [events, firstCut, secondCut] using unload)
  · exact GuardedCutState.quiet_of_related (suffixRelated last (by omega) (Nat.le_refl _)).1 quiet

end Cordis.Repairs.GuardedHistory
