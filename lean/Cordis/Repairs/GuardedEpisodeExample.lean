import Cordis.Repairs.GuardedRenaming
import Cordis.Repairs.FreshNameTransport
import Cordis.Repairs.GuardedEpisodeExcision
import Cordis.Repairs.GuardedNormalization
import Cordis.Repairs.GuardedBirthAddresses
import Cordis.Repairs.ScopedEquation54

/-! A selected episode allocates a child whose declaration reserves the
only key. The guarded close enables removal. The same name is then reused
by a root that installs a live provision. -/
namespace Cordis.Repairs.GuardedEpisodeExample
open Calculus Stages LegalHistory GuardedHistory
open GuardedBirthAddresses
open PaperEffectEquations (CoeffectOperations)
open OrchestrationSorting (Command)
open Vestigial (cutNotes eventActor)

abbrev Values : Unit → Type := fun _ => Nat

def operations : CoeffectOperations Values where
  Name _ := Empty
  Argument _ name := nomatch name
  Outcome _ name := nomatch name
  operation _ name := nomatch name

def observe (_ : Unit) : Setoid Nat := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩

abbrev R := TypedRegistry.RawRegistry Nat operations Bool
abbrev F := TypedRegistry.RawFiber Nat operations Bool
abbrev Ev := Event Nat Unit Bool
abbrev Cmd := Command Nat Unit Bool

def owner : Component Unit Bool := ⟨fun _ => false, fun _ => false, false⟩
def provider : Component Unit Bool := ⟨fun _ => false, fun _ => true, true⟩
def entry (code : Bool) : TypedRegistry.Instruction Nat operations Bool :=
  ⟨if code then .provide () 42 else .instantiate provider, fun _ => none⟩
abbrev program := TypedRegistry.encodeProgram entry
def value : TypedRegistry.Scalar operations := TypedCoeffectReplay.pack () 42

def view : View Nat Unit := fun _ => 0

def empty : R := fun _ => none
def s1 : R := put empty 0 (fresh owner none)
def s2 : R := mark s1 0 (.reloading false [] view)
def s3 : R := mark (put s2 1 (fresh provider (some 0))) 0 (.active [.retire 1] view)
def s4 : R := retire s3 0
def s5 : R := mark s4 0 (.unloading [.retire 1] view)
def s6 : R := mark (retire s5 1) 0 .inactive
def s7 : R := erase s6 1
def s8 : R := put s7 1 (fresh provider none)
def s9 : R := mark s8 1 (.reloading true [] view)
def s10 : R := mark (write s9 1 () (some value)) 1 (.active [.restrict 1 ()] view)

def states : Nat → R
  | 0 => empty | 1 => s1 | 2 => s2 | 3 => s3 | 4 => s4 | 5 => s5
  | 6 => s6 | 7 => s7 | 8 => s8 | 9 => s9 | _ => s10

def events : Nat → Ev
  | 0 => .command (.insert 0 owner)
  | 1 => .lifecycle .begin 0
  | 2 => .lifecycle .finish 0
  | 3 => .command (.retire 0)
  | 4 => .lifecycle .leave 0
  | 5 => .lifecycle .unload 0
  | 6 => .command (.remove 1)
  | 7 => .command (.insert 1 provider)
  | 8 => .lifecycle .begin 1
  | _ => .lifecycle .finish 1

private theorem s6_row (name : Nat) : s6 name =
    if name = 0 then some { (fresh owner none : F) with retired := true }
    else if name = 1 then some { (fresh provider (some 0) : F) with retired := true } else none := by
  by_cases atOwner : name = 0
  · subst name; rfl
  by_cases atChild : name = 1
  · subst name; rfl
  simp [s6, s5, s4, s3, s2, s1, empty, mark, Calculus.modify, retire, put, atOwner, atChild]

private theorem remove_child : Removable s6 1 := by
  rw [Removable, s6_row]
  refine ⟨rfl, rfl, fun _ => rfl, ?_⟩
  intro name
  rw [s6_row]
  by_cases atOwner : name = 0
  · subst name; simp [fresh]
  by_cases atChild : name = 1
  · subst name; simp [fresh]
  simp [atOwner, atChild]

private theorem insert_replacement : Insertable s7 1 provider none := by
  refine ⟨rfl, by simp, ?_⟩
  intro name key
  cases key
  by_cases selected : name = 1
  · subst name
    simp [s7, erase]
  · rw [s7, Transposition.erase_other _ _ _ selected, s6_row]
    by_cases atOwner : name = 0 <;> simp [atOwner, selected, fresh, owner, provider]

def trace : Trace program 10 where
  state := states
  notes := cutNotes states (fun time => eventActor (events time))
  event := events
  start := rfl
  seed := rfl
  step time bound := by
    have cuts : time = 0 ∨ time = 1 ∨ time = 2 ∨ time = 3 ∨ time = 4 ∨ time = 5 ∨
        time = 6 ∨ time = 7 ∨ time = 8 ∨ time = 9 := by omega
    rcases cuts with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨⟨⟨rfl, by simp, fun _ _ => trivial⟩, rfl⟩, rfl⟩
    · exact ⟨.begin s1 0 (fresh owner none) view rfl rfl (by change some _ ≠ none; simp)
        ⟨rfl, fun _ impossible => Bool.noConfusion impossible⟩, rfl⟩
    · have birth : Insertable s2 1 provider (some 0) := by
        refine ⟨rfl, ?_, ?_⟩
        · intro name parent
          cases parent
          change some _ ≠ none
          simp
        · intro name key
          by_cases atOwner : name = 0
          · subst name
            cases key
            change true = true → ¬ false = true
            simp
          · simp [s2, s1, empty, mark, Calculus.modify, put, atOwner]
      exact ⟨.finish s2 _ 0 { (fresh owner none : F) with phase := .reloading false [] view }
        false [] view (.retire 1) rfl rfl ⟨rfl, fun _ impossible => Bool.noConfusion impossible⟩
        (.instantiate s2 0 false provider 1 rfl birth), rfl⟩
    · exact ⟨⟨by change some _ ≠ none; simp, rfl⟩, rfl⟩
    · exact ⟨.leave s4 0 { (fresh owner none : F) with retired := true, phase := .active [.retire 1] view }
        [.retire 1] view rfl rfl (fun target => Bool.noConfusion target.1), rfl⟩
    · have lack : ¬ Relied s5 0 := by
        rintro ⟨name, different, claim⟩
        by_cases atChild : name = 1
        · subst name
          exact claim
        · simp [s5, s4, s3, s2, s1, empty, mark, retire, Calculus.modify, put, different, atChild] at claim
      exact ⟨⟨{ (fresh owner none : F) with retired := true, phase := .unloading [.retire 1] view },
        view, rfl, rfl, lack, rfl⟩, rfl⟩
    · exact ⟨⟨remove_child, rfl⟩, rfl⟩
    · exact ⟨⟨insert_replacement, rfl⟩, rfl⟩
    · exact ⟨.begin s8 1 (fresh provider none) view rfl rfl (by change some _ ≠ none; simp)
        ⟨rfl, fun _ impossible => Bool.noConfusion impossible⟩, rfl⟩
    · exact ⟨.finish s9 _ 1 { (fresh provider none : F) with phase := .reloading true [] view }
        true [] view (.restrict 1 ()) rfl rfl ⟨rfl, fun _ impossible => Bool.noConfusion impossible⟩
        (.provide s9 1 true _ () value rfl rfl rfl rfl), rfl⟩

def selected : ClosedEpisode trace where
  name := 0
  opened := 2
  closed := 5
  interval := ⟨by decide, by decide, by decide, installed, rfl, rfl⟩
where
  installed time (lower : 2 ≤ time) (upper : time ≤ 5) : ControlFrame.viewAt (trace.state time) 0 ≠ none := by
    have choices : time = 2 ∨ time = 3 ∨ time = 4 ∨ time = 5 := by omega
    rcases choices with rfl | rfl | rfl | rfl <;> exact Option.noConfusion

private theorem quiet : Progress.Quiet (trace.state 10) := by
  intro name row present
  by_cases atOwner : name = 0
  · subst name
    change some { (fresh owner none : F) with retired := true } = some row at present
    cases Option.some.inj present
    intro _ target
    exact Bool.noConfusion target.1
  by_cases atRoot : name = 1
  · subst name
    let root : F := { (fresh provider none : F) with
      table := fun _ => some value
      phase := .active [.restrict 1 ()] view }
    change some root = some row at present
    rw [← Option.some.inj present]
    exact ⟨rfl, fun _ impossible => Bool.noConfusion impossible⟩
  have absent : trace.state 10 name = none := by
    change s10 name = none
    simp [s10, s9, s8, s7, write, mark, Calculus.modify, put, erase, atRoot, s6_row, atOwner]
  rw [absent] at present
  cases present

private theorem selected_maximal (later : ClosedEpisode trace) : ¬ EpisodeEdge selected later := by
  intro edge
  have laterStarts := episode_edge_earlier edge
  change 2 < later.opened at laterStarts
  have ordered := later.interval.ordered
  have bound := later.interval.bounded
  obtain ⟨opens, _⟩ := begin_boundary trace later.interval
  change events (later.opened - 1) = .lifecycle .begin later.name at opens
  have cuts : later.opened - 1 = 2 ∨ later.opened - 1 = 3 ∨ later.opened - 1 = 4 ∨
      later.opened - 1 = 5 ∨ later.opened - 1 = 6 ∨ later.opened - 1 = 7 ∨ later.opened - 1 = 8 := by omega
  have start : later.opened - 1 = 8 := by
    rcases cuts with cut | cut | cut | cut | cut | cut | cut
    all_goals first | exact cut | simp [cut, events] at opens
  rw [start] at opens
  have name : later.name = 1 := by simpa [events] using opens.symm
  have ends : later.closed + 1 = 10 := by omega
  have gone := later.interval.after
  rw [ends, name] at gone
  cases gone

theorem guarded_excision : EpisodeExcised trace selected observe :=
  excise_closed_episode trace selected selected_maximal quiet observe (fun _ name => nomatch name)
    (fun _ name => nomatch name) (fun _ name => nomatch name)

/-- The child removal is deleted, and the root at that same name still
executes its insertion, activation, and real provision. -/
theorem replay_keeps_reused_name :
    excisedEvents trace selected [1] =
      [(1, events 0), (4, events 3), (8, events 7), (9, events 8), (10, events 9)] ∧
    originalRoots trace = [.insert 0 owner, .retire 0, .insert 1 provider] ∧
    StageRecovery.tableAt (trace.state 10) 1 () = some value :=
  ⟨rfl, rfl, rfl⟩

/-- The exact five stamped events returned by the repaired proof execute
from empty with the source root commands and a related final table. -/
theorem actual_replay :
  letI : Setoid (TypedRegistry.Scalar operations) := TypedCoeffectReplay.setoid observe
  ∃ final recorded,
    GuardedSuffix.Exec program
      [(1, events 0), (4, events 3), (8, events 7), (9, events 8), (10, events 9)]
      empty (trace.notes 0) final recorded [.insert 0 owner, .retire 0, .insert 1 provider] ∧
      StageRecovery.TablesRelated (trace.state 10) final := by
  obtain ⟨names, final, notes, unique, selectedNames, _, replayed, _, _, _, compared, _, _⟩ := guarded_excision
  have mask (name : Nat) : withdraws trace selected selected.closed name = true ↔ name = 1 := by
    change (IncarnationReplay.Capture.retires (trace.notes 5).1 name
      (⟨.retire 1, 3⟩ : IncarnationReplay.Capture Nat Unit (TypedRegistry.Scalar operations)) || false) = true ↔ _
    have live : (trace.notes 5).1 1 = some 3 := rfl
    simp [IncarnationReplay.Capture.retires, live]
  have member (name : Nat) : name ∈ names ↔ name = 1 := (selectedNames name).trans (mask name)
  have exactly : names = [1] := by
    cases names with
    | nil => exact False.elim (List.not_mem_nil ((member 1).mpr rfl))
    | cons head tail =>
      have first := (member head).mp List.mem_cons_self
      subst head
      have empty : tail = [] := by
        cases tail with
        | nil => rfl
        | cons other rest =>
          have same := (member other).mp (List.mem_cons_of_mem 1 List.mem_cons_self)
          subst other
          exact False.elim ((List.nodup_cons.mp unique).1 List.mem_cons_self)
      rw [empty]
  rw [exactly, replay_keeps_reused_name.1, replay_keeps_reused_name.2.1] at replayed
  exact ⟨final, notes, replayed.forgetSources, compared⟩

/-- Deleting the closed episode moves the surviving root retirement from
event stamp four to two. The retirement still addresses the first root. -/
theorem compacted_retirement_target :
    ∃ (length : Nat) (compact : Trace program length) (expand : Nat → Nat),
      RetainedEvents trace compact expand ∧ expand 2 = 4 ∧ compact.event 1 = .command (.retire 0) ∧
      targetAt compact 1 0 = some (.root 0, owner) := by
  obtain ⟨names, compact, expand, retained, eventsAt, _⟩ :=
    reindex_excision trace selected observe guarded_excision
  have valid : 1 < (excisedEvents trace selected names).length := by
    change 1 < ((1, events 0) :: (4, events 3) :: _).length
    simp
  have event : compact.event 1 = .command (.retire 0) := (eventsAt 1 valid).1
  have stamp : expand 2 = 4 := (eventsAt 1 valid).2
  obtain ⟨birth, newAddress, oldAddress, payload, newBirth, oldBirth, newTarget, oldTarget⟩ :=
    retained_command_target retained valid (Or.inl event)
  change targetAt trace (expand 2 - 1) 0 = some (oldAddress, payload) at oldTarget
  rw [stamp] at oldTarget
  have oldRoot : Addressed trace 1 (.root 0) := .root (time := 0) (by decide) rfl
  have oldKnown : targetAt trace 3 0 = some (.root 0, owner) :=
    (targetAt_eq_some trace).mpr ⟨1, _, rfl, oldRoot, rfl, rfl⟩
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (oldTarget.symm.trans oldKnown))
  have compactRoot : Addressed compact 1 (.root 0) := .root (time := 0) (by omega) (eventsAt 0 (by omega)).1
  have firstStamp : expand 1 = 1 := (eventsAt 0 (by omega)).2
  have birthEq : birth = 1 := retained.injective ((oldBirth.injective oldRoot rfl).trans firstStamp.symm)
  subst birth
  rw [newBirth.unique compactRoot] at newTarget
  exact ⟨_, compact, expand, retained, stamp, event, newTarget⟩

/-- The unchanged name-insensitive program can run with this bijection. The
renamed history records the first child's retirement at the same birth stamp
and the later root at its own distinct stamp. -/
theorem renamed_history_through_reuse :
    ∃ moved : Trace program 10,
      moved.event 5 = .lifecycle .unload 0 ∧
      moved.event 6 = .command (.remove 2) ∧
      (moved.notes 5).1 2 = some 3 ∧
      (moved.notes 5).2 0 = [⟨.retire 2, 3⟩] ∧
      (moved.notes 8).1 2 = some 8 ∧
      StageRecovery.tableAt (moved.state 10) 2 () = some value ∧
      Progress.Quiet (moved.state 10) := by
  let names := FreshNameTransport.swap (1 : Nat) 2
  have fixed : Renaming.program names program = program := by
    rw [← FreshNameTransport.encode_program, (FreshNameTransport.program_fixed_iff names entry).mpr]
    intro current child
    rfl
  let moved := GuardedRenaming.trace names trace
  have witnesses :
      ∃ replay : Trace (Renaming.program names program) 10,
        replay.event 5 = .lifecycle .unload 0 ∧
        replay.event 6 = .command (.remove 2) ∧
        (replay.notes 5).1 2 = some 3 ∧
        (replay.notes 5).2 0 = [⟨.retire 2, 3⟩] ∧
        (replay.notes 8).1 2 = some 8 ∧
        StageRecovery.tableAt (replay.state 10) 2 () = some value ∧
        Progress.Quiet (replay.state 10) :=
    ⟨moved, rfl, rfl, rfl, rfl, rfl, rfl, GuardedRenaming.quiet_transport names quiet⟩
  rwa [fixed] at witnesses

/-- The scoped Equation (54) comparison transfers the real provision of
the replacement root and re-establishes its stored function fields. -/
theorem scoped_comparison_transfers_provision :
    ∃ output recorded,
      GuardedSuffix.Step program (.lifecycle .finish 1) 10 s9 (trace.notes 9) output recorded ∧
      ∃ provided, StageRecovery.tableAt output 1 () = some provided ∧
        TypedCoeffectReplay.ValueRelated observe value provided := by
  letI : Setoid (TypedRegistry.Scalar operations) := TypedCoeffectReplay.setoid observe
  have recovery : PaperEffectEquations.ValueOperationWitness operations := fun _ name => nomatch name
  have respect : ∀ key, PaperObservationEquations.OperationRespects operations key (observe key).r := fun _ name => nomatch name
  have laws : ∀ key, PaperObservationEquations.CommutativeKey operations
      (PartialCoeffectIndependenceContracts.tableSetoid observe (fun _ => True)) key := fun _ name => nomatch name
  let lawful := MediatedAdmission.lawful_of_contracts operations observe recovery respect
  let meaning := TypedReplayContracts.coeffects operations observe entry recovery laws
  have terminal (code : Bool) (reply : Outcome Nat (TypedRegistry.Scalar operations)) : (program code).next reply = none := by
    change (TypedRegistry.decodeOutcome operations reply).bind (entry code).next = none
    cases TypedRegistry.decodeOutcome operations reply <;> rfl
  have ownerGrammar : GuardedIteratorProvenance.Mediated program owner owner.entry :=
    .birth false provider rfl (fun reply _ selected => by rw [terminal] at selected; cases selected)
  have providerGrammar : GuardedIteratorProvenance.Mediated program provider provider.entry :=
    .provision true () value rfl rfl (fun reply _ selected => by rw [terminal] at selected; cases selected)
  have absent (name : Nat) (notOwner : name ≠ 0) (notProvider : name ≠ 1) : s9 name = none := by
    simp [s9, s8, s7, mark, Calculus.modify, put, erase, s6_row, notOwner, notProvider]
  have entries : GuardedIteratorProvenance.Entries program s9 := by
    intro name row found
    by_cases own : name = 0
    · subst name
      cases Option.some.inj found
      exact ownerGrammar
    by_cases supplied : name = 1
    · subst name
      cases Option.some.inj found
      exact providerGrammar
    rw [absent name own supplied] at found
    cases found
  have remaining : GuardedIteratorProvenance.Remaining program s9 := by
    apply GuardedIteratorProvenance.Remaining.of_rows
    intro name row code word committed found phase
    by_cases own : name = 0
    · subst name
      cases Option.some.inj found
      cases phase
    by_cases supplied : name = 1
    · subst name
      cases Option.some.inj found
      cases phase
      exact providerGrammar
    rw [absent name own supplied] at found
    cases found
  have witnesses : StageRecovery.OperationWitnesses program := by
    intro code key callback action
    cases code <;> simp [TypedRegistry.encodeInstruction, TypedRegistry.encodeAction, entry] at action
  have source := trace.self_related 9 (by decide) witnesses
  have projects := trace.projects 9 (by decide)
  have annotations := EpisodeAnnotations.notesRelated_self source (trace.notes 9) projects
  have compared := ScopedEquation54.of_structural observe lawful meaning
    (ScopedReplayComparison.typed_decode_respects operations observe entry recovery laws)
    source annotations projects projects entries remaining
  have noBirth : GuardedIteratorProvenance.NewEntries program s9 s10 := by
    intro name row vacant found
    have same : s10 name = none := by
      rw [s10, Transposition.mark_presence]
      by_cases equal : name = 1
      · subst name
        simp [Stages.write, Calculus.modify, vacant]
      · simp [Stages.write, Calculus.modify, equal, vacant]
    rw [same] at found
    cases found
  obtain ⟨output, recorded, step, outputs, _, _⟩ :=
    (ScopedEquation54.lemma60_scoped observe recovery laws respect trace trace (time := 9) (by decide) (by decide) compared).1
      (.lifecycle .finish 1) s10 (trace.notes 10) (trace.step 9 (by decide)) noBirth
  have tables := outputs.controls.tables 1 ()
  change Iterators.OptionRel (TypedCoeffectReplay.ValueRelated observe) (some value) (StageRecovery.tableAt output 1 ()) at tables
  cases cell : StageRecovery.tableAt output 1 () with
  | none => simp [cell, Iterators.OptionRel] at tables
  | some provided => exact ⟨output, recorded, step, provided, cell, by simpa only [cell, Iterators.OptionRel] using tables⟩

end Cordis.Repairs.GuardedEpisodeExample
