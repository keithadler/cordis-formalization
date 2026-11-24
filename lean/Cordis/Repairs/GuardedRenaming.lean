import Cordis.Repairs.GuardedOpenProvenance
import Cordis.Repairs.ReplayTransport

/-! Name transport for actual guarded histories, including the corrected
unload and the notes that identify the incarnation each command targets. -/
namespace Cordis.Repairs.GuardedRenaming
open Calculus Stages LegalHistory GuardedHistory IncarnationReplay
open Vestigial (CutNotes noteStep eventActor)
open OrchestrationSorting (Command)
universe u
variable {Name Key Value Code Error : Type u}
local notation "P" => Renaming.Permutation Name
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "Notes" => CutNotes Name Key Value
local notation "C" => Capture Name Key Value
local notation "Cmd" => Command Name Key Code
local notation "Ev" => Event Name Key Code
local notation "Program" => Code → Instruction Name Key Value Code Error
variable {program : Code → Instruction Name Key Value Code Error} {last : Nat}

def command (p : P) : Cmd → Cmd
  | .insert name component => .insert (p.toFun name) component
  | .retire name => .retire (p.toFun name)
  | .remove name => .remove (p.toFun name)

def event (p : P) : Ev → Ev
  | .command cmd => .command (command p cmd)
  | .lifecycle kind actor => .lifecycle kind (p.toFun actor)

def notes (p : P) (original : Notes) : Notes :=
  (fun name => original.1 (p.invFun name),
   fun name => (original.2 (p.invFun name)).map (Capture.transport p id))

@[simp] theorem note_birth (p : P) (original : Notes) (name : Name) :
    (notes p original).1 (p.toFun name) = original.1 name := by simp [notes]

@[simp] theorem note_stack (p : P) (original : Notes) (name : Name) :
    (notes p original).2 (p.toFun name) = (original.2 name).map (Capture.transport p id) := by simp [notes]

@[simp] theorem actor_event (p : P) (original : Ev) :
    eventActor (event p original) = p.toFun (eventActor original) := by
  cases original with
  | lifecycle => rfl
  | command cmd => cases cmd <;> rfl

@[simp] theorem event_symm (p : P) (original : Ev) : event p.symm (event p original) = original := by
  cases original with
  | lifecycle => simp [event, Renaming.Permutation.symm]
  | command cmd => cases cmd <;> simp [event, command, Renaming.Permutation.symm]

@[simp] theorem notes_symm (p : P) (original : Notes) : notes p.symm (notes p original) = original := by
  apply Prod.ext
  · funext name
    simp [notes, Renaming.Permutation.symm]
  · funext name
    have captureBack (captured : C) : Capture.transport p.symm id (Capture.transport p id captured) = captured := by
      cases captured
      simp [Capture.transport]
    change ((original.2 (p.invFun (p.toFun name))).map (Capture.transport p id)).map
      (Capture.transport p.symm id) = original.2 name
    rw [p.left_inv, List.map_map]
    simp [Function.comp_def, captureBack]

variable [DecidableEq Name] [DecidableEq Key]

omit [DecidableEq Key] in

theorem noteStep_transport (p : P) (before after : R) (actor : Name) (stamp : Nat) (old : Notes) :
    noteStep (Renaming.registry p before) (Renaming.registry p after) (p.toFun actor) stamp (notes p old) =
      notes p (noteStep before after actor stamp old) := by
  apply Prod.ext
  · funext name
    obtain ⟨original, rfl⟩ := p.surjective name
    change ((Renaming.registry p after) (p.toFun original)).map
      (fun _ => ((notes p old).1 (p.toFun original)).getD stamp) = _
    rw [Renaming.registry_at, note_birth, note_birth]
    cases present : after original <;> simp [noteStep, present]
  · funext name
    obtain ⟨original, rfl⟩ := p.surjective name
    exact (advance_renamed p before after actor original stamp old.2 (notes p old).2
      (note_stack p old)).trans (note_stack p (noteStep before after actor stamp old) original).symm

omit [DecidableEq Key] in
theorem command_step (p : P) (cmd : Cmd) {before after : R} (step : cmd.Step before after) :
    (command p cmd).Step (Renaming.registry p before) (Renaming.registry p after) := by
  obtain ⟨ready, rfl⟩ := step
  cases cmd with
  | insert name component =>
    refine ⟨Renaming.insertable_map p before name component none ready, ?_⟩
    simp only [Command.apply, command, Renaming.put_eq, Renaming.fresh_fiber, Option.map_none]
  | retire name =>
    exact ⟨by simpa [command, Command.Enabled] using ready, Renaming.retire_eq p before name⟩
  | remove name =>
    exact ⟨Renaming.removable_map p before name ready, Renaming.erase_eq p before name⟩

theorem unload_transport (p : P) {actor : Name} {before after : R} {old : Notes}
    (step : GuardedSuffix.Unload actor before old after) :
    GuardedSuffix.Unload (p.toFun actor) (Renaming.registry p before) (notes p old)
      (Renaming.registry p after) := by
  obtain ⟨row, view, present, phase, free, rfl⟩ := step
  refine ⟨Renaming.fiber p row, Renaming.view p view, by simp [present], ?_,
    fun used => free ((Renaming.relied_iff p before actor).mp used), ?_⟩
  · simp only [Renaming.fiber, phase, Renaming.phase, note_stack, List.map_map]
    rfl
  · rw [Renaming.mark_eq, note_stack]
    change mark (Renaming.registry p (replay old.1 (old.2 actor) before)) (p.toFun actor) .inactive =
      mark (replay (notes p old).1 ((old.2 actor).map (Capture.transport p id))
        (Renaming.registry p before)) (p.toFun actor) .inactive
    have aligned (name : Name) : (notes p old).1 (p.toFun name) = (old.1 name).map id := by simp
    rw [replay_transport p (birth := id) (fun _ _ same => same) aligned]

private theorem transition_transport_with (p : P) {other : Program}
    (ordinary : ∀ {rule actor before after}, Labeled.Step program rule actor before after →
      Labeled.Step other rule (p.toFun actor) (Renaming.registry p before) (Renaming.registry p after))
    {original : Ev} {before after : R} {old : Notes}
    (step : GuardedSuffix.Transition program old original before after) :
    GuardedSuffix.Transition other (notes p old) (event p original)
      (Renaming.registry p before) (Renaming.registry p after) := by
  cases original with
  | command cmd => exact command_step p cmd step
  | lifecycle kind actor =>
    cases kind
    case unload => exact unload_transport p step
    all_goals exact ordinary step

theorem transition_transport (p : P) {original : Ev} {before after : R} {old : Notes}
    (step : GuardedSuffix.Transition program old original before after) :
    GuardedSuffix.Transition (Renaming.program p program) (notes p old) (event p original)
      (Renaming.registry p before) (Renaming.registry p after) :=
  transition_transport_with p (Renaming.labeled_step_map p) step

theorem transition_transport_same (p : P) (stable : Renaming.PreservesChildBranches p program)
    {original : Ev} {before after : R} {old : Notes}
    (step : GuardedSuffix.Transition program old original before after) :
    GuardedSuffix.Transition program (notes p old) (event p original)
      (Renaming.registry p before) (Renaming.registry p after) :=
  transition_transport_with p (Renaming.labeled_step_map_same p stable) step

private theorem step_transport_with (p : P) {other : Program}
    (transport : ∀ {original before after old}, GuardedSuffix.Transition program old original before after →
      GuardedSuffix.Transition other (notes p old) (event p original)
        (Renaming.registry p before) (Renaming.registry p after))
    {original : Ev} {before after : R} {old recorded : Notes} {stamp : Nat}
    (step : GuardedSuffix.Step program original stamp before old after recorded) :
    GuardedSuffix.Step other (event p original) stamp
      (Renaming.registry p before) (notes p old) (Renaming.registry p after) (notes p recorded) := by
  obtain ⟨actual, recorded⟩ := step
  refine ⟨transport actual, ?_⟩
  rw [actor_event, recorded]
  exact (noteStep_transport p _ _ _ _ _).symm

theorem step_equivariant (p : P) {original : Ev} {before after : R} {old recorded : Notes} {stamp : Nat} :
    GuardedSuffix.Step program original stamp before old after recorded ↔
      GuardedSuffix.Step (Renaming.program p program) (event p original) stamp
        (Renaming.registry p before) (notes p old) (Renaming.registry p after) (notes p recorded) := by
  constructor
  · exact step_transport_with p (transition_transport p)
  · intro step
    simpa only [event_symm, notes_symm, Renaming.registry_symm, Renaming.program_symm] using
      step_transport_with p.symm (transition_transport p.symm) step

theorem step_equivariant_same (p : P) (stable : Renaming.PreservesChildBranches p program)
    {original : Ev} {before after : R} {old recorded : Notes} {stamp : Nat} :
    GuardedSuffix.Step program original stamp before old after recorded ↔
      GuardedSuffix.Step program (event p original) stamp
        (Renaming.registry p before) (notes p old) (Renaming.registry p after) (notes p recorded) := by
  constructor
  · exact step_transport_with p (transition_transport_same p stable)
  · intro step
    simpa only [event_symm, notes_symm, Renaming.registry_symm] using
      step_transport_with p.symm (transition_transport_same p.symm stable.symm) step

omit [DecidableEq Name] [DecidableEq Key] in
theorem quiet_transport (p : P) {state : R} (quiet : Progress.Quiet state) :
    Progress.Quiet (Renaming.registry p state) := by
  intro name renamed present
  obtain ⟨original, rfl⟩ := p.surjective name
  rw [Renaming.registry_at] at present
  cases found : state original with
  | none => simp [found] at present
  | some row =>
    have same : Renaming.fiber p row = renamed := Option.some.inj (by simpa only [found, Option.map_some] using present)
    subst renamed
    have source := quiet original row found
    cases phase : row.phase <;> simp only [Renaming.fiber, phase, Renaming.phase] <;>
      simp only [phase] at source
    case inactive =>
      intro view valid
      have roundTrip : Renaming.view p (Renaming.view p.symm view) = view := Renaming.view_symm p.symm view
      have mapped : Target (Renaming.registry p state) (p.toFun original)
          (Renaming.view p (Renaming.view p.symm view)) := by
        rw [roundTrip]
        exact valid
      exact source _ ((Renaming.target_iff p state original _).mp mapped)
    case active => exact (Renaming.target_iff p state original _).mpr source
    all_goals exact source

/-- The renamed trace records the same birth stamps and carries each command
target through the name bijection. -/
def trace (p : P) (original : Trace program last) : Trace (Renaming.program p program) last where
  state time := Renaming.registry p (original.state time)
  notes time := notes p (original.notes time)
  event time := event p (original.event time)
  start := by rw [original.start]; rfl
  seed := by rw [original.seed]; rfl
  step time bounded := (step_equivariant p).mp (original.step time bounded)

/-- Under branch agreement, the renamed history runs the original program. -/
def trace_same (p : P) (stable : Renaming.PreservesChildBranches p program) (original : Trace program last) :
    Trace program last where
  state time := Renaming.registry p (original.state time)
  notes time := notes p (original.notes time)
  event time := event p (original.event time)
  start := (trace p original).start
  seed := (trace p original).seed
  step time bounded := (step_equivariant_same p stable).mp (original.step time bounded)

theorem root_commands (p : P) (original : Trace program last) :
    originalRoots (trace p original) = (originalRoots original).map (command p) := by
  unfold originalRoots
  rw [List.map_flatMap]
  congr 1
  funext time
  change eventRoots (Renaming.registry p (original.state time)) (event p (original.event time)) =
    (eventRoots (original.state time) (original.event time)).map (command p)
  have root (name : Name) : rootAt (Renaming.registry p (original.state time)) (p.toFun name) =
      rootAt (original.state time) name := by
    unfold rootAt
    rw [Renaming.registry_at]
    cases original.state time name <;> simp [Renaming.fiber]
  cases original.event time with
  | lifecycle => rfl
  | command cmd =>
    cases cmd <;> simp [event, command, eventRoots, commandRoots, root] <;> split <;> rfl

end Cordis.Repairs.GuardedRenaming
