import Cordis.Repairs.ReplayTransport
import Cordis.Repairs.HistoryProvenance
import Cordis.TranspositionPhases

/-! Births and saved inverse words through actual adjacent exchanges. -/
namespace Cordis.Repairs.ExchangeReplay
open Calculus Stages
open Incarnation IncarnationReplay
open LegalHistory (commandRoots commandRoots_same_row rootAt_lifecycle)
open PartialReplayRegistry (saved)
open OrchestrationSorting (Command)
universe u
variable {Name Key Value Code Error : Type u}
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "C" => Capture Name Key Value
local notation "Cmd" => Command Name Key Code
local notation "Program" => Code → Instruction Name Key Value Code Error

/-- The two post-step indices move with their events. -/
def exchangedIndex (point index : Nat) : Nat :=
  if index = point + 1 then point + 2 else if index = point + 2 then point + 1 else index

@[simp] theorem exchangedIndex_first (point : Nat) : exchangedIndex point (point + 1) = point + 2 := by
  simp [exchangedIndex]

@[simp] theorem exchangedIndex_second (point : Nat) : exchangedIndex point (point + 2) = point + 1 := by
  simp [exchangedIndex]

theorem exchangedIndex_other {point index : Nat} (first : index ≠ point + 1) (second : index ≠ point + 2) :
    exchangedIndex point index = index := by simp [exchangedIndex, first, second]

theorem exchangedIndex_involutive (point index : Nat) :
    exchangedIndex point (exchangedIndex point index) = index := by
  by_cases first : index = point + 1
  · simp [first]
  · by_cases second : index = point + 2
    · simp [second]
    · rw [exchangedIndex_other first second, exchangedIndex_other first second]

theorem exchangedIndex_injective (point : Nat) : Function.Injective (exchangedIndex point) := by
  intro a b same
  have moved := congrArg (exchangedIndex point) same
  simpa [exchangedIndex_involutive] using moved

/-- The source cuts of the two exchanged events. `exchangedIndex` acts on
their post-event stamps. -/
def exchangedCut (point cut : Nat) : Nat :=
  if cut = point then point + 1 else if cut = point + 1 then point else cut

theorem exchanged_stamp (point cut : Nat) : exchangedIndex point (cut + 1) = exchangedCut point cut + 1 := by
  by_cases first : cut = point
  · subst cut; simp [exchangedCut]
  by_cases second : cut = point + 1
  · subst cut; simp [exchangedCut]
  · rw [exchangedIndex_other (by omega) (by omega)]
    simp [exchangedCut, first, second]

private theorem birthAt_next (states : Nat → R) (name : Name) (time : Nat) :
    birthAt states name (time + 1) =
      if (states (time + 1) name).isNone then none
      else some ((birthAt states name time).getD (time + 1)) := by
  cases found : states (time + 1) name <;> simp [birthAt, found]

private theorem birthAt_pair {source moved : Nat → R} {point : Nat} (name : Name)
    (earlier : birthAt moved name point = birthAt source name point)
    (sameFinal : moved (point + 2) name = none ↔ source (point + 2) name = none)
    (changesFirst : (source (point + 1) name = none ↔ source (point + 2) name = none) ∧
        (moved (point + 1) name = none ↔ source point name = none) ∨
      (moved (point + 1) name = none ↔ source (point + 2) name = none) ∧
        (source (point + 1) name = none ↔ source point name = none)) :
    birthAt moved name (point + 2) = (birthAt source name (point + 2)).map (exchangedIndex point) := by
  have atSource := birthAt_next source name (point + 1)
  have atMoved := birthAt_next moved name (point + 1)
  rw [atSource, atMoved, birthAt_next source name, birthAt_next moved name, earlier]
  by_cases final : source (point + 2) name = none
  · simp [sameFinal, final]
  · cases born : birthAt source name point with
    | none =>
      have absent := birthAt_none.mp born
      rcases changesFirst with ⟨inSource, inMoved⟩ | ⟨inMoved, inSource⟩ <;>
        simp [sameFinal, final, inSource, inMoved, absent]
    | some birth =>
      have present : source point name ≠ none := fun gone => by
        rw [birthAt_none.mpr gone] at born
        cases born
      have bounded := (resident_of_birthAt born).ordered
      have stays : exchangedIndex point birth = birth :=
        exchangedIndex_other (by omega) (by omega)
      rcases changesFirst with ⟨inSource, inMoved⟩ | ⟨inMoved, inSource⟩ <;>
        simp [sameFinal, final, inSource, inMoved, present, stays]

variable [DecidableEq Name] [DecidableEq Key]

omit [DecidableEq Key] in
private theorem command_saved (command : Cmd) {before after : R} (step : command.Step before after) :
    saved after = saved before := by
  obtain ⟨ready, rfl⟩ := step
  funext name
  by_cases same : name = command.actor
  · subst name
    cases command with
    | insert name payload =>
      have missing : before name = none := ready.1
      simp [Command.apply, Command.actor, put_self, saved, missing, fresh, Phase.accumulator]
    | retire name =>
      rcases found : before name with _ | entry <;>
        simp [Command.apply, Command.actor, Calculus.retire, Calculus.modify, saved, found]
    | remove name =>
      rcases found : before name with _ | entry
      · simp [Command.Enabled, Removable, found] at ready
      · simp only [Command.Enabled, Removable, found] at ready
        simp [Command.apply, Command.actor, erase, saved, found, ready.2.1, Phase.accumulator]
  · unfold saved
    rw [CausalCommands.apply_other command before name same]

private theorem command_track {program : Program} {last : Nat}
    (trace : Indexed.Trace program (fun _ => none) last) {time : Nat} (bounded : time < last)
    {command : Cmd} (step : command.Step (trace.state time) (trace.state (time + 1))) :
    track trace.state trace.actor (time + 1) = track trace.state trace.actor time := by
  exact advance_control _ _ _ (tracked_stack trace time (by omega)).projects (command_saved command step)

def commandRule : Cmd → Labeled.Rule
  | .insert .. => .insert
  | .retire _ => .retire
  | .remove _ => .remove

theorem command_labeled {program : Program} (command : Cmd) {before after : R}
    (step : command.Step before after) :
    Labeled.Step program (commandRule command) command.actor before after := by
  obtain ⟨ready, rfl⟩ := step
  cases command with
  | insert name component => exact .insert _ name component none ready
  | retire name => exact .retire _ name ready
  | remove name => exact .remove _ name ready

private def replacePair {program : Program} {initial : R} {last : Nat}
    (source : Indexed.Trace program initial last) (point : Nat)
    (middle : R) {firstRule secondRule : Labeled.Rule} {firstActor secondActor : Name}
    (first : Labeled.Step program firstRule firstActor (source.state point) middle)
    (second : Labeled.Step program secondRule secondActor middle (source.state (point + 2))) :
    Indexed.Trace program initial last where
  state index := if index = point + 1 then middle else source.state index
  rule index := if index = point then firstRule else if index = point + 1 then secondRule else source.rule index
  actor index := if index = point then firstActor else if index = point + 1 then secondActor else source.actor index
  start := by simpa using source.start
  step index valid := by
    by_cases one : index = point
    · subst index
      simpa using first
    · by_cases two : index = point + 1
      · subst index
        simpa using second
      · have finish : index + 1 ≠ point + 1 := by omega
        simpa [one, two, finish] using source.step index valid

private theorem common_prefix {program : Program} {initial : R} {last : Nat}
    (source moved : Indexed.Trace program initial last) {point time : Nat} (before : time ≤ point)
    (state : ∀ index, index ≤ point → moved.state index = source.state index)
    (actor : ∀ index, index < point → moved.actor index = source.actor index) :
    (∀ name, birthAt moved.state name time = birthAt source.state name time) ∧
      track moved.state moved.actor time = track source.state source.actor time := by
  induction time with
  | zero =>
    exact ⟨fun name => by simp [birthAt, state 0 (by omega)], rfl⟩
  | succ time ih =>
    obtain ⟨births, words⟩ := ih (by omega)
    constructor
    · intro name
      simp only [birthAt, state (time + 1) before, births]
    · simp only [track, words, state time (by omega), state (time + 1) before, actor time (by omega)]

private theorem annotate_eq_before {program : Program} {last point : Nat}
    (source : Indexed.Trace program (fun _ => none) last) (bounded : point ≤ last)
    (name : Name) :
    (track source.state source.actor point name).map (Capture.reindex (exchangedIndex point)) =
      track source.state source.actor point name := by
  apply List.map_congr_left (g := id) ?_ |>.trans (List.map_id _)
  intro entry member
  have within := ((tracked_stack source point bounded).origins name entry member).1
  unfold Capture.reindex
  rw [exchangedIndex_other (by omega) (by omega)]
  cases entry
  rfl

private theorem common_suffix {program : Program} {initial : R} {last point : Nat}
    (source moved : Indexed.Trace program initial last)
    (state : ∀ index, point + 2 ≤ index → moved.state index = source.state index)
    (actor : ∀ index, point + 2 ≤ index → moved.actor index = source.actor index)
    (baseBirths : ∀ name, birthAt moved.state name (point + 2) =
      (birthAt source.state name (point + 2)).map (exchangedIndex point))
    (baseWords : ∀ name, track moved.state moved.actor (point + 2) name =
      (track source.state source.actor (point + 2) name).map (Capture.reindex (exchangedIndex point))) :
    ∀ time, point + 2 ≤ time →
      (∀ name, birthAt moved.state name time = (birthAt source.state name time).map (exchangedIndex point)) ∧
        ∀ name, track moved.state moved.actor time name =
          (track source.state source.actor time name).map (Capture.reindex (exchangedIndex point)) := by
  intro time afterPair
  induction time with
  | zero => omega
  | succ time ih =>
    by_cases atPair : time + 1 = point + 2
    · simpa only [atPair] using And.intro baseBirths baseWords
    have later : point + 2 ≤ time := by omega
    obtain ⟨births, words⟩ := ih later
    have fixed : exchangedIndex point (time + 1) = time + 1 :=
      exchangedIndex_other (by omega) (by omega)
    constructor
    · intro name
      rw [birthAt_next moved.state, birthAt_next source.state, state _ afterPair, births]
      cases born : birthAt source.state name time <;> split <;> simp [fixed]
    · intro name
      have adjusted := advance_annotate (exchangedIndex point)
        (time := time + 1) (actor := source.actor time) words
        (congrArg (fun r => saved r (source.actor time)) (state _ later))
        (congrArg (fun r => saved r (source.actor time)) (state _ afterPair)) name
      simpa only [track, actor _ later, fixed] using adjusted

private theorem activation_presence {program : Program} {rule : Labeled.Rule} {actor : Name}
    {before after : R} (step : Labeled.Step program rule actor before after)
    (activation : Transposition.Activation rule) (name : Name)
    (notCreated : before name = none → after name = none) :
    after name = none ↔ before name = none := by
  refine ⟨?_, notCreated⟩
  intro missing
  cases original : before name with
  | none => rfl
  | some entry =>
    cases step with
    | begin => simp [Transposition.mark_presence, original] at missing
    | iter _ _ _ _ _ _ _ _ _ _ _ _ landed
    | finish _ _ _ _ _ _ _ _ _ _ _ landed =>
      obtain ⟨later, found, _, _⟩ := Ordering.land_existing_control program landed name entry original
      simp [Transposition.mark_presence, found] at missing
    | _ => simp [Transposition.Activation] at activation

omit [DecidableEq Key] in
private theorem command_presence {command : Cmd} {before after : R} (step : command.Step before after)
    (name : Name) (different : name ≠ command.actor) :
    after name = none ↔ before name = none := by
  rw [step.2, CausalCommands.apply_other _ _ _ different]

private theorem command_presence_congr (command : Cmd) {before middle : R}
    (unchanged : middle command.actor = none ↔ before command.actor = none) :
    command.apply before command.actor = none ↔ command.apply middle command.actor = none := by
  cases command with
  | insert => simp [Command.apply, Command.actor, put_self]
  | remove => simp [Command.apply, Command.actor, erase]
  | retire name =>
    change Calculus.retire before name name = none ↔ Calculus.retire middle name name = none
    rw [Transposition.retire_presence, Transposition.retire_presence]
    exact unchanged.symm

/-- Beyond the exchanged pair, registry data agrees literally. Incarnation
and capture indices follow their events through the exchange. -/
structure Exchange {program : Program} {last : Nat}
    (source moved : Indexed.Trace program (fun _ => none) last) (point : Nat) (command : Cmd) : Prop where
  original : source.rule (point + 1) = commandRule command ∧ source.actor (point + 1) = command.actor
  first : moved.rule point = commandRule command ∧ moved.actor point = command.actor
  second : moved.rule (point + 1) = source.rule point ∧ moved.actor (point + 1) = source.actor point
  middle : moved.state (point + 1) = command.apply (source.state point)
  state : ∀ time, time ≠ point + 1 → moved.state time = source.state time
  label : ∀ time, time ≠ point → time ≠ point + 1 →
    moved.rule time = source.rule time ∧ moved.actor time = source.actor time
  root : commandRoots (moved.state point) command = commandRoots (source.state (point + 1)) command
  birth : ∀ time, point + 2 ≤ time → ∀ name, birthAt moved.state name time =
    (birthAt source.state name time).map (exchangedIndex point)
  word : ∀ time, point + 2 ≤ time → ∀ name, track moved.state moved.actor time name =
    (track source.state source.actor time name).map (Capture.reindex (exchangedIndex point))
  commandStep : command.Step (moved.state point) (moved.state (point + 1))

theorem Exchange.replayAt {program : Program} {last point : Nat} {command : Cmd}
    {source moved : Indexed.Trace program (fun _ => none) last}
    (exchange : Exchange source moved point command) (time : Nat) (later : point + 2 ≤ time)
    (name : Name) :
    IncarnationReplay.replayAt moved.state time (track moved.state moved.actor time name) =
      IncarnationReplay.replayAt source.state time (track source.state source.actor time name) := by
  unfold IncarnationReplay.replayAt
  rw [exchange.word time later, exchange.state time (by omega)]
  exact replay_reindex (exchangedIndex_injective point) (exchange.birth time later) _ _

/-- The root-command subsequence is unchanged when at least one of the
two commands acts on a child. Classification comes from each step's source. -/
theorem Exchange.commandPair_roots {program : Program} {last point : Nat} {first second : Cmd}
    {source moved : Indexed.Trace program (fun _ => none) last}
    (exchange : Exchange source moved point second) (different : first.actor ≠ second.actor)
    (oneChild : commandRoots (source.state point) first = [] ∨
      commandRoots (source.state (point + 1)) second = []) :
    commandRoots (moved.state point) second ++ commandRoots (moved.state (point + 1)) first =
      commandRoots (source.state point) first ++ commandRoots (source.state (point + 1)) second := by
  have firstRoot : commandRoots (moved.state (point + 1)) first = commandRoots (source.state point) first := by
    apply commandRoots_same_row
    rw [exchange.middle, CausalCommands.apply_other _ _ _ different]
  rw [exchange.root, firstRoot]
  rcases oneChild with child | child <;> simp [child]

private theorem exchange_with_command {program : Program} {last point : Nat}
    (source : Indexed.Trace program (fun _ => none) last) (bounded : point + 1 < last)
    (command : Cmd)
    (external : source.rule (point + 1) = commandRule command ∧ source.actor (point + 1) = command.actor)
    (late : command.Step (source.state (point + 1)) (source.state (point + 2)))
    (early : command.Enabled (source.state point))
    (swapped : Labeled.Step program (source.rule point) (source.actor point)
      (command.apply (source.state point)) (source.state (point + 2)))
    (commandRow : source.state (point + 1) command.actor = none ↔ source.state point command.actor = none)
    (root : commandRoots (source.state point) command = commandRoots (source.state (point + 1)) command) :
    ∃ moved, Exchange source moved point command := by
  let mid := command.apply (source.state point)
  have earlyStep : command.Step (source.state point) mid := ⟨early, rfl⟩
  let moved := replacePair source point mid (command_labeled command earlyStep) swapped
  have beforeRows (index : Nat) (earlier : index ≤ point) : moved.state index = source.state index := by
    have different : index ≠ point + 1 := by omega
    simp [moved, replacePair, different]
  have afterRows (index : Nat) (later : point + 2 ≤ index) : moved.state index = source.state index := by
    have different : index ≠ point + 1 := by omega
    simp [moved, replacePair, different]
  have beforeActors (index : Nat) (earlier : index < point) : moved.actor index = source.actor index := by
    have current : index ≠ point := by omega
    have next : index ≠ point + 1 := by omega
    simp [moved, replacePair, current, next]
  have afterActors (index : Nat) (later : point + 2 ≤ index) : moved.actor index = source.actor index := by
    have current : index ≠ point := by omega
    have next : index ≠ point + 1 := by omega
    simp [moved, replacePair, current, next]
  have midRow : moved.state (point + 1) = mid := by simp [moved, replacePair]
  have newActor : moved.actor (point + 1) = source.actor point := by simp [moved, replacePair]
  obtain ⟨earlierBorn, earlierWords⟩ := common_prefix source moved (point := point) (time := point)
    (Nat.le_refl _) beforeRows beforeActors
  have reused : ∀ name, track moved.state moved.actor point name =
      (track source.state source.actor point name).map (Capture.reindex (exchangedIndex point)) := by
    intro name
    rw [earlierWords, annotate_eq_before source (by omega)]
  have matchedBirths (name : Name) :
      birthAt moved.state name (point + 2) =
        (birthAt source.state name (point + 2)).map (exchangedIndex point) := by
    refine birthAt_pair name (earlierBorn name) (by rw [afterRows _ (by omega)]) ?_
    rw [midRow]
    by_cases atCommand : name = command.actor
    · subst name
      right
      exact ⟨by rw [late.2]; exact command_presence_congr command commandRow, commandRow⟩
    · left
      exact ⟨(command_presence late name atCommand).symm, command_presence earlyStep name atCommand⟩
  have skipsNew : track moved.state moved.actor (point + 1) = track moved.state moved.actor point := by
    apply command_track moved (by omega)
    rw [beforeRows _ (by omega), midRow]
    exact earlyStep
  have skipsOld : track source.state source.actor (point + 2) = track source.state source.actor (point + 1) :=
    command_track source bounded late
  have matchedWords (name : Name) :
      track moved.state moved.actor (point + 2) name =
        (track source.state source.actor (point + 2) name).map (Capture.reindex (exchangedIndex point)) := by
    have applied := advance_annotate (exchangedIndex point) (actor := source.actor point)
      (time := point + 1) reused (congrFun (command_saved command earlyStep) (source.actor point))
      (congrFun (command_saved command late) (source.actor point)) name
    rw [skipsOld]
    simp only [exchangedIndex_first] at applied
    change advance (moved.state (point + 1)) (moved.state (point + 2)) (moved.actor (point + 1))
      (point + 2) (track moved.state moved.actor (point + 1)) name = _
    rw [newActor, midRow, afterRows _ (Nat.le_refl _), skipsNew]
    exact applied
  have suffix := common_suffix source moved afterRows afterActors matchedBirths matchedWords
  refine ⟨moved, ⟨external, ?_, ?_, midRow, ?_, ?_, (congrArg (fun r => commandRoots r command)
      (beforeRows point (Nat.le_refl _))).trans root,
    fun time later => (suffix time later).1, fun time later => (suffix time later).2, ?_⟩⟩
  · simp [moved, replacePair]
  · exact ⟨by simp [moved, replacePair], newActor⟩
  · intro time different
    simp [moved, replacePair, different]
  · intro time first second
    simp [moved, replacePair, first, second]
  · rw [beforeRows point (Nat.le_refl _), midRow]
    exact earlyStep

/-- Lemma 78(2) with the continuation, saved word, and child incarnation
carried through the adjacent exchange. The actual rule supplies the first
event, including the fresh name or operation result that it selected. -/
theorem activation_command {program : Program} {last point : Nat}
    (source : Indexed.Trace program (fun _ => none) last) (bounded : point + 1 < last)
    (command : Cmd) (activation : Transposition.Activation (source.rule point))
    (external : source.rule (point + 1) = commandRule command ∧ source.actor (point + 1) = command.actor)
    (late : command.Step (source.state (point + 1)) (source.state (point + 2)))
    (different : source.actor point ≠ command.actor)
    (notCreated : source.state point command.actor = none → source.state (point + 1) command.actor = none) :
    ∃ moved, Exchange source moved point command := by
  have step := source.step point (by omega)
  obtain ⟨early, swapped⟩ := OrchestrationSorting.activation_command_diamond program command
    step activation late.1 different notCreated
  rw [← late.2] at swapped
  have root : commandRoots (source.state point) command =
      commandRoots (source.state (point + 1)) command := by
    have stable := by
      show ∀ name, LegalHistory.rootAt (source.state (point + 1)) name =
        LegalHistory.rootAt (source.state point) name
      rcases activation with beginRule | iterRule | finishRule
      · exact rootAt_lifecycle .begin (beginRule ▸ step)
      · exact rootAt_lifecycle .iter (iterRule ▸ step)
      · exact rootAt_lifecycle .finish (finishRule ▸ step)
    cases command <;> simp [commandRoots, stable]
  exact exchange_with_command source bounded command external late early swapped
    (activation_presence step activation command.actor notCreated) root

/-- The corresponding result for two orchestration steps. Applicability
before the exchange is checked by the native command diamond. -/
theorem commands {program : Program} {last point : Nat}
    (source : Indexed.Trace program (fun _ => none) last) (bounded : point + 1 < last)
    (first second : Cmd) (firstRule : source.rule point = commandRule first)
    (firstActor : source.actor point = first.actor)
    (external : source.rule (point + 1) = commandRule second ∧ source.actor (point + 1) = second.actor)
    (a : first.Step (source.state point) (source.state (point + 1)))
    (b : second.Step (source.state (point + 1)) (source.state (point + 2)))
    (different : first.actor ≠ second.actor) (enabled : second.Enabled (source.state point)) :
    ∃ moved, Exchange source moved point second := by
  obtain ⟨middle, earlier, later⟩ := CausalCommands.command_diamond first second a b different enabled
  have step : Labeled.Step program (source.rule point) (source.actor point) middle (source.state (point + 2)) := by
    rw [firstRule, firstActor]
    exact command_labeled first later
  rw [earlier.2] at step
  have same : source.state (point + 1) second.actor = source.state point second.actor := by
    rw [a.2, CausalCommands.apply_other _ _ _ (Ne.symm different)]
  exact exchange_with_command source bounded second external b enabled step
    (command_presence a second.actor (Ne.symm different)) (commandRoots_same_row second same.symm)

end Cordis.Repairs.ExchangeReplay
