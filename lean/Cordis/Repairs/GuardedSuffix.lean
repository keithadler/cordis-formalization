import Cordis.Repairs.EpisodeAnnotations
import Cordis.Repairs.ExchangeReplay

/-! The suffix uses the native commands and lifecycle rules with the
incarnation test on L-Unload. Stamps come from the ordered source events,
including when some events are deleted from the replay. -/
namespace Cordis.Repairs.GuardedSuffix
open Calculus Stages IncarnationReplay LegalHistory
open Vestigial (CutNotes eventActor noteStep)
universe u
variable {Name Key Value Code Error : Type u} [DecidableEq Name] [DecidableEq Key]
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "C" => Capture Name Key Value
local notation "Notes" => CutNotes Name Key Value
local notation "Ev" => Event Name Key Code
local notation "Program" => Code → Instruction Name Key Value Code Error

def eraseNotes (name : Name) (notes : Notes) : Notes :=
  (fun query => if query = name then none else notes.1 query,
   fun query => if query = name then [] else notes.2 query)

/-- Corrected unload discharges the annotations of the actual saved stack
using the recorded live births. All original unload guards still apply. -/
def Unload (actor : Name) (before : R) (notes : Notes) (after : R) : Prop :=
  ∃ row view, before actor = some row ∧
    row.phase = .unloading ((notes.2 actor).map Capture.token) view ∧ ¬ Relied before actor ∧
    after = mark (replay notes.1 (notes.2 actor) before) actor .inactive

def Transition (program : Program) (notes : Notes) (event : Ev) (before after : R) : Prop :=
  match event with
  | .lifecycle .unload actor => Unload actor before notes after
  | .lifecycle kind actor => Labeled.Step program kind.rule actor before after
  | .command command => command.Step before after

def Step (program : Program) (event : Ev) (stamp : Nat)
    (before : R) (notes : Notes) (after : R) (recorded : Notes) : Prop :=
  Transition program notes event before after ∧ recorded = noteStep before after (eventActor event) stamp notes

omit [DecidableEq Name] [DecidableEq Key] in
def SavedWordsAgree (state : R) (notes : Notes) : Prop :=
  ∀ name, (notes.2 name).map Capture.token = PartialReplayRegistry.saved state name

theorem replay_saved (live : Name → Option Nat) (word : List C) (state : R) :
    PartialReplayRegistry.saved (replay live word state) = PartialReplayRegistry.saved state := by
  funext name
  cases found : state name with
  | none => simp [PartialReplayRegistry.saved, found, (replay_presence live word state name).mpr found]
  | some row =>
    obtain ⟨after, present, _, _, phase⟩ := replay_keeps_control live word state name row found
    simp [PartialReplayRegistry.saved, present, found, phase]

/-- The stamp recorder carries the exact new saved word, including after
an unload whose incarnation test skipped a stale retirement. -/
theorem step_projects {program : Program} {before after : R} {event : Ev} {stamp : Nat} {notes recorded : Notes}
    (step : Step program event stamp before notes after recorded) (projects : SavedWordsAgree before notes) :
    SavedWordsAgree after recorded := by
  obtain ⟨native, rfl⟩ := step
  cases event with
  | command command =>
    exact Vestigial.noteStep_projects (ExchangeReplay.command_labeled (program := program) command native) stamp notes projects
  | lifecycle kind actor =>
    cases kind
    case unload =>
      obtain ⟨row, view, present, phase, free, rfl⟩ := native
      let reverted := replay notes.1 (notes.2 actor) before
      obtain ⟨survives, found, _, _, _⟩ := replay_keeps_control notes.1 (notes.2 actor) before actor row present
      intro name
      have cleaned : PartialReplayRegistry.saved (mark reverted actor .inactive) name =
          if name = actor then [] else PartialReplayRegistry.saved before name := by
        rw [PartialReplayRegistry.saved_mark _ _ _ found, replay_saved]
        rfl
      change (advance before (mark reverted actor .inactive) actor stamp notes.2 name).map Capture.token = _
      rw [advance, cleaned]
      by_cases acts : name = actor <;> simp only [acts, if_true, if_false, projects name, List.map_nil]
    all_goals exact Vestigial.noteStep_projects native stamp notes projects

private theorem replay_removable (live : Name → Option Nat) (word : List C) {before : R}
    {name : Name} (ready : Removable before name) : Removable (replay live word before) name := by
  induction word generalizing before with
  | nil => exact ready
  | cons capture rest ih =>
    apply ih
    obtain ⟨token, index⟩ := capture
    cases token with
    | retire child =>
      by_cases current : live child = some index
      · simpa only [Capture.apply, if_pos current] using Vestigial.removable_undo ready (.retire child)
      · simpa only [Capture.apply, if_neg current] using ready
    | unit => exact ready
    | restrict owner key => exact Vestigial.removable_undo ready (.restrict owner key)
    | operate owner key inverse => exact Vestigial.removable_undo ready (.operate owner key inverse)

theorem unload_erase {before after : R} {actor name : Name} {notes : Notes}
    (step : Unload actor before notes after) (different : actor ≠ name) (ready : Removable before name) :
    Removable after name ∧ Unload actor (erase before name) (eraseNotes name notes) (erase after name) := by
  obtain ⟨row, view, present, phase, free, rfl⟩ := step
  have live (child : Name) (retained : child ≠ name) : (eraseNotes name notes).1 child = notes.1 child :=
    if_neg retained
  have words : (eraseNotes name notes).2 actor = notes.2 actor := if_neg different
  have same := Vestigial.replay_erase before name live (notes.2 actor)
  refine ⟨Vestigial.removable_mark (replay_removable _ _ ready) different .inactive,
    row, view, by simpa only [erase, if_neg different] using present,
    by simpa only [words] using phase, fun relied => free ((Vestigial.erase_relied ready).mp relied), ?_⟩
  rw [words, same]
  exact (Vestigial.modify_erase _ _ _ _).symm

omit [DecidableEq Key] in
theorem noteStep_erase (before after : R) (actor name : Name) (stamp : Nat) (notes : Notes)
    (different : actor ≠ name) :
    noteStep (erase before name) (erase after name) actor stamp (eraseNotes name notes) =
      eraseNotes name (noteStep before after actor stamp notes) := by
  apply Prod.ext
  · funext query
    by_cases erased : query = name <;> simp [noteStep, eraseNotes, erase, erased]
  · funext query
    by_cases erased : query = name
    · subst query
      simp [noteStep, eraseNotes, advance, Ne.symm different]
    · simp [noteStep, eraseNotes, advance, PartialReplayRegistry.saved, erase, erased]

/-- Deleting the inactive leaf commutes with all foreign suffix steps,
including a guarded unload whose saved word names the withdrawn child. -/
theorem step_erase {program : Program} {before after : R} {event : Ev} {stamp : Nat} {notes recorded : Notes}
    {name : Name} (step : Step program event stamp before notes after recorded)
    (different : eventActor event ≠ name) (ready : Removable before name) :
    Removable after name ∧ Step program event stamp (erase before name) (eraseNotes name notes)
      (erase after name) (eraseNotes name recorded) := by
  obtain ⟨eventStep, rfl⟩ := step
  have annotated := (noteStep_erase before after (eventActor event) name stamp notes different).symm
  have moved : Removable after name ∧ Transition program (eraseNotes name notes) event (erase before name) (erase after name) := by
    cases event with
    | command command => exact Vestigial.command_erase command eventStep different ready
    | lifecycle kind actor =>
      cases kind
      case unload => exact unload_erase eventStep different ready
      all_goals exact Vestigial.event_erase (event := .lifecycle _ actor) eventStep different ready
  exact ⟨moved.1, moved.2, annotated⟩

omit [DecidableEq Name] [DecidableEq Key] in
def BirthsAgree (state : R) (notes : Notes) : Prop :=
  ∀ name, notes.1 name = none ↔ state name = none

omit [DecidableEq Key] in
theorem noteStep_births (before after : R) (actor : Name) (stamp : Nat) (notes : Notes) :
    BirthsAgree after (noteStep before after actor stamp notes) := by
  intro name
  cases found : after name <;> simp [noteStep, found]

omit [DecidableEq Key] in
private theorem note_retained_birth {before after : R} {notes : Notes}
    (valid : BirthsAgree before notes) {name : Name} (same : after name = before name) (actor : Name) (stamp : Nat) :
    (noteStep before after actor stamp notes).1 name = notes.1 name := by
  change (after name).map (fun _ => (notes.1 name).getD stamp) = _
  rw [same]
  cases found : before name with
  | none => exact ((valid name).mpr found).symm
  | some row =>
    cases born : notes.1 name with
    | none =>
      have absent := (valid name).mp born
      rw [found] at absent
      cases absent
    | some index => rfl

private theorem step_at_vestige {program : Program} {before after : R} {event : Ev} {notes : Notes}
    {name : Name} (step : Transition program notes event before after) (acts : eventActor event = name)
    (ready : Removable before name) :
    (event = .command (.retire name) ∧ after = before) ∨
    (event = .command (.remove name) ∧ after = erase before name) := by
  cases event with
  | command command =>
    change command.actor = name at acts
    cases command with
    | insert target component =>
      change target = name at acts
      subst target
      exact False.elim (Transposition.removable_present _ _ ready step.1.1)
    | retire target =>
      change target = name at acts
      subst target
      exact .inl ⟨rfl, step.2.trans (Vestigial.retire_vestigial ready)⟩
    | remove target =>
      change target = name at acts
      subst target
      exact .inr ⟨rfl, step.2⟩
  | lifecycle kind actor =>
    change actor = name at acts
    subst actor
    cases kind
    case unload =>
      obtain ⟨row, view, present, phase, _, _⟩ := step
      simp [Removable, present, phase] at ready
    all_goals
      rcases Vestigial.steps_at_vestige ready step with ⟨wrong, _⟩ | ⟨wrong, _⟩ <;> cases wrong

private theorem rootAt_replay (live : Name → Option Nat) (word : List C) (state : R) (name : Name) :
    rootAt (replay live word state) name = rootAt state name := by
  induction word generalizing state with
  | nil => rfl
  | cons capture rest ih =>
    rw [replay, ih]
    obtain ⟨token, index⟩ := capture
    cases token with
    | retire child =>
      by_cases matched : live child = some index <;> simp [Capture.apply, matched]
    | unit => rfl
    | restrict owner key => exact rootAt_undo state (.restrict owner key) name
    | operate owner key inverse => exact rootAt_undo state (.operate owner key inverse) name

private theorem rootAt_foreign {program : Program} {before after : R} {event : Ev} {notes : Notes}
    {name : Name} (step : Transition program notes event before after) (different : eventActor event ≠ name) :
    rootAt after name = rootAt before name := by
  cases event with
  | command command =>
    rw [step.2]
    unfold rootAt
    rw [CausalCommands.apply_other command before name (Ne.symm different)]
  | lifecycle kind actor =>
    cases kind
    case unload =>
      obtain ⟨row, view, _, _, _, rfl⟩ := step
      rw [rootAt_mark, rootAt_replay]
    all_goals exact rootAt_lifecycle _ step name

omit [DecidableEq Key] in
private theorem eventRoots_erase_foreign (event : Ev) (state : R) {name : Name} (different : eventActor event ≠ name) :
    eventRoots (erase state name) event = eventRoots state event := by
  cases event with
  | lifecycle => rfl
  | command command => exact commandRoots_same_row command (by simp [erase, show command.actor ≠ name from different])

omit [DecidableEq Key] in
private theorem omit_retirement_notes (state : R) (name : Name) (stamp : Nat) (notes : Notes)
    (valid : BirthsAgree state notes) :
    eraseNotes name (noteStep state state name stamp notes) = eraseNotes name notes := by
  apply Prod.ext <;> funext query <;> by_cases same : query = name
  · simp [eraseNotes, same]
  · simpa only [eraseNotes, if_neg same] using note_retained_birth valid (name := query) rfl name stamp
  · simp [eraseNotes, same]
  · simp [eraseNotes, noteStep, advance, same]

omit [DecidableEq Key] in
private theorem omit_removal_notes (state : R) (name : Name) (stamp : Nat) (notes : Notes)
    (valid : BirthsAgree state notes) :
    noteStep state (erase state name) name stamp notes = eraseNotes name notes := by
  apply Prod.ext <;> funext query <;> by_cases same : query = name
  · subst query
    simp [eraseNotes, erase, noteStep]
  · simpa only [eraseNotes, if_neg same] using
      note_retained_birth valid (name := query) (by simp [erase, same]) name stamp
  · subst query
    simp [eraseNotes, erase, noteStep, advance, PartialReplayRegistry.saved]
  · simp [eraseNotes, noteStep, advance, same]

local notation "Cmd" => OrchestrationSorting.Command Name Key Code

/-- The birth stamp and component of an event's actual actor at the source
cut. An insertion has no existing actor, while retire and remove refer to
the live incarnation immediately before their command. -/
abbrev ActorSource (Key Code : Type u) := Option Nat × Option (Component Key Code)

def actorSource (before : R) (notes : Notes) (event : Ev) : ActorSource Key Code :=
  let actor := eventActor event
  (notes.1 actor, (before actor).map Fiber.component)

def CheckedSource (sources : Nat → Option (ActorSource Key Code)) (stamp : Nat)
    (before : R) (notes : Notes) (event : Ev) : Prop :=
  match sources stamp with
  | none => True
  | some expected => actorSource before notes event = expected

omit [DecidableEq Key] in
theorem actorSource_erase {before : R} {notes : Notes} {event : Ev} {name : Name}
    (different : eventActor event ≠ name) :
    actorSource (erase before name) (eraseNotes name notes) event = actorSource before notes event := by
  simp [actorSource, erase, eraseNotes, different]

omit [DecidableEq Key] in
theorem CheckedSource.erase {sources : Nat → Option (ActorSource Key Code)} {stamp : Nat}
    {before : R} {notes : Notes} {event : Ev} {name : Name}
    (checked : CheckedSource sources stamp before notes event) (different : eventActor event ≠ name) :
    CheckedSource sources stamp (erase before name) (eraseNotes name notes) event := by
  unfold CheckedSource at *
  rw [actorSource_erase different]
  exact checked

inductive ExecWith (program : Program) (sources : Nat → Option (ActorSource Key Code)) :
    List (Nat × Ev) → R → Notes → R → Notes → List Cmd → Prop
  | nil (state notes) : ExecWith program sources [] state notes state notes []
  | cons {stamp event events before notes middle recorded final finalNotes roots} :
      Step program event stamp before notes middle recorded →
      ExecWith program sources events middle recorded final finalNotes roots →
      (checked : CheckedSource sources stamp before notes event := by trivial) →
      ExecWith program sources ((stamp, event) :: events) before notes final finalNotes (eventRoots before event ++ roots)

abbrev Exec (program : Program) := ExecWith program (fun _ => none)

theorem ExecWith.forgetSources {program : Program} {sources : Nat → Option (ActorSource Key Code)}
    {events : List (Nat × Ev)} {before final : R} {notes finalNotes : Notes} {roots : List Cmd}
    (run : ExecWith program sources events before notes final finalNotes roots) :
    Exec program events before notes final finalNotes roots := by
  induction run with
  | nil => exact .nil _ _
  | cons step _ _ ih => exact .cons step ih

theorem ExecWith.append {program : Program} {sources : Nat → Option (ActorSource Key Code)}
    {front suffix : List (Nat × Ev)} {before middle after : R}
    {first intermediate last : Notes} {frontRoots suffixRoots : List Cmd}
    (left : ExecWith program sources front before first middle intermediate frontRoots)
    (right : ExecWith program sources suffix middle intermediate after last suffixRoots) :
    ExecWith program sources (front ++ suffix) before first after last (frontRoots ++ suffixRoots) := by
  induction left with
  | nil => exact right
  | cons step _ checked ih => simpa only [List.cons_append, List.append_assoc] using ExecWith.cons step (ih right) checked

omit [DecidableEq Key] in
/-- Skip redundant retirement and the first removal of the withdrawn live
child. Every later event is copied with its original stamp and payload. -/
def prune (name : Name) : List (Nat × Ev) → List (Nat × Ev)
  | [] => []
  | (stamp, .command (.retire target)) :: rest =>
    if target = name then prune name rest else (stamp, .command (.retire target)) :: prune name rest
  | (stamp, .command (.remove target)) :: rest =>
    if target = name then rest else (stamp, .command (.remove target)) :: prune name rest
  | event :: rest => event :: prune name rest

omit [DecidableEq Key] in
theorem prune_sublist (name : Name) (events : List (Nat × Ev)) : (prune name events).Sublist events := by
  induction events with
  | nil => exact .slnil
  | cons first rest ih =>
    obtain ⟨stamp, event⟩ := first
    cases event with
    | lifecycle => exact .cons₂ _ ih
    | command command =>
      cases command with
      | insert => exact .cons₂ _ ih
      | retire target =>
        by_cases same : target = name
        · rw [prune, if_pos same]
          exact .cons _ ih
        · rw [prune, if_neg same]
          exact .cons₂ _ ih
      | remove target =>
        by_cases same : target = name
        · rw [prune, if_pos same]
          exact .cons _ (List.Sublist.refl rest)
        · rw [prune, if_neg same]
          exact .cons₂ _ ih

omit [DecidableEq Key] in
private theorem prune_other (stamp : Nat) (event : Ev) (events : List (Nat × Ev)) (name : Name)
    (different : eventActor event ≠ name) :
    prune name ((stamp, event) :: events) = (stamp, event) :: prune name events ∧
      Vestigial.mentionsRemoval name event = false := by
  cases event with
  | lifecycle => exact ⟨rfl, rfl⟩
  | command command =>
    cases command with
    | insert => exact ⟨rfl, rfl⟩
    | retire target => simp [prune, Vestigial.mentionsRemoval, show target ≠ name from different]
    | remove target => simp [prune, Vestigial.mentionsRemoval, show target ≠ name from different]

omit [DecidableEq Key] in
def removed (name : Name) (events : List (Nat × Ev)) : Bool :=
  events.any (fun event => Vestigial.mentionsRemoval name event.2)

/-- A vestige that reaches the end of the suffix before its removal
still occupies a removable, nonroot row. -/
theorem remaining_vestige {program : Program} {sources : Nat → Option (ActorSource Key Code)}
    {events : List (Nat × Ev)} {before final : R} {notes finalNotes : Notes} {roots : List Cmd}
    (run : ExecWith program sources events before notes final finalNotes roots)
    (name : Name) (ready : Removable before name) (nonroot : rootAt before name = false)
    (still : removed name events = false) : Removable final name ∧ rootAt final name = false := by
  induction run with
  | nil => exact ⟨ready, nonroot⟩
  | @cons stamp event events before notes middle recorded final finalNotes roots step suffix _ ih =>
    have remaining : removed name events = false := (Bool.or_eq_false_iff.mp still).2
    by_cases own : eventActor event = name
    · rcases step_at_vestige step.1 own ready with ⟨retired, same⟩ | ⟨removedHere, _⟩
      · subst middle
        exact ih ready nonroot remaining
      · simp [removed, removedHere, Vestigial.mentionsRemoval] at still
    · exact ih (step_erase step own ready).1 ((rootAt_foreign step.1 own).trans nonroot) remaining

/-- A guarded suffix can omit a withdrawn vestige through its own removal.
The suffix derives its root commands from the actual source rows. -/
theorem prune_suffix {program : Program} {sources : Nat → Option (ActorSource Key Code)}
    {events : List (Nat × Ev)} {before final : R} {notes finalNotes : Notes} {roots : List Cmd}
    (run : ExecWith program sources events before notes final finalNotes roots)
    (name : Name) (valid : BirthsAgree before notes) (ready : Removable before name) (child : rootAt before name = false) :
    ExecWith program sources (prune name events) (erase before name) (eraseNotes name notes)
      (if removed name events then final else erase final name)
      (if removed name events then finalNotes else eraseNotes name finalNotes) roots := by
  induction run with
  | nil => exact .nil _ _
  | @cons stamp event events before notes middle recorded final finalNotes roots step suffix checked ih =>
    obtain ⟨native, rfl⟩ := step
    have nextValid := noteStep_births before middle (eventActor event) stamp notes
    by_cases own : eventActor event = name
    · rcases step_at_vestige native own ready with ⟨eventEq, stateEq⟩ | ⟨eventEq, stateEq⟩
      · subst event
        subst middle
        have earlier := ih nextValid ready child
        simp only [eventActor, OrchestrationSorting.Command.actor] at earlier
        rw [omit_retirement_notes before name stamp notes valid] at earlier
        simpa only [prune, removed, if_pos rfl, List.any_cons, Vestigial.mentionsRemoval, Bool.false_or,
          eventRoots, commandRoots, child, Bool.false_eq_true, if_false, List.nil_append] using earlier
      · subst event
        subst middle
        simp only [eventActor, OrchestrationSorting.Command.actor] at suffix
        rw [omit_removal_notes before name stamp notes valid] at suffix
        simpa only [prune, removed, if_pos rfl, List.any_cons, Vestigial.mentionsRemoval, decide_true, Bool.true_or,
          if_true, eventRoots, commandRoots, child, Bool.false_eq_true, if_false, List.nil_append] using suffix
    · have moved := step_erase (show Step program event stamp before notes middle _ from ⟨native, rfl⟩) own ready
      have stays : rootAt middle name = false := (rootAt_foreign native own).trans child
      have tail := ih nextValid moved.1 stays
      obtain ⟨listEq, keepsStamp⟩ := prune_other stamp event events name own
      rw [listEq, removed, List.any_cons, keepsStamp, Bool.false_or, ← eventRoots_erase_foreign event before own]
      exact .cons moved.2 tail (checked.erase own)

omit [DecidableEq Key] in
def pruneAll : List Name → List (Nat × Ev) → List (Nat × Ev)
  | [], events => events
  | name :: rest, events => pruneAll rest (prune name events)

omit [DecidableEq Key] in
theorem pruneAll_sublist (names : List Name) (events : List (Nat × Ev)) : (pruneAll names events).Sublist events := by
  induction names generalizing events with
  | nil => exact List.Sublist.refl _
  | cons name rest ih => exact (ih (prune name events)).trans (prune_sublist name events)

omit [DecidableEq Key] in
def eraseAllNotes : List Name → Notes → Notes
  | [], notes => notes
  | name :: rest, notes => eraseAllNotes rest (eraseNotes name notes)

omit [DecidableEq Key] in
def stillPresent (names : List Name) (events : List (Nat × Ev)) : List Name :=
  names.filter fun name => !(removed name events)

omit [DecidableEq Key] in
theorem eraseAllNotes_apply (names : List Name) (notes : Notes) :
    eraseAllNotes names notes =
      (fun name => if name ∈ names then none else notes.1 name,
        fun name => if name ∈ names then [] else notes.2 name) := by
  induction names generalizing notes with
  | nil => simp [eraseAllNotes]
  | cons first rest ih =>
    rw [eraseAllNotes, ih]
    apply Prod.ext <;> funext query <;> by_cases here : query = first <;> by_cases later : query ∈ rest <;>
      simp [eraseNotes, here, later]

omit [DecidableEq Key] in
private theorem eraseNotes_births {state : R} {notes : Notes} (valid : BirthsAgree state notes) (name : Name) :
    BirthsAgree (erase state name) (eraseNotes name notes) := by
  intro query
  by_cases erased : query = name <;> simp [eraseNotes, erase, erased, valid query]

omit [DecidableEq Key] in
private theorem removed_prune_other {forgotten name : Name} (different : name ≠ forgotten)
    (events : List (Nat × Ev)) : removed name (prune forgotten events) = removed name events := by
  induction events with
  | nil => rfl
  | cons head rest ih =>
    obtain ⟨stamp, event⟩ := head
    cases event with
    | lifecycle => simpa [removed, prune, Vestigial.mentionsRemoval] using ih
    | command command =>
      cases command with
      | insert => simpa [removed, prune, Vestigial.mentionsRemoval] using ih
      | retire target =>
        by_cases same : target = forgotten <;> simpa [removed, prune, Vestigial.mentionsRemoval, same] using ih
      | remove target =>
        by_cases same : target = forgotten
        · subst target
          simp [removed, prune, Vestigial.mentionsRemoval, Ne.symm different]
        · rw [prune, if_neg same]
          change (decide (target = name) || removed name (prune forgotten rest)) =
            (decide (target = name) || removed name rest)
          rw [ih]

/-- Multiple vestiges may be projected from a guarded suffix. Each
omission ends at its own removal, and all other stamps survive. -/
theorem prune_all {program : Program} {sources : Nat → Option (ActorSource Key Code)}
    {events : List (Nat × Ev)} {before final : R} {notes finalNotes : Notes} {roots : List Cmd}
    (run : ExecWith program sources events before notes final finalNotes roots)
    (names : List Name) (unique : names.Nodup) (valid : BirthsAgree before notes)
    (children : ∀ name ∈ names, Removable before name ∧ rootAt before name = false) :
    ExecWith program sources (pruneAll names events) (Vestigial.eraseAll names before) (eraseAllNotes names notes)
      (Vestigial.eraseAll (stillPresent names events) final) (eraseAllNotes (stillPresent names events) finalNotes) roots := by
  induction names generalizing before notes events final finalNotes with
  | nil => exact run
  | cons first rest ih =>
    obtain ⟨distinct, restUnique⟩ := List.nodup_cons.mp unique
    obtain ⟨ready, child⟩ := children first List.mem_cons_self
    have projected := prune_suffix run first valid ready child
    have keptLeaves : ∀ name ∈ rest, Removable (erase before first) name ∧ rootAt (erase before first) name = false := by
      intro name member
      have different : name ≠ first := fun same => distinct (same ▸ member)
      obtain ⟨leaf, nonroot⟩ := children name (List.mem_cons_of_mem _ member)
      exact ⟨Vestigial.erase_removable different leaf, by simpa [rootAt, erase, different] using nonroot⟩
    have replayed := ih projected restUnique (eraseNotes_births valid first) keptLeaves
    have sameMask : stillPresent rest (prune first events) = stillPresent rest events := by
      apply List.filter_congr
      intro name member
      have different : name ≠ first := fun same => distinct (same ▸ member)
      simp only [removed_prune_other different]
    rw [sameMask] at replayed
    cases taken : removed first events <;> simpa [pruneAll, Vestigial.eraseAll, eraseAllNotes, stillPresent, taken] using replayed

end Cordis.Repairs.GuardedSuffix
