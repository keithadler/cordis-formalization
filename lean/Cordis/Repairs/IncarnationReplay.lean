import Cordis.Repairs.Incarnation
import Cordis.PartialReplayRegistry

/-!
Birth-indexed accumulator replay. Each annotation comes from an actual
landing that pushed the token. Replay uses the probe's live birth indices
throughout the word because inverse steps preserve every fiber's presence.
-/
namespace Cordis.Repairs.IncarnationReplay
open Calculus Stages StageRecovery PartialReplayRegistry
open Incarnation (birthAt birthAt_of_created Residency)
universe u
variable {Name Key Value Code Error : Type u} [DecidableEq Name] [DecidableEq Key]
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
local notation "I" => Inverse Name Key Value
local notation "Program" => Code → Instruction Name Key Value Code Error

structure Capture (Name Key Value : Type u) where
  token : Inverse Name Key Value
  index : Nat

local notation "C" => Capture Name Key Value

def OriginOn (program : Program) (last : Nat) (states : Nat → R) (actors : Nat → Name)
    (actor : Name) (capture : C) : Prop :=
  ∃ step, step < last ∧ capture.index = step + 1 ∧ actors step = actor ∧
    ∃ middle code next,
      Land program actor code (states step) middle capture.token next ∧
      (∀ name, saved (states (step + 1)) name =
        if name = actor then capture.token :: saved (states step) name
        else saved (states step) name) ∧
      (∀ name, states (step + 1) name = none ↔ middle name = none)

abbrev Origin {program : Program} {initial : R} {last : Nat}
    (trace : Indexed.Trace program initial last) (actor : Name) (capture : C) : Prop :=
  OriginOn program last trace.state trace.actor actor capture

/-- A native event preserves the acting stack, pushes once, or clears it.
The lengths identify a push even when two captured raw tokens are equal. -/
def advance (before after : R) (actor : Name) (index : Nat)
    (stacks : Name → List C) (name : Name) : List C :=
  if name = actor then
    match saved after name with
    | [] => []
    | token :: rest =>
      if (saved before name).length < (token :: rest).length
      then ⟨token, index⟩ :: stacks name else stacks name
  else stacks name

def track (states : Nat → R) (actors : Nat → Name) : Nat → (Name → List C)
  | 0 => fun _ => []
  | time + 1 => advance (states time) (states (time + 1)) (actors time)
      (time + 1) (track states actors time)

structure StackAt {program : Program} {initial : R} {last : Nat}
    (trace : Indexed.Trace program initial last) (time : Nat) (stacks : Name → List C) : Prop where
  tracked : stacks = track trace.state trace.actor time
  projects : ∀ name, (stacks name).map Capture.token = saved (trace.state time) name
  origins : ∀ actor capture, capture ∈ stacks actor → capture.index ≤ time ∧ Origin trace actor capture

omit [DecidableEq Key] in
/-- A step that preserves raw saved words also preserves their annotations. -/
theorem advance_control {before after : R} (actor : Name) (index : Nat)
    (stacks : Name → List C)
    (projected : ∀ name, (stacks name).map Capture.token = saved before name)
    (stable : saved after = saved before) :
    advance before after actor index stacks = stacks := by
  funext name
  by_cases same : name = actor
  · subst name
    cases word : saved before actor with
    | nil =>
      have empty : stacks actor = [] := List.map_eq_nil_iff.mp ((projected actor).trans word)
      simp [advance, stable, word, empty]
    | cons token rest => simp [advance, stable, word]
  · simp [advance, same]

omit [DecidableEq Key] in
theorem advance_capture {before after : R} (actor : Name) (index : Nat)
    (stacks : Name → List C) (token : I)
    (pushed : ∀ name, saved after name =
      if name = actor then token :: saved before name else saved before name) :
    advance before after actor index stacks =
      fun name => if name = actor then ⟨token, index⟩ :: stacks name else stacks name := by
  funext name
  by_cases same : name = actor <;> simp [advance, same, pushed]

omit [DecidableEq Key] in
theorem advance_cleanup {before after : R} (actor : Name) (index : Nat)
    (stacks : Name → List C) (cleared : ∀ name,
      saved after name = if name = actor then [] else saved before name) :
    advance before after actor index stacks = fun name => if name = actor then [] else stacks name := by
  funext name
  by_cases same : name = actor <;> simp [advance, same, cleared]

variable {program : Code → Instruction Name Key Value Code Error}
variable {initial : Registry Name Key Value Code (Inverse Name Key Value) Error} {last : Nat}

/-- The annotation at each position is computed from the native trace. The
proof tracks the exact order of pushes, including repeated equal raw tokens
captured for different births. -/
theorem track_facts (states : Nat → R) (actors : Nat → Name)
    (start : states 0 = fun _ => none)
    (events : ∀ step, step < last → ReplayEvent program (actors step) (states step) (states (step + 1)))
    (time : Nat) (bounded : time ≤ last) :
    (∀ name, (track states actors time name).map Capture.token = saved (states time) name) ∧
      ∀ actor capture, capture ∈ track states actors time actor →
        capture.index ≤ time ∧ OriginOn program last states actors actor capture := by
  induction time with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro name
      simp [track, start, saved]
    · intro _ _ impossible
      cases impossible
  | succ time ih =>
    let stacks := track states actors time
    have earlier := ih (by omega)
    have projected := earlier.1
    have origins := earlier.2
    have event := events time (by omega)
    cases event with
    | control tables stable =>
      have unchanged : track states actors (time + 1) = stacks :=
        advance_control _ _ stacks projected stable
      rw [unchanged]
      refine ⟨fun name => ?_, fun name capture member => ?_⟩
      · rw [stable]
        exact projected name
      · obtain ⟨earlier, origin⟩ := origins name capture member
        exact ⟨by omega, origin⟩
    | capture landed tables pushed presence =>
      rename_i middle code inverse next
      let actor := actors time
      let capture : C := ⟨inverse, time + 1⟩
      let updated := fun name => if name = actor then capture :: stacks name else stacks name
      have recorded : track states actors (time + 1) = updated :=
        advance_capture actor (time + 1) stacks inverse pushed
      rw [recorded]
      refine ⟨fun name => ?_, ?_⟩
      · rw [pushed name]
        change (updated name).map Capture.token = _
        by_cases same : name = actor <;> simp [updated, same, actor, capture, projected, stacks]
      · intro name entry member
        by_cases same : name = actor
        · subst name
          simp only [updated, if_pos rfl, List.mem_cons] at member
          rcases member with rfl | earlier
          · exact ⟨Nat.le_refl _, time, by omega, rfl, rfl, middle, code, next, landed, pushed, presence⟩
          · obtain ⟨bounded, origin⟩ := origins actor entry earlier
            exact ⟨by omega, origin⟩
        · have earlier : entry ∈ stacks name := by simpa [updated, same] using member
          obtain ⟨bounded, origin⟩ := origins name entry earlier
          exact ⟨by omega, origin⟩
    | cleanup selected free tables cleared _ =>
      let actor := actors time
      let updated := fun name => if name = actor then [] else stacks name
      have recorded : track states actors (time + 1) = updated :=
        advance_cleanup actor (time + 1) stacks cleared
      rw [recorded]
      refine ⟨fun name => ?_, ?_⟩
      · rw [cleared name]
        by_cases same : name = actor <;> simp [updated, same, actor, projected, stacks]
      · intro name entry member
        by_cases same : name = actor
        · simp [updated, same] at member
        · have earlier : entry ∈ stacks name := by simpa [updated, same] using member
          obtain ⟨bounded, origin⟩ := origins name entry earlier
          exact ⟨by omega, origin⟩

theorem tracked_stack (trace : Indexed.Trace program (fun _ => none) last)
    (time : Nat) (bounded : time ≤ last) :
    StackAt trace time (track trace.state trace.actor time) := by
  obtain ⟨projects, origins⟩ := track_facts trace.state trace.actor trace.start
    (fun step bound => event_of_step program (trace.step step bound)) time bounded
  exact ⟨rfl, projects, origins⟩

theorem stack_at (trace : Indexed.Trace program (fun _ => none) last)
    (time : Nat) (bounded : time ≤ last) : ∃ stacks, StackAt trace time stacks :=
  ⟨_, tracked_stack trace time bounded⟩

/-- An installed row retains its previously recorded captures. -/
theorem event_capture_persists {actor : Name} {before after : R}
    (event : ReplayEvent program actor before after) (index : Nat) (stacks : Name → List C)
    (projected : ∀ name, (stacks name).map Capture.token = saved before name)
    (name : Name) {capture : C} (installed : ControlFrame.viewAt after name ≠ none)
    (recorded : capture ∈ stacks name) : capture ∈ advance before after actor index stacks name := by
  by_cases same : name = actor
  · subst name
    cases event with
    | control _ stable =>
      rw [advance_control _ _ _ projected stable]
      exact recorded
    | capture landed _ pushed _ =>
      rw [advance_capture _ _ _ _ pushed]
      simpa only [if_pos rfl] using (List.mem_cons_of_mem _ recorded)
    | cleanup _ _ _ _ closed => exact False.elim (installed closed)
  · simpa only [advance, if_neg same] using recorded

theorem capture_persists (trace : Indexed.Trace program (fun _ => none) last)
    {time : Nat} (bounded : time < last) (name : Name) {capture : C}
    (installed : ControlFrame.viewAt (trace.state (time + 1)) name ≠ none)
    (recorded : capture ∈ track trace.state trace.actor time name) :
    capture ∈ track trace.state trace.actor (time + 1) name :=
  event_capture_persists (event_of_step program (trace.step time bounded)) (time + 1) _
    (tracked_stack trace time (by omega)).projects name installed recorded

/-- A recorded capture survives any number of intervening steps in the
same installed interval, including foreign commands and lifecycle steps. -/
theorem capture_through_interval (trace : Indexed.Trace program (fun _ => none) last)
    (name : Name) {first time : Nat} (lower : first ≤ time) (bounded : time ≤ last)
    (installed : ∀ point, first < point → point ≤ time →
      ControlFrame.viewAt (trace.state point) name ≠ none)
    {capture : C} (recorded : capture ∈ track trace.state trace.actor first name) :
    capture ∈ track trace.state trace.actor time name := by
  induction time with
  | zero =>
    have same : first = 0 := by omega
    exact same ▸ recorded
  | succ time ih =>
    by_cases same : first = time + 1
    · exact same ▸ recorded
    apply capture_persists trace (by omega) name (installed (time + 1) (by omega) (by omega))
    exact ih (by omega) (by omega) (fun point later earlier => installed point later (by omega))

omit [DecidableEq Key] in
/-- An empty stack at an earlier cut excludes captures from that cut or
any earlier episode. A push records the new step's index. -/
theorem capture_after_empty (states : Nat → R) (actors : Nat → Name)
    (name : Name) {first time : Nat} (lower : first ≤ time)
    (empty : track states actors first name = [])
    {capture : C} (recorded : capture ∈ track states actors time name) :
    first < capture.index := by
  induction time with
  | zero =>
    have same : first = 0 := by omega
    rw [← same, empty] at recorded
    cases recorded
  | succ time ih =>
    by_cases same : first = time + 1
    · rw [← same, empty] at recorded
      cases recorded
    have earlier : first ≤ time := by omega
    change capture ∈ advance (states time) (states (time + 1)) (actors time)
      (time + 1) (track states actors time) name at recorded
    by_cases acts : name = actors time
    · simp only [advance, if_pos acts] at recorded
      cases word : saved (states (time + 1)) name with
      | nil => rw [word] at recorded; cases recorded
      | cons token rest =>
        simp only [word] at recorded
        split at recorded
        · rcases List.mem_cons.mp recorded with rfl | prior
          · exact Nat.lt_succ_of_le earlier
          · exact ih earlier prior
        · exact ih earlier recorded
    · simp only [advance, if_neg acts] at recorded
      exact ih earlier recorded

/-- A retirement record names the incarnation created by its own landing.
The registry's phase edit cannot change that landing's new entry presence. -/
theorem Origin.retirement_birth {trace : Indexed.Trace program initial last}
    {actor child : Name} {capture : C} (origin : Origin trace actor capture)
    (retirement : capture.token = .retire child) :
    birthAt trace.state child capture.index = some capture.index := by
  obtain ⟨step, _, index, _, middle, code, next, landed, _, presence⟩ := origin
  rw [retirement] at landed
  cases landed with
  | instantiate _ _ _ component child _ ready =>
    rw [index]
    apply birthAt_of_created ready.1
    intro absent
    have impossible := (presence child).mp absent
    simp [put_self] at impossible

def Capture.apply (live : Name → Option Nat) (capture : C) (state : R) : R :=
  match capture.token with
  | .retire child => if live child = some capture.index then Calculus.retire state child else state
  | token => Stages.undo token state

def replay (live : Name → Option Nat) : List C → R → R
  | [], state => state
  | capture :: rest, state => replay live rest (capture.apply live state)

def replayAt (states : Nat → R) (time : Nat) (word : List C) : R :=
  replay (fun name => birthAt states name time) word (states time)

omit [DecidableEq Key] in
private theorem modify_presence (state : R) (name query : Name) (edit : F → F) :
    Calculus.modify state name edit query = none ↔ state query = none := by
  by_cases same : query = name <;> simp [Calculus.modify, same]

theorem Capture.presence (live : Name → Option Nat) (capture : C) (state : R) (name : Name) :
    capture.apply live state name = none ↔ state name = none := by
  rcases capture with ⟨token, index⟩
  cases token with
  | unit => rfl
  | restrict owner key => exact modify_presence state owner name _
  | operate owner key inverse => exact modify_presence state owner name _
  | retire child =>
    simp only [Capture.apply]
    split
    · exact modify_presence state child name _
    · rfl

theorem replay_presence (live : Name → Option Nat) (word : List C) (state : R) (name : Name) :
    replay live word state name = none ↔ state name = none := by
  induction word generalizing state with
  | nil => rfl
  | cons capture rest ih =>
    exact (ih (capture.apply live state)).trans (capture.presence live state name)

/-- The live index function affects a saved word only at its actual
retirement tests. In particular, a birth later than every capture is invisible
to the old word. -/
theorem replay_congr_matches {live later : Name → Option Nat} (word : List C) (state : R)
    (agree : ∀ capture ∈ word, ∀ name, capture.token = .retire name →
      (later name = some capture.index ↔ live name = some capture.index)) :
    replay later word state = replay live word state := by
  induction word generalizing state with
  | nil => rfl
  | cons capture rest ih =>
    have applied : capture.apply later state = capture.apply live state := by
      obtain ⟨token, index⟩ := capture
      cases token with
      | retire child =>
        have matched := agree ⟨.retire child, index⟩ (List.mem_cons_self ..) child rfl
        simp only [Capture.apply, matched]
      | _ => rfl
    rw [replay, replay, applied]
    exact ih _ (fun token member => agree token (List.mem_cons_of_mem _ member))

/-- An old word leaves a newly inserted empty row intact. Table operations
cannot create a binding and the old live-index map cannot retire the row. -/
theorem replay_put_fresh (live : Name → Option Nat) (word : List C) (state : R)
    (name : Name) (component : Component Key Code) (parent : Option Name)
    (absent : live name = none) :
    replay live word (put state name (fresh component parent)) =
      put (replay live word state) name (fresh component parent) := by
  let row : F := fresh component parent
  have modify_put (r : R) (actor : Name) (edit : F → F)
      (stable : actor = name → edit row = row) :
      Calculus.modify (put r name row) actor edit = put (Calculus.modify r actor edit) name row := by
    funext query
    by_cases atBirth : query = name
    · subst query
      by_cases atActor : name = actor
      · simp [Calculus.modify, atActor.symm, stable atActor.symm]
      · simp [Calculus.modify, atActor]
    · by_cases atActor : query = actor
      · subst query
        simp [Calculus.modify, put, atBirth]
      · simp [Calculus.modify, put, atBirth, atActor]
  induction word generalizing state with
  | nil => rfl
  | cons capture rest ih =>
    have step : capture.apply live (put state name row) = put (capture.apply live state) name row := by
      obtain ⟨token, index⟩ := capture
      cases token with
      | unit => rfl
      | restrict owner key =>
        apply modify_put
        intro _
        have table : (fun other => if other = key then none else row.table other) = row.table := by
          funext other
          by_cases same : other = key <;> simp [row, fresh, same]
        exact congrArg (fun table => { row with table := table }) table
      | operate owner key inverse =>
        apply modify_put
        intro _
        have table : (fun other => if other = key then (row.table key).map inverse else row.table other) = row.table := by
          funext other
          by_cases same : other = key <;> simp [row, fresh, same]
        exact congrArg (fun table => { row with table := table }) table
      | retire child =>
        by_cases matched : live child = some index
        · simp only [Capture.apply, if_pos matched]
          apply modify_put
          intro same
          simp [same, absent] at matched
        · simp [Capture.apply, matched]
    change replay live rest (capture.apply live (put state name row)) = _
    rw [step, ih]
    rfl

private theorem Capture.keeps_control (live : Name → Option Nat) (capture : C) (state : R)
    (name : Name) (row : F) (present : state name = some row) :
    ∃ after, capture.apply live state name = some after ∧
      after.component = row.component ∧ after.parent = row.parent ∧ after.phase = row.phase := by
  have undoControl (token : I) : ∃ after, Stages.undo token state name = some after ∧
      after.component = row.component ∧ after.parent = row.parent ∧ after.phase = row.phase := by
    obtain ⟨after, found, samePhase⟩ := Ordering.undo_existing_phases state token name row present
    obtain ⟨sameComponent, sameParent, _⟩ := Frame.undo_stable state token name row after present found
    exact ⟨after, found, sameComponent.symm, sameParent.symm, samePhase⟩
  rcases capture with ⟨token, index⟩
  cases token with
  | retire child =>
    by_cases current : live child = some index
    · simpa only [Capture.apply, if_pos current] using undoControl (.retire child)
    · exact ⟨row, by simp [Capture.apply, current, present], rfl, rfl, rfl⟩
  | unit => exact ⟨row, present, rfl, rfl, rfl⟩
  | restrict owner key => exact undoControl (.restrict owner key)
  | operate owner key inverse => exact undoControl (.operate owner key inverse)

/-- Guarded discharge preserves each existing row's component, parent,
and phase, even when one of its retirement records is stale. -/
theorem replay_keeps_control (live : Name → Option Nat) (word : List C) (state : R)
    (name : Name) (row : F) (present : state name = some row) :
    ∃ after, replay live word state name = some after ∧
      after.component = row.component ∧ after.parent = row.parent ∧ after.phase = row.phase := by
  induction word generalizing state row with
  | nil => exact ⟨row, present, rfl, rfl, rfl⟩
  | cons capture rest ih =>
    obtain ⟨middle, atCut, component, parent, phase⟩ := capture.keeps_control live state name row present
    obtain ⟨after, result, finalComponent, finalParent, finalPhase⟩ := ih _ middle atCut
    exact ⟨after, result, finalComponent.trans component, finalParent.trans parent, finalPhase.trans phase⟩

private theorem undo_table_congr (token : I) {left right : R} (name : Name) (key : Key)
    (same : tableAt left name key = tableAt right name key) :
    tableAt (Stages.undo token left) name key = tableAt (Stages.undo token right) name key := by
  cases token with
  | unit => exact same
  | restrict =>
    rw [tableAt_restrict, tableAt_restrict, same]
  | operate owner query inverse =>
    rw [tableAt_operate, tableAt_operate, same]
    split
    · rename_i routed
      obtain ⟨rfl, rfl⟩ := routed
      rw [same]
    · rfl
  | retire =>
    simpa only [Stages.undo, tableAt_retire] using same

private theorem Capture.tables (live : Name → Option Nat) (capture : C) (state : R) :
    RuleEvaluation.TablesUnchanged (Stages.undo capture.token state) (capture.apply live state) := by
  intro name key
  rcases capture with ⟨token, index⟩
  cases token with
  | unit | restrict | operate => rfl
  | retire =>
    simp only [Capture.apply, Stages.undo]
    split
    · rfl
    · apply tableAt_retire

/-- Retirement stamps affect control only. In particular, this does not
change any table coordinate of the existing partial replay projection. -/
theorem replay_tables (live : Name → Option Nat) (word : List C) {left right : R}
    (tables : RuleEvaluation.TablesUnchanged left right) :
    RuleEvaluation.TablesUnchanged
      (discharge Stages.undo (word.map Capture.token) left) (replay live word right) := by
  induction word generalizing left right with
  | nil => exact tables
  | cons capture rest ih =>
    change RuleEvaluation.TablesUnchanged
      (discharge Stages.undo (rest.map Capture.token) (Stages.undo capture.token left))
      (replay live rest (capture.apply live right))
    apply ih
    intro name key
    exact (undo_table_congr capture.token name key (tables name key)).trans (capture.tables live right name key)

/-- The entire guarded replay at one table coordinate only depends on the
input value at that coordinate. In particular a write at another slot
cannot change this replay. -/
theorem replay_slot_congr (live : Name → Option Nat) (word : List C)
    {left right : R} (name : Name) (key : Key)
    (same : tableAt left name key = tableAt right name key) :
    tableAt (replay live word left) name key = tableAt (replay live word right) name key := by
  induction word generalizing left right with
  | nil => exact same
  | cons capture rest ih =>
    apply ih
    exact (capture.tables live left name key).symm.trans
      ((undo_table_congr capture.token name key same).trans (capture.tables live right name key))

theorem replay_partial_slot (denote : PartialReplaySlots.InverseMeaning Key Value)
    (agrees : PartialReplaySlots.Agrees denote) (owner : Name) (key : Key)
    (live : Name → Option Nat) (word : List C) (state : R) (value : Option Value)
    (performed : PartialReplayHistory.run
      ((word.map Capture.token).map (PartialReplaySlots.project denote owner key))
      (tableAt state owner key) = some value) :
    tableAt (replay live word state) owner key = value := by
  rw [← replay_tables live word (fun _ _ => rfl) owner key]
  exact PartialReplaySlots.project_word denote agrees owner key (word.map Capture.token) state value performed

def Capture.retires (live : Name → Option Nat) (name : Name) (capture : C) : Bool :=
  match capture.token with
  | .retire child => decide (name = child ∧ live child = some capture.index)
  | _ => false

theorem Capture.retired (live : Name → Option Nat) (capture : C) (state : R) (name : Name) :
    (capture.apply live state name).map Fiber.retired =
      (state name).map (fun row => row.retired || capture.retires live name) := by
  rcases capture with ⟨token, index⟩
  cases token with
  | unit => simp [Capture.apply, Capture.retires, Stages.undo]
  | restrict owner key =>
    by_cases same : name = owner
    · subst name
      cases found : state owner <;> simp [Capture.apply, Capture.retires, Stages.undo, write,
        Calculus.modify, found]
    · simp [Capture.apply, Capture.retires, Stages.undo, write, Calculus.modify, same]
  | operate owner key inverse =>
    by_cases same : name = owner
    · subst name
      cases found : state owner <;> simp [Capture.apply, Capture.retires, Stages.undo,
        Calculus.modify, found]
    · simp [Capture.apply, Capture.retires, Stages.undo, Calculus.modify, same]
  | retire child =>
    by_cases same : name = child
    · subst name
      cases found : state child <;> by_cases current : live child = some index <;>
        simp [Capture.apply, Capture.retires, Calculus.retire, Calculus.modify, found, current]
    · by_cases current : live child = some index <;>
        simp [Capture.apply, Capture.retires, Calculus.retire, Calculus.modify, same, current]

/-- The flag changes only if a record matches the current incarnation at
that particular name. Ordinary inverses and stale child records preserve it. -/
theorem replay_retired (live : Name → Option Nat) (word : List C) (state : R) (name : Name) :
    (replay live word state name).map Fiber.retired =
      (state name).map (fun row => row.retired || word.any (Capture.retires live name)) := by
  induction word generalizing state with
  | nil => simp [replay]
  | cons capture rest ih =>
    simp only [replay, ih, List.any_cons]
    let addRest := fun flag => flag || rest.any (Capture.retires live name)
    have mapped := congrArg (Option.map addRest) (capture.retired live state name)
    simpa [addRest, Option.map_map, Function.comp_def, Bool.or_assoc] using mapped

/-- Original discharge agrees on the entire registry whenever the named
targets of retirement records are either the captured incarnation or absent. -/
theorem replay_eq_native (live : Name → Option Nat) (word : List C) (state : R)
    (valid : ∀ capture ∈ word, ∀ child, capture.token = .retire child →
      state child = none ∨ live child = some capture.index) :
    replay live word state = discharge Stages.undo (word.map Capture.token) state := by
  induction word generalizing state with
  | nil => rfl
  | cons capture rest ih =>
    have first : capture.apply live state = Stages.undo capture.token state := by
      rcases capture with ⟨token, index⟩
      cases token with
      | unit | restrict | operate => rfl
      | retire child =>
        rcases valid _ List.mem_cons_self child rfl with absent | same
        · have inactive : Calculus.retire state child = state := by
            funext name
            by_cases target : name = child
            · subst name
              simp [Calculus.retire, Calculus.modify, absent]
            · simp [Calculus.retire, Calculus.modify, target]
          simp [Capture.apply, Stages.undo, inactive]
        · simp [Capture.apply, Stages.undo, same]
    change replay live rest (capture.apply live state) =
      discharge Stages.undo (rest.map Capture.token) (Stages.undo capture.token state)
    rw [ih _ (fun entry member child kind => ?_), first]
    rcases valid entry (List.mem_cons_of_mem _ member) child kind with absent | matchesBirth
    · exact .inl ((capture.presence live state child).mpr absent)
    · exact .inr matchesBirth

/-- An always-matching annotation recovers ordinary discharge exactly.
This representation is used to compare its effects with the guarded word. -/
theorem replay_native_discharge (state : R) (word : List I) :
    replay (fun _ => some 0) (word.map fun token => (⟨token, 0⟩ : C)) state = discharge Stages.undo word state := by
  have tests (capture : C) (member : capture ∈ word.map (fun token => (⟨token, 0⟩ : C)))
      (child : Name) (_ : capture.token = .retire child) : state child = none ∨ some 0 = some capture.index := by
    obtain ⟨token, _, rfl⟩ := List.mem_map.mp member
    exact .inr rfl
  simpa [List.map_map, Function.comp_def] using replay_eq_native (fun _ => some 0) _ state tests

/-- On an actual unload, discharging the witnessed annotated stack and
then applying the native phase edit preserves each table coordinate of
the original transition. Its retirement flags follow `replay_retired`. -/
theorem unload_tables (trace : Indexed.Trace program initial last)
    (time : Nat) (bounded : time < last) (rule : trace.rule time = .unload)
    {stacks : Name → List C} (annotated : StackAt trace time stacks) :
    RuleEvaluation.TablesUnchanged (trace.state (time + 1))
      (mark (replayAt trace.state time (stacks (trace.actor time))) (trace.actor time) .inactive) := by
  have step := trace.step time bounded
  rw [rule] at step
  generalize trace.state (time + 1) = result at step ⊢
  cases step with
  | unload _ _ fiber word view present phase free =>
    have selected : (stacks (trace.actor time)).map Capture.token = word := by
      rw [annotated.projects]
      simp [saved, present, phase, Phase.accumulator]
    intro name key
    rw [tableAt_mark, tableAt_mark]
    simpa only [selected, replayAt] using
      replay_tables (fun name => birthAt trace.state name time) (stacks (trace.actor time))
        (left := trace.state time) (right := trace.state time) (fun _ _ => rfl) name key

end Cordis.Repairs.IncarnationReplay
