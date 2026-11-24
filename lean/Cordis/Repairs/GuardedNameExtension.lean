import Cordis.Repairs.GuardedCompleteAlignment

/-! Embed an open history in a larger name set. This lets the alignment
proof use temporary draws while retaining the original endpoint rows. -/
namespace Cordis.Repairs.GuardedNameExtension
open Calculus Stages LegalHistory GuardedHistory GuardedCutState
open GuardedBirthAddresses
open GuardedAddressSchedule
open PaperEffectEquations (CoeffectOperations)
open TypedRegistry (encodeProgram Scalar)

universe u
variable {Name Key Value Code Error : Type u} [DecidableEq Name] [DecidableEq Key]
abbrev Names (Name : Type u) := Sum Name Nat
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "R'" => Registry (Names Name) Key Value Code (Inverse (Names Name) Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
local notation "F'" => Fiber (Names Name) Key Value Code (Inverse (Names Name) Key Value) Error

def liftInverse : Inverse Name Key Value → Inverse (Names Name) Key Value
  | .unit => .unit
  | .restrict owner key => .restrict (.inl owner) key
  | .operate owner key fn => .operate (.inl owner) key fn
  | .retire child => .retire (.inl child)

def liftPhase : Phase Name Key Code (Inverse Name Key Value) → Phase (Names Name) Key Code (Inverse (Names Name) Key Value)
  | .inactive => .inactive
  | .reloading code word view => .reloading code (word.map liftInverse) (Sum.inl ∘ view)
  | .active word view => .active (word.map liftInverse) (Sum.inl ∘ view)
  | .unloading word view => .unloading (word.map liftInverse) (Sum.inl ∘ view)

def liftFiber (row : F) : F' := ⟨row.component, row.parent.map Sum.inl, row.table, row.retired, liftPhase row.phase⟩

def liftRegistry (state : R) : R'
  | .inl name => (state name).map liftFiber
  | .inr _ => none

omit [DecidableEq Name] [DecidableEq Key] in
@[simp] theorem lift_registry_inl (state : R) (name : Name) : liftRegistry state (.inl name) = (state name).map liftFiber := rfl
omit [DecidableEq Name] [DecidableEq Key] in
@[simp] theorem lift_registry_inr (state : R) (name : Nat) : liftRegistry state (.inr name) = none := rfl

omit [DecidableEq Key] in
private theorem lift_put (state : R) (name : Name) (row : F) :
    liftRegistry (put state name row) = put (liftRegistry state) (.inl name) (liftFiber row) := by
  funext query
  cases query with
  | inl old => by_cases same : old = name <;> simp [put, same]
  | inr spare => simp [put]

omit [DecidableEq Key] in
private theorem lift_modify (state : R) (name : Name) (change : F → F) (other : F' → F')
    (agrees : ∀ row, liftFiber (change row) = other (liftFiber row)) :
    liftRegistry (Calculus.modify state name change) = Calculus.modify (liftRegistry state) (.inl name) other := by
  funext query
  cases query with
  | inl old =>
    by_cases same : old = name
    · subst old; cases found : state name <;> simp [Calculus.modify, found, agrees]
    · simp [Calculus.modify, same]
  | inr spare => simp [Calculus.modify]

private theorem lift_write (state : R) (name : Name) (key : Key) (value : Option Value) :
    liftRegistry (write state name key value) = write (liftRegistry state) (.inl name) key value :=
  lift_modify _ _ _ _ (fun _ => rfl)

omit [DecidableEq Key] in
private theorem lift_mark (state : R) (name : Name) (phase : Phase Name Key Code (Inverse Name Key Value)) :
    liftRegistry (mark state name phase) = mark (liftRegistry state) (.inl name) (liftPhase phase) :=
  lift_modify _ _ _ _ (fun _ => rfl)

omit [DecidableEq Key] in
private theorem lift_retire (state : R) (name : Name) :
    liftRegistry (retire state name) = retire (liftRegistry state) (.inl name) := lift_modify _ _ _ _ (fun _ => rfl)

omit [DecidableEq Key] in
private theorem lift_erase (state : R) (name : Name) :
    liftRegistry (erase state name) = erase (liftRegistry state) (.inl name) := by
  funext query
  cases query with
  | inl old => by_cases same : old = name <;> simp [erase, same]
  | inr spare => simp [erase]

omit [DecidableEq Name] [DecidableEq Key] in
private theorem lift_insertable (state : R) (name : Name) (component : Component Key Code) (parent : Option Name)
    (ready : Insertable state name component parent) :
    Insertable (liftRegistry state) (.inl name) component (parent.map Sum.inl) := by
  refine ⟨by simp [ready.1], ?_, ?_⟩
  · intro owner tag absent
    cases parent with
    | none => cases tag
    | some p =>
      have same : Sum.inl p = owner := Option.some.inj tag
      subst owner
      exact ready.2.1 p rfl (by simpa using absent)
  · intro other key
    cases other with
    | inr spare => trivial
    | inl old =>
      have consistent := ready.2.2 old key
      cases entry : state old <;> simp [entry, liftFiber] at consistent ⊢ <;> exact consistent

omit [DecidableEq Name] [DecidableEq Key] in
private theorem lift_removable (state : R) (name : Name) (ready : Removable state name) :
    Removable (liftRegistry state) (.inl name) := by
  cases found : state name with
  | none => simp [Removable, found] at ready
  | some row =>
    rw [Removable, found] at ready
    rw [Removable, lift_registry_inl, found]
    refine ⟨ready.1, by change liftPhase row.phase = .inactive; rw [show row.phase = .inactive from ready.2.1]; rfl,
      ready.2.2.1, ?_⟩
    intro child
    cases child with
    | inr spare => trivial
    | inl old =>
      have leaf := ready.2.2.2 old
      cases entry : state old with
      | none => simp [entry]
      | some child =>
        simp only [entry] at leaf
        simp only [lift_registry_inl, entry, Option.map_some]
        intro parentEq
        cases parent : child.parent with
        | none => simp [liftFiber, parent] at parentEq
        | some owner =>
          have same : owner = name := Sum.inl.inj (Option.some.inj (by simpa only [liftFiber, parent, Option.map_some] using parentEq))
          exact leaf (parent.trans (congrArg some same))

omit [DecidableEq Name] [DecidableEq Key] in
private theorem lift_available (phase : Phase Name Key Code (Inverse Name Key Value)) : (liftPhase phase).available ↔ phase.available := by
  cases phase <;> rfl

omit [DecidableEq Name] [DecidableEq Key] in
theorem target_lift_iff (state : R) (actor : Name) (view : View Name Key) :
    Target (liftRegistry state) (.inl actor) (Sum.inl ∘ view) ↔ Target state actor view := by
  cases found : state actor with
  | none => simp [Target, found]
  | some row =>
    simp only [Target, lift_registry_inl, found, Option.map_some]
    apply and_congr Iff.rfl
    apply forall_congr'
    intro key
    apply imp_congr_right
    intro _
    cases provider : state (view key) <;> simp [Function.comp_apply, provider, liftFiber, lift_available]

omit [DecidableEq Name] [DecidableEq Key] in
private theorem lift_location (state : R) (actor : Name) (key : Key) :
    location (liftRegistry state) (.inl actor) key = (location state actor key).map (fun pair => (.inl pair.1, pair.2)) := by
  have owner : bindingOwner (liftRegistry state) (.inl actor) key = (bindingOwner state actor key).map Sum.inl := by
    cases found : state actor with
    | none => simp [bindingOwner, found]
    | some row =>
      cases phase : row.phase <;> simp [bindingOwner, found, liftFiber, liftPhase, phase, Phase.committed] <;>
        split <;> simp <;> split <;> rfl
  unfold location
  rw [owner]
  cases atKey : bindingOwner state actor key with
  | none => rfl
  | some name => cases live : state name <;> simp [live, liftFiber, Option.map_map, Function.comp_def]

open OrchestrationSorting (Command)

def liftCommand : Command Name Key Code → Command (Names Name) Key Code
  | .insert name component => .insert (.inl name) component
  | .retire name => .retire (.inl name)
  | .remove name => .remove (.inl name)

def liftEvent : Event Name Key Code → Event (Names Name) Key Code
  | .command command => .command (liftCommand command)
  | .lifecycle kind actor => .lifecycle kind (.inl actor)

omit [DecidableEq Key] in
private theorem lift_command {before after : R} (command : Command Name Key Code) (step : command.Step before after) :
    (liftCommand command).Step (liftRegistry before) (liftRegistry after) := by
  obtain ⟨ready, rfl⟩ := step
  cases command with
  | insert name component => exact ⟨lift_insertable _ _ _ none ready, lift_put _ _ _⟩
  | retire name => exact ⟨by simpa [Command.Enabled, liftCommand] using ready, lift_retire _ _⟩
  | remove name => exact ⟨lift_removable _ _ ready, lift_erase _ _⟩

omit [DecidableEq Name] [DecidableEq Key] in
theorem lift_quiet {state : R} (quiet : Progress.Quiet state) : Progress.Quiet (liftRegistry state) := by
  intro actor row found
  cases actor with
  | inr spare => simp at found
  | inl name =>
    cases old : state name with
    | none => simp [old] at found
    | some entry =>
      have exactRow : liftFiber entry = row := Option.some.inj (by simpa only [lift_registry_inl, old, Option.map_some] using found)
      subst row
      have settled := quiet name entry old
      cases phase : entry.phase with
      | inactive =>
        simp only [liftFiber, phase, liftPhase]
        intro view valid
        let decode : Names Name → Name := Sum.elim id (fun _ => name)
        have target : Target state name (decode ∘ view) := by
          simp only [Target, lift_registry_inl, old, Option.map_some] at valid
          simp only [Target, old]
          refine ⟨valid.1, fun key demand => ?_⟩
          have enabled := valid.2 key demand
          cases owner : view key with
          | inr spare => simp [owner] at enabled
          | inl provider =>
            cases present : state provider <;> simp [Function.comp_apply, owner, decode, present, liftFiber, lift_available] at enabled ⊢
            exact enabled
        exact (show ∀ view, ¬ Target state name view from by rwa [phase] at settled) _ target
      | active word view =>
        have enabled : Target state name view := by simpa only [phase] using settled
        simpa only [liftFiber, phase, liftPhase] using (target_lift_iff state name view).mpr enabled
      | reloading | unloading => simp [phase] at settled

section Typed
variable {V : Key → Type u} {ops : CoeffectOperations V}
variable {program : Code → TypedRegistry.Instruction Name ops Code}
local notation "A" => Scalar ops
local notation "S" => TypedRegistry.RawRegistry Name ops Code
local notation "S'" => TypedRegistry.RawRegistry (Names Name) ops Code

def extendProgram (fallback : Name) (base : Code → TypedRegistry.Instruction Name ops Code) :
    Code → TypedRegistry.Instruction (Names Name) ops Code := fun code =>
  ⟨(match (base code).action with
    | .unit => .unit
    | .provide key value => .provide key value
    | .operate key op argument => .operate key op argument
    | .instantiate component => .instantiate component),
   fun outcome => (base code).next (match outcome with
    | .unit => .unit
    | .provision key value => .provision key value
    | .operation key op result => .operation key op result
    | .child (.inl name) => .child name
    | .child (.inr _) => .child fallback)⟩

private def liftAction : Stages.Action Name Key A Code (PUnit.{u + 1}) →
    Stages.Action (Names Name) Key A Code (PUnit.{u + 1})
  | .unit => .unit
  | .provide key value => .provide key value
  | .operate key run => .operate key run
  | .instantiate part => .instantiate part

private def liftOutcome : Stages.Outcome Name A → Stages.Outcome (Names Name) A
  | .unit => .unit
  | .value value => .value value
  | .child name => .child (.inl name)

omit [DecidableEq Name] in
private theorem extended_action (fallback : Name) (code : Code) :
    (encodeProgram (extendProgram fallback program) code).action = liftAction (encodeProgram program code).action := by
  change TypedRegistry.encodeAction ops (extendProgram fallback program code).action =
    liftAction (TypedRegistry.encodeAction ops (program code).action)
  cases current : (program code).action <;> simp [extendProgram, current, TypedRegistry.encodeAction, liftAction]

omit [DecidableEq Name] in
private theorem extended_next (fallback : Name) (code : Code) (outcome : Stages.Outcome Name A) :
    (encodeProgram (extendProgram fallback program) code).next (liftOutcome outcome) =
      (encodeProgram program code).next outcome := by
  cases outcome with
  | unit | child => rfl
  | value data =>
    cases data with
    | inl value => cases value <;> rfl
    | inr others => cases others <;> rfl

omit [DecidableEq Name] in
/-- The extended child outcomes use the original program's continuation.
On new names the fallback selects the same branch under the contract. -/
theorem extend_child_continuations (fallback : Name)
    (stable : GuardedLandingMatching.ChildContinuations (encodeProgram program)) :
    GuardedLandingMatching.ChildContinuations (encodeProgram (extendProgram fallback program)) := by
  intro code part action child other
  rw [extended_action] at action
  have original : (encodeProgram program code).action = .instantiate part := by
    generalize (encodeProgram program code).action = raw at action ⊢
    cases raw <;> simp [liftAction] at action
    exact congrArg Stages.Action.instantiate action
  cases child <;> cases other <;> exact stable code part original _ _

private theorem lift_performed (fallback : Name) {actor : Name} {code : Code} {before after : S} {token outcome}
    (step : Performed (encodeProgram program) actor code before after token outcome) :
    Performed (encodeProgram (extendProgram fallback program)) (.inl actor) code
      (liftRegistry before) (liftRegistry after) (liftInverse token) (liftOutcome outcome) := by
  cases step with
  | unit _ _ _ action => exact .unit _ _ _ (by rw [extended_action, action]; rfl)
  | provide _ _ _ row key value action found declared empty =>
    rw [lift_write]
    exact .provide _ _ _ (liftFiber row) key value (by rw [extended_action, action]; rfl)
      (by simp [found]) declared empty
  | operate _ _ _ key run owner input output inverse value action located called =>
    rw [lift_write]
    refine .operate _ _ _ key run (Sum.inl owner) input output inverse value ?_ ?_ called
    · rw [extended_action, action]; rfl
    · rw [lift_location, located]; rfl
  | instantiate _ _ _ part child action allowed =>
    rw [lift_put]
    refine .instantiate _ _ _ part (Sum.inl child) ?_ (lift_insertable _ _ _ _ allowed)
    rw [extended_action, action]; rfl

private theorem lift_landing (fallback : Name) {actor : Name} {code : Code} {before after : S} {token next}
    (step : Land (encodeProgram program) actor code before after token next) :
    Land (encodeProgram (extendProgram fallback program)) (.inl actor) code
      (liftRegistry before) (liftRegistry after) (liftInverse token) next := by
  obtain ⟨outcome, performed, result⟩ := Renaming.land_has_outcome (encodeProgram program) step
  have mapped := (lift_performed fallback performed).toLand (encodeProgram (extendProgram fallback program))
  rwa [extended_next, result] at mapped

private theorem lift_activation (fallback : Name) {before after : S} {rule : Labeled.Rule} {actor : Name}
    (step : Labeled.Step (encodeProgram program) rule actor before after) (activation : Transposition.Activation rule) :
    Labeled.Step (encodeProgram (extendProgram fallback program)) rule (.inl actor) (liftRegistry before) (liftRegistry after) := by
  cases step with
  | begin _ _ row view found phase free target =>
    rw [lift_mark]
    exact .begin _ _ (liftFiber row) (Sum.inl ∘ view) (by simp [found]) (by simp [liftFiber, phase, liftPhase])
      (by simp [ErrorFree, found]) ((target_lift_iff _ _ _).mpr target)
  | iter _ middle _ row code word view token next found phase target landed =>
    rw [lift_mark]
    exact .iter _ _ _ (liftFiber row) code (word.map liftInverse) (Sum.inl ∘ view) (liftInverse token) next
      (by simp [found]) (by simp [liftFiber, phase, liftPhase]) ((target_lift_iff _ _ _).mpr target) (lift_landing fallback landed)
  | finish _ middle _ row code word view token found phase target landed =>
    rw [lift_mark]
    exact .finish _ _ _ (liftFiber row) code (word.map liftInverse) (Sum.inl ∘ view) (liftInverse token)
      (by simp [found]) (by simp [liftFiber, phase, liftPhase]) ((target_lift_iff _ _ _).mpr target) (lift_landing fallback landed)
  | _ => simp [Transposition.Activation] at activation

/-- The embedded history executes the original events and draws on the old
names. Added names are absent from every registry of this history. -/
def extendTrace {last : Nat} (trace : Trace (encodeProgram program) last) (fallback : Name)
    (openOnly : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last)) :
    Trace (encodeProgram (extendProgram fallback program)) last where
  state cut := liftRegistry (trace.state cut)
  event cut := liftEvent (trace.event cut)
  notes cut := Vestigial.cutNotes (fun time => liftRegistry (trace.state time))
    (fun time => Vestigial.eventActor (liftEvent (trace.event time))) cut
  start := by rw [trace.start]; funext name; cases name <;> rfl
  seed := by
    apply Prod.ext
    · funext name
      change (liftRegistry (trace.state 0) name).map (fun _ => 0) = none
      rw [trace.start]
      cases name <;> rfl
    · rfl
  step time bounded := by
    refine ⟨?_, rfl⟩
    cases event : trace.event time with
    | command cmd =>
      have step := (trace.step time bounded).1
      rw [event] at step
      exact lift_command cmd step
    | lifecycle kind actor =>
      obtain ⟨activation, step⟩ := trace.activation_at openOnly quiet bounded event
      have ordinary : kind ≠ .unload := by
        intro same
        subst kind
        simp [Transposition.Activation, Lifecycle.rule] at activation
      exact lifecycle_transition ordinary (lift_activation fallback step activation)

theorem extend_trace_open {last : Nat} (trace : Trace (encodeProgram program) last) (fallback : Name)
    (openOnly : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last)) :
    ¬ Nonempty (ClosedEpisode (extendTrace trace fallback openOnly quiet)) := by
  rintro ⟨episode⟩
  have unload := (unload_boundary (extendTrace trace fallback openOnly quiet) episode.interval).1
  have bounded := episode.interval.bounded
  change liftEvent (trace.event episode.closed) = .lifecycle .unload episode.name at unload
  cases source : trace.event episode.closed with
  | command => simp [liftEvent, source] at unload
  | lifecycle kind name =>
    have same : kind = .unload := (Event.lifecycle.inj (by simpa only [source, liftEvent] using unload)).1
    subst kind
    exact trace.no_unload openOnly bounded source

theorem extend_trace_tags {last : Nat} (trace : Trace (encodeProgram program) last) (fallback : Name)
    (openOnly : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    {cut : Nat} (bounded : cut ≤ last) (name : Name) :
    ((extendTrace trace fallback openOnly quiet).notes cut).1 (.inl name) = (trace.notes cut).1 name := by
  rw [trace.notes_eq cut bounded]
  change Incarnation.birthAt (fun time => liftRegistry (trace.state time)) (.inl name) cut = Incarnation.birthAt trace.state name cut
  induction cut with
  | zero => cases found : trace.state 0 name <;> simp [Incarnation.birthAt, found]
  | succ cut ih =>
    rw [Incarnation.birthAt, Incarnation.birthAt, ih (by omega)]
    cases found : trace.state (cut + 1) name <;> simp [found]

theorem extend_birth_address {last : Nat} (trace : Trace (encodeProgram program) last) (fallback : Name)
    (openOnly : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    {birth : Nat} {path : Address} (address : Addressed trace birth path) :
    Addressed (extendTrace trace fallback openOnly quiet) birth path := by
  let extended := extendTrace trace fallback openOnly quiet
  have rootTest (cut : Nat) : isRootInsertion extended cut = isRootInsertion trace cut := by
    have label : extended.event cut = liftEvent (trace.event cut) := rfl
    rw [isRootInsertion, isRootInsertion, label]
    cases event : trace.event cut with
    | command cmd => cases cmd <;> rfl
    | lifecycle => rfl
  have rule (cut : Nat) : extended.rule cut = trace.rule cut := by
    change eventRule (liftEvent (trace.event cut)) = eventRule (trace.event cut)
    cases event : trace.event cut with
    | command cmd => cases cmd <;> rfl
    | lifecycle => rfl
  have actor (cut : Nat) : extended.actor cut = .inl (trace.actor cut) := by
    change Vestigial.eventActor (liftEvent (trace.event cut)) = .inl (Vestigial.eventActor (trace.event cut))
    cases event : trace.event cut with
    | command cmd => cases cmd <;> rfl
    | lifecycle => rfl
  have tag (cut : Nat) (bounded : cut ≤ last) : (extended.notes cut).1 (extended.actor cut) = (trace.notes cut).1 (trace.actor cut) := by
    rw [actor]
    exact extend_trace_tags trace fallback openOnly quiet bounded (trace.actor cut)
  have rootCounts : isRootInsertion extended = isRootInsertion trace := funext rootTest
  have stageCounts (stamp : Nat) {time : Nat} (bounded : time ≤ last) :
      occurrencesBefore (isParentStage extended stamp) time = occurrencesBefore (isParentStage trace stamp) time := by
    induction time with
    | zero => rfl
    | succ time ih =>
      rw [occurrencesBefore, occurrencesBefore, ih (by omega), isParentStage, isParentStage, rule, tag time (by omega)]
  change Addressed extended birth path
  induction address with
  | @root cut name part inside event =>
    have moved : extended.event cut = .command (.insert (.inl name) part) := by
      change liftEvent (trace.event cut) = _
      rw [event]
      rfl
    simpa only [rootCounts] using Addressed.root inside moved
  | @child cut parentBirth child path inside allocation vacant born stamp parent ih =>
    have empty : extended.state cut (.inl child) = none := by
      change (trace.state cut child).map liftFiber = none
      simp [vacant]
    have present : extended.state (cut + 1) (.inl child) ≠ none := by
      change (trace.state (cut + 1) child).map liftFiber ≠ none
      simpa using born
    have childBirth := Addressed.child inside ((rule cut).symm ▸ allocation) empty present
      ((tag cut (by omega)).trans stamp) ih
    simpa only [stageCounts parentBirth (by omega : cut ≤ last)] using childBirth

theorem extend_addressedEvents {last : Nat} (trace : Trace (encodeProgram program) last) (fallback : Name)
    (opened : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last)) :
    addressedEvents (extendTrace trace fallback opened quiet) = addressedEvents trace := by
  let extended := extendTrace trace fallback opened quiet
  unfold addressedEvents
  apply List.map_congr_left
  intro cut member
  have bounded := List.mem_range.mp member
  have actor : extended.actor cut = .inl (trace.actor cut) := by
    change Vestigial.eventActor (liftEvent (trace.event cut)) = .inl (Vestigial.eventActor (trace.event cut))
    cases event : trace.event cut with
    | command cmd => cases cmd <;> rfl
    | lifecycle => rfl
  have tag : (extended.notes cut).1 (extended.actor cut) = (trace.notes cut).1 (trace.actor cut) := by
    rw [actor]
    exact extend_trace_tags trace fallback opened quiet (Nat.le_of_lt bounded) (trace.actor cut)
  have addressed : actorAddress extended cut = actorAddress trace cut := by
    unfold actorAddress
    rw [tag]
    cases found : (trace.notes cut).1 (trace.actor cut) with
    | none => rfl
    | some birth =>
      obtain ⟨path, source⟩ := exists_address trace (GuardedBirthMatching.recorded_birth trace (Nat.le_of_lt bounded) found).1
      have lifted := extend_birth_address trace fallback opened quiet source
      exact ((addressOf_eq_some extended).mpr lifted).trans ((addressOf_eq_some trace).mpr source).symm
  change addressedEventAt extended cut = addressedEventAt trace cut
  have event : extended.event cut = liftEvent (trace.event cut) := rfl
  simp only [addressedEventAt, event, addressed]
  cases trace.event cut with
  | command cmd => cases cmd <;> rfl
  | lifecycle => rfl

def liftAddressedCommand : AddressedCommand Name Key Code → AddressedCommand (Names Name) Key Code
  | .insert name component => .insert (.inl name) component
  | .retire target component => .retire target component
  | .remove target component => .remove target component

/-- Embedding leaves every birth path and command component intact. Root
insertions carry the original names into the original-name summand. -/
theorem extend_trace_input {last : Nat} (trace : Trace (encodeProgram program) last) (fallback : Name)
    (openOnly : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last)) :
    orchestrationInput (extendTrace trace fallback openOnly quiet) = (orchestrationInput trace).map liftAddressedCommand := by
  let extended := extendTrace trace fallback openOnly quiet
  have mappedTarget {cut : Nat} (bounded : cut < last) {name : Name} {path : Address} {component : Component Key Code}
      (found : targetAt trace cut name = some (path, component)) :
      targetAt extended cut (.inl name) = some (path, component) := by
    obtain ⟨birth, row, live, known, present, payload⟩ := (targetAt_eq_some trace).mp found
    refine (targetAt_eq_some extended).mpr ⟨birth, liftFiber row,
      (extend_trace_tags trace fallback openOnly quiet (Nat.le_of_lt bounded) name).trans live,
      extend_birth_address trace fallback openOnly quiet known, ?_, payload⟩
    change (trace.state cut name).map liftFiber = some (liftFiber row)
    simp [present]
  have steps (cut : Nat) (bounded : cut < last) : commandAt extended cut = (commandAt trace cut).map liftAddressedCommand := by
    have label : extended.event cut = liftEvent (trace.event cut) := rfl
    cases event : trace.event cut with
    | lifecycle => simp [commandAt, label, event, liftEvent]
    | command cmd =>
      cases cmd with
      | insert => simp [commandAt, label, event, liftEvent, liftCommand, liftAddressedCommand]
      | retire name =>
        obtain ⟨_, _, found⟩ := targetAt_command trace bounded (.inl event)
        simp [commandAt, label, event, liftEvent, liftCommand, liftAddressedCommand, found, mappedTarget bounded found]
      | remove name =>
        obtain ⟨_, _, found⟩ := targetAt_command trace bounded (.inr event)
        simp [commandAt, label, event, liftEvent, liftCommand, liftAddressedCommand, found, mappedTarget bounded found]
  change orchestrationInput extended = _
  unfold orchestrationInput
  rw [List.map_filterMap]
  have maps : (List.range last).map (commandAt extended) =
      (List.range last).map (fun cut => (commandAt trace cut).map liftAddressedCommand) := by
    apply List.map_congr_left
    exact fun i member => steps i (List.mem_range.mp member)
  simpa only [List.filterMap_map, Function.id_comp, Function.comp_apply] using congrArg (List.filterMap id) maps

end Typed

omit [DecidableEq Name] [DecidableEq Key] in
theorem extended_name_supply (used : List (Names Name)) : ∃ spare, spare ∉ used := by
  have bounded : ∃ limit : Nat, ∀ n, Sum.inr n ∈ used → n < limit := by
    induction used with
    | nil => exact ⟨0, fun _ absent => False.elim (List.not_mem_nil absent)⟩
    | cons head tail ih =>
      obtain ⟨limit, smaller⟩ := ih
      cases head with
      | inl name =>
        refine ⟨limit, fun n member => ?_⟩
        rcases List.mem_cons.mp member with wrong | inside
        · cases wrong
        · exact smaller n inside
      | inr index =>
        refine ⟨max limit (index + 1), fun n member => ?_⟩
        rcases List.mem_cons.mp member with same | inside
        · have equal := Sum.inr.inj same
          omega
        · have previous := smaller n inside
          omega
  obtain ⟨limit, below⟩ := bounded
  exact ⟨.inr limit, fun found => (Nat.lt_irrefl _) (below limit found)⟩

omit [DecidableEq Name] [DecidableEq Key] in
private theorem project_lift (state : R) : project (liftRegistry state) = liftRegistry (project state) := by
  funext name
  cases name with
  | inr spare => rfl
  | inl actor =>
    have view (required : Key → Bool) (chosen : View Name Key) :
        requiredView (Sum.inl actor : Names Name) required (Sum.inl ∘ chosen) = Sum.inl ∘ requiredView actor required chosen := by
      funext key
      cases need : required key <;> simp [requiredView, need]
    cases found : state actor with
    | none => simp [project, found]
    | some row =>
      have same : projectFiber (.inl actor) (liftFiber row) = liftFiber (projectFiber actor row) := by
        cases status : row.phase <;> simp [projectFiber, projectPhase, liftFiber, liftPhase, status, view]
      simp only [project, lift_registry_inl, found, Option.map_some, same]

omit [DecidableEq Key] in
private theorem restrict_live_permutation {state : R} (finite : SupportUniqueness.FiniteDomain state)
    (p : Renaming.Permutation (Names Name))
    (intoOld : ∀ name, state name ≠ none → ∃ target, p.toFun (.inl name) = .inl target) :
    ∃ q : Renaming.Permutation Name, ∀ name, state name ≠ none → p.toFun (.inl name) = .inl (q.toFun name) := by
  obtain ⟨used, covers⟩ := finite
  let pair (name : Name) : Option (Name × Name) :=
    match p.toFun (.inl name) with
    | .inl target => some (name, target)
    | .inr _ => none
  let pairs := used.filterMap pair
  have sound {name target : Name} (member : (name, target) ∈ pairs) : p.toFun (.inl name) = .inl target := by
    obtain ⟨source, _, found⟩ := List.mem_filterMap.mp member
    unfold pair at found
    split at found
    · rename_i actual _ located
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj found)
      exact located
    · cases found
  obtain ⟨q, eq⟩ := GuardedBirthMatching.extend_pairs pairs
    (fun a b => Sum.inl.inj ((sound a).symm.trans (sound b)))
    (fun a b => Sum.inl.inj (p.injective ((sound a).trans (sound b).symm)))
  refine ⟨q, ?_⟩
  intro name live
  obtain ⟨target, maps⟩ := intoOld name live
  have seen : name ∈ used := by
    cases present : state name with
    | none => exact False.elim (live present)
    | some row => exact covers name row present
  have listed : (name, target) ∈ pairs := List.mem_filterMap.mpr ⟨name, seen, by simp [pair, maps]⟩
  exact maps.trans (congrArg Sum.inl (eq listed).symm)

omit [DecidableEq Name] [DecidableEq Key] in
private theorem lift_related_stack [Setoid Value] {first second : List (Inverse Name Key Value)}
    (related : StageSimulation.StackRelated (first.map liftInverse) (second.map liftInverse)) :
    StageSimulation.StackRelated first second := by
  induction first generalizing second with
  | nil => cases second <;> cases related; exact .nil
  | cons token rest ih =>
    cases second with
    | nil => cases related
    | cons other remaining =>
      change StageSimulation.StackRelated (liftInverse token :: rest.map liftInverse)
        (liftInverse other :: remaining.map liftInverse) at related
      cases related with
      | cons head tail =>
        apply StageSimulation.StackRelated.cons _ (ih tail)
        cases token <;> cases other <;> simp only [liftInverse] at head <;> cases head <;> constructor <;> assumption

omit [DecidableEq Name] [DecidableEq Key] in
private theorem lift_related_phase [Setoid Value]
    {first second : Phase Name Key Code (Inverse Name Key Value)}
    (related : StageSimulation.PhaseRelated Eq (liftPhase first) (liftPhase second)) :
    StageSimulation.PhaseRelated Eq first second := by
  classical
  have views {a b : View Name Key} (eq : (Sum.inl ∘ a : View (Names Name) Key) = Sum.inl ∘ b) : a = b :=
    funext (fun key => Sum.inl.inj (congrFun eq key))
  have shapes := related.observed.1
  cases first <;> cases second <;> simp only [liftPhase, GuardObservations.phaseKind] at shapes related
  all_goals try omega
  · exact .inactive
  · obtain ⟨_, _, equal, code, words⟩ := StageSimulation.phase_reloading related
    obtain ⟨sameCode, sameWord, viewEq⟩ := Phase.reloading.inj equal
    rw [← sameWord] at words
    cases views viewEq
    exact .reloading _ (code.trans sameCode.symm) (lift_related_stack words)
  · obtain ⟨_, equal, words⟩ := StageSimulation.phase_active related
    obtain ⟨sameWord, viewEq⟩ := Phase.active.inj equal
    rw [← sameWord] at words
    cases views viewEq
    exact .active _ (lift_related_stack words)
  · obtain ⟨_, equal, words⟩ := StageSimulation.phase_unloading related
    obtain ⟨sameWord, viewEq⟩ := Phase.unloading.inj equal
    rw [← sameWord] at words
    cases views viewEq
    exact .unloading _ (lift_related_stack words)

omit [DecidableEq Name] [DecidableEq Key] in
private theorem lift_related_fiber [Setoid Value] {first second : F}
    (related : StageSimulation.FiberRelated Eq (liftFiber first) (liftFiber second)) :
    StageSimulation.FiberRelated Eq first second := by
  refine ⟨related.component, ?_, related.retired, lift_related_phase related.phase, related.table⟩
  have parent := related.parent
  change first.parent.map Sum.inl = second.parent.map Sum.inl at parent
  cases a : first.parent <;> cases b : second.parent <;> simp_all

omit [DecidableEq Name] [DecidableEq Key] in
private theorem rename_projected_lift {state : R} (closed : Safety.ParentClosed state) (supported : Ordering.Supported state)
    {actor : Name} {row : F} (found : state actor = some row)
    (p : Renaming.Permutation (Names Name)) (q : Renaming.Permutation Name)
    (fixed : ∀ name, state name ≠ none → p.toFun (.inl name) = .inl (q.toFun name)) :
    Renaming.fiber p (liftFiber (projectFiber actor row)) = liftFiber (Renaming.fiber q (projectFiber actor row)) := by
  classical
  have parent : (row.parent.map Sum.inl).map p.toFun = (row.parent.map q.toFun).map Sum.inl := by
    cases declared : row.parent with
    | none => rfl
    | some owner => exact congrArg some (fixed owner (closed actor row owner found declared))
  have view (chosen : View Name Key) (committed : row.phase.committed = some chosen) :
      Renaming.view p (Sum.inl ∘ requiredView actor row.component.requires chosen) =
        Sum.inl ∘ Renaming.view q (requiredView actor row.component.requires chosen) := by
    funext key
    change p.toFun (.inl (requiredView actor row.component.requires chosen key)) =
      .inl (q.toFun (requiredView actor row.component.requires chosen key))
    apply fixed
    by_cases required : row.component.requires key = true
    · obtain ⟨_, provider, present, _, _⟩ := Ordering.retained_provider state actor row chosen key supported found committed required
      simp [requiredView, required, present]
    · simp [requiredView, required, found]
  cases status : row.phase <;>
    simp only [Renaming.fiber, liftFiber, projectFiber, status, projectPhase, liftPhase, Renaming.phase, List.map_nil, parent]
  all_goals rw [view _ (by rw [status]; rfl)]

omit [DecidableEq Key] in
/-- An agreement in the larger name set restricts to a permutation of the
original names. The original endpoint's finite live correspondence fixes
every parent and required provider mentioned by the projected rows. -/
theorem reflect_projected_agreement [Setoid Value] {left right : R}
    (finite : SupportUniqueness.FiniteDomain left) (closed : Safety.ParentClosed left)
    (supported : Ordering.Supported left) (compared : ProjectedAgreement (liftRegistry left) (liftRegistry right)) :
    ProjectedAgreement left right := by
  obtain ⟨p, relation⟩ := compared
  rw [project_lift, project_lift] at relation
  have presence (name : Names Name) : liftRegistry (project left) name = none ↔
      liftRegistry (project right) (p.toFun name) = none := by
    have atName := relation (p.toFun name)
    rw [Renaming.registry_at] at atName
    cases l : liftRegistry (project left) name <;> cases r : liftRegistry (project right) (p.toFun name) <;>
      simp_all [Iterators.OptionRel]
  have intoOld (name : Name) (live : left name ≠ none) : ∃ target, p.toFun (.inl name) = .inl target := by
    cases mapped : p.toFun (.inl name) with
    | inl target => exact ⟨target, rfl⟩
    | inr spare =>
      have absent := (presence (.inl name)).mpr (by rw [mapped]; rfl)
      exact False.elim (live ((project_present _ _).mp (by simpa using absent)))
  obtain ⟨q, names⟩ := restrict_live_permutation finite p intoOld
  refine ⟨q, fun query => ?_⟩
  obtain ⟨name, rfl⟩ := q.surjective query
  rw [Renaming.registry_at]
  cases l : left name with
  | none =>
    have rAbsent : right (q.toFun name) = none := by
      cases r : right (q.toFun name) with
      | none => rfl
      | some row =>
        obtain ⟨old, image⟩ := p.surjective (.inl (q.toFun name))
        have oldLive : liftRegistry (project left) old ≠ none := by
          intro absent
          have wrong := (presence old).mp absent
          rw [image] at wrong
          simp [project, r] at wrong
        cases old with
        | inr spare => exact False.elim (oldLive rfl)
        | inl source =>
          have live : left source ≠ none := by
            intro missing
            exact oldLive (by simp [project, missing])
          have same := q.injective (Sum.inl.inj ((names source live).symm.trans image))
          exact False.elim (live (same.symm ▸ l))
    simp [project, l, rAbsent, Iterators.OptionRel]
  | some old =>
    have mapped := names name (by simp [l])
    have atName := relation (p.toFun (.inl name))
    rw [Renaming.registry_at, mapped] at atName
    cases r : right (q.toFun name) with
    | none => simp [project, l, r, Iterators.OptionRel] at atName
    | some row =>
      have sameFiber := rename_projected_lift closed supported l p q names
      simp only [lift_registry_inl, project, l, r, Option.map_some, Iterators.OptionRel, sameFiber] at atName ⊢
      exact lift_related_fiber atName

section TypedConfluence
open PaperEffectEquations (ValueOperationWitness)
open PaperObservationEquations (OperationRespects)
open PartialCoeffectIndependenceContracts (tableSetoid)
open GuardedLandingMatching (ChildContinuations)
variable {V : Key → Type u} {ops : CoeffectOperations V}
variable {program : Code → TypedRegistry.Instruction Name ops Code}

private theorem lift_active_endpoint {length : Nat} (trace : Trace (encodeProgram program) length)
    (fallback : Name) (opened : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state length))
    {address : Address} {name : Name}
    {row : Fiber Name Key (Scalar ops) Code (Inverse Name Key (Scalar ops)) PUnit.{u + 1}}
    (active : ActiveEndpoint trace address name row) :
    ActiveEndpoint (extendTrace trace fallback opened quiet) address (.inl name) (liftFiber row) := by
  obtain ⟨found, ready, birth, tag, known⟩ := active
  exact ⟨by change (trace.state length name).map liftFiber = _; rw [found]; rfl,
    (lift_available _).mpr ready, birth,
    (extend_trace_tags trace fallback opened quiet (Nat.le_refl _) name).trans tag,
    extend_birth_address trace fallback opened quiet known⟩

/-- Confluence, including the comparison of actual rows by active birth address.
The auxiliary names are used only to prove the endpoint comparison, whose
permutation acts on the original name set. -/
theorem compare_open_endpoints_addressed {leftLength rightLength : Nat}
    (left : Trace (encodeProgram program) leftLength) (right : Trace (encodeProgram program) rightLength)
    (leftOpen : ¬ Nonempty (ClosedEpisode left)) (leftQuiet : Progress.Quiet (left.state leftLength))
    (rightOpen : ¬ Nonempty (ClosedEpisode right)) (rightQuiet : Progress.Quiet (right.state rightLength))
    (stable : ChildContinuations (encodeProgram program)) (input : orchestrationInput left = orchestrationInput right)
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r) :
    letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
    leftLength = rightLength ∧ ProjectedAgreement (left.state leftLength) (right.state rightLength) ∧
      (addressedEvents left).Perm (addressedEvents right) ∧
      (∀ {address name peer row other}, ActiveEndpoint left address name row →
        ActiveEndpoint right address peer other → row.component = other.component ∧
          ∀ key, Iterators.OptionRel (fun a b : Scalar ops => a ≈ b) (row.table key) (other.table key)) := by
  letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
  let fallback := left.actor 0
  let first := extendTrace left fallback leftOpen leftQuiet
  let second := extendTrace right fallback rightOpen rightQuiet
  have word : orchestrationInput first = orchestrationInput second := by
    exact (extend_trace_input left fallback leftOpen leftQuiet).trans
      ((congrArg (List.map liftAddressedCommand) input).trans (extend_trace_input right fallback rightOpen rightQuiet).symm)
  obtain ⟨moved, lengths, agreement, order, _, rightEndpoint, _, _, retained, path⟩ :=
    GuardedCompleteAlignment.align_surviving_schedules_with_spare_names first second
      (extend_trace_open left fallback leftOpen leftQuiet) (lift_quiet leftQuiet)
      (extend_trace_open right fallback rightOpen rightQuiet) (lift_quiet rightQuiet)
      (extend_child_continuations fallback stable) word extended_name_supply observe recovery commutative respect
  have leftEndpoint : ProjectedAgreement (first.state leftLength) (moved.state rightLength) := by
    obtain ⟨_, states, _, _⟩ := agreement
    rw [← congrArg moved.state lengths]
    exact .of_rename_eq states
  have transported : ProjectedAgreement (liftRegistry (left.state leftLength)) (liftRegistry (right.state rightLength)) :=
    leftEndpoint.trans rightEndpoint.symm
  have finite := SupportUniqueness.reachable_finite (encodeProgram program)
    (Results.rootTrace (left.toIndexed leftOpen) (left.indexed_roots leftOpen) leftLength (Nat.le_refl _))
  refine ⟨lengths, reflect_projected_agreement finite (left.parent_closed _ (Nat.le_refl _))
    (left.supported _ (Nat.le_refl _)) transported, ?_, ?_⟩
  · have equal : addressedEvents first = addressedEvents moved := by
      subst rightLength
      exact addressedEvents_congr first moved order
    have permuted := (List.Perm.of_eq equal).trans retained
    rw [extend_addressedEvents left fallback leftOpen leftQuiet, extend_addressedEvents right fallback rightOpen rightQuiet] at permuted
    exact permuted
  · intro address name peer row other leftActive rightActive
    subst rightLength
    have lifted := lift_active_endpoint left fallback leftOpen leftQuiet leftActive
    have otherLifted := lift_active_endpoint right fallback rightOpen rightQuiet rightActive
    obtain ⟨_, _, matched, component, tables⟩ := active_endpoint_of_matched_schedule order agreement lifted
    obtain ⟨otherComponent, otherTables⟩ := path.active_endpoint_payload
      (extend_trace_open right fallback rightOpen rightQuiet) (lift_quiet rightQuiet) otherLifted matched
    refine ⟨component.trans otherComponent.symm, fun key => ?_⟩
    have related := Iterators.OptionRel.mono (fun _ _ h => Setoid.symm h)
      (Iterators.OptionRel.symm (otherTables key))
    rw [← tables] at related
    exact related

theorem compare_open_endpoints {leftLength rightLength : Nat}
    (left : Trace (encodeProgram program) leftLength) (right : Trace (encodeProgram program) rightLength)
    (leftOpen : ¬ Nonempty (ClosedEpisode left)) (leftQuiet : Progress.Quiet (left.state leftLength))
    (rightOpen : ¬ Nonempty (ClosedEpisode right)) (rightQuiet : Progress.Quiet (right.state rightLength))
    (stable : ChildContinuations (encodeProgram program)) (input : orchestrationInput left = orchestrationInput right)
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r) :
    letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
    leftLength = rightLength ∧ ProjectedAgreement (left.state leftLength) (right.state rightLength) ∧
      (addressedEvents left).Perm (addressedEvents right) := by
  obtain ⟨lengths, endpoint, events, _⟩ := compare_open_endpoints_addressed left right
    leftOpen leftQuiet rightOpen rightQuiet stable input observe recovery commutative respect
  exact ⟨lengths, endpoint, events⟩

/-- With equal surviving commands, a chain of providers in the reference
orders the corresponding Finish events in the peer. A pending reference
Finish remains outside the peer's matched prefix. -/
theorem peer_finish_of_provider_chain {leftLength rightLength : Nat}
    (left : Trace (encodeProgram program) leftLength) (right : Trace (encodeProgram program) rightLength)
    (leftOpen : ¬ Nonempty (ClosedEpisode left)) (leftQuiet : Progress.Quiet (left.state leftLength))
    (rightOpen : ¬ Nonempty (ClosedEpisode right)) (rightQuiet : Progress.Quiet (right.state rightLength))
    (stable : ChildContinuations (encodeProgram program)) (input : orchestrationInput left = orchestrationInput right)
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r)
    {start firstCut secondCut : Nat}
    (pending : start ≤ firstCut) (firstBound : firstCut < leftLength) (secondBound : secondCut < rightLength)
    (past : ∀ i, i < start → addressedEventAt left i = addressedEventAt right i)
    {provider consumer : Address} (chain : Relation.TransGen (EndpointProvider left) provider consumer)
    (firstFinish : addressedEventAt left firstCut = some (.lifecycle .finish provider))
    (secondFinish : addressedEventAt right secondCut = some (.lifecycle .finish consumer)) :
    ∃ cut, start ≤ cut ∧ cut < secondCut ∧
      addressedEventAt right cut = some (.lifecycle .finish provider) := by
  letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
  obtain ⟨_, _, events, payload⟩ := compare_open_endpoints_addressed left right
    leftOpen leftQuiet rightOpen rightQuiet stable input observe recovery commutative respect
  have peerChain := endpoint_provider_chain_of_comparison leftOpen leftQuiet rightOpen rightQuiet events
    (fun first second => (payload first second).1) chain
  have member : some (.lifecycle .finish provider) ∈ addressedEvents left :=
    List.mem_map.mpr ⟨firstCut, List.mem_range.mpr firstBound, firstFinish⟩
  obtain ⟨cut, inside, event⟩ := List.mem_map.mp (events.mem_iff.mp member)
  exact ⟨cut, finish_after_matched_prefix leftOpen leftQuiet pending firstBound past firstFinish event,
    addressed_finish_lt_of_provider_chain right rightOpen rightQuiet peerChain
      (List.mem_range.mp inside) secondBound event secondFinish, event⟩

/-- Advance the reference's frontier provider stage in the peer when a
dependency chain forces it before a Finish in the peer's command-free prefix. -/
theorem align_provider_chain_before_peer_finish {leftLength rightLength : Nat}
    (left : Trace (encodeProgram program) leftLength) (right : Trace (encodeProgram program) rightLength)
    (leftOpen : ¬ Nonempty (ClosedEpisode left)) (leftQuiet : Progress.Quiet (left.state leftLength))
    (rightOpen : ¬ Nonempty (ClosedEpisode right)) (rightQuiet : Progress.Quiet (right.state rightLength))
    (stable : ChildContinuations (encodeProgram program)) (input : orchestrationInput left = orchestrationInput right)
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r)
    {start firstCut secondCut : Nat}
    (pending : start ≤ firstCut) (firstBound : firstCut < leftLength) (secondBound : secondCut < rightLength)
    (current : GuardedScheduleMatching.CutAgreement left right start)
    (past : ∀ i, i < start → addressedEventAt left i = addressedEventAt right i)
    {provider consumer : Address} (chain : Relation.TransGen (EndpointProvider left) provider consumer)
    (firstFinish : addressedEventAt left firstCut = some (.lifecycle .finish provider))
    (secondFinish : addressedEventAt right secondCut = some (.lifecycle .finish consumer))
    (block : ∀ i, start ≤ i → i < secondCut → ∃ kind name, right.event i = .lifecycle kind name)
    {kind : Lifecycle} {actor : Name} (frontier : left.event start = .lifecycle kind actor)
    (finish : left.event firstCut = .lifecycle .finish actor) :
    letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
    ∃ moved : Trace (encodeProgram program) rightLength,
      (∀ i, i < start + 1 → addressedEventAt left i = addressedEventAt moved i) ∧
      GuardedScheduleMatching.CutAgreement left moved (start + 1) ∧
      (¬ Nonempty (ClosedEpisode moved)) ∧ Progress.Quiet (moved.state rightLength) ∧
      GuardedCompleteAlignment.ScheduleAlignmentPath right moved := by
  letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
  obtain ⟨cut, lower, earlier, addressed⟩ := peer_finish_of_provider_chain left right
    leftOpen leftQuiet rightOpen rightQuiet stable input observe recovery commutative respect
    pending firstBound secondBound past chain firstFinish secondFinish
  obtain ⟨name, birth, event, tag, source⟩ := (addressed_finish_at left).mp firstFinish
  have same := (Event.lifecycle.inj (event.symm.trans finish)).2
  subst name
  have stamp := left.activation_stamp_through leftOpen leftQuiet (by omega) pending (Nat.le_of_lt firstBound) frontier
  obtain ⟨_, _, peerEvent, peerTag, peerAddress⟩ := (addressed_finish_at right).mp addressed
  obtain ⟨moved, _, order, agreement, _, endpoint, opened, quiet, path⟩ :=
    GuardedActivationAlignment.align_pending_parent_before_required_stage left right (by omega) (by omega) lower
      leftOpen leftQuiet rightOpen rightQuiet current stable past input frontier peerEvent
      (stamp.trans tag) peerTag source peerAddress
      (fun i lo hi => block i lo (by omega)) observe recovery commutative respect
  exact ⟨moved, order, agreement, opened, quiet, .activation path endpoint⟩

/-- If the frontier lies on a mixed prerequisite chain to an
activation in the peer's command-free prefix, advance its matching
activation within the original name set. -/
theorem align_frontier_of_mixed_prerequisites {leftLength rightLength start leftCut rightCut : Nat}
    (left : Trace (encodeProgram program) leftLength) (right : Trace (encodeProgram program) rightLength)
    (leftOpen : ¬ Nonempty (ClosedEpisode left)) (leftQuiet : Progress.Quiet (left.state leftLength))
    (rightOpen : ¬ Nonempty (ClosedEpisode right)) (rightQuiet : Progress.Quiet (right.state rightLength))
    (stable : ChildContinuations (encodeProgram program)) (input : orchestrationInput left = orchestrationInput right)
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r)
    (leftBound : leftCut < leftLength) (rightStart : start ≤ rightCut) (rightBound : rightCut < rightLength)
    (current : GuardedScheduleMatching.CutAgreement left right start)
    (past : ∀ i, i < start → addressedEventAt left i = addressedEventAt right i)
    {kind otherKind : Lifecycle} {actor peer : Name}
    (frontier : left.event start = .lifecycle kind actor)
    (later : right.event rightCut = .lifecycle otherKind peer)
    (actors : actorAddress left leftCut = actorAddress right rightCut)
    (chain : Relation.TransGen (GuardedReservationAlignment.ActivationPrerequisite left) start leftCut)
    (block : ∀ i, start ≤ i → i < rightCut → ∃ label name, right.event i = .lifecycle label name) :
    letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
    ∃ moved : Trace (encodeProgram program) rightLength,
      (∀ i, i < start + 1 → addressedEventAt left i = addressedEventAt moved i) ∧
      GuardedScheduleMatching.CutAgreement left moved (start + 1) ∧
      (¬ Nonempty (ClosedEpisode moved)) ∧ Progress.Quiet (moved.state rightLength) ∧
      GuardedCompleteAlignment.ScheduleAlignmentPath right moved := by
  letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
  obtain ⟨_, _, events, payload⟩ := compare_open_endpoints_addressed left right
    leftOpen leftQuiet rightOpen rightQuiet stable input observe recovery commutative respect
  have before := GuardedReservationAlignment.ActivationPrerequisite.chain_lt chain
  obtain ⟨cut, _, name, lower, earlier, step, matched, _⟩ :=
    GuardedReservationAlignment.ActivationPrerequisite.peer_chain leftOpen leftQuiet rightOpen rightQuiet
      events (fun first second => (payload first second).1) (Nat.le_refl _) leftBound
      rightStart rightBound past later actors chain
  obtain ⟨_, address, _, resolved, _⟩ := active_endpoint_of_activation left leftOpen leftQuiet (by omega) frontier
  obtain ⟨birth, tag, known⟩ := (actorAddress_eq_some left).mp resolved
  obtain ⟨peerBirth, peerTag, peerKnown⟩ := (actorAddress_eq_some right).mp (matched.symm.trans resolved)
  have owner : left.actor start = actor := by simp [Trace.actor, Vestigial.eventActor, frontier]
  have peerOwner : right.actor cut = name := by simp [Trace.actor, Vestigial.eventActor, step]
  obtain ⟨moved, _, order, agreement, _, endpoint, opened, quiet, path⟩ :=
    GuardedActivationAlignment.align_pending_parent_before_required_stage left right (by omega) (by omega) lower
      leftOpen leftQuiet rightOpen rightQuiet current stable past input frontier step
      (owner ▸ tag) (peerOwner ▸ peerTag) known peerKnown
      (fun i lo hi => block i lo (by omega)) observe recovery commutative respect
  exact ⟨moved, order, agreement, opened, quiet, .activation path endpoint⟩

/-- A matching downstream activation in two command-free blocks
supplies a legal common first move. Find a ready predecessor, move
its first activation in the reference, then align the peer to it. -/
theorem align_ready_prerequisite_in_both_histories {leftLength rightLength start leftCut rightCut : Nat}
    (left : Trace (encodeProgram program) leftLength) (right : Trace (encodeProgram program) rightLength)
    (leftOpen : ¬ Nonempty (ClosedEpisode left)) (leftQuiet : Progress.Quiet (left.state leftLength))
    (rightOpen : ¬ Nonempty (ClosedEpisode right)) (rightQuiet : Progress.Quiet (right.state rightLength))
    (stable : ChildContinuations (encodeProgram program)) (input : orchestrationInput left = orchestrationInput right)
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r)
    (leftStart : start ≤ leftCut) (leftBound : leftCut < leftLength)
    (rightStart : start ≤ rightCut) (rightBound : rightCut < rightLength)
    (past : ∀ i, i < start → addressedEventAt left i = addressedEventAt right i)
    {kind otherKind : Lifecycle} {actor peer : Name} {address : Address}
    (first : left.event leftCut = .lifecycle kind actor)
    (second : right.event rightCut = .lifecycle otherKind peer)
    (leftAddress : actorAddress left leftCut = some address) (rightAddress : actorAddress right rightCut = some address)
    (leftBlock : ∀ i, start ≤ i → i < leftCut → ∃ label name, left.event i = .lifecycle label name)
    (rightBlock : ∀ i, start ≤ i → i < rightCut → ∃ label name, right.event i = .lifecycle label name) :
    letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
    ∃ (leftMoved : Trace (encodeProgram program) leftLength) (rightMoved : Trace (encodeProgram program) rightLength),
      (∀ i, i < start + 1 → addressedEventAt leftMoved i = addressedEventAt rightMoved i) ∧
      GuardedScheduleMatching.CutAgreement leftMoved rightMoved (start + 1) ∧
      GuardedCompleteAlignment.ScheduleAlignmentPath left leftMoved ∧
      GuardedCompleteAlignment.ScheduleAlignmentPath right rightMoved := by
  letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
  obtain ⟨cut, label, name, provider, view, lower, earlier, event, resolved, target, chain⟩ :=
    GuardedReservationAlignment.activation_prerequisites_to_ready left leftOpen leftQuiet leftStart leftBound
      first leftAddress leftBlock
  have peerStage : ∃ time label name, start ≤ time ∧ time ≤ rightCut ∧
      right.event time = .lifecycle label name ∧ actorAddress right time = some provider := by
    rcases chain with rfl | chain
    · exact ⟨rightCut, otherKind, peer, rightStart, Nat.le_refl _, second,
        rightAddress.trans (leftAddress.symm.trans resolved)⟩
    · obtain ⟨_, _, events, payload⟩ := compare_open_endpoints_addressed left right
        leftOpen leftQuiet rightOpen rightQuiet stable input observe recovery commutative respect
      obtain ⟨time, label, name, afterStart, before, step, addressEq, _⟩ :=
        GuardedReservationAlignment.ActivationPrerequisite.peer_chain leftOpen leftQuiet rightOpen rightQuiet
          events (fun first second => (payload first second).1) lower leftBound rightStart rightBound
          past second (leftAddress.trans rightAddress.symm) chain
      exact ⟨time, label, name, afterStart, Nat.le_of_lt before, step, addressEq.symm.trans resolved⟩
  obtain ⟨time, peerLabel, peerName, peerLower, peerUpper, peerEvent, peerAddress⟩ := peerStage
  obtain ⟨leftMoved, _, _, movedEvent, prefixEq, movedAddress, commands, endpoint, movedOpen, movedQuiet, leftPath⟩ :=
    GuardedActivationAlignment.pull_first_ready_activation left leftOpen leftQuiet lower (by omega) event target
      (fun i lo hi => leftBlock i lo (by omega)) observe recovery commutative respect
  have aligned (i : Nat) (before : i < start) : addressedEventAt leftMoved i = addressedEventAt right i :=
    (prefixEq i before).symm.trans (past i before)
  have current := GuardedCompleteAlignment.matched_prefix leftMoved right (by omega) (by omega)
    movedOpen movedQuiet rightOpen rightQuiet stable aligned
  obtain ⟨birth, tag, known⟩ := (actorAddress_eq_some leftMoved).mp (movedAddress.trans resolved)
  obtain ⟨otherBirth, otherTag, otherKnown⟩ := (actorAddress_eq_some right).mp peerAddress
  have movedActor : leftMoved.actor start = name := by simp [Trace.actor, Vestigial.eventActor, movedEvent]
  have peerActor : right.actor time = peerName := by simp [Trace.actor, Vestigial.eventActor, peerEvent]
  obtain ⟨rightMoved, _, order, agreement, _, rightEndpoint, _, _, rightPath⟩ :=
    GuardedActivationAlignment.align_pending_parent_before_required_stage leftMoved right (by omega) (by omega)
      peerLower movedOpen movedQuiet rightOpen rightQuiet current stable aligned (commands.trans input)
      movedEvent peerEvent (movedActor ▸ tag) (peerActor ▸ otherTag) known otherKnown
      (fun i lo hi => rightBlock i lo (by omega)) observe recovery commutative respect
  exact ⟨leftMoved, rightMoved, order, agreement, .activation leftPath endpoint, .activation rightPath rightEndpoint⟩

/-- When a command remains after the matched prefix, certified exchanges
in both histories produce a common next event in the original name set.
An immediate command is shared, and a delayed command supplies the
matching allocation from which to search for a ready prerequisite. -/
theorem align_next_event_with_pending_command {leftLength rightLength start time : Nat}
    (left : Trace (encodeProgram program) leftLength) (right : Trace (encodeProgram program) rightLength)
    (leftOpen : ¬ Nonempty (ClosedEpisode left)) (leftQuiet : Progress.Quiet (left.state leftLength))
    (rightOpen : ¬ Nonempty (ClosedEpisode right)) (rightQuiet : Progress.Quiet (right.state rightLength))
    (stable : ChildContinuations (encodeProgram program)) (input : orchestrationInput left = orchestrationInput right)
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r)
    (lower : start ≤ time) (bounded : time < leftLength) (rightBound : start ≤ rightLength)
    (past : ∀ i, i < start → addressedEventAt left i = addressedEventAt right i)
    {command : OrchestrationSorting.Command Name Key Code} (pending : left.event time = .command command) :
    letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
    ∃ (leftMoved : Trace (encodeProgram program) leftLength) (rightMoved : Trace (encodeProgram program) rightLength),
      start < rightLength ∧
      (∀ i, i < start + 1 → addressedEventAt leftMoved i = addressedEventAt rightMoved i) ∧
      GuardedScheduleMatching.CutAgreement leftMoved rightMoved (start + 1) ∧
      GuardedCompleteAlignment.ScheduleAlignmentPath left leftMoved ∧
      GuardedCompleteAlignment.ScheduleAlignmentPath right rightMoved := by
  letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
  obtain ⟨offset, _, externalBound, external, originalBlock⟩ :=
    GuardedCommandAlignment.least_later_command left lower bounded pending
  obtain ⟨first, _, firstNormal, _, firstInput, _, _, firstOpen, firstQuiet, firstPath, _, _, firstPrefix⟩ :=
    GuardedCommandAlignment.push_commands_to_birth_barriers_from left start leftOpen leftQuiet
  obtain ⟨second, _, secondNormal, _, secondInput, _, _, secondOpen, secondQuiet, secondPath, _, _, secondPrefix⟩ :=
    GuardedCommandAlignment.push_commands_to_birth_barriers_from right start rightOpen rightQuiet
  have fromLeft (i : Nat) (before : i < start) : addressedEventAt left i = addressedEventAt first i :=
    (firstPrefix i before (by omega)).symm
  have matched (i : Nat) (before : i < start) : addressedEventAt first i = addressedEventAt second i :=
    ((fromLeft i before).symm.trans (past i before)).trans (secondPrefix i before (by omega)).symm
  have sameInput := firstInput.trans (input.trans secondInput.symm)
  obtain ⟨leftSpan, leftCmd, leftInside, leftEvent, leftBlock⟩ :=
    GuardedCommandAlignment.pending_delayed_command_occurs left first externalBound (by omega)
      fromLeft firstInput.symm external originalBlock
  have current := GuardedCompleteAlignment.matched_prefix first second (by omega) rightBound
    firstOpen firstQuiet secondOpen secondQuiet stable matched
  by_cases immediate : leftSpan = 0
  · have now : first.event start = .command leftCmd := by simpa [immediate] using leftEvent
    have leftBound : start < leftLength := by omega
    obtain ⟨inside, _ , same⟩ := GuardedCommandAlignment.pending_command_at_suffix_birth_frontier
      first second leftBound rightBound secondNormal current matched sameInput now
    refine ⟨first, second, inside, ?_, ?_, .command firstPath, .command secondPath⟩
    · intro i bound
      rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ bound) with rfl | earlier
      · exact same
      · exact matched i earlier
    · exact advance_addressed_cut first second leftBound inside current stable
        (fun event => (first.activation_at firstOpen firstQuiet leftBound event).1)
        (fun event => (second.activation_at secondOpen secondQuiet inside event).1) matched same
  · obtain ⟨rightSpan, rightCmd, rightInside, rightEvent, rightBlock⟩ :=
      GuardedCommandAlignment.pending_delayed_command_occurs first second leftInside rightBound
        matched sameInput leftEvent leftBlock
    have rightPositive : 0 < rightSpan := by
      apply Nat.lt_of_not_ge
      intro zero
      have now : second.event start = .command rightCmd := by
        have same : rightSpan = 0 := by omega
        simpa [same] using rightEvent
      have reverse := GuardedCompleteAlignment.matched_prefix second first rightBound (by omega)
        secondOpen secondQuiet firstOpen firstQuiet stable (fun i before => (matched i before).symm)
      obtain ⟨_, ⟨_, impossible⟩, _⟩ :=
        GuardedCommandAlignment.pending_command_at_suffix_birth_frontier second first (by omega) (by omega)
          firstNormal reverse (fun i before => (matched i before).symm) sameInput.symm now
      obtain ⟨_, _, lifecycle⟩ := leftBlock start (Nat.le_refl _) (by omega)
      rw [lifecycle] at impossible
      cases impossible
    obtain ⟨parent, _, birth, otherBirth, actor, peer, kind, otherKind, _, alloc, otherAlloc,
      tag, otherTag, known, otherKnown, _, _, _, _⟩ :=
      GuardedCommandAlignment.delayed_commands_wait_for_same_allocating_stage first second leftInside rightInside
        (by omega) rightPositive firstNormal secondNormal matched sameInput leftEvent rightEvent leftBlock rightBlock
    have owner : first.actor (start + leftSpan - 1) = actor := by simp [Trace.actor, Vestigial.eventActor, alloc]
    have peerOwner : second.actor (start + rightSpan - 1) = peer := by simp [Trace.actor, Vestigial.eventActor, otherAlloc]
    have address := (actorAddress_eq_some first).mpr ⟨birth, owner.symm ▸ tag, known⟩
    have peerAddress := (actorAddress_eq_some second).mpr ⟨otherBirth, peerOwner.symm ▸ otherTag, otherKnown⟩
    obtain ⟨leftMoved, rightMoved, order, agreement, leftPath, rightPath⟩ :=
      align_ready_prerequisite_in_both_histories first second firstOpen firstQuiet secondOpen secondQuiet stable sameInput
        observe recovery commutative respect (by omega) (by omega) (by omega) (by omega)
        matched alloc otherAlloc address peerAddress (fun i lo hi => leftBlock i lo (by omega))
        (fun i lo hi => rightBlock i lo (by omega))
    exact ⟨leftMoved, rightMoved, by omega, order, agreement,
      .trans (.command firstPath) leftPath, .trans (.command secondPath) rightPath⟩

/-- Any two quiet open survivors with equal addressed commands can
reach a common addressed schedule by certified exchanges. Both paths
stay within the original name set, with no spare-name bound. -/
theorem align_open_histories_in_original_names {leftLength rightLength : Nat}
    (left : Trace (encodeProgram program) leftLength) (right : Trace (encodeProgram program) rightLength)
    (leftOpen : ¬ Nonempty (ClosedEpisode left)) (leftQuiet : Progress.Quiet (left.state leftLength))
    (rightOpen : ¬ Nonempty (ClosedEpisode right)) (rightQuiet : Progress.Quiet (right.state rightLength))
    (stable : ChildContinuations (encodeProgram program)) (input : orchestrationInput left = orchestrationInput right)
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r) :
    letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
    ∃ (leftMoved : Trace (encodeProgram program) leftLength) (rightMoved : Trace (encodeProgram program) rightLength),
      leftLength = rightLength ∧
      (∀ i, i < leftLength → addressedEventAt leftMoved i = addressedEventAt rightMoved i) ∧
      GuardedScheduleMatching.CutAgreement leftMoved rightMoved leftLength ∧
      GuardedCompleteAlignment.ScheduleAlignmentPath left leftMoved ∧
      GuardedCompleteAlignment.ScheduleAlignmentPath right rightMoved := by
  letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
  have align (remaining : Nat) {start : Nat}
      (first : Trace (encodeProgram program) leftLength) (second : Trace (encodeProgram program) rightLength)
      (count : start + remaining = leftLength) (rightBound : start ≤ rightLength)
      (firstOpen : ¬ Nonempty (ClosedEpisode first)) (firstQuiet : Progress.Quiet (first.state leftLength))
      (secondOpen : ¬ Nonempty (ClosedEpisode second)) (secondQuiet : Progress.Quiet (second.state rightLength))
      (sameInput : orchestrationInput first = orchestrationInput second)
      (past : ∀ i, i < start → addressedEventAt first i = addressedEventAt second i) :
      ∃ leftMoved rightMoved, leftLength = rightLength ∧
        (∀ i, i < leftLength → addressedEventAt leftMoved i = addressedEventAt rightMoved i) ∧
        GuardedScheduleMatching.CutAgreement leftMoved rightMoved leftLength ∧
        GuardedCompleteAlignment.ScheduleAlignmentPath first leftMoved ∧
        GuardedCompleteAlignment.ScheduleAlignmentPath second rightMoved := by
    induction remaining generalizing start first second with
    | zero =>
      obtain rfl : start = leftLength := by omega
      have current := GuardedCompleteAlignment.matched_prefix first second (Nat.le_refl _) rightBound
        firstOpen firstQuiet secondOpen secondQuiet stable past
      have same := GuardedCommandAlignment.matched_endpoint_is_terminal first second rightBound current
        past sameInput firstQuiet secondQuiet secondOpen
      exact ⟨first, second, same, past, current, .refl _, .refl _⟩
    | succ remaining ih =>
      by_cases pending : ∃ cut command, start ≤ cut ∧ cut < leftLength ∧ first.event cut = .command command
      · obtain ⟨cut, command, lower, bounded, event⟩ := pending
        obtain ⟨mid, peer, inside, order, _, leftPath, rightPath⟩ :=
          align_next_event_with_pending_command first second firstOpen firstQuiet secondOpen secondQuiet
            stable sameInput observe recovery commutative respect lower bounded rightBound past event
        obtain ⟨midOpen, midQuiet⟩ := leftPath.open_quiet firstOpen firstQuiet
        obtain ⟨peerOpen, peerQuiet⟩ := rightPath.open_quiet secondOpen secondQuiet
        obtain ⟨leftMoved, rightMoved, lengths, aligned, endpoint, leftRest, rightRest⟩ :=
          ih (start := start + 1) mid peer (by omega) (by omega) midOpen midQuiet peerOpen peerQuiet
            (leftPath.input_eq.trans (sameInput.trans rightPath.input_eq.symm)) order
        exact ⟨leftMoved, rightMoved, lengths, aligned, endpoint, .trans leftPath leftRest, .trans rightPath rightRest⟩
      · have free (i : Nat) (lo : start ≤ i) (hi : i < leftLength) :
            ∃ kind name, first.event i = .lifecycle kind name := by
          cases label : first.event i with
          | lifecycle kind name => exact ⟨kind, name, rfl⟩
          | command command => exact False.elim (pending ⟨i, command, lo, hi, label⟩)
        have current := GuardedCompleteAlignment.matched_prefix first second (by omega) rightBound
          firstOpen firstQuiet secondOpen secondQuiet stable past
        obtain ⟨moved, _, lengths, _, aligned, endpoint, _, related, _, _, path⟩ :=
          GuardedActivationAlignment.align_command_free_suffix first second (by omega) rightBound
            firstOpen firstQuiet secondOpen secondQuiet current stable past sameInput free
            observe recovery commutative respect
        exact ⟨first, moved, lengths, aligned, endpoint, .refl _, .activation path related⟩
  exact align leftLength (start := 0) left right (Nat.zero_add _) (Nat.zero_le _)
    leftOpen leftQuiet rightOpen rightQuiet input (fun _ impossible => by omega)

/-- Equal addressed commands connect any two quiet open histories by
a certified path within the original name set. -/
theorem connect_open_histories_in_original_names {length : Nat}
    (left right : Trace (encodeProgram program) length)
    (leftOpen : ¬ Nonempty (ClosedEpisode left)) (leftQuiet : Progress.Quiet (left.state length))
    (rightOpen : ¬ Nonempty (ClosedEpisode right)) (rightQuiet : Progress.Quiet (right.state length))
    (stable : ChildContinuations (encodeProgram program)) (input : orchestrationInput left = orchestrationInput right)
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r) :
    letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
    GuardedCompleteAlignment.ScheduleAlignmentPath left right := by
  letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
  obtain ⟨first, second, _, order, _, leftPath, rightPath⟩ :=
    align_open_histories_in_original_names left right leftOpen leftQuiet rightOpen rightQuiet
      stable input observe recovery commutative respect
  obtain ⟨firstOpen, firstQuiet⟩ := leftPath.open_quiet leftOpen leftQuiet
  obtain ⟨secondOpen, secondQuiet⟩ := rightPath.open_quiet rightOpen rightQuiet
  have redraw := GuardedCompleteAlignment.path_of_same_addressed_schedule first second
    firstOpen firstQuiet secondOpen secondQuiet stable
    (leftPath.input_eq.trans (input.trans rightPath.input_eq.symm)) order
  exact .trans leftPath (.trans redraw (.reverse rightPath))

/-- Equal surviving addressed commands identify the providers selected
at any two valid target cuts, even when the original name set is full. -/
theorem selected_providers_of_matching_input {leftLength rightLength : Nat}
    (left : Trace (encodeProgram program) leftLength) (right : Trace (encodeProgram program) rightLength)
    (leftOpen : ¬ Nonempty (ClosedEpisode left)) (leftQuiet : Progress.Quiet (left.state leftLength))
    (rightOpen : ¬ Nonempty (ClosedEpisode right)) (rightQuiet : Progress.Quiet (right.state rightLength))
    (stable : ChildContinuations (encodeProgram program)) (input : orchestrationInput left = orchestrationInput right)
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r)
    {leftCut rightCut : Nat} (leftBound : leftCut ≤ leftLength) (rightBound : rightCut ≤ rightLength)
    {name peer : Name} {key : Key} {leftView rightView : View Name Key}
    {row other : Fiber Name Key (Scalar ops) Code (Inverse Name Key (Scalar ops)) PUnit.{u + 1}}
    (found : left.state leftCut name = some row) (needed : row.component.requires key = true)
    (leftTarget : Target (left.state leftCut) name leftView)
    (otherFound : right.state rightCut peer = some other) (otherNeeded : other.component.requires key = true)
    (rightTarget : Target (right.state rightCut) peer rightView) :
    ∃ address birth otherBirth, (left.notes leftCut).1 (leftView key) = some birth ∧
      (right.notes rightCut).1 (rightView key) = some otherBirth ∧
      Addressed left birth address ∧ Addressed right otherBirth address := by
  letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
  obtain ⟨_, _, events, payload⟩ := compare_open_endpoints_addressed left right
    leftOpen leftQuiet rightOpen rightQuiet stable input observe recovery commutative respect
  obtain ⟨_, provider, active, reserves⟩ := selected_provider_at_cut leftBound found needed leftTarget
  obtain ⟨_, otherProvider, otherActive, otherReserves⟩ :=
    selected_provider_at_cut rightBound otherFound otherNeeded rightTarget
  exact available_providers_of_endpoint_comparison leftOpen leftQuiet rightOpen rightQuiet events
    (fun first second => (payload first second).1) leftBound rightBound
    provider active reserves otherProvider otherActive otherReserves

/-- If a provider finishes in the unmatched reference suffix, its peer
also finishes outside the matched prefix and before the peer target
uses it. The upper bound can be the next command's pre-cut. -/
theorem provider_finish_before_peer_target {leftLength rightLength : Nat}
    (left : Trace (encodeProgram program) leftLength) (right : Trace (encodeProgram program) rightLength)
    (leftOpen : ¬ Nonempty (ClosedEpisode left)) (leftQuiet : Progress.Quiet (left.state leftLength))
    (rightOpen : ¬ Nonempty (ClosedEpisode right)) (rightQuiet : Progress.Quiet (right.state rightLength))
    (stable : ChildContinuations (encodeProgram program)) (input : orchestrationInput left = orchestrationInput right)
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r)
    {start finish leftCut rightCut : Nat} (pending : start ≤ finish) (bounded : finish < leftLength)
    (beforeTarget : finish < leftCut) (leftBound : leftCut ≤ leftLength) (rightBound : rightCut ≤ rightLength)
    (past : ∀ i, i < start → addressedEventAt left i = addressedEventAt right i)
    {name peer : Name} {key : Key} {leftView rightView : View Name Key}
    {row other : Fiber Name Key (Scalar ops) Code (Inverse Name Key (Scalar ops)) PUnit.{u + 1}}
    (event : left.event finish = .lifecycle .finish (leftView key))
    (found : left.state leftCut name = some row) (needed : row.component.requires key = true)
    (leftTarget : Target (left.state leftCut) name leftView)
    (otherFound : right.state rightCut peer = some other) (otherNeeded : other.component.requires key = true)
    (rightTarget : Target (right.state rightCut) peer rightView) :
    ∃ cut address, start ≤ cut ∧ cut < rightCut ∧
      right.event cut = .lifecycle .finish (rightView key) ∧
      addressedEventAt left finish = some (.lifecycle .finish address) ∧
      addressedEventAt right cut = some (.lifecycle .finish address) := by
  obtain ⟨address, birth, otherBirth, stamp, otherStamp, known, otherKnown⟩ :=
    selected_providers_of_matching_input left right leftOpen leftQuiet rightOpen rightQuiet
      stable input observe recovery commutative respect leftBound rightBound
      found needed leftTarget otherFound otherNeeded rightTarget
  obtain ⟨_, _, _, atFinish⟩ := left.finished_row_at_cut leftOpen leftQuiet
    beforeTarget leftBound event
  have leftAddressed := (addressed_finish_at left).mpr ⟨_, birth, event, atFinish.symm.trans stamp, known⟩
  obtain ⟨_, otherProvider, active, _⟩ := selected_provider_at_cut rightBound otherFound otherNeeded rightTarget
  obtain ⟨cut, earlier, rightEvent, rightTag⟩ :=
    right.active_row_has_finish rightOpen rightQuiet rightBound otherProvider active
  have rightAddressed := (addressed_finish_at right).mpr
    ⟨_, otherBirth, rightEvent, rightTag.trans otherStamp, otherKnown⟩
  exact ⟨cut, address, finish_after_matched_prefix leftOpen leftQuiet pending bounded past leftAddressed rightAddressed,
    earlier, rightEvent, leftAddressed, rightAddressed⟩

/-- A delayed child command needs the allocating parent's target at the
child's birth. A provider enabling that parent's installed view in the
reference must therefore finish before the peer's allocating stage. -/
theorem provider_finish_before_peer_child_birth {leftLength rightLength : Nat}
    (left : Trace (encodeProgram program) leftLength) (right : Trace (encodeProgram program) rightLength)
    (leftOpen : ¬ Nonempty (ClosedEpisode left)) (leftQuiet : Progress.Quiet (left.state leftLength))
    (rightOpen : ¬ Nonempty (ClosedEpisode right)) (rightQuiet : Progress.Quiet (right.state rightLength))
    (stable : ChildContinuations (encodeProgram program)) (input : orchestrationInput left = orchestrationInput right)
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r)
    {start turn leftCut birth parentBirth ordinal : Nat} (pending : start ≤ turn) (bounded : turn < leftLength)
    (beforeTarget : turn < leftCut) (leftBound : leftCut ≤ leftLength)
    (past : ∀ i, i < start → addressedEventAt left i = addressedEventAt right i)
    {parent : Address} (peerChild : Addressed right birth (.child parent ordinal))
    {actor : Name} {key : Key} {view : View Name Key}
    {row : Fiber Name Key (Scalar ops) Code (Inverse Name Key (Scalar ops)) PUnit.{u + 1}}
    (event : left.event turn = .lifecycle .finish (view key))
    (found : left.state leftCut actor = some row) (needed : row.component.requires key = true)
    (installed : row.phase.committed = some view)
    (stamp : (left.notes leftCut).1 actor = some parentBirth) (known : Addressed left parentBirth parent)
    (leftTarget : Target (left.state leftCut) actor view) :
    ∃ cut address, start ≤ cut ∧ cut < birth - 1 ∧
      addressedEventAt left turn = some (.lifecycle .finish address) ∧
      addressedEventAt right cut = some (.lifecycle .finish address) := by
  letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
  obtain ⟨alloc, peer, peerBirth, other, otherView, placed, inside, otherFound, otherInstalled,
    otherStamp, otherKnown, rightTarget⟩ := allocating_parent_target rightOpen rightQuiet peerChild
  obtain ⟨_, atLeft, leftComponent⟩ := active_endpoint_of_installed left leftOpen leftQuiet
    leftBound found installed stamp known
  obtain ⟨_, atRight, rightComponent⟩ := active_endpoint_of_installed right rightOpen rightQuiet
    (Nat.le_of_lt inside) otherFound otherInstalled otherStamp otherKnown
  obtain ⟨_, _, _, payload⟩ := compare_open_endpoints_addressed left right
    leftOpen leftQuiet rightOpen rightQuiet stable input observe recovery commutative respect
  have components := leftComponent.symm.trans ((payload atLeft atRight).1.trans rightComponent)
  obtain ⟨cut, address, lower, upper, _, leftFinish, rightFinish⟩ :=
    provider_finish_before_peer_target left right leftOpen leftQuiet rightOpen rightQuiet stable input
      observe recovery commutative respect pending bounded beforeTarget leftBound (Nat.le_of_lt inside) past
      event found needed leftTarget otherFound (components ▸ needed) rightTarget
  exact ⟨cut, address, lower, by omega, leftFinish, rightFinish⟩

/-- Advance a frontier provider activation when the peer must finish the
same provider before an allocation on the path to a required descendant
in its command-free prefix. -/
theorem align_provider_stage_before_peer_descendant_birth {leftLength rightLength : Nat}
    (left : Trace (encodeProgram program) leftLength) (right : Trace (encodeProgram program) rightLength)
    (leftOpen : ¬ Nonempty (ClosedEpisode left)) (leftQuiet : Progress.Quiet (left.state leftLength))
    (rightOpen : ¬ Nonempty (ClosedEpisode right)) (rightQuiet : Progress.Quiet (right.state rightLength))
    (stable : ChildContinuations (encodeProgram program)) (input : orchestrationInput left = orchestrationInput right)
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r)
    {start turn leftCut birth parentBirth ordinal : Nat}
    (pending : start ≤ turn) (beforeTarget : turn < leftCut)
    (leftBound : leftCut ≤ leftLength)
    (current : GuardedScheduleMatching.CutAgreement left right start)
    (past : ∀ i, i < start → addressedEventAt left i = addressedEventAt right i)
    {parent descendant : Address} (peerDescendant : Addressed right birth descendant)
    (lineage : descendant.DescendsFrom (.child parent ordinal))
    (block : ∀ i, start ≤ i → i < birth - 1 → ∃ kind name, right.event i = .lifecycle kind name)
    {actor : Name} {key : Key} {view : View Name Key}
    {row : Fiber Name Key (Scalar ops) Code (Inverse Name Key (Scalar ops)) PUnit.{u + 1}}
    {firstKind : Lifecycle} (first : left.event start = .lifecycle firstKind (view key))
    (event : left.event turn = .lifecycle .finish (view key))
    (found : left.state leftCut actor = some row) (needed : row.component.requires key = true)
    (installed : row.phase.committed = some view)
    (stamp : (left.notes leftCut).1 actor = some parentBirth) (known : Addressed left parentBirth parent)
    (leftTarget : Target (left.state leftCut) actor view) :
    letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
    ∃ moved : Trace (encodeProgram program) rightLength,
      (∀ i, i < start + 1 → addressedEventAt left i = addressedEventAt moved i) ∧
      GuardedScheduleMatching.CutAgreement left moved (start + 1) ∧
      (¬ Nonempty (ClosedEpisode moved)) ∧ Progress.Quiet (moved.state rightLength) ∧
      GuardedCompleteAlignment.ScheduleAlignmentPath right moved := by
  letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
  obtain ⟨childBirth, beforeDescendant, peerChild⟩ := peerDescendant.ancestor_birth lineage
  obtain ⟨cut, _, lower, upper, leftFinish, rightFinish⟩ := provider_finish_before_peer_child_birth left right
    leftOpen leftQuiet rightOpen rightQuiet stable input observe recovery commutative respect
    pending (by omega) beforeTarget leftBound past peerChild event found needed installed stamp known leftTarget
  obtain ⟨provider, providerBirth, label, tag, addressed⟩ := (addressed_finish_at left).mp leftFinish
  have providerName := (Event.lifecycle.inj (label.symm.trans event)).2
  subst provider
  have sameProvider := left.activation_stamp_through leftOpen leftQuiet (by omega) pending
    (by omega : turn ≤ leftLength) first
  obtain ⟨otherProvider, otherBirth, otherLabel, otherTag, otherAddressed⟩ := (addressed_finish_at right).mp rightFinish
  obtain ⟨alloc, _, _, _, placed, allocBound, _, _, _⟩ := peerChild.allocating_event
  obtain ⟨moved, _, order, agreement, _, endpoint, opened, quiet, path⟩ :=
    GuardedActivationAlignment.align_pending_parent_before_required_stage left right (by omega) (by omega) lower
      leftOpen leftQuiet rightOpen rightQuiet current stable past input first otherLabel (sameProvider.trans tag) otherTag addressed otherAddressed
      (fun i lo hi => block i lo (by omega)) observe recovery commutative respect
  exact ⟨moved, order, agreement, opened, quiet, .activation path endpoint⟩

/-- An endpoint provider chain to an allocating ancestor gives a
certified exchange before the peer's next command, even when the
ancestor itself finishes only after that command. -/
theorem align_provider_chain_before_peer_descendant_birth {leftLength rightLength : Nat}
    (left : Trace (encodeProgram program) leftLength) (right : Trace (encodeProgram program) rightLength)
    (leftOpen : ¬ Nonempty (ClosedEpisode left)) (leftQuiet : Progress.Quiet (left.state leftLength))
    (rightOpen : ¬ Nonempty (ClosedEpisode right)) (rightQuiet : Progress.Quiet (right.state rightLength))
    (stable : ChildContinuations (encodeProgram program)) (input : orchestrationInput left = orchestrationInput right)
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r)
    {start birth ordinal : Nat} (leftBound : start < leftLength)
    (current : GuardedScheduleMatching.CutAgreement left right start)
    (past : ∀ i, i < start → addressedEventAt left i = addressedEventAt right i)
    {provider ancestor descendant : Address}
    (chain : Relation.TransGen (EndpointProvider left) provider ancestor)
    (peerDescendant : Addressed right birth descendant)
    (lineage : descendant.DescendsFrom (.child ancestor ordinal))
    (block : ∀ i, start ≤ i → i < birth - 1 → ∃ kind name, right.event i = .lifecycle kind name)
    {kind : Lifecycle} {actor : Name} (frontier : left.event start = .lifecycle kind actor)
    (frontierAddress : actorAddress left start = some provider) :
    letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
    ∃ moved : Trace (encodeProgram program) rightLength,
      (∀ i, i < start + 1 → addressedEventAt left i = addressedEventAt moved i) ∧
      GuardedScheduleMatching.CutAgreement left moved (start + 1) ∧
      (¬ Nonempty (ClosedEpisode moved)) ∧ Progress.Quiet (moved.state rightLength) ∧
      GuardedCompleteAlignment.ScheduleAlignmentPath right moved := by
  letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
  obtain ⟨turn, pending, bounded, finish, addressed⟩ :=
    finish_of_activation left leftOpen leftQuiet leftBound frontier frontierAddress
  obtain ⟨_, _, events, payload⟩ := compare_open_endpoints_addressed left right
    leftOpen leftQuiet rightOpen rightQuiet stable input observe recovery commutative respect
  have peerChain := endpoint_provider_chain_of_comparison leftOpen leftQuiet rightOpen rightQuiet events
    (fun first second => (payload first second).1) chain
  have member : some (.lifecycle .finish provider) ∈ addressedEvents left :=
    List.mem_map.mpr ⟨turn, List.mem_range.mpr bounded, addressed⟩
  obtain ⟨cut, inside, peerFinish⟩ := List.mem_map.mp (events.mem_iff.mp member)
  obtain ⟨childBirth, older, child⟩ := peerDescendant.ancestor_birth lineage
  obtain ⟨alloc, _, _, _, _, placed, allocBound, found, installed, tag, known, target⟩ :=
    allocating_parent_target rightOpen rightQuiet child
  have earlier := addressed_finish_lt_of_provider_chain_at_installed right rightOpen rightQuiet peerChain
    (List.mem_range.mp inside) (Nat.le_of_lt allocBound) peerFinish found installed target tag known
  have lower := finish_after_matched_prefix leftOpen leftQuiet pending bounded past addressed peerFinish
  obtain ⟨name, _, event, live, address⟩ := (addressed_finish_at left).mp addressed
  have same := (Event.lifecycle.inj (event.symm.trans finish)).2
  subst name
  have stamp := left.activation_stamp_through leftOpen leftQuiet (by omega) pending (Nat.le_of_lt bounded) frontier
  obtain ⟨_, _, peerEvent, peerTag, peerAddress⟩ := (addressed_finish_at right).mp peerFinish
  obtain ⟨moved, _, order, agreement, _, endpoint, opened, quiet, path⟩ :=
    GuardedActivationAlignment.align_pending_parent_before_required_stage left right (by omega) (by omega) lower
      leftOpen leftQuiet rightOpen rightQuiet current stable past input frontier peerEvent
      (stamp.trans live) peerTag address peerAddress
      (fun i lo hi => block i lo (by omega)) observe recovery commutative respect
  exact ⟨moved, order, agreement, opened, quiet, .activation path endpoint⟩

private theorem matching_delayed_birth_in_normalized_peer {leftLength rightLength start span : Nat}
    (left : Trace (encodeProgram program) leftLength) (right : Trace (encodeProgram program) rightLength)
    (leftOpen : ¬ Nonempty (ClosedEpisode left)) (leftQuiet : Progress.Quiet (left.state leftLength))
    (rightOpen : ¬ Nonempty (ClosedEpisode right)) (rightQuiet : Progress.Quiet (right.state rightLength))
    (stable : ChildContinuations (encodeProgram program)) (input : orchestrationInput left = orchestrationInput right)
    (leftBound : start + span < leftLength) (rightBound : start ≤ rightLength) (positive : 0 < span)
    (normal : GuardedCommandAlignment.CommandsAtBirthBarriersFrom left start)
    (past : ∀ i, i < start → addressedEventAt left i = addressedEventAt right i)
    {command : OrchestrationSorting.Command Name Key Code}
    (next : left.event (start + span) = .command command)
    (block : ∀ i, start ≤ i → i < start + span → ∃ kind name, left.event i = .lifecycle kind name)
    {kind : Lifecycle} {actor : Name} (frontier : left.event start = .lifecycle kind actor) :
    ∃ (mid : Trace (encodeProgram program) rightLength) (expand : Nat → Nat) (delay : Nat) (address : Address) (component : Component Key Code),
      0 < delay ∧ start + delay < rightLength ∧
      (¬ Nonempty (ClosedEpisode mid)) ∧ Progress.Quiet (mid.state rightLength) ∧
      GuardedCommandAlignment.CommandExchangePath right mid expand ∧
      orchestrationInput left = orchestrationInput mid ∧
      (∀ i, i < start → addressedEventAt left i = addressedEventAt mid i) ∧
      GuardedScheduleMatching.CutAgreement left mid start ∧
      Addressed mid (start + delay) address ∧
      targetAt left (start + span) command.actor = some (address, component) ∧
      (∀ i, start ≤ i → i < start + delay → ∃ kind name, mid.event i = .lifecycle kind name) := by
  obtain ⟨mid, _, normalized, _, commands, _, _, opened, quiet, commandPath, _, _, addresses⟩ :=
    GuardedCommandAlignment.push_commands_to_birth_barriers_from right start rightOpen rightQuiet
  have earlier (i : Nat) (before : i < start) : addressedEventAt left i = addressedEventAt mid i :=
    (past i before).trans (addresses i before (by omega)).symm
  have sameInput := input.trans commands.symm
  obtain ⟨delay, peer, inside, external, peerBlock⟩ :=
    GuardedCommandAlignment.pending_delayed_command_occurs left mid leftBound rightBound earlier sameInput next block
  cases delay with
  | zero =>
    have atStart : mid.event start = .command peer := external
    have reverse := GuardedCompleteAlignment.matched_prefix mid left rightBound (by omega) opened quiet leftOpen leftQuiet stable
      (fun i before => (earlier i before).symm)
    obtain ⟨_, ⟨_, impossible⟩, _⟩ :=
      GuardedCommandAlignment.pending_command_at_suffix_birth_frontier mid left (by omega) (by omega)
        normal reverse (fun i before => (earlier i before).symm) sameInput.symm atStart
    rw [frontier] at impossible
    cases impossible
  | succ delay =>
    obtain ⟨actual, payload, _, _, _, peerBirth, target, _⟩ :=
      GuardedCommandAlignment.delayed_commands_wait_for_same_birth left mid leftBound inside
        positive (by omega) normal normalized earlier sameInput next external block peerBlock
    have current := GuardedCompleteAlignment.matched_prefix left mid (by omega) rightBound
      leftOpen leftQuiet opened quiet stable earlier
    exact ⟨mid, _, delay + 1, actual, payload, by omega, inside, opened, quiet, commandPath,
      sameInput, earlier, current, peerBirth, target, peerBlock⟩

/-- Derive the peer's exchange window from the next actual addressed
command. Only the peer suffix is normalized before advancing the
upstream provider of the command target's allocating ancestor. -/
theorem align_provider_chain_for_next_command {leftLength rightLength start span : Nat}
    (left : Trace (encodeProgram program) leftLength) (right : Trace (encodeProgram program) rightLength)
    (leftOpen : ¬ Nonempty (ClosedEpisode left)) (leftQuiet : Progress.Quiet (left.state leftLength))
    (rightOpen : ¬ Nonempty (ClosedEpisode right)) (rightQuiet : Progress.Quiet (right.state rightLength))
    (stable : ChildContinuations (encodeProgram program)) (input : orchestrationInput left = orchestrationInput right)
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r)
    (leftBound : start + span < leftLength) (rightBound : start ≤ rightLength) (positive : 0 < span)
    (normal : GuardedCommandAlignment.CommandsAtBirthBarriersFrom left start)
    (past : ∀ i, i < start → addressedEventAt left i = addressedEventAt right i)
    {command : OrchestrationSorting.Command Name Key Code}
    (next : left.event (start + span) = .command command)
    (block : ∀ i, start ≤ i → i < start + span → ∃ kind name, left.event i = .lifecycle kind name)
    {provider ancestor descendant : Address} {ordinal : Nat} {component : Component Key Code}
    (chain : Relation.TransGen (EndpointProvider left) provider ancestor)
    (commandTarget : targetAt left (start + span) command.actor = some (descendant, component))
    (lineage : descendant.DescendsFrom (.child ancestor ordinal))
    {kind : Lifecycle} {actor : Name}
    (frontier : left.event start = .lifecycle kind actor)
    (frontierAddress : actorAddress left start = some provider) :
    letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
    ∃ moved : Trace (encodeProgram program) rightLength,
      start < rightLength ∧
      (∀ i, i < start + 1 → addressedEventAt left i = addressedEventAt moved i) ∧
      GuardedScheduleMatching.CutAgreement left moved (start + 1) ∧
      (¬ Nonempty (ClosedEpisode moved)) ∧ Progress.Quiet (moved.state rightLength) ∧
      GuardedCompleteAlignment.ScheduleAlignmentPath right moved := by
  letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
  obtain ⟨mid, _, delay, actual, payload, _, inside, opened, quiet, commandPath, sameInput,
    earlier, current, peerBirth, target, peerBlock⟩ :=
    matching_delayed_birth_in_normalized_peer left right leftOpen leftQuiet rightOpen rightQuiet stable input
      leftBound rightBound positive normal past next block frontier
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (target.symm.trans commandTarget))
  obtain ⟨moved, order, agreement, openMoved, quietMoved, path⟩ :=
    align_provider_chain_before_peer_descendant_birth left mid leftOpen leftQuiet opened quiet stable sameInput
      observe recovery commutative respect (by omega) current earlier chain peerBirth lineage
      (fun i lo hi => peerBlock i lo (by omega)) frontier frontierAddress
  exact ⟨moved, by omega, order, agreement, openMoved, quietMoved, .trans (.command commandPath) path⟩

/-- A mixed chain ending at an actual ancestor allocation of the next
command supplies a certified frontier exchange in the original name set.
The peer's allocation and command-free window come from the command word. -/
theorem align_mixed_prerequisites_for_next_command {leftLength rightLength start span leftCut : Nat}
    (left : Trace (encodeProgram program) leftLength) (right : Trace (encodeProgram program) rightLength)
    (leftOpen : ¬ Nonempty (ClosedEpisode left)) (leftQuiet : Progress.Quiet (left.state leftLength))
    (rightOpen : ¬ Nonempty (ClosedEpisode right)) (rightQuiet : Progress.Quiet (right.state rightLength))
    (stable : ChildContinuations (encodeProgram program)) (input : orchestrationInput left = orchestrationInput right)
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r)
    (leftBound : start + span < leftLength) (rightBound : start ≤ rightLength) (positive : 0 < span)
    (normal : GuardedCommandAlignment.CommandsAtBirthBarriersFrom left start)
    (past : ∀ i, i < start → addressedEventAt left i = addressedEventAt right i)
    {command : OrchestrationSorting.Command Name Key Code}
    (next : left.event (start + span) = .command command)
    (block : ∀ i, start ≤ i → i < start + span → ∃ kind name, left.event i = .lifecycle kind name)
    {ancestor descendant : Address} {ordinal : Nat} {component : Component Key Code}
    (chain : Relation.TransGen (GuardedReservationAlignment.ActivationPrerequisite left) start leftCut)
    (commandTarget : targetAt left (start + span) command.actor = some (descendant, component))
    (lineage : descendant.DescendsFrom (.child ancestor ordinal))
    (leftBirth : Addressed left (leftCut + 1) (.child ancestor ordinal))
    {kind : Lifecycle} {actor : Name} (frontier : left.event start = .lifecycle kind actor) :
    letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
    ∃ moved : Trace (encodeProgram program) rightLength,
      start < rightLength ∧
      (∀ i, i < start + 1 → addressedEventAt left i = addressedEventAt moved i) ∧
      GuardedScheduleMatching.CutAgreement left moved (start + 1) ∧
      (¬ Nonempty (ClosedEpisode moved)) ∧ Progress.Quiet (moved.state rightLength) ∧
      GuardedCompleteAlignment.ScheduleAlignmentPath right moved := by
  letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
  obtain ⟨mid, _, delay, actual, payload, _, inside, opened, quiet, commandPath, sameInput,
    earlier, current, peerDescendant, target, window⟩ :=
    matching_delayed_birth_in_normalized_peer left right leftOpen leftQuiet rightOpen rightQuiet stable input
      leftBound rightBound positive normal past next block frontier
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (target.symm.trans commandTarget))
  obtain ⟨birth, older, peerBirth⟩ := peerDescendant.ancestor_birth lineage
  obtain ⟨alloc, parentBirth, label, name, placed, allocBound, event, tag, path⟩ := peerBirth.allocating_event
  obtain ⟨source, sourceBirth, sourceLabel, sourceName, atSource, sourceBound, sourceEvent, sourceTag, sourcePath⟩ :=
    leftBirth.allocating_event
  have sourceCut : source = leftCut := by omega
  subst source
  have sourceActor : left.actor leftCut = sourceName := by simp [Trace.actor, Vestigial.eventActor, sourceEvent]
  have peerActor : mid.actor alloc = name := by simp [Trace.actor, Vestigial.eventActor, event]
  have matched := ((actorAddress_eq_some left).mpr ⟨sourceBirth, sourceActor.symm ▸ sourceTag, sourcePath⟩).trans
    ((actorAddress_eq_some mid).mpr ⟨parentBirth, peerActor.symm ▸ tag, path⟩).symm
  have ordered := GuardedReservationAlignment.ActivationPrerequisite.chain_lt chain
  have afterStart : start ≤ alloc := by
    apply Nat.le_of_not_gt
    intro before
    have same := birth_stamp_of_ordered_addresses left mid (by omega : start ≤ leftLength) rightBound
      earlier leftBirth peerBirth (by omega)
    omega
  obtain ⟨moved, order, agreement, openMoved, quietMoved, exchange⟩ :=
    align_frontier_of_mixed_prerequisites left mid leftOpen leftQuiet opened quiet stable sameInput
      observe recovery commutative respect sourceBound afterStart allocBound current earlier frontier event
      matched chain (fun i lo hi => window i lo (by omega))
  exact ⟨moved, by omega, order, agreement, openMoved, quietMoved, .trans (.command commandPath) exchange⟩

/-- When both normalized suffixes are waiting on their next command,
the addressed command word supplies the peer child birth and the
command-free prefix needed to bring the provider's stage forward. -/
theorem align_provider_stage_before_delayed_command {leftLength rightLength start leftSpan rightSpan : Nat}
    (left : Trace (encodeProgram program) leftLength) (right : Trace (encodeProgram program) rightLength)
    (leftBound : start + leftSpan < leftLength) (rightBound : start + rightSpan < rightLength)
    (leftPositive : 0 < leftSpan) (rightPositive : 0 < rightSpan)
    (leftOpen : ¬ Nonempty (ClosedEpisode left)) (leftQuiet : Progress.Quiet (left.state leftLength))
    (rightOpen : ¬ Nonempty (ClosedEpisode right)) (rightQuiet : Progress.Quiet (right.state rightLength))
    (leftNormal : GuardedCommandAlignment.CommandsAtBirthBarriersFrom left start)
    (rightNormal : GuardedCommandAlignment.CommandsAtBirthBarriersFrom right start)
    (current : GuardedScheduleMatching.CutAgreement left right start)
    (stable : ChildContinuations (encodeProgram program)) (input : orchestrationInput left = orchestrationInput right)
    (past : ∀ i, i < start → addressedEventAt left i = addressedEventAt right i)
    {first later : OrchestrationSorting.Command Name Key Code}
    (leftCommand : left.event (start + leftSpan) = .command first)
    (rightCommand : right.event (start + rightSpan) = .command later)
    (leftBlock : ∀ i, start ≤ i → i < start + leftSpan → ∃ kind actor, left.event i = .lifecycle kind actor)
    (rightBlock : ∀ i, start ≤ i → i < start + rightSpan → ∃ kind actor, right.event i = .lifecycle kind actor)
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r)
    {kind : Lifecycle} {key : Key} {view : View Name Key}
    {row : Fiber Name Key (Scalar ops) Code (Inverse Name Key (Scalar ops)) PUnit.{u + 1}}
    (firstStage : left.event start = .lifecycle kind (view key))
    (found : left.state (start + leftSpan - 1) (left.actor (start + leftSpan - 1)) = some row)
    (needed : row.component.requires key = true) (installed : row.phase.committed = some view)
    (target : Target (left.state (start + leftSpan - 1)) (left.actor (start + leftSpan - 1)) view) :
    letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
    ∃ moved : Trace (encodeProgram program) rightLength,
      (∀ i, i < start + 1 → addressedEventAt left i = addressedEventAt moved i) ∧
      GuardedScheduleMatching.CutAgreement left moved (start + 1) ∧
      (¬ Nonempty (ClosedEpisode moved)) ∧ Progress.Quiet (moved.state rightLength) ∧
      GuardedCompleteAlignment.ScheduleAlignmentPath right moved := by
  obtain ⟨address, _, _, _, leftBirth, peerBirth, _, _⟩ :=
    GuardedCommandAlignment.delayed_commands_wait_for_same_birth left right leftBound rightBound
      leftPositive rightPositive leftNormal rightNormal past input leftCommand rightCommand leftBlock rightBlock
  let cut := start + leftSpan - 1
  have after : cut + 1 = start + leftSpan := by dsimp [cut]; omega
  obtain ⟨label, actor, event⟩ := leftBlock cut (by dsimp [cut]; omega) (by dsimp [cut]; omega)
  obtain ⟨birth, parent, stamp, known, rfl⟩ :=
    (show Addressed left (cut + 1) address from after ▸ leftBirth).parent_of_lifecycle event
  have source : left.actor cut = actor := by simp [Trace.actor, Vestigial.eventActor, event]
  have startBefore : start ≤ cut := by dsimp [cut]; omega
  have cutBound : cut ≤ leftLength := by dsimp [cut]; omega
  obtain ⟨provider, providerBirth, providerTag, providerPath, edge⟩ :=
    endpoint_provider_of_installed_target left leftOpen leftQuiet cutBound
      found installed target needed (source.symm ▸ stamp) known
  have same := left.activation_stamp_through leftOpen leftQuiet (by omega) startBefore cutBound firstStage
  have frontierActor : left.actor start = view key := by simp [Trace.actor, Vestigial.eventActor, firstStage]
  have frontierAddress := (actorAddress_eq_some left).mpr
    ⟨providerBirth, frontierActor.symm ▸ (same.trans providerTag), providerPath⟩
  exact align_provider_chain_before_peer_descendant_birth left right leftOpen leftQuiet rightOpen rightQuiet
    stable input observe recovery commutative respect (by omega) current past (.single edge) peerBirth (.self _)
    (fun i lo hi => rightBlock i lo (by omega)) firstStage frontierAddress

end TypedConfluence

end Cordis.Repairs.GuardedNameExtension
