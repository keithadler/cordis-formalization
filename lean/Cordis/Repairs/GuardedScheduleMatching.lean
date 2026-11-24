import Cordis.Repairs.GuardedLandingMatching
import Cordis.Repairs.GuardedBirthReplay

/-! Two open schedules that agree by acting incarnation have matching
cuts. Begin's actual provider is unique at every required key. Fresh
names, birth notes, and the actual selected continuation are matched by
the guarded rules. -/
namespace Cordis.Repairs.GuardedScheduleMatching
open Calculus Stages GuardedHistory GuardedBirthMatching GuardedCutState GuardedLandingMatching LegalHistory
open GuardedBirthReplay IncarnationReplay
open OrchestrationSorting (Command)

universe u
variable {Name Key Value Code Error : Type u} [DecidableEq Name] [DecidableEq Key]
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
local notation "P" => Renaming.Permutation Name
variable {program : Code → Instruction Name Key Value Code Error} {last otherLast : Nat}

local instance exactValues : Setoid Value := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩

/-- Compare ordered activation events and commands after excision. A birth
is matched by its position. Root insertions keep their component payloads.
Already born actors and command targets are identified by their actual
birth stamps at the cut. -/
def OpenEventsAgree (left : Trace program last) (right : Trace program otherLast) (time : Nat) : Prop :=
  match left.event time, right.event time with
  | .command (.insert _ a), .command (.insert _ b) => a = b
  | .command (.retire a), .command (.retire b)
  | .command (.remove a), .command (.remove b) => (left.notes time).1 a = (right.notes time).1 b
  | .lifecycle kind a, .lifecycle otherKind b =>
    kind = otherKind ∧ Transposition.Activation kind.rule ∧ (left.notes time).1 a = (right.notes time).1 b
  | _, _ => False

def CutAgreement (left : Trace program last) (right : Trace program otherLast) (time : Nat) : Prop :=
  ∃ p : P, Renaming.registry p (project (left.state time)) = project (right.state time) ∧
    (∀ name, (right.notes time).1 (p.toFun name) = (left.notes time).1 name) ∧
    SavedMatch left right time time p id

private theorem successor (left : Trace program last) (right : Trace program otherLast)
    {time : Nat} (hi : time < last) (hj : time < otherLast) {p : P}
    (aligned : ∀ name, (right.notes time).1 (p.toFun name) = (left.notes time).1 name)
    (words : SavedMatch left right (time + 1) (time + 1) p id)
    (states : Renaming.registry p (project (left.state (time + 1))) = project (right.state (time + 1))) :
    CutAgreement left right (time + 1) := by
  refine ⟨p, states, ?_, words⟩
  simpa using advance_cut left right hi hj (stamp := id) (by simpa using aligned)
    (fun name => by
      rw [← project_present (right.state (time + 1)), ← project_present (left.state (time + 1)),
        ← states, Renaming.registry_at]
      simp) rfl

private theorem notes_unchanged_at (trace : Trace program last) {time : Nat} (valid : time < last)
    (raw : PartialReplayRegistry.saved (trace.state (time + 1)) = PartialReplayRegistry.saved (trace.state time)) :
    (trace.notes (time + 1)).2 = (trace.notes time).2 := by
  rw [(trace.step time valid).2]
  exact advance_control _ _ _ (trace.projects time (Nat.le_of_lt valid)) raw

private theorem command_notes (trace : Trace program last) {time : Nat} (valid : time < last)
    {command : Command Name Key Code} (event : trace.event time = .command command) :
    (trace.notes (time + 1)).2 = (trace.notes time).2 := by
  have step := (trace.step time valid).1
  rw [event] at step
  apply notes_unchanged_at trace valid
  exact PartialReplayRegistry.saved_of_command program (ExchangeReplay.command_labeled command step)
    (by cases command <;> simp [ExchangeReplay.commandRule])

private theorem apply_insert (left : Trace program last) (right : Trace program otherLast)
    {time : Nat} (hi : time < last) (hj : time < otherLast) {p : P}
    (aligned : ∀ name, (right.notes time).1 (p.toFun name) = (left.notes time).1 name)
    (states : Renaming.registry p (project (left.state time)) = project (right.state time))
    (saved : SavedMatch left right time time p id)
    {name otherName : Name} {component : Component Key Code}
    (first : left.event time = .command (.insert name component))
    (second : right.event time = .command (.insert otherName component)) :
    CutAgreement left right (time + 1) := by
  have leftStep := (left.step time hi).1
  have rightStep := (right.step time hj).1
  rw [first] at leftStep
  rw [second] at rightStep
  have leftVacant : left.state time name = none := leftStep.1.1
  have rightVacant : right.state time otherName = none := rightStep.1.1
  obtain ⟨q, newName, newAlignment, keeps⟩ := match_fresh_draw (stamp := id) (by simpa using aligned)
    ((left.births_agree time (by omega) name).mpr leftVacant)
    ((right.births_agree time (by omega) otherName).mpr rightVacant)
  have keepsPresent (name : Name) (present : left.state time name ≠ none) : q.toFun name = p.toFun name :=
    keeps name (fun vacant => present ((left.births_agree time (by omega) name).mp vacant))
  have sourceEq := (rename_on_live left (Nat.le_of_lt hi) keepsPresent).trans states
  have nextWords : SavedMatch left right (time + 1) (time + 1) q id := by
    intro name
    rw [command_notes left hi first, command_notes right hj second]
    exact saved.rematch (Nat.le_of_lt hi) (Nat.le_of_lt hj) keepsPresent newAlignment name
  apply successor left right hi hj (by simpa using newAlignment) nextWords
  rw [leftStep.2, rightStep.2]
  simp only [OrchestrationSorting.Command.apply, project_put, Renaming.put_eq]
  change put (Renaming.registry q (project (left.state time))) (q.toFun name)
      (Renaming.fiber q (fresh component none)) =
    put (project (right.state time)) otherName (fresh component none)
  rw [newName, sourceEq, Renaming.fresh_fiber, Option.map_none]

private theorem match_present_name (left : Trace program last) (right : Trace program otherLast)
    {time : Nat} (hi : time ≤ last) (hj : time ≤ otherLast) {p : P}
    (aligned : ∀ name, (right.notes time).1 (p.toFun name) = (left.notes time).1 name)
    {name otherName : Name} (present : left.state time name ≠ none)
    (same : (left.notes time).1 name = (right.notes time).1 otherName) :
    p.toFun name = otherName := by
  cases h : (left.notes time).1 name with
  | none => exact False.elim (present ((left.births_agree time hi name).mp h))
  | some birth =>
    exact live_stamp_unique right hj (by rw [aligned, h]) (same.symm.trans h)

private theorem existing_command_present (trace : Trace program last) {time : Nat} (valid : time < last)
    {name : Name} (event : trace.event time = .command (.retire name) ∨
      trace.event time = .command (.remove name)) :
    trace.state time name ≠ none := by
  obtain ⟨_, row, _, _, found, _⟩ := trace.retire_remove_birth valid event
  simp [found]

private theorem begins_at (trace : Trace program last) {time : Nat} (valid : time < last)
    {actor : Name} (event : trace.event time = .lifecycle .begin actor) :
    ∃ (row : F) (view : View Name Key), trace.state time actor = some row ∧ row.phase = .inactive ∧
      Target (trace.state time) actor view ∧
      trace.state (time + 1) = mark (trace.state time) actor (.reloading row.component.entry [] view) := by
  have step := (trace.step time valid).1
  rw [event] at step
  generalize ending : trace.state (time + 1) = after at step ⊢
  cases (show Labeled.Step program .begin actor _ _ from step) with
  | begin _ _ row view found inactive notRetired target => exact ⟨row, view, found, inactive, target, rfl⟩

private theorem begin_notes (trace : Trace program last) {time : Nat} (valid : time < last)
    {actor : Name} (event : trace.event time = .lifecycle .begin actor) :
    (trace.notes (time + 1)).2 = (trace.notes time).2 := by
  obtain ⟨row, view, present, inactive, _, ended⟩ := begins_at trace valid event
  apply notes_unchanged_at trace valid
  rw [ended]
  funext name
  rw [PartialReplayRegistry.saved_mark _ actor row present]
  by_cases same : name = actor
  · subst name
    simp [PartialReplayRegistry.saved, present, inactive, Phase.accumulator]
  · simp [same]

private theorem apply_begin (left : Trace program last) (right : Trace program otherLast)
    {time : Nat} (hi : time < last) (hj : time < otherLast) {p : P}
    (aligned : ∀ name, (right.notes time).1 (p.toFun name) = (left.notes time).1 name)
    (states : Renaming.registry p (project (left.state time)) = project (right.state time))
    (saved : SavedMatch left right time time p id)
    {actor otherActor : Name} (same : (left.notes time).1 actor = (right.notes time).1 otherActor)
    (first : left.event time = .lifecycle .begin actor)
    (second : right.event time = .lifecycle .begin otherActor) :
    CutAgreement left right (time + 1) := by
  obtain ⟨row, v, found, _, target, ended⟩ := begins_at left hi first
  obtain ⟨otherRow, w, otherFound, _, otherTarget, otherEnded⟩ := begins_at right hj second
  have actorEq := match_present_name left right (Nat.le_of_lt hi) (Nat.le_of_lt hj) aligned (by simp [found]) same
  subst otherActor
  have mapped := congrFun states (p.toFun actor)
  rw [Renaming.registry_at] at mapped
  have rowEq : Renaming.fiber p (projectFiber actor row) = projectFiber (p.toFun actor) otherRow := by
    simpa [project, found, otherFound] using mapped
  have components := congrArg Fiber.component rowEq
  change row.component = otherRow.component at components
  have valid := right.ownership time (Nat.le_of_lt hj)
  have rightProjected : project (right.state time) (p.toFun actor) = some (projectFiber (p.toFun actor) otherRow) := by
    simp [project, otherFound]
  have mappedTarget : Target (project (right.state time)) (p.toFun actor) (Renaming.view p v) := by
    rw [← states]
    exact (Renaming.target_iff p _ _ _).mpr ((project_target _ _ _).mpr target)
  have mask := TargetView.masked_targets_equal _ _ _ rightProjected
    (project_owned _ valid.1) (project_disjoint _ valid.2) _ _ mappedTarget
    ((project_target _ _ _).mpr otherTarget)
  have views : Renaming.view p (requiredView actor row.component.requires v) =
      requiredView (p.toFun actor) otherRow.component.requires w := by
    funext key
    rw [components]
    have atKey := congrFun mask key
    by_cases needed : otherRow.component.requires key = true
    · have viewEq : p.toFun (v key) = w key := by
        simpa [TargetView.mask, projectFiber, needed, Renaming.view] using atKey
      simp [requiredView, Renaming.view, needed, viewEq]
    · simp [requiredView, Renaming.view, needed]
  have nextWords : SavedMatch left right (time + 1) (time + 1) p id := by
    intro name
    rw [begin_notes left hi first, begin_notes right hj second]
    exact saved name
  apply successor left right hi hj aligned nextWords
  rw [ended, otherEnded, project_mark _ _ found, project_mark _ _ otherFound, Renaming.mark_eq, states]
  simp only [components] at views ⊢
  simp [projectPhase, Renaming.phase, views]

private theorem apply_activation (left : Trace program last) (right : Trace program otherLast)
    {time : Nat} (hi : time < last) (hj : time < otherLast) {p : P}
    (aligned : ∀ name, (right.notes time).1 (p.toFun name) = (left.notes time).1 name)
    (states : Renaming.registry p (project (left.state time)) = project (right.state time))
    (saved : SavedMatch left right time time p id)
    (stable : ChildContinuations program)
    {kind : Lifecycle} {actor otherActor : Name} (same : (left.notes time).1 actor = (right.notes time).1 otherActor)
    (first : left.event time = .lifecycle kind actor)
    (second : right.event time = .lifecycle kind otherActor)
    (active : Transposition.Activation kind.rule) :
    CutAgreement left right (time + 1) := by
  cases kind with
  | begin => exact apply_begin left right hi hj aligned states saved same first second
  | iter | finish =>
    have step := (left.step time hi).1
    rw [first] at step
    obtain ⟨row, _, present, _, _⟩ := Transposition.activation_source program step active
    have nameEq := match_present_name left right (Nat.le_of_lt hi) (Nat.le_of_lt hj) aligned (by simp [present]) same
    subst otherActor
    have event : left.event time = .lifecycle .iter actor ∨ left.event time = .lifecycle .finish actor := by
      first | exact .inl first | exact .inr first
    have otherEvent : right.event time = .lifecycle .iter (p.toFun actor) ∨
        right.event time = .lifecycle .finish (p.toFun actor) := by
      first | exact .inl second | exact .inr second
    obtain ⟨q, a, b, keeps, newAlignment, result, births, token, leftWords, rightWords, _⟩ :=
      match_activations left right hi hj event otherEvent
      (stamp := id) (by simpa using aligned) rfl states stable
    have retained := saved.rematch (Nat.le_of_lt hi) (Nat.le_of_lt hj) keeps newAlignment
    refine ⟨q, result, by simpa using births, fun name => ?_⟩
    rw [leftWords, rightWords]
    by_cases same : name = actor
    · subst name
      dsimp only
      rw [if_pos rfl, if_pos rfl, ← token]
      exact .cons (CapturePair.of_inverse q id (time + 1) a (fun _ _ undo _ {_ _} eq => congrArg undo eq))
        (retained actor)
    · simp only [if_neg same, if_neg (fun eq => same (q.injective eq))]
      exact retained name
  | leave | divert | unload => simp [Lifecycle.rule, Transposition.Activation] at active

theorem CutAgreement.advance (left : Trace program last) (right : Trace program otherLast)
    {time : Nat} (hi : time < last) (hj : time < otherLast)
    (current : CutAgreement left right time) (schedule : OpenEventsAgree left right time)
    (stable : ChildContinuations program) :
    CutAgreement left right (time + 1) := by
  obtain ⟨p, states, aligned, saved⟩ := current
  cases first : left.event time with
  | command cmd =>
    cases second : right.event time with
    | command otherCmd =>
      cases cmd <;> cases otherCmd <;> simp only [OpenEventsAgree, first, second] at schedule <;> try cases schedule
      case retire.retire name otherName =>
        have live := existing_command_present left hi (.inl first)
        have names := match_present_name left right (Nat.le_of_lt hi) (Nat.le_of_lt hj) aligned live schedule
        subst otherName
        have l := (left.step time hi).1
        have r := (right.step time hj).1
        rw [first] at l
        rw [second] at r
        have nextWords : SavedMatch left right (time + 1) (time + 1) p id := by
          intro name
          rw [command_notes left hi first, command_notes right hj second]
          exact saved name
        apply successor left right hi hj aligned nextWords
        rw [l.2, r.2]
        simp only [OrchestrationSorting.Command.apply, project_retire, Renaming.retire_eq, states]
      case remove.remove name otherName =>
        have live := existing_command_present left hi (.inr first)
        have names := match_present_name left right (Nat.le_of_lt hi) (Nat.le_of_lt hj) aligned live schedule
        subst otherName
        have l := (left.step time hi).1
        have r := (right.step time hj).1
        rw [first] at l
        rw [second] at r
        have nextWords : SavedMatch left right (time + 1) (time + 1) p id := by
          intro name
          rw [command_notes left hi first, command_notes right hj second]
          exact saved name
        apply successor left right hi hj aligned nextWords
        rw [l.2, r.2]
        simp only [OrchestrationSorting.Command.apply, project_erase, Renaming.erase_eq, states]
      case insert.insert.refl =>
        exact apply_insert left right hi hj aligned states saved first second
    | lifecycle => simp [OpenEventsAgree, first, second] at schedule
  | lifecycle kind actor =>
    cases second : right.event time with
    | command => simp [OpenEventsAgree, first, second] at schedule
    | lifecycle otherKind otherActor =>
      obtain ⟨rfl, active, names⟩ := (show kind = otherKind ∧ _ from by
        simpa [OpenEventsAgree, first, second] using schedule)
      exact apply_activation left right hi hj aligned states saved stable names first second active

/-- Starting at the empty cut, any two actual guarded traces with the same
open event schedule agree after each matched prefix. Name reuse may force
the permutation to vary by cut. -/
theorem match_open_prefix (left : Trace program last) (right : Trace program otherLast)
    (stable : ChildContinuations program)
    (time : Nat) (hi : time ≤ last) (hj : time ≤ otherLast)
    (schedule : ∀ cut, cut < time → OpenEventsAgree left right cut) :
    CutAgreement left right time := by
  induction time with
  | zero =>
    refine ⟨⟨id, id, fun _ => rfl, fun _ => rfl⟩, ?_, ?_, ?_⟩
    · rw [left.start, right.start]; rfl
    · rw [left.seed, right.seed]; intro name; rfl
    · intro name
      rw [left.seed, right.seed]
      exact .nil
  | succ time ih =>
    exact CutAgreement.advance left right (by omega) (by omega)
      (ih (by omega) (by omega) (fun cut earlier => schedule cut (by omega))) (schedule time (by omega)) stable

/-- Registry agreement at a cut gives the paper's name-indexed table
observation in that cut's namespace. -/
theorem CutAgreement.tables {left : Trace program last} {right : Trace program otherLast} {time : Nat}
    (matching : CutAgreement left right time) :
    ∃ p : P, ∀ name key, StageRecovery.tableAt (left.state time) name key =
      StageRecovery.tableAt (right.state time) (p.toFun name) key := by
  obtain ⟨p, states, _, _⟩ := matching
  refine ⟨p, fun name key => ?_⟩
  have rows := congrFun states (p.toFun name)
  rw [Renaming.registry_at] at rows
  have values := congrArg (fun (row : Option F) => row.bind fun entry => entry.table key) rows
  cases lp : left.state time name <;> cases rp : right.state time (p.toFun name) <;>
    simp [project, projectFiber, Renaming.fiber, StageRecovery.tableAt, lp, rp] at values ⊢ <;>
    exact values

/-- The matched open prefix also determines the comparison of its actual
saved words when run from that cut. -/
theorem CutAgreement.replays {left : Trace program last} {right : Trace program otherLast} {time : Nat}
    (hi : time ≤ last) (hj : time ≤ otherLast) (matching : CutAgreement left right time) :
    ∃ p : P, Renaming.registry p (project (left.state time)) = project (right.state time) ∧
      ∀ actor, StageSimulation.Related Eq
        (Renaming.registry p (project (replay (left.notes time).1 ((left.notes time).2 actor) (left.state time))))
        (project (replay (right.notes time).1 ((right.notes time).2 (p.toFun actor)) (right.state time))) := by
  obtain ⟨p, states, births, saved⟩ := matching
  refine ⟨p, states, fun actor => replay_actual_words left right hi hj (stamp := id) ?_ ?_ actor (saved actor) ?_⟩
  · simpa using births
  · exact fun {_ _} same => same
  · rw [states]
    exact project_self_related _

/-- Matching cuts compare every prefix of the actual saved rollback
words. Each word is defined at its own cut under the partial semantics. -/
theorem CutAgreement.replay_prefixes_in_domain {left : Trace program last} {right : Trace program otherLast}
    {time : Nat} (hi : time ≤ last) (hj : time ≤ otherLast)
    (meaning : PartialReplayRegistry.Coeffects program) (matching : CutAgreement left right time) :
    ∃ p : P, Renaming.registry p (project (left.state time)) = project (right.state time) ∧
      ∀ actor, ReplayBindingDomains.WordDefined meaning (left.notes time).1 ((left.notes time).2 actor) (left.state time) ∧
        ReplayBindingDomains.WordDefined meaning (right.notes time).1
          ((right.notes time).2 (p.toFun actor)) (right.state time) ∧
        ∀ count, StageSimulation.Related Eq
          (Renaming.registry p (project (replay (left.notes time).1
            (((left.notes time).2 actor).take count) (left.state time))))
          (project (replay (right.notes time).1
            (((right.notes time).2 (p.toFun actor)).take count) (right.state time))) := by
  obtain ⟨p, states, births, saved⟩ := matching
  refine ⟨p, states, fun actor => GuardedBirthReplay.replay_prefixes_in_domain left right meaning meaning
    hi hj (stamp := id) ?_ (fun {_ _} same => same) actor (saved actor) ?_⟩
  · simpa using births
  · rw [states]
    exact project_self_related _

end Cordis.Repairs.GuardedScheduleMatching
