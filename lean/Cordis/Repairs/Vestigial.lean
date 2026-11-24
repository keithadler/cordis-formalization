import Cordis.Repairs.HistoryProvenance

/-! Erasing a retired, inactive, empty leaf from the root-only calculus.
All ordinary foreign steps still apply with the same payload. The absent
leaf is omitted until its original removal, when the two runs coincide. -/
namespace Cordis.Repairs.Vestigial
open Calculus Stages StageRecovery Transposition
open LegalHistory OrchestrationSorting
universe u
variable {Name Key Value Code Error : Type u} [DecidableEq Name] [DecidableEq Key]
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
local notation "Program" => Code → Instruction Name Key Value Code Error
local notation "I" => Inverse Name Key Value

omit [DecidableEq Key] in
theorem modify_erase (r : R) (actor name : Name) (edit : F → F) :
    Calculus.modify (erase r name) actor edit = erase (Calculus.modify r actor edit) name := by
  funext query
  by_cases erased : query = name <;> by_cases edited : query = actor <;>
    simp_all [erase, Calculus.modify]

omit [DecidableEq Key] in
private theorem removable_modify {r : R} {actor name : Name} (ready : Removable r name)
    (edit : F → F) (parent : ∀ row, (edit row).parent = row.parent)
    (unchanged : ∀ row, actor = name → r name = some row → edit row = row) :
    Removable (Calculus.modify r actor edit) name := by
  have rowSame : Calculus.modify r actor edit name = r name := by
    by_cases same : name = actor
    · subst actor
      cases found : r name with
      | none => simp [Calculus.modify, found]
      | some row => simp [Calculus.modify, found, unchanged row rfl found]
    · simp [Calculus.modify, same]
  simp only [Removable, rowSame]
  cases found : r name with
  | none => simp [Removable, found] at ready
  | some row =>
    simp only [Removable, found] at ready
    refine ⟨ready.1, ready.2.1, ready.2.2.1, ?_⟩
    intro query
    by_cases same : query = actor
    · subst query
      cases placed : r actor with
      | none => simp [Calculus.modify, placed]
      | some old => simpa [Calculus.modify, placed, parent] using ready.2.2.2 actor
    · simpa [Calculus.modify, same] using ready.2.2.2 query

omit [DecidableEq Key] in
private theorem removable_put {r : R} {inserted name : Name} (ready : Removable r name)
    (row : F) (different : inserted ≠ name) (foreign : row.parent ≠ some name) :
    Removable (put r inserted row) name := by
  cases found : r name with
  | none => simp [Removable, found] at ready
  | some old =>
    simp only [Removable, found] at ready
    simp only [Removable, put, if_neg (Ne.symm different), found]
    refine ⟨ready.1, ready.2.1, ready.2.2.1, ?_⟩
    intro child
    by_cases same : child = inserted
    · simp [same, foreign]
    · simpa [same] using ready.2.2.2 child

omit [DecidableEq Key] in
private theorem removable_erase {r : R} {removed name : Name} (ready : Removable r name)
    (different : removed ≠ name) : Removable (erase r removed) name := by
  cases found : r name with
  | none => simp [Removable, found] at ready
  | some old =>
    simp only [Removable, found] at ready
    simp only [Removable, erase, if_neg (Ne.symm different), found]
    refine ⟨ready.1, ready.2.1, ready.2.2.1, ?_⟩
    intro child
    by_cases same : child = removed
    · simp [same]
    · simpa [same] using ready.2.2.2 child

omit [DecidableEq Key] in
theorem removable_mark {r : R} {actor name : Name} (ready : Removable r name)
    (different : actor ≠ name) (phase : Phase Name Key Code I) :
    Removable (mark r actor phase) name :=
  removable_modify ready _ (fun _ => rfl) (fun _ equal _ => False.elim (different equal))

omit [DecidableEq Key] in
private theorem removable_retire {r : R} {actor name : Name} (ready : Removable r name) :
    Removable (Calculus.retire r actor) name := by
  refine removable_modify ready (fun row => {row with retired := true}) (fun _ => rfl) ?_
  intro row _ found
  have facts := ready
  simp only [Removable, found] at facts
  have retired := facts.1
  cases row
  simp_all

private theorem removable_write {r : R} {actor name : Name} (ready : Removable r name)
    (different : actor ≠ name) (key : Key) (value : Option Value) :
    Removable (write r actor key value) name := by
  unfold write
  exact removable_modify ready _ (fun _ => rfl) (fun _ equal _ => False.elim (different equal))

private theorem removable_land (program : Program) {r s : R} {actor name : Name}
    {code : Code} {token next} (landed : Land program actor code r s token next)
    (different : actor ≠ name) (ready : Removable r name) : Removable s name := by
  cases landed with
  | unit => exact ready
  | provide => exact removable_write ready different _ _
  | operate _ _ _ key call owner before after inv result action located returned =>
    apply removable_write ready ?_ key
    intro same
    subst owner
    obtain ⟨row, found, bound⟩ := Safety.location_binding r actor name key before located
    have absent := removable_tables r name ready key
    simp [tableAt, found, bound] at absent
  | instantiate _ _ _ component child _ allowed =>
    refine removable_put ready _ ?_ ?_
    · intro same
      exact removable_present r name ready (same ▸ allowed.1)
    · intro equal
      exact different (Option.some.inj equal)

theorem undo_erase (r : R) (name : Name) (token : I) :
    Stages.undo token (erase r name) = erase (Stages.undo token r) name := by
  cases token with
  | unit => rfl
  | restrict owner key => exact modify_erase r owner name _
  | operate owner key inverse => exact modify_erase r owner name _
  | retire child => exact modify_erase r child name _

theorem removable_undo {r : R} {name : Name} (ready : Removable r name) (token : I) :
    Removable (Stages.undo token r) name := by
  cases token with
  | unit => exact ready
  | restrict owner key =>
    change Removable (Calculus.modify r owner (fun row =>
      {row with table := fun query => if query = key then none else row.table query})) name
    refine removable_modify ready _ ?_ ?_
    · intro row; rfl
    intro row _ found
    have facts := ready
    simp only [Removable, found] at facts
    have empty := facts.2.2.1
    have same : (fun k => if k = key then none else row.table k) = row.table := by
      funext key
      simp [empty]
    change {row with table := _} = row
    rw [same]
  | operate owner key inverse =>
    change Removable (Calculus.modify r owner (fun row =>
      {row with table := fun query => if query = key then (row.table key).map inverse else row.table query})) name
    refine removable_modify ready _ ?_ ?_
    · intro row; rfl
    intro row _ found
    have facts := ready
    simp only [Removable, found] at facts
    have empty := facts.2.2.1
    have same : (fun k => if k = key then (row.table key).map inverse else row.table k) = row.table := by
      funext key
      simp [empty]
    change {row with table := _} = row
    rw [same]
  | retire => exact removable_retire ready

theorem discharge_erase (r : R) (name : Name) (word : List I) :
    discharge Stages.undo word (erase r name) = erase (discharge Stages.undo word r) name := by
  induction word generalizing r with
  | nil => rfl
  | cons token rest ih => simp only [discharge, undo_erase, ih]

private theorem removable_discharge {r : R} {name : Name} (ready : Removable r name) (word : List I) :
    Removable (discharge Stages.undo word r) name := by
  induction word generalizing r with
  | nil => exact ready
  | cons token rest ih => exact ih (removable_undo ready token)

omit [DecidableEq Key] in
theorem erase_relied {r : R} {forgotten actor : Name} (ready : Removable r forgotten) :
    Relied (erase r forgotten) actor ↔ Relied r actor := by
  constructor
  · rintro ⟨consumer, different, evidence⟩
    by_cases erased : consumer = forgotten
    · subst consumer
      simp [erase] at evidence
    · exact ⟨consumer, different, by simpa [erase, erased] using evidence⟩
  · rintro ⟨consumer, different, evidence⟩
    by_cases erased : consumer = forgotten
    · subst consumer
      cases found : r forgotten with
      | none => simp [found] at evidence
      | some row =>
        simp only [Removable, found] at ready
        simp [found, ready.2.1, Phase.committed] at evidence
    · exact ⟨consumer, different, by simpa [erase, erased] using evidence⟩

omit [DecidableEq Key] in
theorem erase_removable {r : R} {forgotten actor : Name} (different : actor ≠ forgotten)
    (ready : Removable r actor) : Removable (erase r forgotten) actor :=
  removable_erase ready (Ne.symm different)

omit [DecidableEq Key] in
theorem erase_erase (r : R) (first second : Name) :
    erase (erase r first) second = erase (erase r second) first := by
  funext name
  by_cases a : name = first <;> by_cases b : name = second <;> simp [erase, a, b]

variable {program : Code → Instruction Name Key Value Code Error}

def eventActor : Event Name Key Code → Name
  | .command command => command.actor
  | .lifecycle _ actor => actor

theorem lifecycle_erase (kind : Lifecycle) {actor name : Name} {before after : R}
    (step : Labeled.Step program kind.rule actor before after)
    (different : actor ≠ name) (ready : Removable before name) :
    Removable after name ∧ Labeled.Step program kind.rule actor (erase before name) (erase after name) := by
  cases kind with
  | begin =>
    cases step with
    | begin _ _ row view found phase free target =>
      refine ⟨removable_mark ready different _, ?_⟩
      rw [← mark_erase _ _ _ _ different]
      exact .begin _ _ row view ((erase_other _ _ _ different).trans found) phase
        (by simpa [ErrorFree, erase, different] using free)
        ((removable_erase_target _ _ _ different ready _).mpr target)
  | iter =>
    cases step with
    | iter _ middle _ row code acc view inverse next found phase target landed =>
      refine ⟨removable_mark (removable_land program landed different ready) different _, ?_⟩
      rw [← mark_erase _ _ _ _ different]
      exact .iter _ _ _ row _ _ _ _ _ ((erase_other _ _ _ different).trans found) phase
        ((removable_erase_target _ _ _ different ready _).mpr target)
        (land_erase program landed name different ready)
  | finish =>
    cases step with
    | finish _ middle _ row code acc view inverse found phase target landed =>
      refine ⟨removable_mark (removable_land program landed different ready) different _, ?_⟩
      rw [← mark_erase _ _ _ _ different]
      exact .finish _ _ _ row _ _ _ _ ((erase_other _ _ _ different).trans found) phase
        ((removable_erase_target _ _ _ different ready _).mpr target)
        (land_erase program landed name different ready)
  | divert =>
    cases step with
    | divert _ middle _ row code acc view tail found phase target branch =>
      have noTarget : ¬ Target (erase before name) actor view :=
        fun yes => target ((removable_erase_target _ _ _ different ready _).mp yes)
      rcases branch with ⟨rfl, rfl⟩ | ⟨inverse, next, landed, rfl⟩
      · refine ⟨removable_mark ready different _, ?_⟩
        rw [← mark_erase _ _ _ _ different]
        exact .divert _ _ _ row _ _ _ _ ((erase_other _ _ _ different).trans found) phase noTarget
          (.inl ⟨rfl, rfl⟩)
      · refine ⟨removable_mark (removable_land program landed different ready) different _, ?_⟩
        rw [← mark_erase _ _ _ _ different]
        exact .divert _ _ _ row _ _ _ _ ((erase_other _ _ _ different).trans found) phase noTarget
          (.inr ⟨inverse, next, land_erase program landed name different ready, rfl⟩)
  | leave =>
    cases step with
    | leave _ _ row acc view found phase target =>
      refine ⟨removable_mark ready different _, ?_⟩
      rw [← mark_erase _ _ _ _ different]
      exact .leave _ _ row _ _ ((erase_other _ _ _ different).trans found) phase
        (fun yes => target ((removable_erase_target _ _ _ different ready _).mp yes))
  | unload =>
    cases step with
    | unload _ _ row word view found phase free =>
      refine ⟨removable_mark (removable_discharge ready word) different _, ?_⟩
      rw [← mark_erase _ _ _ _ different, ← discharge_erase]
      exact .unload _ _ row _ _ ((erase_other _ _ _ different).trans found) phase
        (fun yes => free ((erase_relied ready).mp yes))

theorem command_erase (command : Command Name Key Code) {name : Name} {before after : R}
    (step : command.Step before after) (different : command.actor ≠ name)
    (ready : Removable before name) :
    Removable after name ∧ command.Step (erase before name) (erase after name) := by
  obtain ⟨enabled, rfl⟩ := step
  cases command with
  | insert actor component =>
    refine ⟨removable_put ready _ different (by simp [fresh]), ?_, ?_⟩
    · apply (CausalCommands.root_insertable_before_erase before different component).mp enabled |>.1
    · exact (put_erase before actor name _ different).symm
  | retire actor =>
    refine ⟨removable_retire ready, ?_, ?_⟩
    · change erase before name actor ≠ none
      rw [erase_other before actor name different]
      exact enabled
    · exact (modify_erase before actor name _).symm
  | remove actor =>
    exact ⟨removable_erase ready different, erase_removable different enabled, erase_erase before actor name⟩

theorem event_erase {event : Event Name Key Code} {name : Name} {before after : R}
    (step : event.Step program before after)
    (different : eventActor event ≠ name)
    (ready : Removable before name) :
    Removable after name ∧ event.Step program (erase before name) (erase after name) := by
  cases event with
  | command command => exact command_erase command step different ready
  | lifecycle kind actor => exact lifecycle_erase kind step different ready

private theorem no_lifecycle {state after : R} {name : Name} (ready : Removable state name)
    (kind : Lifecycle) (step : Labeled.Step program kind.rule name state after) : False := by
  cases kind with
  | begin =>
    cases step with
    | begin _ _ row view found phase free target =>
      simp only [Removable, found] at ready
      simp [Target, found, ready.1] at target
  | iter =>
    cases step with
    | iter _ _ _ _ _ _ _ _ _ found phase _ _ => simp [Removable, found, phase] at ready
  | finish =>
    cases step with
    | finish _ _ _ _ _ _ _ _ found phase _ _ => simp [Removable, found, phase] at ready
  | divert =>
    cases step with
    | divert _ _ _ _ _ _ _ _ found phase _ _ => simp [Removable, found, phase] at ready
  | leave =>
    cases step with
    | leave _ _ _ _ _ found phase _ => simp [Removable, found, phase] at ready
  | unload =>
    cases step with
    | unload _ _ _ _ _ found phase _ => simp [Removable, found, phase] at ready

omit [DecidableEq Key] in
theorem retire_vestigial {state : R} {name : Name} (ready : Removable state name) :
    Calculus.retire state name = state := by
  funext query
  by_cases same : query = name
  · subst query
    cases found : state name with
    | none => simp [Calculus.retire, Calculus.modify, found]
    | some row =>
      simp only [Removable, found] at ready
      have retired := ready.1
      cases row
      simp_all [Calculus.retire, Calculus.modify]
  · simp [Calculus.retire, Calculus.modify, same]

/-- The only native steps at a removable fiber are its redundant retirement
and its removal. In particular, later activity at the same name requires a
different incarnation. -/
theorem steps_at_vestige {state after : R} {name : Name} {rule : Labeled.Rule}
    (ready : Removable state name) (step : Labeled.Step program rule name state after) :
    (rule = .retire ∧ after = state) ∨ (rule = .remove ∧ after = erase state name) := by
  cases rule with
  | insert =>
    cases step with
    | insert _ _ _ _ enabled =>
      exact False.elim (removable_present state name ready enabled.1)
  | retire =>
    cases step
    exact .inl ⟨rfl, retire_vestigial ready⟩
  | remove =>
    cases step
    exact .inr ⟨rfl, rfl⟩
  | begin => exact False.elim (no_lifecycle ready .begin step)
  | iter => exact False.elim (no_lifecycle ready .iter step)
  | finish => exact False.elim (no_lifecycle ready .finish step)
  | divert => exact False.elim (no_lifecycle ready .divert step)
  | leave => exact False.elim (no_lifecycle ready .leave step)
  | unload => exact False.elim (no_lifecycle ready .unload step)

/-- The foreign projection for indexed traces. A native external insertion
must have root provenance, witnessed by its actual target row. -/
theorem labeled_erase {before after : R} {actor name : Name} {rule : Labeled.Rule}
    (step : Labeled.Step program rule actor before after) (different : actor ≠ name)
    (ready : Removable before name)
    (root : rule = .insert → ∃ row, after actor = some row ∧ row.parent = none) :
    Removable after name ∧ Labeled.Step program rule actor (erase before name) (erase after name) := by
  cases rule with
  | insert =>
    cases step with
    | insert _ _ component parent enabled =>
      obtain ⟨row, found, noParent⟩ := root rfl
      have parentNone : parent = none := by
        have equal : fresh component parent = row := Option.some.inj ((put_self _ _ _).symm.trans found)
        exact (congrArg Fiber.parent equal).trans noParent
      subst parent
      obtain ⟨still, allowed, endpoint⟩ :=
        command_erase (.insert actor component) ⟨enabled, rfl⟩ different ready
      exact ⟨still, endpoint ▸ Labeled.Step.insert _ _ _ _ allowed⟩
  | retire =>
    cases step with
    | retire _ _ present =>
      obtain ⟨still, allowed, endpoint⟩ := command_erase (.retire actor) ⟨present, rfl⟩ different ready
      exact ⟨still, endpoint ▸ Labeled.Step.retire _ _ allowed⟩
  | remove =>
    cases step with
    | remove _ _ enabled =>
      obtain ⟨still, allowed, endpoint⟩ := command_erase (.remove actor) ⟨enabled, rfl⟩ different ready
      exact ⟨still, endpoint ▸ Labeled.Step.remove _ _ allowed⟩
  | begin => exact lifecycle_erase .begin step different ready
  | iter => exact lifecycle_erase .iter step different ready
  | finish => exact lifecycle_erase .finish step different ready
  | divert => exact lifecycle_erase .divert step different ready
  | leave => exact lifecycle_erase .leave step different ready
  | unload => exact lifecycle_erase .unload step different ready

def mentionsRemoval (name : Name) : Event Name Key Code → Bool
  | .command (.remove target) => decide (target = name)
  | _ => false

/-- Erasure lasts for the remaining lifetime of the withdrawn child. The
original Remove is omitted and every later event is copied verbatim. -/
def prune (name : Name) : List (Event Name Key Code) → List (Event Name Key Code)
  | [] => []
  | .command (.remove target) :: rest =>
      if target = name then rest else .command (.remove target) :: prune name rest
  | .command (.retire target) :: rest =>
      if target = name then prune name rest else .command (.retire target) :: prune name rest
  | event :: rest => event :: prune name rest

omit [DecidableEq Key] in
theorem prune_sublist (name : Name) (events : List (Event Name Key Code)) :
    (prune name events).Sublist events := by
  induction events with
  | nil => exact .slnil
  | cons event rest ih =>
    cases event with
    | lifecycle => exact .cons₂ _ ih
    | command command =>
      cases command with
      | insert => exact .cons₂ _ ih
      | retire target =>
        by_cases same : target = name
        · simpa [prune, same] using (List.Sublist.cons (.command (.retire target)) ih)
        · simpa [prune, same] using (List.Sublist.cons₂ (.command (.retire target)) ih)
      | remove target =>
        by_cases same : target = name
        · rw [prune, if_pos same]
          exact List.Sublist.cons _ (List.Sublist.refl rest)
        · simpa [prune, same] using (List.Sublist.cons₂ (.command (.remove target)) ih)

def prunedEndpoint (name : Name) (events : List (Event Name Key Code)) (final : R) : R :=
  if events.any (mentionsRemoval name) then final else erase final name

omit [DecidableEq Key] in
private theorem command_source_root (command : Command Name Key Code) {state after : R}
    (step : command.Step state after) {name : Name} (different : command.actor ≠ name) :
    rootAt after name = rootAt state name := by
  rw [step.2]
  unfold rootAt
  rw [CausalCommands.apply_other command state name (Ne.symm different)]

private theorem step_command_prune {command : Command Name Key Code} {name : Name} {state after : R}
    (step : command.Step state after) (ready : Removable state name) (different : command.actor ≠ name) :
    Removable after name ∧ command.Step (erase state name) (erase after name) ∧
      commandRoots (erase state name) command = commandRoots state command :=
  let replay := command_erase command step different ready
  ⟨replay.1, replay.2, commandRoots_same_row command (erase_other state command.actor name different)⟩

/-- Prune the suffix at one vestigial child, preserving the actual root
command subsequence. Its retirement is redundant and its removal is a point
at which the projected history rejoins the unprojected history. -/
theorem prune_suffix {events : List (Event Name Key Code)} {before final : R}
    {roots : List (Command Name Key Code)} (execution : RootExec program events before final roots)
    (name : Name) (ready : Removable before name) (child : rootAt before name = false) :
    RootExec program (prune name events) (erase before name) (prunedEndpoint name events final) roots ∧
      (events.any (mentionsRemoval name) = false → Removable final name) := by
  induction execution with
  | nil =>
    exact ⟨.nil _, fun _ => ready⟩
  | @cons event events before middle after roots step tail ih =>
    cases event with
    | lifecycle kind actor =>
      by_cases same : actor = name
      · subst actor
        exact False.elim (no_lifecycle ready kind step)
      · obtain ⟨still, projected⟩ := lifecycle_erase kind step same ready
        obtain ⟨remaining, finalReady⟩ := ih still ((rootAt_lifecycle kind step name).trans child)
        exact ⟨.cons (event := .lifecycle kind actor) projected remaining, finalReady⟩
    | command command =>
      by_cases same : command.actor = name
      · cases command with
        | insert actor component =>
          exact False.elim (removable_present before name ready (same ▸ step.1.1))
        | retire actor =>
          change actor = name at same
          subst actor
          have unchanged : middle = before := step.2.trans (retire_vestigial ready)
          subst middle
          simpa [prune, prunedEndpoint, mentionsRemoval, eventRoots, commandRoots, child] using ih ready child
        | remove actor =>
          change actor = name at same
          subst actor
          have removed : middle = erase before name := step.2
          subst middle
          exact ⟨by simpa [prune, prunedEndpoint, mentionsRemoval, eventRoots, commandRoots, child] using tail,
            by simp [mentionsRemoval]⟩
      · obtain ⟨still, projected, root⟩ := step_command_prune step ready same
        obtain ⟨remaining, finalReady⟩ := ih still ((command_source_root command step same).trans child)
        have kept := RootExec.cons (event := .command command) projected remaining
        have keptRoots : eventRoots (erase before name) (.command command) = eventRoots before (.command command) := root
        rw [keptRoots] at kept
        cases command with
        | insert => exact ⟨kept, finalReady⟩
        | retire target => exact ⟨by simpa [prune, show target ≠ name from same] using kept, finalReady⟩
        | remove target =>
          have distinct : target ≠ name := same
          exact ⟨by simpa [prune, prunedEndpoint, mentionsRemoval, distinct] using kept,
            by simpa [mentionsRemoval, distinct] using finalReady⟩


end Cordis.Repairs.Vestigial
