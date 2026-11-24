import Cordis.Repairs.GuardedOpenHistory

/-! The origin of a surviving row and the actual entry landing of an
active actor are determined by the guarded execution. -/
namespace Cordis.Repairs.GuardedHistory
open Calculus Stages LegalHistory Incarnation
open OrchestrationSorting (Command)
universe u
variable {Name Key Value Code Error : Type u} [DecidableEq Name] [DecidableEq Key]
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
variable {program : Code → Instruction Name Key Value Code Error} {last : Nat}

/-- Find the actual creation event of the incarnation present at a cut. -/
theorem Trace.resident_birth (trace : Trace program last) {name : Name} {time : Nat}
    (bounded : time ≤ last) {row : F} (found : trace.state time name = some row) :
    ∃ birth, birth < time ∧ Residency trace.state name (birth + 1) time ∧
      trace.state birth name = none ∧
      ∃ original, trace.state (birth + 1) name = some original ∧
        original.component = row.component ∧ original.parent = row.parent := by
  cases tag : birthAt trace.state name time with
  | none =>
    have absent := birthAt_none.mp tag
    rw [found] at absent
    cases absent
  | some index =>
    have lives := resident_of_birthAt tag
    have ordered := lives.ordered
    have positive : 0 < index := by
      apply Nat.pos_of_ne_zero
      intro impossible
      have atStart := lives.present 0 (by omega) (Nat.zero_le _)
      rw [trace.start] at atStart
      exact atStart rfl
    have cut : index - 1 + 1 = index := by omega
    have vacant := lives.boundary.resolve_left (by omega)
    have live : trace.state (index - 1 + 1) name ≠ none := by
      rw [cut]
      exact lives.present _ (Nat.le_refl _) ordered
    cases originalAt : trace.state (index - 1 + 1) name with
    | none => exact False.elim (live originalAt)
    | some original =>
      have origin : trace.state index name = some original := cut ▸ originalAt
      have metadata := lives.metadata_of_stable
        (fun point valid => transition_stable (trace.step point valid).1) bounded origin found
      exact ⟨index - 1, by omega, cut ▸ lives, vacant, original, originalAt, metadata⟩

/-- A legal retirement or removal targets the row present before the
command. Its notes identify the actual birth of that incarnation. -/
theorem Trace.retire_remove_birth (trace : Trace program last) {cut : Nat} {name : Name}
    (bounded : cut < last) (command : trace.event cut = .command (.retire name) ∨
      trace.event cut = .command (.remove name)) :
    ∃ birth row original, birth < cut ∧ trace.state cut name = some row ∧
      (trace.notes cut).1 name = some (birth + 1) ∧
      Residency trace.state name (birth + 1) cut ∧ trace.state birth name = none ∧
      trace.state (birth + 1) name = some original ∧
      original.component = row.component ∧ original.parent = row.parent := by
  have step := (trace.step cut bounded).1
  have present : trace.state cut name ≠ none := by
    rcases command with entered | removed
    · rw [entered] at step
      exact (show (Command.retire name).Step (trace.state cut) (trace.state (cut + 1)) from step).1
    · rw [removed] at step
      exact Transposition.removable_present _ name
        (show (Command.remove name).Step (trace.state cut) (trace.state (cut + 1)) from step).1
  cases found : trace.state cut name with
  | none => exact False.elim (present found)
  | some row =>
    obtain ⟨birth, earlier, lives, vacant, original, atBirth, fields⟩ :=
      trace.resident_birth (Nat.le_of_lt bounded) found
    refine ⟨birth, row, original, earlier, rfl, ?_, lives, vacant, atBirth, fields⟩
    rw [trace.notes_eq cut (Nat.le_of_lt bounded)]
    exact birthAt_eq_some.mpr lives

/-- A resident root still has the exact component payload of its actual
external insertion. -/
theorem Trace.resident_root_insertion (trace : Trace program last)
    (openOnly : ¬ Nonempty (ClosedEpisode trace))
    {time : Nat} (bounded : time ≤ last) {name : Name} {row : F}
    (found : trace.state time name = some row) (root : row.parent = none) :
    ∃ birth, birth < time ∧ Residency trace.state name (birth + 1) time ∧
      trace.event birth = .command (.insert name row.component) ∧
      trace.state (birth + 1) name = some (fresh row.component none) := by
  obtain ⟨birth, earlier, lives, vacant, original, atBirth, sameComponent, sameParent⟩ :=
    trace.resident_birth bounded found
  have step := (trace.step birth (by omega)).1
  rcases transition_cases step with native | ⟨actor, unload, _⟩
  · have fromRoot : rootAt (trace.state birth) name = false := by simp [rootAt, vacant]
    have toRoot : rootAt (trace.state (birth + 1)) name = true := by simp [rootAt, atBirth, sameParent, root]
    have event : (trace.event birth).Step program (trace.state birth) (trace.state (birth + 1)) := by
      cases tag : trace.event birth with
      | command command =>
        rw [tag] at step
        exact step
      | lifecycle kind actor =>
        rw [tag] at native
        exact native
    obtain ⟨component, insertion⟩ := root_origin event name fromRoot toRoot
    rw [insertion] at step
    have actual := (show (Command.insert name component).Step (trace.state birth) (trace.state (birth + 1)) from step).2
    have inserted : trace.state (birth + 1) name = some (fresh component none) := by
      rw [actual]
      exact put_self _ _ _
    have same := Option.some.inj (inserted.symm.trans atBirth)
    have payload : component = row.component := (congrArg Fiber.component same).trans sameComponent
    exact ⟨birth, earlier, lives, by simpa only [payload] using insertion, by simpa only [payload] using inserted⟩
  · exact False.elim (trace.no_unload openOnly (by omega) unload)

/-- A resident child was actually allocated by its recorded parent. The
parent's event and the child's exact declaration are recovered at that cut. -/
theorem Trace.resident_child_creation (trace : Trace program last)
    (openOnly : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    {time : Nat} (bounded : time ≤ last) {name parent : Name} {row : F}
    (found : trace.state time name = some row) (child : row.parent = some parent) :
    ∃ birth kind, birth < time ∧ Residency trace.state name (birth + 1) time ∧
      trace.event birth = .lifecycle kind parent ∧
      trace.state (birth + 1) name = some (fresh row.component (some parent)) := by
  obtain ⟨birth, earlier, lives, vacant, original, atBirth, sameComponent, sameParent⟩ :=
    trace.resident_birth bounded found
  have present : trace.state (birth + 1) name ≠ none := by simp [atBirth]
  cases event : trace.event birth with
  | command command =>
    have step := (trace.step birth (by omega)).1
    rw [event] at step
    obtain ⟨ready, edit⟩ := (show command.Step (trace.state birth) (trace.state (birth + 1)) from step)
    cases command with
    | insert actor component =>
      by_cases same : name = actor
      · subst actor
        change trace.state (birth + 1) = put (trace.state birth) name (fresh component none) at edit
        rw [edit, put_self] at atBirth
        have equal := Option.some.inj atBirth
        have impossible := (congrArg Fiber.parent equal).trans (sameParent.trans child)
        cases impossible
      · exact False.elim (present ((congrFun edit name).trans
          ((CausalCommands.apply_other (Command.insert actor component) _ name same).trans vacant)))
    | retire actor =>
      apply False.elim (present _)
      rw [edit]
      exact (Transposition.retire_presence _ _ _).mpr vacant
    | remove actor =>
      apply False.elim (present _)
      rw [edit]
      change erase (trace.state birth) actor name = none
      by_cases same : name = actor <;> simp [erase, same, vacant]
  | lifecycle kind actor =>
    obtain ⟨active, step⟩ := trace.activation_at openOnly quiet (by omega) event
    have different : actor ≠ name := by
      intro same
      subst name
      obtain ⟨_, _, present, _, _⟩ := Transposition.activation_source program step active
      rw [vacant] at present
      cases present
    have creation := (Transposition.activation_creates_iff program step active name different).mpr ⟨vacant, present⟩
    obtain ⟨component, newborn⟩ := EpisodeBoundary.born_row vacant creation
    have same := Option.some.inj (newborn.symm.trans atBirth)
    have owner : actor = parent := Option.some.inj ((congrArg Fiber.parent same).trans (sameParent.trans child))
    have payload : component = row.component := (congrArg Fiber.component same).trans sameComponent
    exact ⟨birth, kind, earlier, lives, by simpa only [owner] using event, by simpa only [owner, payload] using newborn⟩

/-- In a quiet history after closed-episode excision, the target of a
child-directed command refers back to an actual parent lifecycle event.
The command and its target carry the same birth recorded by the execution. -/
theorem Trace.child_command_origin (trace : Trace program last)
    (openOnly : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    {cut : Nat} {name parent : Name} {row : F} (bounded : cut < last)
    (command : trace.event cut = .command (.retire name) ∨
      trace.event cut = .command (.remove name))
    (found : trace.state cut name = some row) (child : row.parent = some parent) :
    ∃ birth kind, birth < cut ∧ (trace.notes cut).1 name = some (birth + 1) ∧
      trace.event birth = .lifecycle kind parent ∧
      trace.state (birth + 1) name = some (fresh row.component (some parent)) := by
  obtain ⟨birth, kind, earlier, lives, event, newborn⟩ :=
    trace.resident_child_creation openOnly quiet (Nat.le_of_lt bounded) found child
  obtain ⟨recorded, _, _, _, _, stamp, recordedLifetime, _⟩ :=
    trace.retire_remove_birth bounded command
  have same : recorded + 1 = birth + 1 := Option.some.inj
    ((birthAt_eq_some.mpr recordedLifetime).symm.trans (birthAt_eq_some.mpr lives))
  exact ⟨birth, kind, earlier, same ▸ stamp, event, newborn⟩

/-- A reservation held since its birth excludes a competing allocation
at any intervening cut, independent of the proposed fresh name. -/
theorem Trace.reservation_precedes_residency (trace : Trace program last)
    {owner candidate : Name} {birth cutoff : Nat}
    (lives : Residency trace.state owner birth last) (bounded : cutoff ≤ last)
    {row : F} (first : trace.state birth owner = some row)
    {component : Component Key Code} {parent : Option Name}
    (ready : Insertable (trace.state cutoff) candidate component parent) (key : Key)
    (reserved : row.component.provides key = true) (requested : component.provides key = true) :
    cutoff < birth := by
  apply Nat.lt_of_not_ge
  intro before
  cases atCut : trace.state cutoff owner with
  | none => exact lives.present cutoff before bounded atCut
  | some current =>
    have same := ((lives.prefix cutoff before bounded).metadata_of_stable
      (fun point valid => transition_stable (trace.step point valid).1) bounded first atCut).1
    have conflict := ready.2.2 owner key
    rw [atCut] at conflict
    exact conflict requested (by rwa [← same])

private def advancedFromEntry (row : F) : Prop :=
  match row.phase with
  | .reloading code _ _ => code ≠ row.component.entry
  | .active _ _ => True
  | _ => False

private theorem Trace.entry_landing_of_advanced (trace : Trace program last)
    (openOnly : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    {time : Nat} (bounded : time ≤ last) {name : Name} {row : F}
    (found : trace.state time name = some row) (advanced : advancedFromEntry row) :
    ∃ cut kind, cut < time ∧ trace.event cut = .lifecycle kind name ∧
      ∃ landed token next, Land program name row.component.entry (trace.state cut) landed token next := by
  classical
  induction time generalizing row with
  | zero =>
    rw [trace.start] at found
    cases found
  | succ time ih =>
    have earlier {old : F} (previous : trace.state time name = some old)
        (component : old.component = row.component) (already : advancedFromEntry old) :
        ∃ cut kind, cut < time + 1 ∧ trace.event cut = .lifecycle kind name ∧
          ∃ landed token next, Land program name row.component.entry (trace.state cut) landed token next := by
      obtain ⟨cut, kind, before, event, landing⟩ := ih (by omega) previous already
      exact ⟨cut, kind, by omega, event, component ▸ landing⟩
    cases tag : trace.event time with
    | command command =>
      have stepped := (trace.step time (by omega)).1
      rw [tag] at stepped
      obtain ⟨_, edit⟩ := (show command.Step (trace.state time) (trace.state (time + 1)) from stepped)
      rw [edit] at found
      by_cases same : name = command.actor
      · cases command with
        | insert actor component =>
          change name = actor at same
          subst actor
          change put (trace.state time) name (fresh component none) name = some row at found
          rw [put_self] at found
          cases Option.some.inj found
          exact False.elim advanced
        | retire actor =>
          change name = actor at same
          subst actor
          cases previous : trace.state time name with
          | none => simp [Command.apply, Calculus.retire, Calculus.modify, previous] at found
          | some old =>
            have sameRow : {old with retired := true} = row := Option.some.inj
              (by simpa [Command.apply, Calculus.retire, Calculus.modify, previous] using found)
            subst row
            exact earlier previous rfl advanced
        | remove actor =>
          change name = actor at same
          subst actor
          simp [Command.apply, erase] at found
      · rw [CausalCommands.apply_other command _ _ same] at found
        exact earlier found rfl advanced
    | lifecycle kind actor =>
      obtain ⟨active, step⟩ := trace.activation_at openOnly quiet (by omega) tag
      by_cases same : name = actor
      · subst actor
        have finish_entry {old : F} {code : Code} {word : List (Inverse Name Key Value)}
            {view : View Name Key} {landed : R} {token : Inverse Name Key Value} {next : Option Code}
            (present : trace.state time name = some old) (reloading : old.phase = .reloading code word view)
            (land : Land program name code (trace.state time) landed token next) :
            ∃ cut kind, cut < time + 1 ∧ trace.event cut = .lifecycle kind name ∧
              ∃ stateAfter tokenAfter nextAfter,
                Land program name row.component.entry (trace.state cut) stateAfter tokenAfter nextAfter := by
          have component := (Frame.step_stable program step.toCalculus name old row present found).1
          by_cases entry : code = row.component.entry
          · exact ⟨time, kind, by omega, tag, landed, token, next, entry ▸ land⟩
          · exact earlier present component (by simpa [advancedFromEntry, reloading, component] using entry)
        generalize endpoint : trace.state (time + 1) = nextState at step found
        cases kind with
        | begin =>
          cases step with
          | begin _ _ previous view present inactive free target =>
            have actual := mark_self (trace.state time) name previous (.reloading previous.component.entry [] view) present
            have sameRow := Option.some.inj (actual.symm.trans found)
            subst row
            exact False.elim (advanced rfl)
        | iter =>
          cases step with
          | iter _ _ _ _ _ _ _ _ _ present reloading _ land => exact finish_entry present reloading land
        | finish =>
          cases step with
          | finish _ _ _ _ _ _ _ _ present reloading _ land => exact finish_entry present reloading land
        | _ => simp [Lifecycle.rule, Transposition.Activation] at active
      · cases previous : trace.state time name with
        | none =>
          have creation := (Transposition.activation_creates_iff program step active name (Ne.symm same)).mpr
            ⟨previous, by simp [found]⟩
          obtain ⟨component, birth⟩ := EpisodeBoundary.born_row previous creation
          have rowEq := Option.some.inj (birth.symm.trans found)
          subst row
          exact False.elim advanced
        | some old =>
          obtain ⟨table, retained⟩ := Transposition.activation_other_table program step active name old same previous
          have rowEq := Option.some.inj (retained.symm.trans found)
          subst row
          exact earlier previous rfl advanced

/-- A resident active row has actually landed its declared entry code.
The witness carries the source lifecycle event and full native landing. -/
theorem Trace.active_entry_landing (trace : Trace program last)
    (openOnly : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    {time : Nat} (bounded : time ≤ last) {name : Name} {row : F}
    (found : trace.state time name = some row) (available : row.phase.available) :
    ∃ cut kind, cut < time ∧ trace.event cut = .lifecycle kind name ∧
      ∃ landed token next, Land program name row.component.entry (trace.state cut) landed token next := by
  apply trace.entry_landing_of_advanced openOnly quiet bounded found
  cases phase : row.phase <;> simp [phase, Phase.available, advancedFromEntry] at available ⊢

end Cordis.Repairs.GuardedHistory
