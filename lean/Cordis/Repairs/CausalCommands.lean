import Cordis.OrchestrationSorting

/-! Payload-preserving orchestration exchanges for the proposed repair of
Theorem 80. An exchange requires actual applicability, including insertion
conflicts and removal guards. Distinct names alone do not license reordering.
These are local exchange and finite-history results, not an unqualified
all-roots-first normalization theorem. -/
namespace Cordis.Repairs.CausalCommands
open Calculus Stages OrchestrationSorting
universe u
variable {Name Key Value Code Error : Type u} [DecidableEq Name] [DecidableEq Key]
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
local notation "Cmd" => Command Name Key Code

omit [DecidableEq Key] in
theorem apply_other (command : Cmd) (state : R) (name : Name) (different : name ≠ command.actor) :
    command.apply state name = state name := by
  cases command <;> simp_all [Command.apply, Command.actor, put, erase, Calculus.retire, Calculus.modify]

omit [DecidableEq Key] in
/-- The state updates commute at distinct names; legality is a separate
obligation discharged below, not inferred from this function equality. -/
theorem updates_commute (first second : Cmd) (state : R) (different : first.actor ≠ second.actor) :
    first.apply (second.apply state) = second.apply (first.apply state) := by
  funext name
  cases first <;> cases second <;>
    simp only [Command.actor] at different <;>
    simp only [Command.apply, put, erase, Calculus.retire, Calculus.modify]
  all_goals split <;> split <;> simp_all

omit [DecidableEq Key] in
private theorem no_children_preserved (command : Cmd) (state : R) (parent : Name)
    (old : ∀ child, match state child with
      | none => True | some fiber => fiber.parent ≠ some parent) :
    ∀ child, match command.apply state child with
      | none => True | some fiber => fiber.parent ≠ some parent := by
  intro child
  cases command with
  | insert name component =>
    by_cases same : child = name
    · simp [Command.apply, put, same, fresh]
    · simpa [Command.apply, put, same] using old child
  | retire name =>
    by_cases same : child = name
    · subst child
      cases present : state name with
      | none => simp [Command.apply, Calculus.retire, Calculus.modify, present]
      | some entry => simpa [Command.apply, Calculus.retire, Calculus.modify, present] using old name
    · simpa [Command.apply, Calculus.retire, Calculus.modify, same] using old child
  | remove name =>
    by_cases same : child = name
    · simp [Command.apply, erase, same]
    · simpa [Command.apply, erase, same] using old child

private theorem origins_or_insert (command : Cmd) (state : R) (name : Name) (fiber : F)
    (found : command.apply state name = some fiber) :
    (∃ old, state name = some old ∧ old.component = fiber.component) ∨
      ∃ component, command = .insert name component ∧ fiber.component = component := by
  cases command with
  | insert actor component =>
    by_cases same : name = actor
    · subst name
      have eq : fresh component none = fiber := Option.some.inj (by simpa [Command.apply, put] using found)
      subst fiber
      exact .inr ⟨component, rfl, rfl⟩
    · exact .inl ⟨fiber, by simpa [Command.apply, put, same] using found, rfl⟩
  | retire actor =>
    exact .inl (WellFormed.modify_origins state actor (fun f => {f with retired := true})
      (fun _ => rfl) name fiber found)
  | remove actor =>
    by_cases same : name = actor
    · simp [Command.apply, erase, same] at found
    · exact .inl ⟨fiber, by simpa [Command.apply, erase, same] using found, rfl⟩

private theorem insertion_enabled_after (state : R) (name : Name) (component : Component Key Code)
    (second : Cmd) (different : name ≠ second.actor)
    (firstReady : Insertable state name component none)
    (secondLater : second.Enabled (put state name (fresh component none))) :
    Insertable (second.apply state) name component none := by
  refine ⟨(apply_other second state name different).trans firstReady.1, by simp, ?_⟩
  intro other key
  cases found : second.apply state other with
  | none => trivial
  | some fiber =>
    obtain original | ⟨newComponent, rfl, declaration⟩ := origins_or_insert second state other fiber found
    · obtain ⟨old, oldAt, same⟩ := original
      have excludes := firstReady.2.2 other key
      simpa [oldAt, same] using excludes
    · intro provided newProvided
      have excludes := secondLater.2.2 name key
      simp only [put_self, fresh] at excludes
      exact excludes (declaration ▸ newProvided) provided

theorem enabled_after (first second : Cmd) (state : R) (different : first.actor ≠ second.actor)
    (firstReady : first.Enabled state) (secondLater : second.Enabled (first.apply state)) :
    first.Enabled (second.apply state) := by
  cases first with
  | insert name component => exact insertion_enabled_after state name component second different firstReady secondLater
  | retire name =>
    change second.apply state name ≠ none
    rw [apply_other second state name different]
    exact firstReady
  | remove name =>
    change Removable (second.apply state) name
    cases found : state name with
    | none => simp [Command.Enabled, Removable, found] at firstReady
    | some fiber =>
      simp only [Command.Enabled, Removable, found] at firstReady
      simp only [Removable, apply_other second state name different, found]
      refine ⟨firstReady.1, firstReady.2.1, firstReady.2.2.1, ?_⟩
      have oldChildren : ∀ child, match state child with
          | none => True | some entry => entry.parent ≠ some name := by
        intro child
        cases h : state child with
        | none => trivial
        | some entry => simpa only [h] using firstReady.2.2.2 child
      have children := no_children_preserved second state name oldChildren
      intro child
      cases h : second.apply state child with
      | none => trivial
      | some entry => simpa only [h] using children child

/-- Two actual commands can exchange if the second is already legal before
the first. The result retains every payload and the exact final registry. -/
theorem command_diamond (first second : Cmd) {before middle final : R}
    (a : first.Step before middle) (b : second.Step middle final)
    (different : first.actor ≠ second.actor) (earlier : second.Enabled before) :
    ∃ swapped, second.Step before swapped ∧ first.Step swapped final := by
  obtain ⟨firstReady, rfl⟩ := a
  obtain ⟨secondReady, rfl⟩ := b
  refine ⟨second.apply before, ⟨earlier, rfl⟩, enabled_after first second before different firstReady secondReady, ?_⟩
  exact (updates_commute first second before different).symm

omit [DecidableEq Key] in
/-- Restoring an erased entry affects a different root insertion only
through the restored provision reservations. -/
theorem root_insertable_before_erase (state : R) {removed name : Name}
    (different : name ≠ removed) (component : Component Key Code) :
    Insertable state name component none ↔
      Insertable (erase state removed) name component none ∧
      ∀ entry, state removed = some entry →
        ∀ key, component.provides key → ¬ entry.component.provides key := by
  constructor
  · intro enabled
    refine ⟨⟨by simpa [erase, different] using enabled.1, by simp, ?_⟩, ?_⟩
    · intro other key
      by_cases same : other = removed
      · simp [erase, same]
      · simpa [erase, same] using enabled.2.2 other key
    · intro entry present key
      simpa only [present] using enabled.2.2 removed key
  · rintro ⟨later, disjoint⟩
    refine ⟨by simpa [erase, different] using later.1, by simp, ?_⟩
    intro other key
    by_cases same : other = removed
    · subst other
      cases present : state removed with
      | none => trivial
      | some entry => exact disjoint entry present key
    · simpa [erase, same] using later.2.2 other key

/-- An actual removal followed by a distinct root insertion can be
exchanged exactly when the removed entry reserved none of the new root's
provision keys. The reversed pair retains the original endpoint. -/
theorem remove_insert_exchange_iff {before middle final : R} {removed name : Name}
    (different : name ≠ removed) (component : Component Key Code)
    (removal : (Command.remove (Key := Key) (Code := Code) removed).Step before middle)
    (insertion : (Command.insert name component).Step middle final) :
    (∃ swapped, (Command.insert name component).Step before swapped ∧
      (Command.remove removed).Step swapped final) ↔
      ∀ entry, before removed = some entry →
        ∀ key, component.provides key → ¬ entry.component.provides key := by
  constructor
  · rintro ⟨_, insertFirst, _⟩
    exact ((root_insertable_before_erase before different component).mp insertFirst.1).2
  · intro released
    obtain ⟨_, rfl⟩ := removal
    have earlier := (root_insertable_before_erase before different component).mpr ⟨insertion.1, released⟩
    exact command_diamond (.remove removed) (.insert name component)
      ⟨by assumption, rfl⟩ insertion (Ne.symm different) earlier

/-- A foreign erasure changes the removal guard exactly when it removes
a child of the second target. -/
theorem removable_before_erase (state : R) {removed name : Name} (different : name ≠ removed) :
    Removable state name ↔ Removable (erase state removed) name ∧
      ∀ entry, state removed = some entry → entry.parent ≠ some name := by
  cases present : state name with
  | none => simp [Removable, erase, different, present]
  | some row =>
    simp only [Removable, Transposition.erase_other state name removed different, present]
    constructor
    · rintro ⟨retired, inactive, empty, leaf⟩
      refine ⟨⟨retired, inactive, empty, ?_⟩, ?_⟩
      · intro child
        by_cases gone : child = removed
        · simp [erase, gone]
        · simpa only [Transposition.erase_other state child removed gone] using leaf child
      · intro entry found
        simpa only [found] using leaf removed
    · rintro ⟨⟨retired, inactive, empty, leaf⟩, detached⟩
      refine ⟨retired, inactive, empty, ?_⟩
      intro child
      by_cases gone : child = removed
      · subst child
        cases found : state removed with
        | none => trivial
        | some entry => exact detached entry found
      · simpa only [Transposition.erase_other state child removed gone] using leaf child

theorem removable_retire_other (state : R) {retiring name : Name} (different : name ≠ retiring) :
    Removable (Calculus.retire state retiring) name ↔ Removable state name := by
  cases present : state name with
  | none => simp [Removable, Transposition.retire_other state name retiring different, present]
  | some row =>
    simp only [Removable, Transposition.retire_other state name retiring different, present]
    apply and_congr_right
    intro _
    apply and_congr_right
    intro _
    apply and_congr_right
    intro _
    apply forall_congr'
    intro child
    by_cases changed : child = retiring
    · subst child
      cases found : state retiring <;> simp [Calculus.retire, Calculus.modify, found]
    · rw [Transposition.retire_other state child retiring changed]

theorem enabled_retire_other (state : R) {retiring : Name} (command : Cmd) (different : command.actor ≠ retiring) :
    command.Enabled (Calculus.retire state retiring) ↔ command.Enabled state := by
  cases command with
  | insert name component => exact Transposition.retire_insertable state retiring name component none
  | retire name =>
    change name ≠ retiring at different
    change Calculus.retire state retiring name ≠ none ↔ state name ≠ none
    rw [Transposition.retire_other state name retiring different]
  | remove name => exact removable_retire_other state different

end Cordis.Repairs.CausalCommands
