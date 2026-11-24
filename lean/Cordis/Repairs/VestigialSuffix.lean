import Cordis.Repairs.VestigialRestore
import Cordis.Repairs.VestigialReplay
import Cordis.Repairs.IncarnationExample

/-! Suffix replay for a finite set of withdrawn children. Once an original
incarnation is removed, later uses of the same name are retained. -/
namespace Cordis.Repairs.Vestigial
open Calculus Stages StageRecovery LegalHistory
universe u
variable {Name Key Value Code Error : Type u} [DecidableEq Name] [DecidableEq Key]
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "Ev" => Event Name Key Code
local notation "Cmd" => OrchestrationSorting.Command Name Key Code

def pruneAll : List Name → List Ev → List Ev
  | [], events => events
  | name :: names, events => pruneAll names (prune name events)

def eraseAll : List Name → R → R
  | [], state => state
  | name :: names, state => eraseAll names (erase state name)

def stillPresent (names : List Name) (events : List Ev) : List Name :=
  names.filter fun name => !(events.any (mentionsRemoval name))

omit [DecidableEq Key] in
theorem prune_preserves_other_removals {deleted name : Name} (different : name ≠ deleted) (events : List Ev) :
    (prune deleted events).any (mentionsRemoval name) = events.any (mentionsRemoval name) := by
  induction events with
  | nil => rfl
  | cons event rest ih =>
    cases event with
    | lifecycle => simpa [prune, mentionsRemoval] using ih
    | command command =>
      cases command with
      | insert => simpa [prune, mentionsRemoval] using ih
      | retire actor =>
        by_cases same : actor = deleted <;> simpa [prune, mentionsRemoval, same] using ih
      | remove actor =>
        by_cases same : actor = deleted
        · subst actor
          simp [prune, mentionsRemoval, Ne.symm different]
        · simp [prune, mentionsRemoval, same, ih]

omit [DecidableEq Key] in
theorem eraseAll_apply (names : List Name) (state : R) (name : Name) :
    eraseAll names state name = if name ∈ names then none else state name := by
  induction names generalizing state with
  | nil => simp [eraseAll]
  | cons first rest ih =>
    rw [eraseAll, ih]
    by_cases here : name = first <;> by_cases later : name ∈ rest <;> simp [erase, here, later]

omit [DecidableEq Key] in
theorem eraseAll_outside (names : List Name) (state : R) (name : Name) (outside : name ∉ names) :
    eraseAll names state name = state name := by
  rw [eraseAll_apply, if_neg outside]

variable {program : Code → Instruction Name Key Value Code Error}

/-- Apply the one-child replay successively. Distinct withdrawals cannot
erase each other's removal events, so the final mask is computed from
the original suffix. -/
theorem prune_all {events : List Ev} {before final : R} {roots : List Cmd}
    (execution : RootExec program events before final roots)
    (names : List Name) (distinct : names.Nodup)
    (children : ∀ name ∈ names, Removable before name ∧ rootAt before name = false) :
    RootExec program (pruneAll names events) (eraseAll names before)
      (eraseAll (stillPresent names events) final) roots := by
  induction names generalizing before events final with
  | nil => exact execution
  | cons first rest ih =>
    obtain ⟨notInRest, restDistinct⟩ := List.nodup_cons.mp distinct
    obtain ⟨ready, child⟩ := children first List.mem_cons_self
    obtain ⟨projected, _⟩ := prune_suffix execution first ready child
    have others : ∀ name ∈ rest, Removable (erase before first) name ∧ rootAt (erase before first) name = false := by
      intro name member
      have different : name ≠ first := by
        intro same
        subst name
        exact notInRest member
      obtain ⟨leaf, wasChild⟩ := children name (List.mem_cons_of_mem _ member)
      exact ⟨erase_removable different leaf, by simpa [rootAt, erase, different] using wasChild⟩
    have replayed := ih projected restDistinct others
    have mask : stillPresent rest (prune first events) = stillPresent rest events := by
      apply List.filter_congr
      intro name member
      have different : name ≠ first := fun same => notInRest (same ▸ member)
      simp only [prune_preserves_other_removals different]
    rw [mask] at replayed
    cases removed : events.any (mentionsRemoval first) <;>
      simpa [pruneAll, eraseAll, stillPresent, prunedEndpoint, removed] using replayed

/-- No name outside the selected vestigial incarnations is lost.
Every table coordinate is preserved, even at erased names. -/
theorem prune_all_endpoint {events : List Ev} {before final : R} {roots : List Cmd}
    (execution : RootExec program events before final roots)
    (names : List Name) (distinct : names.Nodup)
    (children : ∀ name ∈ names, Removable before name ∧ rootAt before name = false) :
    let forgotten := stillPresent names events
    (∀ name, name ∉ forgotten → eraseAll forgotten final name = final name) ∧
      RuleEvaluation.TablesUnchanged final (eraseAll forgotten final) := by
  dsimp only
  refine ⟨fun name outside => eraseAll_outside _ _ name outside, ?_⟩
  have leaves : ∀ name ∈ stillPresent names events, Removable final name := by
    intro name member
    obtain ⟨inNames, noRemoval⟩ := List.mem_filter.mp member
    obtain ⟨ready, child⟩ := children name inNames
    exact (prune_suffix execution name ready child).2 (by simpa using noRemoval)
  have tables (remaining : List Name) (state : R)
      (distinct : remaining.Nodup) (leaves : ∀ name ∈ remaining, Removable state name) :
      RuleEvaluation.TablesUnchanged state (eraseAll remaining state) := by
    induction remaining generalizing state with
    | nil => intro _ _; rfl
    | cons name rest ih =>
      intro owner key
      obtain ⟨outside, restDistinct⟩ := List.nodup_cons.mp distinct
      have restReady : ∀ child ∈ rest, Removable (erase state name) child := by
        intro child member
        have original := leaves child (List.mem_cons_of_mem _ member)
        have different : child ≠ name := fun same => outside (same ▸ member)
        exact erase_removable different original
      exact (Transposition.removable_erase_tables state name (leaves name List.mem_cons_self) owner key).symm.trans
        (ih (erase state name) restDistinct restReady owner key)
  exact tables _ _ ((List.filter_sublist (l := names)).nodup distinct) leaves

end Cordis.Repairs.Vestigial

namespace Cordis.Repairs.IncarnationExample
open Calculus CommandBarrier LegalHistory Vestigial

/-- The child's Remove is omitted. The root insertion and retirement at
the reused name both survive with their original payloads and endpoint. -/
theorem prune_keeps_reissued_root :
    RootExec program
      (prune 1 [.command removeChild, .command reissueCommand, .command retireAgain])
      (erase before 1) retiredRoot [reissueCommand, retireAgain] := by
  have suffix : RootExec program [.command removeChild, .command reissueCommand, .command retireAgain]
      before retiredRoot [reissueCommand, retireAgain] :=
    .cons (event := .command removeChild) ⟨removal_enabled, rfl⟩
      (.cons (event := .command reissueCommand) ⟨reuse_enabled, rfl⟩
        (.cons (event := .command retireAgain) ⟨by change some _ ≠ none; simp, rfl⟩ (.nil _)))
  exact (prune_suffix suffix 1 removal_enabled rfl).1

open Incarnation (birthAt)
open IncarnationReplay (replayAt track)

private theorem reuse_trace_roots : PaperLifecycleClaims.RootInsertions trace := by
  intro time bounded rule
  have range : time = 0 ∨ time = 1 ∨ time = 2 ∨ time = 3 ∨ time = 4 ∨ time = 5 ∨ time = 6 := by omega
  rcases range with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨_, rfl, rfl⟩ | cases rule

/-- The indexed suffix deletes only the old child's Remove. The root
inserted at the very same name is retained with its original payload.
The parent's old retirement token still cannot retire that root. -/
theorem prune_indexed_reissue :
    (retainedFrom trace 1 4 4 3 = [5, 6]) ∧
    (∃ moved : Indexed.Trace program (erase before 1) 2,
      moved.rule 0 = .insert ∧ moved.actor 0 = 1 ∧ moved.state 1 = reissued ∧
      moved.rule 1 = .retire ∧ moved.actor 1 = 1 ∧ moved.state 2 = retiredRoot) ∧
    let states := projectedState trace 1 4
    birthAt states 1 4 = none ∧ birthAt states 1 6 = some 6 ∧
      track states trace.actor 6 0 = [⟨.retire 1, 3⟩] ∧
      replayAt states 6 (track states trace.actor 6 0) = reissued := by
  have ready : Removable (trace.state 4) 1 := removal_enabled
  refine ⟨rfl, ?_, ?_⟩
  · obtain ⟨moved, last, aligns, _⟩ := compress_suffix trace reuse_trace_roots (cut := 4) ready 4 3
      (by decide) (by decide)
    obtain ⟨inserted, root, _, replaces⟩ := aligns 0 (by decide)
    obtain ⟨retires, newRoot, _, _⟩ := aligns 1 (by decide)
    exact ⟨moved, inserted, root, replaces, retires, newRoot, last⟩
  · dsimp only
    refine ⟨rfl, rfl, ?_, ?_⟩
    · rw [projected_track trace reuse_trace_roots ready 6 (by decide)]
      rfl
    · rw [projected_replayAt trace reuse_trace_roots ready 6 (by decide)]
      rfl

/-- Recompute the annotations on the compressed native suffix itself.
The retained insertion carries stamp 6, and the inherited token still
carries stamp 3 at the cut before the root's own retirement. -/
theorem compressed_reissue_replay :
    ∃ moved : Indexed.Trace program (erase before 1) 1,
      moved.state 1 = reissued ∧
      let projected := projectedState trace 1 4
      let notes := recordSuffix moved.state moved.actor 0 [5] (cutNotes projected trace.actor 4)
      notes.1 1 = some 6 ∧ notes.2 0 = [⟨.retire 1, 3⟩] ∧
        IncarnationReplay.replay notes.1 (notes.2 0) (moved.state 1) = reissued := by
  have ready : Removable (trace.state 4) 1 := removal_enabled
  obtain ⟨moved, endpoint, _, notes⟩ := compress_suffix trace reuse_trace_roots (cut := 4) ready 4 2
    (by decide) (by decide)
  refine ⟨moved, endpoint, ?_⟩
  dsimp only
  change recordSuffix moved.state moved.actor 0 [5]
    (cutNotes (projectedState trace 1 4) trace.actor 4) =
      cutNotes (projectedState trace 1 4) trace.actor 6 at notes
  rw [notes, show moved.state 1 = reissued from endpoint]
  exact ⟨rfl, rfl, rfl⟩

end Cordis.Repairs.IncarnationExample
