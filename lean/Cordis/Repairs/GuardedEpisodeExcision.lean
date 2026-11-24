import Cordis.Repairs.GuardedEpisodeInterior
import Cordis.Repairs.GuardedCutState

/-! Repaired Lemma 79 on the guarded calculus, including its unchanged
prefix, filtered interior, and incarnation-sensitive suffix. -/
namespace Cordis.Repairs.GuardedHistory
open Calculus Stages LegalHistory
open EpisodeAnnotations (NotesRelated)
open PaperEffectEquations (CoeffectOperations ValueOperationWitness)
open PartialCoeffectIndependenceContracts (tableSetoid)
open PaperObservationEquations (OperationRespects)
open TypedRegistry (encodeProgram RawRegistry Scalar)
open StageRecovery (tableAt TablesRelated)
open Iterators (OptionRel)
universe u
variable {Name Key Code : Type u} {V : Key → Type u} {ops : CoeffectOperations V}
variable [DecidableEq Name] [DecidableEq Key]
variable {program : Code → TypedRegistry.Instruction Name ops Code} {last : Nat}
local notation "A" => Scalar ops
local notation "R" => RawRegistry Name ops Code
local notation "Source" => Trace (encodeProgram program) last

def excisedEvents (trace : Source) (episode : ClosedEpisode trace) (names : List Name) :
    List (Nat × Event Name Key Code) :=
  let stamp := fun time => (time + 1, trace.event time)
  let interior := (List.range' episode.opened (episode.closed - episode.opened)).filter (keepsInterior trace episode)
  let suffix := List.range' (episode.closed + 1) (last - (episode.closed + 1))
  (List.range (episode.opened - 1)).map stamp ++ interior.map stamp ++ GuardedSuffix.pruneAll names (suffix.map stamp)

theorem excision_shortens (trace : Source) (episode : ClosedEpisode trace) (names : List Name) :
    (excisedEvents trace episode names).length < last := by
  have positive := episode.interval.positive
  have ordered := episode.interval.ordered
  have bound := episode.interval.bounded
  have interior := List.length_filter_le (p := keepsInterior trace episode)
    (l := List.range' episode.opened (episode.closed - episode.opened))
  have suffix := (GuardedSuffix.pruneAll_sublist names
    ((List.range' (episode.closed + 1) (last - (episode.closed + 1))).map fun time => (time + 1, trace.event time))).length_le
  simp only [List.length_map, List.length_range'] at interior suffix
  simp only [excisedEvents, List.length_append, List.length_map, List.length_range]
  omega

private theorem episode_cut_partition (trace : Source) (episode : ClosedEpisode trace) :
    List.range last = List.range (episode.opened - 1) ++
      (episode.opened - 1) :: (List.range' episode.opened (episode.closed - episode.opened) ++
        episode.closed :: List.range' (episode.closed + 1) (last - (episode.closed + 1))) := by
  have ordered := episode.interval.ordered
  have positive := episode.interval.positive
  have bound := episode.interval.bounded
  have front : List.range last = List.range' 0 (episode.opened - 1) ++
      List.range' (episode.opened - 1) (last - (episode.opened - 1)) := by
    rw [List.range_eq_range']
    simpa only [Nat.zero_add, show episode.opened - 1 + (last - (episode.opened - 1)) = last by omega] using
      (List.range'_append_1 (s := 0) (m := episode.opened - 1) (n := last - (episode.opened - 1))).symm
  have skipEntry : List.range' (episode.opened - 1) (last - (episode.opened - 1)) =
      (episode.opened - 1) :: List.range' episode.opened (last - episode.opened) := by
    rw [show last - (episode.opened - 1) = (last - episode.opened) + 1 by omega, List.range'_succ,
      show episode.opened - 1 + 1 = episode.opened by omega]
  have splitMiddle : List.range' episode.opened (last - episode.opened) =
      List.range' episode.opened (episode.closed - episode.opened) ++ List.range' episode.closed (last - episode.closed) := by
    simpa only [show episode.opened + (episode.closed - episode.opened) = episode.closed by omega,
      show episode.closed - episode.opened + (last - episode.closed) = last - episode.opened by omega] using
      (List.range'_append_1 (s := episode.opened) (m := episode.closed - episode.opened) (n := last - episode.closed)).symm
  have skipExit : List.range' episode.closed (last - episode.closed) =
      episode.closed :: List.range' (episode.closed + 1) (last - (episode.closed + 1)) := by
    rw [show last - episode.closed = (last - (episode.closed + 1)) + 1 by omega, List.range'_succ]
  rw [front, skipEntry, splitMiddle, skipExit, List.range_eq_range']

/-- Excision retains a subsequence with the exact original events and stamps. -/
theorem excised_sublist (trace : Source) (episode : ClosedEpisode trace) (names : List Name) :
    (excisedEvents trace episode names).Sublist ((List.range last).map fun time => (time + 1, trace.event time)) := by
  let stamp := fun time => (time + 1, trace.event time)
  let middle := List.range' episode.opened (episode.closed - episode.opened)
  let suffix := List.range' (episode.closed + 1) (last - (episode.closed + 1))
  have middleSub : ((middle.filter (keepsInterior trace episode)).map stamp).Sublist (middle.map stamp) :=
    List.Sublist.map stamp List.filter_sublist
  have suffixSub := GuardedSuffix.pruneAll_sublist names (suffix.map stamp)
  unfold excisedEvents
  rw [episode_cut_partition trace episode]
  simp only [List.map_append, List.map_cons, List.append_assoc]
  exact (List.Sublist.cons (stamp (episode.opened - 1))
    (middleSub.append (List.Sublist.cons (stamp episode.closed) suffixSub))).append_left _

private theorem original_roots_split (trace : Source) (episode : ClosedEpisode trace) :
    originalRoots trace =
      ((List.range' 0 (episode.opened - 1)).flatMap fun time => eventRoots (trace.state time) (trace.event time)) ++
      ((List.range' episode.opened (episode.closed - episode.opened)).flatMap fun time =>
        eventRoots (trace.state time) (trace.event time)) ++
      ((List.range' (episode.closed + 1) (last - (episode.closed + 1))).flatMap fun time =>
        eventRoots (trace.state time) (trace.event time)) := by
  obtain ⟨begin, _⟩ := begin_boundary trace episode.interval
  obtain ⟨finish, _⟩ := unload_boundary trace episode.interval
  unfold originalRoots
  rw [episode_cut_partition trace episode]
  simp [begin, finish, eventRoots, List.append_assoc, List.range_eq_range']

omit [DecidableEq Key] in
private theorem erase_vestige_tables (state : R) (names : List Name)
    (ready : ∀ name ∈ names, Removable state name) (name : Name) (key : Key) :
    tableAt (Vestigial.eraseAll names state) name key = tableAt state name key := by
  unfold tableAt
  rw [Vestigial.eraseAll_apply]
  by_cases member : name ∈ names
  · rw [if_pos member]
    have removable := ready name member
    cases found : state name with
    | none => rfl
    | some row =>
      rw [Removable, found] at removable
      exact (removable.2.2.1 key).symm
  · rw [if_neg member]

private theorem erase_vestige_quiet (state : R) (names : List Name) (unique : names.Nodup)
    (ready : ∀ name ∈ names, Removable state name) (quiet : Progress.Quiet state) :
    Progress.Quiet (Vestigial.eraseAll names state) := by
  induction names generalizing state with
  | nil => exact quiet
  | cons first rest ih =>
    obtain ⟨distinct, unique⟩ := List.nodup_cons.mp unique
    have removable := ready first List.mem_cons_self
    have after : Progress.Quiet (erase state first) := by
      intro name row found
      have different : name ≠ first := by intro same; subst name; simp [erase] at found
      have prior := quiet name row ((Transposition.erase_other state _ _ different).symm.trans found)
      cases phase : row.phase with
      | inactive =>
        intro view target
        exact (show ∀ view, ¬ Target state name view by simpa only [phase] using prior) view
          ((Transposition.removable_erase_target _ _ _ different removable _).mp target)
      | active stack view =>
        exact (Transposition.removable_erase_target _ _ _ different removable _).mpr (by simpa only [phase] using prior)
      | reloading | unloading => simp only [phase] at prior
    exact ih (erase state first) unique
      (fun name member => Vestigial.erase_removable (fun same => distinct (same ▸ member))
        (ready name (List.mem_cons_of_mem _ member))) after

/-- The repaired conclusion of the episode deletion lemma, with exact
root order and the allowed erased endpoint rows made explicit. -/
def EpisodeExcised (trace : Source) (episode : ClosedEpisode trace) (observe : ∀ key, Setoid (V key)) : Prop :=
  letI := TypedCoeffectReplay.setoid (Yield := TypedRegistry.Yield ops) observe
  let suffix := (List.range' (episode.closed + 1) (last - (episode.closed + 1))).map
    fun time => (time + 1, trace.event time)
  ∃ names after recorded,
    names.Nodup ∧ (∀ name, name ∈ names ↔ withdraws trace episode episode.closed name = true) ∧
    (∀ name ∈ GuardedSuffix.stillPresent names suffix, Removable (trace.state last) name ∧
      rootAt (trace.state last) name = false) ∧
    GuardedSuffix.ExecWith (encodeProgram program) trace.sourceAt (excisedEvents trace episode names)
      (trace.state 0) (trace.notes 0) after recorded (originalRoots trace) ∧
    StageSimulation.Related Eq (Vestigial.eraseAll (GuardedSuffix.stillPresent names suffix) (trace.state last)) after ∧
    NotesRelated (GuardedSuffix.eraseAllNotes (GuardedSuffix.stillPresent names suffix) (trace.notes last)) recorded ∧
    GuardedSuffix.SavedWordsAgree after recorded ∧ TablesRelated (trace.state last) after ∧
    Progress.Quiet after ∧ (excisedEvents trace episode names).length < last

theorem excise_closed_episode (trace : Source) (episode : ClosedEpisode trace)
    (maximal : ∀ later : ClosedEpisode trace, ¬ EpisodeEdge episode later)
    (quiet : Progress.Quiet (trace.state last))
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r) :
    EpisodeExcised trace episode observe := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  have bound := episode.interval.bounded
  have ordered := episode.interval.ordered
  have front := trace.source_segment 0 (episode.opened - 1) (by omega)
  simp only [Nat.zero_add] at front
  obtain ⟨middle, middleNotes, interior, compare, notes, projects⟩ :=
    replay_interior_from_opening trace episode maximal quiet observe recovery commutative respect
  obtain ⟨names, distinct, member, suffix, vestiges⟩ := project_suffix trace episode maximal quiet
  obtain ⟨after, recorded, moved, aligned, stamped, projected⟩ :=
    GuardedSuffix.transport_exec observe program respect suffix (compare.symm (fun _ _ same => same.symm)) notes.symm projects
  have full := (front.append interior).append moved
  rw [← original_roots_split trace episode] at full
  refine ⟨names, after, recorded, distinct, member, vestiges, ?_, aligned, stamped, projected, ?_, ?_,
    excision_shortens trace episode names⟩
  · simpa only [excisedEvents, List.range_eq_range'] using full
  · intro name key
    let gone := GuardedSuffix.stillPresent names ((List.range' (episode.closed + 1) (last - (episode.closed + 1))).map
      fun time => (time + 1, trace.event time))
    rw [← erase_vestige_tables (trace.state last) gone (fun child lives => (vestiges child lives).1) name key]
    have same := aligned name
    change OptionRel (StageSimulation.FiberRelated Eq) (Vestigial.eraseAll gone (trace.state last) name) (after name) at same
    cases left : Vestigial.eraseAll gone (trace.state last) name <;> cases right : after name <;>
      simp only [left, right, OptionRel] at same
    · simp [tableAt, left, right, OptionRel]
    · simpa only [tableAt, left, right, Option.bind_some] using same.table key

  · exact GuardedCutState.quiet_of_related aligned (erase_vestige_quiet _ _ (distinct.filter _)
      (fun name stored => (vestiges name stored).1) quiet)

/-- Some actual closing episode can be excised from a quiet guarded
history, while retaining its root commands and its table observation. -/
theorem lemma79_guarded (trace : Source) (closed : Nonempty (ClosedEpisode trace))
    (quiet : Progress.Quiet (trace.state last))
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r) :
    ∃ episode : ClosedEpisode trace, EpisodeExcised trace episode observe := by
  obtain ⟨episode, maximal⟩ := select_closing trace closed
  exact ⟨episode, excise_closed_episode trace episode maximal quiet observe recovery commutative respect⟩

end Cordis.Repairs.GuardedHistory
