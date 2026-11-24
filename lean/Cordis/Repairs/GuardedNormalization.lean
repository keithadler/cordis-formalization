import Cordis.Repairs.GuardedEpisodeExcision
import Cordis.Repairs.GuardedReindex
import Cordis.Repairs.GuardedOpenExchange
import Cordis.Repairs.GuardedActivationOrder

/-! Closed-episode elimination and root-command placement. Each shortening
or exchange produces a new guarded source trace. -/
namespace Cordis.Repairs.GuardedHistory
open Calculus Stages LegalHistory
open EpisodeAnnotations (NotesRelated)
open PaperEffectEquations (CoeffectOperations ValueOperationWitness)
open PartialCoeffectIndependenceContracts (tableSetoid)
open PaperObservationEquations (OperationRespects)
open TypedRegistry (encodeProgram RawRegistry Scalar)
open StageRecovery (TablesRelated)
open SupportAtQuiescence (TotalProvision)
open Iterators (OptionRel)
universe u
variable {Name Key Code : Type u} {V : Key → Type u} {ops : CoeffectOperations V}
variable [DecidableEq Name] [DecidableEq Key]
variable {program : Code → TypedRegistry.Instruction Name ops Code} {last : Nat}
local notation "A" => Scalar ops
local notation "R" => RawRegistry Name ops Code
local notation "Source" => Trace (encodeProgram program) last

/-- The structural difference permitted at the endpoint by repeated
episode excision. Each erased row must be removable when it is erased. -/
inductive VestigeErasures : R → R → Prop
  | refl (state : R) : VestigeErasures state state
  | remove {before after : R} (name : Name) : Removable before name → rootAt before name = false →
      VestigeErasures (erase before name) after → VestigeErasures before after

omit [DecidableEq Key] in
/-- Erasing vestiges does not add or replace any retained row. -/
theorem VestigeErasures.origin {before after : R} (erased : VestigeErasures before after)
    {name : Name} {row : TypedRegistry.RawFiber Name ops Code} (present : after name = some row) :
    before name = some row := by
  induction erased with
  | refl => exact present
  | @remove before after removed _ _ _ ih =>
    have found := ih present
    by_cases same : name = removed
    · simp [erase, same] at found
    · simpa [erase, same] using found

omit [DecidableEq Key] in
/-- Vestige erasure keeps every active row literally. -/
theorem VestigeErasures.active_row {before after : R}
    (erased : VestigeErasures before after) {name : Name} {row : TypedRegistry.RawFiber Name ops Code}
    (present : before name = some row) (active : row.phase.available) : after name = some row := by
  induction erased with
  | refl => exact present
  | @remove before after removed removable _ rest ih =>
    apply ih
    have different : name ≠ removed := by
      intro same
      subst removed
      rw [Removable, present] at removable
      simp [removable.2.1, Phase.available] at active
    simpa [erase, different] using present

/-- Erasure of removable rows preserves each table coordinate, including
the distinction between a bound key and an absent key. -/
theorem VestigeErasures.table_at {before after : R} (erased : VestigeErasures before after)
    (owner : Name) (key : Key) : StageRecovery.tableAt after owner key = StageRecovery.tableAt before owner key := by
  induction erased with
  | refl => rfl
  | remove name ready _ _ ih =>
    exact ih.trans (Transposition.removable_erase_tables _ name ready owner key)

private theorem erase_vestiges (state : R) (names : List Name) (distinct : names.Nodup)
    (ready : ∀ name ∈ names, Removable state name ∧ rootAt state name = false) :
    VestigeErasures state (Vestigial.eraseAll names state) := by
  induction names generalizing state with
  | nil => exact .refl state
  | cons first rest ih =>
    obtain ⟨unique, remaining⟩ := List.nodup_cons.mp distinct
    obtain ⟨removable, child⟩ := ready first List.mem_cons_self
    apply VestigeErasures.remove first removable child
    apply ih (erase state first) remaining
    intro name member
    have different : name ≠ first := fun same => unique (same ▸ member)
    obtain ⟨canErase, root⟩ := ready name (List.mem_cons_of_mem _ member)
    refine ⟨Vestigial.erase_removable different canErase, ?_⟩
    unfold rootAt
    rw [Transposition.erase_other _ _ _ different]
    exact root

omit [DecidableEq Key] in
theorem VestigeErasures.append {before middle after : R}
    (front : VestigeErasures before middle) (suffix : VestigeErasures middle after) : VestigeErasures before after := by
  induction front with
  | refl => exact suffix
  | remove name removable child _ ih => exact .remove name removable child (ih suffix)

/-- A permitted erasure and a sequence of erasures can continue to a
common registry. Different removable rows stay removable after erasure. -/
private theorem VestigeErasures.join_remove {before after : R}
    (path : VestigeErasures before after) {name : Name}
    (ready : Removable before name) (child : rootAt before name = false) :
    ∃ joined, VestigeErasures (erase before name) joined ∧ VestigeErasures after joined := by
  induction path with
  | refl before => exact ⟨erase before name, .refl _, .remove name ready child (.refl _)⟩
  | @remove before after other otherReady otherChild rest ih =>
    by_cases same : name = other
    · subst other
      exact ⟨after, rest, .refl _⟩
    · have afterRoot {first second : Name} (different : first ≠ second) :
          rootAt (erase before second) first = rootAt before first := by
        unfold rootAt
        rw [Transposition.erase_other _ _ _ different]
      obtain ⟨joined, left, right⟩ :=
        ih (Vestigial.erase_removable same ready) ((afterRoot same).trans child)
      have swapped : erase (erase before name) other = erase (erase before other) name := by
        funext query
        by_cases first : query = name <;> by_cases second : query = other <;>
          simp [erase, first, second]
      exact ⟨joined, .remove other (Vestigial.erase_removable (Ne.symm same) otherReady)
        ((afterRoot (Ne.symm same)).trans otherChild) (swapped.symm ▸ left), right⟩

/-- Any two legal vestige erasures from the same registry can be joined
by legal erasures, with literal equality of the resulting registries. -/
theorem VestigeErasures.join {before left right : R}
    (first : VestigeErasures before left) (second : VestigeErasures before right) :
    ∃ joined, VestigeErasures left joined ∧ VestigeErasures right joined := by
  induction first generalizing right with
  | refl => exact ⟨right, second, .refl _⟩
  | remove name ready child rest ih =>
    obtain ⟨middle, earlier, later⟩ := second.join_remove ready child
    obtain ⟨joined, leftPath, middlePath⟩ := ih earlier
    exact ⟨joined, leftPath, later.append middlePath⟩

/-- A registry is fully pruned when no further vestige can be erased. -/
def VestigeNormal (state : R) : Prop :=
  ∀ name, Removable state name → rootAt state name ≠ false

omit [DecidableEq Key] in
theorem VestigeErasures.eq_of_normal {before after : R}
    (path : VestigeErasures before after) (normal : VestigeNormal before) : before = after := by
  cases path with
  | refl => rfl
  | remove name ready child _ => exact False.elim (normal name ready child)

/-- Every finite registry has a unique fully pruned result. -/
theorem exists_unique_vestige_normal (state : R) (finite : SupportUniqueness.FiniteDomain state) :
    ∃ result, VestigeErasures state result ∧ VestigeNormal result ∧
      ∀ other, VestigeErasures state other → VestigeNormal other → result = other := by
  have terminates (size : Nat) (registry : R) (names : List Name) (length : names.length = size)
      (cover : ∀ name row, registry name = some row → name ∈ names) :
      ∃ result, VestigeErasures registry result ∧ VestigeNormal result := by
    induction size using Nat.strongRecOn generalizing registry names with
    | ind size ih =>
      by_cases normal : VestigeNormal registry
      · exact ⟨registry, .refl _, normal⟩
      · have removable : ∃ name, Removable registry name ∧ rootAt registry name = false := by
          by_cases found : ∃ name, Removable registry name ∧ rootAt registry name = false
          · exact found
          · exact False.elim (normal (fun name ready child => found ⟨name, ready, child⟩))
        obtain ⟨name, ready, child⟩ := removable
        have listed : name ∈ names := by
          cases found : registry name with
          | none => exact False.elim (Transposition.removable_present registry name ready found)
          | some row => exact cover name row found
        let remaining := names.filter (· != name)
        have decreases : remaining.length < size := by
          rw [← length]
          exact List.length_filter_lt_length_iff_exists.mpr ⟨name, listed, by simp⟩
        have covers (other : Name) (row : TypedRegistry.RawFiber Name ops Code)
            (present : erase registry name other = some row) : other ∈ remaining := by
          by_cases same : other = name
          · simp [erase, same] at present
          · rw [Transposition.erase_other _ _ _ same] at present
            exact List.mem_filter.mpr ⟨cover other row present, by simp [same]⟩
        obtain ⟨result, erased, done⟩ := ih remaining.length decreases (erase registry name) remaining rfl covers
        exact ⟨result, .remove name ready child erased, done⟩
  obtain ⟨names, cover⟩ := finite
  obtain ⟨result, erased, normal⟩ := terminates names.length state names rfl cover
  refine ⟨result, erased, normal, fun other otherErased otherNormal => ?_⟩
  obtain ⟨joined, first, second⟩ := erased.join otherErased
  exact (first.eq_of_normal normal).trans (second.eq_of_normal otherNormal).symm

private theorem VestigeErasures.transport [Setoid A] {source final before : R}
    (erased : VestigeErasures source final) (related : StageSimulation.Related Eq before source) :
    ∃ after, VestigeErasures before after ∧ StageSimulation.Related Eq after final := by
  induction erased generalizing before with
  | refl => exact ⟨before, .refl before, related⟩
  | @remove source final name canErase child _ ih =>
    have guard := (GuardObservations.removable_iff related.observed name).mpr canErase
    have parent : rootAt before name = false := by
      have compared := related.observed name
      cases first : before name <;> cases second : source name <;> simp_all [rootAt, OptionRel]
      rwa [compared.parent]
    obtain ⟨after, remaining, endpoint⟩ := ih (StageSimulation.erase_related related name)
    exact ⟨after, .remove name guard parent remaining, endpoint⟩

private theorem total_after_erasure (observe : ∀ key, Setoid (V key)) {before after : R} (names : List Name)
    (aligned : @StageSimulation.Related Name Key A Code PUnit.{u + 1} (TypedCoeffectReplay.setoid observe) Eq
      (Vestigial.eraseAll names before) after) (total : TotalProvision before) : TotalProvision after := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  intro name row found ready key
  obtain ⟨old, oldAt, fields⟩ := StageSimulation.present_related (aligned.symm (fun _ _ same => same.symm)) name row found
  rw [Vestigial.eraseAll_apply] at oldAt
  split at oldAt
  · cases oldAt
  · have wasReady := (GuardObservations.phase_available_iff fields.phase.observed.1).mp ready
    have original := total name old oldAt wasReady key
    have shape := fields.table key
    have same : row.table key = none ↔ old.table key = none := by
      cases left : row.table key <;> cases right : old.table key <;> simp_all [OptionRel]
    exact (not_congr same).trans (original.trans (by rw [fields.component.provides]))

/-- Deleted histories really are legal source traces after compaction. The
embedding recovers the original event stamps and the recorded final notes. -/
theorem reindex_excision (trace : Source) (episode : ClosedEpisode trace)
    (observe : ∀ key, Setoid (V key)) (excised : EpisodeExcised trace episode observe) :
    letI : Setoid A := TypedCoeffectReplay.setoid observe
    let suffix := (List.range' (episode.closed + 1) (last - (episode.closed + 1))).map
      fun time => (time + 1, trace.event time)
    ∃ (names : List Name) (compact : Trace (encodeProgram program) (excisedEvents trace episode names).length)
      (expand : Nat → Nat),
      RetainedEvents trace compact expand ∧
      (∀ index (bound : index < (excisedEvents trace episode names).length),
        compact.event index = (excisedEvents trace episode names)[index].2 ∧
        expand (index + 1) = (excisedEvents trace episode names)[index].1) ∧
      originalRoots compact = originalRoots trace ∧
      VestigeErasures (trace.state last) (Vestigial.eraseAll (GuardedSuffix.stillPresent names suffix) (trace.state last)) ∧
      StageSimulation.Related Eq (Vestigial.eraseAll (GuardedSuffix.stillPresent names suffix) (trace.state last))
        (compact.state (excisedEvents trace episode names).length) ∧
      NotesRelated (GuardedSuffix.eraseAllNotes (GuardedSuffix.stillPresent names suffix) (trace.notes last))
        (reindexNotes expand (compact.notes (excisedEvents trace episode names).length)) ∧
      TablesRelated (trace.state last) (compact.state (excisedEvents trace episode names).length) ∧
      Progress.Quiet (compact.state (excisedEvents trace episode names).length) ∧
      (TotalProvision (trace.state last) → TotalProvision (compact.state (excisedEvents trace episode names).length)) := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  obtain ⟨names, after, notes, unique, _, ready, run, related, annotations, _, tables, quiet, _⟩ := excised
  rw [trace.start, trace.seed] at run
  let retained := excisedEvents trace episode names
  have sub : (retained.map Prod.fst).Sublist ((List.range last).map (· + 1)) := by
    simpa only [List.map_map, Function.comp_def] using (excised_sublist trace episode names).map Prod.fst
  have distinct : ((List.range last).map (· + 1)).Nodup :=
    List.nodup_range.map (· + 1) (fun _ _ different equal => different (Nat.add_right_cancel equal))
  have limits (stamp : Nat) (member : stamp ∈ retained.map Prod.fst) : 0 < stamp ∧ stamp ≤ last := by
    obtain ⟨index, within, rfl⟩ := List.mem_map.mp (sub.subset member)
    exact ⟨Nat.zero_lt_succ _, List.mem_range.mp within⟩
  obtain ⟨compact, expand, injective, finish, mapped, stamps, rootOrder⟩ :=
    trace_with_sources run (sub.nodup distinct) (fun member => Nat.lt_irrefl _ (limits 0 member).1) last
      (fun stamp member => (limits stamp member).2) (trace.event 0)
  have sourceCut (i : Nat) (bounded : i < retained.length) :
      ∃ time, time < last ∧ expand (i + 1) = time + 1 ∧ compact.event i = trace.event time := by
    obtain ⟨time, inside, found⟩ := List.mem_map.mp
      ((excised_sublist trace episode names).subset (List.getElem_mem bounded))
    have ⟨label, stamp, _⟩ := stamps i bounded
    exact ⟨time, List.mem_range.mp inside, stamp.trans (congrArg Prod.fst found).symm,
      label.trans (congrArg Prod.snd found).symm⟩
  have retains : RetainedEvents trace compact expand := by
    refine ⟨injective, ?_, ?_, ?_⟩
    · intro i bounded
      obtain ⟨time, inside, stamp, _⟩ := sourceCut i bounded
      rw [stamp]
      exact ⟨Nat.zero_lt_succ _, inside⟩
    · intro i bounded
      obtain ⟨time, _, stamp, label⟩ := sourceCut i bounded
      simpa only [stamp, Nat.add_sub_cancel] using label
    · intro i bounded
      obtain ⟨time, _, oldStamp, _⟩ := sourceCut i bounded
      obtain ⟨_, stamp, checked⟩ := stamps i bounded
      rw [GuardedSuffix.CheckedSource, ← stamp, oldStamp, trace.sourceAt_succ] at checked
      simpa only [oldStamp, Nat.add_sub_cancel] using checked
  refine ⟨names, compact, expand, retains, fun i bounded => ⟨(stamps i bounded).1, (stamps i bounded).2.1⟩, rootOrder,
    erase_vestiges _ _ (unique.filter _) ready, ?_, ?_, ?_, ?_, ?_⟩
  · rwa [finish]
  · rwa [mapped]
  · rwa [finish]
  · rwa [finish]
  · intro total
    rw [finish]
    exact total_after_erasure observe _ related total

/-- The selected guarded excision can be repeated until no closed episode
remains. No exchange or insertion order is needed for this phase. -/
theorem eliminate_closed_episodes_with_length (trace : Source)
    (quiet : Progress.Quiet (trace.state last))
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r) :
    letI : Setoid A := TypedCoeffectReplay.setoid observe
    ∃ (length : Nat) (result : Trace (encodeProgram program) length) (expand : Nat → Nat),
      length ≤ last ∧ (Nonempty (ClosedEpisode trace) → length < last) ∧ (¬ Nonempty (ClosedEpisode result)) ∧
      RetainedEvents trace result expand ∧
      originalRoots result = originalRoots trace ∧
      TablesRelated (trace.state last) (result.state length) ∧ Progress.Quiet (result.state length) ∧
      (TotalProvision (trace.state last) → TotalProvision (result.state length)) ∧
      ∃ projected, VestigeErasures (trace.state last) projected ∧
        StageSimulation.Related Eq projected (result.state length) := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  induction last using Nat.strongRecOn with
  | ind last ih =>
    by_cases closed : Nonempty (ClosedEpisode trace)
    · obtain ⟨episode, excised⟩ := lemma79_guarded trace closed quiet observe recovery commutative respect
      obtain ⟨names, compact, expand, retained, _, roots, erased, related, _, tables, nextQuiet, nextTotal⟩ :=
        reindex_excision trace episode observe excised
      have smaller := excision_shortens trace episode names
      obtain ⟨length, result, embed, order, _, openOnly, resultRetained, resultRoots, resultTables, finalQuiet, finalTotal,
        projected, more, endpoint⟩ :=
        ih _ smaller compact nextQuiet
      obtain ⟨after, preserved, projectedAlignment⟩ := more.transport related
      have aligned := StageSimulation.Related.trans (Q := Eq) (fun first second => first.trans second)
        projectedAlignment endpoint
      exact ⟨length, result, expand ∘ embed, Nat.le_trans order (Nat.le_of_lt smaller), fun _ => Nat.lt_of_le_of_lt order smaller, openOnly,
        retained.trans resultRetained, resultRoots.trans roots,
        StageRecovery.tables_trans tables resultTables, finalQuiet, finalTotal ∘ nextTotal,
        after, erased.append preserved, aligned⟩
    · have self := trace.self_related last (Nat.le_refl _)
        (TypedRegistry.encoded_program_callbacks ops observe program recovery commutative)
      exact ⟨last, trace, id, Nat.le_refl _, fun existsClosed => False.elim (closed existsClosed), closed, .refl trace, rfl, StageRecovery.tables_refl _, quiet, id, _, .refl _, self⟩

theorem eliminate_closed_episodes (trace : Source)
    (quiet : Progress.Quiet (trace.state last))
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r) :
    letI : Setoid A := TypedCoeffectReplay.setoid observe
    ∃ (length : Nat) (result : Trace (encodeProgram program) length) (expand : Nat → Nat),
      length ≤ last ∧ (¬ Nonempty (ClosedEpisode result)) ∧
      RetainedEvents trace result expand ∧
      originalRoots result = originalRoots trace ∧
      TablesRelated (trace.state last) (result.state length) ∧ Progress.Quiet (result.state length) ∧
      (TotalProvision (trace.state last) → TotalProvision (result.state length)) ∧
      ∃ projected, VestigeErasures (trace.state last) projected ∧
        StageSimulation.Related Eq projected (result.state length) := by
  obtain ⟨length, result, expand, bounded, _, opened, retained, roots, tables, settled, total, erasures⟩ :=
    eliminate_closed_episodes_with_length trace quiet observe recovery commutative respect
  exact ⟨length, result, expand, bounded, opened, retained, roots, tables, settled, total, erasures⟩

/-- From an arbitrary quiet guarded history, eliminate closed episodes and
move the roots earlier up to the actual root/child command barriers. The
endpoint comparison is the one justified by the episode erasures. -/
theorem eliminate_closed_episodes_and_place_roots (trace : Source)
    (quiet : Progress.Quiet (trace.state last))
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r) :
    letI : Setoid A := TypedCoeffectReplay.setoid observe
    ∃ (length : Nat) (result : Trace (encodeProgram program) length),
      length ≤ last ∧ (¬ Nonempty (ClosedEpisode result)) ∧ RootsAtBarriers result ∧
      originalRoots result = originalRoots trace ∧
      TablesRelated (trace.state last) (result.state length) ∧ Progress.Quiet (result.state length) ∧
      (TotalProvision (trace.state last) → TotalProvision (result.state length)) ∧
      ∃ projected, VestigeErasures (trace.state last) projected ∧
        StageSimulation.Related Eq projected (result.state length) := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  obtain ⟨length, openHistory, _, bounded, openOnly, _, roots, tables, openQuiet, total, projected, erased, relation⟩ :=
    eliminate_closed_episodes trace quiet observe recovery commutative respect
  obtain ⟨result, placed, resultRoots, _, endpoint, resultOpen, resultQuiet⟩ :=
    openHistory.push_roots_to_barriers openOnly openQuiet
  exact ⟨length, result, bounded, resultOpen, placed, resultRoots.trans roots, endpoint ▸ tables,
    resultQuiet, endpoint ▸ total, projected, erased, endpoint ▸ relation⟩

/-- The three normalization phases together. Between command cuts,
the surviving activations group by actor in support order. -/
theorem normalize_activation_runs (trace : Source)
    (quiet : Progress.Quiet (trace.state last))
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r) :
    letI : Setoid A := TypedCoeffectReplay.setoid observe
    ∃ (length : Nat) (placed result : Trace (encodeProgram program) length) (rank : Name → Nat),
      length ≤ last ∧ RootsAtBarriers placed ∧
      (∀ cut, cut < length → ∀ command : OrchestrationSorting.Command Name Key Code,
        result.event cut = .command command ↔ placed.event cut = .command command) ∧
      (¬ Nonempty (ClosedEpisode result)) ∧ OrderedActivationRuns result rank ∧ ChronologicalOpenings result rank ∧
      originalRoots result = originalRoots trace ∧
      TablesRelated (trace.state last) (result.state length) ∧ Progress.Quiet (result.state length) ∧
      (TotalProvision (trace.state last) → TotalProvision (result.state length)) ∧
      (TotalProvision (trace.state last) →
        ∀ {a b}, SupportUniqueness.ActivePredecessor (result.state length) a b → rank a < rank b) ∧
      ∃ projected, VestigeErasures (trace.state last) projected ∧
        StageSimulation.Related Eq projected (result.state length) := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  obtain ⟨length, placed, bounded, openOnly, barriers, roots, tables, placedQuiet, placedTotal,
      projected, erased, aligned⟩ :=
    eliminate_closed_episodes_and_place_roots trace quiet observe recovery commutative respect
  obtain ⟨result, sorted, chronological, commands, preservedRoots, relation, finalOpen, finalQuiet⟩ :=
    placed.order_activation_runs openOnly placedQuiet observe recovery commutative respect
  have fixedRank : ChronologicalOpenings result (openingRanks placed length) := chronological
  have total := fun initial => related_total_provision relation (placedTotal initial)
  have preservedTables : TablesRelated (placed.state length) (result.state length) := by
    intro owner key
    have row := relation owner
    cases left : placed.state length owner <;> cases right : result.state length owner <;>
      simp only [left, right, OptionRel] at row
    · simp [StageRecovery.tableAt, left, right, OptionRel]
    · simpa only [StageRecovery.tableAt, left, right, Option.bind_some] using row.table key
  exact ⟨length, placed, result, openingRanks placed length, bounded, barriers, commands,
    finalOpen, sorted, chronological, preservedRoots.trans roots, StageRecovery.tables_trans tables preservedTables,
    finalQuiet, total, fun provisions => fixedRank.support finalOpen finalQuiet (total provisions), projected, erased,
    StageSimulation.Related.trans (Q := Eq) (fun a b => a.trans b) aligned relation⟩

end Cordis.Repairs.GuardedHistory
