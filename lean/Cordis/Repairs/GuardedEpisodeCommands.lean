import Cordis.Repairs.GuardedEpisodeReplay

/-! Preserve the external commands of the guarded episode, using the live
birth at the source cut and the native guards at the projected cut. -/
namespace Cordis.Repairs.GuardedHistory
open Calculus Stages Incarnation IncarnationReplay LegalHistory OrchestrationSorting
open PartialReplayRegistry (saved)
open EpisodeBoundary (born_row)
open Iterators (OptionRel)
open Vestigial (CutNotes noteStep)
universe u
variable {Name Key Value Code Error : Type u} [DecidableEq Name] [DecidableEq Key]
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "C" => Capture Name Key Value
local notation "I" => Inverse Name Key Value
local notation "Program" => Code → Instruction Name Key Value Code Error
variable {program : Code → Instruction Name Key Value Code Error} {last : Nat}

theorem vacant_not_withdrawn (trace : Trace program last) (episode : ClosedEpisode trace)
    {time : Nat} (bounded : time ≤ last) {name : Name} (vacant : trace.state time name = none) :
    ¬ withdraws trace episode time name = true := by
  intro omitted
  obtain ⟨capture, _, matched⟩ := List.any_eq_true.mp omitted
  cases token : capture.token with
  | retire target =>
    have ⟨same, live⟩ : name = target ∧ (trace.notes time).1 target = some capture.index := by
      simpa [Capture.retires, token] using matched
    subst target
    rw [(trace.births_agree time bounded name).mpr vacant] at live
    cases live
  | _ => simp [Capture.retires, token] at matched

theorem vacant_ne_closing (trace : Trace program last) (episode : ClosedEpisode trace)
    {time : Nat} (lower : episode.opened ≤ time) (upper : time ≤ episode.closed)
    {name : Name} (vacant : trace.state time name = none) : name ≠ episode.name := by
  intro same
  subst name
  exact episode.interval.installed time lower upper (by simp [ControlFrame.viewAt, vacant])

theorem probe_rootAt (trace : Trace program last) (episode : ClosedEpisode trace)
    (maximal : ∀ later : ClosedEpisode trace, ¬ EpisodeEdge episode later)
    (quiet : Progress.Quiet (trace.state last))
    {time : Nat} (lower : episode.opened ≤ time) (upper : time ≤ episode.closed) (name : Name) :
    rootAt (trace.state time) name = rootAt (probeAt trace episode time) name := by
  have projected := probe_projects trace episode maximal quiet lower upper
  by_cases omitted : withdraws trace episode time name = true
  · obtain ⟨step, _, earlier, creator, birthRule, lives⟩ := withdrawn_birth trace episode lower upper omitted
    have bounded := episode.interval.bounded
    have vacant : trace.state step name = none := by simpa using lives.boundary.resolve_left (by omega)
    have born := lives.present (step + 1) (Nat.le_refl _) lives.ordered
    have creation := (trace.actual_child_birth (by omega) birthRule vacant born).1
    rw [creator] at creation
    obtain ⟨component, start⟩ := born_row vacant creation
    cases present : trace.state time name with
    | none => simp [rootAt, present, projected.absent name omitted]
    | some row =>
      have parent := (lives.metadata_of_stable (last := last) (fun t bound => transition_stable (trace.step t bound).1)
        (by omega) start present).2.symm
      simp [rootAt, present, projected.absent name omitted, parent, fresh]
  · have paired := projected.kept name omitted
    cases source : trace.state time name <;> cases target : probeAt trace episode time name <;>
      simp_all [rootAt, OptionRel]
    rw [paired.parent]

/-- A birth with the current source stamp cannot match an earlier capture
of the closing actor. Both the mask and its effect on the input are stable. -/
theorem rollbackOf_next_birth (trace : Trace program last) (episode : ClosedEpisode trace)
    {time : Nat} (bounded : time < last) {name : Name}
    (different : trace.actor time ≠ episode.name)
    (vacant : trace.state time name = none) (born : trace.state (time + 1) name ≠ none)
    (outside : ∀ other, other ≠ name → (trace.state (time + 1) other = none ↔ trace.state time other = none)) :
    withdraws trace episode (time + 1) = withdraws trace episode time ∧
      ∀ state, rollbackOf trace episode (time + 1) state = rollbackOf trace episode time state := by
  let word := (trace.notes time).2 episode.name
  have words : (trace.notes (time + 1)).2 episode.name = word :=
    trace.foreign_word_unchanged bounded (Ne.symm different)
  have agrees (capture : C) (member : capture ∈ word) (target : Name) :
      ((trace.notes (time + 1)).1 target = some capture.index ↔
        (trace.notes time).1 target = some capture.index) := by
    by_cases selected : target = name
    · subst target
      have age := (trace.capture_origin time (Nat.le_of_lt bounded) episode.name capture member).1
      have earlier : time + 1 ≠ capture.index := by omega
      rw [trace.notes_eq time (by omega), trace.notes_eq (time + 1) (by omega)]
      simp [Vestigial.cutNotes, birthAt_of_created vacant born, birthAt_none.mpr vacant, earlier]
    · rw [trace.live_unchanged_at bounded target (outside target selected)]
  have mask : withdraws trace episode (time + 1) = withdraws trace episode time := by
    funext query
    have tested (capture : C) (member : capture ∈ word) :
        Capture.retires (trace.notes (time + 1)).1 query capture =
          Capture.retires (trace.notes time).1 query capture := by
      cases token : capture.token with
      | retire target => simp only [Capture.retires, token, agrees capture member target]
      | _ => simp [Capture.retires, token]
    apply Bool.eq_iff_iff.mpr
    simp only [withdraws, words, List.any_eq_true]
    constructor
    · rintro ⟨capture, member, triggered⟩
      exact ⟨capture, member, (tested capture member).symm.trans triggered⟩
    · rintro ⟨capture, member, triggered⟩
      exact ⟨capture, member, (tested capture member).trans triggered⟩
  refine ⟨mask, fun state => ?_⟩
  have replayed : replay (trace.notes (time + 1)).1 word state = replay (trace.notes time).1 word state :=
    replay_congr_matches word state (fun capture member target _ => agrees capture member target)
  unfold rollbackOf
  rw [words, replayed, mask]

theorem rollbackOf_put_fresh (trace : Trace program last) (episode : ClosedEpisode trace) (time : Nat)
    (bounded : time ≤ last) {name : Name} (component : Component Key Code) (parent : Option Name)
    (vacant : trace.state time name = none) (different : name ≠ episode.name) :
    rollbackOf trace episode time (put (trace.state time) name (fresh component parent)) =
      put (probeAt trace episode time) name (fresh component parent) := by
  have unmasked := vacant_not_withdrawn trace episode bounded vacant
  let live := (trace.notes time).1
  let word := (trace.notes time).2 episode.name
  let reverted := replay live word (trace.state time)
  funext query
  change (if withdraws trace episode time query then none else
    mark (replay live word (put (trace.state time) name (fresh component parent))) episode.name .inactive query) = _
  rw [replay_put_fresh live word _ _ component parent ((trace.births_agree time bounded name).mpr vacant),
    Transposition.mark_put reverted episode.name name (fresh component parent) .inactive (Ne.symm different)]
  by_cases selected : query = name
  · subst query
    simp [unmasked]
  · simp [put, selected, probeAt, rollbackOf, reverted, live, word]

private theorem probe_after_retire (trace : Trace program last) (episode : ClosedEpisode trace)
    {time : Nat} (bounded : time < last)
    (ended : trace.state (time + 1) = Calculus.retire (trace.state time) (trace.actor time)) :
    probeAt trace episode (time + 1) = Calculus.retire (probeAt trace episode time) (trace.actor time) ∧
      probeNotes trace episode (time + 1) = probeNotes trace episode time ∧
      withdraws trace episode (time + 1) = withdraws trace episode time := by
  let actor := trace.actor time
  let source := trace.state time
  have stable : saved (trace.state (time + 1)) = saved source := by
    rw [ended]
    funext name
    by_cases selected : name = actor
    · subst name
      cases found : source actor <;> simp [saved, Calculus.retire, Calculus.modify, source, actor, found]
    · unfold saved
      rw [Transposition.retire_other _ _ _ selected]
  have words : (trace.notes (time + 1)).2 = (trace.notes time).2 := by
    rw [(trace.step time bounded).2]
    exact advance_control actor (time + 1) _ (trace.projects time (by omega)) stable
  have births := trace.live_unchanged bounded fun name => by rw [ended, Transposition.retire_presence]
  have mask := mask_unchanged trace episode births (congrFun words episode.name)
  refine ⟨?_, ?_, mask⟩
  · unfold probeAt rollbackOf
    rw [mask, births, words, ended, EpisodeRollback.replay_retire]
    dsimp only
    rw [Transposition.mark_retire]
    funext name
    by_cases selected : name = actor
    · subst name
      by_cases omitted : withdraws trace episode time actor = true <;>
        simp [Calculus.retire, Calculus.modify, omitted, actor]
    · simp [Calculus.retire, Calculus.modify, selected, actor]
  · unfold probeNotes
    rw [mask, births, words]

private theorem probe_after_remove (trace : Trace program last) (episode : ClosedEpisode trace) {time : Nat}
    (bound : time < last) (different : trace.actor time ≠ episode.name)
    (ended : trace.state (time + 1) = erase (trace.state time) (trace.actor time)) :
    probeAt trace episode (time + 1) = erase (probeAt trace episode time) (trace.actor time) ∧
      ∀ name, name ≠ trace.actor time → withdraws trace episode (time + 1) name = withdraws trace episode time name := by
  let actor := trace.actor time
  let word := (trace.notes time).2 episode.name
  have words : (trace.notes (time + 1)).2 episode.name = word :=
    trace.foreign_word_unchanged bound (Ne.symm different)
  have births (name : Name) (other : name ≠ actor) :
      (trace.notes (time + 1)).1 name = (trace.notes time).1 name :=
    trace.live_unchanged_at bound name (by simp [ended, erase, actor, other])
  have mask (name : Name) (distinct : name ≠ actor) :
      withdraws trace episode (time + 1) name = withdraws trace episode time name := by
    unfold withdraws
    apply List.any_congr words
    intro capture
    cases token : capture.token with
    | retire child =>
      by_cases selected : name = child
      · subst child
        simp only [Capture.retires, token, births name distinct]
      · simp [Capture.retires, token, selected]
    | _ => simp [Capture.retires, token]
  refine ⟨?_, mask⟩
  have replayed := Vestigial.replay_erase (trace.state time) actor births word
  unfold probeAt rollbackOf
  rw [words, ended, replayed]
  dsimp only
  unfold mark
  rw [Vestigial.modify_erase]
  funext name
  by_cases selected : name = actor
  · subst name
    simp [erase, actor]
  · simp [erase, mask name selected, selected, actor, word]

/-- Commands retain their payload and root provenance at the actual guarded
probe. Retirement of the selected actor is still an external command. -/
theorem replay_command_between_probes (trace : Trace program last) (episode : ClosedEpisode trace)
    (maximal : ∀ later : ClosedEpisode trace, ¬ EpisodeEdge episode later)
    (quiet : Progress.Quiet (trace.state last))
    {time : Nat} (lower : episode.opened ≤ time) (upper : time < episode.closed)
    (command : Command Name Key Code) (event : trace.event time = .command command)
    (kept : ¬ withdraws trace episode time command.actor = true) :
    GuardedSuffix.Step program (trace.event time) (time + 1) (probeAt trace episode time) (probeNotes trace episode time)
        (probeAt trace episode (time + 1)) (probeNotes trace episode (time + 1)) ∧
      eventRoots (trace.state time) (trace.event time) = eventRoots (probeAt trace episode time) (trace.event time) := by
  have bound : time < last := Nat.lt_trans upper episode.interval.bounded
  have actor : command.actor = trace.actor time := by simp [Trace.actor, event, Vestigial.eventActor]
  have actual := (trace.step time bound).1
  rw [event] at actual
  change command.Step _ _ at actual
  have removeForeign (name : Name) (selected : command = .remove name) : name ≠ episode.name := by
    subst command
    have ready : Removable (trace.state time) name := actual.1
    intro same
    subst name
    apply episode.interval.installed time lower (Nat.le_of_lt upper)
    cases found : trace.state time episode.name with
    | none => simp [ControlFrame.viewAt, found]
    | some row =>
      rw [Removable, found] at ready
      simp [ControlFrame.viewAt, found, ready.2.1, Phase.committed]
  have permitted := (probe_projects trace episode maximal quiet lower (Nat.le_of_lt upper)).command
    command kept removeForeign actual
  have unmasked : ¬ withdraws trace episode time (trace.actor time) = true := actor ▸ kept
  have simultaneous (endpoint : probeAt trace episode (time + 1) = command.apply (probeAt trace episode time))
      (noRevival : ∀ name, probeAt trace episode (time + 1) name ≠ none →
        ¬ withdraws trace episode time name = true)
      (afterSaved : trace.actor time ≠ episode.name →
        saved (probeAt trace episode (time + 1)) (trace.actor time) = saved (trace.state (time + 1)) (trace.actor time)) :
      GuardedSuffix.Step program (trace.event time) (time + 1) (probeAt trace episode time) (probeNotes trace episode time)
        (probeAt trace episode (time + 1)) (probeNotes trace episode (time + 1)) := by
    refine ⟨?_, probe_notes_of_step trace episode bound noRevival
      (fun different => probe_keeps_saved trace episode different unmasked) afterSaved⟩
    rw [event]
    exact ⟨permitted.1, endpoint⟩
  have fixedMask (endpoint : probeAt trace episode (time + 1) = command.apply (probeAt trace episode time))
      (mask : withdraws trace episode (time + 1) = withdraws trace episode time) :=
    simultaneous endpoint (fun name present omitted => present (if_pos ((congrFun mask name).trans omitted)))
      (fun different => probe_keeps_saved trace episode different (by rwa [mask]))
  refine ⟨?_, eventRoots_agree _ (probe_rootAt trace episode maximal quiet lower (Nat.le_of_lt upper))⟩
  cases command with
  | insert name component =>
    have ready : Insertable (trace.state time) name component none := actual.1
    have different := vacant_ne_closing trace episode lower (Nat.le_of_lt upper) ready.1
    have ended : trace.state (time + 1) = put (trace.state time) name (fresh component none) := actual.2
    have born : trace.state (time + 1) name ≠ none := by simp [ended]
    have outside (other : Name) (distinct : other ≠ name) :
        trace.state (time + 1) other = none ↔ trace.state time other = none := by
      rw [ended, Transposition.put_other _ _ _ _ distinct]
    obtain ⟨mask, same⟩ := rollbackOf_next_birth trace episode bound (actor ▸ different) ready.1 born outside
    apply fixedMask _ mask
    change rollbackOf trace episode (time + 1) (trace.state (time + 1)) = _
    rw [same, ended]
    exact rollbackOf_put_fresh trace episode time (Nat.le_of_lt bound) component none ready.1 different
  | retire name =>
    have sameName : name = trace.actor time := actor
    have ended : trace.state (time + 1) = Calculus.retire (trace.state time) (trace.actor time) := by
      simpa only [Command.apply, sameName] using actual.2
    obtain ⟨registry, _, mask⟩ := probe_after_retire trace episode bound ended
    exact fixedMask (by simpa only [Command.apply, sameName] using registry) mask
  | remove name =>
    have sameName : name = trace.actor time := actor
    have ended : trace.state (time + 1) = erase (trace.state time) (trace.actor time) := by
      simpa only [Command.apply, sameName] using actual.2
    obtain ⟨registry, mask⟩ := probe_after_remove trace episode bound (sameName ▸ removeForeign name rfl) ended
    refine simultaneous (by simpa only [Command.apply, sameName] using registry) ?_ ?_
    · intro query present omitted
      have distinct : query ≠ trace.actor time := by
        intro same
        subst query
        exact present (by simp [registry, erase])
      exact present (if_pos ((mask query distinct).trans omitted))
    · intro _
      simp [saved, registry, ended, erase]

/-- A withdrawn child command stutters and contributes no root command.
A later insertion at the same name uses its own source stamp. -/
theorem probe_omits_withdrawn_command (trace : Trace program last) (episode : ClosedEpisode trace)
    (maximal : ∀ later : ClosedEpisode trace, ¬ EpisodeEdge episode later)
    (quiet : Progress.Quiet (trace.state last))
    {time : Nat} (lower : episode.opened ≤ time) (upper : time < episode.closed)
    (command : Command Name Key Code) (event : trace.event time = .command command)
    (withdrawn : withdraws trace episode time command.actor = true) :
    probeAt trace episode (time + 1) = probeAt trace episode time ∧
      probeNotes trace episode (time + 1) = probeNotes trace episode time ∧
      eventRoots (trace.state time) (trace.event time) = [] := by
  have bound : time < last := Nat.lt_trans upper episode.interval.bounded
  have actor : command.actor = trace.actor time := by simp [Trace.actor, event, Vestigial.eventActor]
  have absent : probeAt trace episode time command.actor = none := if_pos withdrawn
  have child : rootAt (trace.state time) command.actor = false := by
    rw [probe_rootAt trace episode maximal quiet lower (Nat.le_of_lt upper), rootAt, absent]
    rfl
  have different : trace.actor time ≠ episode.name := by
    intro same
    exact closing_actor_retained trace episode lower (Nat.le_of_lt upper) ((actor.trans same) ▸ withdrawn)
  have actual := (trace.step time bound).1
  rw [event] at actual
  change command.Step _ _ at actual
  rw [event]
  cases command with
  | insert name component => exact False.elim (vacant_not_withdrawn trace episode (Nat.le_of_lt bound) actual.1.1 withdrawn)
  | retire name =>
    have sameName : name = trace.actor time := actor
    have ended : trace.state (time + 1) = Calculus.retire (trace.state time) (trace.actor time) := by
      simpa only [Command.apply, sameName] using actual.2
    obtain ⟨registry, notes, _⟩ := probe_after_retire trace episode bound ended
    rw [registry, ← sameName]
    refine ⟨?_, notes, by simp [eventRoots, commandRoots, show rootAt (trace.state time) name = false from child]⟩
    funext query
    by_cases selected : query = name
    · subst query
      simp [Calculus.retire, Calculus.modify, show probeAt trace episode time name = none from absent]
    · simp [Calculus.retire, Calculus.modify, selected]
  | remove name =>
    have sameName : name = trace.actor time := actor
    have ended : trace.state (time + 1) = erase (trace.state time) (trace.actor time) := by
      simpa only [Command.apply, sameName] using actual.2
    have ⟨registry, mask⟩ := probe_after_remove trace episode bound different ended
    have stutter : probeAt trace episode (time + 1) = probeAt trace episode time := by
      rw [registry, ← sameName]
      funext query
      by_cases selected : query = name
      · subst query
        simp [erase, show probeAt trace episode time name = none from absent]
      · simp [erase, selected]
    refine ⟨stutter, ?_, by simp [eventRoots, commandRoots, show rootAt (trace.state time) name = false from child]⟩
    apply Prod.ext
    · funext query
      have one := probe_births trace episode time (by omega) query
      have two := probe_births trace episode (time + 1) (by omega) query
      by_cases selected : query = trace.actor time
      · subst query
        have gone : probeAt trace episode time (trace.actor time) = none := actor ▸ absent
        exact (two.mpr (stutter.symm ▸ gone)).trans (one.mpr gone).symm
      · have live := trace.live_unchanged_at bound query (by simp [ended, erase, selected])
        change (if withdraws trace episode (time + 1) query then none else (trace.notes (time + 1)).1 query) =
          if withdraws trace episode time query then none else (trace.notes time).1 query
        rw [mask query selected, live]
    · funext query
      change (if query = episode.name then [] else (trace.notes (time + 1)).2 query) =
        if query = episode.name then [] else (trace.notes time).2 query
      by_cases selected : query = trace.actor time
      · subst query
        rw [if_neg different, if_neg different]
        have old : trace.state time (trace.actor time) ≠ none := by
          simpa [← sameName] using Transposition.removable_present _ name actual.1
        cases found : trace.state time (trace.actor time) with
        | none => exact False.elim (old found)
        | some row =>
          have dormant := (probe_projects trace episode maximal quiet lower (Nat.le_of_lt upper)).dormant
            (trace.actor time) (actor ▸ withdrawn)
          have inactive : row.phase = .inactive := by
            cases phase : row.phase <;> simp [ControlFrame.viewAt, found, phase, Phase.committed] at dormant ⊢
          have empty : ((trace.notes time).2 (trace.actor time)).map Capture.token = [] := by
            simpa [saved, found, inactive, Phase.accumulator] using trace.projects time (by omega) (trace.actor time)
          rw [List.map_eq_nil_iff.mp empty]
          have cleared : ((trace.notes (time + 1)).2 (trace.actor time)).map Capture.token = [] := by
            simpa only [saved, ended, erase, if_pos rfl, Option.map_none, Option.getD_none] using trace.projects (time + 1) (by omega) (trace.actor time)
          exact List.map_eq_nil_iff.mp cleared
      · rw [trace.foreign_word_unchanged bound selected]

/-- A retained allocation keeps both its actual child and its guard. In
particular an older retirement capture at that name remains stale. -/
private theorem replay_marked_birth (trace : Trace program last) (episode : ClosedEpisode trace)
    {time : Nat} (bound : time < last) {child : Name} {component : Component Key Code}
    {phase : Phase Name Key Code I} {kind : Lifecycle}
    (event : trace.event time = .lifecycle kind (trace.actor time)) (native : kind ≠ .unload)
    (different : trace.actor time ≠ episode.name)
    (kept : ¬ withdraws trace episode time (trace.actor time) = true)
    (freshName : trace.state time child = none) (childDifferent : child ≠ episode.name)
    (ended : trace.state (time + 1) = mark
      (put (trace.state time) child (fresh component (some (trace.actor time)))) (trace.actor time) phase)
    (moved : Labeled.Step program kind.rule (trace.actor time) (probeAt trace episode time)
      (mark (put (probeAt trace episode time) child (fresh component (some (trace.actor time))))
        (trace.actor time) phase)) :
    GuardedSuffix.Step program (trace.event time) (time + 1) (probeAt trace episode time) (probeNotes trace episode time)
      (probeAt trace episode (time + 1)) (probeNotes trace episode (time + 1)) := by
  have born : trace.state (time + 1) child ≠ none := by
    rw [ended, ne_eq, Transposition.mark_presence]
    simp
  have outside (other : Name) (distinct : other ≠ child) :
      trace.state (time + 1) other = none ↔ trace.state time other = none := by
    rw [ended, Transposition.mark_presence, Transposition.put_other _ _ _ _ distinct]
  obtain ⟨mask, same⟩ := rollbackOf_next_birth trace episode bound different freshName born outside
  have exactEndpoint : probeAt trace episode (time + 1) =
      mark (put (probeAt trace episode time) child (fresh component (some (trace.actor time)))) (trace.actor time) phase := by
    change rollbackOf trace episode (time + 1) (trace.state (time + 1)) = _
    rw [same, ended, rollbackOf_mark _ _ _ _ _ _ different kept,
      rollbackOf_put_fresh trace episode time (Nat.le_of_lt bound) _ _ freshName childDifferent]
  refine ⟨?_, probe_notes_of_step trace episode bound
    (fun name present omitted => present (if_pos ((congrFun mask name).trans omitted)))
    (fun _ => probe_keeps_saved trace episode different kept)
    (fun _ => probe_keeps_saved trace episode different (by rwa [mask]))⟩
  rw [event, exactEndpoint]
  cases kind
  case unload => exact False.elim (native rfl)
  all_goals exact moved

theorem replay_allocation_activation (trace : Trace program last) (episode : ClosedEpisode trace)
    (maximal : ∀ later : ClosedEpisode trace, ¬ EpisodeEdge episode later)
    (quiet : Progress.Quiet (trace.state last))
    {time : Nat} (lower : episode.opened ≤ time) (upper : time < episode.closed)
    {kind : Lifecycle} (event : trace.event time = .lifecycle kind (trace.actor time))
    (different : trace.actor time ≠ episode.name)
    (kept : ¬ withdraws trace episode time (trace.actor time) = true)
    {row : Fiber Name Key Value Code I Error} {code : Code} {word : List I} {view : View Name Key}
    (present : trace.state time (trace.actor time) = some row)
    (phase : row.phase = .reloading code word view)
    (target : Target (trace.state time) (trace.actor time) view)
    {child : Name} {component : Component Key Code} (action : (program code).action = .instantiate component)
    (ready : Insertable (trace.state time) child component (some (trace.actor time)))
    (label : kind.rule = Transposition.landedRule ((program code).next (.child child)))
    (ended : trace.state (time + 1) = mark
      (put (trace.state time) child (fresh component (some (trace.actor time)))) (trace.actor time)
      (Transposition.landedPhase ((program code).next (.child child)) (.retire child) word view)) :
    GuardedSuffix.Step program (trace.event time) (time + 1) (probeAt trace episode time) (probeNotes trace episode time)
      (probeAt trace episode (time + 1)) (probeNotes trace episode (time + 1)) := by
  obtain ⟨other, found, phaseAt⟩ := probe_keeps_phase trace episode different kept present
  have projected := probe_projects trace episode maximal quiet lower (Nat.le_of_lt upper)
  have avoids := committed_avoids_closing trace episode maximal lower (Nat.le_of_lt upper) present
    (show row.phase.committed = some view by simp [phase, Phase.committed])
  have pairedReady := projected.insertable (fun parent identifies => by cases identifies; exact kept) ready
  have native : kind ≠ .unload := by
    intro impossible
    subst kind
    cases next : (program code).next (.child child) <;> simp [Lifecycle.rule, Transposition.landedRule, next] at label
  apply replay_marked_birth trace episode (Nat.lt_trans upper episode.interval.bounded) event native different kept
    ready.1 (vacant_ne_closing trace episode lower (Nat.le_of_lt upper) ready.1) ended
  rw [label]
  exact Transposition.landed_step program other word view found (phaseAt.trans phase)
    (projected.target_forward kept present view avoids target) (.instantiate _ _ _ _ _ action pairedReady)

theorem replay_allocation_divert (trace : Trace program last) (episode : ClosedEpisode trace)
    (maximal : ∀ later : ClosedEpisode trace, ¬ EpisodeEdge episode later)
    (quiet : Progress.Quiet (trace.state last))
    {time : Nat} (lower : episode.opened ≤ time) (upper : time < episode.closed)
    (event : trace.event time = .lifecycle .divert (trace.actor time))
    (different : trace.actor time ≠ episode.name)
    (kept : ¬ withdraws trace episode time (trace.actor time) = true)
    {row : Fiber Name Key Value Code I Error} {code : Code} {word : List I} {view : View Name Key}
    (present : trace.state time (trace.actor time) = some row)
    (phase : row.phase = .reloading code word view)
    (stale : ¬ Target (trace.state time) (trace.actor time) view)
    {child : Name} {component : Component Key Code} (action : (program code).action = .instantiate component)
    (ready : Insertable (trace.state time) child component (some (trace.actor time)))
    (ended : trace.state (time + 1) = mark
      (put (trace.state time) child (fresh component (some (trace.actor time)))) (trace.actor time)
      (.unloading (.retire child :: word) view)) :
    GuardedSuffix.Step program (trace.event time) (time + 1) (probeAt trace episode time) (probeNotes trace episode time)
      (probeAt trace episode (time + 1)) (probeNotes trace episode (time + 1)) := by
  obtain ⟨other, found, phaseAt⟩ := probe_keeps_phase trace episode different kept present
  have projected := probe_projects trace episode maximal quiet lower (Nat.le_of_lt upper)
  have pairedReady := projected.insertable (fun parent identifies => by cases identifies; exact kept) ready
  exact replay_marked_birth trace episode (Nat.lt_trans upper episode.interval.bounded) event (by decide) different kept
    ready.1 (vacant_ne_closing trace episode lower (Nat.le_of_lt upper) ready.1) ended
    (.divert _ _ _ other code word view [.retire child] found (phaseAt.trans phase)
      (fun active => stale (projected.target_backward _ _ active))
      (.inr ⟨_, _, .instantiate _ _ _ _ _ action pairedReady, rfl⟩))

end Cordis.Repairs.GuardedHistory
