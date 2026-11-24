import Cordis.Repairs.GuardedSuffix

/-! The closing boundary of Lemma 79. Discharge uses the original saved
word and the live birth indices at the cut. Its retirement guards matter
for the external removal commands in the suffix. -/
namespace Cordis.Repairs.EpisodeClosure
open Calculus Stages Indexed Incarnation IncarnationReplay
open EpisodeDependencies EpisodeBoundary EpisodeRollback
open PartialReplayRegistry (saved)
open StageRecovery (tableAt)
open Iterators (OptionRel)
universe u
variable {Name Key Value Code Error : Type u} [DecidableEq Name] [DecidableEq Key]
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
local notation "C" => Capture Name Key Value
variable {program : Code → Instruction Name Key Value Code Error} {last : Nat}
local notation "History" => Trace program (fun _ => none : R) last

/-- The closing L-Unload uses the saved word, with retirement matched
against the live incarnation. The vestiges still occupy their rows here. -/
def correctedClosure (trace : History) (episode : ClosedEpisode trace) : R :=
  mark (replayAt trace.state episode.closed (track trace.state trace.actor episode.closed episode.name))
    episode.name .inactive

omit [DecidableEq Key] in
private theorem matching_is_named (live : Name → Option Nat) (word : List C) (name : Name)
    (matched : word.any (Capture.retires live name) = true) :
    (word.map fun capture => (⟨capture.token, 0⟩ : C)).any (Capture.retires (fun _ => some 0) name) = true := by
  obtain ⟨capture, member, retires⟩ := List.any_eq_true.mp matched
  apply List.any_eq_true.mpr
  refine ⟨⟨capture.token, 0⟩, List.mem_map_of_mem member, ?_⟩
  cases token : capture.token with
  | retire child =>
    have selected : name = child ∧ live child = some capture.index := by
      simpa [Capture.retires, token] using retires
    simp [Capture.retires, selected.1]
  | _ => simp [Capture.retires, token] at retires

omit [DecidableEq Key] in
private theorem named_without_match (live : Name → Option Nat) (word : List C) (name : Name)
    (named : (word.map fun capture => (⟨capture.token, 0⟩ : C)).any (Capture.retires (fun _ => some 0) name) = true)
    (unmatched : word.any (Capture.retires live name) = false) :
    ∃ capture ∈ word, capture.token = .retire name ∧ live name ≠ some capture.index := by
  obtain ⟨item, member, retires⟩ := List.any_eq_true.mp named
  obtain ⟨capture, recorded, rfl⟩ := List.mem_map.mp member
  have fails := List.any_eq_false.mp unmatched capture recorded
  cases token : capture.token with
  | retire child =>
    have selected : name = child := by simpa [Capture.retires, token] using retires
    subst child
    exact ⟨capture, recorded, token, by simpa [Capture.retires, token] using fails⟩
  | _ => simp [Capture.retires, token] at retires

structure ClosingFields (live : Name → Option Nat) (word : List C) (name : Name) (ordinary guarded : F) : Prop where
  component : ordinary.component = guarded.component
  parent : ordinary.parent = guarded.parent
  table : ordinary.table = guarded.table
  phase : ordinary.phase = guarded.phase
  retired : guarded.retired = true → ordinary.retired = true
  stale : ordinary.retired ≠ guarded.retired →
    ∃ capture ∈ word, capture.token = .retire name ∧ live name ≠ some capture.index

/-- At the real closing event, every row survives both forms of discharge.
All fields agree except a retirement caused by a stale capture. -/
theorem closing_fields (trace : History) (episode : ClosedEpisode trace) (name : Name) :
    OptionRel (ClosingFields (fun name => birthAt trace.state name episode.closed)
      (track trace.state trace.actor episode.closed episode.name) name)
      (trace.state (episode.closed + 1) name) (correctedClosure trace episode name) := by
  let time := episode.closed
  let state := trace.state time
  let live := fun target => birthAt trace.state target time
  let word := track trace.state trace.actor time episode.name
  let always := fun (_ : Name) => some 0
  let rawWord := word.map fun capture => (⟨capture.token, 0⟩ : C)
  let ordinary := replay always rawWord state
  let guarded := replay live word state
  let fields : F → F → Prop := ClosingFields live word name
  have bounded := episode.interval.bounded
  obtain ⟨parent, raw, view, foundParent, unloading, _, endpoint⟩ := unload_boundary trace episode.interval
  have savedWord : word.map Capture.token = raw := by
    change (track trace.state trace.actor time episode.name).map Capture.token = _
    rw [(tracked_stack trace time (by omega)).projects]
    simp [saved, time, foundParent, unloading, Phase.accumulator]
  have native : ordinary = discharge Stages.undo raw state := by
    unfold ordinary rawWord always
    rw [← savedWord]
    simpa only [List.map_map, Function.comp_def] using replay_native_discharge state (word.map Capture.token)
  have tables : ∀ key, tableAt ordinary name key = tableAt guarded name key := by
    intro key
    rw [native, ← savedWord]
    exact replay_tables live word (left := state) (right := state) (fun _ _ => rfl) name key
  change OptionRel fields (trace.state (time + 1) name) (mark guarded episode.name .inactive name)
  have nativeClosure : trace.state (time + 1) = mark ordinary episode.name .inactive :=
    (show trace.state (time + 1) = _ from endpoint).trans (congrArg (fun r => mark r episode.name .inactive) native.symm)
  rw [nativeClosure]
  cases before : state name with
  | none =>
    have left := (Transposition.mark_presence ordinary episode.name name .inactive).mpr
      ((replay_presence always rawWord state name).mpr before)
    have right := (Transposition.mark_presence guarded episode.name name .inactive).mpr
      ((replay_presence live word state name).mpr before)
    simp [left, right, OptionRel]
  | some row =>
    obtain ⟨old, oldAt, oldComponent, oldParent, oldPhase⟩ := replay_keeps_control always rawWord state name row before
    obtain ⟨new, newAt, newComponent, newParent, newPhase⟩ := replay_keeps_control live word state name row before
    have oldFlag := replay_retired always rawWord state name
    have newFlag := replay_retired live word state name
    change ordinary name = some old at oldAt
    change guarded name = some new at newAt
    rw [show replay always rawWord state name = some old from oldAt, before] at oldFlag
    rw [show replay live word state name = some new from newAt, before] at newFlag
    simp only [Option.map_some, Option.some.injEq] at oldFlag newFlag
    have fieldsAgree : fields old new := by
      refine ⟨oldComponent.trans newComponent.symm, oldParent.trans newParent.symm, ?_,
        oldPhase.trans newPhase.symm, ?_, ?_⟩
      · funext key
        simpa only [tableAt, oldAt, newAt, Option.bind_some] using tables key
      · rw [oldFlag, newFlag]
        intro retired
        cases flag : row.retired with
        | false =>
          have matched : word.any (Capture.retires live name) = true := by simpa only [flag, Bool.false_or] using retired
          exact matching_is_named live word name matched
        | true => rfl
      · intro changed
        have unretired : row.retired = false := by
          cases flag : row.retired
          · rfl
          · apply False.elim (changed ?_)
            simp [oldFlag, newFlag, flag]
        have missed : word.any (Capture.retires live name) = false := by
          apply Bool.eq_false_iff.mpr
          intro hit
          have named : rawWord.any (Capture.retires always name) = true := matching_is_named live word name hit
          exact changed (by rw [oldFlag, newFlag, unretired, named, hit])
        have named : rawWord.any (Capture.retires always name) = true := by
          cases flag : rawWord.any (Capture.retires always name) with
          | false => exact False.elim (changed (by rw [oldFlag, newFlag, unretired, flag, missed]))
          | true => rfl
        exact named_without_match live word name named missed
    by_cases selected : name = episode.name
    · subst name
      rw [mark_self _ _ _ _ oldAt, mark_self _ _ _ _ newAt]
      exact ⟨fieldsAgree.component, fieldsAgree.parent, fieldsAgree.table, rfl, fieldsAgree.retired, fieldsAgree.stale⟩
    · rw [Transposition.mark_other _ _ _ _ selected, Transposition.mark_other _ _ _ _ selected, oldAt, newAt]
      exact fieldsAgree

/-- A live child withdrawn by the closing episode meets the removal guard
in the corrected closing registry, with its original parent provenance. -/
theorem corrected_closure_vestigial (trace : History) (episode : ClosedEpisode trace)
    (roots : PaperLifecycleClaims.RootInsertions trace)
    (maximal : ∀ later : ClosedEpisode trace, ¬ EpisodeEdge episode later)
    (quiet : Progress.Quiet (trace.state last)) {child : Name}
    (withdrawn : withdraws trace episode episode.closed child = true) :
    Removable (correctedClosure trace episode) child ∧ LegalHistory.rootAt (correctedClosure trace episode) child = false := by
  let ordinary := trace.state (episode.closed + 1)
  let corrected := correctedClosure trace episode
  obtain ⟨eligible, nonroot⟩ := withdrawn_at_closure_vestigial trace episode roots maximal quiet withdrawn
  obtain ⟨step, starts, earlier, creator, native, lives⟩ :=
    withdrawn_birth trace episode episode.interval.ordered (Nat.le_refl _) withdrawn
  have flag : (corrected child).map Fiber.retired = some true :=
    (child_retired_at_closure trace episode starts earlier creator native lives).2
  have paired := closing_fields trace episode child
  change Removable ordinary child at eligible
  change LegalHistory.rootAt ordinary child = false at nonroot
  change OptionRel _ (ordinary child) (corrected child) at paired
  cases oldAt : ordinary child with
  | none => simp [Removable, oldAt] at eligible
  | some old =>
    cases newAt : corrected child with
    | none => simp [OptionRel, oldAt, newAt] at paired
    | some new =>
      rw [oldAt, newAt] at paired
      rw [Removable, oldAt] at eligible
      change Removable corrected child ∧ LegalHistory.rootAt corrected child = false
      rw [Removable, newAt]
      refine ⟨⟨by simpa only [newAt, Option.map_some, Option.some.injEq] using flag,
        paired.phase.symm.trans eligible.2.1, fun key => ?_, ?_⟩, ?_⟩
      · rw [← paired.table]
        exact eligible.2.2.1 key
      · intro name
        have aligned := closing_fields trace episode name
        change OptionRel _ (ordinary name) (corrected name) at aligned
        cases target : corrected name with
        | none => trivial
        | some entry =>
          cases source : ordinary name with
          | none => simp [OptionRel, source, target] at aligned
          | some original =>
            rw [source, target] at aligned
            have noChild := eligible.2.2.2 name
            rw [source] at noChild
            simpa only [← aligned.parent] using noChild
      · simpa only [LegalHistory.rootAt, oldAt, newAt, Option.any_some, ← paired.parent] using nonroot

omit [DecidableEq Key] in
private theorem distinct_members (names : List Name) :
    ∃ distinct : List Name, distinct.Nodup ∧ ∀ name, name ∈ distinct ↔ name ∈ names := by
  induction names with
  | nil => exact ⟨[], .nil, fun _ => Iff.rfl⟩
  | cons first rest ih =>
    obtain ⟨prior, unique, members⟩ := ih
    by_cases recorded : first ∈ rest
    · refine ⟨prior, unique, fun name => (members name).trans ?_⟩
      exact ⟨fun later => List.mem_cons_of_mem _ later, fun later =>
        (List.mem_cons.mp later).elim (fun same => same.symm ▸ recorded) id⟩
    · exact ⟨first :: prior, List.nodup_cons.mpr ⟨fun member => recorded ((members first).mp member), unique⟩,
        fun name => by simp only [List.mem_cons, members name]⟩

omit [DecidableEq Key] in
theorem matching_children (live : Name → Option Nat) (word : List C) :
    ∃ names : List Name, names.Nodup ∧
      ∀ name, name ∈ names ↔ word.any (Capture.retires live name) = true := by
  let chosen (capture : C) : Option Name := match capture.token with
    | .retire child => if live child = some capture.index then some child else none
    | _ => none
  have exactly (name : Name) (capture : C) : chosen capture = some name ↔ Capture.retires live name capture = true := by
    cases token : capture.token with
    | retire child =>
      by_cases current : live child = some capture.index
      · simp [chosen, Capture.retires, token, current, eq_comm]
      · simp [chosen, Capture.retires, token, current]
    | _ => simp [chosen, Capture.retires, token]
  obtain ⟨names, unique, selected⟩ := distinct_members (word.filterMap chosen)
  refine ⟨names, unique, fun name => ?_⟩
  rw [selected name, List.mem_filterMap]
  simp only [List.any_eq_true, exactly]

/-- The finite mask supplies exactly the vestiges to remove from the
incarnation-aware closing registry. The probe is that exact projection. -/
theorem closing_withdrawals (trace : History) (episode : ClosedEpisode trace)
    (roots : PaperLifecycleClaims.RootInsertions trace)
    (maximal : ∀ later : ClosedEpisode trace, ¬ EpisodeEdge episode later)
    (quiet : Progress.Quiet (trace.state last)) :
    ∃ names : List Name, names.Nodup ∧
      (∀ name, name ∈ names ↔ withdraws trace episode episode.closed name = true) ∧
      probeAt trace episode episode.closed = Vestigial.eraseAll names (correctedClosure trace episode) ∧
      ∀ name ∈ names, Removable (correctedClosure trace episode) name ∧
        LegalHistory.rootAt (correctedClosure trace episode) name = false := by
  let word := track trace.state trace.actor episode.closed episode.name
  let live := fun name => birthAt trace.state name episode.closed
  obtain ⟨names, unique, membership⟩ := matching_children live word
  change (∀ name, name ∈ names ↔ withdraws trace episode episode.closed name = true) at membership
  refine ⟨names, unique, membership, ?_, ?_⟩
  · funext name
    rw [Vestigial.eraseAll_apply]
    change (if withdraws trace episode episode.closed name then none else correctedClosure trace episode name) = _
    by_cases member : name ∈ names
    · rw [if_pos member, if_pos ((membership name).mp member)]
    · rw [if_neg member, if_neg (fun withdrawn => member ((membership name).mpr withdrawn))]
  · intro name member
    exact corrected_closure_vestigial trace episode roots maximal quiet ((membership name).mp member)

def postNotes (trace : History) (episode : ClosedEpisode trace) : Vestigial.CutNotes Name Key Value :=
  Vestigial.cutNotes trace.state trace.actor (episode.closed + 1)

theorem correctedClosure_births (trace : History) (episode : ClosedEpisode trace) :
    GuardedSuffix.BirthsAgree (correctedClosure trace episode) (postNotes trace episode) := by
  intro name
  change birthAt trace.state name (episode.closed + 1) = none ↔ correctedClosure trace episode name = none
  rw [birthAt_none]
  have same := closing_fields trace episode name
  cases oldAt : trace.state (episode.closed + 1) name <;> cases newAt : correctedClosure trace episode name <;>
    simp_all [OptionRel]

theorem closing_notes_erased (trace : History) (episode : ClosedEpisode trace)
    (roots : PaperLifecycleClaims.RootInsertions trace)
    (maximal : ∀ later : ClosedEpisode trace, ¬ EpisodeEdge episode later)
    (quiet : Progress.Quiet (trace.state last)) (names : List Name)
    (membership : ∀ name, name ∈ names ↔ withdraws trace episode episode.closed name = true) :
    EpisodeAnnotations.probeNotes trace episode episode.closed = GuardedSuffix.eraseAllNotes names (postNotes trace episode) := by
  rw [EpisodeAnnotations.probeNotes_at_closure, GuardedSuffix.eraseAllNotes_apply]
  apply Prod.ext
  · funext name
    change (if withdraws trace episode episode.closed name then none else birthAt trace.state name (episode.closed + 1)) =
      if name ∈ names then none else birthAt trace.state name (episode.closed + 1)
    by_cases member : name ∈ names
    · rw [if_pos member, if_pos ((membership name).mp member)]
    · rw [if_neg member, if_neg (fun withdrawn => member ((membership name).mpr withdrawn))]
  · funext name
    change track trace.state trace.actor (episode.closed + 1) name =
      if name ∈ names then [] else track trace.state trace.actor (episode.closed + 1) name
    by_cases member : name ∈ names
    · rw [if_pos member]
      have ready := (withdrawn_at_closure_vestigial trace episode roots maximal quiet ((membership name).mp member)).1
      have empty : saved (trace.state (episode.closed + 1)) name = [] := by
        cases found : trace.state (episode.closed + 1) name with
        | none => simp [saved, found]
        | some row =>
          simp only [Removable, found] at ready
          simp [saved, found, ready.2.1, Phase.accumulator]
      have bounded := episode.interval.bounded
      exact List.map_eq_nil_iff.mp (((tracked_stack trace (episode.closed + 1) (by omega)).projects name).trans empty)
    · rw [if_neg member]

/-- A legal guarded suffix starting at the corrected closing state
projects from the closing probe with its actual birth and capture notes.
No suffix command is moved before its enabling removal. -/
theorem guarded_suffix_from_closing_probe (trace : History) (episode : ClosedEpisode trace)
    (roots : PaperLifecycleClaims.RootInsertions trace)
    (maximal : ∀ later : ClosedEpisode trace, ¬ EpisodeEdge episode later)
    (quiet : Progress.Quiet (trace.state last))
    {events : List (Nat × LegalHistory.Event Name Key Code)}
    {final : R} {finalNotes : Vestigial.CutNotes Name Key Value}
    {rootCommands : List (OrchestrationSorting.Command Name Key Code)}
    (suffix : GuardedSuffix.Exec program events (correctedClosure trace episode) (postNotes trace episode)
      final finalNotes rootCommands) :
    ∃ names : List Name, names.Nodup ∧
      (∀ name, name ∈ names ↔ withdraws trace episode episode.closed name = true) ∧
      GuardedSuffix.Exec program (GuardedSuffix.pruneAll names events) (probeAt trace episode episode.closed)
        (EpisodeAnnotations.probeNotes trace episode episode.closed)
        (Vestigial.eraseAll (GuardedSuffix.stillPresent names events) final)
        (GuardedSuffix.eraseAllNotes (GuardedSuffix.stillPresent names events) finalNotes) rootCommands := by
  obtain ⟨names, unique, membership, registry, vestiges⟩ := closing_withdrawals trace episode roots maximal quiet
  have projected := GuardedSuffix.prune_all suffix names unique (correctedClosure_births trace episode) vestiges
  have notes := closing_notes_erased trace episode roots maximal quiet names membership
  rw [← registry, ← notes] at projected
  exact ⟨names, unique, membership, projected⟩

end Cordis.Repairs.EpisodeClosure
