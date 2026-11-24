import Cordis.Repairs.GuardedDrawReplay
import Cordis.Repairs.GuardedReservationOrder
import Cordis.Repairs.GuardedActivationAlignment

/-! Replace one fresh draw for the lifetime of the child. A later birth
at the old name and every external insertion retain their raw names. -/
namespace Cordis.Repairs.GuardedIncarnationRedraw
open Calculus Stages LegalHistory GuardedHistory GuardedCutState GuardedBirthAddresses GuardedAddressSchedule
open GuardedScheduleMatching GuardedDrawReplay GuardedReservationOrder Incarnation IncarnationReplay
open GuardedLandingMatching (ChildContinuations)
open GuardedActivationOccurrence (pending_activation_occurs)
open GuardedActivationAlignment (AdjacentActivationExchange move_waiting_activation_one_step_with_exchange)
open FreshNameTransport (swap swap_first swap_other)

universe u
variable {Name Key Value Code Error : Type u} [DecidableEq Name] [DecidableEq Key]
variable {program : Code → Instruction Name Key Value Code Error} {last : Nat}
local notation "P" => Renaming.Permutation Name
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error

private def identity : P := ⟨id, id, fun _ => rfl, fun _ => rfl⟩

private def lifetimeNames (old fresh : Name) (birth final cut : Nat) : P :=
  if birth - 1 ≤ cut ∧ cut ≤ final then swap old fresh else identity

private theorem fixed_outside {old fresh : Name} {birth final cut : Nat}
    (outside : ¬ (birth - 1 ≤ cut ∧ cut ≤ final)) (name : Name) :
    (lifetimeNames old fresh birth final cut).toFun name = name := by
  rw [lifetimeNames, if_neg outside]
  rfl

private theorem lifetimeNames_consistent (trace : Trace program last) {old fresh : Name} {birth final : Nat}
    (oldBefore : trace.state (birth - 1) old = none)
    (oldAfter : final < last → trace.state (final + 1) old = none)
    (freshBefore : trace.state (birth - 1) fresh = none)
    (freshAfter : final < last → trace.state (final + 1) fresh = none) :
    ∀ cut, cut < last → ∀ name, trace.state (cut + 1) name ≠ none →
      (lifetimeNames old fresh birth final cut).toFun name = (lifetimeNames old fresh birth final (cut + 1)).toFun name := by
  intro cut inside name present
  by_cases earlier : birth - 1 ≤ cut ∧ cut ≤ final <;>
    by_cases later : birth - 1 ≤ cut + 1 ∧ cut + 1 ≤ final
  · simp only [lifetimeNames, if_pos earlier, if_pos later]
  · have atEnd : cut = final := by omega
    subst cut
    have oldVacant := oldAfter inside
    have freshVacant := freshAfter inside
    have keepOld : name ≠ old := fun equal => present (equal.symm ▸ oldVacant)
    have keepFresh : name ≠ fresh := fun equal => present (equal.symm ▸ freshVacant)
    simpa only [lifetimeNames, if_pos earlier, if_neg later] using (swap_other keepOld keepFresh)
  · have atBirth : cut + 1 = birth - 1 := by omega
    have oldVacant := oldBefore
    have freshVacant : trace.state (cut + 1) fresh = none := atBirth.symm ▸ freshBefore
    have keepOld : name ≠ old := fun equal => present (equal.symm ▸ (atBirth.symm ▸ oldVacant))
    have keepFresh : name ≠ fresh := fun equal => present (equal.symm ▸ freshVacant)
    simpa only [lifetimeNames, if_neg earlier, if_pos later] using (swap_other keepOld keepFresh).symm
  · simp only [lifetimeNames, if_neg earlier, if_neg later]

/-- The replay renames events and projected registries at each cut, keeps
birth stamps, and changes the permutation only off the next cut's live names.
External insertions keep their original names. -/
def ConsistentRedraw (source moved : Trace program last) : Prop :=
  ∃ names : Nat → P,
    (∀ time, time < last → moved.event time = GuardedRenaming.event (names time) (source.event time)) ∧
    (∀ time, time ≤ last →
      Renaming.registry (names time) (project (source.state time)) = project (moved.state time) ∧
      ∀ name, (moved.notes time).1 ((names time).toFun name) = (source.notes time).1 name) ∧
    (∀ time, time < last → ∀ name, source.state (time + 1) name ≠ none →
      (names time).toFun name = (names (time + 1)).toFun name) ∧
    (∀ time name component, time < last → source.event time = .command (.insert name component) →
      (names time).toFun name = name)

/-- A consistent redraw maps an active endpoint row to an active row
with the same component, table and birth address. -/
theorem ConsistentRedraw.active_endpoint_address {source moved : Trace program last}
    (redraw : ConsistentRedraw source moved) {name : Name}
    {row : Fiber Name Key Value Code (Inverse Name Key Value) Error}
    (found : source.state last name = some row) (active : row.phase.available) :
    ∃ target peer birth address, moved.state last target = some peer ∧ peer.phase.available ∧
      peer.component = row.component ∧
      (source.notes last).1 name = some birth ∧ (moved.notes last).1 target = some birth ∧
      Addressed source birth address ∧ Addressed moved birth address ∧ peer.table = row.table := by
  obtain ⟨names, labels, cuts, keeps, _⟩ := redraw
  let p := names last
  obtain ⟨states, tags⟩ := cuts last (Nat.le_refl _)
  have mapped := congrFun states (p.toFun name)
  change Renaming.registry p (project (source.state last)) (p.toFun name) =
    project (moved.state last) (p.toFun name) at mapped
  rw [Renaming.registry_at] at mapped
  cases actual : moved.state last (p.toFun name) with
  | none => simp [project, found, actual] at mapped
  | some peer =>
    have rows : Renaming.fiber p (projectFiber name row) = projectFiber (p.toFun name) peer := by
      simpa [project, found, actual] using mapped
    have components := congrArg Fiber.component rows
    have details := congrArg Fiber.phase rows
    have ready : peer.phase.available := by
      cases before : row.phase <;> cases after : peer.phase <;>
        simp [Phase.available, projectFiber, projectPhase, Renaming.fiber, Renaming.phase,
          before, after] at active details ⊢
    cases tag : (source.notes last).1 name with
    | none =>
      have vacant := (source.births_agree last (Nat.le_refl _) name).mp tag
      rw [found] at vacant
      cases vacant
    | some birth =>
      obtain ⟨address, addressed⟩ := exists_address source (GuardedBirthMatching.recorded_birth source (Nat.le_refl _) tag).1
      have sameAddress := birth_addresses_of_consistent_names source moved names labels cuts keeps addressed
      exact ⟨p.toFun name, peer, birth, address, actual, ready, components.symm, rfl,
        (tags name).trans tag, addressed, sameAddress, (congrArg Fiber.table rows).symm⟩

theorem ConsistentRedraw.active_endpoint_payload {source moved : Trace program last}
    (redraw : ConsistentRedraw source moved) {address : Address} {name target : Name}
    {row peer : Fiber Name Key Value Code (Inverse Name Key Value) Error}
    (first : ActiveEndpoint source address name row) (second : ActiveEndpoint moved address target peer) :
    row.component = peer.component ∧ row.table = peer.table := by
  obtain ⟨other, foundRow, birth, path, present, ready, components, tag, movedTag, addressed, movedAddressed, tables⟩ :=
    redraw.active_endpoint_address first.1 first.2.1
  obtain ⟨givenBirth, givenTag, givenAddress⟩ := first.2.2
  have stamps := Option.some.inj (tag.symm.trans givenTag)
  have paths := addressed.unique (stamps.symm ▸ givenAddress)
  have rows := (second.unique (show ActiveEndpoint moved address other foundRow from
    ⟨present, ready, birth, movedTag, paths ▸ movedAddressed⟩)).2
  exact ⟨rows.symm ▸ components.symm, rows.symm ▸ tables.symm⟩

/-- At matching adjacent cuts, any two stamp-preserving permutations
agree on the incarnations that are present on both sides of the step.
The only way to lose the matched name is the matching removal, which
would also have removed the source incarnation. -/
theorem matched_permutations_agree_on_survivors {source moved : Trace program last}
    {time : Nat} (bounded : time < last) (schedule : OpenEventsAgree source moved time)
    {p q : P}
    (before : ∀ name, (moved.notes time).1 (p.toFun name) = (source.notes time).1 name)
    (after : ∀ name, (moved.notes (time + 1)).1 (q.toFun name) = (source.notes (time + 1)).1 name)
    {name : Name} (present : source.state time name ≠ none)
    (survives : source.state (time + 1) name ≠ none) :
    p.toFun name = q.toFun name := by
  have movedPresent : moved.state time (p.toFun name) ≠ none := by
    intro missing
    exact present ((source.births_agree time (by omega) name).mp
      ((before name).symm.trans ((moved.births_agree time (by omega) _).mpr missing)))
  have movedSurvives : moved.state (time + 1) (p.toFun name) ≠ none := by
    intro missing
    have removal := removal_at_gap moved bounded movedPresent missing
    cases event : source.event time with
    | lifecycle => simp [OpenEventsAgree, event, removal] at schedule
    | command command =>
      cases command with
      | insert | retire => simp [OpenEventsAgree, event, removal] at schedule
      | remove target =>
        have same : (source.notes time).1 target = (source.notes time).1 name := by
          simpa [OpenEventsAgree, event, removal, before] using schedule
        cases tag : (source.notes time).1 name with
        | none => exact present ((source.births_agree time (by omega) name).mp tag)
        | some birth =>
          have equal := GuardedBirthMatching.live_stamp_unique source (by omega : time ≤ last)
            (same.trans tag) tag
          subst target
          have step := (source.step time bounded).1
          rw [event] at step
          exact survives (by rw [step.2]; simp [OrchestrationSorting.Command.apply, erase])
  have stays (trace : Trace program last) (actor : Name) (old : trace.state time actor ≠ none)
      (new : trace.state (time + 1) actor ≠ none) :
      (trace.notes (time + 1)).1 actor = (trace.notes time).1 actor := by
    rw [trace.notes_eq (time + 1) (by omega), trace.notes_eq time (by omega)]
    exact birth_stays trace.state actor time old new
  have matched : (moved.notes (time + 1)).1 (p.toFun name) =
      (moved.notes (time + 1)).1 (q.toFun name) := by
    rw [stays moved _ movedPresent movedSurvives, before, after, stays source _ present survives]
  cases tag : (moved.notes (time + 1)).1 (q.toFun name) with
  | none =>
    exact False.elim (movedSurvives ((moved.births_agree (time + 1) (by omega) _).mp (matched.trans tag)))
  | some birth =>
    exact GuardedBirthMatching.live_stamp_unique moved (by omega : time + 1 ≤ last) (matched.trans tag) tag

private theorem matched_step_permutation {source moved : Trace program last}
    {time : Nat} (bounded : time < last) (schedule : OpenEventsAgree source moved time)
    (current : CutAgreement source moved time) (next : CutAgreement source moved (time + 1))
    (roots : ∀ name other component, source.event time = .command (.insert name component) →
      moved.event time = .command (.insert other component) → name = other) :
    ∃ p : P, moved.event time = GuardedRenaming.event p (source.event time) ∧
      Renaming.registry p (project (source.state time)) = project (moved.state time) ∧
      (∀ name, (moved.notes time).1 (p.toFun name) = (source.notes time).1 name) ∧
      (∀ name, source.state (time + 1) name ≠ none →
        (moved.notes (time + 1)).1 (p.toFun name) = (source.notes (time + 1)).1 name) ∧
      ∀ name component, source.event time = .command (.insert name component) → p.toFun name = name := by
  obtain ⟨p, states, before, _⟩ := current
  obtain ⟨q, _, after, _⟩ := next
  have same (notRemove : ∀ name, source.event time ≠ .command (.remove name))
      (name : Name) (present : source.state time name ≠ none) : p.toFun name = q.toFun name :=
    matched_permutations_agree_on_survivors bounded schedule before after present
      (fun absent => notRemove name (removal_at_gap source bounded present absent))
  have useNext (notRemove : ∀ name, source.event time ≠ .command (.remove name)) :
      Renaming.registry q (project (source.state time)) = project (moved.state time) ∧
      ∀ name, (moved.notes time).1 (q.toFun name) = (source.notes time).1 name := by
    have renamed := (rename_on_live source (by omega) (same notRemove)).symm.trans states
    refine ⟨renamed, fun name => ?_⟩
    by_cases vacant : source.state time name = none
    · have missing := (GuardedReservationAlignment.vacancy_of_renamed_cut renamed name).mpr vacant
      rw [(source.births_agree time (by omega) name).mpr vacant,
        (moved.births_agree time (by omega) _).mpr missing]
    · rw [← same notRemove name vacant, before]
  have matchName (name other : Name) (present : source.state time name ≠ none)
      (tags : (source.notes time).1 name = (moved.notes time).1 other) : p.toFun name = other := by
    cases tag : (source.notes time).1 name with
    | none => exact False.elim (present ((source.births_agree time (by omega) name).mp tag))
    | some birth =>
      exact GuardedBirthMatching.live_stamp_unique moved (by omega : time ≤ last)
        ((before name).trans tag) (tags.symm.trans tag)
  cases first : source.event time with
  | lifecycle kind name =>
    cases second : moved.event time with
    | command => simp [OpenEventsAgree, first, second] at schedule
    | lifecycle otherKind other =>
      obtain ⟨rfl, active, tags⟩ := (show kind = otherKind ∧ _ from by
        simpa [OpenEventsAgree, first, second] using schedule)
      have step := (source.step time bounded).1
      rw [first] at step
      have native : Labeled.Step program kind.rule name (source.state time) (source.state (time + 1)) := by
        cases kind <;> first | exact step | simp [Lifecycle.rule, Transposition.Activation] at active
      obtain ⟨row, _, found, _, _⟩ := Transposition.activation_source program native active
      have present : source.state time name ≠ none := by simp [found]
      have notRemove (name : Name) : source.event time ≠ .command (.remove name) := by simp [first]
      have image := (same notRemove name present).symm.trans (matchName name other present tags)
      exact ⟨q, by simp [GuardedRenaming.event, image], (useNext notRemove).1,
        (useNext notRemove).2, fun name _ => after name, by simp⟩
  | command cmd =>
    cases second : moved.event time with
    | lifecycle => simp [OpenEventsAgree, first, second] at schedule
    | command otherCmd =>
      cases cmd <;> cases otherCmd <;> simp only [OpenEventsAgree, first, second] at schedule <;> try cases schedule
      case insert.insert.refl name component other =>
        have names := roots name other component first second
        subst other
        have birth (trace : Trace program last) (event : trace.event time = .command (.insert name component)) :
            (trace.notes (time + 1)).1 name = some (time + 1) := by
          have step := (trace.step time bounded).1
          rw [event] at step
          have fresh := step.1.1
          have found : trace.state (time + 1) name ≠ none := by
            rw [step.2]
            simp [OrchestrationSorting.Command.apply, put]
          rw [trace.notes_eq (time + 1) (by omega)]
          exact birthAt_of_created fresh found
        have image := GuardedBirthMatching.live_stamp_unique moved (by omega : time + 1 ≤ last)
          ((after name).trans (birth source first)) (birth moved second)
        have notRemove (target : Name) : source.event time ≠ .command (.remove target) := by simp [first]
        refine ⟨q, by simp [GuardedRenaming.event, GuardedRenaming.command, image], (useNext notRemove).1,
          (useNext notRemove).2, fun name _ => after name, ?_⟩
        intro target payload inserted
        have equal := OrchestrationSorting.Command.insert.inj (Event.command.inj inserted)
        exact equal.1 ▸ image
      case retire.retire name other =>
        obtain ⟨_, row, _, _, found, _, _⟩ := source.retire_remove_birth bounded (.inl first)
        have present : source.state time name ≠ none := by simp [found]
        have notRemove (target : Name) : source.event time ≠ .command (.remove target) := by simp [first]
        have image := (same notRemove name present).symm.trans (matchName name other present schedule)
        exact ⟨q, by simp [GuardedRenaming.event, GuardedRenaming.command, image], (useNext notRemove).1,
          (useNext notRemove).2, fun name _ => after name, by simp⟩
      case remove.remove name other =>
        obtain ⟨_, row, _, _, found, _, _⟩ := source.retire_remove_birth bounded (.inr first)
        have image := matchName name other (by simp [found]) schedule
        have left := (source.step time bounded).1
        have right := (moved.step time bounded).1
        rw [first] at left
        rw [second] at right
        have renamed : Renaming.registry p (project (source.state (time + 1))) = project (moved.state (time + 1)) := by
          rw [left.2, right.2]
          simp only [OrchestrationSorting.Command.apply, project_erase, Renaming.erase_eq, image, states]
        have aligned := GuardedBirthMatching.advance_cut source moved bounded bounded (stamp := id)
          (by simpa using before) (GuardedReservationAlignment.vacancy_of_renamed_cut renamed) rfl
        exact ⟨p, by simp [GuardedRenaming.event, GuardedRenaming.command, image], states, before,
          fun name _ => by simpa using aligned name, by simp⟩

/-- Matching open event orders with the same literal insertions admit
a consistent redraw, including every release and subsequent reuse. -/
theorem consistent_redraw_of_open_events (source moved : Trace program last)
    (stable : ChildContinuations program)
    (schedule : ∀ time, time < last → OpenEventsAgree source moved time)
    (roots : ∀ time name other component, time < last →
      source.event time = .command (.insert name component) →
      moved.event time = .command (.insert other component) → name = other) :
    ConsistentRedraw source moved := by
  classical
  have cut (time : Nat) (bounded : time ≤ last) : CutAgreement source moved time :=
    match_open_prefix source moved stable time bounded bounded
      (fun i earlier => schedule i (by omega))
  have step (time : Nat) (bounded : time < last) :=
    matched_step_permutation bounded (schedule time bounded) (cut time (by omega)) (cut (time + 1) (by omega))
      (fun name other component => roots time name other component bounded)
  let names (time : Nat) : P :=
    if bounded : time < last then Classical.choose (step time bounded)
    else if final : time = last then Classical.choose (cut time (by omega))
    else identity
  have atStep (time : Nat) (bounded : time < last) := Classical.choose_spec (step time bounded)
  have cutData (time : Nat) (bounded : time ≤ last) :
      Renaming.registry (names time) (project (source.state time)) = project (moved.state time) ∧
        ∀ name, (moved.notes time).1 ((names time).toFun name) = (source.notes time).1 name := by
    by_cases inside : time < last
    · simpa only [names, dif_pos inside] using ⟨(atStep time inside).2.1, (atStep time inside).2.2.1⟩
    · have final : time = last := by omega
      have data := Classical.choose_spec (cut time bounded)
      simpa only [names, dif_neg inside, dif_pos final] using ⟨data.1, data.2.1⟩
  refine ⟨names, ?_, cutData, ?_, ?_⟩
  · intro time bounded
    simpa only [names, dif_pos bounded] using (atStep time bounded).1
  · intro time bounded name present
    have before : (moved.notes (time + 1)).1 ((names time).toFun name) = (source.notes (time + 1)).1 name := by
      simpa only [names, dif_pos bounded] using (atStep time bounded).2.2.2.1 name present
    have after := (cutData (time + 1) (by omega)).2 name
    cases tag : (source.notes (time + 1)).1 name with
    | none => exact False.elim (present ((source.births_agree _ (by omega) name).mp tag))
    | some birth =>
      exact GuardedBirthMatching.live_stamp_unique moved (by omega : time + 1 ≤ last)
        (before.trans tag) (after.trans tag)
  · intro time name component bounded inserted
    simpa only [names, dif_pos bounded] using (atStep time bounded).2.2.2.2 name component inserted

/-- A consistent redraw cannot make room for an earlier birth at a full
cut. Any path placing the birth here must first change which rows are
present at this cut. -/
theorem ConsistentRedraw.no_birth_at_full_cut {source moved : Trace program last}
    (redraw : ConsistentRedraw source moved) {cut : Nat} (bounded : cut ≤ last)
    (full : ∀ name, source.state cut name ≠ none) {draw : Name} :
    ¬ GuardedBirthMatching.BornAt moved draw (cut + 1) := by
  obtain ⟨names, _, cuts, consistent, _⟩ := redraw
  intro born
  let original := (names cut).invFun draw
  have vacant : moved.state cut ((names cut).toFun original) = none := by
    simpa only [original, (names cut).right_inv, Nat.add_sub_cancel] using born.2.2.1
  exact full original ((GuardedReservationAlignment.vacancy_of_renamed_cut
    (cuts cut bounded).1 original).mp vacant)

/-- A replay with the same addressed schedule that replaces one actual
child draw and its captured retirement. -/
abbrev ChildRedraw (trace : Trace program last) (old fresh : Name) (birth final : Nat)
    (kind : Lifecycle) (parent : Name) : Prop :=
    ∃ moved : Trace program last,
      orchestrationInput moved = orchestrationInput trace ∧
      (∀ time, time < last → addressedEventAt moved time = addressedEventAt trace time) ∧
      (∀ time, final < time → time < last → moved.event time = trace.event time) ∧
      (∀ time, time < birth - 1 → moved.event time = trace.event time) ∧
      (∀ time, final < time → time ≤ last → (moved.notes time).1 = (trace.notes time).1) ∧
      moved.event (birth - 1) = .lifecycle kind parent ∧ moved.state birth old = none ∧
      (moved.notes (birth - 1)).1 parent = (trace.notes (birth - 1)).1 parent ∧
      GuardedBirthMatching.BornAt moved fresh birth ∧ (moved.notes birth).1 fresh = some birth ∧
      (⟨.retire fresh, birth⟩ : Capture Name Key Value) ∈ (moved.notes birth).2 (moved.actor (birth - 1)) ∧
      CutAgreement trace moved last ∧ (¬ Nonempty (ClosedEpisode moved)) ∧ Progress.Quiet (moved.state last) ∧
      (∀ cut, birth - 1 ≤ cut → cut ≤ final →
        (moved.notes cut).1 fresh = (trace.notes cut).1 old ∧
        (moved.notes cut).1 old = (trace.notes cut).1 fresh) ∧
      ConsistentRedraw trace moved

/-- The exchange needs the replayed prefix, the same acting incarnation,
and a vacant old draw after the replacement birth. Later names may be
assigned by an arbitrary consistent renaming. -/
abbrev RedrawForExchange (trace : Trace program last) (old : Name) (birth : Nat)
    (kind : Lifecycle) (parent : Name) : Prop :=
    ∃ moved : Trace program last,
      orchestrationInput moved = orchestrationInput trace ∧
      (∀ time, time < last → addressedEventAt moved time = addressedEventAt trace time) ∧
      (∀ time, time < birth - 1 → moved.event time = trace.event time) ∧
      moved.event (birth - 1) = .lifecycle kind parent ∧ moved.state birth old = none ∧
      (moved.notes (birth - 1)).1 parent = (trace.notes (birth - 1)).1 parent ∧
      CutAgreement trace moved last ∧ (¬ Nonempty (ClosedEpisode moved)) ∧ Progress.Quiet (moved.state last) ∧
      ConsistentRedraw trace moved

/-- A redraw that leaves the released name unused needs a second vacancy
at the post-removal cut, even if it reassigns all subsequent draws. -/
theorem RedrawForExchange.requires_second_vacancy {source : Trace program last}
    {cut : Nat} {old parent : Name} {kind : Lifecycle}
    (bounded : cut + 1 < last) (removal : source.event cut = .command (.remove old))
    (rebound : source.state (cut + 2) old ≠ none)
    (redraw : RedrawForExchange source old (cut + 2) kind parent) :
    ∃ spare, spare ≠ old ∧ source.state (cut + 1) spare = none := by
  obtain ⟨moved, _, _, earlier, _, unused, _, _, _, _, names, _, cuts, consistent, _⟩ := redraw
  have movedRemoval := (earlier cut (by omega)).trans removal
  have movedStep := (moved.step cut (by omega)).1
  rw [movedRemoval] at movedStep
  have movedVacant : moved.state (cut + 1) old = none := by
    rw [movedStep.2]
    simp [OrchestrationSorting.Command.apply, erase]
  let p := names (cut + 1)
  let q := names (cut + 2)
  have drawPresent : moved.state (cut + 2) (q.toFun old) ≠ none :=
    fun vacant => rebound ((GuardedReservationAlignment.vacancy_of_renamed_cut
      (cuts (cut + 2) (by omega)).1 old).mp vacant)
  have drawDistinct : q.toFun old ≠ old := by
    intro equal
    exact drawPresent (by rwa [equal])
  have carry := consistent (cut + 1) bounded old rebound
  let spare := p.invFun old
  refine ⟨spare, ?_, (GuardedReservationAlignment.vacancy_of_renamed_cut
    (cuts (cut + 1) (by omega)).1 spare).mp ?_⟩
  · intro equal
    apply drawDistinct
    have mapped : p.toFun spare = old := p.right_inv old
    rw [equal] at mapped
    exact carry.symm.trans mapped
  · change moved.state (cut + 1) (p.toFun (p.invFun old)) = none
    rwa [p.right_inv]

/-- At a full cut the removal creates the only vacancy, so the same
event order cannot be redrawn to enable the adjacent exchange. -/
theorem not_redraw_for_exchange_at_full_cut {source : Trace program last}
    {cut : Nat} {old parent : Name} {kind : Lifecycle}
    (bounded : cut + 1 < last) (removal : source.event cut = .command (.remove old))
    (rebound : source.state (cut + 2) old ≠ none)
    (full : ∀ name, source.state cut name ≠ none) :
    ¬ RedrawForExchange source old (cut + 2) kind parent := by
  intro redraw
  obtain ⟨spare, distinct, vacant⟩ := redraw.requires_second_vacancy bounded removal rebound
  have step := (source.step cut (by omega)).1
  rw [removal] at step
  rw [step.2] at vacant
  exact full spare (by simpa [OrchestrationSorting.Command.apply, erase, distinct] using vacant)

theorem redraw_for_exchange_of_child_redraw {trace : Trace program last} {old spare parent : Name}
    {birth stop : Nat} {kind : Lifecycle} (redraw : ChildRedraw trace old spare birth stop kind parent) :
    RedrawForExchange trace old birth kind parent := by
  obtain ⟨moved, commands, events, _, earlier, _, birthEvent, vacant, parentTag, _, _, _, endpoint,
    opened, quiet, _, consistent⟩ := redraw
  exact ⟨moved, commands, events, earlier, birthEvent, vacant, parentTag, endpoint, opened, quiet, consistent⟩

/-- An assignment may replace any number of future draws. Before the
selected birth it keeps every event's actor, and at the birth it leaves
the old draw unused. -/
theorem redraw_for_exchange_of_assignment (trace : Trace program last)
    (opened : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    (stable : ChildContinuations program) (assign : Nat → Name) (legal : BirthNameAssignment trace assign)
    {birth : Nat} {old parent : Name} {kind : Lifecycle}
    (born : GuardedBirthMatching.BornAt trace old birth)
    (birthEvent : trace.event (birth - 1) = .lifecycle kind parent)
    (fixed : ∀ time tag, time ≤ birth - 1 → (trace.notes time).1 (trace.actor time) = some tag →
      assign tag = trace.actor time)
    (vacancy : ∀ name tag, (trace.notes birth).1 name = some tag → assign tag ≠ old) :
    RedrawForExchange trace old birth kind parent := by
  obtain ⟨moved, names, labels, cuts, keeps, roots, assigned, movedOpen, movedQuiet, commands, events⟩ :=
    replay_with_birth_assignment trace opened quiet stable assign legal
  have actorFixed (time : Nat) (bounded : time < last) (before : time ≤ birth - 1)
      (present : trace.state time (trace.actor time) ≠ none) :
      (names time).toFun (trace.actor time) = trace.actor time := by
    cases tag : (trace.notes time).1 (trace.actor time) with
    | none => exact False.elim (present ((trace.births_agree time (Nat.le_of_lt bounded) _).mp tag))
    | some index => exact (assigned time (Nat.le_of_lt bounded) _ index tag).trans (fixed time index before tag)
  have literal (time : Nat) (bounded : time < last) (before : time ≤ birth - 1) :
      moved.event time = trace.event time := by
    rw [labels time bounded]
    cases event : trace.event time with
    | command command =>
      cases command with
      | insert name component => simp [GuardedRenaming.event, GuardedRenaming.command, roots time name component bounded event]
      | retire name | remove name =>
        have actor : trace.actor time = name := by
          simp [Trace.actor, event, Vestigial.eventActor, OrchestrationSorting.Command.actor]
        have step := (trace.step time bounded).1
        rw [event] at step
        have present : trace.state time name ≠ none := by
          all_goals
            first
            | exact step.1
            | intro missing; have ready : Removable (trace.state time) name := step.1; simp [Removable, missing] at ready
        have stays := actorFixed time bounded before (actor.symm ▸ present)
        rw [actor] at stays
        simp [GuardedRenaming.event, GuardedRenaming.command, stays]
    | lifecycle stepKind name =>
      obtain ⟨active, step⟩ := trace.activation_at opened quiet bounded event
      obtain ⟨row, _, found, _, _⟩ := Transposition.activation_source program step active
      have actor : trace.actor time = name := by simp [Trace.actor, event, Vestigial.eventActor]
      have stays := actorFixed time bounded before (by simp [actor, found])
      rw [actor] at stays
      simp [GuardedRenaming.event, stays]
  have bornBound := born.2.1
  have landing : birth - 1 < last := by have := born.1; omega
  have parentFixed : (names (birth - 1)).toFun parent = parent := by
    obtain ⟨active, step⟩ := trace.activation_at opened quiet landing birthEvent
    obtain ⟨row, _, present, _, _⟩ := Transposition.activation_source program step active
    have actor : trace.actor (birth - 1) = parent := by simp [Trace.actor, birthEvent, Vestigial.eventActor]
    have stays := actorFixed _ landing (Nat.le_refl _) (by simp [actor, present])
    simpa only [actor] using stays
  have vacant : moved.state birth old = none := by
    let source := (names birth).invFun old
    have toOld : (names birth).toFun source = old := (names birth).right_inv old
    cases tag : (trace.notes birth).1 source with
    | none =>
      have missing := ((cuts birth bornBound).2 source).trans tag
      rw [toOld] at missing
      exact (moved.births_agree birth bornBound old).mp missing
    | some index => exact False.elim (vacancy source index tag ((assigned birth bornBound source index tag).symm.trans toOld))
  have order (time : Nat) (bounded : time < last) : addressedEventAt moved time = addressedEventAt trace time :=
    addressed_event_of_consistent_names trace moved names labels cuts keeps bounded
  refine ⟨moved, commands, order, fun time prior => literal time (by omega) (by omega),
    (literal _ landing (Nat.le_refl _)).trans birthEvent, vacant, ?_, ?_, movedOpen, movedQuiet,
    ⟨names, labels, cuts, keeps, roots⟩⟩
  · simpa only [parentFixed] using (cuts _ (Nat.le_of_lt landing)).2 parent
  · apply match_open_prefix trace moved stable last (Nat.le_refl _) (Nat.le_refl _)
    intro time bounded
    exact match_addressed_event trace moved bounded bounded
      (fun event => (trace.activation_at opened quiet bounded event).1)
      (fun event => (moved.activation_at movedOpen movedQuiet bounded event).1)
      (fun cut earlier => (order cut (by omega)).symm) (order time bounded).symm

/-- The name assignment constraints for one removal/birth exchange.
Only actual birth stamps and existing prefix actors affect the test. -/
def AssignmentForExchange (trace : Trace program last) (old : Name) (birth : Nat) : Prop :=
  ∃ assign : Nat → Name, BirthNameAssignment trace assign ∧
    (∀ time tag, time ≤ birth - 1 → (trace.notes time).1 (trace.actor time) = some tag →
      assign tag = trace.actor time) ∧
    (∀ name tag, (trace.notes birth).1 name = some tag → assign tag ≠ old)

/-- Finite assignment validation for concrete histories. The pool names
cover the original name set and are also the possible assigned names. -/
def checkExchangeAssignment (trace : Trace program last) (pool : List Name)
    (old : Name) (birth : Nat) (assign : Nat → Name) : Bool :=
  ((List.range (last + 1)).all fun cut =>
    pool.all fun left => pool.all fun right =>
      match eventBirth trace cut left, eventBirth trace cut right with
      | some a, some b => decide (assign a ≠ assign b ∨ left = right)
      | _, _ => true) &&
  ((List.range last).all fun cut =>
    match trace.event cut with
    | .command (.insert name _) => decide (assign (cut + 1) = name)
    | _ => true) &&
  ((List.range birth).all fun time =>
    match (trace.notes time).1 (trace.actor time) with
    | some tag => decide (assign tag = trace.actor time)
    | none => true) &&
  (pool.all fun name =>
    match (trace.notes birth).1 name with
    | some tag => decide (assign tag ≠ old)
    | none => true)

theorem checkExchangeAssignment_iff (trace : Trace program last) (pool : List Name)
    (covers : ∀ name, name ∈ pool) (old : Name) {birth : Nat} (positive : 0 < birth)
    (assign : Nat → Name) :
    checkExchangeAssignment trace pool old birth assign = true ↔
      BirthNameAssignment trace assign ∧
      (∀ time tag, time ≤ birth - 1 → (trace.notes time).1 (trace.actor time) = some tag →
        assign tag = trace.actor time) ∧
      (∀ name tag, (trace.notes birth).1 name = some tag → assign tag ≠ old) := by
  simp only [checkExchangeAssignment, Bool.and_eq_true, List.all_eq_true]
  constructor
  · rintro ⟨⟨⟨collision, roots⟩, earlier⟩, vacant⟩
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · intro cut bounded left right a b first second same
      have checked := collision cut (List.mem_range.mpr (by omega)) left (covers left) right (covers right)
      simpa [first, second, same] using checked
    · intro cut name component bounded event
      simpa [event] using roots cut (List.mem_range.mpr bounded)
    · intro time tag before found
      simpa [found] using earlier time (List.mem_range.mpr (by omega))
    · intro name tag found
      simpa [found] using vacant name (covers name)
  · rintro ⟨⟨collision, roots⟩, earlier, vacant⟩
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · intro cut inside left _ right _
      have bounded := List.mem_range.mp inside
      cases first : eventBirth trace cut left <;> cases second : eventBirth trace cut right <;> simp
      rename_i a b
      by_cases same : assign a = assign b
      · exact .inr (collision cut (by omega) first second same)
      · exact .inl same
    · intro cut bounded
      cases event : trace.event cut with
      | lifecycle => rfl
      | command command =>
        cases command with
        | insert name component => simpa using roots cut name component (List.mem_range.mp bounded) event
        | retire | remove => rfl
    · intro time before
      have inside := List.mem_range.mp before
      cases stamp : (trace.notes time).1 (trace.actor time) with
      | none => rfl
      | some tag => simpa using earlier time tag (by omega) stamp
    · intro name _
      cases stamp : (trace.notes birth).1 name with
      | none => rfl
      | some tag => simpa using vacant name tag stamp

private def assignmentCandidates (pool : List Name) (fallback : Name) : Nat → List (Nat → Name)
  | 0 => [fun _ => fallback]
  | slots + 1 => pool.flatMap fun head =>
    (assignmentCandidates pool fallback slots).map fun tail => fun
      | 0 => head
      | index + 1 => tail index

private theorem assignmentCandidates_cover (pool : List Name) (covers : ∀ name, name ∈ pool)
    (fallback : Name) (slots : Nat) (assign : Nat → Name) :
    ∃ candidate ∈ assignmentCandidates pool fallback slots,
      ∀ index, index < slots → candidate index = assign index := by
  induction slots generalizing assign with
  | zero => exact ⟨fun _ => fallback, by simp [assignmentCandidates], fun _ impossible => by omega⟩
  | succ slots ih =>
    obtain ⟨tail, listed, agrees⟩ := ih (fun index => assign (index + 1))
    let candidate : Nat → Name
      | 0 => assign 0
      | index + 1 => tail index
    refine ⟨candidate, List.mem_flatMap.mpr ⟨assign 0, covers _, List.mem_map.mpr ⟨tail, listed, rfl⟩⟩, ?_⟩
    intro index inside
    cases index with
    | zero => rfl
    | succ index => exact agrees index (by omega)

/-- Exhaustive search over the bounded birth stamps of a finite history. -/
def findExchangeAssignment (trace : Trace program last) (pool : List Name) (old : Name) (birth : Nat) :
    Option (Nat → Name) :=
  (assignmentCandidates pool old (last + 1)).find? (checkExchangeAssignment trace pool old birth)

private theorem eventBirth_bounded (trace : Trace program last) {time tag : Nat} {name : Name}
    (bounded : time ≤ last) (found : eventBirth trace time name = some tag) : tag ≤ last := by
  unfold eventBirth at found
  cases prior : (trace.notes time).1 name with
  | none =>
    have stamp : (trace.notes (min (time + 1) last)).1 name = some tag := by simpa [prior] using found
    exact Nat.le_trans (GuardedBirthMatching.recorded_birth trace (Nat.min_le_right _ _) stamp).2
      (Nat.min_le_right _ _)
  | some stamp =>
    have tagEq : stamp = tag := Option.some.inj (by simpa [prior] using found)
    exact tagEq ▸ Nat.le_trans (GuardedBirthMatching.recorded_birth trace bounded prior).2 bounded

theorem findExchangeAssignment_sound (trace : Trace program last) (pool : List Name)
    (covers : ∀ name, name ∈ pool) (old : Name) {birth : Nat} (positive : 0 < birth)
    {assign : Nat → Name} (found : findExchangeAssignment trace pool old birth = some assign) :
    BirthNameAssignment trace assign ∧
      (∀ time tag, time ≤ birth - 1 → (trace.notes time).1 (trace.actor time) = some tag →
        assign tag = trace.actor time) ∧
      (∀ name tag, (trace.notes birth).1 name = some tag → assign tag ≠ old) :=
  (checkExchangeAssignment_iff trace pool covers old positive assign).mp (List.find?_some found)

theorem findExchangeAssignment_iff (trace : Trace program last) (pool : List Name)
    (covers : ∀ name, name ∈ pool) (old : Name) {birth : Nat} (positive : 0 < birth) (bounded : birth ≤ last) :
    (findExchangeAssignment trace pool old birth).isSome = true ↔ AssignmentForExchange trace old birth := by
  constructor
  · intro found
    cases result : findExchangeAssignment trace pool old birth with
    | none => simp [result] at found
    | some assign => exact ⟨assign, findExchangeAssignment_sound trace pool covers old positive result⟩
  · rintro ⟨assign, legal, fixed, vacant⟩
    obtain ⟨candidate, member, agrees⟩ := assignmentCandidates_cover pool covers old (last + 1) assign
    apply List.find?_isSome.mpr
    refine ⟨candidate, member, (checkExchangeAssignment_iff trace pool covers old positive candidate).mpr ?_⟩
    have agreesAt (tag : Nat) (inside : tag ≤ last) := agrees tag (by omega)
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · intro cut range left right a b first second same
      rw [agreesAt a (eventBirth_bounded trace range first), agreesAt b (eventBirth_bounded trace range second)] at same
      exact legal.1 cut range first second same
    · intro cut name component range event
      rw [agreesAt _ (by omega)]
      exact legal.2 cut name component range event
    · intro time tag range found
      have within : time ≤ last := by omega
      rw [agreesAt _ (Nat.le_trans (GuardedBirthMatching.recorded_birth trace within found).2 within)]
      exact fixed time tag range found
    · intro name tag found
      rw [agreesAt _ (Nat.le_trans (GuardedBirthMatching.recorded_birth trace bounded found).2 bounded)]
      exact vacant name tag found

/-- The assignment condition exactly characterizes the consistent redraws
that preserve the prefix needed by the adjacent exchange. -/
theorem redraw_for_exchange_iff_assignment (trace : Trace program last)
    (opened : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    (stable : ChildContinuations program)
    {birth : Nat} {old parent : Name} {kind : Lifecycle}
    (born : GuardedBirthMatching.BornAt trace old birth)
    (birthEvent : trace.event (birth - 1) = .lifecycle kind parent) :
    RedrawForExchange trace old birth kind parent ↔ AssignmentForExchange trace old birth := by
  constructor
  · rintro ⟨moved, _, _, earlier, landing, vacant, _, _, _, _, names, labels, cuts, keeps, roots⟩
    obtain ⟨assign, legal, represented⟩ := birth_assignment_of_consistent_names trace names old keeps
      (fun bounded event => roots _ _ _ bounded event)
    refine ⟨assign, legal, ?_, ?_⟩
    · intro time tag before present
      have bounded : time < last := by have := born.1; have := born.2.1; omega
      have literal : moved.event time = trace.event time := by
        rcases Nat.eq_or_lt_of_le before with equal | prior
        · rw [equal, landing, birthEvent]
        · exact earlier time prior
      have fixed := congrArg Vestigial.eventActor ((labels time bounded).symm.trans literal)
      rw [GuardedRenaming.actor_event] at fixed
      exact (represented time (Nat.le_of_lt bounded) (trace.actor time) tag
        (by simp [eventBirth, present])).symm.trans fixed
    · intro name tag present same
      have mapped := represented birth born.2.1 name tag (by simp [eventBirth, present])
      have located := ((cuts birth born.2.1).2 name).trans present
      rw [mapped, same, (moved.births_agree birth born.2.1 old).mpr vacant] at located
      cases located
  · rintro ⟨assign, legal, fixed, vacant⟩
    exact redraw_for_exchange_of_assignment trace opened quiet stable assign legal born birthEvent fixed vacant

/-- For a finite name set, the search decides whether the selected
exchange has a consistent prefix-preserving redraw. -/
theorem findExchangeAssignment_iff_redraw (trace : Trace program last) (pool : List Name)
    (covers : ∀ name, name ∈ pool)
    (opened : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    (stable : ChildContinuations program)
    {birth : Nat} {old parent : Name} {kind : Lifecycle}
    (born : GuardedBirthMatching.BornAt trace old birth)
    (birthEvent : trace.event (birth - 1) = .lifecycle kind parent) :
    (findExchangeAssignment trace pool old birth).isSome = true ↔ RedrawForExchange trace old birth kind parent :=
  (findExchangeAssignment_iff trace pool covers old born.1 born.2.1).trans
    (redraw_for_exchange_iff_assignment trace opened quiet stable born birthEvent).symm

/-- A fixed external insertion pins its live name until the first cut at
which the row is absent. -/
private theorem redraw_fixes_resident_root {source : Trace program last} {names : Nat → P}
    (keeps : ∀ time, time < last → ∀ name, source.state (time + 1) name ≠ none →
      (names time).toFun name = (names (time + 1)).toFun name)
    {inserted cut : Nat} {name : Name} (ordered : inserted ≤ cut) (bounded : cut ≤ last)
    (fixed : (names inserted).toFun name = name)
    (resident : ∀ time, inserted < time → time ≤ cut → source.state time name ≠ none) :
    (names cut).toFun name = name := by
  induction cut with
  | zero =>
    obtain rfl : inserted = 0 := by omega
    exact fixed
  | succ time ih =>
    rcases Nat.eq_or_lt_of_le ordered with same | earlier
    · exact same ▸ fixed
    · exact (keeps time (by omega) name (resident _ earlier (Nat.le_refl _))).symm.trans
        (ih (by omega) (by omega) (fun i lower upper => resident i lower (by omega)))

/-- If every other name belongs to an uninterrupted external insertion
at the replacement birth, that birth cannot be redrawn in this name set. -/
theorem no_child_redraw_when_other_names_pinned (source : Trace program last)
    {old spare parent : Name} {birth final : Nat} {kind : Lifecycle}
    (bounded : birth ≤ last)
    (tag : (source.notes birth).1 old = some birth)
    (pinned : ∀ name, name ≠ old → ∃ inserted component,
      inserted < birth ∧ source.event inserted = .command (.insert name component) ∧
      ∀ time, inserted < time → time ≤ birth → source.state time name ≠ none) :
    ¬ ChildRedraw source old spare birth final kind parent := by
  rintro ⟨moved, _, _, _, _, _, _, vacant, _, _, spareTag, _, _, _, _, _,
    names, _, cuts, keeps, insertions⟩
  have movedTag : (moved.notes birth).1 ((names birth).toFun old) = some birth :=
    ((cuts birth bounded).2 old).trans tag
  have renamed := GuardedBirthMatching.live_stamp_unique moved bounded movedTag spareTag
  have different : spare ≠ old := by
    intro same
    have atSpare := (GuardedBirthMatching.recorded_birth moved bounded spareTag).1
    exact atSpare.2.2.2 (same.symm ▸ vacant)
  obtain ⟨inserted, component, earlier, event, resident⟩ := pinned spare different
  have fixed : (names birth).toFun spare = spare :=
    redraw_fixes_resident_root keeps (Nat.le_of_lt earlier) bounded
      (insertions inserted spare component (by omega) event) resident
  exact different ((names birth).injective (fixed.trans renamed.symm))

theorem no_exchange_redraw_when_other_names_pinned (source : Trace program last)
    {old parent : Name} {birth : Nat} {kind : Lifecycle}
    (bounded : birth ≤ last) (tag : (source.notes birth).1 old = some birth)
    (pinned : ∀ name, name ≠ old → ∃ inserted component,
      inserted < birth ∧ source.event inserted = .command (.insert name component) ∧
      ∀ time, inserted < time → time ≤ birth → source.state time name ≠ none) :
    ¬ RedrawForExchange source old birth kind parent := by
  rintro ⟨moved, _, _, _, _, vacant, _, _, _, _, names, _, cuts, keeps, insertions⟩
  let target := (names birth).toFun old
  have live : (moved.notes birth).1 target = some birth := ((cuts birth bounded).2 old).trans tag
  have different : target ≠ old := by
    intro same
    have absent := (moved.births_agree birth bounded old).mpr vacant
    rw [same, absent] at live
    cases live
  obtain ⟨inserted, component, earlier, event, resident⟩ := pinned target different
  have fixed := redraw_fixes_resident_root keeps (Nat.le_of_lt earlier) bounded
    (insertions inserted target component (by omega) event) resident
  exact different ((names birth).injective fixed)

/-- Keep a swap in force beyond the particular child's lifetime if
both names cannot be restored at its removal. The swap may end at any
later double vacancy, or stay in force through the endpoint. -/
theorem redraw_child_with_swap_interval (trace : Trace program last)
    (openOnly : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    (stable : ChildContinuations program)
    {old fresh : Name} {birth final stop : Nat} (life : Lifetime trace old birth final) (born : 0 < birth)
    (through : final ≤ stop) (stopBound : stop ≤ last)
    {kind : Lifecycle} {parent : Name} (birthEvent : trace.event (birth - 1) = .lifecycle kind parent)
    (different : old ≠ fresh)
    (freshBefore : trace.state (birth - 1) fresh = none)
    (oldAfter : stop < last → trace.state (stop + 1) old = none)
    (freshAfter : stop < last → trace.state (stop + 1) fresh = none)
    (noInsertion : ∀ i name component, birth - 1 ≤ i → i ≤ stop → i < last →
      trace.event i = .command (.insert name component) → name ≠ old ∧ name ≠ fresh) : ChildRedraw trace old fresh birth stop kind parent := by
  let names := lifetimeNames old fresh birth stop
  have oldBefore := life.resident.boundary.resolve_left (by omega : birth ≠ 0)
  have keeps := lifetimeNames_consistent trace oldBefore oldAfter freshBefore freshAfter
  have birthBeforeStop := Nat.le_trans life.resident.ordered through
  have rootInsertions {time name component} (bounded : time < last)
      (event : trace.event time = .command (.insert name component)) : (names time).toFun name = name := by
    by_cases within : birth - 1 ≤ time ∧ time ≤ stop
    · obtain ⟨oldName, freshName⟩ := noInsertion time name component within.1 within.2 bounded event
      simpa only [names, lifetimeNames, if_pos within] using (swap_other oldName freshName)
    · exact fixed_outside within name
  obtain ⟨moved, labels, cuts, opened, settled⟩ := replay_with_consistent_names trace openOnly quiet stable names keeps
  have input := command_input_of_consistent_names trace moved names labels cuts keeps rootInsertions
  have ordered (time : Nat) (within : time < last) : addressedEventAt moved time = addressedEventAt trace time :=
    addressed_event_of_consistent_names trace moved names labels cuts keeps within
  have literal (time : Nat) (within : time < last) (outside : ¬ (birth - 1 ≤ time ∧ time ≤ stop)) :
      moved.event time = trace.event time := by
    rw [labels time within]
    have fixed (name : Name) : (names time).toFun name = name := fixed_outside outside name
    cases event : trace.event time with
    | lifecycle => simp [GuardedRenaming.event, fixed]
    | command cmd => cases cmd <;> simp [GuardedRenaming.event, GuardedRenaming.command, fixed]
  have under : birth ≤ last := Nat.le_trans life.resident.ordered life.bounded
  have before : birth - 1 < last := by omega
  have sourceTag : (trace.notes birth).1 old = some birth := by
    rw [trace.notes_eq birth under]
    exact birthAt_eq_some.mpr (life.resident.prefix birth (Nat.le_refl _) life.resident.ordered)
  have switched (time : Nat) (lower : birth - 1 ≤ time) (upper : time ≤ stop) : (names time).toFun old = fresh := by
    change (lifetimeNames old fresh birth stop time).toFun old = fresh
    rw [lifetimeNames, if_pos ⟨lower, upper⟩]
    exact swap_first _ _
  have switchedBack (time : Nat) (lower : birth - 1 ≤ time) (upper : time ≤ stop) : (names time).toFun fresh = old := by
    change (lifetimeNames old fresh birth stop time).toFun fresh = old
    rw [lifetimeNames, if_pos ⟨lower, upper⟩]
    simp [swap, different.symm]
  have atBirth := (cuts birth under).2 old
  rw [switched birth (by omega) birthBeforeStop, sourceTag] at atBirth
  have newBorn := (GuardedBirthMatching.recorded_birth moved under atBirth).1
  have parentFixed : (names (birth - 1)).toFun parent = parent := by
    obtain ⟨active, step⟩ := trace.activation_at openOnly quiet before birthEvent
    obtain ⟨row, _, found, _, _⟩ := Transposition.activation_source program step active
    have oldVacant := life.resident.boundary.resolve_left (by omega : birth ≠ 0)
    have notOld : parent ≠ old := by intro same; rw [same, oldVacant] at found; cases found
    have notFresh : parent ≠ fresh := by intro same; rw [same, freshBefore] at found; cases found
    change (lifetimeNames old fresh birth stop (birth - 1)).toFun parent = parent
    rw [lifetimeNames, if_pos ⟨Nat.le_refl _, by omega⟩]
    exact swap_other notOld notFresh
  have event : moved.event (birth - 1) = .lifecycle kind parent := by
    rw [labels _ before, birthEvent]
    simp only [GuardedRenaming.event, parentFixed]
  have rawNameVacant : moved.state birth old = none := by
    have spareAtBirth : trace.state birth fresh = none := by
      apply Classical.byContradiction
      intro present
      have oldBorn := (GuardedBirthMatching.recorded_birth trace under sourceTag).1
      exact different (GuardedBirthMatching.born_unique trace oldBorn ⟨born, under, freshBefore, present⟩)
    have reversed := switchedBack birth (by omega) birthBeforeStop
    rw [← project_present (moved.state birth), ← (cuts birth under).1, ← reversed, Renaming.registry_at]
    simp [project, spareAtBirth]
  have stage : EpisodeSelection.canBirth (moved.rule (birth - 1)) = true := by
    obtain ⟨active, step⟩ := moved.activation_at opened settled before event
    have existsAfter : moved.state (birth - 1 + 1) fresh ≠ none := by
      rw [show birth - 1 + 1 = birth by omega]
      exact newBorn.2.2.2
    change EpisodeSelection.canBirth (eventRule (moved.event (birth - 1))) = true
    rw [event]
    cases kind with
    | iter | finish => rfl
    | begin =>
      generalize ending : moved.state (birth - 1 + 1) = after at step existsAfter
      cases step with
      | begin _ _ _ _ _ _ _ _ =>
        exact False.elim (existsAfter ((Transposition.mark_presence _ _ _ _).mpr newBorn.2.2.1))
    | unload | divert | leave => simp [Transposition.Activation, Lifecycle.rule] at active
  have captured := (moved.actual_child_birth before stage newBorn.2.2.1 (by
    rw [show birth - 1 + 1 = birth by omega]; exact newBorn.2.2.2)).2
  rw [show birth - 1 + 1 = birth by omega] at captured
  have laterBirths (time : Nat) (later : stop < time) (bounded : time ≤ last) :
      (moved.notes time).1 = (trace.notes time).1 := by
    funext name
    have fixed : (names time).toFun name = name := fixed_outside (by omega) name
    simpa only [fixed] using (cuts time bounded).2 name
  refine ⟨moved, input, ordered, fun time later within => literal time within (by omega),
    fun time earlier => literal time (by omega) (by omega), laterBirths, event, rawNameVacant,
    by simpa only [parentFixed] using (cuts _ (Nat.le_of_lt before)).2 parent,
    newBorn, atBirth, captured, ?_, opened, settled, ?_,
    ⟨names, labels, cuts, keeps, fun _ _ _ => rootInsertions⟩⟩
  · apply match_open_prefix trace moved stable last (Nat.le_refl _) (Nat.le_refl _)
    intro time within
    exact match_addressed_event trace moved within within
      (fun event => (trace.activation_at openOnly quiet within event).1)
      (fun event => (moved.activation_at opened settled within event).1)
      (fun cut earlier => (ordered cut (by omega)).symm) (ordered time within).symm
  · intro cut lower upper
    have tags := (cuts cut (Nat.le_trans upper stopBound)).2
    exact ⟨by rw [← switched cut lower upper]; exact tags old,
      by rw [← switchedBack cut lower upper]; exact tags fresh⟩

/-- A vacancy before the removal can be used until both swapped names
are vacant again. A root insertion at either name is allowed after that
restoration cut, and insertions at other names are allowed throughout. -/
theorem redraw_for_exchange_before_restoration (trace : Trace program last)
    (openOnly : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    (stable : ChildContinuations program)
    {cut final stop : Nat} {old spare parent : Name} {kind : Lifecycle}
    (removal : trace.event cut = .command (.remove old))
    (birthEvent : trace.event (cut + 1) = .lifecycle kind parent)
    (life : Lifetime trace old (cut + 2) final)
    (through : final ≤ stop) (stopBound : stop ≤ last)
    (vacant : trace.state cut spare = none)
    (oldAfter : stop < last → trace.state (stop + 1) old = none)
    (spareAfter : stop < last → trace.state (stop + 1) spare = none)
    (noInsertion : ∀ i name component, cut < i → i ≤ stop → i < last →
      trace.event i = .command (.insert name component) → name ≠ old ∧ name ≠ spare) :
    RedrawForExchange trace old (cut + 2) kind parent := by
  have lower := life.resident.ordered
  have step := (trace.step cut (by omega)).1
  rw [removal] at step
  have distinct : old ≠ spare := by
    rintro rfl
    have removable : Removable (trace.state cut) old := step.1
    simp [Removable, vacant] at removable
  have after : trace.state (cut + 1) spare = none := by
    rw [step.2]
    simpa [OrchestrationSorting.Command.apply, erase, Ne.symm distinct] using vacant
  refine redraw_for_exchange_of_child_redraw (redraw_child_with_swap_interval
    trace openOnly quiet stable life (by omega) through stopBound
    ?_ distinct ?_ oldAfter spareAfter ?_)
  · simpa only [Nat.add_sub_cancel] using birthEvent
  · simpa only [Nat.add_sub_cancel] using after
  · intro i name component earlier within inside event
    exact noInsertion i name component (by omega) within inside event

/-- Once root insertions can no longer pin the swapped names, a reuse
barrier admits a consistent redraw exactly when the pre-removal cut has
a vacancy. The swap can stay in force through the end of the history. -/
theorem redraw_for_exchange_iff_vacancy_without_later_insertions
    (trace : Trace program last)
    (openOnly : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    (stable : ChildContinuations program)
    {cut final : Nat} {old parent : Name} {kind : Lifecycle}
    (removal : trace.event cut = .command (.remove old))
    (birthEvent : trace.event (cut + 1) = .lifecycle kind parent)
    (life : Lifetime trace old (cut + 2) final)
    (noInsertion : ∀ i name component, cut < i → i < last →
      trace.event i ≠ .command (.insert name component)) :
    RedrawForExchange trace old (cut + 2) kind parent ↔
      ∃ spare, trace.state cut spare = none := by
  have upper := life.bounded
  have lower := life.resident.ordered
  have bounded : cut + 1 < last := by omega
  have step := (trace.step cut (by omega)).1
  rw [removal] at step
  constructor
  · intro redraw
    have rebound := life.resident.present (cut + 2) (Nat.le_refl _) lower
    obtain ⟨spare, different, vacant⟩ := redraw.requires_second_vacancy bounded removal rebound
    refine ⟨spare, ?_⟩
    rw [step.2] at vacant
    simpa [OrchestrationSorting.Command.apply, erase, different] using vacant
  · rintro ⟨spare, vacant⟩
    exact redraw_for_exchange_before_restoration trace openOnly quiet stable removal birthEvent life
      upper (Nat.le_refl _) vacant (fun impossible => (Nat.lt_irrefl _ impossible).elim)
      (fun impossible => (Nat.lt_irrefl _ impossible).elim)
      (fun i name component earlier _ inside event => (noInsertion i name component earlier inside event).elim)

/-- Swap two names for the actual lifetime of a child. Both names must
be vacant at the cuts where the permutation changes, and the swap must
fix every root insertion. The other name can be drawn by another child
inside the interval. -/
theorem redraw_child_incarnation_with_reuse (trace : Trace program last)
    (openOnly : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    (stable : ChildContinuations program)
    {old fresh : Name} {birth final : Nat} (life : Lifetime trace old birth final) (born : 0 < birth)
    {kind : Lifecycle} {parent : Name} (birthEvent : trace.event (birth - 1) = .lifecycle kind parent)
    (different : old ≠ fresh)
    (freshBefore : trace.state (birth - 1) fresh = none)
    (freshAfter : final < last → trace.state (final + 1) fresh = none)
    (noInsertion : ∀ cut component, birth - 1 ≤ cut → cut ≤ final → cut < last →
      trace.event cut ≠ .command (.insert fresh component)) : ChildRedraw trace old fresh birth final kind parent := by
  apply redraw_child_with_swap_interval trace openOnly quiet stable life born (Nat.le_refl _) life.bounded
    birthEvent different freshBefore life.gone freshAfter
  intro time name component earlier later bounded event
  refine ⟨?_, fun equal => noInsertion time component earlier later bounded (equal ▸ event)⟩
  intro same
  have notBirth : time ≠ birth - 1 := by
    intro equal
    rw [equal, birthEvent] at event
    cases event
  have step := (trace.step time bounded).1
  rw [event] at step
  exact life.resident.present time (by omega) later (same ▸ step.1.1)

/-- The vacant-lifetime case is a special case of the guarded name swap. -/
theorem redraw_child_incarnation (trace : Trace program last)
    (openOnly : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    (stable : ChildContinuations program)
    {old fresh : Name} {birth final : Nat} (life : Lifetime trace old birth final) (born : 0 < birth)
    {kind : Lifecycle} {parent : Name} (birthEvent : trace.event (birth - 1) = .lifecycle kind parent)
    (spare : ∀ cut, birth - 1 ≤ cut → cut ≤ final + 1 → cut ≤ last → trace.state cut fresh = none) :
    ChildRedraw trace old fresh birth final kind parent :=
  redraw_child_incarnation_with_reuse trace openOnly quiet stable life born birthEvent
    (fun same => life.resident.present birth (Nat.le_refl _) life.resident.ordered (by
      rw [same]
      have := life.resident.ordered
      have := life.bounded
      exact spare birth (by omega) (by omega) (by omega)))
    (by
      have := life.resident.ordered
      have := life.bounded
      exact spare (birth - 1) (by omega) (by omega) (by omega))
    (fun inside => by
      have := life.resident.ordered
      exact spare (final + 1) (by omega) (Nat.le_refl _) (by omega))
    (fun cut component first final bounded event => by
      have step := (trace.step cut bounded).1
      rw [event] at step
      have absent := spare (cut + 1) (by omega) (by omega) (by omega)
      have present : trace.state (cut + 1) fresh = some (Calculus.fresh component none) := by
        rw [step.2]
        exact put_self _ _ _
      rw [present] at absent
      cases absent)

section Typed
open PaperEffectEquations (CoeffectOperations ValueOperationWitness)
open PaperObservationEquations (OperationRespects)
open PartialCoeffectIndependenceContracts (tableSetoid)
open TypedRegistry (encodeProgram Scalar)
variable {V : Key → Type u} {ops : CoeffectOperations V}
variable {typedProgram : Code → TypedRegistry.Instruction Name ops Code}

/-- Cross the actual removal once a legal redraw has moved its replacement
to another name. The redraw may come from a vacant lifetime or a swap
between locally reused names. -/
theorem cross_reuse_with_local_redraw {leftLength rightLength start cut : Nat}
    (left : Trace (encodeProgram typedProgram) leftLength) (right : Trace (encodeProgram typedProgram) rightLength)
    (leftBound : start < leftLength) (rightBound : cut + 1 < rightLength) (order : start ≤ cut)
    (leftOpen : ¬ Nonempty (ClosedEpisode left)) (leftQuiet : Progress.Quiet (left.state leftLength))
    (stable : ChildContinuations (encodeProgram typedProgram))
    (past : ∀ time, time < start → addressedEventAt left time = addressedEventAt right time)
    (input : orchestrationInput left = orchestrationInput right)
    {leftKind rightKind : Lifecycle} {actor other old : Name} (first : left.event start = .lifecycle leftKind actor)
    (removal : right.event cut = .command (.remove old))
    (rebound : right.state (cut + 2) old ≠ none)
    (sameActorBirth : (left.notes start).1 actor = (right.notes (cut + 1)).1 other)
    (earliest : ∀ time, start ≤ time → time < cut + 1 → ∀ k, right.event time ≠ .lifecycle k other)
    (redraw : ∀ final, Lifetime right old (cut + 2) final →
      RedrawForExchange right old (cut + 2) rightKind other)
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r) :
    letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
    ∃ (redrawn moved : Trace (encodeProgram typedProgram) rightLength),
      CutAgreement right redrawn rightLength ∧ StableActorAddresses redrawn moved (ExchangeReplay.exchangedIndex cut) ∧
      orchestrationInput moved = orchestrationInput right ∧ moved.event cut = .lifecycle rightKind other ∧
      (moved.notes cut).1 other = (left.notes start).1 actor ∧
      (∀ time, time < cut → addressedEventAt moved time = addressedEventAt right time) ∧
      StageSimulation.Related Eq (redrawn.state rightLength) (moved.state rightLength) ∧
      (¬ Nonempty (ClosedEpisode moved)) ∧ Progress.Quiet (moved.state rightLength) ∧
      addressedEvents redrawn = addressedEvents right ∧
      orchestrationInput redrawn = orchestrationInput right ∧ AdjacentActivationExchange redrawn moved cut ∧
      ConsistentRedraw right redrawn := by
  have boundedRemoval : cut < rightLength := by omega
  have removed := (right.step cut boundedRemoval).1
  rw [removal] at removed
  have absent : right.state (cut + 1) old = none := by
    rw [removed.2]
    simp [OrchestrationSorting.Command.apply, erase]
  have born : GuardedBirthMatching.BornAt right old (cut + 2) :=
    ⟨by omega, by omega, by simpa only [Nat.add_sub_cancel] using absent, rebound⟩
  obtain ⟨final, life⟩ := lifetime_of_birth right born
  obtain ⟨redrawn, commands, orderEq, prefixLabels, atBirth, nowVacant, parentTag,
    endpoint, opened, settled, certificate⟩ := redraw final life
  have label : redrawn.event (cut + 1) = .lifecycle rightKind other := by simpa only [Nat.add_sub_cancel] using atBirth
  have reservedName : redrawn.state (cut + 2) old = none := nowVacant
  have oldRemoved : redrawn.event cut = .command (.remove old) :=
    (prefixLabels cut (by omega)).trans removal
  have prior (i : Nat) (before : i < start) : addressedEventAt left i = addressedEventAt redrawn i :=
    (past i before).trans (orderEq i (by omega)).symm
  have initial : CutAgreement left redrawn start := by
    apply match_open_prefix left redrawn stable start (by omega) (by omega)
    intro time within
    exact match_addressed_event left redrawn (by omega) (by omega)
      (fun event => (left.activation_at leftOpen leftQuiet (by omega) event).1)
      (fun event => (redrawn.activation_at opened settled (by omega) event).1)
      (fun i before => prior i (by omega)) (prior time within)
  obtain ⟨time, kind, act, stamp, path, lower, inside, event, leftTag, rightTag, laterTag, leftPath, rightPath,
    phase, targets, firstOccurrence⟩ := pending_activation_occurs left redrawn leftBound (by omega)
      leftOpen leftQuiet opened settled initial prior (input.trans commands.symm) first
  have otherTag : (redrawn.notes (cut + 1)).1 other = some stamp := by
    simpa only [Nat.add_sub_cancel] using parentTag.trans (sameActorBirth.symm.trans leftTag)
  have sameName := GuardedBirthMatching.born_unique redrawn
    (GuardedBirthMatching.recorded_birth redrawn (Nat.le_of_lt inside) laterTag).1
    (GuardedBirthMatching.recorded_birth redrawn (Nat.le_of_lt rightBound) otherTag).1
  subst act
  have actualTime : time = cut + 1 := by
    apply Nat.le_antisymm
    · exact Nat.le_of_not_gt (fun before => firstOccurrence (cut + 1) (by omega) before rightKind label)
    · apply Nat.le_of_not_gt
      intro before
      have original := (prefixLabels time (by omega)).symm.trans event
      exact earliest time lower before kind original
  subst time
  have sameKind := (Event.lifecycle.inj (event.symm.trans label)).1
  subst kind
  rcases move_waiting_activation_one_step_with_exchange left redrawn leftBound rightBound order leftOpen leftQuiet opened settled
    initial prior (input.trans commands.symm) first label leftTag rightTag laterTag leftPath rightPath phase firstOccurrence
    (targets cut order (by omega)).2.2 observe recovery commutative respect with
    ⟨moved, kept, fixed, _, newEvent, word, related, stillOpen, stillQuiet, exchange⟩ | ⟨wrongName, wrongRemoval, stillUsed⟩
  · have movedTag : (moved.notes cut).1 other = (left.notes start).1 actor := by
      rw [(fixed cut (Nat.le_refl _)).2, (targets cut order (by omega)).1, leftTag]
    refine ⟨redrawn, moved, endpoint, kept, word.trans commands, newEvent, movedTag, ?_, related, stillOpen, stillQuiet,
      addressedEvents_congr _ _ orderEq, commands, exchange, certificate⟩
    intro time before
    have addressed := stable_addressed_event kept (cut := time) (by omega)
    rw [ExchangeReplay.exchangedIndex_other (by omega) (by omega), Nat.add_sub_cancel] at addressed
    exact addressed.trans (orderEq time (by omega))
  · have names := OrchestrationSorting.Command.remove.inj (Event.command.inj (oldRemoved.symm.trans wrongRemoval))
    subst wrongName
    exact False.elim (stillUsed reservedName)

theorem cross_reuse_with_redraw {leftLength rightLength start cut : Nat}
    (left : Trace (encodeProgram typedProgram) leftLength) (right : Trace (encodeProgram typedProgram) rightLength)
    (leftBound : start < leftLength) (rightBound : cut + 1 < rightLength) (order : start ≤ cut)
    (leftOpen : ¬ Nonempty (ClosedEpisode left)) (leftQuiet : Progress.Quiet (left.state leftLength))
    (stable : ChildContinuations (encodeProgram typedProgram))
    (past : ∀ time, time < start → addressedEventAt left time = addressedEventAt right time)
    (input : orchestrationInput left = orchestrationInput right)
    {leftKind rightKind : Lifecycle} {actor other old spare : Name} (first : left.event start = .lifecycle leftKind actor)
    (removal : right.event cut = .command (.remove old))
    (rebound : right.state (cut + 2) old ≠ none)
    (sameActorBirth : (left.notes start).1 actor = (right.notes (cut + 1)).1 other)
    (earliest : ∀ time, start ≤ time → time < cut + 1 → ∀ k, right.event time ≠ .lifecycle k other)
    (redraw : ∀ final, Lifetime right old (cut + 2) final →
      ChildRedraw right old spare (cut + 2) final rightKind other)
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r) :
    letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
    ∃ (redrawn moved : Trace (encodeProgram typedProgram) rightLength),
      CutAgreement right redrawn rightLength ∧ StableActorAddresses redrawn moved (ExchangeReplay.exchangedIndex cut) ∧
      orchestrationInput moved = orchestrationInput right ∧ moved.event cut = .lifecycle rightKind other ∧
      (moved.notes cut).1 other = (left.notes start).1 actor ∧
      (∀ time, time < cut → addressedEventAt moved time = addressedEventAt right time) ∧
      StageSimulation.Related Eq (redrawn.state rightLength) (moved.state rightLength) ∧
      (¬ Nonempty (ClosedEpisode moved)) ∧ Progress.Quiet (moved.state rightLength) ∧
      addressedEvents redrawn = addressedEvents right := by
  letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
  obtain ⟨redrawn, moved, drawCut, kept, commands, event, stamp, earlier, related, opened, quiet, addresses, _, _, _⟩ :=
    cross_reuse_with_local_redraw left right leftBound rightBound order leftOpen leftQuiet stable past
      input first removal rebound sameActorBirth earliest (fun final life => redraw_for_exchange_of_child_redraw (redraw final life))
      observe recovery commutative respect
  exact ⟨redrawn, moved, drawCut, kept, commands, event, stamp, earlier, related, opened, quiet, addresses⟩

end Typed

private def birthSlot (rule : Labeled.Rule) : Bool :=
  decide (rule = .insert) || EpisodeSelection.canBirth rule

/-- Count only transitions whose rule can introduce a row. -/
def birthSlotsThrough (trace : Trace program last) : Nat → Nat
  | 0 => 0
  | cut + 1 => birthSlotsThrough trace cut + if birthSlot (trace.rule cut) then 1 else 0

theorem birthSlotsThrough_le (trace : Trace program last) (cut : Nat) :
    birthSlotsThrough trace cut ≤ cut := by
  induction cut with
  | zero => exact Nat.le_refl _
  | succ cut ih =>
    rw [birthSlotsThrough]
    split <;> omega

private def addressedBirthSlot : Option (AddressedEvent Key Code) → Bool
  | some (.insert _) => true
  | some (.lifecycle kind _) => EpisodeSelection.canBirth kind.rule
  | _ => false

private theorem addressed_birth_slot (trace : Trace program last) {cut : Nat} (bounded : cut < last) :
    addressedBirthSlot (addressedEventAt trace cut) = birthSlot (trace.rule cut) := by
  cases event : trace.event cut with
  | command command =>
    cases command
    · simp [addressedEventAt, addressedBirthSlot, birthSlot, Trace.rule, event, eventRule,
        ExchangeReplay.commandRule]
    all_goals
      cases tagged : actorAddress trace cut <;>
        simp [addressedEventAt, addressedBirthSlot, birthSlot, Trace.rule, event, tagged, eventRule,
          ExchangeReplay.commandRule, EpisodeSelection.canBirth]
  | lifecycle kind actor =>
    have ruleEq : trace.rule cut = kind.rule := by simp [Trace.rule, eventRule, event]
    have notInsert : kind.rule ≠ .insert := by cases kind <;> decide
    by_cases capable : EpisodeSelection.canBirth kind.rule = true
    · have native : Labeled.Step program kind.rule actor (trace.state cut) (trace.state (cut + 1)) := by
        have step := (trace.step cut bounded).1
        rw [event] at step
        cases kind <;> simp [Lifecycle.rule, EpisodeSelection.canBirth] at capable
        all_goals exact step
      have present : trace.state cut actor ≠ none := by
        generalize tag : kind.rule = rule at native capable
        generalize trace.state (cut + 1) = after at native
        cases rule <;> simp [EpisodeSelection.canBirth] at capable
        all_goals
          cases native <;> rename_i phase found guard landed <;> simp [found]
      cases recorded : (trace.notes cut).1 actor with
      | none => exact False.elim (present ((trace.births_agree cut (Nat.le_of_lt bounded) actor).mp recorded))
      | some birth =>
        obtain ⟨address, known⟩ := exists_address trace
          (GuardedBirthMatching.recorded_birth trace (Nat.le_of_lt bounded) recorded).1
        have actorEq : trace.actor cut = actor := by simp [Trace.actor, event, Vestigial.eventActor]
        have tagged : actorAddress trace cut = some address :=
          (actorAddress_eq_some trace).mpr ⟨birth, actorEq.symm ▸ recorded, known⟩
        simp [addressedEventAt, addressedBirthSlot, birthSlot, event, tagged, ruleEq, notInsert, capable]
    · cases tagged : actorAddress trace cut <;>
        simp [addressedEventAt, addressedBirthSlot, birthSlot, event, tagged, ruleEq, notInsert, capable]

theorem birth_slots_of_event_permutation (first second : Trace program last)
    (same : (addressedEvents first).Perm (addressedEvents second)) :
    birthSlotsThrough first last = birthSlotsThrough second last := by
  have count (trace : Trace program last) (cut : Nat) (bounded : cut ≤ last) :
      birthSlotsThrough trace cut = ((List.range cut).map (addressedEventAt trace)).countP addressedBirthSlot := by
    induction cut with
    | zero => rfl
    | succ cut ih =>
      rw [birthSlotsThrough, List.range_succ, List.map_append, List.countP_append, ih (by omega)]
      simp [addressed_birth_slot trace (by omega : cut < last)]
  rw [count first last (Nat.le_refl _), count second last (Nat.le_refl _)]
  exact same.countP_eq addressedBirthSlot

private theorem birth_slots_eq_filter (trace : Trace program last) (cut : Nat) :
    birthSlotsThrough trace cut = ((List.range cut).filter fun i => birthSlot (trace.rule i)).length := by
  induction cut with
  | zero => rfl
  | succ cut ih =>
    rw [birthSlotsThrough, List.range_succ, List.filter_append, List.length_append, ih]
    cases slot : birthSlot (trace.rule cut) <;> simp [slot]

private theorem length_le_of_distinct_subset {used available : List Nat} (distinct : used.Nodup)
    (includes : used ⊆ available) : used.length ≤ available.length := by
  induction used generalizing available with
  | nil => simp
  | cons head rest ih =>
    obtain ⟨separate, tailDistinct⟩ := List.nodup_cons.mp distinct
    have headMember := includes List.mem_cons_self
    have tails : rest ⊆ available.erase head := by
      intro item member
      have different : item ≠ head := fun same => separate (same ▸ member)
      exact (List.mem_erase_of_ne different).mpr (includes (List.mem_cons_of_mem _ member))
    have smaller := ih tailDistinct tails
    rw [List.length_erase_of_mem headMember] at smaller
    have nonempty : 0 < available.length := List.length_pos_of_mem headMember
    simp only [List.length_cons]
    omega

private theorem retained_event_count_le {length : Nat} {original : Trace program last} {compact : Trace program length}
    {expand : Nat → Nat} (retained : RetainedEvents original compact expand)
    (counts : Event Name Key Code → Bool) :
    ((List.range length).filter fun i => counts (compact.event i)).length ≤
      ((List.range last).filter fun i => counts (original.event i)).length := by
  let cuts := (List.range length).filter fun i => counts (compact.event i)
  let source (cut : Nat) := expand (cut + 1) - 1
  have bounded {cut : Nat} (member : cut ∈ cuts) : cut < length :=
    List.mem_range.mp (List.mem_filter.mp member).1
  have distinct : (cuts.map source).Nodup := by
    apply List.pairwise_map.mpr
    refine List.Pairwise.imp_of_mem ?_ (List.nodup_range.filter _)
    intro a b first second different equal
    obtain ⟨positiveA, _⟩ := retained.stamp a (bounded first)
    obtain ⟨positiveB, _⟩ := retained.stamp b (bounded second)
    have stamps := retained.injective (by dsimp [source] at equal; omega : expand (a + 1) = expand (b + 1))
    exact different (by omega)
  have includes : cuts.map source ⊆ (List.range last).filter (fun i => counts (original.event i)) := by
    intro i present
    obtain ⟨cut, member, rfl⟩ := List.mem_map.mp present
    have inside := bounded member
    obtain ⟨positive, upper⟩ := retained.stamp cut inside
    refine List.mem_filter.mpr ⟨List.mem_range.mpr (by dsimp [source]; omega), ?_⟩
    have same := retained.label cut inside
    exact same ▸ (List.mem_filter.mp member).2
  simpa only [List.length_map] using length_le_of_distinct_subset distinct includes

/-- Excision cannot increase the number of transitions allowed to create
a row. Each surviving occurrence has a distinct source occurrence. -/
theorem retained_birth_slots_le {length : Nat} {original : Trace program last} {compact : Trace program length}
    {expand : Nat → Nat} (retained : RetainedEvents original compact expand) :
    birthSlotsThrough compact length ≤ birthSlotsThrough original last := by
  rw [birth_slots_eq_filter, birth_slots_eq_filter]
  exact retained_event_count_le retained (birthSlot ∘ eventRule)

private theorem birth_slot_of_transition (trace : Trace program last) {cut : Nat} (bounded : cut < last)
    {name : Name} (vacant : trace.state cut name = none) (present : trace.state (cut + 1) name ≠ none) :
    birthSlot (trace.rule cut) = true := by
  rcases transition_cases (trace.step cut bounded).1 with native | ⟨actor, _, unload⟩
  · rcases EpisodeBoundary.new_entry_rule native vacant present with ⟨inserts, _⟩ | allocates
    · simp [birthSlot, show trace.rule cut = .insert from inserts]
    · simp [birthSlot, show EpisodeSelection.canBirth (trace.rule cut) = true from allocates]
  · obtain ⟨_, _, _, _, _, endpoint⟩ := unload
    exact False.elim (present (endpoint.symm ▸ (Transposition.mark_presence _ _ _ _).mpr
      ((replay_presence _ _ _ _).mpr vacant)))

/-- Each cut adds at most one new raw name to the history's finite
cover. Removals and reuse do not require extra names in the cover. -/
theorem history_name_cover_by_birth_slots (trace : Trace program last) :
    ∃ used : List Name, used.length ≤ birthSlotsThrough trace last ∧
      ∀ time, time ≤ last → ∀ name row, trace.state time name = some row → name ∈ used := by
  have coverThrough (length : Nat) (bounded : length ≤ last) :
      ∃ used : List Name, used.length ≤ birthSlotsThrough trace length ∧
        ∀ time, time ≤ length → ∀ name row, trace.state time name = some row → name ∈ used := by
    classical
    induction length with
    | zero =>
      refine ⟨[], by simp, ?_⟩
      intro time inside name row found
      obtain rfl : time = 0 := by omega
      rw [trace.start] at found
      cases found
    | succ time ih =>
      obtain ⟨old, size, cover⟩ := ih (by omega)
      by_cases birth : ∃ name, trace.state time name = none ∧ trace.state (time + 1) name ≠ none
      · obtain ⟨new, vacant, present⟩ := birth
        refine ⟨new :: old, ?_, ?_⟩
        · have capable := birth_slot_of_transition trace (by omega) vacant present
          simpa [birthSlotsThrough, capable] using Nat.succ_le_succ size
        · intro cut earlier name row found
          rcases Nat.eq_or_lt_of_le earlier with rfl | prior
          · cases before : trace.state time name with
            | some entry => exact List.mem_cons_of_mem _ (cover time (Nat.le_refl _) name entry before)
            | none =>
              have unique := GuardedBirthMatching.transition_birth (trace.step time (by omega)).1
              exact List.mem_cons.mpr (.inl (unique before (by simp [found]) vacant present))
          · exact List.mem_cons_of_mem _ (cover cut (by omega) name row found)
      · refine ⟨old, Nat.le_trans size (Nat.le_add_right _ _), ?_⟩
        intro cut earlier name row found
        rcases Nat.eq_or_lt_of_le earlier with rfl | prior
        · cases before : trace.state time name with
          | some entry => exact cover time (Nat.le_refl _) name entry before
          | none => exact False.elim (birth ⟨name, before, by simp [found]⟩)
        · exact cover cut (by omega) name row found
  exact coverThrough last (Nat.le_refl _)

theorem history_name_cover (trace : Trace program last) :
    ∃ used : List Name, used.length ≤ last ∧
      ∀ time, time ≤ last → ∀ name row, trace.state time name = some row → name ∈ used := by
  obtain ⟨used, size, cover⟩ := history_name_cover_by_birth_slots trace
  exact ⟨used, Nat.le_trans size (birthSlotsThrough_le trace last), cover⟩

/-- Domain information needed for counting names survives projected
endpoint agreement. -/
def LiveDomainRenaming (left right : R) : Prop :=
  ∃ p : P, ∀ name, right (p.toFun name) = none ↔ left name = none

omit [DecidableEq Name] [DecidableEq Key] in
theorem live_domain_of_projected_agreement [Setoid Value] {left right : R}
    (agreement : ProjectedAgreement left right) : LiveDomainRenaming left right := by
  obtain ⟨p, related⟩ := agreement
  refine ⟨p, fun name => ?_⟩
  have atName := related (p.toFun name)
  rw [Renaming.registry_at] at atName
  rw [← project_present right (p.toFun name), ← project_present left name]
  cases first : project left name <;> cases second : project right (p.toFun name) <;>
    simp_all [Iterators.OptionRel]

omit [DecidableEq Name] [DecidableEq Key] in
theorem LiveDomainRenaming.trans {left middle right : R}
    (first : LiveDomainRenaming left middle) (second : LiveDomainRenaming middle right) :
    LiveDomainRenaming left right := by
  obtain ⟨p, before⟩ := first
  obtain ⟨q, after⟩ := second
  exact ⟨⟨q.toFun ∘ p.toFun, p.invFun ∘ q.invFun,
    fun name => by simp [p.left_inv, q.left_inv],
    fun name => by simp [p.right_inv, q.right_inv]⟩,
    fun name => (after (p.toFun name)).trans (before name)⟩

omit [DecidableEq Name] [DecidableEq Key] in
theorem LiveDomainRenaming.map_cover {left right : R}
    (agreement : LiveDomainRenaming left right) (names : List Name)
    (cover : ∀ name row, left name = some row → name ∈ names) :
    ∃ renamed : List Name, renamed.length = names.length ∧
      ∀ name row, right name = some row → name ∈ renamed := by
  obtain ⟨p, same⟩ := agreement
  refine ⟨names.map p.toFun, List.length_map _, ?_⟩
  intro name row present
  let old := p.invFun name
  have corresponds : p.toFun old = name := p.right_inv name
  cases original : left old with
  | none =>
    have absent := (same old).mpr original
    rw [corresponds, present] at absent
    cases absent
  | some entry => exact List.mem_map.mpr ⟨old, cover old entry original, corresponds⟩

private def removedName (event : Event Name Key Code) : Option Name :=
  match event with
  | .command (.remove name) => some name
  | _ => none

private theorem raw_removal_count (trace : Trace program last) (cut : Nat) (bounded : cut ≤ last) :
    ((List.range cut).filterMap (fun i => removedName (trace.event i))).length =
      (releasesBefore trace cut).length := by
  induction cut with
  | zero => rfl
  | succ cut ih =>
    have same : (removedName (trace.event cut)).isSome = (removalAddress trace cut).isSome := by
      unfold removalAddress
      cases event : trace.event cut with
      | lifecycle => simp [removedName, commandAt, event]
      | command command =>
        cases command with
        | insert => simp [removedName, commandAt, event, releasedAddress]
        | retire name =>
          cases target : targetAt trace cut name <;> simp [removedName, commandAt, event, target, releasedAddress]
        | remove name =>
          obtain ⟨address, component, target⟩ := targetAt_command trace (by omega) (.inr event)
          simp [removedName, commandAt, event, target, releasedAddress]
    unfold releasesBefore at *
    rw [List.range_succ, List.filterMap_append, List.length_append,
      List.filterMap_append, List.length_append, ih (by omega)]
    cases name : removedName (trace.event cut) <;> cases address : removalAddress trace cut <;>
      simp_all
private theorem raw_removal_filter (trace : Trace program last) (cut : Nat) :
    ((List.range cut).filterMap (fun i => removedName (trace.event i))).length =
      ((List.range cut).filter fun i => (removedName (trace.event i)).isSome).length := by
  induction cut with
  | zero => rfl
  | succ cut ih =>
    rw [List.range_succ, List.filterMap_append, List.filter_append, List.length_append,
      List.length_append, ih]
    cases removed : removedName (trace.event cut) <;> simp [removed]

theorem retained_release_count_le {length : Nat} {original : Trace program last} {compact : Trace program length}
    {expand : Nat → Nat} (retained : RetainedEvents original compact expand) :
    (releasesBefore compact length).length ≤ (releasesBefore original last).length := by
  rw [← raw_removal_count compact length (Nat.le_refl _), ← raw_removal_count original last (Nat.le_refl _),
    raw_removal_filter, raw_removal_filter]
  exact retained_event_count_le retained (fun event => (removedName event).isSome)

/-- All names ever occupied are either present at the endpoint or named
by a removal. This bound counts actual incarnations rather than stage rules. -/
theorem history_name_cover_by_releases (trace : Trace program last) (liveNames : List Name)
    (liveCover : ∀ name row, trace.state last name = some row → name ∈ liveNames) :
    ∃ used : List Name, used.length = liveNames.length + (releasesBefore trace last).length ∧
      ∀ time, time ≤ last → ∀ name row, trace.state time name = some row → name ∈ used := by
  let removed := (List.range last).filterMap (fun cut => removedName (trace.event cut))
  refine ⟨liveNames ++ removed, by simp only [List.length_append, removed, raw_removal_count trace last (Nat.le_refl _)], ?_⟩
  intro time bounded name row found
  apply List.mem_append.mpr
  cases atEnd : trace.state last name with
  | some final => exact .inl (liveCover name final atEnd)
  | none =>
    have stamped : (trace.notes time).1 name ≠ none := by
      intro missing
      have absent := (trace.births_agree time bounded name).mp missing
      rw [found] at absent
      cases absent
    cases tag : (trace.notes time).1 name with
    | none => exact False.elim (stamped tag)
    | some birth =>
      have born := (GuardedBirthMatching.recorded_birth trace bounded tag).1
      obtain ⟨final, life⟩ := lifetime_of_birth trace born
      have closes : final < last := by
        by_cases same : final = last
        · exact False.elim (life.resident.present last (same ▸ life.resident.ordered)
            (same.symm ▸ Nat.le_refl last) atEnd)
        · exact Nat.lt_of_le_of_ne life.bounded same
      exact .inr (List.mem_filterMap.mpr ⟨final, List.mem_range.mpr closes,
        by simp [removedName, (life.release closes).1]⟩)

/-- A bounded name supply suffices. The spare may differ between
intermediate histories, each of which has the same length. -/
theorem spare_of_birth_slots (trace : Trace program last)
    (supply : ∀ used : List Name, used.length ≤ birthSlotsThrough trace last → ∃ spare, spare ∉ used) :
    ∃ spare, ∀ time, time ≤ last → trace.state time spare = none := by
  obtain ⟨used, size, cover⟩ := history_name_cover_by_birth_slots trace
  obtain ⟨spare, outside⟩ := supply used size
  refine ⟨spare, fun time bounded => ?_⟩
  cases found : trace.state time spare with
  | none => rfl
  | some row => exact False.elim (outside (cover time bounded spare row found))

theorem spare_of_bounded_history (trace : Trace program last)
    (supply : ∀ used : List Name, used.length ≤ last → ∃ spare, spare ∉ used) :
    ∃ spare, ∀ time, time ≤ last → trace.state time spare = none :=
  spare_of_birth_slots trace (fun used size => supply used (Nat.le_trans size (birthSlotsThrough_le trace last)))

theorem spare_of_finite_history (trace : Trace program last) (_openOnly : ¬ Nonempty (ClosedEpisode trace))
    (supply : ∀ used : List Name, ∃ spare, spare ∉ used) :
    ∃ spare, ∀ time, time ≤ last → trace.state time spare = none :=
  spare_of_bounded_history trace (fun used _ => supply used)

end Cordis.Repairs.GuardedIncarnationRedraw
