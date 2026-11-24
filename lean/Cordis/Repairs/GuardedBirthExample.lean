import Cordis.Repairs.GuardedBirthReplay
import Cordis.Repairs.GuardedScheduleMatching
import Cordis.Repairs.GuardedAddressSchedule
import Cordis.Repairs.CommandBarrier

/-! Two actual histories choose different names for one child and the same
name for a later root. The stale child captures survive until the parent's
unload, when both must be skipped. -/
namespace Cordis.Repairs.GuardedBirthExample
open Calculus Stages CommandBarrier LegalHistory GuardedHistory
open GuardedBirthMatching GuardedBirthReplay GuardedCutState IncarnationReplay
open GuardedScheduleMatching
open GuardedBirthAddresses GuardedAddressSchedule
open Iterators (OptionRel)
open Vestigial (cutNotes eventActor)

private def parentRow (phase : Phase Nat Unit Bool (Inverse Nat Unit Unit)) (retired := false) : F :=
  { (fresh parentComponent none : F) with phase := phase, retired := retired }

private def childRow (retired := false) : F :=
  { (fresh providerComponent (some 0) : F) with retired := retired }

private def chosenView (child : Nat) : View Nat Unit := fun _ => child

private def opened (child : Nat) : R := mark inserted 0 (.reloading true [] (chosenView child))

private def active (child : Nat) : R := put empty 0 (parentRow (.active [.retire child] (chosenView child)))
private def replacement (child : Nat) : R := put (active child) 1 (fresh providerComponent none)
private def leaving (child : Nat) : R :=
  put (active child) 0 (parentRow (.unloading [.retire child] (chosenView child)) true)
private def closing (child : Nat) : R := put (leaving child) 1 (fresh providerComponent none)
private def finishedUnload : R :=
  put (put empty 0 (parentRow .inactive true)) 1 (fresh providerComponent none)

private def states (child : Nat) : Nat → R
  | 0 => empty
  | 1 => inserted
  | 2 => opened child
  | 3 => put (active child) child (childRow)
  | 4 => put (active child) child (childRow true)
  | 5 => active child
  | 6 => replacement child
  | 7 => retire (replacement child) 0
  | 8 => closing child
  | _ => finishedUnload

private def events (child : Nat) : Nat → Event Nat Unit Bool
  | 0 => .command (.insert 0 parentComponent)
  | 1 => .lifecycle .begin 0
  | 2 => .lifecycle .finish 0
  | 3 => .command (.retire child)
  | 4 => .command (.remove child)
  | 5 => .command (.insert 1 providerComponent)
  | 6 => .command (.retire 0)
  | 7 => .lifecycle .leave 0
  | _ => .lifecycle .unload 0

private def notes (child : Nat) := cutNotes (states child) (fun time => eventActor (events child time))

private theorem removed_child (child : Nat) (different : child ≠ 0) : Removable (states child 4) child := by
  rw [Removable, show states child 4 child = some (childRow true) by simp [states]]
  refine ⟨rfl, rfl, fun _ => rfl, ?_⟩
  intro name
  by_cases atChild : name = child
  · subst name; simp [states, childRow, fresh, Ne.symm different]
  by_cases atParent : name = 0
  · subst name; simp [states, active, parentRow, fresh, put, Ne.symm different]
  simp [states, active, empty, put, atChild, atParent]

private theorem closing_free (child : Nat) : ¬ Relied (closing child) 0 := by
  rintro ⟨name, other, relied⟩
  by_cases atRoot : name = 1
  · subst name; exact relied
  simp [closing, leaving, active, empty, put, atRoot, other] at relied

private theorem note_at_unload (child : Nat) (different : child ≠ 0) :
    (notes child 8).2 0 = [⟨.retire child, 3⟩] := by
  have parentDifferent : 0 ≠ child := Ne.symm different
  simp [notes, cutNotes, track, eventActor, events, advance, PartialReplayRegistry.saved, states, closing,
    leaving, replacement, active, opened, inserted, parentRow, mark, retire, Calculus.modify, put,
    parentDifferent, OrchestrationSorting.Command.actor, Phase.accumulator, fresh]

private theorem note_live_at_unload (child : Nat) (different : child ≠ 0) (name : Nat) :
    (notes child 8).1 name = if name = 0 then some 1 else if name = 1 then some 6 else none := by
  by_cases atParent : name = 0
  · subst name
    simp [notes, cutNotes, Incarnation.birthAt, states, opened, inserted, mark, closing, leaving,
      replacement, active, empty, retire, Calculus.modify, put, Ne.symm different]
  by_cases atRoot : name = 1
  · subst name
    simp [notes, cutNotes, Incarnation.birthAt, states, closing, leaving, replacement, active, empty,
      retire, Calculus.modify, put]
  simp [notes, cutNotes, Incarnation.birthAt, states, closing, leaving, replacement, active, empty,
    put, atParent, atRoot]

def trace (child : Nat) (different : child ≠ 0) : Trace program 9 where
  state := states child
  notes := notes child
  event := events child
  start := rfl
  seed := rfl
  step time bounded := by
    have cuts : time = 0 ∨ time = 1 ∨ time = 2 ∨ time = 3 ∨ time = 4 ∨
        time = 5 ∨ time = 6 ∨ time = 7 ∨ time = 8 := by omega
    apply And.intro ?_ rfl
    rcases cuts with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨⟨rfl, by simp, fun _ _ => trivial⟩, rfl⟩
    · exact .begin inserted 0 (fresh parentComponent none) (chosenView child) rfl rfl
        (by change some _ ≠ none; simp) ⟨rfl, fun _ impossible => Bool.noConfusion impossible⟩
    · have ready : Insertable (opened child) child providerComponent (some 0) := by
        refine ⟨by simp [opened, inserted, empty, mark, Calculus.modify, put, different], ?_, ?_⟩
        · intro name parent
          cases parent
          change some _ ≠ none
          simp
        · intro name key
          by_cases atParent : name = 0
          · subst name
            simp [opened, inserted, mark, Calculus.modify, put, fresh, parentComponent]
          · simp [opened, inserted, empty, mark, Calculus.modify, put, atParent]
      have endpoint : mark (put (opened child) child (fresh providerComponent (some 0))) 0
          (.active [.retire child] (chosenView child)) = states child 3 := by
        funext name
        by_cases atParent : name = 0
        · subst name; simp [states, active, parentRow, opened, inserted, fresh, mark,
            Calculus.modify, put, Ne.symm different]
        by_cases atChild : name = child
        · subst name; simp [states, childRow, fresh, mark, Calculus.modify, different]
        simp [states, active, opened, inserted, empty, mark, Calculus.modify, put, atChild, atParent]
      change Labeled.Step program .finish 0 (opened child) (states child 3)
      rw [← endpoint]
      exact .finish (opened child) _ 0 (parentRow (.reloading true [] (chosenView child)))
        true [] (chosenView child) (.retire child)
        rfl rfl ⟨rfl, fun _ impossible => Bool.noConfusion impossible⟩
        (.instantiate (opened child) 0 true providerComponent child rfl ready)
    · refine ⟨by change states child 3 child ≠ none; simp [states], ?_⟩
      funext name
      change states child 4 name = retire (states child 3) child name
      by_cases atChild : name = child <;> simp [states, retire, Calculus.modify, put, atChild, childRow]
    · refine ⟨removed_child child different, ?_⟩
      funext name
      change active child name = erase (states child 4) child name
      by_cases atChild : name = child
      · subst name; simp [active, empty, put, erase, different]
      · simp [states, put, erase, atChild]
    · refine ⟨⟨rfl, by simp, ?_⟩, rfl⟩
      intro name key
      by_cases atParent : name = 0 <;> simp [states, active, empty, put, parentRow, fresh, parentComponent, atParent]
    · exact ⟨by change some _ ≠ none; simp, rfl⟩
    · have endpoint : mark (states child 7) 0 (.unloading [.retire child] (chosenView child)) = states child 8 := by
        funext name
        by_cases atHome : name = 0
        · subst name; rfl
        · simp [states, closing, leaving, replacement, mark, retire, Calculus.modify, put, atHome]
      change Labeled.Step program .leave 0 (states child 7) (states child 8)
      rw [← endpoint]
      exact .leave (states child 7) 0 (parentRow (.active [.retire child] (chosenView child)) true) [.retire child] (chosenView child)
        rfl rfl (fun target => Bool.noConfusion target.1)
    · refine ⟨parentRow (.unloading [.retire child] (chosenView child)) true, chosenView child, rfl, ?_, closing_free child, ?_⟩
      · rw [note_at_unload child different]; rfl
      · change finishedUnload = mark (replay (notes child 8).1 ((notes child 8).2 0) (closing child)) 0 .inactive
        rw [note_at_unload child different]
        have stale : (notes child 8).1 child ≠ some 3 := by
          rw [note_live_at_unload child different]
          by_cases reused : child = 1 <;> simp [different, reused]
        simp only [replay, Capture.apply, if_neg stale]
        funext name
        by_cases atHome : name = 0
        · subst name; rfl
        · simp [finishedUnload, mark, Calculus.modify, closing, leaving, active, put, atHome]

private abbrev first := trace 1 (by decide)
private abbrev second := trace 2 (by decide)

theorem different_unused_views :
    ControlFrame.viewAt (first.state 2) 0 ≠ ControlFrame.viewAt (second.state 2) 0 := by
  intro same
  have coordinate := congrArg (Option.map fun (selected : View Nat Unit) => selected ()) same
  exact (by decide : (some 1 : Option Nat) ≠ some 2) coordinate

private def firstSix (renamed : Bool) : Trace program 6 :=
  let source := trace (if renamed then 2 else 1) (by cases renamed <;> decide)
  ⟨source.state, source.notes, source.event, source.start, source.seed, fun cut bounded => source.step cut (by omega)⟩

private theorem root_address (renamed : Bool) : Addressed (firstSix renamed) 1 (.root 0) :=
  .root (time := 0) (by decide) rfl

private theorem child_address (renamed : Bool) : Addressed (firstSix renamed) 3 (.child (.root 0) 0) := by
  refine .child (time := 2) (parentBirth := 1) (name := if renamed then 2 else 1)
    (by decide) rfl ?_ ?_ rfl (root_address renamed)
  · cases renamed <;> rfl
  · intro absent
    cases renamed <;> cases absent

private theorem parent_at (renamed : Bool) (cut : Nat) (atParent : cut = 1 ∨ cut = 2) :
    actorAddress (firstSix renamed) cut = some (.root 0) := by
  apply (actorAddress_eq_some _).mpr
  refine ⟨1, ?_, root_address renamed⟩
  rcases atParent with rfl | rfl <;> cases renamed <;> rfl

private theorem child_at (renamed : Bool) (cut : Nat) (atChild : cut = 3 ∨ cut = 4) :
    actorAddress (firstSix renamed) cut = some (.child (.root 0) 0) := by
  apply (actorAddress_eq_some _).mpr
  refine ⟨3, ?_, child_address renamed⟩
  rcases atChild with rfl | rfl <;> cases renamed <;> rfl

private theorem activity (renamed : Bool) {cut : Nat} {kind : Lifecycle} {name : Nat} (bounded : cut < 6)
    (event : (firstSix renamed).event cut = .lifecycle kind name) : Transposition.Activation kind.rule := by
  change events (if renamed then 2 else 1) cut = .lifecycle kind name at event
  have cuts : cut = 0 ∨ cut = 1 ∨ cut = 2 ∨ cut = 3 ∨ cut = 4 ∨ cut = 5 := by omega
  rcases cuts with rfl | rfl | rfl | rfl | rfl | rfl <;> cases event <;> simp [Lifecycle.rule, Transposition.Activation]

theorem equal_addressed_prefix : ∀ cut, cut < 6 → addressedEventAt (firstSix false) cut = addressedEventAt (firstSix true) cut := by
  intro cut bounded
  have range : cut = 0 ∨ cut = 1 ∨ cut = 2 ∨ cut = 3 ∨ cut = 4 ∨ cut = 5 := by omega
  have label (renamed : Bool) (i : Nat) : (firstSix renamed).event i = events (if renamed then 2 else 1) i := rfl
  rcases range with rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  · simp [addressedEventAt, label, events, parent_at _ 1 (Or.inl rfl)]
  · simp [addressedEventAt, label, events, parent_at _ 2 (Or.inr rfl)]
  · simp [addressedEventAt, label, events, child_at _ 3 (Or.inl rfl)]
  · simp [addressedEventAt, label, events, child_at _ 4 (Or.inr rfl)]
  · rfl

/-- The matched prefix includes creation, retirement and removal of the
two differently named children, followed by reusing name 1 for a root.
The address sequence itself supplies the common birth stamps. -/
theorem matched_prefix_through_reuse : CutAgreement first second 6 := by
  let left := firstSix false
  let right := firstSix true
  have beforeReuse : CutAgreement left right 5 := by
    apply match_open_prefix left right (fun _ _ _ _ _ => rfl) 5 (by decide) (by decide)
    intro cut bounded
    exact match_addressed_events left right (activity false) (activity true) equal_addressed_prefix cut (by omega)
  exact advance_addressed_cut left right (by decide) (by decide) beforeReuse (fun _ _ _ _ _ => rfl)
    (activity false (by decide)) (activity true (by decide))
    (fun cut prior => equal_addressed_prefix cut (by omega)) (equal_addressed_prefix 5 (by decide))

/-- A single name permutation cannot match the paired births across both
cuts. The same source name is the old child at 3 and the new root at 8. -/
theorem no_whole_history_permutation :
    ¬ ∃ p : Renaming.Permutation Nat, ∀ cut ∈ [3, 8], ∀ name,
      (second.notes cut).1 (p.toFun name) = (first.notes cut).1 name := by
  rintro ⟨p, allCuts⟩
  have childName : p.toFun 1 = 2 :=
    live_stamp_unique second (cut := 3) (birth := 3) (by decide) (allCuts 3 (by simp) 1) rfl
  have rootName : p.toFun 1 = 1 :=
    live_stamp_unique second (cut := 8) (birth := 6) (by decide) (allCuts 8 (by simp) 1) rfl
  exact (by decide : (2 : Nat) ≠ 1) (childName.symm.trans rootName)

local instance : Setoid Unit := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩

/-- At the actual unload both histories agree under the current identity
matching, even though their saved child names differ. -/
theorem unload_with_different_stale_names :
    StageSimulation.Related Eq (project (first.state 9)) (project (second.state 9)) ∧
      (first.state 9 1).map Fiber.retired = some false ∧
      (second.state 9 1).map Fiber.retired = some false := by
  let p : Renaming.Permutation Nat := ⟨id, id, fun _ => rfl, fun _ => rfl⟩
  have aligned : ∀ name, (second.notes 8).1 (p.toFun name) = ((first.notes 8).1 name).map id := by
    intro name
    change (notes 2 8).1 name = ((notes 1 8).1 name).map id
    rw [note_live_at_unload 2 (by decide), note_live_at_unload 1 (by decide), Option.map_id_fun]
    rfl
  have paired : ObservationLifting.ListRelated (CapturePair p id)
      ((first.notes 8).2 0) ((second.notes 8).2 (p.toFun 0)) :=
    .cons (.retire 1 2 3) .nil
  have initial : StageSimulation.Related Eq
      (Renaming.registry p (project (first.state 8))) (project (second.state 8)) := by
    intro name
    by_cases atHome : name = 0
    · subst name
      exact ⟨⟨rfl, rfl, rfl⟩, rfl, rfl, .unloading _ .nil, fun _ => trivial⟩
    by_cases atRoot : name = 1
    · subst name
      exact ⟨⟨rfl, rfl, rfl⟩, rfl, rfl, .inactive, fun _ => trivial⟩
    simp [p, Renaming.registry, project, OptionRel, trace, states, closing, leaving, active,
      empty, put, atHome, atRoot]
  have compared := unload_endpoints first second (i := 8) (j := 8) (by decide) (by decide) 0
    rfl rfl aligned (fun {_ _} same => same) paired initial
  refine ⟨?_, rfl, rfl⟩
  have exactNamespace : Renaming.registry p (project (first.state 9)) = project (first.state 9) := by
    funext name
    by_cases atHome : name = 0
    · subst name; rfl
    by_cases atRoot : name = 1
    · subst name; rfl
    simp [p, Renaming.registry, project, trace, states, finishedUnload, empty, put, atHome, atRoot]
  simpa only [exactNamespace] using compared

end Cordis.Repairs.GuardedBirthExample
