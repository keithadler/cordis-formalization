import Cordis.ChildProvenance
import Cordis.ControlFrame

/-! A derived order for live installed support. Each real L-Begin receives a
fresh natural rank; every other rule keeps ranks. Existing provider demands
cannot point to an inactive actor, and captured-child provenance excludes live
children of an inactive actor. Thus Begin preserves all old inequalities.
This does not assert the false unrestricted support order of Lemma75. -/
namespace Cordis.SupportOrder
open Calculus Stages
universe u
variable {Name Key Value Code Error : Type u}
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
variable [DecidableEq Name] [DecidableEq Key]
set_option linter.unusedSectionVars false

structure Ordered (r : R) (rank : Name → Nat) : Prop where
  provider : ∀ consumer provider key, Ordering.Demand r consumer provider key → rank provider < rank consumer
  parent : ∀ child entry ancestor view, r child = some entry → entry.parent = some ancestor →
    entry.retired = false → entry.phase.committed = some view → rank ancestor < rank child

def Ranked (r : R) : Prop := ∃ rank : Name → Nat, ∃ bound, (∀ n, rank n ≤ bound) ∧ Ordered r rank

theorem empty_ranked : Ranked (fun _ => none : R) := by
  refine ⟨fun _ => 0, 0, fun _ => Nat.le_refl _, ?_⟩
  constructor
  · intro c p k ⟨f, v, impossible, _⟩; cases impossible
  · intro c f p v impossible; cases impossible

/-- All preserved installed views carry old declarations, parentage and live
status backwards. This derives rank transfer from actual frame theorems. -/
theorem ordered_of_stable_views {r s : R} (stable : Frame.Stable r s)
    (views : ∀ n view, ControlFrame.viewAt s n = some view → ControlFrame.viewAt r n = some view)
    (rank : Name → Nat) (old : Ordered r rank) : Ordered s rank := by
  have origin : ∀ n after view, s n = some after → after.phase.committed = some view →
      ∃ before, r n = some before ∧ before.phase.committed = some view ∧
        before.component = after.component ∧ before.parent = after.parent ∧
        (after.retired = false → before.retired = false) := by
    intro n after view present committed
    have prior := views n view (by simp [ControlFrame.viewAt, present, committed])
    cases found : r n with
    | none => simp [ControlFrame.viewAt, found] at prior
    | some before =>
      have stable := stable n before after found present
      exact ⟨before, rfl, by simpa [ControlFrame.viewAt, found] using prior,
        stable.1, stable.2.1, ChildProvenance.false_of_monotone stable.2.2⟩
  constructor
  · intro c p k ⟨after, view, present, required, committed, names⟩
    obtain ⟨before, found, sameView, component, _, _⟩ := origin c after view present committed
    exact old.provider c p k ⟨before, view, found, by simpa [component] using required, sameView, names⟩
  · intro child after parent view present ancestor live committed
    obtain ⟨before, found, sameView, _, sameParent, wasLive⟩ := origin child after view present committed
    exact old.parent child before parent view found (sameParent.trans ancestor) (wasLive live) sameView

theorem ordered_of_views (program : Code → Instruction Name Key Value Code Error)
    {r s : R} (step : Calculus.Step (Land program) Stages.undo r s)
    (views : ∀ n view, ControlFrame.viewAt s n = some view → ControlFrame.viewAt r n = some view)
    (rank : Name → Nat) (old : Ordered r rank) : Ordered s rank :=
  ordered_of_stable_views (Frame.step_stable program step) views rank old

theorem inactive_has_no_live_child (r : R) (actor : Name) (fiber : F)
    (present : r actor = some fiber) (inactive : fiber.phase = .inactive)
    (captured : ChildProvenance.Captured r)
    (child : Name) (entry : F) (found : r child = some entry)
    (parent : entry.parent = some actor) (live : entry.retired = false) : False := by
  obtain ⟨owner, ownerFound, member⟩ := captured child entry actor found parent live
  have same : owner = fiber := Option.some.inj (ownerFound.symm.trans present)
  subst owner
  simp [inactive, Phase.accumulator] at member

def advance (rank : Name → Nat) (actor : Name) (bound : Nat) : Name → Nat :=
  fun n => if n = actor then bound + 1 else rank n

theorem begin_ordered (r : R) (actor : Name) (fiber : F) (view : View Name Key)
    (present : r actor = some fiber) (inactive : fiber.phase = .inactive)
    (target : Target r actor view) (supported : Ordering.Supported r)
    (captured : ChildProvenance.Captured r) (rank : Name → Nat) (bound : Nat)
    (bounded : ∀ n, rank n ≤ bound) (old : Ordered r rank) :
    Ordered (mark r actor (.reloading fiber.component.entry [] view)) (advance rank actor bound) := by
  constructor
  · intro consumer provider key ⟨entry, chosen, found, required, committed, names⟩
    by_cases acting : consumer = actor
    · subst consumer
      have same : { fiber with phase := .reloading fiber.component.entry [] view } = entry :=
        Option.some.inj (by simpa [mark, Calculus.modify, present] using found)
      subst entry
      have chosenEq : view = chosen := Option.some.inj committed
      subst chosen
      have available := target
      simp only [Target, present] at available
      have providerReady := available.2 key required
      have different : provider ≠ actor := by
        intro same
        have ownerEq : view key = actor := names.trans same
        simp [ownerEq, present, inactive, Phase.available] at providerReady
      simp only [advance, if_neg different]
      exact Nat.lt_succ_of_le (bounded provider)
    · have before : r consumer = some entry := by simpa [mark, Calculus.modify, acting] using found
      have demand : Ordering.Demand r consumer provider key := ⟨entry, chosen, before, required, committed, names⟩
      have different : provider ≠ actor := by
        intro same
        have demandActor : Ordering.Demand r consumer actor key := by simpa only [same] using demand
        obtain ⟨_, supplier, supplierFound, retained, _⟩ := supported consumer actor key demandActor
        have same : supplier = fiber := Option.some.inj (supplierFound.symm.trans present)
        subst supplier
        simp [inactive, Ordering.Retained] at retained
      simpa [advance, acting, different] using old.provider consumer provider key demand
  · intro child entry parent chosen found ancestor live committed
    by_cases acting : child = actor
    · subst child
      have same : { fiber with phase := .reloading fiber.component.entry [] view } = entry :=
        Option.some.inj (by simpa [mark, Calculus.modify, present] using found)
      subst entry
      have different : parent ≠ actor := by
        intro same
        subst parent
        exact inactive_has_no_live_child r actor fiber present inactive captured actor fiber present ancestor live
      simp only [advance, if_neg different]
      exact Nat.lt_succ_of_le (bounded parent)
    · have before : r child = some entry := by simpa [mark, Calculus.modify, acting] using found
      have different : parent ≠ actor := by
        intro same
        subst parent
        exact inactive_has_no_live_child r actor fiber present inactive captured child entry before ancestor live
      simpa [advance, acting, different] using old.parent child entry parent chosen before ancestor live committed

theorem step_ranked (program : Code → Instruction Name Key Value Code Error)
    {r s : R} (step : Orchestration.Step program r s) (old : Ranked r)
    (supported : Ordering.Supported r) (captured : ChildProvenance.Captured r) : Ranked s := by
  obtain ⟨rank, bound, bounded, ordered⟩ := old
  rcases ControlFrame.step_view_cases program step.toCalculus with unchanged | ⟨actor, begins⟩ | ⟨actor, unloads⟩
  · exact ⟨rank, bound, bounded, ordered_of_views program step.toCalculus
      (fun n v found => by simpa [unchanged] using found) rank ordered⟩
  · obtain ⟨fiber, view, present, inactive, _, target, rfl⟩ := begins
    refine ⟨advance rank actor bound, bound + 1, ?_,
      begin_ordered r actor fiber view present inactive target supported captured rank bound bounded ordered⟩
    intro n
    by_cases same : n = actor
    · simp [advance, same]
    · simpa [advance, same] using Nat.le_trans (bounded n) (Nat.le_succ bound)
  · obtain ⟨fiber, acc, view, present, unloading, _, rfl⟩ := unloads
    refine ⟨rank, bound, bounded, ordered_of_views program step.toCalculus ?_ rank ordered⟩
    intro n chosen found
    obtain ⟨after, afterFound, _⟩ := Ordering.discharge_existing_phases r acc actor fiber present
    rw [ControlFrame.mark_viewAt _ actor after .inactive afterFound] at found
    by_cases same : n = actor
    · simp [same, Phase.committed] at found
    · simpa [same, ControlFrame.discharge_views] using found

/-- The rank is constructed from the actual execution. No mixed-order
acyclicity, rank, support uniqueness or invariant-preservation premise is used. -/
theorem reachable_ranked (program : Code → Instruction Name Key Value Code Error)
    {r : R} (run : Orchestration.Run program (fun _ => none) r) : Ranked r := by
  have preservation : ∀ {a b : R}, Orchestration.Run program a b →
      Ranked a → Ordering.Invariant a → ChildProvenance.Captured a →
      Ranked b ∧ Ordering.Invariant b ∧ ChildProvenance.Captured b := by
    intro a b path
    induction path with
    | refl => intro ranked supported captured; exact ⟨ranked, supported, captured⟩
    | step history step ih =>
      intro ranked supported captured
      obtain ⟨rankAfter, supportAfter, captureAfter⟩ := ih ranked supported captured
      exact ⟨step_ranked program step rankAfter supportAfter.1 captureAfter,
        Ordering.step_invariant program step.toCalculus supportAfter,
        ChildProvenance.step_captured program step captureAfter⟩
  exact (preservation run empty_ranked ⟨Ordering.supported_empty, Ordering.local_empty⟩ ChildProvenance.captured_empty).1

end Cordis.SupportOrder
