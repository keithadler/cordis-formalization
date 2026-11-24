import Cordis.Repairs.EpisodeReleaseBarrier
import Cordis.Repairs.EpisodeInterleaving
import Cordis.Repairs.GuardedCanonicalSchedule

/-! The release barrier with only two names, forcing the second allocation
to reuse the first child's name. -/
namespace Cordis.Repairs.PinnedRedrawExample
open Calculus Stages LegalHistory GuardedHistory
open Vestigial (cutNotes eventActor)
open GuardedEpisodeExample (operations)
open EpisodeReleaseBarrier (Code parent child)

abbrev Name := Fin 2

abbrev R := TypedRegistry.RawRegistry Name operations Code
abbrev F := TypedRegistry.RawFiber Name operations Code
abbrev Ev := Event Name Unit Code

def entry : Code → TypedRegistry.Instruction Name operations Code
  | .first => ⟨.instantiate child, fun _ => some .second⟩
  | .second => ⟨.instantiate child, fun _ => none⟩
  | .child => ⟨.provide () 42, fun _ => none⟩
abbrev program := TypedRegistry.encodeProgram entry

def view : View Name Unit := fun _ => 0
def empty : R := fun _ => none
def s1 : R := put empty 0 (fresh parent none)
def s2 : R := mark s1 0 (.reloading .first [] view)
def s3 : R := mark (put s2 1 (fresh child (some 0))) 0 (.reloading .second [.retire 1] view)
def s4 : R := retire s3 1
def s5 : R := erase s4 1
def s6 : R := mark (put s5 1 (fresh child (some 0))) 0 (.active [.retire 1, .retire 1] view)
def s7 : R := retire s6 1

def states : Nat → R
  | 0 => empty | 1 => s1 | 2 => s2 | 3 => s3 | 4 => s4 | 5 => s5 | 6 => s6 | _ => s7

def events : Nat → Ev
  | 0 => .command (.insert 0 parent)
  | 1 => .lifecycle .begin 0
  | 2 => .lifecycle .iter 0
  | 3 => .command (.retire 1)
  | 4 => .command (.remove 1)
  | 5 => .lifecycle .finish 0
  | _ => .command (.retire 1)

private theorem firstBirth : Insertable s2 1 child (some 0) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro name equal
    cases equal
    change some _ ≠ none
    simp
  · intro name key
    by_cases owner : name = 0
    · subst name
      change true = true → ¬ false = true
      simp
    · simp [s2, s1, empty, mark, Calculus.modify, put, owner]

private theorem release : Removable s4 1 := by
  refine ⟨rfl, rfl, fun _ => rfl, ?_⟩
  intro name
  by_cases owner : name = 0
  · subst name; change (none : Option Name) ≠ some 1; simp
  by_cases old : name = 1
  · subst name; change (some 0 : Option Name) ≠ some 1; decide
  simp [s4, s3, s2, s1, empty, retire, mark, Calculus.modify, put, owner, old]

private theorem secondBirth : Insertable s5 1 child (some 0) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro name equal
    cases equal
    change some _ ≠ none
    simp
  · intro name key
    by_cases owner : name = 0
    · subst name
      change true = true → ¬ false = true
      simp
    by_cases old : name = 1
    · subst name; exact True.intro
    simp [s5, s4, s3, s2, s1, empty, erase, retire, mark, Calculus.modify, put, owner, old]

def trace : Trace program 7 where
  state := states
  notes := cutNotes states (fun cut => eventActor (events cut))
  event := events
  start := rfl
  seed := rfl
  step cut valid := by
    have cuts : cut = 0 ∨ cut = 1 ∨ cut = 2 ∨ cut = 3 ∨ cut = 4 ∨ cut = 5 ∨ cut = 6 := by omega
    rcases cuts with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨⟨⟨rfl, by simp, fun _ _ => trivial⟩, rfl⟩, rfl⟩
    · exact ⟨.begin s1 0 (fresh parent none) view rfl rfl (by change some _ ≠ none; simp)
        ⟨rfl, fun _ impossible => Bool.noConfusion impossible⟩, rfl⟩
    · exact ⟨.iter s2 _ 0 { (fresh parent none : F) with phase := .reloading .first [] view }
        .first [] view (.retire 1) .second rfl rfl ⟨rfl, fun _ impossible => Bool.noConfusion impossible⟩
        (.instantiate s2 0 .first child 1 rfl firstBirth), rfl⟩
    · exact ⟨⟨by change some _ ≠ none; simp, rfl⟩, rfl⟩
    · exact ⟨⟨release, rfl⟩, rfl⟩
    · exact ⟨.finish s5 _ 0 { (fresh parent none : F) with phase := .reloading .second [.retire 1] view }
        .second [.retire 1] view (.retire 1) rfl rfl ⟨rfl, fun _ impossible => Bool.noConfusion impossible⟩
        (.instantiate s5 0 .second child 1 rfl secondBirth), rfl⟩
    · exact ⟨⟨by change some _ ≠ none; simp, rfl⟩, rfl⟩

theorem open_only : ¬ Nonempty (ClosedEpisode trace) := by
  rintro ⟨closed⟩
  obtain ⟨unload, _⟩ := unload_boundary trace closed.interval
  change events closed.closed = .lifecycle .unload closed.name at unload
  have bound := closed.interval.bounded
  have cuts : closed.closed = 0 ∨ closed.closed = 1 ∨ closed.closed = 2 ∨ closed.closed = 3 ∨
      closed.closed = 4 ∨ closed.closed = 5 ∨ closed.closed = 6 := by omega
  rcases cuts with cut | cut | cut | cut | cut | cut | cut <;> simp [events, cut] at unload


private theorem name_cases (name : Name) : name = 0 ∨ name = 1 := by
  have upper := name.isLt
  rcases Nat.eq_zero_or_pos name.val with zero | positive
  · exact .inl (Fin.ext zero)
  · exact .inr (Fin.ext (by omega))

theorem quiet : Progress.Quiet (trace.state 7) := by
  intro name row found
  rcases name_cases name with rfl | rfl
  · have known : trace.state 7 0 = some { (fresh parent none : F) with phase := .active [.retire 1, .retire 1] view } := rfl
    rw [known] at found
    cases Option.some.inj found
    exact ⟨rfl, fun _ impossible => Bool.noConfusion impossible⟩
  · have known : trace.state 7 1 = some { (fresh child (some 0) : F) with retired := true } := rfl
    rw [known] at found
    cases Option.some.inj found
    intro _ target
    exact Bool.noConfusion target.1

/-- At the replacement birth the root is pinned to 0. The child
must avoid both 0 (collision) and 1 (the name being released). -/
theorem no_assignment_at_reuse :
    ¬ GuardedIncarnationRedraw.AssignmentForExchange trace 1 6 := by
  rintro ⟨assign, legal, _, vacant⟩
  have pinned : assign 1 = 0 := legal.2 0 0 parent (by decide) rfl
  have notOne : assign 6 ≠ 1 := vacant 1 6 rfl
  obtain zero | one := name_cases (assign 6)
  · have same : assign 1 = assign 6 := pinned.trans zero.symm
    have collision : (0 : Name) = 1 := legal.1 6 (by decide)
      (show GuardedDrawReplay.eventBirth trace 6 0 = some 1 from rfl)
      (show GuardedDrawReplay.eventBirth trace 6 1 = some 6 from rfl) same
    exact (by decide : (0 : Name) ≠ 1) collision
  · exact notOne one

theorem search_rejects_pinned_reuse :
    (GuardedIncarnationRedraw.findExchangeAssignment trace [0, 1] 1 6).isSome = false := by decide

theorem search_finds_assignment_at_earlier_vacancy :
    (GuardedIncarnationRedraw.findExchangeAssignment trace [0, 1] 1 1).isSome = true := by decide

theorem no_redraw_for_trace :
    ¬ GuardedCompleteAlignment.RedrawAtReuseFor trace := by
  intro redraw
  have life : GuardedReservationOrder.Lifetime trace 1 6 7 := by
    refine ⟨Incarnation.resident_of_birthAt ?_, Nat.le_refl _, fun impossible => False.elim (Nat.lt_irrefl _ impossible)⟩
    rfl
  have stable : GuardedLandingMatching.ChildContinuations program := by
    intro code component action left right
    cases code <;> rfl
  have born : GuardedBirthMatching.BornAt trace 1 6 := ⟨by decide, by decide, rfl, fun absent => by cases absent⟩
  have proposed := redraw open_only quiet
    (show trace.event 4 = .command (.remove 1) from rfl)
    (show trace.event (4 + 1) = .lifecycle .finish 0 from rfl) life
  exact no_assignment_at_reuse ((GuardedIncarnationRedraw.redraw_for_exchange_iff_assignment
    trace open_only quiet stable born rfl).mp proposed)

theorem no_redraw_at_reuse :
    ¬ GuardedCompleteAlignment.RedrawAtReuse (program := entry) :=
  fun redraw => no_redraw_for_trace (redraw trace trivial)

/-- The matched-cut hypothesis excludes the pinned removal as a request
to align an immediately waiting birth. Both names are occupied at cut 4. -/
theorem waiting_redraw_at_full_cut :
    GuardedCompleteAlignment.RedrawAtWaitingReuseFor trace 4 := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨name, vacant⟩ _
  rcases name_cases name with rfl | rfl <;> cases vacant

/-- The concrete retirement and removal cannot be executed before the
first child birth, even though the child's name is about to be reused. -/
theorem cannot_advance_first_child_commands :
    ¬ ∃ moved : Trace program 7, moved.state 2 = trace.state 2 ∧
      moved.event 2 = .command (.retire 1) ∧ moved.event 3 = .command (.remove 1) := by
  rintro ⟨moved, same, retirement, removal⟩
  have block : ∀ cut, 2 < cut → cut ≤ 2 + 2 → ∃ command, trace.event cut = .command command := by
    intro cut lower upper
    have atCut : cut = 3 ∨ cut = 4 := by omega
    rcases atCut with rfl | rfl
    · exact ⟨.retire 1, rfl⟩
    · exact ⟨.remove 1, rfl⟩
  have shifted : ∀ cut, 2 ≤ cut → cut < 2 + 2 → moved.event cut = trace.event (cut + 1) := by
    intro cut lower upper
    have atCut : cut = 2 ∨ cut = 3 := by omega
    rcases atCut with rfl | rfl
    · exact retirement
    · exact removal
  have ready := (GuardedCommandAlignment.command_block_can_advance_iff trace open_only quiet
    (pivot := 2) (span := 2) (by decide)
    (show trace.event 2 = .lifecycle .iter 0 from rfl) block).mpr ⟨moved, same, shifted⟩
  have impossible := ready 3 (by decide) (by decide) (.retire 1) rfl rfl
  cases impossible

/-- The replacement cannot finish one cut earlier while the old child
still occupies the only available child name. -/
theorem no_finish_before_removal (moved : Trace program 7)
    (sameCut : moved.state 4 = trace.state 4) (finish : moved.event 4 = .lifecycle .finish 0) :
    False := by
  obtain ⟨row, code, word, selected, mid, token, next, present, loading, landed, _, _⟩ :=
    GuardedLandingMatching.activation_landing moved (by decide) (.inr finish)
  have current : trace.state 4 0 = some
      { (fresh parent none : F) with phase := .reloading .second [.retire 1] view } := rfl
  rw [sameCut, current] at present
  cases Option.some.inj present
  cases loading
  rw [sameCut] at landed
  generalize source : trace.state 4 = before at landed
  cases landed
  all_goals try contradiction
  rename_i draw action ready continues ending
  have full (name : Name) : before name ≠ none := by
    rw [← source]
    rcases name_cases name with rfl | rfl <;> (change some _ ≠ none; exact Option.noConfusion)
  exact full draw ready.1

/-- A legal canonical schedule exists in the two-name set despite the
failed uniform redraw hypothesis for this program. -/
theorem canonical_exists_with_no_uniform_redraw :
    (∃ result : Trace program 7,
      GuardedCanonicalSchedule.Canonical (GuardedBirthAddresses.orchestrationInput trace) result) ∧
      ¬ GuardedCompleteAlignment.RedrawAtReuse (program := entry) :=
  ⟨GuardedCanonicalSchedule.exists_canonical trace open_only quiet, no_redraw_at_reuse⟩

/-- The seven-transition release history needs only four names in the
sufficient supply: one insertion and two allocating stages can add rows. -/
theorem release_history_four_name_supply :
    letI : Setoid (TypedRegistry.Scalar operations) :=
      TypedCoeffectReplay.setoid GuardedEpisodeExample.observe
    ∃ (length : Nat) (reduced moved : Trace EpisodeReleaseBarrier.program length),
      GuardedCanonicalSchedule.Canonical (GuardedBirthAddresses.orchestrationInput reduced) moved ∧
      GuardedCompleteAlignment.ScheduleAlignmentPath reduced moved ∧
      originalRoots moved = originalRoots EpisodeReleaseBarrier.trace := by
  have stable : GuardedLandingMatching.ChildContinuations EpisodeReleaseBarrier.program := by
    intro code component action left right
    cases code <;> rfl
  obtain ⟨length, reduced, moved, _, _, _, canonical, path, roots, _⟩ :=
    GuardedCanonicalSchedule.normalize_with_birth_slot_supply EpisodeReleaseBarrier.trace
      EpisodeReleaseBarrier.quiet stable [0, 1, 2, 3] (by decide) (by decide)
      GuardedEpisodeExample.observe (fun _ op => nomatch op) (fun _ op => nomatch op)
      (fun _ op => nomatch op)
  exact ⟨length, reduced, moved, canonical, path, roots⟩

/-- The swap can continue past Q's child removal and rename the later
allocation by P. The spare is occupied at the original endpoint. -/
theorem redraw_past_child_removal :
    EpisodeInterleaving.trace.state 14 4 ≠ none ∧
      GuardedIncarnationRedraw.ChildRedraw EpisodeInterleaving.trace 3 4 8 14 .iter 1 := by
  refine ⟨(by intro absent; cases absent), ?_⟩
  have life : GuardedReservationOrder.Lifetime EpisodeInterleaving.trace 3 8 9 :=
    GuardedReservationOrder.lifetime_of_removal EpisodeInterleaving.trace (by decide) rfl rfl
  have stable : GuardedLandingMatching.ChildContinuations EpisodeInterleaving.program := by
    intro code component action left right
    cases code <;> rfl
  apply GuardedIncarnationRedraw.redraw_child_with_swap_interval EpisodeInterleaving.trace
    EpisodeInterleaving.open_only EpisodeInterleaving.quiet stable life (by decide) (by decide) (by decide)
    rfl (by decide) rfl (fun impossible => (Nat.lt_irrefl _ impossible).elim)
    (fun impossible => (Nat.lt_irrefl _ impossible).elim)
  intro cut name component lower _ bounded event
  have cuts : cut = 7 ∨ cut = 8 ∨ cut = 9 ∨ cut = 10 ∨ cut = 11 ∨ cut = 12 ∨ cut = 13 := by omega
  rcases cuts with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases event

end Cordis.Repairs.PinnedRedrawExample
