import Cordis.Repairs.GuardedEpisodeExample
import Cordis.Repairs.GuardedOpenExchange

/-! Two stages of the same open episode allocate children that reserve the
same key. The first reservation has to be released before the second birth. -/
namespace Cordis.Repairs.EpisodeReleaseBarrier
open Calculus Stages LegalHistory GuardedHistory
open Vestigial (cutNotes eventActor CompatibleBirths)
open GuardedEpisodeExample (operations)

inductive Code where
  | first | second | child
  deriving DecidableEq

abbrev R := TypedRegistry.RawRegistry Nat operations Code
abbrev F := TypedRegistry.RawFiber Nat operations Code
abbrev Ev := Event Nat Unit Code

def parent : Component Unit Code := ⟨fun _ => false, fun _ => false, .first⟩
def child : Component Unit Code := ⟨fun _ => false, fun _ => true, .child⟩
def entry : Code → TypedRegistry.Instruction Nat operations Code
  | .first => ⟨.instantiate child, fun _ => some .second⟩
  | .second => ⟨.instantiate child, fun _ => none⟩
  | .child => ⟨.provide () 42, fun _ => none⟩
abbrev program := TypedRegistry.encodeProgram entry

def view : View Nat Unit := fun _ => 0
def empty : R := fun _ => none
def s1 : R := put empty 0 (fresh parent none)
def s2 : R := mark s1 0 (.reloading .first [] view)
def s3 : R := mark (put s2 1 (fresh child (some 0))) 0 (.reloading .second [.retire 1] view)
def s4 : R := retire s3 1
def s5 : R := erase s4 1
def s6 : R := mark (put s5 2 (fresh child (some 0))) 0 (.active [.retire 2, .retire 1] view)
def s7 : R := retire s6 2

def states : Nat → R
  | 0 => empty | 1 => s1 | 2 => s2 | 3 => s3 | 4 => s4 | 5 => s5 | 6 => s6 | _ => s7

def events : Nat → Ev
  | 0 => .command (.insert 0 parent)
  | 1 => .lifecycle .begin 0
  | 2 => .lifecycle .iter 0
  | 3 => .command (.retire 1)
  | 4 => .command (.remove 1)
  | 5 => .lifecycle .finish 0
  | _ => .command (.retire 2)

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
  · subst name; change (none : Option Nat) ≠ some 1; simp
  by_cases old : name = 1
  · subst name; change (some 0 : Option Nat) ≠ some 1; decide
  simp [s4, s3, s2, s1, empty, retire, mark, Calculus.modify, put, owner, old]

private theorem secondBirth : Insertable s5 2 child (some 0) := by
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
        .second [.retire 1] view (.retire 2) rfl rfl ⟨rfl, fun _ impossible => Bool.noConfusion impossible⟩
        (.instantiate s5 0 .second child 2 rfl secondBirth), rfl⟩
    · exact ⟨⟨by change some _ ≠ none; simp, rfl⟩, rfl⟩

theorem open_only : ¬ Nonempty (ClosedEpisode trace) := by
  rintro ⟨closed⟩
  obtain ⟨unload, _⟩ := unload_boundary trace closed.interval
  change events closed.closed = .lifecycle .unload closed.name at unload
  have bound := closed.interval.bounded
  have cuts : closed.closed = 0 ∨ closed.closed = 1 ∨ closed.closed = 2 ∨ closed.closed = 3 ∨
      closed.closed = 4 ∨ closed.closed = 5 ∨ closed.closed = 6 := by omega
  rcases cuts with cut | cut | cut | cut | cut | cut | cut <;> simp [events, cut] at unload

private theorem final_rows (name : Nat) : s7 name =
    if name = 0 then some { (fresh parent none : F) with phase := .active [.retire 2, .retire 1] view }
    else if name = 2 then some { (fresh child (some 0) : F) with retired := true } else none := by
  by_cases owner : name = 0
  · subst name; rfl
  by_cases new : name = 2
  · subst name; rfl
  by_cases old : name = 1
  · subst name; rfl
  simp [s7, s6, s5, s4, s3, s2, s1, empty, erase, retire, mark, Calculus.modify, put, owner, new, old]

theorem quiet : Progress.Quiet (trace.state 7) := by
  intro name row found
  change s7 name = some row at found
  rw [final_rows] at found
  by_cases owner : name = 0
  · subst name
    simp only [ite_true] at found
    cases Option.some.inj found
    exact ⟨rfl, fun _ impossible => Bool.noConfusion impossible⟩
  by_cases new : name = 2
  · subst name
    simp only [if_neg owner, ite_true] at found
    cases Option.some.inj found
    intro _ target
    exact Bool.noConfusion target.1
  simp [owner, new] at found

theorem total : SupportAtQuiescence.TotalProvision (trace.state 7) := by
  intro name row found available key
  change s7 name = some row at found
  rw [final_rows] at found
  by_cases owner : name = 0
  · subst name
    simp only [ite_true] at found
    cases Option.some.inj found
    simp [fresh, parent]
  by_cases new : name = 2
  · subst name
    simp only [if_neg owner, ite_true] at found
    cases Option.some.inj found
    exact False.elim available
  simp [owner, new] at found

/-- The release is needed because the old and new rows claim the same
provision. The later birth already chooses a different fresh name. -/
theorem removal_cannot_follow_finish :
    ¬ ∃ middle, Labeled.Step program .finish 0 (trace.state 4) middle ∧
      (OrchestrationSorting.Command.remove (Key := Unit) (Code := Code) 1).Step middle (trace.state 6) := by
  intro swapped
  have compatible := (trace.activation_crosses_removal_iff open_only quiet (time := 4) (by decide)
    (removed := 1) (actor := 0) (kind := .finish) rfl rfl).mp swapped
  have disjoint := (compatible 2 (fresh child (some 0)) rfl rfl).2
  exact disjoint { (fresh child (some 0) : F) with retired := true } rfl () rfl rfl

/-- Changing the draw does not free the provision reservation of the first
child. Before removal, no new name can admit the second child. -/
theorem no_fresh_draw_before_release (name : Nat) : ¬ Insertable (trace.state 4) name child (some 0) := by
  intro allowed
  exact allowed.2.2 1 () rfl rfl

/-- The first landing has to be an allocation, including in executions
that use a different registry or fresh-name draw. -/
private theorem iter_keeps_claim {actor : Nat} {before after : R}
    (iter : Labeled.Step program .iter actor before after) :
    ∃ (row : F), ∃ word selected newName, after actor = some row ∧
      row.phase = .reloading .second word selected ∧ after newName = some (fresh child (some actor)) := by
  cases iter with
  | iter _ stage _ row code word selected inverse next found phase target land =>
    generalize result : some next = continuation at land
    cases code <;> cases land
    all_goals try contradiction
    all_goals try (simp [entry, TypedRegistry.encodeInstruction, TypedRegistry.decodeOutcome] at result)
    subst next
    rename_i component newName action ready
    have payload : child = component := Stages.Action.instantiate.inj action
    subst component
    have foreign : newName ≠ actor := by
      intro same
      subst newName
      exact ready.2.1 actor rfl ready.1
    have placed : put before newName (fresh child (some actor)) actor = some row :=
      (Transposition.put_other _ _ _ _ (Ne.symm foreign)).trans found
    exact ⟨_, _, selected, newName, mark_self _ _ _ _ placed, rfl, by
      rw [Transposition.mark_other _ _ _ _ foreign, put_self]⟩

/-- The two stages of this episode cannot be consecutive in any execution.
A reservation has to be released between them, independently of names. -/
theorem no_adjacent_iter_finish {actor : Nat} {before middle after : R}
    (iter : Labeled.Step program .iter actor before middle)
    (finish : Labeled.Step program .finish actor middle after) : False := by
  obtain ⟨row, word, selected, old, present, phase, claim⟩ := iter_keeps_claim iter
  cases finish with
  | finish _ stage _ other code tail chosen inverse found reloading target land =>
    have same := Option.some.inj (found.symm.trans present)
    subst other
    rw [phase] at reloading
    cases reloading
    generalize result : (none : Option Code) = continuation at land
    cases land
    all_goals try contradiction
    rename_i component draw action ready
    have payload : child = component := Stages.Action.instantiate.inj action
    subst component
    have conflict := ready.2.2 old ()
    rw [claim] at conflict
    exact conflict rfl rfl

end Cordis.Repairs.EpisodeReleaseBarrier
