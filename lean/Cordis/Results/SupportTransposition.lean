import Cordis.PaperTranspositionExamples
import Cordis.PaperTotalLabeled
import Cordis.PaperTranspositionAdjacent
import Cordis.RenamingLiteralExamples
import Cordis.TranspositionOrchestration
import Cordis.Results.NondeterministicTransposition

/-! Transposition and counterexamples for Lemma 78 of arXiv:2608.25512v1. -/

namespace Cordis.Results

section CoarseObservation
open Calculus Stages Effects Iterators PaperTranspositionExamples
noncomputable section

local instance : Setoid Nat := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
local instance : Setoid sem.Gamma := PaperStateObservation.base sem

/-- Definition 65's Definition 34 table observation makes the two terminal
instantiations independent. There are no table keys, and each chooses the same
component with no continuation. -/
theorem lemma78_terminal_births_independent :
    Iterators.Independent (sem.iterator 0 true) (sem.iterator 1 true) := by
  constructor
  · exact fun _ _ _ _ _ => all_tables _ _
  · intro head reached _ _ _
    rw [terminal_reach 0 true reached]
    exact ⟨fun {_ _} _ => all_tables _ _, True.intro⟩
  · intro head reached _ _ _
    rw [terminal_reach 1 true reached]
    exact ⟨fun {_ _} _ => all_tables _ _, True.intro⟩

private def model : PaperTotal.Model Nat Empty Nat Bool Empty := ⟨program, draw, failed⟩
private def initial : R := fun _ => none
private def firstRoot : R := put initial 0 (fresh (component true) none)
private def bothRoots : R := put firstRoot 1 (fresh (component true) none)
private def oneReloading : R := mark bothRoots 0 (.reloading true [] view)
private def bothReloading : R := mark oneReloading 1 (.reloading true [] view)
private def reloading : F := {(fresh (component true) none : F) with phase := .reloading true [] view}

private theorem history : PaperTotal.Run program draw failed initial bothReloading := by
  have insertFirst : Calculus.Step (PaperTotal.Landing program draw failed) Stages.undo initial firstRoot :=
    .insert _ _ _ _ (by simp [Insertable, initial])
  have insertSecond : Calculus.Step (PaperTotal.Landing program draw failed) Stages.undo firstRoot bothRoots :=
    .insert _ _ _ _ ⟨rfl, by simp, fun _ key => nomatch key⟩
  have beginFirst : Calculus.Step (PaperTotal.Landing program draw failed) Stages.undo bothRoots oneReloading :=
    .begin _ 0 (fresh (component true) none) view rfl rfl (by change some _ ≠ none; simp) ⟨rfl, fun key => nomatch key⟩
  have beginSecond : Calculus.Step (PaperTotal.Landing program draw failed) Stages.undo oneReloading bothReloading :=
    .begin _ 1 (fresh (component true) none) view rfl rfl (by change some _ ≠ none; simp) ⟨rfl, fun key => nomatch key⟩
  exact .tail (.tail (.tail (.tail (.refl _) insertFirst) insertSecond) beginFirst) beginSecond

private def born (before : R) (actor child : Nat) : R :=
  mark (put before child (fresh (component false) (some actor))) actor (.active [.retire child] view)

private theorem finish_birth {before : R} {actor child : Nat}
    (found : before actor = some reloading) (vacant : before child = none)
    (chosen : draw before = child) :
    PaperTotal.Labeled.Step model .finish actor before (born before actor child) := by
  have landed := birth_at before actor child (by rw [found]; simp) vacant
  exact .finish _ _ _ reloading true [] view (.retire child) found rfl
    (by rw [Target, found]; exact ⟨rfl, fun key => nomatch key⟩) (PaperTotal.ordinary_landing program draw failed landed chosen)

private theorem finish_unique {before first second : R} {actor : Nat}
    (left : PaperTotal.Labeled.Step model .finish actor before first)
    (right : PaperTotal.Labeled.Step model .finish actor before second) : first = second := by
  cases left
  rename_i firstStage firstRow firstCode firstStack firstView firstInverse firstPhase firstFound firstTarget firstLanded
  cases right
  rename_i secondStage secondRow secondCode secondStack secondView secondInverse secondPhase secondFound secondTarget secondLanded
  have rowEq := Option.some.inj (firstFound.symm.trans secondFound)
  subst secondRow
  rw [firstPhase] at secondPhase
  cases secondPhase
  change PaperTotal.evaluate program draw failed actor firstCode before = (_, _, _) at firstLanded secondLanded
  have landedEq := firstLanded.symm.trans secondLanded
  cases landedEq
  rfl

private theorem originalFirst :
    PaperTotal.Labeled.Step model .finish 0 bothReloading (born bothReloading 0 2) := by
  apply finish_birth (by rfl) (by rfl)
  simp [draw, drawFrom, bothReloading, oneReloading, bothRoots, firstRoot, initial, mark, Calculus.modify, put]

private theorem originalSecond :
    PaperTotal.Labeled.Step model .finish 1 (born bothReloading 0 2) (born (born bothReloading 0 2) 1 3) := by
  apply finish_birth (by rfl) (by rfl)
  simp [draw, drawFrom, born, bothReloading, oneReloading, bothRoots, firstRoot, initial, mark, Calculus.modify, put]

private theorem swappedFirst :
    PaperTotal.Labeled.Step model .finish 1 bothReloading (born bothReloading 1 2) := by
  apply finish_birth (by rfl) (by rfl)
  simp [draw, drawFrom, bothReloading, oneReloading, bothRoots, firstRoot, initial, mark, Calculus.modify, put]

private theorem swappedSecond :
    PaperTotal.Labeled.Step model .finish 0 (born bothReloading 1 2) (born (born bothReloading 1 2) 0 3) := by
  apply finish_birth (by rfl) (by rfl)
  simp [draw, drawFrom, born, bothReloading, oneReloading, bothRoots, firstRoot, initial, mark, Calculus.modify, put]

private theorem nondeterministic_finish {before : R} {actor child : Nat}
    (found : before actor = some reloading) (vacant : before child = none) :
    Labeled.Step program .finish actor before (born before actor child) := by
  have landed := birth_at before actor child (by rw [found]; simp) vacant
  exact .finish _ _ _ reloading true [] view (.retire child) found rfl
    (by rw [Target, found]; exact ⟨rfl, fun key => nomatch key⟩) landed

private theorem nondeterministic_swaps :
    ∃ intermediate,
      Labeled.Step program .finish 1 bothReloading intermediate ∧
      Labeled.Step program .finish 0 intermediate (born (born bothReloading 0 2) 1 3) := by
  have first := nondeterministic_finish (before := bothReloading) (actor := 1) (child := 3) rfl rfl
  have second := nondeterministic_finish (before := born bothReloading 1 3) (actor := 0) (child := 2) rfl rfl
  have same : born (born bothReloading 1 3) 0 2 = born (born bothReloading 0 2) 1 3 := by
    funext name
    by_cases root0 : name = 0
    · subst name; rfl
    by_cases root1 : name = 1
    · subst name; rfl
    by_cases child2 : name = 2
    · subst name; rfl
    by_cases child3 : name = 3
    · subst name; rfl
    simp [born, mark, Calculus.modify, put, root0, root1, child2, child3]
  exact ⟨_, first, same ▸ second⟩

/-- Under one presence-only fresh allocator both original L-Finish steps are
admissible, and the second is already applicable before the first. Every
reversed execution changes the parent of child 2, which (54) preserves.
This distinguishes fixed fresh selection and coarse independence from the
finer independence premise in the positive transposition theorem. The same
original endpoint is reachable in reverse order when each rule is allowed to
reuse the original draw. -/
theorem lemma78_coarse_fixed_draw_counterexample :
    ∃ (model : PaperTotal.Model Nat Empty Nat Bool Empty) (source middle endpoint : R),
      PaperTotal.Run model.program model.draw model.failed (fun _ => none) source ∧
      PaperTransposition.DrawByPresence model.draw ∧
      PaperTransposition.FailureByTables model.failed ∧
      (∀ before : G, before.val (model.draw before.val) = none) ∧
      (∀ actor code, WitnessedIterator (sem.iterator actor code)) ∧
      (∀ code, MediatedRegistry.Mediated model.program (fun _ => False) (fun _ => False) code) ∧
      (∀ actor code, PaperTransposition.EvaluationRep sem model.program model.draw model.failed actor code) ∧
      WellFormed.WellFormed source ∧
      ¬ PaperTransposition.ComponentsIndependent sem source 0 1 ∧
      (∃ left right : F, source 0 = some left ∧ source 1 = some right ∧
        Iterators.Independent (sem.iterator 0 left.component.entry) (sem.iterator 1 right.component.entry)) ∧
      PaperTotal.Labeled.Step model .finish 0 source middle ∧
      PaperTotal.Labeled.Step model .finish 1 middle endpoint ∧
      (∃ before, PaperTotal.Labeled.Step model .finish 1 source before) ∧
      (∃ before, Labeled.Step model.program .finish 1 source before ∧
        Labeled.Step model.program .finish 0 before endpoint) ∧
      ¬ (∃ reorderedMiddle reorderedEndpoint,
        PaperTotal.Labeled.Step model .finish 1 source reorderedMiddle ∧
        PaperTotal.Labeled.Step model .finish 0 reorderedMiddle reorderedEndpoint ∧
        PaperStateObservation.Related sem reorderedEndpoint endpoint) := by
  refine ⟨model, bothReloading, _, _, history, draw_by_presence, failure_by_tables, draw_fresh,
    all_witnessed, all_mediated, representation, ?_, ?_, ⟨reloading, reloading, rfl, rfl, lemma78_terminal_births_independent⟩,
    originalFirst, originalSecond, ⟨_, swappedFirst⟩, nondeterministic_swaps, ?_⟩
  · have invariant := PaperTotal.reachable_invariant program draw failed history
    exact WellFormed.wellFormed_of_invariants _ invariant.1.1.1 invariant.1.2.2.2 invariant.2.1
  · intro independent
    exact fixed_birth_pair_rejects_finer_independence (independent reloading reloading rfl rfl)
  · rintro ⟨reorderedMiddle, reorderedEndpoint, first, second, related⟩
    have firstEq := finish_unique first swappedFirst
    subst reorderedMiddle
    have secondEq := finish_unique second swappedSecond
    subst reorderedEndpoint
    have fields := PaperStateObservation.fields sem related 2
      (fresh (component false) (some 1)) (fresh (component false) (some 0)) rfl rfl
    cases fields.parent

end
end CoarseObservation

section DisplayedInsert
open Calculus Stages RenamingLiteral RenamingLiteralExamples

/-- The unrestricted displayed O-Insert cannot be moved ahead of the activation
that created its designated parent. The external actor 2 differs from the
activation actor 0 and is also distinct from the child actually created at 1. -/
theorem lemma78_displayed_insert_counterexample :
    Orchestration.Run program r0 r2 ∧ rootName ≠ replacementName ∧
    (∃ after, Labeled.Step program .finish rootName r2 r3 ∧
      Labeled.Step program .insert replacementName r3 after ∧
      after replacementName = some (fresh childComponent (some childName))) ∧
    ¬ Transposition.CreatesChild program rootName r2 r3 replacementName ∧
    ¬ Insertable r2 replacementName childComponent (some childName) := by
  have finish : Labeled.Step program .finish rootName r2 r3 :=
    .finish r2 middle rootName
      { (fresh rootComponent none : F) with phase := .reloading true [] emptyView }
      true [] emptyView (.retire childName) rfl rfl
      ⟨rfl, fun key => nomatch key⟩ actual_birth
  have insert : Insertable r3 replacementName childComponent (some childName) :=
    ⟨rfl, (by intro name same; cases same; intro absent; cases absent), fun _ key => nomatch key⟩
  have creates : ¬ Transposition.CreatesChild program rootName r2 r3 replacementName := by
    rintro ⟨code, entry, phase, _, _, result⟩
    have observed := congrFun result replacementName
    simp [r3, middle, r2, r1, r0, mark, Calculus.modify, put, rootName, childName, replacementName] at observed
  have notInsert : ¬ Insertable r2 replacementName childComponent (some childName) :=
    fun allowed => allowed.2.1 childName rfl rfl
  exact ⟨.step (.step (.refl _) insert_step) begin_step, by decide,
    ⟨_, finish, .insert r3 replacementName childComponent (some childName) insert, rfl⟩, creates, notInsert⟩
end DisplayedInsert

end Cordis.Results
