import Cordis.PaperTranspositionTotal
import Cordis.PaperTranspositionObservation
import Cordis.PaperTotalInvariants
import Cordis.ProgressDefinedness

/-! An inhabited original-base/finer-commutation pair: a genuine terminal
birth and a terminal unit, with empty declarations. The admissible Gamma is
every finite rooted structural registry, not a domain selected by the diamond.
All function-field respect is derived because the table observation has no
keys and both code meanings terminate. Arbitrary captured retirement words are
allowed. This is a control-changing example, not a nonempty table-mutation
claim under the incompatible checked global witnesses. -/
namespace Cordis.PaperTranspositionExamples
noncomputable section
open Calculus Stages Iterators Effects StageRecovery PaperTransposition
abbrev R := Registry Nat Empty Nat Bool (Inverse Nat Empty Nat) Empty
abbrev F := Fiber Nat Empty Nat Bool (Inverse Nat Empty Nat) Empty
abbrev G := MediatedRegistry.Gamma Nat Empty Nat Bool Empty
local instance : Setoid Nat := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩

def component (entry : Bool) : Component Empty Bool := ⟨Empty.elim, Empty.elim, entry⟩
def program : Bool → Instruction Nat Empty Nat Bool Empty
  | false => {action := .unit, next := fun _ => none}
  | true => {action := .instantiate (component false), next := fun _ => none}
def drawFrom (vacant : Nat → Prop) : Nat := by
  classical
  exact if vacant 2 then 2 else if vacant 3 then 3 else
    if available : ∃ name, vacant name then Classical.choose available else 0
def draw (state : R) : Nat := drawFrom (fun name => state name = none)
def failed (_ : Bool) (_ : R) : Option (Outcome Nat Nat) := none

theorem draw_by_presence : DrawByPresence draw := by
  intro left right present
  exact congrArg drawFrom (funext (fun name => propext (present name)))
theorem failure_by_tables : FailureByTables failed := fun _ _ _ _ => rfl
theorem draw_fresh (state : G) : state.val (draw state.val) = none := by
  classical
  obtain ⟨names, covered⟩ := state.property.2.1
  have available := ProgressDefinedness.nat_fresh_of_finite state.val names covered
  unfold draw drawFrom
  split
  · assumption
  · split
    · assumption
    · exact Classical.choose_spec available

def meaning (actor : Nat) (code : Bool) : Iterator G :=
  embed (MediatedRegistry.head program actor (fun state => draw state.val) code)
def sem : PaperStateObservation.Semantics Nat Empty Nat Bool Empty := PaperStateObservation.structural meaning
local instance : Setoid sem.Gamma := PaperStateObservation.base sem

theorem all_tables (left right : sem.Gamma) : left ≈ right := by
  intro key
  cases key
theorem all_witnessed (actor : Nat) (code : Bool) : WitnessedIterator (sem.iterator actor code) := by
  apply witnessed_embed
  exact ⟨fun _ => all_tables _ _, fun {_ _} _ => ⟨all_tables _ _, fun {_ _} _ => all_tables _ _⟩⟩

theorem all_mediated (code : Bool) :
    MediatedRegistry.Mediated program (fun _ => False) (fun _ => False) code := by
  cases code with
  | false => exact .unit false rfl (fun _ => rfl)
  | true =>
    apply MediatedRegistry.Mediated.birth true (component false) rfl
    intro outcome following impossible
    cases impossible

theorem representation (actor : Nat) (code : Bool) : EvaluationRep sem program draw failed actor code := by
  constructor
  · intro state
    exact (PaperTotal.gamma_triple program draw failed actor code state).1
  · intro state
    funext probe
    apply Subtype.ext
    exact (PaperTotal.gamma_triple program draw failed actor code state).2.1 probe
  · intro state
    change none = (PaperTotal.evaluate program draw failed actor code state.val).2.2.map (sem.iterator actor)
    have selected := (PaperTotal.gamma_triple program draw failed actor code state).2.2
    have terminal : MediatedRegistry.completedSelected program actor (fun input => draw input.val)
        (fun chosen input => failed chosen input.val) code state = none := by
      cases code with
      | false => rfl
      | true =>
        by_cases ready : Insertable state.val (draw state.val) (component false) (some actor) <;>
          simp [MediatedRegistry.completedSelected, program, failed, SemanticHead.evaluate, ready]
    rw [← selected, terminal]
    rfl

theorem terminal_reach (actor : Nat) (code : Bool) {iterator : Iterator G}
    (reached : Reach (sem.iterator actor code) iterator) : iterator = sem.iterator actor code := by
  induction reached with
  | root => rfl
  | continuation _ state selected ih => simp [ih, sem, meaning, embed, Iterator.next, PaperStateObservation.structural] at selected

def view : View Nat Empty := Empty.elim
def empty : R := fun _ => none
def insertedBirth : R := put empty 0 (fresh (component true) none)
def insertedBoth : R := put insertedBirth 1 (fresh (component false) none)
def birthRunning : R := mark insertedBoth 0 (.reloading true [] view)
def running : R := mark birthRunning 1 (.reloading false [] view)

theorem origin : PaperTotal.Run program draw failed empty running := by
  apply PaperTotal.Run.tail
    (PaperTotal.Run.tail
      (PaperTotal.Run.tail
        (PaperTotal.Run.tail (.refl empty) (.insert empty 0 (component true) none
          (by simp [Insertable, empty])))
        (.insert insertedBirth 1 (component false) none
          ⟨rfl, by simp, fun _ key => nomatch key⟩))
      (.begin insertedBoth 0 (fresh (component true) none) view rfl rfl (by change some _ ≠ none; simp)
        ⟨rfl, fun key => nomatch key⟩))
    (.begin birthRunning 1 (fresh (component false) none) view rfl rfl (by change some _ ≠ none; simp)
      ⟨rfl, fun key => nomatch key⟩)

def current : sem.Gamma := ⟨running, (PaperTotal.reachable_invariant program draw failed origin).1⟩

theorem birth_at (state : R) (actor child : Nat) (present : state actor ≠ none) (vacant : state child = none) :
    Land program actor true state (put state child (fresh (component false) (some actor))) (.retire child) none := by
  apply Execution.instantiate (program := program) state actor true (component false) child rfl
  exact ⟨vacant, by intro name same; cases same; exact present, fun _ key => nomatch key⟩

theorem running_draw : draw running = 2 := by
  simp [draw, drawFrom, running, birthRunning, insertedBoth, insertedBirth, empty, mark, Calculus.modify, put]

theorem first_birth_forward (actor : Nat) (present : running actor ≠ none) :
    (Tracking.forward (sem.iterator actor true).effect current).val =
      put running 2 (fresh (component false) (some actor)) := by
  have actual := birth_at running actor 2 present rfl
  have evaluated := PaperTotal.ordinary_landing program draw failed actual running_draw
  rw [(representation actor true).forward]
  change (PaperTotal.evaluate program draw failed actor true running).1 = _
  rw [evaluated]

theorem two_births_forward (first second : Nat)
    (firstPresent : running first ≠ none) (secondPresent : running second ≠ none) :
    (Tracking.forward (sem.iterator second true).effect
      (Tracking.forward (sem.iterator first true).effect current)).val =
    put (put running 2 (fresh (component false) (some first))) 3 (fresh (component false) (some second)) := by
  let intermediate := Tracking.forward (sem.iterator first true).effect current
  have before := first_birth_forward first firstPresent
  have present : intermediate.val second ≠ none := by
    change (Tracking.forward (sem.iterator first true).effect current).val second ≠ none
    rw [before]
    by_cases same : second = 2
    · simp [put, same]
    · simpa [put, same] using secondPresent
  have vacant : intermediate.val 3 = none := by rw [show intermediate.val = _ from before]; rfl
  have selected : draw intermediate.val = 3 := by
    rw [show intermediate.val = _ from before]
    simp [draw, drawFrom, put, running, birthRunning, insertedBoth, insertedBirth, empty, mark, Calculus.modify]
  have evaluated := PaperTotal.ordinary_landing program draw failed (birth_at intermediate.val second 3 present vacant) selected
  rw [(representation second true).forward]
  change (PaperTotal.evaluate program draw failed second true intermediate.val).1 = _
  rw [evaluated, before]

/-- The tempting fixed-draw birth/birth countermodel does NOT satisfy the
finer commutation hypothesis actually used by the p46/p52 proof. It therefore
cannot be advertised as a counterexample to that reading of Lemma78. -/
theorem fixed_birth_pair_rejects_finer_independence :
    ¬ PaperTransposition.Independent sem (sem.iterator 0 true) (sem.iterator 1 true) := by
  intro independent
  have compared := independent.fine _ (Generator.forward Reach.root) _ (Generator.forward Reach.root) current
  rw [two_births_forward 1 0 (by simp [running, birthRunning, insertedBoth, mark, Calculus.modify, put])
      (by simp [running, birthRunning, insertedBoth, insertedBirth, mark, Calculus.modify, put]),
    two_births_forward 0 1 (by simp [running, birthRunning, insertedBoth, insertedBirth, mark, Calculus.modify, put])
      (by simp [running, birthRunning, insertedBoth, mark, Calculus.modify, put])] at compared
  have fields := PaperStateObservation.fields sem compared 2
    (fresh (component false) (some 1)) (fresh (component false) (some 0)) rfl rfl
  cases fields.parent

end
end Cordis.PaperTranspositionExamples
