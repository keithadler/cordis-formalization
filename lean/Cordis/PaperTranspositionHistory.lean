import Cordis.PaperTranspositionAdjacent
import Cordis.PaperTotalTrace

/-! History-derived function typing for the explicit total interpretation.

An admitted component supplies its root witness and exact all-input head
representation only at named codes reached from that root. The reach relation
uses the actual evaluator and selected continuation, not equality of code
denotations. Admission concerns only entries actually introduced by a step.
It contains neither current-tail witnessing, captured-generator provenance,
whole-state typing nor any transition/commutation conclusion.

All nine rules preserve the derived invariant. In particular both Divert
alternatives and arbitrary actual cleanup words are included. The structural
Gamma wrapper obtains admissibility from the actual empty-origin trace.
The total-completion and full union-base entry-witness interpretation remain
explicit; local Definition48 interface witnessing is not silently promoted.
-/
namespace Cordis.PaperTranspositionHistory
noncomputable section
open Calculus Stages Iterators Effects PaperTransposition
universe u
variable {Name Key Value Code Error : Type u}
variable [DecidableEq Name] [DecidableEq Key] [Setoid Value]
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
local notation "I" => Inverse Name Key Value
variable (sem : PaperStateObservation.Semantics Name Key Value Code Error)
variable (model : PaperTotal.Model Name Key Value Code Error)
local instance : Setoid sem.Gamma := PaperStateObservation.base sem
set_option linter.unusedSectionVars false

/-- Named, produced-code reach, retaining the actor throughout. -/
inductive NamedReach (actor : Name) (root : Code) : Code → Prop
  | root : NamedReach actor root root
  | tail {code next} : NamedReach actor root code → (state : sem.Gamma) →
      (PaperTotal.evaluate model.program model.draw model.failed actor code state.val).2.2 = some next →
      NamedReach actor root next

/-- A component-input contract. No representation is requested outside its
own produced-code reach, even when the program contains unreachable junk. -/
structure Entry (actor : Name) (root : Code) : Prop where
  witnessed : WitnessedIterator (sem.iterator actor root)
  represented : ∀ code, NamedReach sem model actor root code →
    EvaluationRep sem model.program model.draw model.failed actor code

theorem Entry.reach {actor : Name} {root code : Code}
    (entry : Entry sem model actor root) (named : NamedReach sem model actor root code) :
    Reach (sem.iterator actor root) (sem.iterator actor code) := by
  induction named with
  | root => exact .root
  | @tail code next prior state selected ih =>
    apply Reach.continuation ih state
    rw [(entry.represented code prior).selected, selected]
    rfl

def Row (actor : Name) (fiber : F) : Prop :=
  Entry sem model actor fiber.component.entry ∧
    (∀ code stack view, fiber.phase = .reloading code stack view →
      NamedReach sem model actor fiber.component.entry code) ∧
    ∀ token ∈ fiber.phase.accumulator, PaperTranspositionObservation.GeneratedInverse sem token

def Fields (state : R) : Prop := ∀ actor fiber, state actor = some fiber → Row sem model actor fiber

theorem Fields.typed {state : R} (fields : Fields sem model state) : TypedFields sem state := by
  constructor
  · intro actor fiber present
    exact (fields actor fiber present).1.witnessed
  · intro actor fiber present code stack view phase
    have row := fields actor fiber present
    exact row.1.witnessed.reachable (row.1.reach sem model (row.2.1 code stack view phase))
  · intro actor fiber present token member
    exact (fields actor fiber present).2.2 token member

theorem Fields.heads {state : R} (fields : Fields sem model state) : CurrentHeads sem model state := by
  intro actor fiber code stack view present phase
  have row := fields actor fiber present
  have named := row.2.1 code stack view phase
  exact ⟨row.1.reach sem model named, row.1.represented code named⟩

theorem fields_empty : Fields sem model (fun _ => none : R) := by
  intro actor fiber impossible
  cases impossible

/-- Only actual newly present rows need component admission. Actual rule
frames below identify them with the external-insert or birth payload. -/
def Admissions (before after : R) : Prop :=
  ∀ actor fiber, before actor = none → after actor = some fiber →
    Entry sem model actor fiber.component.entry

theorem row_frame {actor : Name} {left right : F} (row : Row sem model actor left)
    (entry : right.component.entry = left.component.entry) (phase : right.phase = left.phase) :
    Row sem model actor right := by
  rcases row with ⟨member, reach, captured⟩
  exact ⟨by simpa only [entry] using member,
    by simpa only [entry, phase] using reach, by simpa only [phase] using captured⟩

theorem fields_modify {state : R} (fields : Fields sem model state) (actor : Name) (change : F → F)
    (entry : ∀ fiber, (change fiber).component.entry = fiber.component.entry)
    (phase : ∀ fiber, (change fiber).phase = fiber.phase) :
    Fields sem model (Calculus.modify state actor change) := by
  intro name fiber found
  by_cases same : name = actor
  · subst name
    cases old : state actor with
    | none => simp [Calculus.modify, old] at found
    | some original =>
      have equal : change original = fiber := by simpa [Calculus.modify, old] using found
      subst fiber
      exact row_frame sem model (fields actor original old) (entry original) (phase original)
  · exact fields name fiber (by simpa [Calculus.modify, same] using found)

theorem fields_insert {state : R} (fields : Fields sem model state) (actor : Name)
    (component : Component Key Code) (parent : Option Name)
    (entry : Entry sem model actor component.entry) :
    Fields sem model (put state actor (fresh component parent)) := by
  intro name fiber found
  by_cases same : name = actor
  · subst name
    have equal : fresh component parent = fiber := by simpa [put] using found
    subst fiber
    refine ⟨entry, ?_, ?_⟩
    · intro code stack view impossible
      cases impossible
    · intro token member
      cases member
  · exact fields name fiber (by simpa [put, same] using found)

theorem fields_erase {state : R} (fields : Fields sem model state) (actor : Name) :
    Fields sem model (erase state actor) := by
  intro name fiber found
  by_cases same : name = actor
  · simp [erase, same] at found
  · exact fields name fiber (by simpa [erase, same] using found)

theorem fields_mark {state : R} (fields : Fields sem model state) (actor : Name)
    (phase : Phase Name Key Code I)
    (current : ∀ fiber, state actor = some fiber → ∀ code stack view,
      phase = .reloading code stack view → NamedReach sem model actor fiber.component.entry code)
    (captured : ∀ token ∈ phase.accumulator, PaperTranspositionObservation.GeneratedInverse sem token) :
    Fields sem model (mark state actor phase) := by
  intro name fiber found
  by_cases same : name = actor
  · subst name
    cases old : state actor with
    | none => simp [mark, Calculus.modify, old] at found
    | some original =>
      have equal : {original with phase := phase} = fiber := by simpa [mark, Calculus.modify, old] using found
      subst fiber
      exact ⟨(fields actor original old).1, current original old, captured⟩
  · exact fields name fiber (by simpa [mark, Calculus.modify, same] using found)

theorem fields_undo {state : R} (fields : Fields sem model state) (token : I) :
    Fields sem model (Stages.undo token state) := by
  cases token with
  | unit => exact fields
  | restrict | operate | retire => exact fields_modify sem model fields _ _ (fun _ => rfl) (fun _ => rfl)

theorem fields_discharge {state : R} (fields : Fields sem model state) (stack : List I) :
    Fields sem model (discharge Stages.undo stack state) := by
  induction stack generalizing state with
  | nil => exact fields
  | cons token rest ih => exact ih (fields_undo sem model fields token)

theorem admissions_before_mark {before after : R} {actor : Name} {phase : Phase Name Key Code I}
    (admitted : Admissions sem model before (mark after actor phase)) : Admissions sem model before after := by
  intro name fiber absent present
  by_cases same : name = actor
  · subst name
    exact admitted actor {fiber with phase := phase} absent (by simp [mark, Calculus.modify, present])
  · exact admitted name fiber absent (by simpa [mark, Calculus.modify, same] using present)

theorem fields_landing {actor : Name} {code : Code} {before after : R} {inverse : I} {next : Option Code}
    (landed : PaperTotal.Landing model.program model.draw model.failed actor code before after inverse next)
    (fields : Fields sem model before) (admitted : Admissions sem model before after) :
    Fields sem model after := by
  rcases PaperTotal.landing_cases model.program model.draw model.failed landed with ⟨actual, _⟩ | ⟨_, rfl, _, _⟩
  · cases actual with
    | unit => exact fields
    | provide | operate => exact fields_modify sem model fields _ _ (fun _ => rfl) (fun _ => rfl)
    | instantiate _ _ _ component child action ready =>
      exact fields_insert sem model fields child component (some actor)
        (admitted child (fresh component (some actor)) ready.1 (by simp [put]))
  · exact fields

theorem landing_capture {actor : Name} {code : Code} (state : sem.Gamma)
    {stage : R} {inverse : I} {next : Option Code}
    (landed : PaperTotal.Landing model.program model.draw model.failed actor code state.val stage inverse next)
    (fiber : F) (present : state.val actor = some fiber) (stack : List I) (view : View Name Key)
    (phase : fiber.phase = .reloading code stack view) (fields : Fields sem model state.val) :
    PaperTranspositionObservation.GeneratedInverse sem inverse := by
  have row := fields actor fiber present
  have named := row.2.1 code stack view phase
  have represented := row.1.represented code named
  have current := row.1.witnessed.reachable (row.1.reach sem model named)
  refine ⟨sem.iterator actor code, current, ?_⟩
  have same : Tracking.inverse (sem.iterator actor code).effect state = PaperStateObservation.inverse sem inverse := by
    rw [represented.inverse, landed]
  rw [← same]
  exact Generator.inverse Reach.root state

theorem fields_landed_phase {actor : Name} {code : Code} (state : sem.Gamma)
    {stage : R} {inverse : I} {next : Option Code}
    (landed : PaperTotal.Landing model.program model.draw model.failed actor code state.val stage inverse next)
    (fiber : F) (present : state.val actor = some fiber) (stack : List I) (view : View Name Key)
    (phase : fiber.phase = .reloading code stack view) (fields : Fields sem model state.val)
    (admitted : Admissions sem model state.val (mark stage actor (Transposition.landedPhase next inverse stack view))) :
    Fields sem model (mark stage actor (Transposition.landedPhase next inverse stack view)) := by
  have row := fields actor fiber present
  have named := row.2.1 code stack view phase
  have captured := landing_capture sem model state landed fiber present stack view phase fields
  have old : ∀ token ∈ stack, PaperTranspositionObservation.GeneratedInverse sem token := by
    simpa only [phase, Phase.accumulator] using row.2.2
  apply fields_mark sem model (fields_landing sem model landed fields (admissions_before_mark sem model admitted)) actor
  · intro after found following tail selected newPhase
    obtain ⟨table, retained⟩ := landing_existing_table model.program model.draw model.failed landed actor fiber present
    have equal : {fiber with table := table} = after := Option.some.inj (retained.symm.trans found)
    subst after
    cases next with
    | none => cases newPhase
    | some next =>
      cases newPhase
      exact NamedReach.tail named state (by rw [landed])
  · intro token member
    have inWord : token ∈ inverse :: stack := by cases next <;> exact member
    rcases List.mem_cons.mp inWord with same | prior
    · subst token
      exact captured
    · exact old token prior

/-- The all-nine-rule preservation theorem. Admissions concern only rows
actually created by THIS step; new tails and inverses are conclusions. -/
theorem step_fields {rule : Labeled.Rule} {actor : Name} (state : sem.Gamma) {after : R}
    (step : PaperTotal.Labeled.Step model rule actor state.val after)
    (fields : Fields sem model state.val) (admitted : Admissions sem model state.val after) :
    Fields sem model after := by
  cases step with
  | insert _ actor component parent ready =>
    exact fields_insert sem model fields actor component parent
      (admitted actor (fresh component parent) ready.1 (by simp [put]))
  | retire => exact fields_modify sem model fields _ _ (fun _ => rfl) (fun _ => rfl)
  | remove => exact fields_erase sem model fields _
  | begin _ actor fiber view present phase clean target =>
    apply fields_mark sem model fields actor
    · intro current found code stack selected reloading
      have equal : fiber = current := Option.some.inj (present.symm.trans found)
      subst current
      cases reloading
      exact NamedReach.root
    · intro token member
      cases member
  | iter _ stage actor fiber code stack view inverse next present phase target landed =>
    exact fields_landed_phase sem model state landed fiber present stack view phase fields admitted
  | finish _ stage actor fiber code stack view inverse present phase target landed =>
    exact fields_landed_phase sem model state landed fiber present stack view phase fields admitted
  | divert _ stage actor fiber code stack view tail present phase changed alternative =>
    have old : ∀ token ∈ stack, PaperTranspositionObservation.GeneratedInverse sem token := by
      simpa only [phase, Phase.accumulator] using (fields actor fiber present).2.2
    rcases alternative with ⟨rfl, rfl⟩ | ⟨inverse, next, landed, rfl⟩
    · apply fields_mark sem model fields actor
      · intro current found code tail selected impossible
        cases impossible
      · exact old
    · apply fields_mark sem model (fields_landing sem model landed fields (admissions_before_mark sem model admitted)) actor
      · intro current found code tail selected impossible
        cases impossible
      · intro token member
        rcases List.mem_cons.mp member with same | prior
        · subst token
          exact landing_capture sem model state landed fiber present stack view phase fields
        · exact old token prior
  | leave _ actor fiber stack view present phase changed =>
    apply fields_mark sem model fields actor
    · intro current found code tail selected impossible
      cases impossible
    · simpa only [phase, Phase.accumulator] using (fields actor fiber present).2.2
  | unload _ actor fiber stack view present phase free =>
    apply fields_mark sem model (fields_discharge sem model fields stack) actor
    · intro current found code tail selected impossible
      cases impossible
    · intro token member
      cases member

/-- A generic internal induction, with actual admissibility supplied at each
input. The structural wrapper below DERIVES that premise from the trace. -/
theorem trace_fields {last : Nat} (trace : PaperTotal.Trace model (fun _ => none : R) last)
    (within : ∀ t, t ≤ last → sem.domain (trace.state t))
    (admitted : ∀ t, t < last → Admissions sem model (trace.state t) (trace.state (t + 1)))
    (t : Nat) (bound : t ≤ last) : Fields sem model (trace.state t) := by
  induction t with
  | zero => simpa only [trace.start] using fields_empty sem model
  | succ t ih =>
    exact step_fields sem model ⟨trace.state t, within t (by omega)⟩ (trace.step t (by omega))
      (ih (by omega)) (admitted t (by omega))

/-- Actual empty-origin history supplies structural Gamma membership. The
only semantic inputs are the component admissions at actual creation events. -/
theorem structural_trace_fields
    (meaning : Name → Code → Iterator (MediatedRegistry.Gamma Name Key Value Code Error))
    {last : Nat} (trace : PaperTotal.Trace model (fun _ => none : R) last)
    (admitted : ∀ t, t < last → Admissions (PaperStateObservation.structural meaning) model
      (trace.state t) (trace.state (t + 1))) (t : Nat) (bound : t ≤ last) :
    Fields (PaperStateObservation.structural meaning) model (trace.state t) :=
  trace_fields (PaperStateObservation.structural meaning) model trace
    (fun t bound => trace.allowed PaperTotal.empty_invariant.1 t bound) admitted t bound

end
end Cordis.PaperTranspositionHistory
