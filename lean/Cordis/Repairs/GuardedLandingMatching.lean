import Cordis.Repairs.GuardedCutState

/-! Derive the correspondence of two actual landings from their current
actor, code, and registry. Only a child birth can alter the live renaming. -/
namespace Cordis.Repairs.GuardedLandingMatching
open Calculus Stages GuardedHistory GuardedBirthMatching GuardedCutState LegalHistory
open IncarnationReplay (Capture advance advance_capture)
open Transposition (landedPhase)

universe u
variable {Name Key Value Code Error : Type u} [DecidableEq Name] [DecidableEq Key]
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "I" => Inverse Name Key Value
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
local notation "P" => Renaming.Permutation Name
local notation "Program" => Code → Instruction Name Key Value Code Error

/-- The equations supplied by a successful landing at its actual instruction. -/
private def LandingEquation (program : Program) (actor : Name) (code : Code)
    (before after : R) (token : I) (next : Option Code) : Prop :=
  match (program code).action with
  | .unit => after = before ∧ token = .unit ∧ next = (program code).next .unit
  | .provide key value =>
    after = write before actor key (some value) ∧ token = .restrict actor key ∧
      next = (program code).next (.value value)
  | .operate key run =>
    ∃ owner input output inverse value, location before actor key = some (owner, input) ∧
      run input = .ok (output, inverse, value) ∧ after = write before owner key (some output) ∧
      token = .operate owner key inverse ∧ next = (program code).next (.value value)
  | .instantiate component =>
    ∃ child, before child = none ∧ after = put before child (fresh component (some actor)) ∧
      token = .retire child ∧ next = (program code).next (.child child)

private theorem landing_equation {program : Program} {actor : Name} {code : Code}
    {before after : R} {token : I} {next : Option Code}
    (landed : Land program actor code before after token next) :
    LandingEquation program actor code before after token next := by
  cases landed with
  | unit _ _ _ action => simp [LandingEquation, action]
  | provide _ _ _ _ _ _ action => simp [LandingEquation, action]
  | operate _ _ _ _ _ owner input output inverse value action located returned =>
    exact (show LandingEquation _ _ _ _ _ _ _ from by
      rw [LandingEquation, action]
      exact ⟨owner, input, output, inverse, value, located, returned, rfl, rfl, rfl⟩)
  | instantiate _ _ _ _ child action ready =>
    rw [LandingEquation, action]
    exact ⟨child, ready.1, rfl, rfl, rfl⟩

/-- Native primitive success at a fixed source is deterministic once a
possible fresh draw has been fixed. The state, capture and branch follow
from the actual primitive and its call result. -/
theorem landing_deterministic_at_draw {program : Program} {actor : Name} {code : Code}
    {before left right : R} {first second : I} {next otherNext : Option Code}
    (landed : Land program actor code before left first next)
    (other : Land program actor code before right second otherNext)
    (sameDraw : ∀ child, first = .retire child → second = .retire child) :
    left = right ∧ first = second ∧ next = otherNext := by
  have original := landing_equation landed
  have paired := landing_equation other
  unfold LandingEquation at original paired
  cases action : (program code).action <;> rw [action] at original paired
  case unit =>
    obtain ⟨rfl, rfl, rfl⟩ := original
    obtain ⟨rfl, rfl, rfl⟩ := paired
    exact ⟨rfl, rfl, rfl⟩
  case provide =>
    obtain ⟨rfl, rfl, rfl⟩ := original
    obtain ⟨rfl, rfl, rfl⟩ := paired
    exact ⟨rfl, rfl, rfl⟩
  case operate =>
    obtain ⟨owner, input, output, inverse, result, located, called, rfl, rfl, rfl⟩ := original
    obtain ⟨otherOwner, otherInput, otherOutput, otherInverse, otherResult, otherLocated, otherCalled, rfl, rfl, rfl⟩ := paired
    cases Option.some.inj (located.symm.trans otherLocated)
    cases Except.ok.inj (called.symm.trans otherCalled)
    exact ⟨rfl, rfl, rfl⟩
  case instantiate =>
    obtain ⟨child, _, rfl, rfl, rfl⟩ := original
    obtain ⟨otherChild, _, rfl, rfl, rfl⟩ := paired
    cases Inverse.retire.inj (sameDraw child rfl)
    exact ⟨rfl, rfl, rfl⟩

/-- The exact condition on a fixed program's continuation for these two
successful landings. Ordinary outcomes already agree. -/
def BranchAgreement (program : Program) (code : Code) (left right : I) : Prop :=
  match left, right with
  | .retire child, .retire otherChild =>
    (program code).next (.child child) = (program code).next (.child otherChild)
  | _, _ => True

variable {program : Code → Instruction Name Key Value Code Error} {last otherLast : Nat}

/-- Pair two actual landings at related cuts of the same program. In the
birth case, choose the fresh image using the actual draws. Existing live
matches and the pre-landing projection are preserved. -/
theorem match_landings (left : Trace program last) (right : Trace program otherLast)
    {i j : Nat} (hi : i ≤ last) {p : P} {stamp : Nat → Nat} {actor : Name} {code : Code}
    (present : left.state i actor ≠ none)
    (aligned : ∀ name, (right.notes j).1 (p.toFun name) = ((left.notes i).1 name).map stamp)
    (hj : j ≤ otherLast)
    (states : Renaming.registry p (project (left.state i)) = project (right.state j))
    {l r : R} {a b : I} {next otherNext : Option Code}
    (first : Land program actor code (left.state i) l a next)
    (second : Land program (p.toFun actor) code (right.state j) r b otherNext) :
    ∃ q : P,
      (∀ name, left.state i name ≠ none → q.toFun name = p.toFun name) ∧
      (∀ name, (right.notes j).1 (q.toFun name) = ((left.notes i).1 name).map stamp) ∧
      Renaming.registry q (project l) = project r ∧ Renaming.inverse q a = b ∧
      (next = otherNext ↔ BranchAgreement program code a b) := by
  have leq := landing_equation first
  have req := landing_equation second
  unfold LandingEquation at leq req
  cases action : (program code).action <;> rw [action] at leq req
  case unit =>
    obtain ⟨rfl, rfl, rfl⟩ := leq
    obtain ⟨rfl, rfl, rfl⟩ := req
    exact ⟨p, fun _ _ => rfl, aligned, states, rfl, by simp [BranchAgreement]⟩
  case provide key value =>
    obtain ⟨rfl, rfl, rfl⟩ := leq
    obtain ⟨rfl, rfl, rfl⟩ := req
    refine ⟨p, fun _ _ => rfl, aligned, ?_, rfl, by simp [BranchAgreement]⟩
    rw [project_write, Renaming.write_eq, project_write, states]
  case operate key run =>
    obtain ⟨owner, input, output, inverse, value, locate, returned, rfl, rfl, rfl⟩ := leq
    obtain ⟨otherOwner, otherInput, otherOutput, otherInverse, otherValue, otherLocate, otherReturned,
      rfl, rfl, rfl⟩ := req
    have atOwner : some (otherOwner, otherInput) = some (p.toFun owner, input) := by
      rw [← otherLocate, ← project_location, ← states, Renaming.location_eq, project_location, locate]
      rfl
    cases (Option.some.inj atOwner)
    rw [returned] at otherReturned
    cases (Except.ok.inj otherReturned)
    refine ⟨p, fun _ _ => rfl, aligned, ?_, rfl, by simp [BranchAgreement]⟩
    rw [project_write, Renaming.write_eq, project_write, states]
  case instantiate component =>
    obtain ⟨child, freshHere, rfl, rfl, rfl⟩ := leq
    obtain ⟨otherChild, freshThere, rfl, rfl, rfl⟩ := req
    obtain ⟨q, children, newAlignment, keeps⟩ := match_fresh_draw aligned
      ((left.births_agree i hi child).mpr freshHere) ((right.births_agree j hj otherChild).mpr freshThere)
    have live (name : Name) (found : left.state i name ≠ none) : q.toFun name = p.toFun name :=
      keeps name (fun vacant => found ((left.births_agree i hi name).mp vacant))
    have namespaceEq := (rename_on_live left hi live).trans states
    refine ⟨q, live, newAlignment, ?_, congrArg Inverse.retire children, Iff.rfl⟩
    simp only [project_put, Renaming.put_eq]
    change put (Renaming.registry q (project (left.state i))) (q.toFun child)
        (Renaming.fiber q (fresh component (some actor))) =
      put (project (right.state j)) otherChild (fresh component (some (p.toFun actor)))
    rw [namespaceEq, children, Renaming.fresh_fiber, Option.map_some, live actor present]

/-- A pair of child-producing landings records the same component and
the corresponding parent at the two actual new names. -/
theorem matched_child_payload {actor otherActor child otherChild : Name} {code : Code}
    {before otherBefore after otherAfter : R} {next otherNext : Option Code}
    (first : Land program actor code before after (.retire child) next)
    (second : Land program otherActor code otherBefore otherAfter (.retire otherChild) otherNext) :
    ∃ component, after child = some (fresh component (some actor)) ∧
      otherAfter otherChild = some (fresh component (some otherActor)) := by
  cases first with
  | instantiate _ _ _ component _ firstAction _ =>
    cases second with
    | instantiate _ _ _ otherComponent _ secondAction _ =>
      have same := Action.instantiate.inj (firstAction.symm.trans secondAction)
      subst otherComponent
      exact ⟨component, by simp, by simp⟩

/-- Sufficient fixed-program contract for comparing every pair of fresh
draws. A paired landing uses only the agreement at its two actual draws. -/
def ChildContinuations (program : Program) : Prop :=
  ∀ code component, (program code).action = .instantiate component →
    ∀ child otherChild, (program code).next (.child child) = (program code).next (.child otherChild)

private theorem branch_agrees {actor otherActor : Name} {code : Code}
    {before otherBefore after otherAfter : R} {a b : I} {next otherNext : Option Code}
    (first : Land program actor code before after a next)
    (second : Land program otherActor code otherBefore otherAfter b otherNext)
    (stable : ChildContinuations program) :
    BranchAgreement program code a b := by
  cases a <;> cases b <;> try trivial
  cases first with
  | instantiate _ _ _ component _ action _ => exact stable code component action _ _

/-- An Iter or Finish determines the actual code, primitive landing, and
post-landing phase from the given trace. -/
theorem activation_landing (trace : Trace program last) {time : Nat} (bound : time < last)
    {actor : Name} (event : trace.event time = .lifecycle .iter actor ∨
      trace.event time = .lifecycle .finish actor) :
    ∃ row code word view mid token next,
      trace.state time actor = some row ∧ row.phase = .reloading code word view ∧
      Land program actor code (trace.state time) mid token next ∧
      trace.state (time + 1) = mark mid actor (landedPhase next token word view) ∧
      (next.isSome = true ↔ trace.event time = .lifecycle .iter actor) := by
  have step := (trace.step time bound).1
  generalize ending : trace.state (time + 1) = after at step ⊢
  rcases event with iter | finish
  · rw [iter] at step
    cases (show Labeled.Step program .iter actor _ _ from step) with
    | iter _ mid _ row code word view inverse next present phase target landed =>
      exact ⟨row, code, word, view, mid, inverse, some next, present, phase, landed, rfl, by simp [iter]⟩
  · rw [finish] at step
    cases (show Labeled.Step program .finish actor _ _ from step) with
    | finish _ mid _ row code word view inverse present phase target landed =>
      exact ⟨row, code, word, view, mid, inverse, none, present, phase, landed, rfl, by simp [finish]⟩

private theorem recorded_push (trace : Trace program last) {time : Nat} (bound : time < last)
    {actor : Name} (acts : trace.actor time = actor) {row : F} {code : Code} {word : List I}
    {view : View Name Key} {mid : R} {token : I} {next : Option Code}
    (present : trace.state time actor = some row) (phase : row.phase = .reloading code word view)
    (landed : Land program actor code (trace.state time) mid token next)
    (endpoint : trace.state (time + 1) = mark mid actor (landedPhase next token word view)) :
    (trace.notes (time + 1)).2 =
      fun name => if name = actor then ⟨token, time + 1⟩ :: (trace.notes time).2 name
        else (trace.notes time).2 name := by
  have push := PartialReplayRegistry.saved_after_landing program landed row present
    (landedPhase next token word view) (by cases next <;> simp [phase, landedPhase, Phase.accumulator])
  rw [(trace.step time bound).2]
  change advance (trace.state time) (trace.state (time + 1)) (trace.actor time) (time + 1)
    (trace.notes time).2 = _
  rw [acts, endpoint]
  exact advance_capture _ _ _ _ push

omit [DecidableEq Name] [DecidableEq Key] in
private theorem reloading_at_matches {l r : R} {p : P} {actor : Name} {row otherRow : F}
    (equation : Renaming.registry p (project l) = project r)
    (leftFound : l actor = some row) (rightFound : r (p.toFun actor) = some otherRow)
    {code otherCode : Code} {word otherWord : List I} {view otherView : View Name Key}
    (leftPhase : row.phase = .reloading code word view)
    (rightPhase : otherRow.phase = .reloading otherCode otherWord otherView) :
    row.component = otherRow.component ∧ code = otherCode ∧
      Renaming.view p (requiredView actor row.component.requires view) =
        requiredView (p.toFun actor) otherRow.component.requires otherView := by
  have rows := congrFun equation (p.toFun actor)
  rw [Renaming.registry_at] at rows
  have rowEq : Renaming.fiber p (projectFiber actor row) = projectFiber (p.toFun actor) otherRow := by
    simpa [project, leftFound, rightFound] using rows
  have components := congrArg Fiber.component rowEq
  change row.component = otherRow.component at components
  have phases := congrArg Fiber.phase rowEq
  simp only [projectFiber, Renaming.fiber, leftPhase, rightPhase, projectPhase, Renaming.phase, List.map_nil] at phases
  obtain ⟨codeEq, _, viewEq⟩ := Phase.reloading.inj phases
  exact ⟨components, codeEq, viewEq⟩

private theorem event_actor_eq (trace : Trace program last) {time : Nat} {actor : Name}
    (event : trace.event time = .lifecycle .iter actor ∨ trace.event time = .lifecycle .finish actor) :
    trace.actor time = actor := by
  rcases event with step | step <;> simp [Trace.actor, step, Vestigial.eventActor]

/-- Compare two actual Iter/Finish events with matched acting incarnations.
Their current code is derived from the registry, and their new notes
record the paired capture at the prescribed stamps. -/
theorem match_activations (left : Trace program last) (right : Trace program otherLast)
    {i j : Nat} (hi : i < last) (hj : j < otherLast)
    {p : P} {stamp : Nat → Nat} {actor : Name}
    (event : left.event i = .lifecycle .iter actor ∨ left.event i = .lifecycle .finish actor)
    (otherEvent : right.event j = .lifecycle .iter (p.toFun actor) ∨
      right.event j = .lifecycle .finish (p.toFun actor))
    (aligned : ∀ name, (right.notes j).1 (p.toFun name) = ((left.notes i).1 name).map stamp)
    (stepStamp : stamp (i + 1) = j + 1)
    (states : Renaming.registry p (project (left.state i)) = project (right.state j))
    (stable : ChildContinuations program) :
    ∃ (q : P) (a b : I),
      (∀ name, left.state i name ≠ none → q.toFun name = p.toFun name) ∧
      (∀ name, (right.notes j).1 (q.toFun name) = ((left.notes i).1 name).map stamp) ∧
      Renaming.registry q (project (left.state (i + 1))) = project (right.state (j + 1)) ∧
      (∀ name, (right.notes (j + 1)).1 (q.toFun name) = ((left.notes (i + 1)).1 name).map stamp) ∧
      Renaming.inverse q a = b ∧
      (left.notes (i + 1)).2 = (fun name => if name = actor then
        ⟨a, i + 1⟩ :: (left.notes i).2 name else (left.notes i).2 name) ∧
      (right.notes (j + 1)).2 = (fun name => if name = q.toFun actor then
        ⟨b, j + 1⟩ :: (right.notes j).2 name else (right.notes j).2 name) ∧
      (left.event i = .lifecycle .iter actor ↔ right.event j = .lifecycle .iter (p.toFun actor)) := by
  obtain ⟨row, code, word, view, l, a, next, found, phase, landed, endpoint, continues⟩ :=
    activation_landing left hi event
  obtain ⟨otherRow, otherCode, otherWord, otherView, r, b, otherNext,
    otherFound, otherPhase, otherLanded, otherEndpoint, otherContinues⟩ := activation_landing right hj otherEvent
  have present : left.state i actor ≠ none := by simp [found]
  have codeEq := (reloading_at_matches states found otherFound phase otherPhase).2.1
  subst otherCode
  obtain ⟨q, live, newAlignment, middle, inverses, branches⟩ :=
    match_landings left right (Nat.le_of_lt hi) present aligned (Nat.le_of_lt hj) states landed otherLanded
  have nextEq := branches.mpr (branch_agrees landed otherLanded stable)
  subst otherNext
  have actorEq := live actor present
  have sourceEq := (rename_on_live left (Nat.le_of_lt hi) live).trans states
  have ⟨components, _, views⟩ :=
    reloading_at_matches sourceEq found (by rw [actorEq]; exact otherFound) phase otherPhase
  obtain ⟨_, lp⟩ := Transposition.land_existing_table program landed actor row found
  obtain ⟨_, rp⟩ := Transposition.land_existing_table program otherLanded (p.toFun actor) otherRow otherFound
  have result : Renaming.registry q (project (left.state (i + 1))) = project (right.state (j + 1)) := by
    rw [endpoint, otherEndpoint, project_mark l actor lp, project_mark r (p.toFun actor) rp,
      Renaming.mark_eq, middle, actorEq]
    simp only [components] at views ⊢
    rw [actorEq] at views
    cases next <;> simp [landedPhase, projectPhase, Renaming.phase, views]
  have births := advance_cut left right hi hj newAlignment (fun name => by
    rw [← project_present (right.state (j + 1)), ← project_present (left.state (i + 1)),
      ← result, Renaming.registry_at]
    simp) stepStamp
  refine ⟨q, a, b, live, newAlignment, result, births, inverses,
    recorded_push left hi (event_actor_eq left event) found phase landed endpoint, ?_,
    continues.symm.trans otherContinues⟩
  rw [actorEq]
  exact recorded_push right hj (event_actor_eq right otherEvent) otherFound otherPhase otherLanded otherEndpoint

private theorem begin_and_landing_incompatible (left : Trace program last) (right : Trace program otherLast)
    {i j : Nat} (hi : i < last) (hj : j < otherLast) {p : P} {actor : Name}
    (states : Renaming.registry p (project (left.state i)) = project (right.state j))
    (opening : left.event i = .lifecycle .begin actor)
    (landing : right.event j = .lifecycle .iter (p.toFun actor) ∨
      right.event j = .lifecycle .finish (p.toFun actor)) : False := by
  obtain ⟨other, _, _, _, _, _, _, otherFound, otherPhase, _, _⟩ := activation_landing right hj landing
  have step := (left.step i hi).1
  rw [opening] at step
  generalize ending : left.state (i + 1) = after at step
  cases (show Labeled.Step program .begin actor _ _ from step) with
  | begin _ _ row view found phase _ _ =>
    have compared := congrFun states (p.toFun actor)
    rw [Renaming.registry_at] at compared
    have rowEq : Renaming.fiber p (projectFiber actor row) = projectFiber (p.toFun actor) other := by
      simpa [project, found, otherFound] using compared
    have phases := congrArg Fiber.phase rowEq
    simp [projectFiber, projectPhase, Renaming.fiber, Renaming.phase, phase, otherPhase] at phases

/-- Actual paired activations at related source cuts have the same rule.
The projected phase separates Begin from a landing. For Iter and Finish,
the code and the actual outcomes determine whether both landings continue. -/
theorem matched_activation_kind (left : Trace program last) (right : Trace program otherLast)
    {i j : Nat} (hi : i < last) (hj : j < otherLast) {p : P} {stamp : Nat → Nat} {actor : Name}
    (aligned : ∀ name, (right.notes j).1 (p.toFun name) = ((left.notes i).1 name).map stamp)
    (stepStamp : stamp (i + 1) = j + 1)
    (states : Renaming.registry p (project (left.state i)) = project (right.state j))
    (stable : ChildContinuations program)
    {kind other : Lifecycle} (first : left.event i = .lifecycle kind actor)
    (second : right.event j = .lifecycle other (p.toFun actor))
    (active : Transposition.Activation kind.rule) (otherActive : Transposition.Activation other.rule) : kind = other := by
  have classify (k : Lifecycle) (act : Transposition.Activation k.rule) : k = .begin ∨ k = .iter ∨ k = .finish := by
    cases k <;> simp [Lifecycle.rule, Transposition.Activation] at act ⊢
  rcases classify kind active with rfl | lands
  · rcases classify other otherActive with rfl | otherLands
    · rfl
    · have later : right.event j = .lifecycle .iter (p.toFun actor) ∨
          right.event j = .lifecycle .finish (p.toFun actor) := by
        rcases otherLands with rfl | rfl
        · exact .inl second
        · exact .inr second
      exact False.elim (begin_and_landing_incompatible left right hi hj states first later)
  · have earlier : left.event i = .lifecycle .iter actor ∨ left.event i = .lifecycle .finish actor := by
      rcases lands with rfl | rfl
      · exact .inl first
      · exact .inr first
    rcases classify other otherActive with rfl | otherLands
    · have reversed : Renaming.registry p.symm (project (right.state j)) = project (left.state i) := by
        rw [← states, Renaming.registry_symm]
      have before : left.event i = .lifecycle .iter (p.invFun (p.toFun actor)) ∨
          left.event i = .lifecycle .finish (p.invFun (p.toFun actor)) := by simpa using earlier
      exact False.elim (begin_and_landing_incompatible right left hj hi reversed second before)
    · have later : right.event j = .lifecycle .iter (p.toFun actor) ∨
          right.event j = .lifecycle .finish (p.toFun actor) := by
        rcases otherLands with rfl | rfl
        · exact .inl second
        · exact .inr second
      obtain ⟨_, _, _, _, _, _, _, _, _, _, agrees⟩ :=
        match_activations left right hi hj earlier later aligned stepStamp states stable
      rcases lands with rfl | rfl <;> rcases otherLands with rfl | rfl <;> simp [first, second] at agrees ⊢

end Cordis.Repairs.GuardedLandingMatching
