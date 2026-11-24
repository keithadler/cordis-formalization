import Cordis.TypedRegistrySupport
import Cordis.Results.TypedRules

/-!
Lemma 59 on a registry with dependent tables. The frozen map is evaluated
only at the actual input of its step. The resulting intermediate registry is
decoded, so the frame conclusion compares the original values at their keys.
-/
namespace Cordis.TypedRegistry

open PaperEffectEquations (CoeffectOperations)
open TypedCoeffectReplay (pack unpack)
universe u
variable {Name Key Code : Type u} {V : Key → Type u}
variable {ops : CoeffectOperations V} [DecidableEq Key]
local notation "R" => Registry Name V Code
local notation "F" => Fiber Name V Code

private theorem packedOptions_injective (key : Key) :
    Function.Injective (Option.map (pack (Value := V) (Yield := Yield ops) key)) := by
  intro left right same
  have decoded := congrArg (fun packed => packed.bind (unpack key)) same
  cases left <;> cases right <;> simp at decoded ⊢ <;> exact decoded

/-- The committed view retains only the coordinates declared by this fiber. -/
def committedAt (r : R) (name : Name) : Option (TargetView.PartialView Name Key) := do
  let fiber ← r name
  let view ← fiber.phase.committed
  pure (TargetView.mask fiber.component.requires view)

@[simp] theorem committedAt_encode (r : R) (name : Name) :
    PaperLifecycleClaims.committedAt (encodeRegistry ops r) name = committedAt r name := by
  cases found : r name <;>
    simp [PaperLifecycleClaims.committedAt, committedAt, encodeRegistry, encodeFiber, found]

private theorem stack_encode (fiber : F) :
    (encodeFiber ops fiber).phase.accumulator = fiber.phase.accumulator.map (encodeInverse ops) := by
  cases phase : fiber.phase <;> simp [encodeFiber, encodePhase, phase, Calculus.Phase.accumulator]

variable [DecidableEq Name]

/-- Each permitted application is the identity, one typed primitive, or the
discharge of the typed inverse stack stored at the named actor. -/
private theorem decode_application {program : Code → Instruction Name ops Code}
    {rule : Labeled.Rule} {actor : Name} {before : R} {after : RawRegistry Name ops Code}
    {use : RuleEvaluation.Use Name Key (Scalar ops) Code}
    (application : RuleEvaluation.Application (encodeProgram program) actor use (encodeRegistry ops before) after)
    (permitted : use.allowed rule (encodeRegistry ops before) actor) :
    ∃ middle : R, encodeRegistry ops middle = after := by
  generalize source : encodeRegistry ops before = raw at application permitted
  cases application with
  | identity r =>
    exact ⟨before, source⟩
  | iteration code r s inverse next performed =>
    subst raw
    obtain ⟨middle, _, _, result, _⟩ := land_decode ops performed
    exact ⟨middle, result⟩
  | accumulator stack r =>
    subst raw
    obtain ⟨_, rawFiber, view, found, phase⟩ := permitted
    obtain ⟨fiber, _, rfl⟩ := encodeRegistry_some ops found
    obtain ⟨typed, _, encoded⟩ := decode_unloading phase
    refine ⟨discharge typed before, ?_⟩
    rw [encode_discharge, encoded]

/-- Lemma 59 for the heterogeneous calculus. The supplied frozen trace uses
the exact encoding of the typed steps. Table equalities and membership of
the inverse which retires a child are reflected to the typed registry. -/
theorem lemma59_typed [Setoid (Scalar ops)] {program : Code → Instruction Name ops Code}
    {last : Nat} {sem : PaperStateObservation.Semantics Name Key (Scalar ops) Code (PUnit.{u + 1})}
    (trace : Trace program (fun _ => none) last)
    (run : PaperLifecycleClaims.FrozenTrace (encodeProgram program) last sem)
    (traceMeaning : run.trace = trace.encode) :
    ∀ t, t < last →
      let before := trace.state t
      let after := trace.state (t + 1)
      let actor := trace.actor t
      let rule := trace.rule t
      (∃ middle : R, encodeRegistry ops middle = (run.psi t (run.state t)).val ∧
        ∀ name key, tableAt middle name key = tableAt after name key) ∧
      (∀ owner (other acting later : F), before owner = some other → before actor = some acting →
        after owner = some later → owner ≠ actor →
        (other.table ≠ later.table → ∃ key, other.table key ≠ none ∧ acting.component.requires key = true) ∧
        ∀ key, (other.table key = none ↔ later.table key = none) ∧
          (acting.component.requires key = false → other.table key = later.table key)) ∧
      (∀ name, (committedAt before name = none ∧ committedAt after name ≠ none →
          rule = .begin ∧ actor = name) ∧
        (committedAt before name ≠ none ∧ committedAt after name = none →
          rule = .unload ∧ actor = name) ∧
        (committedAt before name ≠ none → committedAt after name ≠ none →
          committedAt before name = committedAt after name)) ∧
      (∀ stack : List (Inverse Name V),
        RuleEvaluation.Use.allowed rule (encodeRegistry ops before) actor
          (.accumulator (stack.map (encodeInverse ops))) → rule = .unload) ∧
      (∀ name (old new : F), before name = some old → after name = some new →
        (old.phase = .inactive ∧ new.phase ≠ .inactive → rule = .begin ∧ actor = name) ∧
        (old.phase ≠ .inactive ∧ new.phase = .inactive → rule = .unload ∧ actor = name)) ∧
      (∀ name (old new : F), before name = some old → after name = some new →
        old.component = new.component ∧ old.parent = new.parent ∧
        (old.retired = true → new.retired = true) ∧
        (old.retired ≠ new.retired → new.retired = true ∧
          ((rule = .retire ∧ actor = name) ∨
            (rule = .unload ∧ ∃ source, before actor = some source ∧
              Inverse.retire name ∈ source.phase.accumulator)))) := by
  intro t bounded
  dsimp only
  have claims := Results.lemma59 run t bounded
  dsimp only at claims
  rw [traceMeaning] at claims
  rcases claims with ⟨tables, frame, committed, accumulatorRule, boundaries, metadata⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have application := run.applied t bounded
    rw [traceMeaning] at application
    obtain ⟨use, applied, permitted, _⟩ := application
    obtain ⟨middle, result⟩ := decode_application applied permitted
    refine ⟨middle, result, ?_⟩
    intro name key
    have comparison := tables name key
    change StageRecovery.tableAt (run.psi t (run.state t)).val name key =
      StageRecovery.tableAt (encodeRegistry ops (trace.state (t + 1))) name key at comparison
    rw [← result, encode_tableAt, encode_tableAt] at comparison
    exact packedOptions_injective (ops := ops) key comparison
  · intro owner other acting later earlier actorPresent laterPresent different
    obtain ⟨changed, outside⟩ := frame owner _ _ _
      (encode_row earlier) (encode_row actorPresent) (encode_row laterPresent) different
    constructor
    · intro changedTable
      have rawChanged : (encodeFiber ops other).table ≠ (encodeFiber ops later).table := by
        intro equality
        apply changedTable
        funext key
        exact packedOptions_injective (ops := ops) key (congrFun equality key)
      obtain ⟨key, occupied, required⟩ := changed rawChanged
      exact ⟨key, fun absent => occupied (Option.map_eq_none_iff.mpr absent), required⟩
    · intro key
      obtain ⟨domain, values⟩ := outside key
      refine ⟨?_, fun absent => packedOptions_injective (ops := ops) key (values absent)⟩
      simpa only [encodeFiber, Option.map_eq_none_iff] using domain
  · intro name
    simpa only [Trace.encode, committedAt_encode, PaperRemainingClaims.isRuleAt] using committed name
  · intro stack permitted
    exact accumulatorRule (stack.map (encodeInverse ops)) permitted
  · intro name old new present later
    obtain ⟨appears, disappears⟩ := boundaries name _ _ (encode_row present) (encode_row later)
    simpa only [Trace.encode, encodeFiber, ne_eq, encodePhase_inactive, PaperRemainingClaims.isRuleAt] using
      And.intro appears disappears
  · intro name old new present later
    obtain ⟨component, parent, monotone, origin⟩ := metadata name _ _
      (encode_row present) (encode_row later)
    refine ⟨component, parent, monotone, ?_⟩
    intro changed
    obtain ⟨retired, direct | ⟨unloaded, raw, found, member⟩⟩ := origin changed
    · exact ⟨retired, .inl direct⟩
    · obtain ⟨source, sourceAt, rfl⟩ := encodeRegistry_some ops found
      rw [stack_encode] at member
      obtain ⟨token, captured, represented⟩ := List.mem_map.mp member
      have identifies : token = .retire name := encodeInverse_injective ops represented
      exact ⟨retired, .inr ⟨unloaded, source, sourceAt, identifies ▸ captured⟩⟩

private theorem committedAt_step_stable {program : Code → Instruction Name ops Code}
    {rule : Labeled.Rule} {actor : Name} {before after : R}
    (step : Step program rule actor before after) (name : Name)
    (installedBefore : viewAt before name ≠ none) (installedAfter : viewAt after name ≠ none) :
    committedAt before name = committedAt after name := by
  have raw := (encode_step step).toCalculus
  have fields := Frame.step_stable (encodeProgram program) raw
  have views := Ordering.step_views_stable (encodeProgram program) raw
  cases previous : before name with
  | none => simp [viewAt, previous] at installedBefore
  | some old =>
    cases current : after name with
    | none => simp [viewAt, current] at installedAfter
    | some new =>
      cases previousView : old.phase.committed with
      | none => simp [viewAt, previous, previousView] at installedBefore
      | some oldView =>
        cases currentView : new.phase.committed with
        | none => simp [viewAt, current, currentView] at installedAfter
        | some newView =>
          have oldAt := encode_row (ops := ops) previous
          have newAt := encode_row (ops := ops) current
          have sameComponent := (fields name _ _ oldAt newAt).1
          have sameView := views name _ _ oldView newView oldAt newAt
            (by simpa [encodeFiber] using previousView) (by simpa [encodeFiber] using currentView)
          change old.component = new.component at sameComponent
          simp [committedAt, previous, current, previousView, currentView, sameComponent, sameView]

/-- Lemma 59(2): the committed view is constant at every index of an
installed episode, including an episode still open at the end of a trace. -/
theorem lemma59_episode_constancy {program : Code → Instruction Name ops Code}
    {last : Nat} {trace : Trace program (fun _ => none) last} {name : Name} {first stop : Nat}
    (episode : EpisodePrefix trace name first stop) :
    ∀ t, first ≤ t → t ≤ stop → committedAt (trace.state t) name = committedAt (trace.state first) name := by
  intro t lower upper
  induction t with
  | zero =>
    have startsAtZero : first = 0 := Nat.eq_zero_of_le_zero lower
    rw [startsAtZero]
  | succ t ih =>
    by_cases atStart : t + 1 = first
    · rw [atStart]
    · have prior : first ≤ t := by omega
      have still : t ≤ stop := by omega
      have bounded : t < last := by have := episode.bounded; omega
      have stable := committedAt_step_stable (trace.step t bounded) name
        (episode.installed t prior still) (episode.installed (t + 1) lower upper)
      exact stable.symm.trans (ih prior still)

namespace IdentityFinish

abbrev Values : Empty → Type := fun _ => Unit

def operations : CoeffectOperations Values where
  Name key := nomatch key
  Argument key := nomatch key
  Outcome key := nomatch key
  operation key := nomatch key

private abbrev State := Registry Unit Values Unit

def program : Unit → Instruction Unit operations Unit := fun _ => ⟨.unit, fun _ => none⟩

private def component : Calculus.Component Empty Unit := ⟨fun _ => false, fun _ => false, ()⟩
private def empty : State := fun _ => none
private def view : Calculus.View Unit Empty := fun key => nomatch key
private def inserted : State := put empty () (fresh component none)
private def reloadingRow : Fiber Unit Values Unit :=
  {fresh component none with phase := .reloading () [] view}
private def reloading : State := mark inserted () (.reloading () [] view)
private def finished : State := mark reloading () (.active [.unit] view)

private theorem beginTarget : Target inserted () view := by
  refine ⟨rfl, ?_⟩
  exact fun key => nomatch key

private theorem finishTarget : Target reloading () view := by
  refine ⟨rfl, ?_⟩
  exact fun key => nomatch key

/-- The empty-origin trace inserts a root, begins activation, and applies
its terminal unit effect at L-Finish. -/
def trace : Trace program empty 3 where
  state
    | 0 => empty
    | 1 => inserted
    | 2 => reloading
    | _ => finished
  rule
    | 0 => .insert
    | 1 => .begin
    | _ => .finish
  actor _ := ()
  start := rfl
  step := by
    intro t bounded
    have indices : t = 0 ∨ t = 1 ∨ t = 2 := by omega
    rcases indices with rfl | rfl | rfl
    · exact .insert empty () component none ⟨rfl, by simp, fun _ key => nomatch key⟩
    · exact .begin inserted () (fresh component none) view rfl rfl beginTarget
    · exact .finish reloading reloading () reloadingRow () [] view .unit rfl rfl finishTarget (.unit _ _ _ rfl)

private theorem finish_revision_identity : trace.frozenRevision 2 (by decide) = id := by
  obtain ⟨use, middle, raw, _, application, permitted, _, _, _, represented⟩ :=
    Classical.choose_spec (exists_frozen_revision (trace.step 2 (by decide)))
  have ordinary : raw = id := by
    cases application with
    | identity => rfl
    | iteration landing =>
      cases landing with
      | unit => rfl
      | provide _ key => exact nomatch key
      | operate key => exact nomatch key
      | instantiate _ _ action _ =>
        change Stages.Action.unit = .instantiate _ at action
        cases action
    | accumulator =>
      have impossible : Labeled.Rule.finish = .unload := permitted.1
      cases impossible
  funext input
  apply encodeRegistry_injective operations
  have meaning := represented input
  rwa [ordinary] at meaning

end IdentityFinish

/-- The extensional reading of Lemma 59(3) is false. The selected map of
a unit L-Finish is identity, just as the empty accumulator in its source
state is. The trace still selects the iteration and its label is L-Finish. -/
theorem lemma59_extensional_counterexample :
    ∃ (trace : Trace IdentityFinish.program (fun _ => none) 3)
      (t : Nat) (bounded : t < 3) (source : Fiber Unit IdentityFinish.Values Unit),
      trace.state t (trace.actor t) = some source ∧
      trace.rule t = .finish ∧
      trace.frozenRevision t bounded = discharge source.phase.accumulator ∧
      trace.rule t ≠ .unload :=
  ⟨IdentityFinish.trace, 2, by decide, _, rfl, rfl, IdentityFinish.finish_revision_identity, by decide⟩

end Cordis.TypedRegistry
