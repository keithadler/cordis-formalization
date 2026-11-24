import Cordis.RenamingLiteralExamples
import Cordis.ResolutionClosureBoundary
import Cordis.PaperStateObservation
import Cordis.Progress

/-! Original Lemma79 admission certificate on a six-step unit episode.
Every component has the full Definition37 identity witness on all finite rooted
Gamma states. Its head, captured inverse and terminal continuation agree on
ALL inputs with the actual unit primitive. Empty keys make provision-totality
and shared-key commutativity vacuous, not omitted assumptions.

The closed maximal interval is [2,5] in Insert/Begin/Finish/Retire/Leave/Unload.
Literal deletion retains Insert+Begin. Even additionally deleting Begin retains
only Insert. Both endpoints differ from the actual retired endpoint in a field
Equation54 explicitly preserves. The counterexample needs no interpretation of
function-field equality and no invocation of the disputed recovery theorem. -/
namespace Cordis.DeletionAdmissionBoundary
noncomputable section
open Calculus Stages Effects Iterators RenamingLiteral Indexed
open ResolutionClosureBoundary (component program view)

def s0 : R := fun _ => none
def s1 : R := put s0 0 (fresh component none)
def s2 : R := mark s1 0 (.reloading false [] view)
def s3 : R := mark s2 0 (.active [.unit] view)
def s4 : R := Calculus.retire s3 0
def s5 : R := mark s4 0 (.unloading [.unit] view)
def s6 : R := mark (Calculus.discharge Stages.undo [.unit] s5) 0 .inactive

theorem inserted : Labeled.Step program .insert 0 s0 s1 :=
  .insert _ _ _ _ ⟨rfl, by simp, by intro _ key; exact nomatch key⟩
theorem begun : Labeled.Step program .begin 0 s1 s2 :=
  .begin s1 0 (fresh component none) view rfl rfl (by change some _ ≠ none; simp) ⟨rfl, fun key => nomatch key⟩
theorem finished : Labeled.Step program .finish 0 s2 s3 :=
  .finish s2 s2 0 { (fresh component none : F) with phase := .reloading false [] view }
    false [] view .unit rfl rfl ⟨rfl, fun key => nomatch key⟩ (.unit s2 0 false rfl)
theorem retired : Labeled.Step program .retire 0 s3 s4 :=
  .retire _ _ (by intro impossible; cases impossible)
theorem left : Labeled.Step program .leave 0 s4 s5 :=
  .leave s4 0 { (fresh component none : F) with retired := true, phase := .active [.unit] view }
    [.unit] view rfl rfl (retirement_has_no_target s3 0 view)
theorem unloaded : Labeled.Step program .unload 0 s5 s6 :=
  .unload s5 0 { (fresh component none : F) with retired := true, phase := .unloading [.unit] view }
    [.unit] view rfl rfl (RenamingLiteralExamples.no_relied s5 0)

def state : Nat → R
  | 0 => s0 | 1 => s1 | 2 => s2 | 3 => s3 | 4 => s4 | 5 => s5 | _ => s6
def rule : Nat → Labeled.Rule
  | 0 => .insert | 1 => .begin | 2 => .finish | 3 => .retire | 4 => .leave | _ => .unload

def trace : Trace program s0 6 where
  state := state
  rule := rule
  actor := fun _ => 0
  start := rfl
  step := by
    intro t bound
    have cases : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl
    · exact inserted
    · exact begun
    · exact finished
    · exact retired
    · exact left
    · exact unloaded

theorem actual_run : Orchestration.Run program s0 s6 := by
  have first : Orchestration.Step program s0 s1 :=
    .insert _ _ _ ⟨rfl, by simp, by intro _ key; exact nomatch key⟩
  have second : Orchestration.Step program s1 s2 :=
    .begin s1 0 (fresh component none) view rfl rfl (by change some _ ≠ none; simp) ⟨rfl, fun key => nomatch key⟩
  have third : Orchestration.Step program s2 s3 :=
    .finish s2 s2 0 { (fresh component none : F) with phase := .reloading false [] view }
      false [] view .unit rfl rfl ⟨rfl, fun key => nomatch key⟩ (.unit s2 0 false rfl)
  have fourth : Orchestration.Step program s3 s4 := .retire _ _ (by intro impossible; cases impossible)
  have fifth : Orchestration.Step program s4 s5 :=
    .leave s4 0 { (fresh component none : F) with retired := true, phase := .active [.unit] view }
      [.unit] view rfl rfl (retirement_has_no_target s3 0 view)
  have sixth : Orchestration.Step program s5 s6 :=
    .unload s5 0 { (fresh component none : F) with retired := true, phase := .unloading [.unit] view }
      [.unit] view rfl rfl (RenamingLiteralExamples.no_relied s5 0)
  exact .step (.step (.step (.step (.step (.step (.refl _) first) second) third) fourth) fifth) sixth

theorem closed_episode : EpisodeAt trace 0 2 5 where
  positive := by decide
  ordered := by decide
  bounded := by decide
  installed := by
    intro t low high
    have cases : t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    all_goals intro absent; cases absent
  before := rfl
  after := rfl

theorem endpoint_only (name : Name) (fiber : F) (present : s6 name = some fiber) :
    name = 0 ∧ fiber = { (fresh component none : F) with retired := true } := by
  by_cases same : name = 0
  · subst name; exact ⟨rfl, (Option.some.inj present).symm⟩
  · simp [s6, s5, s4, s3, s2, s1, s0, Calculus.discharge, Stages.undo,
      mark, Calculus.modify, Calculus.retire, put, same] at present

theorem quiet : Progress.Quiet s6 := by
  intro name fiber present
  obtain ⟨rfl, rfl⟩ := endpoint_only name fiber present
  intro selected target
  cases target.1

/-- Exact Definition76 table-domain equality, at every possible fiber, not
just a test at the final state. The key type is empty. -/
theorem total_provisions (fiber : F) : ∀ key, fiber.table key ≠ none ↔ fiber.component.provides key = true :=
  fun key => nomatch key

theorem no_dependency (registry : R) (consumer provider : Name) : ¬ Progress.Depends registry consumer provider := by
  rintro ⟨_, _, key, _⟩
  exact nomatch key

/-- A concrete Equation54 interpretation shares the same full structural
Gamma, and interprets every actual program code by the admitted unit. -/
def semantics : PaperStateObservation.Semantics Name Empty Unit Code Empty where
  domain := fun state => Safety.Tree state ∧ FiniteDomain state
  iterator := fun _ _ => embed Effects.identity
  keyObservation := Empty.elim
  undo := Stages.undo
  undo_unit := fun _ => rfl
  undo_retire := fun _ _ => rfl
  undo_closed := by
    intro inverse state allowed
    cases inverse with
    | unit => exact allowed
    | restrict owner key => exact nomatch key
    | operate owner key inverse => exact nomatch key
    | retire child => exact (retireGamma child ⟨state, allowed⟩).property

theorem every_prefix_admissible (t : Nat) (bound : t ≤ 6) : semantics.domain (trace.state t) := by
  have trees : ∀ n, n ≤ 6 → Safety.Tree (trace.state n) := by
    intro n valid
    induction n with
    | zero => exact Safety.empty_tree
    | succ n ih => exact Safety.step_tree program (trace.step n (by omega)).toCalculus (ih (by omega))
  refine ⟨trees t bound, ?_⟩
  refine ⟨[0], ?_⟩
  intro name present
  by_cases same : name = 0
  · simp [same]
  · have cases : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [trace, state, s6, s5, s4, s3, s2, s1, s0, Calculus.discharge,
      Stages.undo, mark, Calculus.modify, Calculus.retire, put, same] at present

theorem semantic_entry_witness (actor : Name) (code : Code) :
    @WitnessedIterator semantics.Gamma (PaperStateObservation.base semantics) (semantics.iterator actor code) :=
  @witnessed_embed semantics.Gamma (PaperStateObservation.base semantics) Effects.identity
    (@Effects.witnessed_identity semantics.Gamma (PaperStateObservation.base semantics))

theorem no_instantiation (actor : Name) (code : Code) (before after : R) (child : Name) (next : Option Code) :
    ¬ Land program actor code before after (.retire child) next := by
  intro landed
  cases landed with
  | instantiate _ _ _ _ _ action => cases action

/-- The exact original deletion predicate for R=empty: remove own events in
[2,5]. Every event here acts on the one root. -/
def deleted (index : Nat) : Bool := decide (2 ≤ index ∧ index ≤ 5)
theorem actual_survivors : (List.range 6).filter (fun index => !deleted index) = [0,1] := rfl

/-- Either reading loses the actual external retirement, violating original
Equation54 for EVERY function-field interpretation. -/
theorem endpoint_not_related (sem : PaperStateObservation.Semantics Name Empty Unit Code Empty) :
    ¬ PaperStateObservation.Related sem s2 s6 ∧ ¬ PaperStateObservation.Related sem s1 s6 := by
  constructor
  · intro related
    have fields := PaperStateObservation.fields sem related 0
      { (fresh component none : F) with phase := .reloading false [] view }
      { (fresh component none : F) with retired := true } rfl rfl
    cases fields.retired
  · intro related
    have fields := PaperStateObservation.fields sem related 0
      (fresh component none : F) { (fresh component none : F) with retired := true } rfl rfl
    cases fields.retired

/-- Admission, original extra hypotheses and failure are inhabited by one
fixed semantic interpretation, including every actual prefix of the history. -/
theorem certified_original_scope :
    (∀ actor code, @WitnessedIterator semantics.Gamma (PaperStateObservation.base semantics)
      (semantics.iterator actor code)) ∧
    (∀ t, t ≤ 6 → semantics.domain (trace.state t)) ∧
    (∀ (fiber : F) key, fiber.table key ≠ none ↔ fiber.component.provides key = true) ∧
    (∀ actor code before after child next, ¬ Land program actor code before after (.retire child) next) ∧
    Orchestration.Run program s0 s6 ∧ EpisodeAt trace 0 2 5 ∧ Progress.Quiet s6 ∧
    (∀ (registry : R) (consumer provider : Name), ¬ Progress.Depends registry consumer provider) ∧
    (List.range 6).filter (fun index => !deleted index) = [0,1] ∧
    ¬ PaperStateObservation.Related semantics s2 s6 ∧
    ¬ PaperStateObservation.Related semantics s1 s6 :=
  ⟨semantic_entry_witness, every_prefix_admissible, total_provisions, no_instantiation,
    actual_run, closed_episode, quiet, no_dependency, actual_survivors,
    (endpoint_not_related semantics).1, (endpoint_not_related semantics).2⟩

end
end Cordis.DeletionAdmissionBoundary
