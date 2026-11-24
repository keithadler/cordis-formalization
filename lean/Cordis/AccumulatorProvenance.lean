import Cordis.IndexedTrace
import Cordis.InterleavedRecovery

/-!
Captured callback provenance for the actual nine-rule calculus. The accumulator
invariant records which successful primitive result produced each operation
inverse. It is derived from an empty registry, including divert and unload;
it is not an assumption that the desired recovery equation already holds.
-/
namespace Cordis.AccumulatorProvenance
open Calculus Stages StageRecovery InterleavedRecovery
universe u
variable {Name Key Value Code Error : Type u}
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
variable [DecidableEq Name] [DecidableEq Key]
set_option linter.unusedSectionVars false

def Accumulators (predicate : Inverse Name Key Value → Prop) (r : R) : Prop :=
  ∀ actor fiber, r actor = some fiber → ∀ inverse ∈ fiber.phase.accumulator, predicate inverse

theorem accumulators_empty (predicate : Inverse Name Key Value → Prop) :
    Accumulators predicate (fun _ => none : R) := by
  intro actor fiber present
  contradiction

theorem modify_accumulators (predicate : Inverse Name Key Value → Prop)
    (r : R) (actor : Name) (change : F → F)
    (phase : ∀ f, (change f).phase = f.phase) (old : Accumulators predicate r) :
    Accumulators predicate (Calculus.modify r actor change) := by
  intro n f present i member
  by_cases eq : n = actor
  · subst n
    cases before : r actor with
    | none => simp [Calculus.modify, before] at present
    | some entry =>
      have same : change entry = f := Option.some.inj (by simpa [Calculus.modify, before] using present)
      subst f
      exact old actor entry before i (by simpa [phase] using member)
  · exact old n f (by simpa [Calculus.modify, eq] using present) i member

theorem insert_accumulators (predicate : Inverse Name Key Value → Prop)
    (r : R) (actor : Name) (component : Component Key Code) (parent : Option Name)
    (old : Accumulators predicate r) :
    Accumulators predicate (put r actor (fresh component parent)) := by
  intro n f present i member
  by_cases eq : n = actor
  · subst n
    have same : fresh component parent = f := Option.some.inj (by simpa [put] using present)
    simp [← same, fresh, Phase.accumulator] at member
  · exact old n f (by simpa [put, eq] using present) i member

theorem erase_accumulators (predicate : Inverse Name Key Value → Prop)
    (r : R) (actor : Name) (old : Accumulators predicate r) :
    Accumulators predicate (erase r actor) := by
  intro n f present i member
  by_cases eq : n = actor
  · simp [erase, eq] at present
  · exact old n f (by simpa [erase, eq] using present) i member

theorem mark_accumulators (predicate : Inverse Name Key Value → Prop)
    (r : R) (actor : Name) (phase)
    (new : ∀ inverse ∈ phase.accumulator, predicate inverse)
    (old : Accumulators predicate r) : Accumulators predicate (mark r actor phase) := by
  intro n f present i member
  by_cases eq : n = actor
  · subst n
    cases before : r actor with
    | none => simp [mark, Calculus.modify, before] at present
    | some entry =>
      have same : { entry with phase := phase } = f :=
        Option.some.inj (by simpa [mark, Calculus.modify, before] using present)
      subst f
      exact new i member
  · exact old n f (by simpa [mark, Calculus.modify, eq] using present) i member

theorem land_accumulators (predicate : Inverse Name Key Value → Prop)
    (program : Code → Instruction Name Key Value Code Error)
    {actor : Name} {code : Code} {r s : R} {i : Inverse Name Key Value} {next : Option Code}
    (land : Land program actor code r s i next) (old : Accumulators predicate r) :
    Accumulators predicate s := by
  cases land with
  | unit => exact old
  | provide => exact modify_accumulators _ _ _ _ (fun _ => rfl) old
  | operate => exact modify_accumulators _ _ _ _ (fun _ => rfl) old
  | instantiate => exact insert_accumulators _ _ _ _ _ old

theorem undo_accumulators (predicate : Inverse Name Key Value → Prop)
    (r : R) (i : Inverse Name Key Value) (old : Accumulators predicate r) :
    Accumulators predicate (Stages.undo i r) := by
  cases i with
  | unit => exact old
  | restrict => exact modify_accumulators _ _ _ _ (fun _ => rfl) old
  | operate => exact modify_accumulators _ _ _ _ (fun _ => rfl) old
  | retire => exact modify_accumulators _ _ _ _ (fun _ => rfl) old

theorem discharge_accumulators (predicate : Inverse Name Key Value → Prop)
    (r : R) (a : List (Inverse Name Key Value)) (old : Accumulators predicate r) :
    Accumulators predicate (discharge Stages.undo a r) := by
  induction a generalizing r with
  | nil => exact old
  | cons i rest ih => exact ih _ (undo_accumulators predicate r i old)

def LandingProperty (program : Code → Instruction Name Key Value Code Error)
    (predicate : Inverse Name Key Value → Prop) : Prop :=
  ∀ actor code r s i next, Land program actor code r s i next → predicate i

theorem step_accumulators (predicate : Inverse Name Key Value → Prop)
    (program : Code → Instruction Name Key Value Code Error) (landing : LandingProperty program predicate)
    {r s : R} (step : Calculus.Step (Land program) Stages.undo r s)
    (old : Accumulators predicate r) : Accumulators predicate s := by
  cases step with
  | insert => exact insert_accumulators _ _ _ _ _ old
  | retire => exact modify_accumulators _ _ _ _ (fun _ => rfl) old
  | remove => exact erase_accumulators _ _ _ old
  | begin n f v present _ _ _ =>
    exact mark_accumulators predicate r n _ (by simp [Phase.accumulator]) old
  | iter s n f c a v i next present phase _ land =>
    apply mark_accumulators predicate s n _ ?_ (land_accumulators predicate program land old)
    intro inv member
    rcases List.mem_cons.mp member with eq | prior
    · subst inv; exact landing n c r s i (some next) land
    · exact old n f present inv (by simpa [phase, Phase.accumulator] using prior)
  | finish s n f c a v i present phase _ land =>
    apply mark_accumulators predicate s n _ ?_ (land_accumulators predicate program land old)
    intro inv member
    rcases List.mem_cons.mp member with eq | prior
    · subst inv; exact landing n c r s i none land
    · exact old n f present inv (by simpa [phase, Phase.accumulator] using prior)
  | divert s n f c a v tail present phase _ alternative =>
    rcases alternative with ⟨same, nil⟩ | ⟨i, next, land, single⟩
    · subst s tail
      apply mark_accumulators predicate r n _ ?_ old
      simpa [phase, Phase.accumulator] using old n f present
    · subst tail
      apply mark_accumulators predicate s n _ ?_ (land_accumulators predicate program land old)
      intro inv member
      rcases List.mem_cons.mp member with eq | prior
      · subst inv; exact landing n c r s i next land
      · exact old n f present inv (by simpa [phase, Phase.accumulator] using prior)
  | leave n f a v present phase _ =>
    apply mark_accumulators predicate r n _ ?_ old
    simpa [phase, Phase.accumulator] using old n f present
  | unload n f a v present phase _ =>
    exact mark_accumulators predicate _ n _ (by simp [Phase.accumulator])
      (discharge_accumulators predicate r a old)

theorem reachable_accumulators (predicate : Inverse Name Key Value → Prop)
    (program : Code → Instruction Name Key Value Code Error) (landing : LandingProperty program predicate)
    {r : R} (run : WellFormed.Run program (fun _ => none) r) : Accumulators predicate r := by
  have preserves : ∀ {s t : R}, WellFormed.Run program s t → Accumulators predicate s →
      Accumulators predicate t := by
    intro s t steps
    induction steps with
    | refl => exact id
    | step _ step ih => exact fun h => step_accumulators predicate program landing step (ih h)
  exact preserves run (accumulators_empty predicate)

/-- An operation inverse must be an actual successful result of one program
primitive at this exact key. No inverse is manufactured for an error result. -/
def Captured (program : Code → Instruction Name Key Value Code Error) :
    Inverse Name Key Value → Prop
  | .operate _ key inverse => ∃ code run before after result,
      (program code).action = .operate key run ∧ run before = .ok (after, inverse, result)
  | _ => True

theorem land_captured (program : Code → Instruction Name Key Value Code Error) :
    LandingProperty program (Captured program) := by
  intro actor code r s i next land
  cases land with
  | unit => trivial
  | provide => trivial
  | instantiate => trivial
  | operate _ _ code key run owner before after inverse result action _ returned =>
    exact ⟨code, run, before, after, result, action, returned⟩

theorem reachable_captured (program : Code → Instruction Name Key Value Code Error)
    {r : R} (run : WellFormed.Run program (fun _ => none) r) : Accumulators (Captured program) r :=
  reachable_accumulators (Captured program) program (land_captured program) run

section Observation
variable [Setoid Value]

/-- A primitive callback as a Definition44 operation. Failure remains visible
in the outcome even though the failed state-map extension is identity. -/
def callbackOperation (run : Value → Except Error (Value × (Value → Value) × Value)) :
    Independence.Operation Value (Except Error Value) where
  effect := ⟨fun value => match run value with
    | .error _ => (value, id)
    | .ok (after, inverse, _) => (after, inverse)⟩
  outcome := fun value => match run value with
    | .error error => .error error
    | .ok (_, _, result) => .ok result

theorem captured_respects (program : Code → Instruction Name Key Value Code Error)
    (witnesses : OperationWitnesses program) (i : Inverse Name Key Value)
    (captured : Captured program i) : InverseRespects i := by
  cases i with
  | unit => trivial
  | restrict => trivial
  | retire => trivial
  | operate owner key inverse =>
    obtain ⟨code, run, before, after, result, action, returned⟩ := captured
    exact (witnesses code key run action before after inverse result returned).2

end Observation
end Cordis.AccumulatorProvenance
