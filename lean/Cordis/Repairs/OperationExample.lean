import Cordis.Repairs.BoundOperationIterators

/-! A nonempty, foreign-provider operation on a native reachable registry.
The consumer increments its dependency from 10 to 11. Its captured partial
inverse restores 10, leaves the consumer row unchanged, and fails at zero.
-/
namespace Cordis.Repairs.OperationExample
open TypedRegistry BoundOperation
open PaperEffectEquations (CoeffectOperations)
open PartialInverseObservation (Operation Witnessed)

abbrev Values : Unit → Type := fun _ => Nat
abbrev State := Registry Nat Values Bool
abbrev Row := Fiber Nat Values Bool

def predecessor : Nat → Option Nat
  | 0 => none
  | n + 1 => some n

def increment : Operation Nat Unit := ⟨fun n => some (n + 1, predecessor, ())⟩

def operations : CoeffectOperations Values where
  Name _ := Unit
  Argument _ _ := Unit
  Outcome _ _ := Unit
  operation _ _ _ := increment

def program (code : Bool) : Instruction Nat operations Bool :=
  ⟨if code then .provide () 10 else .operate () () (), fun _ => none⟩
def provider : Calculus.Component Unit Bool := ⟨fun _ => false, fun _ => true, true⟩
def consumer : Calculus.Component Unit Bool := ⟨fun _ => true, fun _ => false, false⟩
def view : Calculus.View Nat Unit := fun _ => 0
def empty : State := fun _ => none
def inserted : State := put empty 0 (fresh provider none)
def begun : State := mark inserted 0 (.reloading true [] view)
def supplied : State := write begun 0 () (some 10)
def active : State := mark supplied 0 (.active [.restrict 0 ()] view)
def joined : State := put active 1 (fresh consumer none)
def ready : State := mark joined 1 (.reloading false [] view)

theorem insert_provider : Step program .insert 0 empty inserted :=
  .insert empty 0 provider none ⟨rfl, by simp, fun _ _ => trivial⟩
theorem begin_provider : Step program .begin 0 inserted begun :=
  .begin inserted 0 (fresh provider none) view rfl rfl
    ⟨rfl, fun _ required => Bool.noConfusion required⟩
theorem finish_provider : Step program .finish 0 begun active :=
  .finish begun supplied 0 { (fresh provider none : Row) with phase := .reloading true [] view }
    true [] view (.restrict 0 ()) rfl rfl
    ⟨rfl, fun _ required => Bool.noConfusion required⟩
    (.provide begun 0 true { (fresh provider none : Row) with phase := .reloading true [] view }
      () 10 rfl rfl rfl rfl)
theorem insert_consumer : Step program .insert 1 active joined := by
  apply Step.insert active 1 consumer none
  refine ⟨rfl, by simp, ?_⟩
  intro name key
  cases present : active name <;> simp [consumer]
theorem begin_consumer : Step program .begin 1 joined ready :=
  .begin joined 1 (fresh consumer none) view rfl rfl
    ⟨rfl, fun key _ => ⟨trivial, by cases key; decide⟩⟩

/-- The comparison domain is inhabited by the real five-step prefix, not an
arbitrarily assumed state satisfying a witness. -/
def input : Gamma operations 1 consumer 0 provider () := by
  have allowed := CompatibleProvision.step_allowed begin_consumer
    (CompatibleProvision.step_allowed insert_consumer
      (CompatibleProvision.step_allowed finish_provider
        (CompatibleProvision.step_allowed begin_provider
          (CompatibleProvision.step_allowed insert_provider CompatibleProvision.empty_allowed))))
  refine ⟨ready, ⟨?_, ?_, rfl⟩⟩
  · exact ⟨allowed, ⟨{ (fresh consumer none : Row) with phase := .reloading false [] view }, rfl, rfl⟩⟩
  · exact ⟨allowed, ⟨{ (fresh provider none : Row) with
        table := (fun _ => some 10)
        phase := .active [.restrict 0 ()] view }, rfl, rfl⟩⟩

def output : Gamma operations 1 consumer 0 provider () := setSlot rfl (some 11) input
def observation (_ : Unit) : Setoid Nat := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩

theorem increment_witnessed : Witnessed increment Eq := by
  constructor
  · intro before after inverse outcome called
    have same : before + 1 = after ∧ predecessor = inverse ∧ () = outcome := by
      simpa [increment] using called
    obtain ⟨rfl, rfl, rfl⟩ := same
    exact ⟨before, rfl, rfl⟩
  · intro left right equal
    subst right
    refine ⟨rfl, ?_, rfl⟩
    intro a b equal
    subst b
    change Iterators.OptionRel Eq (predecessor a) (predecessor a)
    cases predecessor a <;> first | rfl | trivial

theorem succeeds : (liftOperation rfl increment).run input =
    some (output, liftMap rfl predecessor, ()) := rfl

theorem changes_dependency : tableAt output.val 0 () = some 11 := rfl
theorem consumer_unchanged : output.val 1 = input.val 1 := rfl
theorem restores_input : liftMap rfl predecessor output = some input := by
  apply operation_exact_recovery rfl increment ?_ input output _ () succeeds
  intro before after inverse outcome called
  have same : before + 1 = after ∧ predecessor = inverse ∧ () = outcome := by
    simpa [increment] using called
  obtain ⟨rfl, rfl, rfl⟩ := same
  rfl

theorem witnessed : Witnessed (liftOperation (ops := operations) (actor := 1) (acting := consumer)
    (owner := 0) (providing := provider) (key := ()) rfl increment)
    (Observed observation (fun _ => True)) :=
  operation_witnessed observation (fun _ => True) trivial rfl increment increment_witnessed

theorem native_landing : Land program 1 false input.val output.val (.operate 0 () predecessor) none :=
  operation_is_land rfl program false () () rfl input 10 11 predecessor () rfl rfl

theorem native_inverse : undo (.operate 0 () predecessor) output.val = input.val :=
  (liftMap_agrees_undo rfl predecessor output input restores_input).symm

theorem inverse_retains_partiality : liftMap rfl predecessor (setSlot rfl (some 0) input) = none := rfl

def twoSteps : PartialIterators.Iterator (Gamma operations 1 consumer 0 provider ()) :=
  PartialIterators.stage (liftOperation rfl increment) (fun _ =>
    some (PartialIterators.stage (liftOperation rfl increment) (fun _ => none)))

theorem twoSteps_member : BoundOperationIterators.Mediated rfl twoSteps := by
  apply BoundOperationIterators.Mediated.operation () ()
  intro outcome tail chosen
  have same := Option.some.inj chosen
  subst tail
  apply BoundOperationIterators.Mediated.operation () ()
  intro outcome tail impossible
  cases impossible

theorem twoSteps_witnessed : PartialIterators.Witnessed (Observed observation (fun _ => True)) twoSteps := by
  apply BoundOperationIterators.witnessed observation (fun _ => True) trivial
    (fun _ _ => increment_witnessed) ?_ twoSteps_member
  intro name argument before after inverse outcome called
  have same : before + 1 = after ∧ predecessor = inverse ∧ () = outcome := by
    simpa [operations, increment] using called
  obtain ⟨rfl, rfl, rfl⟩ := same
  rfl

end Cordis.Repairs.OperationExample
