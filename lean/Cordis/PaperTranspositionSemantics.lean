import Cordis.PaperTranspositionPhases
import Cordis.PaperStateObservation

/-! The two observations used in the paper's transposition proof.

The proof of Theorem68 on p46 explicitly reads Def42(1)'s commutation at the
finer Equation54. Def65(2)'s yielded inverse/continuation agreement remains at
Definition34's original table base, which is also the base of Equation54's
function fields. We record this convention explicitly instead of installing a
finer Setoid or assuming reflexivity of arbitrary function-valued states.

`EvaluationRep` is exact all-input forward, captured-map and selected-code
representation. It contains neither witness, independence nor a transition
conclusion. The main lemma extracts the primitive exchange observations from
the original generated-map/yield hypotheses; these observations are not
supplied separately as an assumed diamond. The completion-family and no-control
read boundaries in PaperTranspositionPhases remain explicit. -/
namespace Cordis.PaperTransposition
noncomputable section
open Calculus Stages Iterators Effects StageRecovery
universe u
variable {Name Key Value Code Error : Type u}
variable [DecidableEq Name] [DecidableEq Key] [Setoid Value]
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "I" => Inverse Name Key Value
variable (sem : PaperStateObservation.Semantics Name Key Value Code Error)
local instance : Setoid sem.Gamma := PaperStateObservation.base sem
set_option linter.unusedSectionVars false

structure EvaluationRep (program : Code → Instruction Name Key Value Code Error)
    (draw : R → Name) (failed : Code → R → Option (Outcome Name Value))
    (actor : Name) (code : Code) : Prop where
  forward : ∀ state : sem.Gamma,
    (Tracking.forward (sem.iterator actor code).effect state).val =
      (PaperTotal.evaluate program draw failed actor code state.val).1
  inverse : ∀ state : sem.Gamma,
    Tracking.inverse (sem.iterator actor code).effect state =
      PaperStateObservation.inverse sem (PaperTotal.evaluate program draw failed actor code state.val).2.1
  selected : ∀ state : sem.Gamma,
    (sem.iterator actor code).next state =
      (PaperTotal.evaluate program draw failed actor code state.val).2.2.map (sem.iterator actor)

/-- Definition42's generators, with the p46 finer commutation convention only.
The named-component observation of Definition65 is not weakened or contradicted
here; the finer endpoint relation already checks every created entry field. -/
structure Independent (first second : Iterator sem.Gamma) : Prop where
  original : Iterators.Independent first second
  fine : ∀ f, Generator first f → ∀ g, Generator second g → ∀ state,
    PaperStateObservation.Related sem (f (g state)).val (g (f state)).val

theorem evaluation_yield (program : Code → Instruction Name Key Value Code Error)
    (draw : R → Name) (failed : Code → R → Option (Outcome Name Value))
    (actor : Name) (code : Code) (representation : EvaluationRep sem program draw failed actor code)
    (before after : sem.Gamma) (yielded : YieldRelated (sem.iterator actor code) before after) :
    Effects.Related
      (PaperStateObservation.inverse sem (PaperTotal.evaluate program draw failed actor code before.val).2.1)
      (PaperStateObservation.inverse sem (PaperTotal.evaluate program draw failed actor code after.val).2.1) ∧
    OptionRel (PaperStateObservation.CodeRelated sem actor)
      (PaperTotal.evaluate program draw failed actor code before.val).2.2
      (PaperTotal.evaluate program draw failed actor code after.val).2.2 := by
  refine ⟨?_, ?_⟩
  · have maps := yielded.1
    change Effects.Related (Tracking.inverse (sem.iterator actor code).effect before)
      (Tracking.inverse (sem.iterator actor code).effect after) at maps
    simpa only [representation.inverse] using maps
  · have tails := yielded.2
    rw [representation.selected, representation.selected] at tails
    cases a : (PaperTotal.evaluate program draw failed actor code before.val).2.2 <;>
      cases b : (PaperTotal.evaluate program draw failed actor code after.val).2.2 <;>
      simp_all only [Option.map_none, Option.map_some, OptionRel, PaperStateObservation.CodeRelated]

/-- The actual current heads need only be in the Def40 reach of the two
independent component iterators. All three observations follow from that
independence and the evaluator representation, not from a supplied swapped
execution or a claimed endpoint relation. -/
theorem evaluated_pair (program : Code → Instruction Name Key Value Code Error)
    (draw : R → Name) (failed : Code → R → Option (Outcome Name Value))
    (first second : Name) (firstCode secondCode : Code)
    (firstRoot secondRoot : Iterator sem.Gamma)
    (independent : Independent sem firstRoot secondRoot)
    (firstReached : Reach firstRoot (sem.iterator first firstCode))
    (secondReached : Reach secondRoot (sem.iterator second secondCode))
    (firstRep : EvaluationRep sem program draw failed first firstCode)
    (secondRep : EvaluationRep sem program draw failed second secondCode)
    (state : sem.Gamma) :
    let firstState := Tracking.forward (sem.iterator first firstCode).effect state
    let secondState := Tracking.forward (sem.iterator second secondCode).effect state
    PaperStateObservation.Related sem
      (PaperTotal.evaluate program draw failed first firstCode secondState.val).1
      (PaperTotal.evaluate program draw failed second secondCode firstState.val).1 ∧
    (Effects.Related
      (PaperStateObservation.inverse sem (PaperTotal.evaluate program draw failed first firstCode secondState.val).2.1)
      (PaperStateObservation.inverse sem (PaperTotal.evaluate program draw failed first firstCode state.val).2.1) ∧
      OptionRel (PaperStateObservation.CodeRelated sem first)
        (PaperTotal.evaluate program draw failed first firstCode secondState.val).2.2
        (PaperTotal.evaluate program draw failed first firstCode state.val).2.2) ∧
    (Effects.Related
      (PaperStateObservation.inverse sem (PaperTotal.evaluate program draw failed second secondCode firstState.val).2.1)
      (PaperStateObservation.inverse sem (PaperTotal.evaluate program draw failed second secondCode state.val).2.1) ∧
      OptionRel (PaperStateObservation.CodeRelated sem second)
        (PaperTotal.evaluate program draw failed second secondCode firstState.val).2.2
        (PaperTotal.evaluate program draw failed second secondCode state.val).2.2) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · have maps := independent.fine _ (.forward firstReached) _ (.forward secondReached) state
    simpa only [firstRep.forward, secondRep.forward] using maps
  · exact evaluation_yield sem program draw failed first firstCode firstRep _ _
      (independent.original.left_yield _ firstReached _ (.forward secondReached) state)
  · exact evaluation_yield sem program draw failed second secondCode secondRep _ _
      (independent.original.right_yield _ secondReached _ (.forward firstReached) state)

theorem landed_phases_related (actor : Name) (required : Key → Bool)
    {leftNext rightNext : Option Code} {leftInverse rightInverse : I}
    (next : OptionRel (PaperStateObservation.CodeRelated sem actor) leftNext rightNext)
    (inverses : Effects.Related (PaperStateObservation.inverse sem leftInverse)
      (PaperStateObservation.inverse sem rightInverse))
    (stack : List I) (old : PaperStateObservation.AccumulatorRelated sem stack stack)
    (view : View Name Key) :
    PaperStateObservation.PhaseRelated sem actor required
      (Transposition.landedPhase leftNext leftInverse stack view)
      (Transposition.landedPhase rightNext rightInverse stack view) := by
  cases leftNext <;> cases rightNext <;> simp_all only [OptionRel]
  · exact .active (PaperStateObservation.accumulator_cons sem inverses old) (fun _ _ => rfl)
  · exact .reloading next (PaperStateObservation.accumulator_cons sem inverses old) (fun _ _ => rfl)

theorem landed_rules_equal {actor : Name} {left right : Option Code}
    (next : OptionRel (PaperStateObservation.CodeRelated sem actor) left right) :
    Transposition.landedRule left = Transposition.landedRule right := by
  cases left <;> cases right <;> simp_all [OptionRel, Transposition.landedRule]

end
end Cordis.PaperTransposition
