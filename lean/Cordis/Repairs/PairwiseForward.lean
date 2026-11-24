import Cordis.Repairs.PairwiseAllocation
import Cordis.Repairs.PairwiseOperations
import Cordis.Repairs.GuardedLandingMatching
import Cordis.TypedCallbackExchange

/-! The forward/forward case of Definition 42 on a common native probe.
Both primitive heads are independently enabled. The joint birth reservation
condition decides whether those fixed choices can both run. -/
namespace Cordis.Repairs.PairwiseForward
open TypedRegistry
open PaperEffectEquations (CoeffectOperations ValueOperationWitness)
open PartialCoeffectIndependenceContracts (tableSetoid)
open PartialInverseObservation (MapRelated)
open PairwiseAllocation (DrawCompatible)
open PairwiseOperations

universe u
variable {Name Key Code : Type u} {V : Key → Type u} [DecidableEq Name] [DecidableEq Key]
variable {ops : CoeffectOperations V}
local notation "R" => Registry Name V Code
local notation "I" => Inverse Name V
local notation "Program" => Code → Instruction Name ops Code

/-- The additional check on independently enabled primitive heads. Their
actual tokens record the two draws if both instructions allocate. -/
def AllowsPair (program : Program) (first second : Code) (left right : I) : Prop :=
  match left, right with
  | .retire left, .retire right =>
    match (program first).action, (program second).action with
    | .instantiate firstChild, .instantiate secondChild => DrawCompatible left right firstChild secondChild
    | _, _ => True
  | _, _ => True

omit [DecidableEq Name] [DecidableEq Key] in
theorem AllowsPair.symm {program : Program} {leftCode rightCode : Code} {left right : I}
    (allowed : AllowsPair program leftCode rightCode left right) : AllowsPair program rightCode leftCode right left := by
  cases left <;> cases right <;> try exact True.intro
  cases leftAction : (program leftCode).action <;> cases rightAction : (program rightCode).action <;>
    simp [AllowsPair, leftAction, rightAction] at allowed ⊢
  exact allowed.symm

/-- Preserve the addressed token and compare the actual partial inverse
functions, including their domains at related probes. -/
inductive CaptureRelated (observe : ∀ key, Setoid (V key)) : I → I → Prop where
  | unit : CaptureRelated observe .unit .unit
  | restrict (owner : Name) (key : Key) : CaptureRelated observe (.restrict owner key) (.restrict owner key)
  | operate (owner : Name) (key : Key) {new old : V key → Option (V key)} :
    MapRelated (observe key).r new old → CaptureRelated observe (.operate owner key new) (.operate owner key old)
  | retire (child : Name) : CaptureRelated observe (.retire child) (.retire child)

omit [DecidableEq Name] [DecidableEq Key] in
theorem CaptureRelated.retirement {observe : ∀ key, Setoid (V key)} {new old : I} {child : Name}
    (related : CaptureRelated observe new old) (chosen : old = .retire child) : new = .retire child := by
  cases related <;> first | contradiction | exact chosen

omit [DecidableEq Name] [DecidableEq Key] in
theorem CaptureRelated.symm {observe : ∀ key, Setoid (V key)} {new old : I}
    (related : CaptureRelated observe new old) : CaptureRelated observe old new := by
  cases related with
  | unit => exact .unit
  | restrict owner key => exact .restrict owner key
  | retire child => exact .retire child
  | operate owner key maps =>
    refine .operate owner key (fun left right values => ?_)
    exact Iterators.OptionRel.mono (fun _ _ h => (observe key).symm h)
      (Iterators.OptionRel.symm (maps right left ((observe key).symm values)))

omit [DecidableEq Name] [DecidableEq Key] in
theorem CaptureRelated.trans {observe : ∀ key, Setoid (V key)} {first second third : I}
    (earlier : CaptureRelated observe first second) (later : CaptureRelated observe second third) :
    CaptureRelated observe first third := by
  cases earlier with
  | unit => exact later
  | restrict _ _ => exact later
  | retire _ => exact later
  | operate owner key firstMaps =>
    cases later
    rename_i secondMaps
    refine .operate owner key (fun left right values => ?_)
    exact @Iterators.OptionRel.trans (V key) (observe key).r (fun _ _ _ => (observe key).trans) _ _ _
      (firstMaps left left ((observe key).refl left)) (secondMaps left right values)

/-- Allocation availability after any typed primitive is the original
availability with precisely the possible new reservation checked. -/
private theorem allocation_after_foreign {program : Program} {before after : R}
    {actor other child : Name} {code foreignCode : Code} {token : I} {next : Option Code}
    {component : Calculus.Component Key Code}
    (action : (program code).action = .instantiate component)
    (ready : Insertable before child component (some actor))
    (landed : Land program other foreignCode before after token next)
    (compatible : AllowsPair program code foreignCode (.retire child) token) :
    Insertable after child component (some actor) := by
  have readyRaw := (insertable_encode_iff ops before child component (some actor)).mpr ready
  have presentRaw := readyRaw.2.1 actor rfl
  have allowed : PairwiseAllocation.AllowsDraw child component ((encodeProgram program) foreignCode).action
      (encodeInverse ops token) := by
    cases foreignAction : (program foreignCode).action <;> cases token <;>
      simp [encodeProgram, encodeInstruction, encodeAction, encodeInverse,
        PairwiseAllocation.AllowsDraw, foreignAction]
    simpa [AllowsPair, action, foreignAction] using compatible
  have afterRaw := (PairwiseAllocation.insertable_after_landing_iff presentRaw (land_encode ops landed)).mpr
    ⟨readyRaw, allowed⟩
  exact (insertable_encode_iff ops after child component (some actor)).mp afterRaw

/-- The selected primitive can run after an independently ready foreign
primitive with the original continuation. A child uses its original draw. -/
theorem rerun_after_forward (observe : ∀ key, Setoid (V key)) (program : Program)
    {before leftAfter rightAfter : R} {left right : Name} {leftCode rightCode : Code}
    {leftRow rightRow : Fiber Name V Code} {leftToken rightToken : I} {leftNext rightNext : Option Code}
    (leftFound : before left = some leftRow) (rightFound : before right = some rightRow)
    (different : left ≠ right)
    (separated : Transposition.Separated leftRow.component rightRow.component)
    (laws : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (first : Land program left leftCode before leftAfter leftToken leftNext)
    (second : Land program right rightCode before rightAfter rightToken rightNext)
    (compatible : AllowsPair program leftCode rightCode leftToken rightToken) :
    ∃ final inverse, Land program left leftCode rightAfter final inverse leftNext ∧
      CaptureRelated observe inverse leftToken := by
  cases first with
  | unit _ _ _ action =>
    exact ⟨_, .unit, .unit _ _ _ action, .unit⟩
  | provide _ _ _ row key value action found declared missing =>
    exact ⟨_, .restrict left key,
      rerun_provision_after_foreign_landing program different action found declared missing second, .restrict left key⟩
  | operate _ _ _ key name arg owner beforeValue afterValue inverse result action located returned =>
    obtain ⟨final, saved, replayed, related⟩ := rerun_after_foreign_landing observe program leftFound rightFound
      separated action located returned second (laws key)
    exact ⟨final, .operate owner key saved, replayed, .operate owner key related⟩
  | instantiate _ _ _ component child action ready =>
    exact ⟨_, .retire child, .instantiate _ _ _ _ _ action (allocation_after_foreign action ready second compatible),
      .retire child⟩

omit [DecidableEq Name] in
private theorem encode_retire_inv {token : I} {child : Name}
    (encoded : encodeInverse ops token = .retire child) : token = .retire child := by
  cases token <;> simp_all [encodeInverse]

omit [DecidableEq Name] [DecidableEq Key] in
private theorem raw_retire_inv [Setoid (Scalar ops)] {left right : Stages.Inverse Name Key (Scalar ops)}
    {child : Name} (related : StageSimulation.InverseRelated left right) (chosen : right = .retire child) :
    left = .retire child := by
  cases related <;> first | contradiction | exact chosen

/-- Both orders of two independently enabled native forward heads are
defined on the common probe under their joint draw guard. The orders
preserve each selected continuation and relate each actual partial capture.
The final encoded registries have related tables and full control fields. -/
theorem forward_square_at_probe (observe : ∀ key, Setoid (V key)) (program : Program)
    {before leftAfter rightAfter : R} {left right : Name} {leftCode rightCode : Code}
    {leftRow rightRow : Fiber Name V Code} {leftToken rightToken : I} {leftNext rightNext : Option Code}
    (leftFound : before left = some leftRow) (rightFound : before right = some rightRow)
    (different : left ≠ right)
    (separated : Transposition.Separated leftRow.component rightRow.component)
    (disjoint : WellFormed.Disjoint (encodeRegistry ops before))
    (recovery : ValueOperationWitness ops)
    (laws : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (first : Land program left leftCode before leftAfter leftToken leftNext)
    (second : Land program right rightCode before rightAfter rightToken rightNext)
    (compatible : AllowsPair program leftCode rightCode leftToken rightToken)
    (self : @StageSimulation.Related Name Key (Scalar ops) Code PUnit.{u + 1}
      (TypedCoeffectReplay.setoid observe) Eq (encodeRegistry ops before) (encodeRegistry ops before)) :
    letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
    ∃ leftThenRight rightThenLeft savedLeft savedRight,
      Land program right rightCode leftAfter leftThenRight savedRight rightNext ∧
      Land program left leftCode rightAfter rightThenLeft savedLeft leftNext ∧
      CaptureRelated observe savedLeft leftToken ∧ CaptureRelated observe savedRight rightToken ∧
      StageSimulation.Related Eq (encodeRegistry ops rightThenLeft) (encodeRegistry ops leftThenRight) := by
  letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
  obtain ⟨leftThenRight, savedRight, afterFirst, rightCapture⟩ := rerun_after_forward observe program
    rightFound leftFound (Ne.symm different) separated.symm laws second first compatible.symm
  obtain ⟨rightThenLeft, savedLeft, afterSecond, leftCapture⟩ := rerun_after_forward observe program
    leftFound rightFound different separated laws first second compatible
  have callbacks := encoded_program_callbacks ops observe program recovery laws
  have independent := encoded_program_callback_pair ops observe program laws
  have rawLeft : encodeRegistry ops before left = some (encodeFiber ops leftRow) := by simp [encodeRegistry, leftFound]
  have rawRight : encodeRegistry ops before right = some (encodeFiber ops rightRow) := by simp [encodeRegistry, rightFound]
  obtain ⟨swappedMiddle, swappedFinal, swappedUndoLeft, swappedUndoRight, firstSwap, secondSwap,
    endpoints, rightRelated, leftRelated⟩ := Transposition.landings_diamond (encodeProgram program)
      (land_encode ops first) (land_encode ops afterFirst) (encodeFiber ops leftRow) (encodeFiber ops rightRow)
      rawLeft rawRight different disjoint separated (callbacks leftCode) (callbacks rightCode)
      (independent leftCode rightCode) self
  have fixedRight : ∀ child, encodeInverse ops rightToken = .retire child → swappedUndoRight = .retire child := by
    intro child chosen
    have captured := rightCapture.retirement (encode_retire_inv chosen)
    exact raw_retire_inv rightRelated (by simp [captured, encodeInverse])
  have fixedLeft : ∀ child, encodeInverse ops savedLeft = .retire child → swappedUndoLeft = .retire child := by
    intro child chosen
    have original : leftToken = .retire child := by
      have typed := encode_retire_inv chosen
      cases leftCapture <;> first | contradiction | exact typed
    exact raw_retire_inv leftRelated (by simp [original, encodeInverse])
  have sameMiddle := (GuardedLandingMatching.landing_deterministic_at_draw (land_encode ops second) firstSwap fixedRight).1
  rw [← sameMiddle] at secondSwap
  have sameFinal := (GuardedLandingMatching.landing_deterministic_at_draw (land_encode ops afterSecond) secondSwap fixedLeft).1
  exact ⟨leftThenRight, rightThenLeft, savedLeft, savedRight, afterFirst, afterSecond, leftCapture, rightCapture,
    sameFinal ▸ endpoints⟩

/-- At an actual reachable source, the native invariants and the captured
operation witnesses supply the common probe's structural premises. -/
theorem forward_square (observe : ∀ key, Setoid (V key)) (program : Program)
    {before leftAfter rightAfter : R} {left right : Name} {leftCode rightCode : Code}
    {leftRow rightRow : Fiber Name V Code} {leftToken rightToken : I} {leftNext rightNext : Option Code}
    (leftFound : before left = some leftRow) (rightFound : before right = some rightRow)
    (different : left ≠ right)
    (separated : Transposition.Separated leftRow.component rightRow.component)
    (reached : WellFormed.Run (encodeProgram program) (fun _ => none) (encodeRegistry ops before))
    (recovery : ValueOperationWitness ops)
    (laws : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (first : Land program left leftCode before leftAfter leftToken leftNext)
    (second : Land program right rightCode before rightAfter rightToken rightNext)
    (compatible : AllowsPair program leftCode rightCode leftToken rightToken) :
    letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
    ∃ leftThenRight rightThenLeft savedLeft savedRight,
      Land program right rightCode leftAfter leftThenRight savedRight rightNext ∧
      Land program left leftCode rightAfter rightThenLeft savedLeft leftNext ∧
      CaptureRelated observe savedLeft leftToken ∧ CaptureRelated observe savedRight rightToken ∧
      StageSimulation.Related Eq (encodeRegistry ops rightThenLeft) (encodeRegistry ops leftThenRight) := by
  letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
  have disjoint := (WellFormed.run_invariants _ reached Safety.empty_parentClosed WellFormed.disjoint_empty
    ⟨Ordering.supported_empty, Ordering.local_empty⟩).2.1
  have self := Transposition.reachable_self_related _ (encoded_program_callbacks ops observe program recovery laws) reached
  exact forward_square_at_probe observe program leftFound rightFound different separated disjoint recovery laws
    first second compatible self

end Cordis.Repairs.PairwiseForward
