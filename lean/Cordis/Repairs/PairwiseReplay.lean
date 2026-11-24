import Cordis.Repairs.PairwiseAllocation
import Cordis.Repairs.PairwiseOperations
import Cordis.Repairs.ReplayBindingDomains
import Cordis.TypedReplayContracts

/-! The mixed forward/saved-inverse square at the same typed binding.
The coeffect's commutation witness derives definedness after the forward.
The yield witness supplies the native forward after the saved inverse. -/
namespace Cordis.Repairs.PairwiseReplay
open TypedRegistry
open PaperEffectEquations (CoeffectOperations ValueOperationWitness)
open PartialCoeffectLifting (PartialMap compose forward)
open PartialCoeffectIndependenceContracts (tableSetoid)
open PartialInverseObservation (MapRelated)
open PairwiseOperations

universe u
variable {Name Key Code : Type u} {V : Key → Type u} [DecidableEq Name] [DecidableEq Key]
variable {ops : CoeffectOperations V}
local notation "R" => Registry Name V Code
local notation "Program" => Code → Instruction Name ops Code

private theorem related_after_two_writes (observe : ∀ k, Setoid (V k)) (program : Program)
    {state : R} (owner : Name) (key : Key) (leftMid rightMid : V key) {left right : V key}
    (related : (observe key).r left right)
    (reached : WellFormed.Run (encodeProgram program) (fun _ => none) (encodeRegistry ops state))
    (recovery : ValueOperationWitness ops)
    (laws : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key) :
    letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
    StageSimulation.Related Eq
      (encodeRegistry ops (write (write state owner key (some leftMid)) owner key (some left)))
      (encodeRegistry ops (write (write state owner key (some rightMid)) owner key (some right))) := by
  letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
  simp only [encode_write, Option.map_some, Transposition.write_twice]
  have self := Transposition.reachable_self_related _ (encoded_program_callbacks ops observe program recovery laws) reached
  apply StageSimulation.write_related self owner key
  exact (TypedCoeffectReplay.packed_related (Yield := Yield ops) observe key _ _).mpr related

/-- A forward operation and an inverse captured by a prior foreign native
landing can run in both orders at a shared retained binding. The inverse
is defined after the original forward and the other order returns the same
typed outcome with a related partial capture. -/
theorem shared_operation_inverse_square (observe : ∀ k, Setoid (V k)) (program : Program)
    {state origin captured : R} {actor owner other : Name} {key : Key} {code otherCode : Code}
    {name : ops.Name key} {arg : ops.Argument key name} {input output restored : V key}
    {inverse saved : PartialMap (V key)} {outcome : ops.Outcome key name} {otherNext : Option Code}
    (action : (program code).action = .operate key name arg)
    (located : location state actor key = some (owner, input))
    (returned : (ops.operation key name arg).run input = some (output, inverse, outcome))
    (originLanding : Land program other otherCode origin captured (.operate owner key saved) otherNext)
    (applied : saved input = some restored)
    (reached : WellFormed.Run (encodeProgram program) (fun _ => none) (encodeRegistry ops state))
    (recovery : ValueOperationWitness ops)
    (laws : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key) :
    letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
    let forwardState := write state owner key (some output)
    ∃ replayed replayCapture finalValue,
      Land program actor code state forwardState (.operate owner key inverse)
        ((program code).next (.operation key name outcome)) ∧
      saved output = some finalValue ∧
      Land program actor code (undo (.operate owner key saved) state) replayed (.operate owner key replayCapture)
        ((program code).next (.operation key name outcome)) ∧
      MapRelated (observe key).r replayCapture inverse ∧
      StageSimulation.Related Eq (encodeRegistry ops replayed)
        (encodeRegistry ops (undo (.operate owner key saved) forwardState)) := by
  letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
  cases originLanding with
  | operate _ _ _ _ otherName otherArg _ earlier later _ otherOutcome _ _ oldCall =>
    have inverseGenerator : TypedReplayContracts.Generator ops key saved :=
      ⟨otherName, otherArg, .inverse earlier later _ otherOutcome oldCall⟩
    let localOp := ops.operation key name arg
    have forwardGenerator : TypedReplayContracts.Generator ops key (forward localOp) := ⟨name, arg, .forward⟩
    have forwardMade : forward localOp input = some output := by simp [forward, localOp, returned]
    obtain ⟨replayValue, replayCapture, replayCall, equalCaptures⟩ :=
      TypedReplayContracts.call_after_generator ops observe key (laws key) name arg inverseGenerator applied returned
    have afterUndo : forward localOp restored = some replayValue := by simp [forward, localOp, replayCall]
    have commutes := (TypedReplayContracts.key_laws ops observe key (laws key)).commutes
      (forward localOp) saved forwardGenerator inverseGenerator input input ((observe key).refl input)
    change Iterators.OptionRel (observe key).r (compose (forward localOp) saved input)
      (compose saved (forward localOp) input) at commutes
    rw [show compose (forward localOp) saved input = some replayValue by simp [compose, applied, afterUndo],
      show compose saved (forward localOp) input = saved output by simp [compose, forwardMade]] at commutes
    cases lastCall : saved output with
    | none => simp [lastCall, Iterators.OptionRel] at commutes
    | some finalValue =>
      have related : (observe key).r replayValue finalValue := by simpa only [lastCall, Iterators.OptionRel] using commutes
      have baseWrite := undo_operate_eq_write (table_and_route located).2 applied
      have finalWrite := undo_operate_eq_write (table_and_route (location_write_here located output)).2 lastCall
      refine ⟨write (write state owner key (some restored)) owner key (some replayValue),
        replayCapture, finalValue, .operate _ _ _ _ _ _ _ _ _ _ _ action located returned, rfl,
        ?_, equalCaptures, ?_⟩
      · rw [baseWrite]
        exact .operate _ _ _ _ _ _ _ _ _ _ _ action (location_write_here located restored) replayCall
      · dsimp only
        rw [finalWrite]
        exact related_after_two_writes observe program owner key restored output related reached recovery laws

/-- Two actual pending inverses on a retained slot can be applied in either
order. Membership by permutation selects distinct occurrences, even when
the two functions are equal. The slot history derives both partial successes
before the typed registry applies the saved inverses. -/
theorem pending_inverse_square (observe : ∀ k, Setoid (V k)) (program : Program)
    {state : R} {actor owner : Name} {key : Key} {input : V key}
    {first second : PartialMap (V key)} {pending remaining : List (PartialMap (V key))}
    (located : location state actor key = some (owner, input))
    (history : PartialReplayHistory.History (TypedReplayContracts.Generator ops key) input pending)
    (selected : ([first, second] ++ remaining).Perm pending)
    (reached : WellFormed.Run (encodeProgram program) (fun _ => none) (encodeRegistry ops state))
    (recovery : ValueOperationWitness ops)
    (laws : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key) :
    letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
    ∃ leftMid rightMid left right,
      first input = some leftMid ∧ second leftMid = some left ∧
      second input = some rightMid ∧ first rightMid = some right ∧
      StageSimulation.Related Eq
        (encodeRegistry ops (undo (.operate owner key second) (undo (.operate owner key first) state)))
        (encodeRegistry ops (undo (.operate owner key first) (undo (.operate owner key second) state))) := by
  letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
  have order : (([first] ++ [second]) ++ remaining).Perm pending := selected
  obtain ⟨left, right, firstOrder, secondOrder, related⟩ := PartialReplayHistory.pending_commute
    (TypedReplayContracts.key_laws ops observe key (laws key)) history order
  have firstComposition : compose second first input = some left := by
    simpa [PartialReplayHistory.run, compose] using firstOrder
  have secondComposition : compose first second input = some right := by
    simpa [PartialReplayHistory.run, compose] using secondOrder
  obtain ⟨leftMid, firstApplied, secondAfter⟩ := Option.bind_eq_some_iff.mp firstComposition
  obtain ⟨rightMid, secondApplied, firstAfter⟩ := Option.bind_eq_some_iff.mp secondComposition
  refine ⟨leftMid, rightMid, left, right, firstApplied, secondAfter, secondApplied, firstAfter, ?_⟩
  rw [undo_operate_eq_write (table_and_route located).2 firstApplied,
    undo_operate_eq_write (table_and_route located).2 secondApplied,
    undo_operate_eq_write (table_and_route (location_write_here located leftMid)).2 secondAfter,
    undo_operate_eq_write (table_and_route (location_write_here located rightMid)).2 firstAfter]
  exact related_after_two_writes observe program owner key leftMid rightMid related reached recovery laws

namespace Allocation
open IncarnationReplay (Capture replay)
open ReplayBindingDomains (WordDefined)
variable {Value Error : Type u}
local notation "Raw" => Calculus.Registry Name Key Value Code (Stages.Inverse Name Key Value) Error
local notation "RawProgram" => Code → Stages.Instruction Name Key Value Code Error
local notation "Captured" => Capture Name Key Value

private theorem insertable_after_replay_iff (state : Raw) (live : Name → Option Nat)
    (word : List Captured) (child : Name) (component : Calculus.Component Key Code) (parent : Option Name) :
    Calculus.Insertable (replay live word state) child component parent ↔
      Calculus.Insertable state child component parent := by
  induction word generalizing state with
  | nil => rfl
  | cons first rest ih =>
    exact (ih (first.apply live state)).trans (PairwiseAllocation.insertable_after_capture_iff state live first child component parent)

private theorem replay_through_new_stamp (state : Raw) {live : Name → Option Nat}
    (word : List Captured) (child : Name) (component : Calculus.Component Key Code) (parent : Option Name)
    (stamp : Nat) (absent : live child = none) (earlier : ∀ capture ∈ word, capture.index < stamp) :
    replay (fun name => if name = child then some stamp else live name) word
      (Calculus.put state child (Calculus.fresh component parent)) =
      Calculus.put (replay live word state) child (Calculus.fresh component parent) := by
  rw [IncarnationReplay.replay_congr_matches word _ (later := fun name => if name = child then some stamp else live name)]
  · exact IncarnationReplay.replay_put_fresh live word state child component parent absent
  · intro capture member name _
    by_cases newborn : name = child
    · subst name
      have freshStamp : stamp ≠ capture.index := Nat.ne_of_gt (earlier capture member)
      simp [absent, freshStamp]
    · simp [newborn]

/-- A successful allocation and an earlier saved word commute as actual
registry transformations. The birth keeps its original payload and draw.
Every saved inverse stays in its partial domain after the birth, and no old
retirement capture can accidentally address the newborn incarnation. -/
theorem allocation_word_square {program : RawProgram} (meaning : PartialReplayRegistry.Coeffects program)
    {before after : Raw} {actor child : Name} {code : Code} {next : Option Code}
    (landed : Stages.Land program actor code before after (.retire child) next)
    (live : Name → Option Nat) (word : List Captured) (stamp : Nat)
    (absent : live child = none) (earlier : ∀ capture ∈ word, capture.index < stamp)
    (defined : WordDefined meaning live word before) :
    let liveAfter := fun name => if name = child then some stamp else live name
    WordDefined meaning liveAfter word after ∧
      Stages.Land program actor code (replay live word before) (replay liveAfter word after) (.retire child) next := by
  cases landed with
  | instantiate _ _ _ component _ action ready =>
    refine ⟨?_, ?_⟩
    · exact WordDefined.of_same_tables meaning defined (fun owner key =>
        (Transposition.fresh_put_tables before child component (some actor) ready.1 owner key).symm)
    · dsimp only
      rw [replay_through_new_stamp before word child component (some actor) stamp absent earlier]
      exact .instantiate _ _ _ _ _ action ((insertable_after_replay_iff before live word child component (some actor)).mpr ready)

/-- Apply the allocation square at an actual cut. The native trace supplies
the capture ages, child vacancy in the live-stamp map, and definedness of
every intermediate replay of the other actor's selected saved word. -/
theorem allocation_tracked_word_square {program : RawProgram} (meaning : PartialReplayRegistry.Coeffects program)
    {last time : Nat} (trace : GuardedHistory.Trace program last) (bounded : time ≤ last)
    {after : Raw} {actor reader child : Name} {code : Code} {next : Option Code}
    (landed : Stages.Land program actor code (trace.state time) after (.retire child) next)
    {word : List Captured} (selected : word.Sublist ((trace.notes time).2 reader)) :
    let liveAfter := fun name => if name = child then some (time + 1) else (trace.notes time).1 name
    WordDefined meaning liveAfter word after ∧
      Stages.Land program actor code (replay (trace.notes time).1 word (trace.state time))
        (replay liveAfter word after) (.retire child) next := by
  have vacant : trace.state time child = none := by
    cases landed with
    | instantiate _ _ _ _ _ _ ready => exact ready.1
  have absent := (trace.births_agree time bounded child).mpr vacant
  have earlier (capture : Captured) (member : capture ∈ word) : capture.index < time + 1 :=
    Nat.lt_succ_of_le (trace.capture_origin time bounded reader capture (selected.subset member)).1
  exact allocation_word_square meaning landed (trace.notes time).1 word (time + 1) absent earlier
    (ReplayBindingDomains.saved_subword_defined trace time bounded meaning reader selected)

end Allocation

end Cordis.Repairs.PairwiseReplay
