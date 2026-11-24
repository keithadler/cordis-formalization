import Cordis.Repairs.GuardedHistory
import Cordis.TypedRegistryTrace

/-! Every cut of a guarded history over the encoded program has a typed
registry. Guarded unload uses the actual typed accumulator and the live
birth stamps recorded on that same history. -/
namespace Cordis.Repairs.GuardedTypedCuts
open TypedRegistry
open PaperEffectEquations (CoeffectOperations)
open IncarnationReplay (Capture replay)

universe u
variable {Name Key Code : Type u} {V : Key → Type u} {ops : CoeffectOperations V}
variable [DecidableEq Name] [DecidableEq Key]
local notation "R" => Registry Name V Code
local notation "I" => Inverse Name V
local notation "C" => Capture Name Key (Scalar ops)

private theorem encode_capture (input : R) (live : Name → Option Nat) (capture : C)
    (token : I) (encoded : encodeInverse ops token = capture.token) :
    ∃ output : R, encodeRegistry ops output = capture.apply live (encodeRegistry ops input) := by
  obtain ⟨raw, stamp⟩ := capture
  change encodeInverse ops token = raw at encoded
  subst raw
  cases token with
  | unit => exact ⟨input, rfl⟩
  | restrict owner key => exact ⟨undo (.restrict owner key) input, encode_undo ops _ _⟩
  | operate owner key inverse => exact ⟨undo (.operate owner key inverse) input, encode_undo ops _ _⟩
  | retire child =>
    by_cases firing : live child = some stamp
    · exact ⟨retire input child, by simp [Capture.apply, encodeInverse, firing]⟩
    · exact ⟨input, by simp [Capture.apply, encodeInverse, firing]⟩

private theorem encode_replay (input : R) (live : Name → Option Nat) (word : List C)
    (encoded : ∀ capture ∈ word, ∃ token : I, encodeInverse ops token = capture.token) :
    ∃ output : R, encodeRegistry ops output = replay live word (encodeRegistry ops input) := by
  induction word generalizing input with
  | nil => exact ⟨input, rfl⟩
  | cons capture tail ih =>
    obtain ⟨token, matching⟩ := encoded capture List.mem_cons_self
    obtain ⟨middle, applied⟩ := encode_capture input live capture token matching
    obtain ⟨output, rest⟩ := ih middle (fun previous member => encoded previous (List.mem_cons_of_mem _ member))
    exact ⟨output, by simpa only [applied, replay] using rest⟩

/-- Actual trace capture words remain in the image of typed encoding, even
when a saved retirement skips a replacement occupant at its raw name. -/
theorem typed_cut {program : Code → Instruction Name ops Code} {last : Nat}
    (trace : GuardedHistory.Trace (encodeProgram program) last) (time : Nat) (bounded : time ≤ last) :
    ∃ state : R, encodeRegistry ops state = trace.state time := by
  induction time with
  | zero => exact ⟨fun _ => none, trace.start.symm⟩
  | succ time ih =>
    obtain ⟨source, encoded⟩ := ih (by omega)
    rcases GuardedHistory.transition_cases (trace.step time (by omega : time < last)).1 with
        native | ⟨actor, event, unloading⟩
    · rw [← encoded] at native
      obtain ⟨output, _, result⟩ := decode_step native
      exact ⟨output, result⟩
    · obtain ⟨row, view, present, phase, free, endpoint⟩ := unloading
      rw [← encoded] at present
      obtain ⟨typedRow, typedFound, _⟩ := encodeRegistry_some ops present
      let word := (trace.notes time).2 actor
      have saved : word.map Capture.token = typedRow.phase.accumulator.map (encodeInverse ops) := by
        have projected := trace.projects time (by omega) actor
        rw [← encoded] at projected
        cases phase : typedRow.phase <;>
          simpa [word, PartialReplayRegistry.saved, encodeRegistry, typedFound, encodeFiber, encodePhase,
            phase, Calculus.Phase.accumulator] using projected
      have tokens (capture : C) (recorded : capture ∈ word) : ∃ token : I, encodeInverse ops token = capture.token := by
        have member : capture.token ∈ word.map Capture.token := List.mem_map_of_mem recorded
        rw [saved] at member
        obtain ⟨token, _, paired⟩ := List.mem_map.mp member
        exact ⟨token, paired⟩
      obtain ⟨reverted, reached⟩ := encode_replay source (trace.notes time).1 word tokens
      exact ⟨mark reverted actor .inactive, by rw [encode_mark, reached, encoded, endpoint]; rfl⟩

end Cordis.Repairs.GuardedTypedCuts
