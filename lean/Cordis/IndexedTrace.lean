import Cordis.TableFrame

/-! Finite, indexed traces of the actual nine labeled rules. The initial
registry is a parameter: lifecycle-only suffixes need not start empty. Empty
origin supplies reachable invariants separately, rather than assuming them in
the step relation. Indices beyond `last` carry no semantic obligation. -/
namespace Cordis.Indexed
open Calculus Stages
universe u
variable {Name Key Value Code Error : Type u}
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
variable [DecidableEq Name] [DecidableEq Key]

structure Trace (program : Code → Instruction Name Key Value Code Error)
    (initial : R) (last : Nat) where
  state : Nat → R
  rule : Nat → Labeled.Rule
  actor : Nat → Name
  start : state 0 = initial
  step : ∀ t, t < last → Labeled.Step program (rule t) (actor t) (state t) (state (t + 1))

theorem Trace.prefixRun {program : Code → Instruction Name Key Value Code Error}
    {initial : R} {last : Nat} (trace : Trace program initial last) (t : Nat) (bound : t ≤ last) :
    WellFormed.Run program initial (trace.state t) := by
  induction t with
  | zero => rw [trace.start]; exact .refl _
  | succ t ih =>
    exact .step (ih (by omega)) (trace.step t (by omega)).toCalculus

/-- A closed maximal installed interval, Definition58. Nonemptiness and both
boundaries are explicit; neither nesting nor provider lifetime is a premise. -/
structure EpisodeAtOn (states : Nat → R) (last : Nat) (name : Name) (begin finish : Nat) : Prop where
  positive : 0 < begin
  ordered : begin ≤ finish
  bounded : finish < last
  installed : ∀ t, begin ≤ t → t ≤ finish → ControlFrame.viewAt (states t) name ≠ none
  before : ControlFrame.viewAt (states (begin - 1)) name = none
  after : ControlFrame.viewAt (states (finish + 1)) name = none

abbrev EpisodeAt {program : Code → Instruction Name Key Value Code Error}
    {initial : R} {last : Nat} (trace : Trace program initial last)
    (name : Name) (begin finish : Nat) : Prop :=
  EpisodeAtOn trace.state last name begin finish

/-- A prefix of one episode, including an episode still open at the final
state. No eventual closure, fairness, or future lifecycle transition is assumed. -/
structure EpisodePrefixOn (states : Nat → R) (last : Nat) (name : Name) (begin finish : Nat) : Prop where
  positive : 0 < begin
  ordered : begin ≤ finish
  bounded : finish ≤ last
  installed : ∀ t, begin ≤ t → t ≤ finish → ControlFrame.viewAt (states t) name ≠ none
  before : ControlFrame.viewAt (states (begin - 1)) name = none

abbrev EpisodePrefix {program : Code → Instruction Name Key Value Code Error}
    {initial : R} {last : Nat} (trace : Trace program initial last)
    (name : Name) (begin finish : Nat) : Prop :=
  EpisodePrefixOn trace.state last name begin finish

end Cordis.Indexed
