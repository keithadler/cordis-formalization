import Cordis.ObservationLifting

/-! A witnessed iterator whose continuation depends on the observed input.
Its captured inverse deliberately changes a hidden representation bit, so the
observational theorem is exercised where literal state recovery is false. -/
namespace Cordis.ObservationLiftingExamples
open Effects Tracking Iterators ObservationLifting

abbrev State := Nat × Bool
instance : Setoid State where
  r a b := a.1 = b.1
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

/-- A negative control for the admissibility condition. This function cannot
be an accumulator reached from identity by witnessed effects: it distinguishes
representations which the observation relation identifies. -/
def badAccumulator (s : State) : State := if s.2 then (0, true) else (1, true)

def hiddenFlip : Effect State := ⟨fun s => ((s.1, !s.2), id)⟩

theorem hiddenFlip_witnessed : Witnessed hiddenFlip :=
  ⟨fun _ => rfl, fun {_ _} related => ⟨related, fun {_ _} h => h⟩⟩

end Cordis.ObservationLiftingExamples
