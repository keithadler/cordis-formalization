import Cordis.Iterators

/-! Lemma38's observational forms of the non-definitional state equalities in
Section3.1. Effect contexts use Definition34's product/function lifting, a
partial equivalence: arbitrary non-respecting functions are not identified
even with themselves. Every reachable accumulator is proved respecting.
The unconditional algebraic identities4/5/10/13/14 remain exact in Tracking.
-/
namespace Cordis.ObservationLifting
open Effects Tracking Iterators
universe u
variable {S : Type u} [Setoid S]

def ContextRelated (a b : Context S) : Prop := a.1 ≈ b.1 ∧ Related a.2 b.2
def Admissible (c : Context S) : Prop := Respects c.2

theorem context_refl (c : Context S) (admissible : Admissible c) : ContextRelated c c :=
  ⟨Setoid.refl _, admissible⟩

theorem context_symm {a b : Context S} (h : ContextRelated a b) : ContextRelated b a :=
  ⟨Setoid.symm h.1, Independence.related_symm h.2⟩

theorem context_trans {a b c : Context S} (ab : ContextRelated a b) (bc : ContextRelated b c) :
    ContextRelated a c := ⟨Setoid.trans ab.1 bc.1, Independence.related_trans ab.2 bc.2⟩

theorem recover_related {a b : Context S} (h : ContextRelated a b) : ContextRelated (recover a) (recover b) :=
  ⟨h.2 h.1, fun {_ _} h => h⟩

/-- Theorem7/Equation10 for a respecting accumulator, as supplied by the
reachability clause of Lemma38. Recovery itself resets the accumulator to id. -/
theorem recover_track_observed (pair : Twisted S) (c : Context S)
    (accumulator : Admissible c) (recovers : pair.2 (pair.1 c.1) ≈ c.1) :
    ContextRelated (recover (track pair c)) (recover c) :=
  ⟨accumulator recovers, fun {_ _} h => h⟩

/-- Definition12 also respects the full logical relation on admissible effect
contexts; both its returned state and captured lifted inverse are compared. -/
theorem lift_congruent {e : Effect S} (witness : Witnessed e) {a b : Context S}
    (related : ContextRelated a b) :
    ContextRelated (forward (lift e) a) (forward (lift e) b) ∧
    (∀ x y, ContextRelated x y → ContextRelated (inverse (lift e) a x) (inverse (lift e) b y)) := by
  have outputs := witness.congruent related.1
  constructor
  · exact ⟨outputs.1, fun {_ _} values => related.2 (outputs.2 values)⟩
  · intro x y inputs
    exact ⟨outputs.2 inputs.1, fun {_ _} values => inputs.2 (witness.forward_respects values)⟩

/-- Equation16: the original state is recovered observationally while the
accumulator receives the original captured inverse and replay forward map. -/
theorem lift_revert_observed {e : Effect S} (witness : Witnessed e) (c : Context S)
    (accumulator : Admissible c) :
    ContextRelated (inverse (lift e) c (forward (lift e) c))
      (c.1, c.2 ∘ inverse e c.1 ∘ forward e) :=
  ⟨witness.recover c.1, fun {_ _} h => accumulator
    (witness.sound.respects c.1 (witness.forward_respects h))⟩

/-- The global iff in Theorem15, with the function equation read by the
logical relation. The identity accumulator is admissible, proving necessity. -/
theorem observed_lift_recovery_iff {e : Effect S} (witness : Witnessed e) :
    (∀ c : Context S, Admissible c → ContextRelated
      (inverse (lift e) c (forward (lift e) c)) c) ↔
    (∀ s, Related (inverse e s ∘ forward e) id) := by
  constructor
  · intro restores s
    exact (restores (s, id) (fun {_ _} h => h)).2
  · intro uniform c admissible
    exact ⟨witness.recover c.1, fun {_ _} h => admissible (uniform c.1 h)⟩

/-- The reflexive part of Definition34's context PER. This is a type of
lawful effect contexts, not an extra invariant assumed of executions. -/
abbrev LawfulContext (S : Type u) [Setoid S] := {c : Context S // Admissible c}

instance lawfulContextSetoid : Setoid (LawfulContext S) where
  r a b := ContextRelated a.val b.val
  iseqv := ⟨fun a => context_refl a.val a.property,
    fun h => context_symm h, fun ab bc => context_trans ab bc⟩

/-- Definition12 restricted to the reflexive domain of its logical relation.
The forward and every captured inverse preserve that domain constructively. -/
def lawfulLift (e : Effect S) (witness : Witnessed e) : Effect (LawfulContext S) :=
  ⟨fun c =>
    (⟨forward (lift e) c.val, fun {_ _} h =>
      c.property (witness.sound.respects c.val.1 h)⟩,
     fun current => ⟨inverse (lift e) c.val current.val, fun {_ _} h =>
       current.property (witness.forward_respects h)⟩)⟩

theorem lawful_lift_congruent (e : Effect S) (witness : Witnessed e)
    {a b : LawfulContext S} (related : a ≈ b) :
    ((lawfulLift e witness).run a).1 ≈ ((lawfulLift e witness).run b).1 ∧
      Related ((lawfulLift e witness).run a).2 ((lawfulLift e witness).run b).2 := by
  have lifted := lift_congruent witness related
  exact ⟨lifted.1, fun {_ _} h => lifted.2 _ _ h⟩

/-- The full witnessed-membership iff of Theorem15 after Lemma38's change
of equality, including congruence of the lifted inverse, not only recovery. -/
theorem witnessed_lawful_lift_iff (e : Effect S) (witness : Witnessed e) :
    Witnessed (lawfulLift e witness) ↔ ∀ s, Related (inverse e s ∘ forward e) id := by
  constructor
  · intro lifted s
    exact (lifted.recover ⟨(s, id), fun {_ _} h => h⟩).2
  · intro uniform
    refine ⟨?_, fun {_ _} h => lawful_lift_congruent e witness h⟩
    intro c
    exact (observed_lift_recovery_iff witness).mpr uniform c.val c.property

/-- Even when the full effect context does not restore its accumulator,
Theorem15 preserves the recovered target up to observation. -/
theorem recover_lift_revert_observed {e : Effect S} (witness : Witnessed e) (c : Context S)
    (accumulator : Admissible c) :
    ContextRelated (recover (inverse (lift e) c (forward (lift e) c))) (recover c) := by
  apply context_trans (recover_related (lift_revert_observed witness c accumulator))
  exact ⟨accumulator (witness.recover c.1), fun {_ _} h => h⟩

inductive ListRelated {X Y : Type u} (rel : X → Y → Prop) : List X → List Y → Prop
  | nil : ListRelated rel [] []
  | cons {a b as bs} : rel a b → ListRelated rel as bs → ListRelated rel (a :: as) (b :: bs)

/-- Theorem16(1) at every actual LIFO rollback position. The reference list
contains the original application states; the actual list executes the
captured inverse functions. Their agreement is proved, not built into a trace. -/
theorem actual_reverts_related (history : History S) (valid : history.observedValid)
    (s : S) (state : s ≈ history.state) (accumulator : S → S) (respect : Respects accumulator) :
    ListRelated ContextRelated
      (runMaps history.capturedReverts (s, accumulator)) (history.revertStates accumulator) := by
  induction history generalizing s accumulator with
  | nil initial => exact .cons ⟨state, respect⟩ .nil
  | snoc previous effect ih =>
    apply ListRelated.cons ⟨state, respect⟩
    have restored : inverse effect previous.state s ≈ previous.state :=
      Setoid.trans (valid.2.sound.respects previous.state state) (valid.2.recover previous.state)
    exact ih valid.1 (inverse effect previous.state s) restored (accumulator ∘ forward effect)
      (fun {_ _} h => respect (valid.2.forward_respects h))

end Cordis.ObservationLifting
