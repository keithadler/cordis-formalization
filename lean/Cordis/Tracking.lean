import Cordis.Effects

/-!
The exact algebra of Cordis §3.1, Definitions 1–16. `diamond` uses the paper's
right-to-left order; `Effects.seq` uses program execution order. In particular,
the inverse returned by `lift` updates the accumulator as well as the state.
Theorem 15 does not say a pointwise inverse is a uniform inverse.
-/

namespace Cordis.Tracking

open Effects
universe u
variable {S : Type u}

abbrev Context (S : Type u) := S × (S → S)
abbrev Twisted (S : Type u) := (S → S) × (S → S)

def twistedUnit : Twisted S := (id, id)
def twistedMul (p q : Twisted S) : Twisted S := (p.1 ∘ q.1, q.2 ∘ p.2)
def track (p : Twisted S) (c : Context S) : Context S := (p.1 c.1, c.2 ∘ p.2)
def recover (c : Context S) : Context S := (c.2 c.1, id)

def forward (e : Effect S) : S → S := fun s => (e.run s).1
def inverse (e : Effect S) (s : S) : S → S := (e.run s).2
def ExactWitnessed (e : Effect S) : Prop := ∀ s, inverse e s (forward e s) = s
def uniform (p : Twisted S) : Effect S := ⟨fun s => (p.1 s, p.2)⟩
def diamond (e f : Effect S) : Effect S := seq f e

/-- Definition 12, including the accumulator-transforming captured inverse. -/
def lift (e : Effect S) : Effect (Context S) := ⟨fun c =>
  ((forward e c.1, c.2 ∘ inverse e c.1), track (inverse e c.1, forward e))⟩

/-- Theorem 15's exact computation. The accumulator generally changes. -/
theorem lift_revert {e : Effect S} (he : ExactWitnessed e) (c : Context S) :
    inverse (lift e) c (forward (lift e) c) =
      (c.1, c.2 ∘ inverse e c.1 ∘ forward e) := by
  change (inverse e c.1 (forward e c.1), _) = _
  rw [he]
  rfl

/-- Theorem 15's global iff. Quantification over all accumulators is essential
for the converse: choosing the identity accumulator detects uniform recovery. -/
theorem exact_lift_iff {e : Effect S} (he : ExactWitnessed e) :
    ExactWitnessed (lift e) ↔ ∀ s, inverse e s ∘ forward e = id := by
  constructor
  · intro h s
    have hs := h (s, id)
    rw [lift_revert he] at hs
    exact congrArg Prod.snd hs
  · intro h c
    rw [lift_revert he]
    have hc : c.2 ∘ inverse e c.1 ∘ forward e = c.2 := by
      funext s
      exact congrArg c.2 (congrFun (h c.1) s)
    rw [hc]

/-- A recorded finite application history. Validity stores only the per-effect
witnesses; neither rollback nor its desired invariant is an assumption. -/
inductive History (S : Type u) where
  | nil (start : S)
  | snoc (previous : History S) (effect : Effect S)

def History.start : History S → S
  | .nil s => s
  | .snoc p _ => p.start

def History.state : History S → S
  | .nil s => s
  | .snoc p e => forward e p.state

def History.accumulator : History S → S → S
  | .nil _ => id
  | .snoc p e => p.accumulator ∘ inverse e p.state

def History.valid : History S → Prop
  | .nil _ => True
  | .snoc p e => p.valid ∧ ExactWitnessed e

def History.applicationStates : History S → List (Context S)
  | .nil s => [(s, id)]
  | .snoc p e => p.applicationStates ++
      [(forward e p.state, p.accumulator ∘ inverse e p.state)]

/-- Every entry is the state after some number of LIFO reverts. The accumulator
tracks the replay forward map of each reverted application (Definition 12). -/
def History.revertStates : History S → (S → S) → List (Context S)
  | .nil s, φ => [(s, φ)]
  | .snoc p e, φ => (forward e p.state, φ) :: p.revertStates (φ ∘ forward e)

/-- Theorem 7 iterated; also the forward half of Theorem 16(2). -/
theorem History.accumulator_sound (p : History S) (hp : p.valid) :
    p.accumulator p.state = p.start := by
  induction p with
  | nil s => rfl
  | snoc p e ih =>
    change p.accumulator (inverse e p.state (forward e p.state)) = p.start
    rw [hp.2, ih hp.1]

/-- Theorem 16(2), all intermediate LIFO states, with an arbitrary currently
sound accumulator. The initial instance uses `accumulator_sound`. -/
theorem History.revert_states_sound (p : History S) (φ : S → S) (s₀ : S)
    (hφ : φ p.state = s₀) :
    ∀ c ∈ p.revertStates φ, c.2 c.1 = s₀ := by
  induction p generalizing φ with
  | nil s => simpa [revertStates, state] using hφ
  | snoc p e ih =>
    intro c hc
    simp only [revertStates, List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact hφ
    · exact ih (φ ∘ forward e) hφ c hc

theorem History.all_revert_states_sound (p : History S) (hp : p.valid) :
    ∀ c ∈ p.revertStates p.accumulator, c.2 c.1 = p.start :=
  p.revert_states_sound p.accumulator p.start (p.accumulator_sound hp)

def History.capturedReverts : History S → List (Context S → Context S)
  | .nil _ => []
  | .snoc p e => inverse (lift e) (p.state, id) :: p.capturedReverts

def runMaps {X : Type u} : List (X → X) → X → List X
  | [], x => [x]
  | f :: fs, x => x :: runMaps fs (f x)

section Observation
variable [Setoid S]

def History.observedValid : History S → Prop
  | .nil _ => True
  | .snoc p e => p.observedValid ∧ Witnessed e

/-- Lemma 38: every reachable accumulator respects the chosen equivalence. -/
theorem History.accumulator_respects (p : History S) (hp : p.observedValid) :
    Respects p.accumulator := by
  induction p with
  | nil _ => exact fun _ _ h => h
  | snoc p e ih =>
    exact fun _ _ h => ih hp.1 (hp.2.sound.respects p.state h)

/-- Lemma 38: the accumulated inverse recovers up to observation. -/
theorem History.accumulator_recovers (p : History S) (hp : p.observedValid) :
    p.accumulator p.state ≈ p.start := by
  induction p with
  | nil s => exact Setoid.refl s
  | snoc p e ih =>
    exact Setoid.trans (p.accumulator_respects hp.1 (hp.2.recover p.state)) (ih hp.1)

theorem History.application_states_observed (p : History S) (hp : p.observedValid) :
    ∀ c ∈ p.applicationStates, Respects c.2 ∧ c.2 c.1 ≈ p.start := by
  induction p with
  | nil s =>
    intro c hc
    simp only [applicationStates, List.mem_singleton] at hc
    subst c
    exact ⟨fun _ _ h => h, Setoid.refl _⟩
  | snoc p e ih =>
    intro c hc
    simp only [applicationStates, List.mem_append, List.mem_singleton] at hc
    rcases hc with hc | rfl
    · exact ih hp.1 c hc
    · exact ⟨(History.snoc p e).accumulator_respects hp,
        (History.snoc p e).accumulator_recovers hp⟩

/-- Observational Theorem 16: captured LIFO inverses may return a representative
of the original state. Respect, rather than exact equality of representatives,
propagates recovery through every actual intermediate rollback state. -/
theorem History.actual_revert_states_observed (p : History S) (hp : p.observedValid)
    (s : S) (hs : s ≈ p.state) (φ : S → S) (hφ : Respects φ) (s₀ : S)
    (h₀ : φ s ≈ s₀) :
    ∀ c ∈ runMaps p.capturedReverts (s, φ), Respects c.2 ∧ c.2 c.1 ≈ s₀ := by
  induction p generalizing s φ with
  | nil initial =>
    intro c hc
    simp only [capturedReverts, runMaps, List.mem_singleton] at hc
    subst c
    exact ⟨hφ, h₀⟩
  | snoc p e ih =>
    intro c hc
    simp only [capturedReverts, runMaps, List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact ⟨hφ, h₀⟩
    · have hu : inverse e p.state s ≈ p.state :=
        Setoid.trans (hp.2.sound.respects p.state hs) (hp.2.recover p.state)
      have hf : forward e (inverse e p.state s) ≈ s :=
        Setoid.trans (hp.2.forward_respects hu) (Setoid.symm hs)
      exact ih hp.1 (inverse e p.state s) hu (φ ∘ forward e)
        (fun _ _ h => hφ (hp.2.forward_respects h)) (Setoid.trans (hφ hf) h₀) c hc

end Observation

/-- Nontrivial pointwise inverse: overwriting any natural with zero and retaining
that execution's old value is exact, but its lift is not a witnessed effect on
the full effect context. This is the strictness in Theorem 15. -/
def overwriteZero : Effect Nat := ⟨fun n => (0, fun _ => n)⟩
theorem overwriteZero_exact : ExactWitnessed overwriteZero := fun _ => rfl
theorem overwriteZero_lift_not_exact : ¬ ExactWitnessed (lift overwriteZero) := by
  intro h
  have h₀ := (exact_lift_iff overwriteZero_exact).mp h 0
  have := congrFun h₀ 1
  exact Nat.noConfusion this

def overwriteHistory : History Nat :=
  .snoc (.snoc (.nil 7) overwriteZero) overwriteZero
theorem overwriteHistory_valid : overwriteHistory.valid :=
  ⟨⟨True.intro, overwriteZero_exact⟩, overwriteZero_exact⟩
theorem overwriteHistory_restores :
    ∀ c ∈ overwriteHistory.revertStates overwriteHistory.accumulator, c.2 c.1 = 7 :=
  overwriteHistory.all_revert_states_sound overwriteHistory_valid

end Cordis.Tracking
