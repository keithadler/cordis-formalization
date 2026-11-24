import Std

/-!
Execution-specific inverses. No inverse for source transformations is required.
The observation relation is explicit; raw undo functions need not be idempotent.
Recovery laws are conditional on `Sound` or `Witnessed`, not guarantees about
arbitrary cleanup callbacks.
-/

namespace Cordis
namespace Effects

universe u
variable {S : Type u}

abbrev Undo (S : Type u) := S → S

structure Effect (S : Type u) where
  run : S → S × Undo S

def identity : Effect S := ⟨fun s => (s, id)⟩

/-- Execute `a` and then `b`; retain the inverses actually returned. -/
def seq (a b : Effect S) : Effect S := ⟨fun s =>
  let (s₁, u₁) := a.run s
  let (s₂, u₂) := b.run s₁
  (s₂, u₁ ∘ u₂)⟩

variable [Setoid S]

def Respects (f : S → S) : Prop := ∀ ⦃s t⦄, s ≈ t → f s ≈ f t

/-- A sequential rollback contract, weaker than Cordis Definition 36: it says
nothing about the forward map or how the yielded inverse varies with its input.
Use `Witnessed` when observational congruence or independence is needed. -/
structure Sound (e : Effect S) : Prop where
  recover : ∀ s, (e.run s).2 (e.run s).1 ≈ s
  respects : ∀ s, Respects (e.run s).2

/-- The logical relation on maps: related inputs produce related outputs. -/
def Related (f g : S → S) : Prop := ∀ ⦃s t⦄, s ≈ t → f s ≈ g t

/-- Cordis Definition 36 for effect functions and an explicit observation relation.
Congruence relates both the forward result and the execution-specific inverse. -/
structure Witnessed (e : Effect S) : Prop where
  recover : ∀ s, (e.run s).2 (e.run s).1 ≈ s
  congruent : ∀ ⦃s t⦄, s ≈ t →
    (e.run s).1 ≈ (e.run t).1 ∧ Related (e.run s).2 (e.run t).2

theorem Witnessed.sound {e : Effect S} (h : Witnessed e) : Sound e :=
  ⟨h.recover, fun s => (h.congruent (Setoid.refl s)).2⟩

theorem Witnessed.forward_respects {e : Effect S} (h : Witnessed e) :
    Respects (fun s => (e.run s).1) := fun _ _ hst => (h.congruent hst).1

theorem witnessed_identity : Witnessed (identity : Effect S) :=
  ⟨fun _ => Setoid.refl _, fun _ _ h => ⟨h, fun _ _ h' => h'⟩⟩

end Effects
end Cordis
