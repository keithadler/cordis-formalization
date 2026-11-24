import Cordis.Tracking
import Cordis.Independence

/-!
Cordis Definitions 17, 18 and 34–42 for genuinely outcome-dependent iterators.
`next` is selected by the execution's input, so continuations may vary at every
state and there is no fixed-list or uniform finite-depth assumption. The type
is the least fixed point of the paper's strictly positive iterator functor.
The logical relation is defined as the greatest post-fixed point of its
unfolding, as Definition 34 requires.
-/

namespace Cordis.Iterators

open Effects
universe u
variable {S : Type u}

inductive Iterator (S : Type u) where
  | node (effect : Effect S) (next : S → Option (Iterator S))

def Iterator.effect : Iterator S → Effect S
  | .node e _ => e
def Iterator.next : Iterator S → S → Option (Iterator S)
  | .node _ n => n

def embed (e : Effect S) : Iterator S := .node e (fun _ => none)

/-- Definition 18: the continuation is chosen at this execution's input, and
its retained inverse is composed with the head's lifted captured inverse. -/
noncomputable def effectiter : Iterator S → Effect (Tracking.Context S) :=
  Iterator.rec
    (motive_1 := fun _ => Effect (Tracking.Context S))
    (motive_2 := fun _ => Option (Effect (Tracking.Context S)))
    (fun e _ tails => ⟨fun c =>
      let head := (Tracking.lift e).run c
      match tails c.1 with
      | none => head
      | some remaining =>
          let tail := remaining.run head.1
          (tail.1, head.2 ∘ tail.2)⟩)
    none (fun _ e => some e)

/-- Definition 40, the least continuation-closed set containing the root. -/
inductive Reach (i : Iterator S) : Iterator S → Prop
  | root : Reach i i
  | continuation {j k : Iterator S} (parent : Reach i j)
      (s : S) (next : j.next s = some k) : Reach i k

inductive Generator (i : Iterator S) : (S → S) → Prop
  | forward {j : Iterator S} (reach : Reach i j) : Generator i (Tracking.forward j.effect)
  | inverse {j : Iterator S} (reach : Reach i j) (s : S) :
      Generator i (Tracking.inverse j.effect s)

inductive Closure (G : (S → S) → Prop) : (S → S) → Prop
  | generator {f} : G f → Closure G f
  | identity : Closure G id
  | compose {f g} : Closure G f → Closure G g → Closure G (f ∘ g)

abbrev Generated (i : Iterator S) := Closure (Generator i)

def OptionRel {X Y : Type u} (R : X → Y → Prop) : Option X → Option Y → Prop
  | none, none => True
  | some x, some y => R x y
  | _, _ => False

section Relations
variable [Setoid S]

def Unfold (R : Iterator S → Iterator S → Prop) (i j : Iterator S) : Prop :=
  ∀ ⦃s t⦄, s ≈ t →
    (i.effect.run s).1 ≈ (j.effect.run t).1 ∧
    Related (i.effect.run s).2 (j.effect.run t).2 ∧
    OptionRel R (i.next s) (j.next t)

/-- Greatest relation satisfying Definition 34's recursive unfolding. -/
def RelatedIterator (i j : Iterator S) : Prop :=
  ∃ R : Iterator S → Iterator S → Prop, R i j ∧
    ∀ a b, R a b → Unfold R a b

theorem OptionRel.mono {X Y : Type u} {R T : X → Y → Prop}
    (h : ∀ x y, R x y → T x y) {a : Option X} {b : Option Y}
    (hab : OptionRel R a b) : OptionRel T a b := by
  cases a <;> cases b <;> simp_all [OptionRel]

theorem Unfold.mono {R T : Iterator S → Iterator S → Prop}
    (h : ∀ x y, R x y → T x y) {i j : Iterator S} (hij : Unfold R i j) :
    Unfold T i j := by
  intro s t hst
  obtain ⟨hs, hu, hn⟩ := hij hst
  exact ⟨hs, hu, OptionRel.mono h hn⟩

theorem related_unfold {i j : Iterator S} (h : RelatedIterator i j) :
    Unfold RelatedIterator i j := by
  obtain ⟨R, hij, hR⟩ := h
  exact Unfold.mono (fun a b hab => ⟨R, hab, hR⟩) (hR i j hij)

theorem related_coinduction {R : Iterator S → Iterator S → Prop}
    (hR : ∀ i j, R i j → Unfold R i j) {i j : Iterator S} (h : R i j) :
    RelatedIterator i j := ⟨R, h, hR⟩

/-- Unfolding in both directions, so the greatest-postfixed-point construction
is exactly the recursive logical relation rather than merely a subrelation. -/
theorem related_fold {i j : Iterator S} (h : Unfold RelatedIterator i j) :
    RelatedIterator i j := by
  apply related_coinduction (R := fun a b => Unfold RelatedIterator a b)
  · intro a b hab
    exact Unfold.mono (fun _ _ hab => related_unfold hab) hab
  · exact h

theorem OptionRel.symm {X : Type u} {R : X → X → Prop}
    {a b : Option X} (h : OptionRel R a b) :
    OptionRel (fun x y => R y x) b a := by
  cases a <;> cases b <;> simp_all [OptionRel]

/-- Lemma 35, iterator symmetry, by coinduction on the reversed relation. -/
theorem related_symm {i j : Iterator S} (h : RelatedIterator i j) :
    RelatedIterator j i := by
  apply related_coinduction (R := fun a b => RelatedIterator b a)
  · intro a b hab s t hst
    obtain ⟨hs, hu, hn⟩ := related_unfold hab (Setoid.symm hst)
    exact ⟨Setoid.symm hs, Independence.related_symm hu, OptionRel.symm hn⟩
  · exact h

theorem OptionRel.compose {X : Type u} {R T : X → X → Prop}
    {a b c : Option X} (hab : OptionRel R a b) (hbc : OptionRel T b c) :
    OptionRel (fun x z => ∃ y, R x y ∧ T y z) a c := by
  cases a <;> cases b <;> cases c <;> simp_all [OptionRel]
  exact ⟨_, hab, hbc⟩

/-- Lemma 35, iterator transitivity, by coinduction on relation composition. -/
theorem related_trans {i j k : Iterator S}
    (hij : RelatedIterator i j) (hjk : RelatedIterator j k) : RelatedIterator i k := by
  apply related_coinduction
    (R := fun a c => ∃ b, RelatedIterator a b ∧ RelatedIterator b c)
  · intro a c hac s t hst
    obtain ⟨b, hab, hbc⟩ := hac
    obtain ⟨hs, hu, hn⟩ := related_unfold hab hst
    obtain ⟨hs', hu', hn'⟩ := related_unfold hbc (Setoid.refl t)
    exact ⟨Setoid.trans hs hs', Independence.related_trans hu hu',
      OptionRel.compose hn hn'⟩
  · exact ⟨j, hij, hjk⟩

theorem related_respect_left {i j : Iterator S} (h : RelatedIterator i j) :
    RelatedIterator i i := related_trans h (related_symm h)
theorem related_respect_right {i j : Iterator S} (h : RelatedIterator i j) :
    RelatedIterator j j := related_trans (related_symm h) h

/-- Definition 37: the local recovery witness and the same requirement at every
reachable continuation. Respect is the full recursive logical relation. -/
inductive WitnessedIterator : Iterator S → Prop
  | node (e : Effect S) (n : S → Option (Iterator S))
      (respect : RelatedIterator (.node e n) (.node e n))
      (recover : ∀ s, (e.run s).2 (e.run s).1 ≈ s)
      (continuations : ∀ s j, n s = some j → WitnessedIterator j) :
      WitnessedIterator (.node e n)

theorem WitnessedIterator.respect {i : Iterator S} (h : WitnessedIterator i) :
    RelatedIterator i i := by cases h with | node _ _ h _ _ => exact h

theorem WitnessedIterator.effect_witnessed {i : Iterator S} (h : WitnessedIterator i) :
    Witnessed i.effect := by
  cases h with
  | node e n hr hw _ =>
    exact ⟨hw, fun _ _ hst =>
      ⟨(related_unfold hr hst).1, (related_unfold hr hst).2.1⟩⟩

theorem WitnessedIterator.continuation {i j : Iterator S} (h : WitnessedIterator i)
    (s : S) (hj : i.next s = some j) : WitnessedIterator j := by
  cases h with | node _ _ _ _ hc => exact hc s j hj

theorem WitnessedIterator.reachable {i j : Iterator S} (h : WitnessedIterator i)
    (hj : Reach i j) : WitnessedIterator j := by
  induction hj with
  | root => exact h
  | continuation _ s hn ih => exact ih.continuation s hn

theorem witnessed_embed {e : Effect S} (h : Witnessed e) : WitnessedIterator (embed e) := by
  apply WitnessedIterator.node
  · apply related_fold
    intro s t hst
    obtain ⟨hs, hu⟩ := h.congruent hst
    exact ⟨hs, hu, True.intro⟩
  · exact h.recover
  · intro s j h
    contradiction

theorem generator_respects {i : Iterator S} (hi : WitnessedIterator i)
    {f : S → S} (hf : Generator i f) : Respects f := by
  cases hf with
  | forward hj => exact (hi.reachable hj).effect_witnessed.forward_respects
  | inverse hj s => exact (hi.reachable hj).effect_witnessed.sound.respects s

theorem closure_respects {G : (S → S) → Prop}
    (hG : ∀ f, G f → Respects f) {f : S → S} (hf : Closure G f) : Respects f := by
  induction hf with
  | generator hg => exact hG _ hg
  | identity => exact fun _ _ h => h
  | compose _ _ ih₁ ih₂ => exact fun _ _ h => ih₁ (ih₂ h)

/-- Lemma 41(1) for arbitrary generator families, including all reachable
iterations. Respect is needed when the commutation equations are observational. -/
theorem closure_commute {G H : (S → S) → Prop}
    (hG : ∀ f, G f → Respects f) (hH : ∀ g, H g → Respects g)
    (commute : ∀ f, G f → ∀ g, H g → Independence.Commutes f g)
    {f g : S → S} (hf : Closure G f) (hg : Closure H g) :
    Independence.Commutes f g := by
  have first : ∀ f, G f → ∀ g, Closure H g → Independence.Commutes f g := by
    intro f hf g hg
    induction hg with
    | generator hg => exact commute f hf _ hg
    | identity => exact fun _ => Setoid.refl _
    | @compose g₁ g₂ hg₁ _ ih₁ ih₂ =>
      exact fun s => Setoid.trans (ih₁ (g₂ s)) (closure_respects hH hg₁ (ih₂ s))
  induction hf with
  | generator hf => exact first _ hf _ hg
  | identity => exact fun _ => Setoid.refl _
  | @compose f₁ f₂ hf₁ _ ih₁ ih₂ =>
    exact fun s => Setoid.trans (closure_respects hG hf₁ (ih₂ s)) (ih₁ (f₂ s))

def YieldRelated (i : Iterator S) (s t : S) : Prop :=
  Related (i.effect.run s).2 (i.effect.run t).2 ∧
    OptionRel RelatedIterator (i.next s) (i.next t)

theorem OptionRel.trans {X : Type u} {R : X → X → Prop}
    (trans : ∀ a b c, R a b → R b c → R a c)
    {a b c : Option X} (hab : OptionRel R a b) (hbc : OptionRel R b c) :
    OptionRel R a c := by
  cases a <;> cases b <;> cases c <;> simp_all [OptionRel]
  exact trans _ _ _ hab hbc

theorem YieldRelated.trans {i : Iterator S} {s t v : S}
    (hst : YieldRelated i s t) (htv : YieldRelated i t v) : YieldRelated i s v :=
  ⟨Independence.related_trans hst.1 htv.1,
    OptionRel.trans (R := RelatedIterator) (fun _ _ _ h₁ h₂ => related_trans h₁ h₂)
      hst.2 htv.2⟩

/-- Definition 42 expressed on generators; the next two theorems derive both
clauses for the whole generated monoids. Continuation stability is essential. -/
structure Independent (i j : Iterator S) : Prop where
  commute : ∀ f, Generator i f → ∀ g, Generator j g → Independence.Commutes f g
  left_yield : ∀ a, Reach i a → ∀ g, Generator j g → ∀ s, YieldRelated a (g s) s
  right_yield : ∀ b, Reach j b → ∀ f, Generator i f → ∀ s, YieldRelated b (f s) s

theorem generated_commute {i j : Iterator S}
    (hi : WitnessedIterator i) (hj : WitnessedIterator j) (h : Independent i j)
    {f g : S → S} (hf : Generated i f) (hg : Generated j g) :
    Independence.Commutes f g :=
  closure_commute (fun _ hf => generator_respects hi hf)
    (fun _ hg => generator_respects hj hg) h.commute hf hg

theorem generated_yield {i j a : Iterator S} (hi : WitnessedIterator i)
    (h : Independent i j) (ha : Reach i a) {g : S → S} (hg : Generated j g) (s : S) :
    YieldRelated a (g s) s := by
  induction hg generalizing s with
  | generator hg => exact h.left_yield a ha _ hg s
  | identity => exact (related_unfold (hi.reachable ha).respect (Setoid.refl s)).2
  | @compose f g _ _ ihf ihg => exact (ihf (g s)).trans (ihg s)

omit [Setoid S] in
/-- Lemma 41(2), in the paper's right-to-left diamond convention. Each new
generator is a composition of generators of the two original effects. -/
theorem diamond_generated_subset (e f : Effect S) {g : S → S}
    (hg : Independence.Generated (Tracking.diamond e f) g) :
    Closure (fun h => Independence.Generator e h ∨ Independence.Generator f h) g := by
  induction hg with
  | generator h =>
    cases h with
    | forward =>
      exact Closure.compose (f := Independence.forward e) (g := Independence.forward f)
        (.generator (Or.inl Independence.Generator.forward))
        (.generator (Or.inr Independence.Generator.forward))
    | inverse s =>
      exact Closure.compose (f := Independence.inverse f s)
        (g := Independence.inverse e (Tracking.forward f s))
        (.generator (Or.inr (.inverse s)))
        (.generator (Or.inl (.inverse (Tracking.forward f s))))
  | identity => exact .identity
  | compose _ _ ih₁ ih₂ => exact .compose ih₁ ih₂

end Relations

end Cordis.Iterators
