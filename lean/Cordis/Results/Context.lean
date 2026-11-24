import Cordis.PaperObservationEquations
import Cordis.ObservationAccumulatorDomain

/-!
# Section 3 lemmas

Lemmas 35 and 41 are proved as stated. For Lemmas 32 and 39 we give the
fixed-word result, a counterexample to cross-input inverse respect, and a
conditional iterator theorem isolating the needed respect premise. For Lemma
38 we state the recovery guarantee on respecting accumulators and refute its
unrestricted reading.
-/

namespace Cordis.Results
open Coeffects Iterators PaperEffectEquations PaperObservationEquations
open PartialCoeffectLifting (Table PartialMap)
open PartialInverseObservation (MapRelated)
universe u
variable {K : Type u} {V : K → Type u}

/-- Under Definition 31's fixed-word tests, the relation is the coarsest
relation preserved by every forward letter and every particular yielded
inverse, and those letters agree on their definedness and outcomes. -/
theorem lemma32_fixed (operations : CoeffectOperations V) (k : K) :
    Equivalence (KeyEquivalent operations k) ∧
    RespectsTests (testStep operations k) (KeyEquivalent operations k) ∧
    ∀ relation, RespectsTests (testStep operations k) relation →
      ∀ v w, relation v w → KeyEquivalent operations k v w :=
  ⟨indistinguishable_equivalence _, indistinguishable_respected _,
    indistinguishable_coarsest _⟩

/-- The coarseness clause of Lemma 32 remains valid for full operation
respect. Reflexivity at the input that produced an inverse gives respect
for that fixed inverse. -/
theorem lemma32_coarsest (operations : CoeffectOperations V) (k : K)
    (relation : V k → V k → Prop) (equivalence : Equivalence relation)
    (respect : OperationRespects operations k relation) :
    ∀ v w, relation v w → KeyEquivalent operations k v w := by
  apply indistinguishable_coarsest
  intro letter v w related
  cases letter with
  | forward name arg =>
    have outputs := respect name arg v w related
    cases left : (operations.operation k name arg).run v <;>
      cases right : (operations.operation k name arg).run w <;>
      simp [testStep, left, right, OptionRel] at outputs ⊢
    obtain ⟨states, _, outcomes⟩ := outputs
    exact ⟨states, outcomes⟩
  | inverse g yielded =>
    obtain ⟨name, argument, input, output, outcome, returned⟩ := yielded
    have sameInput := respect name argument input input (equivalence.refl input)
    rw [returned] at sameInput
    have inverseRespect : MapRelated relation g g := sameInput.2.1
    have outputs := inverseRespect v w related
    cases left : g v <;> cases right : g w <;>
      simp [testStep, left, right, OptionRel] at outputs ⊢
    exact outputs

/-- The primitive respect clause needed for Lemma 39 is exactly the operation
relation on the chosen key equivalences. Recovery follows separately from
Definition 29, even if full respect of those operations has yet to be shown. -/
theorem lemma39_partial [DecidableEq K] (operations : CoeffectOperations V)
    (exactRecovery : ValueOperationWitness operations)
    (relation : ∀ k, Setoid (V k))
    (respect : ∀ k, OperationRespects operations k (relation k).r)
    (declared provided keys : K → Prop) (subset : ∀ k, provided k → declared k)
    (i : PartialIterators.Iterator (Table V))
    (member : ContextMediated operations declared provided subset i)
    (support : ∀ j, PartialIterators.Reach i j →
      PartialReachMediatedWitness.HeadLocal operations.stageSignature keys j) :
    PartialIterators.Witnessed
      (PartialCoeffectLifting.TableRelated (fun k => (relation k).r) keys) i := by
  apply PartialReachMediatedWitness.reachable_witnessed relation _ member support
  constructor
  · rintro ⟨k, name, argument⟩
    exact exactRecovery k name argument
  · rintro ⟨k, name, argument⟩
    exact respect k name argument

section FixedWordCounterexample

private abbrev CounterValue := Coeffects.CapturedInverseCounterexample.Value
private abbrev capturedUndo := Coeffects.CapturedInverseCounterexample.capturedUndo
private abbrev SameVisible := Coeffects.CapturedInverseCounterexample.SameVisible

/-- One key holds two bits. Reset clears the visible bit and returns an
inverse that recovers both bits. Read observes only the visible bit. -/
def counterexampleOperations : CoeffectOperations (fun _ : Unit => CounterValue) where
  Name _ := Bool
  Argument _ _ := Unit
  Outcome _ _ := Option Bool
  operation _ name _ := ⟨fun v =>
    if name then some (v, some, some v.2)
    else some ((v.1, false), some ∘ capturedUndo v, none)⟩

theorem counterexample_exact : ValueOperationWitness counterexampleOperations := by
  rintro ⟨⟩ name ⟨⟩ v w inverse outcome returned
  cases name <;>
    simp [counterexampleOperations, Prod.mk.injEq] at returned
  · obtain ⟨rfl, rfl, _⟩ := returned
    rfl
  · obtain ⟨rfl, rfl, _⟩ := returned
    rfl

private theorem fixed_preserves_visible :
    RespectsTests (testStep counterexampleOperations ()) SameVisible := by
  intro letter v w related
  cases letter with
  | forward name arg =>
    cases name
    · exact ⟨rfl, rfl⟩
    · exact ⟨related, by
        change some (⟨true, some v.2⟩ : Outcome counterexampleOperations ()) =
          some ⟨true, some w.2⟩
        rw [show v.2 = w.2 from related]⟩
  | inverse f yielded =>
    obtain ⟨name, _, saved, _, _, returned⟩ := yielded
    cases name
    · simp [counterexampleOperations, Prod.mk.injEq] at returned
      obtain ⟨_, rfl, _⟩ := returned
      exact ⟨by
        change (if v.2 then saved.1 else saved.2) = (if w.2 then saved.1 else saved.2)
        rw [show v.2 = w.2 from related], rfl⟩
    · simp [counterexampleOperations, Prod.mk.injEq] at returned
      obtain ⟨_, rfl, _⟩ := returned
      exact ⟨related, rfl⟩

private theorem fixed_implies_visible {v w : CounterValue}
    (related : KeyEquivalent counterexampleOperations () v w) : SameVisible v w := by
  have read := related [.forward true ()]
  simpa [runTest, testStep, counterexampleOperations, SameVisible] using read

theorem counterexample_fixed_iff_visible (v w : CounterValue) :
    KeyEquivalent counterexampleOperations () v w ↔ SameVisible v w :=
  ⟨fixed_implies_visible, indistinguishable_coarsest _ _ fixed_preserves_visible v w⟩

private theorem bad_key_inputs :
    KeyEquivalent counterexampleOperations () (false, false) (true, false) :=
  (counterexample_fixed_iff_visible _ _).2 rfl

private theorem unequal_visible_outputs :
    ¬ KeyEquivalent counterexampleOperations () (false, false) (true, true) := by
  intro related
  have impossible : false = true := fixed_implies_visible related
  cases impossible

/-- Lemma 32's full operation-respect clause fails for fixed-word tests, even
when every operation has the literal recovery witness of Definition 29. -/
theorem lemma32_fixed_refuted : ¬ lemma32 counterexampleOperations () := by
  intro claimed
  have called := claimed.2.1 false () (false, false) (true, false) bad_key_inputs
  have inverses : MapRelated (KeyEquivalent counterexampleOperations ())
      (some ∘ capturedUndo (false, false)) (some ∘ capturedUndo (true, false)) := called.2.1
  let probe : CounterValue := (false, true)
  have probeRelated : KeyEquivalent counterexampleOperations () probe probe :=
    (lemma32_fixed counterexampleOperations ()).1.refl probe
  exact unequal_visible_outputs (inverses probe probe probeRelated)

private def singletonTable (v : CounterValue) : Table (fun _ : Unit => CounterValue) :=
  fun _ => some v

private def resetStage : PartialIterators.Iterator (Table (fun _ : Unit => CounterValue)) :=
  PartialIterators.stage (counterexampleOperations.stageSignature.lifted ⟨(), false, ()⟩)
    (fun _ => none)

private theorem resetStage_call (v : CounterValue) :
    resetStage.run (singletonTable v) =
      some (singletonTable (v.1, false),
        PartialCoeffectLifting.liftMap () (some ∘ capturedUndo v), none) :=
  rfl

private theorem resetStage_reach {j : PartialIterators.Iterator (Table (fun _ : Unit => CounterValue))}
    (reach : PartialIterators.Reach resetStage j) : j = resetStage := by
  induction reach with
  | root => rfl
  | continuation _ table output undo called ih =>
    rw [ih] at called
    change ((counterexampleOperations.stageSignature.lifted ⟨(), false, ()⟩).run table).map _ =
      some (output, undo, some _) at called
    cases (counterexampleOperations.stageSignature.lifted ⟨(), false, ()⟩).run table <;>
      simp at called

private def observedAll := TableEquivalent counterexampleOperations (fun _ => True)

private theorem singleton_related {v w : CounterValue}
    (relation : KeyEquivalent counterexampleOperations () v w) :
    observedAll (singletonTable v) (singletonTable w) := by
  rintro ⟨⟩ _
  exact relation

/-- In Equation (32)'s partial semantics, the one-stage reset program is
context-mediated with exact recovery. Its selected-key iterator witness
fails with the paper's fixed-word observation. -/
theorem lemma39_fixed_refuted : ¬ lemma39Partial counterexampleOperations := by
  intro claimed
  let keys : Unit → Prop := fun _ => True
  let provided : Unit → Prop := fun _ => False
  have member : ContextMediated counterexampleOperations keys provided
      (fun _ impossible => impossible.elim) resetStage :=
    .operation (signature := counterexampleOperations.stageSignature)
      ⟨(), false, ()⟩ trivial (fun _ => none) (by simp)
  have support : ∀ j, PartialIterators.Reach resetStage j →
      PartialReachMediatedWitness.HeadLocal counterexampleOperations.stageSignature keys j := by
    intro j reached
    rw [resetStage_reach reached]
    exact .operation (signature := counterexampleOperations.stageSignature)
      ⟨(), false, ()⟩ trivial (fun _ => none)
  have result := claimed counterexample_exact keys provided keys
    (fun _ impossible => impossible.elim) resetStage member support
  have self := (result resetStage .root).2
  have unfolded := PartialIterators.related_unfold _ self
    (singletonTable (false, false)) (singletonTable (true, false)) (singleton_related bad_key_inputs)
  rw [resetStage_call, resetStage_call] at unfolded
  have inverseRelated := unfolded.2.1
  let probe := singletonTable (false, true)
  have related := inverseRelated probe probe (singleton_related ((lemma32_fixed counterexampleOperations ()).1.refl _))
  have outputTables : observedAll (singletonTable (false, false)) (singletonTable (true, true)) := related
  exact unequal_visible_outputs (outputTables () trivial)

end FixedWordCounterexample

section LogicalRelations

variable {Γ X Y : Type u}

/-- Lemma 35 for the function former and the greatest iterator relation. -/
theorem lemma35_proved [Setoid Γ] (input : X → X → Prop) (output : Y → Y → Prop) :
    lemma35 (Γ := Γ) input output := by
  refine ⟨?_, ⟨fun _ _ => related_symm, fun _ _ _ => related_trans⟩⟩
  intro inputs outputs
  exact ⟨fun _ _ related x y h => outputs.symm (related y x (inputs.symm h)),
    fun _ _ _ first second x y h => outputs.trans (first x y h) (second y y (inputs.refl y))⟩

theorem lemma35_maps_respect (input : X → X → Prop) (output : Y → Y → Prop)
    (inputs : Equivalence input) (outputs : Equivalence output)
    {f g : X → Y} (related : FunctionRelated input output f g) :
    FunctionRelated input output f f ∧ FunctionRelated input output g g := by
  have reverse : FunctionRelated input output g f :=
    fun x y h => outputs.symm (related y x (inputs.symm h))
  exact ⟨fun x y h => outputs.trans (related x y h) (reverse y y (inputs.refl y)),
    fun x y h => outputs.trans (reverse x y h) (related y y (inputs.refl y))⟩

theorem lemma35_iterators_respect [Setoid Γ] {i j : Iterator Γ}
    (related : IteratorRelated i j) : IteratorRelated i i ∧ IteratorRelated j j :=
  ⟨related_respect_left related, related_respect_right related⟩

end LogicalRelations

section Tracking
open Effects (Effect Respects Witnessed Related)
open Tracking
open ObservationLifting
variable {Γ : Type u} [Setoid Γ]

private theorem effectWitness_iff (effect : Effect Γ) :
    EffectWitness effect ↔ Witnessed effect := by
  constructor
  · rintro ⟨respects, recovers⟩
    exact ⟨fun state => recovers state _ _ rfl,
      fun {x y} related => ⟨(respects x y related).1, (respects x y related).2⟩⟩
  · intro witness
    refine ⟨fun x y related => ⟨(witness.congruent related).1, (witness.congruent related).2⟩, ?_⟩
    intro state output undo result
    have recovered := witness.recover state
    rw [← result] at recovered
    exact recovered

/-- The unrestricted Theorem 15 recovery target is false after the
substitution required by Lemma 38. A witnessed effect changes a hidden bit,
and the accumulator reads it into the observed coordinate. -/
theorem lemma38_unrestricted_refuted :
    ¬ lemma38RecoveryTarget (Γ := ObservationLiftingExamples.State) := by
  open ObservationLiftingExamples in
  intro asserted
  exact unrestricted_observed_theorem15_target_fails.2.2
    (asserted hiddenFlip ((effectWitness_iff _).2 hiddenFlip_witnessed) (0, false) badAccumulator)

/-- Respect is necessary and sufficient for one accumulator to preserve
the observed recovery target of every witnessed effect. -/
theorem lemma38_recovery_iff (φ : Γ → Γ) :
    Respects φ ↔ ∀ effect : Effect Γ, EffectWitness effect → ∀ state,
      φ (inverse effect state (forward effect state)) ≈ φ state := by
  rw [respects_iff_preserves_recovery_targets]
  exact ⟨fun h e witness => h e ((effectWitness_iff e).1 witness),
    fun h e witness => h e ((effectWitness_iff e).2 witness)⟩

/-- Equation (11) after observation. Each inverse must respect the
equivalence and recover that step's actual input. -/
def ObservedPairs : List (Twisted Γ) → Γ → Prop
  | [], _ => True
  | (forward, inverse) :: rest, state =>
      Respects inverse ∧ inverse (forward state) ≈ state ∧ ObservedPairs rest (forward state)

theorem lemma38_tracked_sequence (pairs : List (Twisted Γ)) (c : Context Γ)
    (admissible : Admissible c) (witnesses : ObservedPairs pairs c.1) :
    let final := pairs.foldl (fun current pair => track pair current) c
    Admissible final ∧ ContextRelated (recover final) (recover c) := by
  induction pairs generalizing c with
  | nil => exact ⟨admissible, context_refl (recover c) (fun _ _ h => h)⟩
  | cons pair rest ih =>
    obtain ⟨inverseRespect, recovers, tail⟩ := witnesses
    have trackedAdmissible : Admissible (track pair c) :=
      fun _ _ related => admissible (inverseRespect related)
    obtain ⟨finalAdmissible, tailRelated⟩ := ih (track pair c) trackedAdmissible tail
    exact ⟨finalAdmissible, context_trans tailRelated
      (recover_track_observed pair c admissible recovers)⟩

/-- Theorem 15 on respecting accumulators. Reverting preserves the recovery
target, and the lifted effect has the full witness exactly when each inverse
agrees globally with a left inverse at the chosen observational relation. -/
theorem lemma38_lift (effect : Effect Γ) (effectWitness : EffectWitness effect)
    (c : LawfulContext Γ) :
    ContextRelated
      (inverse (lift effect) c.val (forward (lift effect) c.val))
      (c.val.1, c.val.2 ∘ inverse effect c.val.1 ∘ forward effect) ∧
    ContextRelated
      (recover (inverse (lift effect) c.val (forward (lift effect) c.val)))
      (recover c.val) ∧
    (Witnessed (lawfulLift effect ((effectWitness_iff effect).1 effectWitness)) ↔
      ∀ state, Related (inverse effect state ∘ forward effect) id) := by
  have witness := (effectWitness_iff effect).1 effectWitness
  exact ⟨lift_revert_observed witness c.val c.property,
    recover_lift_revert_observed witness c.val c.property, witnessed_lawful_lift_iff effect witness⟩

/-- Every application and LIFO reversion state reached from identity retains
a respecting accumulator and recovers to the original observation. -/
theorem lemma38_reachable_sound (history : History Γ) (valid : history.observedValid) :
    ∀ c ∈ history.applicationStates ++
      runMaps history.capturedReverts (history.state, history.accumulator),
      Respects c.2 ∧ c.2 c.1 ≈ history.start := by
  intro c reached
  rcases List.mem_append.mp reached with applied | reverted
  · exact history.application_states_observed valid c applied
  · exact history.actual_revert_states_observed valid history.state (Setoid.refl _)
      history.accumulator (history.accumulator_respects valid) history.start
      (history.accumulator_recovers valid) c reverted

theorem lemma38_reachable_accumulator : lemma38ReachableAccumulator (Γ := Γ) := by
  intro history valid
  dsimp only
  intro c reached
  exact (lemma38_reachable_sound history valid c reached).1

omit [Setoid Γ] in
private theorem reference_reverts (history : History Γ) (φ : Γ → Γ) :
    (history.revertStates φ).map Prod.fst = history.applicationStates.reverse.map Prod.fst := by
  induction history generalizing φ with
  | nil _ => rfl
  | snoc previous effect ih =>
    simp [History.revertStates, History.applicationStates, List.reverse_append, ih]

private theorem projected_contexts {left right : List (Context Γ)}
    (related : ListRelated ContextRelated left right) :
    ListRelated Setoid.r (left.map Prod.fst) (right.map Prod.fst) := by
  induction related with
  | nil => exact .nil
  | cons pair _ ih => exact .cons pair.1 ih

/-- Theorem 16 reads the actual inverse states against the corresponding
application states in reverse order, including the starting and ending states. -/
theorem lemma38_lifo_states (history : History Γ) (valid : history.observedValid) :
    ListRelated Setoid.r
      ((runMaps history.capturedReverts (history.state, history.accumulator)).map Prod.fst)
      (history.applicationStates.reverse.map Prod.fst) := by
  rw [← reference_reverts history history.accumulator]
  exact projected_contexts (actual_reverts_related history valid history.state (Setoid.refl _)
    history.accumulator (history.accumulator_respects valid))

end Tracking

section Generators

variable {Γ : Type u}

/-- Lemma 41(1), in literal function equality. The result applies to
arbitrary generating families, so it also applies to iterator generators. -/
theorem lemma41_generated_commute {G H : (Γ → Γ) → Prop}
    (commute : ∀ f, G f → ∀ g, H g → f ∘ g = g ∘ f)
    {f g : Γ → Γ} (first : Closure G f) (second : Closure H g) :
    f ∘ g = g ∘ f := by
  letI : Setoid Γ := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  funext state
  exact closure_commute
    (fun _ _ _ _ h => congrArg _ h)
    (fun _ _ _ _ h => congrArg _ h)
    (fun f hf g hg state => congrFun (commute f hf g hg) state) first second state

private theorem embed_reaches_only (effect : Effects.Effect Γ) {j : Iterator Γ}
    (reached : Reach (embed effect) j) : j = embed effect := by
  induction reached with
  | root => rfl
  | continuation _ _ next ih =>
    rw [ih] at next
    cases next

/-- Lemma 41(2), with effect composition in the paper's right-to-left order.
The composite forward and every execution-specific inverse factor through two
generators in the union. -/
theorem lemma41_diamond_subset (e f : Effects.Effect Γ) {map : Γ → Γ}
    (generated : Generated (embed (Tracking.diamond e f)) map) :
    Closure (fun g => Generated (embed e) g ∨ Generated (embed f) g) map := by
  induction generated with
  | generator source =>
    cases source with
    | forward reached =>
      obtain rfl := embed_reaches_only _ reached
      refine Closure.compose (f := Tracking.forward e) (g := Tracking.forward f) ?_ ?_
      · exact .generator (Or.inl (.generator (.forward .root)))
      · exact .generator (Or.inr (.generator (.forward .root)))
    | inverse reached state =>
      obtain rfl := embed_reaches_only _ reached
      refine Closure.compose (f := Tracking.inverse f state)
        (g := Tracking.inverse e (Tracking.forward f state)) ?_ ?_
      · exact .generator (Or.inr (.generator (.inverse .root state)))
      · exact .generator (Or.inl (.generator (.inverse .root (Tracking.forward f state))))
  | identity => exact .identity
  | compose _ _ ih₁ ih₂ => exact .compose ih₁ ih₂

theorem lemma41_proved : lemma41 (Γ := Γ) :=
  ⟨fun _ _ commute _ first _ second => lemma41_generated_commute commute first second,
    fun e f _ generated => lemma41_diamond_subset e f generated⟩

end Generators
end Cordis.Results
