import Cordis.PairwiseBirthSemantics

/-! Lemma66's additional Definition65 payload observation, with ALL inherited
global Definition37 witnesses retained. The parent always has two iterations,
so its selected tails are ordinary Definition34-related. Its second iteration
names either a unit child or a child with a two-iteration entry. Those child
components fail even semantic entry agreement, independently of code equality.

The obstruction quantifies over ANY continuation relation observing component
agreement. It does not rely on the stronger literal-payload refinements used
elsewhere. Both tested parent heads are legal; the intervening map is an actual
generator of a second, nonentangled, globally witnessed component. -/
namespace Cordis.PairwiseBirthBoundary
noncomputable section
open Calculus Stages Effects Iterators PairwiseBirthSemantics

abbrev view : View Nat Empty := Empty.elim
def empty : R := fun _ => none
def r1 : R := put empty 0 (fresh (component .parent) none)
def r2 : R := put r1 1 (fresh (component .foreign) none)
def r3 : R := mark r2 0 (.reloading .parent [] view)
def r4 : R := mark r3 1 (.reloading .foreign [] view)

theorem target_empty_keys (state : R) (actor : Nat) (fiber : F)
    (present : state actor = some fiber) (live : fiber.retired = false) :
    Target state actor view := by
  simp only [Target, present]
  exact ⟨live, fun key => nomatch key⟩

theorem step1 : Orchestration.Step program empty r1 :=
  .insert empty 0 (component .parent) ⟨rfl, by simp, by intro _ key; exact nomatch key⟩
theorem step2 : Orchestration.Step program r1 r2 :=
  .insert r1 1 (component .foreign) ⟨rfl, by simp, by intro _ key; exact nomatch key⟩
theorem step3 : Orchestration.Step program r2 r3 := by
  apply Orchestration.Step.begin r2 0 (fresh (component .parent) none) view
  · rfl
  · rfl
  · change some _ ≠ none; simp
  · exact target_empty_keys _ _ _ rfl rfl
theorem step4 : Orchestration.Step program r3 r4 := by
  apply Orchestration.Step.begin r3 1 (fresh (component .foreign) none) view
  · rfl
  · rfl
  · change some _ ≠ none; simp
  · exact target_empty_keys _ _ _ rfl rfl

theorem base_run : Orchestration.Run program empty r4 :=
  .step (.step (.step (.step (.refl _) step1) step2) step3) step4

def base : Gamma := ⟨r4, base_run.reachable_invariants.1,
  SupportUniqueness.reachable_finite program base_run⟩

theorem base_draw : draw base = 2 := draw_preferred base rfl
theorem base_parent : base.val 0 ≠ none := by simp [base, r4, r3, r2, r1, mark, Calculus.modify, put]
theorem base_foreign : base.val 1 ≠ none := by simp [base, r4, r3, r2, r1, mark, Calculus.modify, put]

def foreignMap : Gamma → Gamma := Tracking.forward (meaning 1 .foreign).effect
def moved : Gamma := foreignMap base

theorem foreign_generator : Generator (meaning 1 .foreign) foreignMap := .forward .root

theorem moved_state : moved.val = put base.val 2 (fresh (component .unit) (some 1)) := by
  exact (birth_actual 1 (component .unit) base base_foreign).1.trans (by rw [base_draw])

theorem moved_draw : draw moved ≠ 2 := by
  apply draw_other
  rw [moved_state]
  simp [put]

theorem moved_parent : moved.val 0 ≠ none := by
  rw [moved_state]
  simpa [put] using base_parent

/-- Exact primitive part of a real L-Finish from an empty-origin state. -/
theorem foreign_land : Land program 1 .foreign base.val moved.val (.retire 2) none := by
  rw [moved_state]
  apply Execution.instantiate base.val 1 .foreign (component .unit) 2
  · rfl
  · simpa only [base_draw] using fresh_ready 1 (component .unit) base base_foreign

def afterForeign : R := mark moved.val 1 (.active [.retire 2] view)
theorem foreign_finish : Orchestration.Step program r4 afterForeign := by
  apply Orchestration.Step.finish r4 moved.val 1
    { (fresh (component .foreign) none : F) with phase := .reloading .foreign [] view }
    .foreign [] view (.retire 2)
  · rfl
  · rfl
  · exact target_empty_keys _ _ _ rfl rfl
  · exact foreign_land

theorem foreign_run : Orchestration.Run program empty afterForeign := .step base_run foreign_finish

/-- The actual selected code, not inferred from equality of denotations. -/
def nextCode (code : Code) (state : Gamma) : Option Code :=
  match code with
  | .unit | .foreign | .tailShort | .tailLong => none
  | .twoBirths => some .tailShort
  | .parent => some (if draw state = 2 then .tailShort else .tailLong)

theorem selected_base : nextCode .parent base = some .tailShort := by simp [nextCode, base_draw]
theorem selected_moved : nextCode .parent moved = some .tailLong := by simp [nextCode, moved_draw]

theorem parent_legal_both :
    Land program 0 .parent base.val
      (put base.val 2 (fresh (component .unit) (some 0))) (.retire 2) (some .tailShort) ∧
    Land program 0 .parent moved.val
      (put moved.val (draw moved) (fresh (component .unit) (some 0)))
      (.retire (draw moved)) (some .tailLong) := by
  constructor
  · have landed := Execution.instantiate (program := program) (result := fun code => (program code).next)
      base.val 0 .parent
      (component .unit) 2 rfl (by simpa only [base_draw] using fresh_ready 0 (component .unit) base base_parent)
    simpa [program] using landed
  · have landed := Execution.instantiate (program := program) (result := fun code => (program code).next)
      moved.val 0 .parent
      (component .unit) (draw moved) rfl (fresh_ready 0 (component .unit) moved moved_parent)
    simpa [program, moved_draw] using landed

/-- Weaker than recursive payload agreement: only declarations and the ordinary
Definition34 entry relation are requested at SOME pair of possible actors.
This permits different fresh names and is necessary even under renaming. -/
def ComponentsAgree (left right : Component Empty Code) : Prop :=
  left.requires = right.requires ∧ left.provides = right.provides ∧
    ∃ actor other, RelatedIterator (meaning actor left.entry) (meaning other right.entry)

def payload : Code → Option (Component Empty Code)
  | .unit => none
  | .tailLong => some (component .twoBirths)
  | _ => some (component .unit)

/-- Necessary head condition of Definition65's component observation. -/
def ObservesComponents (relation : Code → Code → Prop) : Prop :=
  ∀ left right first second, relation left right →
    payload left = some first → payload right = some second → ComponentsAgree first second

theorem child_components_disagree : ¬ ComponentsAgree (component .unit) (component .twoBirths) := by
  intro agreement
  obtain ⟨actor, other, entries⟩ := agreement.2.2
  exact child_entries_not_related actor other base entries

theorem reversed_child_components_disagree : ¬ ComponentsAgree (component .twoBirths) (component .unit) := by
  intro agreement
  obtain ⟨actor, other, entries⟩ := agreement.2.2
  exact child_entries_not_related other actor base (related_symm entries)

/-- Clause2 must compare returned continuations using the SAME observation that
detects instantiated components. This is only its root-iteration restriction. -/
def RootYieldStable (relation : Code → Code → Prop) : Prop :=
  ∀ transform, Generated (meaning 1 .foreign) transform → ∀ state,
    OptionRel relation (nextCode .parent (transform state)) (nextCode .parent state)

theorem no_component_observing_yield_stability
    (relation : Code → Code → Prop) (observes : ObservesComponents relation) :
    ¬ RootYieldStable relation := by
  intro stable
  have tails := stable foreignMap (.generator foreign_generator) base
  change OptionRel relation (nextCode .parent moved) (nextCode .parent base) at tails
  rw [selected_moved, selected_base] at tails
  exact reversed_child_components_disagree (observes .tailLong .tailShort _ _ tails rfl rfl)

/-- Ordinary Definition42 ignores child payloads; it actually HOLDS here. -/
theorem ordinary_independence : Independent (meaning 0 .parent) (meaning 1 .foreign) := by
  constructor
  · intro _ _ _ _ _; exact projected_all _ _
  · intro iteration reachable transform _ state
    exact (related_unfold ((all_components_witnessed 0 .parent).reachable reachable).respect
      (show transform state ≈ state from projected_all _ _)).2
  · intro iteration reachable transform _ state
    exact (related_unfold ((all_components_witnessed 1 .foreign).reachable reachable).respect
      (show transform state ≈ state from projected_all _ _)).2

/-- All inherited witnesses, actual nonempty prefix and foreign activation,
and the component-agreement obstruction are jointly inhabited. -/
theorem witnessed_pairwise_payload_boundary :
    (∀ actor code, WitnessedIterator (meaning actor code) ∧ Mediated actor (meaning actor code)) ∧
    Orchestration.Run program empty r4 ∧
    Orchestration.Step program r4 afterForeign ∧
    Independent (meaning 0 .parent) (meaning 1 .foreign) ∧
    ∀ relation, ObservesComponents relation → ¬ RootYieldStable relation :=
  ⟨fun actor code => ⟨all_components_witnessed actor code, all_components_mediated actor code⟩,
    base_run, foreign_finish, ordinary_independence, no_component_observing_yield_stability⟩

end
end Cordis.PairwiseBirthBoundary
