import Cordis.IndexedTrace
import Cordis.RuleEvaluation

/-! Theorem70's interval statements over indexed applications of the actual
nine rules. View/declaration transport is derived one rule at a time. Strict
episode nesting follows from L-Begin's active-provider premise and L-Unload's
retained-consumer guard, with no assumed provider lifetime relation. -/
namespace Cordis.OrderingIntervals
open Calculus Stages Indexed
universe u
variable {Name Key Value Code Error : Type u}
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
variable [DecidableEq Name] [DecidableEq Key]

omit [DecidableEq Name] [DecidableEq Key] in
theorem installed_view (r : R) (name : Name) (installed : ControlFrame.viewAt r name ≠ none) :
    ∃ fiber view, r name = some fiber ∧ fiber.phase.committed = some view := by
  cases present : r name with
  | none => simp [ControlFrame.viewAt, present] at installed
  | some fiber =>
    cases committed : fiber.phase.committed with
    | none => simp [ControlFrame.viewAt, present, committed] at installed
    | some view => exact ⟨fiber, view, rfl, committed⟩

/-- Lemma67's pinned-provider case, before any total-map replay convention is
chosen. The only possible actual rules are O-Retire and L-Leave, both of which
have identity state map in Definition58. -/
theorem pinned_provider_rule {program : Code → Instruction Name Key Value Code Error}
    {r s : R} {rule : Labeled.Rule} {consumer provider : Name} {key : Key}
    (supported : Ordering.Supported r) (demand : Ordering.Demand r consumer provider key)
    (step : Labeled.Step program rule provider r s) : rule = .retire ∨ rule = .leave := by
  obtain ⟨different, fiber, present, retained, _⟩ := supported consumer provider key demand
  have relied := Ordering.demand_relied r consumer provider key demand different
  cases step with
  | insert _ _ component parent ready => simp [Insertable, present] at ready
  | retire => exact .inl rfl
  | remove _ _ ready =>
    simp only [Removable, present] at ready
    have inactive : fiber.phase = .inactive := ready.2.1
    simp [inactive, Ordering.Retained] at retained
  | begin _ _ entry view found phase _ _ =>
    have same : fiber = entry := Option.some.inj (present.symm.trans found)
    simp [same, phase, Ordering.Retained] at retained
  | iter _ middle _ entry code acc view inverse next found phase _ _ =>
    have same : fiber = entry := Option.some.inj (present.symm.trans found)
    simp [same, phase, Ordering.Retained] at retained
  | finish _ middle _ entry code acc view inverse found phase _ _ =>
    have same : fiber = entry := Option.some.inj (present.symm.trans found)
    simp [same, phase, Ordering.Retained] at retained
  | divert _ middle _ entry code acc view tail found phase _ _ =>
    have same : fiber = entry := Option.some.inj (present.symm.trans found)
    simp [same, phase, Ordering.Retained] at retained
  | leave => exact .inr rfl
  | unload _ _ entry acc view found phase unrelied => exact False.elim (unrelied relied)

/-- Current declaration overlap identifies the retained provider: its bound
key belongs to its declaration, and registered provisions are disjoint. No
historical/global uniqueness of provision ownership is assumed. -/
theorem declared_provider_is_committed (r : R) (name provider : Name)
    (consumer supplying : F) (view : View Name Key) (key : Key)
    (supported : Ordering.Supported r) (owned : Safety.Owned r) (disjoint : WellFormed.Disjoint r)
    (present : r name = some consumer) (providerPresent : r provider = some supplying)
    (committed : consumer.phase.committed = some view)
    (required : consumer.component.requires key = true) (provided : supplying.component.provides key = true) :
    view key = provider := by
  obtain ⟨_, retained, found, _, bound⟩ :=
    Ordering.retained_provider r name consumer view key supported present committed required
  have declares := owned (view key) retained key found bound
  by_cases same : view key = provider
  · exact same
  · exact False.elim (disjoint (view key) provider retained supplying found providerPresent same key
      ⟨declares, provided⟩)

/-- Lemma67(1)'s declaration-entanglement premise now implies the pinned
rule classification, rather than requiring the provider name in the view as an
extra hypothesis. Both invariant premises are derived for empty-origin traces. -/
theorem entangled_provider_rule {program : Code → Instruction Name Key Value Code Error}
    {r s : R} {rule : Labeled.Rule} (name provider : Name)
    (consumer supplying : F) (view : View Name Key) (key : Key)
    (supported : Ordering.Supported r) (owned : Safety.Owned r) (disjoint : WellFormed.Disjoint r)
    (different : name ≠ provider) (present : r name = some consumer)
    (providerPresent : r provider = some supplying) (committed : consumer.phase.committed = some view)
    (provided : supplying.component.provides key = true)
    (overlap : consumer.component.requires key = true ∨ consumer.component.provides key = true)
    (step : Labeled.Step program rule provider r s) : rule = .retire ∨ rule = .leave := by
  rcases overlap with required | conflict
  · have selected := declared_provider_is_committed r name provider consumer supplying view key
      supported owned disjoint present providerPresent committed required provided
    exact pinned_provider_rule supported ⟨consumer, view, present, required, committed, selected⟩ step
  · exact False.elim (disjoint name provider consumer supplying present providerPresent different key
      ⟨conflict, provided⟩)

/-- The consumer half of Lemma67(3): a reloading provider has no installed
consumer of its provision. This follows from retained-provider support and
current disjoint declarations, not a scheduling-order assumption. -/
theorem reloading_has_no_installed_consumer (r : R) (name provider : Name)
    (consumer supplying : F) (key : Key) (code : Code)
    (acc : List (Inverse Name Key Value)) (providerView : View Name Key)
    (supported : Ordering.Supported r) (owned : Safety.Owned r) (disjoint : WellFormed.Disjoint r)
    (present : r name = some consumer) (providerPresent : r provider = some supplying)
    (phase : supplying.phase = .reloading code acc providerView)
    (required : consumer.component.requires key = true) (provided : supplying.component.provides key = true) :
    consumer.phase.committed = none := by
  cases committed : consumer.phase.committed with
  | none => rfl
  | some view =>
    have selected := declared_provider_is_committed r name provider consumer supplying view key
      supported owned disjoint present providerPresent committed required provided
    obtain ⟨_, retained, found, retainedPhase, _⟩ :=
      Ordering.retained_provider r name consumer view key supported present committed required
    have foundProvider : r provider = some retained := by simpa only [selected] using found
    have same : supplying = retained := Option.some.inj (providerPresent.symm.trans foundProvider)
    simp [← same, phase, Ordering.Retained] at retainedPhase

omit [DecidableEq Key] in
theorem reloading_dependency_blocks_target (r : R) (name provider : Name)
    (consumer supplying : F) (key : Key) (code : Code)
    (acc : List (Inverse Name Key Value)) (providerView : View Name Key)
    (owned : Safety.Owned r) (disjoint : WellFormed.Disjoint r)
    (present : r name = some consumer) (providerPresent : r provider = some supplying)
    (phase : supplying.phase = .reloading code acc providerView)
    (required : consumer.component.requires key = true) (provided : supplying.component.provides key = true) :
    ∀ view, ¬ Target r name view := by
  intro view target
  have targetBinding := target
  simp only [Target, present] at targetBinding
  have available := targetBinding.2 key required
  cases found : r (view key) with
  | none => simp [found] at available
  | some selected =>
    have facts : selected.phase.available ∧ selected.table key ≠ none := by simpa [found] using available
    have selectedProvides := owned (view key) selected key found facts.2
    have sameName : view key = provider := by
      by_cases same : view key = provider
      · exact same
      · exact False.elim (disjoint (view key) provider selected supplying found providerPresent same key
          ⟨selectedProvides, provided⟩)
    have foundProvider : r provider = some selected := by simpa only [sameName] using found
    have same : supplying = selected := Option.some.inj (providerPresent.symm.trans foundProvider)
    have impossible := facts.1
    simp [← same, phase, Phase.available] at impossible

/-- When the other member is a consumer of a reloading fiber, its existing
entry can take only the two orchestration edits. In particular it cannot Begin,
land an iteration, or Unload. Together with `entangled_provider_rule`, this
establishes the rule-exclusion content of Lemma67(3) for registered fibers. -/
theorem reloading_consumer_rule {program : Code → Instruction Name Key Value Code Error}
    {r s : R} {rule : Labeled.Rule} (name provider : Name)
    (consumer supplying : F) (key : Key) (code : Code)
    (acc : List (Inverse Name Key Value)) (providerView : View Name Key)
    (supported : Ordering.Supported r) (owned : Safety.Owned r) (disjoint : WellFormed.Disjoint r)
    (present : r name = some consumer) (providerPresent : r provider = some supplying)
    (phase : supplying.phase = .reloading code acc providerView)
    (required : consumer.component.requires key = true) (provided : supplying.component.provides key = true)
    (step : Labeled.Step program rule name r s) : rule = .retire ∨ rule = .remove := by
  have uninstalled := reloading_has_no_installed_consumer r name provider consumer supplying key code acc providerView
    supported owned disjoint present providerPresent phase required provided
  have inactive : consumer.phase = .inactive := by
    cases h : consumer.phase <;> simp_all [Phase.committed]
  have blocked := reloading_dependency_blocks_target r name provider consumer supplying key code acc providerView
    owned disjoint present providerPresent phase required provided
  cases step with
  | insert _ _ component parent ready => simp [Insertable, present] at ready
  | retire => exact .inl rfl
  | remove => exact .inr rfl
  | begin _ _ entry view found _ _ target => exact False.elim (blocked view target)
  | iter _ middle _ entry c a view inverse next found reloading _ _ =>
    have same : consumer = entry := Option.some.inj (present.symm.trans found)
    simp [same, reloading] at inactive
  | finish _ middle _ entry c a view inverse found reloading _ _ =>
    have same : consumer = entry := Option.some.inj (present.symm.trans found)
    simp [same, reloading] at inactive
  | divert _ middle _ entry c a view tail found reloading _ _ =>
    have same : consumer = entry := Option.some.inj (present.symm.trans found)
    simp [same, reloading] at inactive
  | leave _ _ entry a view found active _ =>
    have same : consumer = entry := Option.some.inj (present.symm.trans found)
    simp [same, active] at inactive
  | unload _ _ entry a view found unloading _ =>
    have same : consumer = entry := Option.some.inj (present.symm.trans found)
    simp [same, unloading] at inactive

end Cordis.OrderingIntervals
