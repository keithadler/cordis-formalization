import Cordis.TypedRegistry
import Cordis.Results.NondeterministicTransposition

/-! Equations (34) and (54) on the registry with key-dependent tables. The
iterator fields are interpreted over typed admitted states throughout, and
the accumulated inverse fields are compared as whole state maps. -/
namespace Cordis.TypedStateObservation

open TypedRegistry Effects Iterators
open Calculus (Phase View)
open PaperEffectEquations (CoeffectOperations)
open TypedCoeffectReplay (pack packed_related)

universe u
variable {Name Key Code : Type u} {Value : Key → Type u} [DecidableEq Name] [DecidableEq Key]

local notation "R" => Registry Name Value Code
local notation "F" => Fiber Name Value Code
local notation "I" => Inverse Name Value

/-- The typed domain used to interpret whole accumulator maps and the
Definition 34 logical relation on stored effect iterators. -/
structure Semantics (Name : Type u) {Key : Type u} (Value : Key → Type u) (Code : Type u)
    [DecidableEq Name] [DecidableEq Key] where
  domain : Registry Name Value Code → Prop
  iterator : Name → Code → Iterator {state // domain state}
  undo_closed : ∀ token state, domain state → domain (TypedRegistry.undo token state)
  keyObservation : ∀ key, Setoid (Value key)

abbrev Semantics.Gamma (sem : Semantics Name Value Code) := {state : R // sem.domain state}

/-- Definitions 33 and 51 on the typed registry. A binding can match a binding
held by a different fiber. Its value remains in its key's own type. -/
def TablesRelatedAt (observe : ∀ key, Setoid (Value key)) (keys : Key → Prop) (left right : R) : Prop :=
  ∀ key, keys key →
    (∀ owner value, tableAt left owner key = some value →
      ∃ other found, tableAt right other key = some found ∧ (observe key).r value found) ∧
    (∀ owner value, tableAt right owner key = some value →
      ∃ other found, tableAt left other key = some found ∧ (observe key).r found value)

omit [DecidableEq Name] [DecidableEq Key] in
theorem TablesRelatedAt.trans {observe : ∀ key, Setoid (Value key)} {keys : Key → Prop}
    {left middle right : R} (first : TablesRelatedAt observe keys left middle)
    (second : TablesRelatedAt observe keys middle right) : TablesRelatedAt observe keys left right := by
  intro key selected
  constructor
  · intro owner value found
    obtain ⟨older, between, bound, firstValue⟩ := (first key selected).1 owner value found
    obtain ⟨current, final, present, secondValue⟩ := (second key selected).1 older between bound
    exact ⟨current, final, present, (observe key).trans firstValue secondValue⟩
  · intro owner value found
    obtain ⟨current, between, bound, secondValue⟩ := (second key selected).2 owner value found
    obtain ⟨older, final, present, firstValue⟩ := (first key selected).2 current between bound
    exact ⟨older, final, present, (observe key).trans firstValue secondValue⟩

omit [DecidableEq Name] in
private theorem encode_tableAt (ops : CoeffectOperations Value) (state : R) (owner : Name) (key : Key) :
    StageRecovery.tableAt (encodeRegistry ops state) owner key = (tableAt state owner key).map (pack key) := by
  cases entry : state owner <;> simp [tableAt, StageRecovery.tableAt, encodeRegistry, encodeFiber, entry]

omit [DecidableEq Name] in
/-- The typed union-table projection is exactly the observation of its
encoding. This comparison works at any set of selected keys. -/
theorem tables_related_encode_iff (ops : CoeffectOperations Value)
    (observe : ∀ key, Setoid (Value key)) (keys : Key → Prop) (left right : R) :
    PaperStateObservation.TablesRelatedAt (fun _ => TypedCoeffectReplay.setoid observe) keys
      (encodeRegistry ops left) (encodeRegistry ops right) ↔ TablesRelatedAt observe keys left right := by
  constructor
  · intro compared key selected
    obtain ⟨forward, backward⟩ := compared key selected
    constructor
    · intro owner value bound
      obtain ⟨other, raw, rawBound, matched⟩ := forward owner (pack key value)
        (by simp [encode_tableAt, bound])
      rw [encode_tableAt] at rawBound
      obtain ⟨found, there, rfl⟩ := Option.map_eq_some_iff.mp rawBound
      exact ⟨other, found, there, (packed_related observe key _ _).mp matched⟩
    · intro owner value bound
      obtain ⟨other, raw, rawBound, matched⟩ := backward owner (pack key value)
        (by simp [encode_tableAt, bound])
      rw [encode_tableAt] at rawBound
      obtain ⟨found, there, rfl⟩ := Option.map_eq_some_iff.mp rawBound
      exact ⟨other, found, there, (packed_related observe key _ _).mp matched⟩
  · intro compared key selected
    obtain ⟨forward, backward⟩ := compared key selected
    constructor
    · intro owner raw rawBound
      rw [encode_tableAt] at rawBound
      obtain ⟨value, bound, rfl⟩ := Option.map_eq_some_iff.mp rawBound
      obtain ⟨other, found, there, matched⟩ := forward owner value bound
      exact ⟨other, pack key found, by simp [encode_tableAt, there], (packed_related observe key _ _).mpr matched⟩
    · intro owner raw rawBound
      rw [encode_tableAt] at rawBound
      obtain ⟨value, bound, rfl⟩ := Option.map_eq_some_iff.mp rawBound
      obtain ⟨other, found, there, matched⟩ := backward owner value bound
      exact ⟨other, pack key found, by simp [encode_tableAt, there], (packed_related observe key _ _).mpr matched⟩

def observation (ops : CoeffectOperations Value) (sem : Semantics Name Value Code)
    (keys : Key → Prop) : Setoid sem.Gamma where
  r left right := TablesRelatedAt sem.keyObservation keys left.val right.val
  iseqv := by
    let raw (state : sem.Gamma) := encodeRegistry ops state.val
    let related : Setoid (RawRegistry Name ops Code) := PaperStateObservation.tablesSetoid (fun _ => TypedCoeffectReplay.setoid sem.keyObservation) keys
    have agreement (a b : sem.Gamma) : related.r (raw a) (raw b) ↔
        TablesRelatedAt sem.keyObservation keys a.val b.val :=
      tables_related_encode_iff ops sem.keyObservation keys a.val b.val
    exact ⟨fun a => (agreement a a).mp (related.refl _),
      fun {a b} same => (agreement b a).mp (related.symm ((agreement a b).mpr same)),
      fun {a b c} first second => (agreement a c).mp
        (related.trans ((agreement a b).mpr first) ((agreement b c).mpr second))⟩

abbrev base (ops : CoeffectOperations Value) (sem : Semantics Name Value Code) : Setoid sem.Gamma :=
  observation ops sem (fun _ => True)

variable (ops : CoeffectOperations Value) (sem : Semantics Name Value Code)

/-- The table frame of a state map at every key outside its interface.
Retirement and changes to an empty registry entry preserve this frame. -/
def FramesOutside (keys : Key → Prop) (map : sem.Gamma → sem.Gamma) : Prop :=
  ∀ input owner key, ¬ keys key →
    tableAt (map input).val owner key = tableAt input.val owner key

/-- Definition 40 generators give exactly the reachable heads and their
captured inverses to which the table frame applies. -/
def IteratorFramesOutside (keys : Key → Prop) (root : Iterator sem.Gamma) : Prop :=
  ∀ map, Iterators.Generator root map → FramesOutside sem keys map

private theorem full_from_scoped_outputs (keys : Key → Prop) {left right : sem.Gamma → sem.Gamma}
    (leftFrame : FramesOutside sem keys left) (rightFrame : FramesOutside sem keys right)
    {input probe : sem.Gamma}
    (related : (base ops sem).r input probe)
    (outputs : (observation ops sem keys).r (left input) (right probe)) :
    (base ops sem).r (left input) (right probe) := by
  classical
  intro key _
  by_cases selected : keys key
  · exact outputs key selected
  · obtain ⟨forward, backward⟩ := related key trivial
    constructor
    · intro owner value found
      rw [leftFrame input owner key selected] at found
      obtain ⟨other, result, reflects, compared⟩ := forward owner value found
      exact ⟨other, result, (rightFrame probe other key selected).trans reflects, compared⟩
    · intro owner value found
      rw [rightFrame probe owner key selected] at found
      obtain ⟨other, result, reflects, compared⟩ := backward owner value found
      exact ⟨other, result, (leftFrame input other key selected).trans reflects, compared⟩

/-- Related maps on the interface are related on all keys when each leaves
the complementary tables unchanged. -/
theorem maps_related_of_scoped (keys : Key → Prop) {left right : sem.Gamma → sem.Gamma}
    (restricted : @Effects.Related sem.Gamma (observation ops sem keys) left right)
    (leftFrame : FramesOutside sem keys left) (rightFrame : FramesOutside sem keys right) :
    @Effects.Related sem.Gamma (base ops sem) left right := by
  intro input probe related
  exact full_from_scoped_outputs ops sem keys leftFrame rightFrame related
    (restricted (fun key _ => related key trivial))

/-- A scoped Eq. (35) iterator comparison extends to the full observation.
The coinduction tracks each continuation's reachability from its own root,
which supplies the two frames for every later head and inverse. -/
theorem iterator_related_of_scoped (keys : Key → Prop) {left right : Iterator sem.Gamma}
    (restricted : @RelatedIterator sem.Gamma (observation ops sem keys) left right)
    (leftFrame : IteratorFramesOutside sem keys left) (rightFrame : IteratorFramesOutside sem keys right) :
    @RelatedIterator sem.Gamma (base ops sem) left right := by
  let candidates (l r : Iterator sem.Gamma) : Prop :=
    Reach left l ∧ Reach right r ∧ @RelatedIterator sem.Gamma (observation ops sem keys) l r
  apply @related_coinduction sem.Gamma (base ops sem) candidates
  · intro l r parents input probe related
    obtain ⟨leftReach, rightReach, weak⟩ := parents
    have scopedInput : (observation ops sem keys).r input probe := fun key _ => related key trivial
    obtain ⟨forwards, inverses, continuation⟩ :=
      @related_unfold _ (observation ops sem keys) _ _ weak input probe scopedInput
    refine ⟨full_from_scoped_outputs ops sem keys
      (leftFrame _ (.forward leftReach)) (rightFrame _ (.forward rightReach)) related forwards,
      maps_related_of_scoped ops sem keys inverses
        (leftFrame _ (.inverse leftReach input)) (rightFrame _ (.inverse rightReach probe)), ?_⟩
    cases leftNext : l.next input <;> cases rightNext : r.next probe <;>
      simp only [leftNext, rightNext, OptionRel] at continuation ⊢
    exact ⟨.continuation leftReach input leftNext,
      .continuation rightReach probe rightNext, continuation⟩
  · exact ⟨.root, .root, restricted⟩

/-- Every forward or captured inverse generator of a scoped witnessed
iterator respects the full table observation under the same frame. -/
theorem generator_respects_on_all_keys (keys : Key → Prop) {root : Iterator sem.Gamma}
    (restricted : @WitnessedIterator sem.Gamma (observation ops sem keys) root)
    (frame : IteratorFramesOutside sem keys root) {map : sem.Gamma → sem.Gamma}
    (generated : Iterators.Generator root map) :
    @Effects.Respects sem.Gamma (base ops sem) map :=
  maps_related_of_scoped ops sem keys
    (@Iterators.generator_respects _ (observation ops sem keys) root restricted map generated)
    (frame map generated) (frame map generated)

/-- Definition 37's witness extends to all keys. The recovery computation
is the composition of a framed forward and its framed captured inverse.
Its scoped recovery therefore also recovers the full observation. -/
theorem witnessed_on_all_keys (keys : Key → Prop) {iterator : Iterator sem.Gamma}
    (restricted : @WitnessedIterator sem.Gamma (observation ops sem keys) iterator)
    (frame : IteratorFramesOutside sem keys iterator) :
    @WitnessedIterator sem.Gamma (base ops sem) iterator := by
  letI : Setoid sem.Gamma := base ops sem
  induction restricted with
  | node effect next related recover continuation earlier =>
    let root : Iterator sem.Gamma := .node effect next
    refine .node effect next (iterator_related_of_scoped ops sem keys related frame frame) ?_ ?_
    · intro input
      let recovery := (Tracking.inverse effect input) ∘ Tracking.forward effect
      have recoveryFrame : FramesOutside sem keys recovery := by
        intro before owner key outside
        exact (frame _ (.inverse (show Reach root root from .root) input)
          (Tracking.forward effect before) owner key outside).trans
          (frame _ (.forward (show Reach root root from .root)) before owner key outside)
      exact full_from_scoped_outputs ops sem keys recoveryFrame
        (fun _ _ _ _ => rfl) ((base ops sem).refl input) (recover input)
    · intro input child selected
      apply earlier input child selected
      have childReach : Reach root child := .continuation .root input selected
      have route : ∀ tail, Reach child tail → Reach root tail := by
        intro tail path
        induction path with
        | root => exact childReach
        | continuation prior input found earlier =>
          exact .continuation earlier input found
      intro map generated
      cases generated with
      | forward reached => exact frame _ (.forward (route _ reached))
      | inverse reached probe => exact frame _ (.inverse (route _ reached) probe)

def inverse (token : I) (state : sem.Gamma) : sem.Gamma :=
  ⟨TypedRegistry.undo token state.val, sem.undo_closed token state.val state.property⟩

def accumulator : List I → sem.Gamma → sem.Gamma
  | [], state => state
  | token :: rest, state => accumulator rest (inverse sem token state)

theorem accumulator_value (tokens : List I) (state : sem.Gamma) :
    (accumulator sem tokens state).val = TypedRegistry.discharge tokens state.val := by
  induction tokens generalizing state with
  | nil => rfl
  | cons token rest ih => exact ih (inverse sem token state)

def AccumulatorRelated (left right : List I) : Prop :=
  @Effects.Related sem.Gamma (base ops sem) (accumulator sem left) (accumulator sem right)

def CodeRelated (actor : Name) (left right : Code) : Prop :=
  @RelatedIterator sem.Gamma (base ops sem) (sem.iterator actor left) (sem.iterator actor right)

inductive PhaseRelated (actor : Name) (required : Key → Bool) :
    Phase Name Key Code I → Phase Name Key Code I → Prop
  | inactive : PhaseRelated actor required .inactive .inactive
  | reloading {left right a b v w} : CodeRelated ops sem actor left right →
      AccumulatorRelated ops sem a b → PaperStateObservation.ViewRelated required v w →
      PhaseRelated actor required (.reloading left a v) (.reloading right b w)
  | active {a b v w} : AccumulatorRelated ops sem a b → PaperStateObservation.ViewRelated required v w →
      PhaseRelated actor required (.active a v) (.active b w)
  | unloading {a b v w} : AccumulatorRelated ops sem a b → PaperStateObservation.ViewRelated required v w →
      PhaseRelated actor required (.unloading a v) (.unloading b w)

structure FiberRelated (actor : Name) (left right : F) : Prop where
  requires : left.component.requires = right.component.requires
  provides : left.component.provides = right.component.provides
  entry : CodeRelated ops sem actor left.component.entry right.component.entry
  parent : left.parent = right.parent
  retired : left.retired = right.retired
  phase : PhaseRelated ops sem actor left.component.requires left.phase right.phase

/-- Equation (54) uses the typed table observation at every key, agreement on
the registry domain and control fields, and Definition 34 for function fields. -/
def Related (left right : R) : Prop :=
  TablesRelatedAt sem.keyObservation (fun _ => True) left right ∧
    ∀ actor, OptionRel (FiberRelated ops sem actor) (left actor) (right actor)

private theorem accumulator_respects (stack : List I)
    (captures : ∀ token ∈ stack, @Effects.Respects sem.Gamma (base ops sem) (inverse sem token)) :
    AccumulatorRelated ops sem stack stack := by
  induction stack with
  | nil => exact fun {_ _} observed => observed
  | cons token rest ih =>
    intro left right observed
    exact ih (fun inverse member => captures inverse (by simp [member]))
      (captures token (by simp) observed)

/-- The encoded structural comparison yields agreement of paired inverse
words on the same probe. Respect of actual captured maps extends agreement
to the two related probes required by Definition 34. -/
theorem accumulator_related_of_encoded {left right : List I}
    (paired : @StageSimulation.StackRelated Name Key (Scalar ops)
      (TypedCoeffectReplay.setoid sem.keyObservation)
      (left.map (encodeInverse ops)) (right.map (encodeInverse ops)))
    (captures : ∀ token ∈ right, @Effects.Respects sem.Gamma (base ops sem) (inverse sem token)) :
    AccumulatorRelated ops sem left right := by
  letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid sem.keyObservation
  intro before after observed
  have sameInput := Results.captured_stack_tables paired (StageRecovery.tables_refl (encodeRegistry ops before.val))
  rw [← encode_discharge, ← encode_discharge] at sameInput
  have raw := PaperStateObservation.tables_of_homogeneous
    (sameInput.projected (fun _ => True)) (fun _ _ _ same => same)
  have typed := (tables_related_encode_iff ops sem.keyObservation (fun _ => True) _ _).mp raw
  have first : (base ops sem).r (accumulator sem left before) (accumulator sem right before) := by
    change TablesRelatedAt sem.keyObservation (fun _ => True)
      (accumulator sem left before).val (accumulator sem right before).val
    simpa only [accumulator_value] using typed
  exact (base ops sem).trans first (accumulator_respects ops sem right captures observed)

private theorem phase_related_of_encoded (actor : Name) (required : Key → Bool)
    {left right : Phase Name Key Code I}
    (paired : @StageSimulation.PhaseRelated Name Key (Scalar ops) Code
      (TypedCoeffectReplay.setoid sem.keyObservation) Eq (encodePhase ops left) (encodePhase ops right))
    (current : ∀ code stack view, right = .reloading code stack view →
      @WitnessedIterator sem.Gamma (base ops sem) (sem.iterator actor code))
    (captures : ∀ token ∈ right.accumulator, @Effects.Respects sem.Gamma (base ops sem) (inverse sem token)) :
    PhaseRelated ops sem actor required left right := by
  letI : Setoid sem.Gamma := base ops sem
  cases left <;> cases right <;> cases paired
  case inactive.inactive.inactive => exact .inactive
  case reloading.reloading.reloading _ _ _ _ codes stacks =>
    cases codes
    exact .reloading (current _ _ _ rfl).respect
      (accumulator_related_of_encoded ops sem stacks captures) (fun _ _ => rfl)
  case active.active.active _ _ _ stacks =>
    exact .active (accumulator_related_of_encoded ops sem stacks captures) (fun _ _ => rfl)
  case unloading.unloading.unloading _ _ _ stacks =>
    exact .unloading (accumulator_related_of_encoded ops sem stacks captures) (fun _ _ => rfl)

/-- Transport the structural comparison of the encoded endpoints to
Equation (54) on native typed registries. Witnesses for the stored iterators
and respect of actual inverse captures identify their semantic fields. -/
theorem related_of_encoded {left right : R}
    (paired : @StageSimulation.Related Name Key (Scalar ops) Code PUnit.{u + 1}
      (TypedCoeffectReplay.setoid sem.keyObservation) Eq (encodeRegistry ops left) (encodeRegistry ops right))
    (entries : ∀ actor fiber, right actor = some fiber →
      @WitnessedIterator sem.Gamma (base ops sem) (sem.iterator actor fiber.component.entry))
    (current : ∀ actor fiber, right actor = some fiber → ∀ code stack view,
      fiber.phase = .reloading code stack view →
      @WitnessedIterator sem.Gamma (base ops sem) (sem.iterator actor code))
    (captures : ∀ actor fiber, right actor = some fiber → ∀ token ∈ fiber.phase.accumulator,
      @Effects.Respects sem.Gamma (base ops sem) (inverse sem token)) :
    Related ops sem left right := by
  letI : Setoid sem.Gamma := base ops sem
  letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid sem.keyObservation
  have raw : StageRecovery.TablesRelated (encodeRegistry ops left) (encodeRegistry ops right) := by
    intro actor key
    have fields := paired actor
    cases first : left actor <;> cases second : right actor <;>
      simp_all only [OptionRel, encodeRegistry, StageRecovery.tableAt, Option.map_none, Option.map_some,
        Option.bind_none, Option.bind_some]
    exact fields.table key
  refine ⟨(tables_related_encode_iff ops sem.keyObservation (fun _ => True) _ _).mp
    (PaperStateObservation.tables_of_homogeneous (raw.projected (fun _ => True)) (fun _ _ _ same => same)), ?_⟩
  intro actor
  have fields := paired actor
  cases first : left actor <;> cases second : right actor <;>
    simp_all only [OptionRel, encodeRegistry, Option.map_none, Option.map_some]
  rename_i a b
  refine ⟨fields.component.requires, fields.component.provides, ?_, fields.parent, fields.retired, ?_⟩
  · change @RelatedIterator sem.Gamma (base ops sem) (sem.iterator actor a.component.entry)
      (sem.iterator actor b.component.entry)
    rw [show a.component.entry = b.component.entry from fields.component.entry]
    exact (entries actor b second).respect
  · exact phase_related_of_encoded ops sem actor a.component.requires fields.phase
      (current actor b second) (captures actor b second)

end Cordis.TypedStateObservation
