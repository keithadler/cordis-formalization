import Cordis.ReplayWitnessCompatibility
import Cordis.MediatedRegistryDomain
import Cordis.PaperObservationEquations
import Cordis.TableFrame
import Cordis.Orchestration
import Cordis.Independence
import Cordis.Coeffects
import Cordis.GuardedApplications
import Cordis.TranspositionActivation
import Cordis.StageSimulation
import Cordis.EntangledApplications
import Cordis.EpisodeRecovery
import Cordis.TranspositionPhases
import Cordis.StageRecovery
import Cordis.MediatedRegistryFrames

/-! Equation (54) uses Definition 34's union-table base for iterator and
accumulator fields. The semantic parameters give the registry domain and
code denotation. Domain closure lifts the individual inverses, whose
composites are compared as functions. Committed views are compared only
at declared keys. -/
namespace Cordis.PaperStateObservation
noncomputable section
open Calculus Stages Effects Iterators StageRecovery
universe u
variable {Name Key Value Code Error : Type u}
variable [DecidableEq Name] [DecidableEq Key]
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
local notation "I" => Inverse Name Key Value
set_option linter.unusedSectionVars false

structure Semantics (Name Key Value Code Error : Type u) [DecidableEq Name] [DecidableEq Key] where
  domain : Registry Name Key Value Code (Inverse Name Key Value) Error → Prop
  iterator : Name → Code → Iterator {state // domain state}
  undo : Inverse Name Key Value → Registry Name Key Value Code (Inverse Name Key Value) Error →
    Registry Name Key Value Code (Inverse Name Key Value) Error
  undo_closed : ∀ inverse state, domain state → domain (undo inverse state)
  undo_unit : ∀ state, undo .unit state = state
  undo_retire : ∀ child state, undo (.retire child) state = Calculus.retire state child
  keyObservation : Key → Setoid Value

abbrev Semantics.Gamma (sem : Semantics Name Key Value Code Error) := {state : R // sem.domain state}

/-- Definitions 33 and 51. Each key uses its own observation on values.
The union drops owner coordinates. Ownership and disjointness make it a
partial function on the admitted registry domain. -/
def TablesRelatedAt (observe : Key → Setoid Value) (keys : Key → Prop) (left right : R) : Prop :=
  ∀ key, keys key →
    (∀ owner value, tableAt left owner key = some value →
      ∃ other found, tableAt right other key = some found ∧ (observe key).r value found) ∧
    (∀ owner value, tableAt right owner key = some value →
      ∃ other found, tableAt left other key = some found ∧ (observe key).r found value)

def tablesSetoid (observe : Key → Setoid Value) (keys : Key → Prop) : Setoid R where
  r := TablesRelatedAt observe keys
  iseqv := by
    constructor
    · intro state key _
      exact ⟨fun owner value bound => ⟨owner, value, bound, (observe key).iseqv.refl value⟩,
        fun owner value bound => ⟨owner, value, bound, (observe key).iseqv.refl value⟩⟩
    · intro left right related key selected
      obtain ⟨forward, backward⟩ := related key selected
      exact ⟨fun owner value bound => by
        obtain ⟨other, found, there, compared⟩ := backward owner value bound
        exact ⟨other, found, there, (observe key).iseqv.symm compared⟩, fun owner value bound => by
        obtain ⟨other, found, there, compared⟩ := forward owner value bound
        exact ⟨other, found, there, (observe key).iseqv.symm compared⟩⟩
    · intro left middle right first second key selected
      obtain ⟨firstForward, firstBackward⟩ := first key selected
      obtain ⟨secondForward, secondBackward⟩ := second key selected
      exact ⟨fun owner value bound => by
        obtain ⟨atMiddle, v, there, earlier⟩ := firstForward owner value bound
        obtain ⟨atRight, w, there, later⟩ := secondForward atMiddle v there
        exact ⟨atRight, w, there, (observe key).iseqv.trans earlier later⟩, fun owner value bound => by
        obtain ⟨atMiddle, w, there, later⟩ := secondBackward owner value bound
        obtain ⟨atLeft, v, there, earlier⟩ := firstBackward atMiddle w there
        exact ⟨atLeft, v, there, (observe key).iseqv.trans earlier later⟩⟩

def observation (sem : Semantics Name Key Value Code Error) (keys : Key → Prop) : Setoid sem.Gamma where
  r left right := TablesRelatedAt sem.keyObservation keys left.val right.val
  iseqv :=
    ⟨fun state => (tablesSetoid sem.keyObservation _).iseqv.refl state.val,
      fun related => (tablesSetoid sem.keyObservation _).iseqv.symm related,
      fun first second => (tablesSetoid sem.keyObservation _).iseqv.trans first second⟩

abbrev base (sem : Semantics Name Key Value Code Error) : Setoid sem.Gamma :=
  observation sem (fun _ => True)

theorem tables_of_homogeneous [Setoid Value] {observe : Key → Setoid Value} {keys : Key → Prop}
    {left right : R} (related : ProjectedRelated keys left right)
    (compatible : ∀ key (v w : Value), v ≈ w → (observe key).r v w) :
    TablesRelatedAt observe keys left right := by
  intro key selected
  obtain ⟨forward, backward⟩ := related key selected
  exact ⟨fun owner value bound => by
    obtain ⟨other, found, there, compared⟩ := forward owner value bound
    exact ⟨other, found, there, compatible key _ _ compared⟩, fun owner value bound => by
    obtain ⟨other, found, there, compared⟩ := backward owner value bound
    exact ⟨other, found, there, compatible key _ _ compared⟩⟩

variable (sem : Semantics Name Key Value Code Error)
local instance : Setoid sem.Gamma := base sem

def inverse (token : I) (state : sem.Gamma) : sem.Gamma :=
  ⟨sem.undo token state.val, sem.undo_closed token state.val state.property⟩

def accumulator : List I → sem.Gamma → sem.Gamma
  | [], state => state
  | token :: rest, state => accumulator rest (inverse sem token state)

theorem accumulator_actual (tokens : List I) (state : sem.Gamma) :
    (accumulator sem tokens state).val = Calculus.discharge sem.undo tokens state.val := by
  induction tokens generalizing state with
  | nil => rfl
  | cons token rest ih => exact ih (inverse sem token state)

def AccumulatorRelated (left right : List I) : Prop :=
  Effects.Related (accumulator sem left) (accumulator sem right)

def CodeRelated (actor : Name) (left right : Code) : Prop :=
  RelatedIterator (sem.iterator actor left) (sem.iterator actor right)

def ViewRelated (required : Key → Bool) (left right : View Name Key) : Prop :=
  ∀ key, required key = true → left key = right key

inductive PhaseRelated (actor : Name) (required : Key → Bool) :
    Phase Name Key Code I → Phase Name Key Code I → Prop
  | inactive : PhaseRelated actor required .inactive .inactive
  | reloading {left right a b v w} : CodeRelated sem actor left right →
      AccumulatorRelated sem a b → ViewRelated required v w →
      PhaseRelated actor required (.reloading left a v) (.reloading right b w)
  | active {a b v w} : AccumulatorRelated sem a b → ViewRelated required v w →
      PhaseRelated actor required (.active a v) (.active b w)
  | unloading {a b v w} : AccumulatorRelated sem a b → ViewRelated required v w →
      PhaseRelated actor required (.unloading a v) (.unloading b w)

structure FiberRelated (actor : Name) (left right : F) : Prop where
  requires : left.component.requires = right.component.requires
  provides : left.component.provides = right.component.provides
  entry : CodeRelated sem actor left.component.entry right.component.entry
  parent : left.parent = right.parent
  retired : left.retired = right.retired
  phase : PhaseRelated sem actor left.component.requires left.phase right.phase

/-- The field formula extends to raw registries; its paper interpretation is
the restriction to `sem.domain` at both endpoints. -/
def Related (left right : R) : Prop :=
  TablesRelatedAt sem.keyObservation (fun _ => True) left right ∧
    ∀ actor, OptionRel (FiberRelated sem actor) (left actor) (right actor)

theorem domain_agrees {left right : R} (related : Related sem left right) (actor : Name) :
    left actor = none ↔ right actor = none := by
  have pair := related.2 actor
  cases l : left actor <;> cases r : right actor <;> simp_all [OptionRel]

theorem fields {left right : R} (related : Related sem left right) (actor : Name)
    (a b : F) (first : left actor = some a) (second : right actor = some b) : FiberRelated sem actor a b := by
  simpa only [first, second, OptionRel] using related.2 actor

theorem accumulator_cons {a b : I} {left right : List I}
    (heads : Effects.Related (inverse sem a) (inverse sem b))
    (tails : AccumulatorRelated sem left right) : AccumulatorRelated sem (a :: left) (b :: right) :=
  fun {_ _} observed => tails (heads observed)

theorem accumulator_respects (tokens : List I)
    (captured : ∀ token ∈ tokens, Effects.Respects (inverse sem token)) : AccumulatorRelated sem tokens tokens := by
  induction tokens with
  | nil => exact fun {_ _} observed => observed
  | cons token rest ih =>
    exact accumulator_cons sem (captured token (by simp)) (ih (fun token member => captured token (by simp [member])))

/-- A phase edit changes no table observation. The replacement's code and
whole cleanup map still need their stated semantic relations. -/
theorem mark_related {left right : R} (related : Related sem left right)
    (actor : Name) (a b : Phase Name Key Code I)
    (replacement : ∀ fiber, left actor = some fiber → PhaseRelated sem actor fiber.component.requires a b) :
    Related sem (mark left actor a) (mark right actor b) := by
  refine ⟨?_, ?_⟩
  · simpa only [TablesRelatedAt, tableAt_mark] using related.1
  · intro other
    by_cases own : other = actor
    · subst other
      have pair := related.2 actor
      cases first : left actor <;> cases second : right actor <;>
        simp_all only [OptionRel, mark, Calculus.modify, if_pos, Option.map_none, Option.map_some]
      rename_i l r
      exact ⟨pair.requires, pair.provides, pair.entry, pair.parent, pair.retired, replacement l rfl⟩
    · simpa only [mark, Calculus.modify, if_neg own] using related.2 other

theorem phase_self (actor : Name) (required : Key → Bool) (phase : Phase Name Key Code I)
    (current : ∀ code stack view, phase = .reloading code stack view →
      WitnessedIterator (sem.iterator actor code))
    (captured : ∀ token ∈ phase.accumulator, Effects.Respects (inverse sem token)) :
    PhaseRelated sem actor required phase phase := by
  cases phase with
  | inactive => exact .inactive
  | reloading code stack view =>
    exact .reloading (current code stack view rfl).respect (accumulator_respects sem stack captured) (fun _ _ => rfl)
  | active stack view => exact .active (accumulator_respects sem stack captured) (fun _ _ => rfl)
  | unloading stack view => exact .unloading (accumulator_respects sem stack captured) (fun _ _ => rfl)

/-- Reflexivity is derived from witnessed stored iterators and the actually
captured maps' respect. It is not granted to arbitrary function-valued fields. -/
theorem witnessed_state_self (state : R)
    (entries : ∀ actor fiber, state actor = some fiber → WitnessedIterator (sem.iterator actor fiber.component.entry))
    (current : ∀ actor fiber, state actor = some fiber → ∀ code stack view,
      fiber.phase = .reloading code stack view → WitnessedIterator (sem.iterator actor code))
    (captured : ∀ actor fiber, state actor = some fiber →
      ∀ token ∈ fiber.phase.accumulator, Effects.Respects (inverse sem token)) : Related sem state state := by
  refine ⟨(tablesSetoid sem.keyObservation _).iseqv.refl state, ?_⟩
  intro actor
  cases found : state actor with
  | none => trivial
  | some fiber =>
    exact ⟨rfl, rfl, (entries actor fiber found).respect, rfl, rfl,
      phase_self sem actor fiber.component.requires fiber.phase (current actor fiber found) (captured actor fiber found)⟩

/-- A homogeneous special case for calculus examples and structural proofs. -/
def structural [Setoid Value]
    (meaning : Name → Code → Iterator (MediatedRegistry.Gamma Name Key Value Code Error)) :
    Semantics Name Key Value Code Error :=
  ⟨MediatedRegistry.Allowed, meaning, Stages.undo, (fun token _ allowed => MediatedRegistry.inverse_allowed token allowed),
    (fun _ => rfl), (fun _ _ => rfl),
    (fun _ => inferInstance)⟩

end
end Cordis.PaperStateObservation
