import Cordis.TypedRegistrySupport
import Cordis.TypedStateObservation

/-! Lemma 75 under global provision maps, on the key-dependent registry.
The argument compares a first provision with the unit-insertion probe at its
actor. The comparison uses only the paper's table observation. -/
namespace Cordis.TypedRegistry
open PaperEffectEquations (CoeffectOperations)
open TypedStateObservation (Semantics)
universe u
variable {Name Key Code : Type u} {V : Key → Type u} {ops : CoeffectOperations V}
variable [DecidableEq Name] [DecidableEq Key]
local notation "R" => Registry Name V Code
local notation "F" => Fiber Name V Code
local notation "Program" => Code → Instruction Name ops Code
local notation "S" => Semantics Name V Code

def EmptyTables (state : R) : Prop := ∀ owner key, tableAt state owner key = none

/-- The domain consequence of closing O-Insert under the admitted terminal
unit component, from Definition 58's empty initial registry. -/
def UnitProbeClosed (sem : S) : Prop :=
  ∀ actor, ∃ code : Code,
    sem.domain (put (fun _ => none) actor (fresh ⟨fun _ => false, fun _ => false, code⟩ none))

/-- Closure under the root insertion rule supplies the probes. Its component
premise is inhabited by the terminal unit at the empty interface. -/
theorem unitProbes_of_closed_insert (sem : S) (code : Code)
    (initial : sem.domain (fun _ => none))
    (unit : ∀ actor, sem.iterator actor code = Iterators.embed Effects.identity)
    (closed : ∀ (state : R) actor component, sem.domain state →
      Insertable state actor component none →
      @Iterators.WitnessedIterator _ (TypedStateObservation.observation ops sem
        (fun k => component.requires k = true ∨ component.provides k = true))
        (sem.iterator actor component.entry) →
      sem.domain (put state actor (fresh component none))) :
    UnitProbeClosed sem := by
  intro actor
  refine ⟨code, closed (fun _ => none) actor ⟨fun _ => false, fun _ => false, code⟩
    initial (by simp [Insertable]) ?_⟩
  change @Iterators.WitnessedIterator _ (TypedStateObservation.observation ops sem _)
    (sem.iterator actor code)
  rw [unit actor]
  exact @Iterators.witnessed_embed _ (TypedStateObservation.observation ops sem _)
    Effects.identity (@Effects.witnessed_identity _ (TypedStateObservation.observation ops sem _))

/-- The writes from Definition 55 used by the unit-probe argument.
The actor must exist in the input. -/
def ProvisionFrame (sem : S) (actor : Name) (forward : sem.Gamma → sem.Gamma) : Prop :=
  ∀ input fiber, input.val actor = some fiber →
    (∀ name, input.val name = none → (forward input).val name = none) ∧
      ∀ output, (forward input).val actor = some output → output.component = fiber.component

/-- The literal global interpretation of a provision from Definitions 49,
55 and 56. Definition 49 supplies the witness of the remaining iterator
stored in the source phase. -/
structure GlobalProvisionMeaning {program : Program} {last : Nat}
    (sem : S) (trace : Trace program (fun _ => none) last) : Prop where
  states : ∀ t, t ≤ last → sem.domain (trace.state t)
  owned : ∀ (input : sem.Gamma) name fiber, input.val name = some fiber →
    ∀ key, fiber.table key ≠ none → fiber.component.provides key = true
  unitProbes : UnitProbeClosed sem
  provision : ∀ t (bounded : t < last) code key (value : V key) (fiber : F) next,
    (program code).action = .provide key value →
    trace.state t (trace.actor t) = some fiber →
    Land program (trace.actor t) code (trace.state t)
      (write (trace.state t) (trace.actor t) key (some value)) (.restrict (trace.actor t) key) next →
    let input : sem.Gamma := ⟨trace.state t, states t (Nat.le_of_lt bounded)⟩
    let head := sem.iterator (trace.actor t) code
    let forward := Tracking.forward head.effect
    (forward input).val = write (trace.state t) (trace.actor t) key (some value) ∧
      ProvisionFrame sem (trace.actor t) forward ∧
      @Iterators.WitnessedIterator _ (TypedStateObservation.observation ops sem
        (fun k => fiber.component.requires k = true ∨ fiber.component.provides k = true)) head

private theorem unit_probe_output_empty {sem : S} {actor : Name} {code : Code}
    (owned : ∀ (input : sem.Gamma) name fiber, input.val name = some fiber →
      ∀ key, fiber.table key ≠ none → fiber.component.provides key = true)
    (forward : sem.Gamma → sem.Gamma) (framed : ProvisionFrame sem actor forward)
    (legal : sem.domain (put (fun _ => none) actor (fresh ⟨fun _ => false, fun _ => false, code⟩ none))) :
    EmptyTables (forward ⟨_, legal⟩).val := by
  let entry : F := fresh ⟨fun _ => false, fun _ => false, code⟩ none
  let probe : sem.Gamma := ⟨put (fun _ => none) actor entry, legal⟩
  have atActor : probe.val actor = some entry := by simp [probe, put]
  intro name key
  change tableAt (forward probe).val name key = none
  obtain ⟨absent, preserved⟩ := framed probe entry atActor
  by_cases same : name = actor
  · subst name
    cases row : (forward probe).val actor with
    | none => simp [tableAt, row]
    | some result =>
      cases binding : result.table key with
      | none => simp [tableAt, row, binding]
      | some value =>
        have claimed := owned (forward probe) actor result row key (by rw [binding]; simp)
        rw [preserved result row] at claimed
        cases claimed
  · have missing := absent name (by simp [probe, put, same])
    simp [tableAt, missing]

private theorem no_first_binding {program : Program} {last : Nat}
    (sem : S) (trace : Trace program (fun _ => none) last)
    (meaning : GlobalProvisionMeaning sem trace) {t : Nat} (bounded : t < last)
    (empty : EmptyTables (trace.state t)) {code : Code} {key : Key} {value : V key}
    {fiber : F} {next : Option Code}
    (action : (program code).action = .provide key value)
    (found : trace.state t (trace.actor t) = some fiber)
    (declared : fiber.component.provides key = true)
    (land : Land program (trace.actor t) code (trace.state t)
      (write (trace.state t) (trace.actor t) key (some value)) (.restrict (trace.actor t) key) next) : False := by
  let actor := trace.actor t
  let actual : sem.Gamma := ⟨trace.state t, meaning.states t (Nat.le_of_lt bounded)⟩
  let scope (k : Key) := fiber.component.requires k = true ∨ fiber.component.provides k = true
  let head := sem.iterator actor code
  obtain ⟨correct, framed, witness⟩ := meaning.provision t bounded code key value fiber next action found land
  obtain ⟨unitCode, legal⟩ := meaning.unitProbes actor
  let probe : sem.Gamma :=
    ⟨put (fun _ => none) actor (fresh ⟨fun _ => false, fun _ => false, unitCode⟩ none), legal⟩
  have emptyProbe : EmptyTables probe.val := by
    intro name k
    by_cases same : name = actor <;> simp [probe, tableAt, put, fresh, same]
  letI : Setoid sem.Gamma := TypedStateObservation.observation ops sem scope
  have indistinguishable : probe ≈ actual := by
    intro k _
    constructor
    · intro name v bound
      rw [emptyProbe name k] at bound
      cases bound
    · intro name v bound
      change tableAt (trace.state t) name k = some v at bound
      rw [empty name k] at bound
      cases bound
  have outputs : TypedStateObservation.TablesRelatedAt sem.keyObservation scope
      (Tracking.forward head.effect probe).val (Tracking.forward head.effect actual).val :=
    witness.effect_witnessed.forward_respects indistinguishable
  have successful : tableAt (Tracking.forward head.effect actual).val actor key = some value := by
    change tableAt (Tracking.forward (sem.iterator (trace.actor t) code).effect actual).val
      (trace.actor t) key = some value
    rw [correct]
    simp [tableAt, write, modify, found]
  obtain ⟨other, result, binding, _⟩ := (outputs key (.inr declared)).2 actor value successful
  have emptyOutput : EmptyTables (Tracking.forward head.effect probe).val :=
    unit_probe_output_empty meaning.owned _ framed legal
  rw [emptyOutput other key] at binding
  cases binding

private theorem landing_stays_empty {program : Program} {last : Nat}
    (sem : S) (trace : Trace program (fun _ => none) last)
    (meaning : GlobalProvisionMeaning sem trace) {t : Nat} (bounded : t < last)
    (empty : EmptyTables (trace.state t)) {code : Code} {middle : R}
    {token : Inverse Name V} {next : Option Code}
    (land : Land program (trace.actor t) code (trace.state t) middle token next) :
    EmptyTables middle := by
  cases land with
  | unit => exact empty
  | provide r _ _ fiber key value action found declared previous =>
    exact False.elim (no_first_binding sem trace meaning bounded empty action found declared
      (.provide _ _ _ fiber key value action found declared previous))
  | operate r actor code key operation argument owner input output inverse result action located called =>
    have absent : location (trace.state t) (trace.actor t) key = none := by
      unfold location
      cases bindingOwner (trace.state t) (trace.actor t) key with
      | none => rfl
      | some name => simp [empty name key]
    rw [absent] at located
    cases located
  | instantiate _ actor code component child action ready =>
    intro name key
    by_cases same : name = child
    · simp [tableAt, put, fresh, same]
    · simpa [tableAt, put, same] using empty name key

/-- The literal global provision assumptions prohibit a first binding in the
typed calculus, with no restriction on the value or outcome families. -/
theorem empty_tables_of_global_provisions {program : Program} {last : Nat}
    (sem : S) (trace : Trace program (fun _ => none) last) (meaning : GlobalProvisionMeaning sem trace) :
    ∀ t, t ≤ last → EmptyTables (trace.state t) := by
  intro t bound
  induction t with
  | zero => rw [trace.start]; intro name key; rfl
  | succ t ih =>
    have empty := ih (Nat.le_of_succ_le bound)
    obtain ⟨use, middle, edit, applied, _, _, _, _, tables⟩ :=
      RuleEvaluation.step_factorization (encodeProgram program) (trace.encode.step t bound)
    have emptyEncoded : Results.EmptyTables (encodeRegistry ops (trace.state t)) := by
      intro name key
      simp [empty name key]
    have middleEmpty : Results.EmptyTables middle := by
      cases applied with
      | identity => exact emptyEncoded
      | accumulator tokens => exact Results.empty_discharge emptyEncoded tokens
      | iteration =>
        rename_i code result inverse next landed
        obtain ⟨typed, token, actual, encoded, _⟩ := land_decode ops landed
        rw [← encoded]
        have noBinding := landing_stays_empty sem trace meaning bound empty actual
        intro name key
        simp [noBinding name key]
    intro name key
    have rawEmpty := (tables name key).symm.trans (middleEmpty name key)
    change StageRecovery.tableAt (encodeRegistry ops (trace.state (t + 1))) name key = none at rawEmpty
    simpa using rawEmpty

/-- Lemma 75 on the heterogeneous registry under the literal global
interpretation. Root-only external insertion is Definition 74's premise. -/
theorem lemma75_typed_global {program : Program} {last : Nat}
    (sem : S) (trace : Trace program (fun _ => none) last) (roots : trace.RootInsertions)
    (meaning : GlobalProvisionMeaning sem trace)
    (acyclic : FiniteOrder.Acyclic (precedes (trace.state last))) :
    WellFounded (supportEdge (trace.state last)) ∧
      ∃ set, SupportSolution (trace.state last) set ∧
        ∀ other, SupportSolution (trace.state last) other → other = set :=
  lemma75_typed_of_empty_tables trace roots (empty_tables_of_global_provisions sem trace meaning) acyclic

end Cordis.TypedRegistry
