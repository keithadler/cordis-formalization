import Cordis.Repairs.ScopedNameTransport
import Cordis.Repairs.MediatedRoutes
import Cordis.Repairs.OperationExample
import Cordis.Repairs.ScopedIteratorGenerators

/-! A reachable mixed-key program: operate on a foreign dependency, create
a child, provide the actor's own key. The allocation guard is proved after the
dependency write and the provision tail accepts the allocated-child output. -/
namespace Cordis.Repairs.ScopedProgramExample
open TypedRegistry ScopedEffects ScopedProgram
open PaperEffectEquations (CoeffectOperations)
open OperationExample (increment predecessor increment_witnessed)

abbrev Values : Bool → Type := fun _ => Nat
abbrev RegistryState := Registry Nat Values Nat
abbrev Row := Fiber Nat Values Nat

def operations : CoeffectOperations Values where
  Name _ := Unit
  Argument _ _ := Unit
  Outcome _ _ := Unit
  operation _ _ _ := increment

def provider : Calculus.Component Bool Nat :=
  ⟨fun _ => false, (!·), 0⟩
def actorComponent : Calculus.Component Bool Nat :=
  ⟨(!·), id, 1⟩
def child : Calculus.Component Bool Nat :=
  ⟨fun _ => false, fun _ => false, 4⟩

def program : Nat → Instruction Nat operations Nat
  | 0 => ⟨.provide false 10, fun _ => none⟩
  | 1 => ⟨.operate false () (), fun _ => some 2⟩
  | 2 => ⟨.instantiate child, fun
    | .child 2 => some 3
    | _ => none⟩
  | 3 => ⟨.provide true 42, fun _ => none⟩
  | _ => ⟨.unit, fun _ => none⟩

def observe (_ : Bool) : Setoid Nat := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
def keys (_ : Bool) : Prop := True
def view : Calculus.View Nat Bool := fun _ => 0
def empty : RegistryState := fun _ => none
def inserted : RegistryState := put empty 0 (fresh provider none)
def begun : RegistryState := mark inserted 0 (.reloading 0 [] view)
def supplied : RegistryState := write begun 0 false (some 10)
def active : RegistryState := mark supplied 0 (.active [.restrict 0 false] view)
def joined : RegistryState := put active 1 (fresh actorComponent none)
def ready : RegistryState := mark joined 1 (.reloading 1 [] view)

theorem ready_allowed : CompatibleProvision.Allowed operations ready := by
  have insertProvider : Step program .insert 0 empty inserted :=
    .insert empty 0 provider none ⟨rfl, by simp, fun _ _ => trivial⟩
  have beginProvider : Step program .begin 0 inserted begun :=
    .begin inserted 0 (fresh provider none) view rfl rfl
      ⟨rfl, fun _ required => Bool.noConfusion required⟩
  have finishProvider : Step program .finish 0 begun active :=
    .finish begun supplied 0 { (fresh provider none : Row) with phase := .reloading 0 [] view }
      0 [] view (.restrict 0 false) rfl rfl
      ⟨rfl, fun _ required => Bool.noConfusion required⟩
      (.provide begun 0 0 { (fresh provider none : Row) with phase := .reloading 0 [] view }
        false 10 rfl rfl rfl rfl)
  have insertActor : Step program .insert 1 active joined := by
    apply Step.insert active 1 actorComponent none
    refine ⟨rfl, by simp, ?_⟩
    intro name key
    by_cases same : name = 0
    · subst name
      change actorComponent.provides key = true → ¬ provider.provides key = true
      cases key <;> decide
    · simp [active, supplied, begun, inserted, empty, mark, write, TypedRegistry.modify, put, same]
  have beginActor : Step program .begin 1 joined ready :=
    .begin joined 1 (fresh actorComponent none) view rfl rfl
      ⟨rfl, fun key required => by cases key <;> first | exact ⟨trivial, by decide⟩ | cases required⟩
  exact CompatibleProvision.step_allowed beginActor
    (CompatibleProvision.step_allowed insertActor
      (CompatibleProvision.step_allowed finishProvider
        (CompatibleProvision.step_allowed beginProvider
          (CompatibleProvision.step_allowed insertProvider CompatibleProvision.empty_allowed))))

abbrev Actor := CompatibleProvision.Compatible operations 1 actorComponent
abbrev Bound := BoundOperation.Compatible operations 1 actorComponent 0 provider false
abbrev CanBirth (state : RegistryState) := Insertable state 2 child (some 1)
abbrev Entry (state : RegistryState) := Bound state ∧ CanBirth state

theorem write_preserves_birth (state : RegistryState) (value : Option Nat)
    (enabled : CanBirth state) : CanBirth (write state 0 false value) := by
  have existsActor := enabled.2.1 1 rfl
  refine ⟨by simpa [write, TypedRegistry.modify] using enabled.1, ?_, ?_⟩
  · intro name parent
    have same : 1 = name := Option.some.inj parent
    subst name
    simpa [write, TypedRegistry.modify] using existsActor
  · intro name key
    cases found : write state 0 false value name <;> simp [child]

def input : State Entry := by
  have actorHere : Actor ready :=
    ⟨ready_allowed, ⟨{(fresh actorComponent none : Row) with phase := .reloading 1 [] view}, rfl, rfl⟩⟩
  have providerHere : CompatibleProvision.Compatible operations 0 provider ready := by
    refine ⟨ready_allowed, ?_⟩
    let row : Row := {
      (fresh provider none : Row) with
      table := fun k => if h : false = k then h ▸ (some 10 : Option (Values false)) else none
      phase := .active [.restrict 0 false] view
    }
    exact ⟨row, rfl, rfl⟩
  have enabled : CanBirth ready := by
    refine ⟨rfl, ?_, ?_⟩
    · intro name parent
      have same : 1 = name := Option.some.inj parent
      subst name
      change some _ ≠ none
      simp
    · intro name key
      cases found : ready name <;> simp [child]
  exact ⟨ready, ⟨actorHere, providerHere, rfl⟩, enabled⟩

def provisionTail : Iterator program 1 observe keys 3 Actor :=
  .stage (Head.provision true trivial rfl 42 rfl) (fun _ => Actor)
    (by intro _ _ impossible; cases impossible)
    (by intro _ _ _ _ _ _ impossible; cases impossible)

def birthTail : Iterator program 1 observe keys 2 (fun state => Actor state ∧ CanBirth state) := by
  refine .stage (Head.allocate 2 rfl) (fun _ => Actor) ?_ ?_
  · intro outcome next selected
    cases selected
    exact provisionTail
  · intro _ output _ _ _ _ _
    exact output.property.1

def operationHead : Head program 1 observe keys 1 Entry Bound Unit :=
  (Head.operate trivial rfl () () increment_witnessed rfl).narrow (fun _ h => h.1)

def plan : Iterator program 1 observe keys 1 Entry := by
  refine .stage operationHead (fun _ state => Actor state ∧ CanBirth state) ?_ ?_
  · intro outcome next selected
    cases selected
    exact birthTail
  · intro before after saved result next called selected
    -- Each successful dependency write keeps the reserved-name and provision guard.
    change (BoundOperation.liftOperation (key := false) (by rfl) increment).run
      (⟨before.val, before.property.1⟩ : State Bound) = some (after, saved, result) at called
    obtain ⟨old, changed, scalarUndo, _, _, equal, _⟩ :=
      (BoundOperation.operation_success_iff (key := false) rfl increment
        (⟨before.val, before.property.1⟩ : State Bound) after saved result).mp called
    exact ⟨after.property.1, equal ▸ write_preserves_birth before.val (some changed) before.property.2⟩

def output : RegistryState :=
  write (put (write ready 0 false (some 11)) 2 (fresh child (some 1))) 1 true (some 42)

theorem succeeds : plan.execute input = some output := rfl

theorem tables : tableAt output 0 false = some 11 ∧ tableAt output 1 true = some 42 ∧
    output 2 = some (fresh child (some 1)) := ⟨rfl, rfl, rfl⟩

theorem native_execution : ∃ tokens, Landings program 1 1 input.val output tokens :=
  plan.execute_sound input output succeeds

private def alternateDraw := FreshNameTransport.swap (2 : Nat) 3

private theorem alternateDraw_fixes_ready :
    FreshNameTransport.registry alternateDraw ready = ready := by
  have absent (name : Nat) (notProvider : name ≠ 0) (notActor : name ≠ 1) : ready name = none := by
    simp [ready, joined, active, supplied, begun, inserted, empty,
      mark, write, TypedRegistry.modify, put, notProvider, notActor]
  funext name
  obtain ⟨original, rfl⟩ := alternateDraw.surjective name
  rw [FreshNameTransport.registry_at]
  by_cases providerName : original = 0
  · subst original
    rfl
  by_cases actorName : original = 1
  · subst original
    rfl
  have movedProvider : alternateDraw.toFun original ≠ 0 :=
    fun same => providerName (alternateDraw.injective (show alternateDraw.toFun original =
      alternateDraw.toFun 0 from same))
  have movedActor : alternateDraw.toFun original ≠ 1 :=
    fun same => actorName (alternateDraw.injective (show alternateDraw.toFun original =
      alternateDraw.toFun 1 from same))
  rw [absent original providerName actorName, absent _ movedProvider movedActor]
  rfl

/-- Transport the actual mixed execution to draw 3, including the
dependent operation's saved inverse and the later provision. -/
theorem renamed_execution : ∃ tokens,
    Landings (FreshNameTransport.program alternateDraw program) 1 1
      input.val (FreshNameTransport.registry alternateDraw output) tokens ∧
    FreshNameTransport.registry alternateDraw output 3 = some (fresh child (some 1)) := by
  obtain ⟨tokens, exec⟩ := native_execution
  have moved := FreshNameTransport.landings_transport alternateDraw exec
  change Landings _ 1 1 (FreshNameTransport.registry alternateDraw ready) _ _ at moved
  rw [alternateDraw_fixes_ready] at moved
  exact ⟨_, moved, rfl⟩

/-- The entire scoped plan runs with draw 3, using the renamed input
domains. The same observation compares the two final tables. -/
theorem scoped_renamed_execution :
    let movedInput := ScopedNameTransport.moveState operations alternateDraw input
    let movedPlan := ScopedNameTransport.iterator alternateDraw plan
    movedInput.val = input.val ∧
      movedPlan.execute movedInput = some (FreshNameTransport.registry alternateDraw output) ∧
      TypedStateObservation.TablesRelatedAt observe keys output (FreshNameTransport.registry alternateDraw output) := by
  dsimp only
  refine ⟨alternateDraw_fixes_ready, ?_, FreshNameTransport.tables_related alternateDraw output observe keys⟩
  rw [ScopedNameTransport.execute_transport, succeeds]
  rfl

/-- In the original program draw 3 instead terminates at the birth.
It cannot take the provision continuation selected by draw 2. -/
theorem original_alternate_draw_stops :
    let before := FreshNameTransport.registry alternateDraw (write ready 0 false (some 11))
    let after := put before 3 (fresh child (some 1))
    Land program 1 2 before after (.retire 3) none ∧
      ¬ Land program 1 2 before after (.retire 3) (some 3) := by
  have readyBirth : CanBirth (write ready 0 false (some 11)) :=
    write_preserves_birth ready _ input.property.2
  have alternateReady := FreshNameTransport.birth_insertable alternateDraw readyBirth
  refine ⟨(FreshNameTransport.birth_landing_iff rfl alternateReady none).mpr rfl, ?_⟩
  intro same
  have chosen := FreshNameTransport.birth_selected same
  cases chosen

/-- The same calculation can be interleaved with the native control updates.
This checks applicability after each lifecycle write as well as after each
standalone effect. -/
def operated : RegistryState :=
  mark (write ready 0 false (some 11)) 1 (.reloading 2 [.operate 0 false predecessor] view)

def birthed : RegistryState :=
  mark (put operated 2 (fresh child (some 1))) 1
    (.reloading 3 [.retire 2, .operate 0 false predecessor] view)

def finished : RegistryState :=
  mark (write birthed 1 true (some 42)) 1
    (.active [.restrict 1 true, .retire 2, .operate 0 false predecessor] view)

theorem iter_operation : Step program .iter 1 ready operated := by
  let row : Row := {(fresh actorComponent none : Row) with phase := .reloading 1 [] view}
  apply Step.iter ready (write ready 0 false (some 11)) 1 row 1 [] view
    (.operate 0 false predecessor) 2 rfl rfl
  · exact ⟨rfl, fun key hk => by cases key <;> first | exact ⟨trivial, by decide⟩ | cases hk⟩
  · exact .operate ready 1 1 false () () 0 10 11 predecessor () rfl rfl rfl

theorem iter_birth : Step program .iter 1 operated birthed := by
  let row : Row := {
    (fresh actorComponent none : Row) with phase := .reloading 2 [.operate 0 false predecessor] view
  }
  apply Step.iter operated (put operated 2 (fresh child (some 1))) 1 row 2
    [.operate 0 false predecessor] view (.retire 2) 3 rfl rfl
  · exact ⟨rfl, fun key hk => by cases key <;> first | exact ⟨trivial, by decide⟩ | cases hk⟩
  · apply Land.instantiate operated 1 2 child 2 rfl
    refine ⟨rfl, ?_, ?_⟩
    · intro name parent
      have same : 1 = name := Option.some.inj parent
      subst name
      change some _ ≠ none
      simp
    · intro name key
      cases found : operated name <;> simp [child]

theorem finish_provision : Step program .finish 1 birthed finished := by
  let row : Row := {
    (fresh actorComponent none : Row) with
    phase := .reloading 3 [.retire 2, .operate 0 false predecessor] view
  }
  apply Step.finish birthed (write birthed 1 true (some 42)) 1 row 3
    [.retire 2, .operate 0 false predecessor] view (.restrict 1 true) rfl rfl
  · exact ⟨rfl, fun key hk => by cases key <;> first | exact ⟨trivial, by decide⟩ | cases hk⟩
  · exact .provide birthed 1 3 row true 42 rfl rfl rfl rfl

theorem actual_bindings : tableAt finished 0 false = some 11 ∧ tableAt finished 1 true = some 42 :=
  ⟨rfl, rfl⟩

/-- Discharge the actual saved stack in LIFO order. The dependency and
provision are restored, and retirement keeps the child as an empty vestige. -/
theorem stack_recovery :
    let restored := discharge [.restrict 1 true, .retire 2, .operate 0 false predecessor] finished
    (∀ name key, tableAt restored name key = tableAt ready name key) ∧
      restored 2 = some { (fresh child (some 1) : Row) with retired := true } := by
  constructor
  · intro name key
    by_cases providerName : name = 0
    · subst name; cases key <;> rfl
    by_cases actorName : name = 1
    · subst name; cases key <;> rfl
    by_cases childName : name = 2
    · subst name; rfl
    simp [discharge, undo, finished, birthed, operated, ready, joined, active, supplied,
      begun, inserted, empty, tableAt, retire, mark, TypedRegistry.modify, write, put,
      providerName, actorName, childName]
  · rfl

private def evaluated := ScopedRollback.evaluate plan (ScopedRollback.Stable.true operations) input trivial

def reversibleResult : ScopedRollback.Result (fun _ : RegistryState => True) :=
  evaluated.get (by decide)

theorem reversible_execution :
    evaluated = some reversibleResult ∧ reversibleResult.output.val = output :=
  ⟨rfl, rfl⟩

/-- Compose the actual provision restriction, child retirement, and operation
inverse. The calculation restores every original table and leaves the child
as the empty retired row returned by native rollback. -/
theorem composed_rollback :
    let restored := discharge [.restrict 1 true, .retire 2, .operate 0 false predecessor] output
    (reversibleResult.restore reversibleResult.output).map Subtype.val = some restored ∧
      (∀ name key, tableAt restored name key = tableAt input.val name key) ∧
      restored 2 = some { (fresh child (some 1) : Row) with retired := true } := by
  dsimp only
  refine ⟨?_, ?_, rfl⟩
  · apply congrArg some
    funext name
    by_cases providerName : name = 0
    · subst name
      rfl
    by_cases actorName : name = 1
    · subst name
      rfl
    by_cases childName : name = 2
    · subst name
      rfl
    change write (retire (write output 1 true none) 2) 0 false (some 10) name = _
    simp [discharge, undo, write, retire, TypedRegistry.modify, providerName, actorName, childName]
  · intro name key
    by_cases providerName : name = 0
    · subst name
      cases key <;> rfl
    by_cases actorName : name = 1
    · subst name
      cases key <;> rfl
    by_cases childName : name = 2
    · subst name
      rfl
    change tableAt (discharge [.restrict 1 true, .retire 2, .operate 0 false predecessor] output) name key =
      tableAt ready name key
    simp [discharge, undo, output, tableAt, write, retire, TypedRegistry.modify, put,
      providerName, actorName, childName]

private def zeroBinding : Inverse Nat Values := .operate 0 false (fun _ => some 0)

private def zeroProbe : State reversibleResult.domain := by
  refine ⟨undo zeroBinding reversibleResult.output.val, ?_⟩
  have bound := ScopedRollback.Stable.operate operations 1 0 actorComponent provider false
  have allocated := ScopedRollback.Stable.allocate operations 1 2 actorComponent child
  have acting := ScopedRollback.Stable.provision operations 1 actorComponent
  have stable : ScopedRollback.Stable operations reversibleResult.domain :=
    ScopedRollback.Stable.and (ScopedRollback.Stable.and
      (ScopedRollback.Stable.and (ScopedRollback.Stable.true operations) bound) allocated) acting
  exact stable.undo zeroBinding reversibleResult.output.val reversibleResult.output.property

/-- The zero binding is admitted to the same structural probe domain.
The composed inverse returns the native dependency inverse's failure. -/
theorem composed_rollback_fails_at_zero :
    tableAt zeroProbe.val 0 false = some 0 ∧ reversibleResult.restore zeroProbe = none :=
  ⟨rfl, rfl⟩

/-- The same dependency capture succeeds on its own output and fails on
an admitted probe with value zero. Its recorded generator has both behaviors. -/
theorem recorded_generator_keeps_partial_domain :
    let root : ScopedIteratorObservation.Node program 1 observe keys := ⟨1, Entry, plan⟩
    let live := fun _ : Nat => (none : Option Nat)
    ∃ saved : PairwiseNativeWords.Saved program 1,
      Nonempty (ScopedIteratorGenerators.Generator root (.replay saved)) ∧
      PairwiseMixed.runMixed saved.word (undo zeroBinding input.val, live) = none ∧
      (PairwiseMixed.runMixed saved.word (saved.output, live)).map (fun state => tableAt state.1 0 false) =
        some (some 10) := by
  dsimp only
  let root : ScopedIteratorObservation.Node program 1 observe keys := ⟨1, Entry, plan⟩
  let result := (root.evaluate input).get (by decide)
  have called : root.evaluate input = some result := rfl
  let live := fun _ : Nat => (none : Option Nat)
  obtain ⟨head, saved, origin, output, code, next, _, actual, agrees, drawn⟩ :=
    ScopedIteratorGenerators.record_head root input result called live 1
  let probe : State result.domain := ⟨undo zeroBinding input.val,
    (ScopedRollback.Stable.operate operations 1 0 actorComponent provider false).undo
      zeroBinding input.val input.property.1⟩
  refine ⟨saved, ⟨.replay root .root input result called saved origin output code next agrees
    (actual.2.1.trans drawn)⟩, ?_, ?_⟩
  · have same := ScopedIteratorGenerators.saved_application saved result agrees probe live
    change (PairwiseMixed.runMixed saved.word (undo zeroBinding input.val, live)).map _ = none at same
    exact Option.map_eq_none_iff.mp same
  · rw [output]
    have same := ScopedIteratorGenerators.saved_application saved result agrees result.output live
    have projected := congrArg (Option.map fun tables : PairwiseSlots.Tables Nat Values => tables (0, false)) same
    simpa only [Option.map_map, PairwiseSlots.tablesOf, Function.comp_def] using projected

/-- Transport the mixed calculation and its entire saved inverse to the
other name draw. Even the failed probe moves with the corresponding domain. -/
theorem renamed_rollback :
    let moved := reversibleResult.rename operations alternateDraw
    ScopedRollback.evaluate (ScopedNameTransport.iterator alternateDraw plan)
      (ScopedNameTransport.stable_domain alternateDraw (ScopedRollback.Stable.true operations))
      (ScopedNameTransport.moveState operations alternateDraw input) trivial = some moved ∧
    moved.restore (ScopedNameTransport.moveState operations alternateDraw zeroProbe) = none := by
  dsimp only
  constructor
  · exact (ScopedRollback.evaluate_rename alternateDraw plan (ScopedRollback.Stable.true operations) input trivial).trans
      (congrArg (Option.map (ScopedRollback.Result.rename operations alternateDraw)) reversible_execution.1)
  · simp [ScopedRollback.Result.rename, composed_rollback_fails_at_zero.2]

private theorem mediated_program : MediatedAdmission.Mediated program actorComponent 1 := by
  have provision : MediatedAdmission.Mediated program actorComponent 3 := by
    refine MediatedRegistry.Mediated.provision (program := encodeProgram program)
      3 true (TypedCoeffectReplay.pack true 42) rfl ?_ ?_
    · rfl
    · intro outcome next selected
      cases decoded : decodeOutcome operations outcome <;>
        simp [encodeProgram, encodeInstruction, program] at selected
  have allocation : MediatedAdmission.Mediated program actorComponent 2 := by
    apply MediatedRegistry.Mediated.birth 2 child rfl
    intro outcome next selected
    cases decoded : decodeOutcome operations outcome with
    | none => simp [encodeProgram, encodeInstruction, program, decoded] at selected
    | some reply =>
      cases reply <;> simp [encodeProgram, encodeInstruction, program, decoded] at selected
      rename_i name
      by_cases expected : name = 2
      · subst name
        cases selected
        exact provision
      · simp [expected] at selected
  refine MediatedRegistry.Mediated.operation (program := encodeProgram program)
    1 false (TypedRegistry.encodeOperation operations false () ()) rfl ?_ ?_
  · exact Or.inl rfl
  · intro outcome next selected
    cases decoded : decodeOutcome operations outcome <;>
      simp [encodeProgram, encodeInstruction, program, decoded] at selected
    cases selected
    exact allocation

private theorem scalar_laws : MediatedAdmission.OperationsLawful operations observe :=
  fun _ _ _ => increment_witnessed

private def afterOtherDraw : RegistryState := put (write ready 0 false (some 11)) 3 (fresh child (some 1))

private theorem native_other_draw :
    Landings program 1 1 ready afterOtherDraw [.operate 0 false predecessor, .retire 3] := by
  refine .next (.operate ready 1 1 false () () 0 10 11 predecessor () rfl rfl rfl) (.last ?_)
  apply Land.instantiate _ _ _ _ _ rfl
  refine ⟨rfl, ?_, ?_⟩
  · intro parent equal
    cases equal
    exact Option.noConfusion
  · intro name key
    cases (write ready 0 false (some 11)) name <;> simp [child]

private noncomputable def synthesizedPlan (tokens : List (Inverse Nat Values)) :=
  MediatedAdmission.admit (actor := 1)
    (MediatedAdmission.choicesOf operations ready 1 tokens) scalar_laws mediated_program

/-- Admission is synthesized from the same program and two native paths.
Draw 2 takes the provision tail. Draw 3 selects the native terminal branch. -/
theorem synthesized_branches :
    (∃ tokens, ∃ valid : (synthesizedPlan tokens).domain ready,
      (synthesizedPlan tokens).iterator.execute ⟨ready, valid⟩ = some output) ∧
    (let admitted := synthesizedPlan [.operate 0 false predecessor, .retire 3]
     ∃ valid : admitted.domain ready, admitted.iterator.execute ⟨ready, valid⟩ = some afterOtherDraw) ∧
    tableAt output 1 true = some 42 ∧ tableAt afterOtherDraw 1 true = none := by
  obtain ⟨tokens, landed⟩ := native_execution
  exact ⟨⟨tokens, MediatedAdmission.admits_actual_run landed mediated_program scalar_laws input.property.1.1⟩,
    MediatedAdmission.admits_actual_run native_other_draw mediated_program scalar_laws input.property.1.1, rfl, rfl⟩

private def competingActor : Calculus.Component Bool Nat :=
  ⟨fun _ => false, fun _ => false, 2⟩

private def withCompetitor : RegistryState := put ready 5 (fresh competingActor none)
private def competingReady : RegistryState := mark withCompetitor 5 (.reloading 2 [] view)
private def competingBirth : RegistryState := put competingReady 2 (fresh child (some 5))

private theorem competing_ready_allowed : CompatibleProvision.Allowed operations competingReady := by
  have inserted : Step program .insert 5 ready withCompetitor := by
    apply Step.insert
    refine ⟨rfl, by simp, ?_⟩
    intro name key
    cases ready name <;> simp [competingActor]
  have begun : Step program .begin 5 withCompetitor competingReady :=
    .begin withCompetitor 5 (fresh competingActor none) view rfl rfl
      ⟨rfl, fun _ required => Bool.noConfusion required⟩
  exact CompatibleProvision.step_allowed begun (CompatibleProvision.step_allowed inserted ready_allowed)

private theorem competitor_birth :
    Land program 5 2 competingReady competingBirth (.retire 2) (some 3) := by
  apply Land.instantiate _ _ _ _ _ rfl
  refine ⟨rfl, ?_, ?_⟩
  · intro name isActor
    cases isActor
    exact Option.noConfusion
  · intro name key
    cases competingReady name <;> simp [child]

private theorem competitor_birth_after_operation :
    Land program 5 2 (write competingReady 0 false (some 11))
      (write competingBirth 0 false (some 11)) (.retire 2) (some 3) := by
  have same : write competingBirth 0 false (some 11) =
      put (write competingReady 0 false (some 11)) 2 (fresh child (some 5)) := by
    funext name
    by_cases atChild : name = 2
    · subst name
      rfl
    · by_cases atProvider : name = 0
      · subst name
        rfl
      · simp [competingBirth, write, TypedRegistry.modify, put, atChild, atProvider]
  rw [same]
  apply Land.instantiate _ _ _ _ _ rfl
  refine ⟨rfl, ?_, ?_⟩
  · intro name isActor
    cases isActor
    exact Option.noConfusion
  · intro name key
    cases (write competingReady 0 false (some 11)) name <;> simp [child]

private def competingInput : State Bound := by
  refine ⟨competingReady, ?_⟩
  obtain ⟨actor, actorHere, actorPayload⟩ := input.property.1.1.2
  obtain ⟨owner, ownerHere, ownerPayload⟩ := input.property.1.2.1.2
  exact ⟨⟨competing_ready_allowed, actor, by simpa [competingReady, withCompetitor, mark, TypedRegistry.modify, put] using actorHere,
      actorPayload⟩,
    ⟨competing_ready_allowed, owner, by simpa [competingReady, withCompetitor, mark, TypedRegistry.modify, put] using ownerHere,
      ownerPayload⟩, rfl⟩

private def inputAfterCompetition : State Bound :=
  ⟨competingBirth, (ScopedRollback.Stable.operate operations 1 0 actorComponent provider false).land
    competitor_birth competingInput.property⟩

private abbrev Recipe := ScopedAdmission.Unlinked program 1 observe keys

private def provisionRecipe : Recipe 3 :=
  .stage (Head.provision (acting := actorComponent) true trivial rfl 42 rfl)
    (by intro _ _ impossible; cases impossible)

private def birthRecipe : Recipe 2 :=
  .stage (Head.allocate (acting := actorComponent) 2 rfl) (by
    intro _ following selected
    cases selected
    exact provisionRecipe)

private def firstHead : Head program 1 observe keys 1 Bound Bound Unit :=
  Head.operate trivial rfl () () increment_witnessed rfl

private def competingRecipe : Recipe 1 :=
  .stage firstHead (by
    intro _ following selected
    cases selected
    exact birthRecipe)

private theorem competing_recipe_stage (input : State Bound)
    (binding : tableAt input.val 0 false = some 10) :
    (ScopedAdmission.compile competingRecipe).domain input.val ↔
      (ScopedAdmission.compile birthRecipe).domain (write input.val 0 false (some 11)) := by
  let output := BoundOperation.setSlot (key := false) rfl (some 11) input
  have called : firstHead.effect.run input = some
      (output, BoundOperation.liftMap rfl predecessor, ()) := by
    exact (BoundOperation.operation_success_iff (key := false) rfl increment input output _ ()).mpr
      ⟨10, 11, predecessor, binding, rfl, rfl, rfl⟩
  exact ScopedAdmission.compile_stage_domain_of_call (tail := fun _ _ selected => by
    cases selected
    exact birthRecipe) input called rfl

/-- A legal foreign birth can change the compiled scope of an ordinary
head while the native head itself keeps its route, inverse and next code.
The lost guard belongs to the selected tail's fixed draw. -/
theorem foreign_birth_blocks_selected_scope :
    Transposition.Separated actorComponent competingActor ∧
    Land program 5 2 competingReady competingBirth (.retire 2) (some 3) ∧
    Land program 1 1 competingReady (write competingReady 0 false (some 11))
      (.operate 0 false predecessor) (some 2) ∧
    Land program 1 1 competingBirth (write competingBirth 0 false (some 11))
      (.operate 0 false predecessor) (some 2) ∧
    Land program 5 2 (write competingReady 0 false (some 11))
      (write competingBirth 0 false (some 11)) (.retire 2) (some 3) ∧
    (ScopedAdmission.compile competingRecipe).domain competingReady ∧
    ¬ (ScopedAdmission.compile competingRecipe).domain competingBirth := by
  refine ⟨⟨?_, ?_, ?_⟩, competitor_birth,
    .operate competingReady 1 1 false () () 0 10 11 predecessor () rfl rfl rfl,
    .operate competingBirth 1 1 false () () 0 10 11 predecessor () rfl rfl rfl,
    competitor_birth_after_operation, ?_, ?_⟩
  · intro _ _
    rfl
  · intro _ _
    rfl
  · intro _ provided
    cases provided
  · apply (competing_recipe_stage competingInput rfl).mpr
    let operated := BoundOperation.setSlot (key := false) rfl (some 11) competingInput
    have ready : Actor operated.val ∧ CanBirth operated.val := by
      refine ⟨operated.property.1, rfl, ?_, ?_⟩
      · intro name same
        cases same
        exact Option.noConfusion
      · intro name key
        cases operated.val name <;> simp [child]
    refine ⟨ready, ?_⟩
    intro _ output saved reply following selected called
    cases Option.some.inj called
    cases selected
    refine ⟨(AllocationDomains.allocate ⟨operated.val, ready⟩).property.1, ?_⟩
    intro _ _ _ reply next impossible
    cases impossible
  · intro admitted
    have tail := (competing_recipe_stage inputAfterCompetition rfl).mp admitted
    exact Option.noConfusion (tail.1.2.1 : write competingBirth 0 false (some 11) 2 = none)

/-- The saved operation compares two admitted probes with the same
tables even though only one contains the unrelated actor at name 5. -/
theorem saved_inverse_compares_table_only_probes :
    let root : ScopedIteratorObservation.Node program 1 observe keys := ⟨1, Entry, plan⟩
    let result := (root.evaluate input).get (by decide)
    let first : State result.domain := ⟨ready, input.property.1⟩
    let second : State result.domain := competingInput
    first.val 5 = none ∧ second.val 5 ≠ none ∧
      Iterators.OptionRel (Observed observe keys) (result.inverse first) (result.inverse second) ∧
      (result.inverse second).map (fun restored => tableAt restored.val 0 false) = some (some 9) := by
  dsimp only
  let root : ScopedIteratorObservation.Node program 1 observe keys := ⟨1, Entry, plan⟩
  let result := (root.evaluate input).get (by decide)
  have called : root.evaluate input = some result := rfl
  obtain ⟨token, actual, agrees, drawn, _⟩ := root.evaluate_native input result called
  have native : Land program 1 1 ready (write ready 0 false (some 11)) (.operate 0 false predecessor) (some 2) :=
    .operate ready 1 1 false () () 0 10 11 predecessor () rfl rfl rfl
  obtain ⟨_, same, _⟩ := PairwiseNativeWords.typed_landing_deterministic actual native drawn
  subst token
  let first : State result.domain := ⟨ready, input.property.1⟩
  let second : State result.domain := competingInput
  have sameTable (owner : Nat) (key : Bool) : tableAt second.val owner key = tableAt first.val owner key := by
    by_cases separate : owner = 5
    · subst owner
      rfl
    · simp [first, second, competingInput, competingReady, withCompetitor, tableAt, mark, TypedRegistry.modify, put,
        separate]
  have observed : Observed observe keys first second := by
    intro key _
    exact ⟨fun owner value bound => ⟨owner, value, (sameTable owner key).trans bound, rfl⟩,
      fun owner value bound => ⟨owner, value, (sameTable owner key).symm.trans bound, rfl⟩⟩
  have scope : InverseScope operations keys (.operate 0 false predecessor) result.domain :=
    ⟨trivial, provider, rfl, fun _ probe => probe.2.1⟩
  have capture : PairwiseForward.CaptureRelated observe (.operate 0 false predecessor) (.operate 0 false predecessor) :=
    .operate 0 false (by
      intro left right same
      cases same
      cases predecessor left <;> first | exact True.intro | rfl)
  have otherPresent : second.val 5 ≠ none := by
    intro absent
    change some _ = none at absent
    exact Option.noConfusion absent
  exact ⟨rfl, otherPresent, ScopedIteratorGenerators.inverse_observation_on_tables agrees agrees capture rfl
    scope first second observed, rfl⟩

end Cordis.Repairs.ScopedProgramExample
