import Cordis.Repairs.EpisodeRollback
import Cordis.TypedCallbackExchange
import Cordis.TypedReplayContracts
import Cordis.TypedRegistry

/-! Retained operations and provisions on the rollback probes of Lemma 79.
Definition 44 preserves the operation outcome and relates the renewed capture.
Reachable slot history justifies both orders at an occupied slot and shows
that an empty provision slot carries no pending operation inverses. -/
namespace Cordis.Repairs.EpisodeOperationReplay
open Calculus Stages Indexed Incarnation IncarnationReplay
open EpisodeDependencies EpisodeBoundary EpisodeReplayGuards EpisodeRollback
open PartialReplayRegistry (saved)
open PartialReplayHistory (run)
open PartialReplaySlots (captures project)
open PaperEffectEquations (CoeffectOperations ValueOperationWitness)
open PartialCoeffectIndependenceContracts (tableSetoid)
open PartialInverseObservation (MapRelated)
open Iterators (OptionRel)
open TypedRegistry (encodeProgram Scalar RawRegistry RawFiber)
open StageRecovery (tableAt)
universe u
variable {Name Key Code : Type u} {V : Key → Type u} {ops : CoeffectOperations V}
variable [DecidableEq Name] [DecidableEq Key]
local notation "R" => RawRegistry Name ops Code
local notation "A" => Scalar ops
variable {program : Code → TypedRegistry.Instruction Name ops Code} {last : Nat}
local notation "History" => Trace (encodeProgram program) (fun _ => none : RawRegistry Name ops Code) last

/-- A retained operation uses the actual partial history of the addressed
slot to compare its forward application with the selected rollback word. -/
theorem operate_on_saved_word
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops
      (tableSetoid observe (fun _ => True)) key)
    (before : R) (closing : Name) (live : Name → Option Nat) (word : List (Capture Name Key A))
    (tokens : word.map Capture.token = saved before closing)
    (scopes : TableFrame.ScopedAccumulators before)
    (history : ∀ owner key, PartialReplayRegistry.SlotHistory
      (TypedReplayContracts.coeffects ops observe program recovery commutative) before owner key)
    {actor owner : Name} {entry : RawFiber Name ops Code}
    (different : actor ≠ closing) (kept : ¬ word.any (Capture.retires live actor) = true)
    (present : before actor = some entry)
    (supported : Ordering.Supported before) (noDemand : ∀ key, ¬ Ordering.Demand before actor closing key)
    (projected : EpisodeReplayGuards.Projection closing (fun name => word.any (Capture.retires live name) = true) before
      (fun name => if word.any (Capture.retires live name) then none else mark (replay live word before) closing .inactive name))
    {code : Code} {key : Key} {call : A → Except PUnit.{u + 1} (A × (A → A) × A)}
    (action : (encodeProgram program code).action = .operate key call)
    {input output outcome : A} {inverse : A → A}
    (located : location before actor key = some (owner, input))
    (performed : call input = .ok (output, inverse, outcome)) :
    let probe : R := fun name => if word.any (Capture.retires live name) then none
      else mark (replay live word before) closing .inactive name
    ∃ adjusted after actualInverse reverted,
      location probe actor key = some (owner, adjusted) ∧
      call adjusted = .ok (after, actualInverse, outcome) ∧
      Land (encodeProgram program) actor code probe
        (write probe owner key (some after))
        (.operate owner key actualInverse) ((encodeProgram program code).next (.value outcome)) ∧
      MapRelated (TypedCoeffectReplay.setoid (Yield := TypedRegistry.Yield ops) observe).r
        (TypedCoeffectReplay.decodeInverse key actualInverse)
        (TypedCoeffectReplay.decodeInverse key inverse) ∧
      @Effects.Related A (TypedCoeffectReplay.setoid observe) actualInverse inverse ∧
      tableAt (replay live word
        (write before owner key (some output))) owner key = some reverted ∧
      (TypedCoeffectReplay.setoid (Yield := TypedRegistry.Yield ops) observe).r after reverted := by
  dsimp only
  let probe : R := fun name => if word.any (Capture.retires live name) then none
    else mark (replay live word before) closing .inactive name
  let meaning := TypedReplayContracts.coeffects ops observe program recovery commutative
  let raw := saved before closing
  let allMaps := captures meaning.denote owner key raw
  have ⟨ownerKept, ownerDifferent⟩ :=
    projected.location_owner_retained kept different supported noDemand present located
  obtain ⟨provider, providerAt, held⟩ := Safety.location_binding before actor owner key input located
  have occupied : tableAt before owner key = some input := by simp [tableAt, providerAt, held]
  have noRestriction : Inverse.restrict owner key ∉ raw := by
    cases parentAt : before closing with
    | none => simp [raw, saved, parentAt]
    | some parent =>
      intro member
      exact ownerDifferent (scopes closing parent parentAt (.restrict owner key)
        (by simpa [raw, saved, parentAt] using member))
  have form : PartialReplaySlots.slotWord meaning.denote owner key raw = (allMaps, false) :=
    PartialReplaySlots.slotWord_unrestricted _ _ _ _ noRestriction
  have twoOrders := PartialReplayRegistry.operation_through_captures_of_history meaning closing owner key
    (history owner key) action occupied performed
  change ∃ adjusted reverted result, (∀ map ∈ allMaps, meaning.admitted key map) ∧
    run allMaps input = some adjusted ∧ run allMaps output = some reverted ∧
    (call adjusted).toOption.map Prod.fst = some result ∧ (meaning.observe key).r reverted result at twoOrders
  obtain ⟨adjusted, reverted, result, allowed, rolledInput, rolledOutput, resultOnly, observed⟩ := twoOrders
  have decoded : ∀ map ∈ allMaps, TypedCoeffectReplay.Lifted (TypedReplayContracts.Generator ops) key map := allowed
  obtain ⟨after, actualInverse, succeeds, inverseRelated, total⟩ :=
    TypedReplayContracts.encoded_call_after_word ops observe program (commutative key)
      action decoded rolledInput performed
  have exactResult : after = result := by simpa [succeeds, Except.toOption] using resultOnly
  subst result
  have replay_slot (state : R) (value target : A) (slot : tableAt state owner key = some value)
      (evaluated : run allMaps value = some target) : tableAt (replay live word state) owner key = some target := by
    apply replay_partial_slot meaning.denote meaning.agrees
    rw [tokens, PartialReplaySlots.slotWord_exact, form, slot]
    simp [PartialReplaySlots.interpret, PartialReplayHistory.keepMissing, evaluated]
  have atInput := replay_slot before input adjusted occupied rolledInput
  have retainedSlot : tableAt probe owner key = some adjusted := by
    have row : probe owner = mark (replay live word before) closing .inactive owner :=
      if_neg ownerKept
    unfold tableAt
    rw [row]
    change tableAt (mark (replay live word before) closing .inactive) owner key = some adjusted
    rw [StageRecovery.tableAt_mark]
    exact atInput
  obtain ⟨supplied, stillLocated⟩ :=
    projected.location_forward kept different supported noDemand present located
  have actualSlot : tableAt probe owner key = some supplied := by
    obtain ⟨row, found, value⟩ := Safety.location_binding _ actor owner key supplied stillLocated
    change probe owner = some row at found
    simp [tableAt, found, value]
  have adjust : supplied = adjusted := Option.some.inj (actualSlot.symm.trans retainedSlot)
  subst supplied
  have occupiedAfter : tableAt (write before owner key (some output)) owner key = some output := by
    rw [PartialReplayRegistry.tableAt_write _ _ _ _ _ _ (by simp [providerAt]), if_pos ⟨rfl, rfl⟩]
  exact ⟨adjusted, after, actualInverse, reverted, stillLocated, succeeds,
    .operate _ _ _ _ _ _ _ _ _ _ action stillLocated succeeds, inverseRelated, total,
    replay_slot _ _ _ occupiedAfter rolledOutput, (meaning.observe key).symm observed⟩

/-- The retained call succeeds at the canonical rollback probe, follows
the original outcome-selected continuation, and captures a related
inverse. Evaluating the retained call then gives a value related to
rolling back the original operation's actual output. -/
theorem operate_on_rollback (trace : History) (episode : ClosedEpisode trace)
    (maximal : ∀ later : ClosedEpisode trace, ¬ EpisodeEdge episode later)
    (quiet : Progress.Quiet (trace.state last))
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops
      (tableSetoid observe (fun _ => True)) key)
    {time : Nat} (lower : episode.opened ≤ time) (upper : time ≤ episode.closed)
    {actor owner : Name} {entry : RawFiber Name ops Code}
    (different : actor ≠ episode.name) (kept : ¬ withdraws trace episode time actor = true)
    (present : trace.state time actor = some entry)
    {code : Code} {key : Key} {call : A → Except PUnit.{u + 1} (A × (A → A) × A)}
    (action : (encodeProgram program code).action = .operate key call)
    {input output outcome : A} {inverse : A → A}
    (located : location (trace.state time) actor key = some (owner, input))
    (performed : call input = .ok (output, inverse, outcome)) :
    ∃ adjusted after actualInverse reverted,
      location (probeAt trace episode time) actor key = some (owner, adjusted) ∧
      call adjusted = .ok (after, actualInverse, outcome) ∧
      Land (encodeProgram program) actor code (probeAt trace episode time)
        (write (probeAt trace episode time) owner key (some after))
        (.operate owner key actualInverse) ((encodeProgram program code).next (.value outcome)) ∧
      MapRelated (TypedCoeffectReplay.setoid (Yield := TypedRegistry.Yield ops) observe).r
        (TypedCoeffectReplay.decodeInverse key actualInverse)
        (TypedCoeffectReplay.decodeInverse key inverse) ∧
      @Effects.Related A (TypedCoeffectReplay.setoid observe) actualInverse inverse ∧
      tableAt (replay (fun name => birthAt trace.state name time) (track trace.state trace.actor time episode.name)
        (write (trace.state time) owner key (some output))) owner key = some reverted ∧
      (TypedCoeffectReplay.setoid (Yield := TypedRegistry.Yield ops) observe).r after reverted := by
  have bounded : time ≤ last := by have := episode.interval.bounded; omega
  let meaning := TypedReplayContracts.coeffects ops observe program recovery commutative
  have reached := trace.prefixRun time bounded
  exact operate_on_saved_word observe recovery commutative (trace.state time) episode.name
    (fun name => birthAt trace.state name time) (track trace.state trace.actor time episode.name)
    ((tracked_stack trace time bounded).projects episode.name) (TableFrame.reachable_scoped _ reached)
    (PartialReplayRegistry.reachable_slot_history meaning reached) different kept present
    (supported_at trace time bounded) (fun _ => no_demand_on_closing trace episode maximal lower upper)
    (probe_projects trace episode maximal quiet lower upper) action located performed

omit [DecidableEq Name] [DecidableEq Key] in
theorem located_owner_present {state : R} {actor owner : Name} {key : Key} {value : A}
    (located : location state actor key = some (owner, value)) : state owner ≠ none := by
  obtain ⟨row, present, _⟩ := Safety.location_binding state actor owner key value located
  simp [present]

/-- Compare one retained write with the selected actor's rollback of the
same source write. The other slots are unchanged by the retained write. -/
theorem compare_rollback_write
    (observe : ∀ key, Setoid (V key)) (before : R) (closing : Name)
    (live : Name → Option Nat) (word : List (Capture Name Key A)) {owner : Name} {key : Key}
    {output after reverted : A}
    (sourceSelf : @StageSimulation.Related Name Key A Code PUnit.{u + 1}
      (TypedCoeffectReplay.setoid observe) Eq before before)
    (liveInSource : before owner ≠ none)
    (liveInProbe : rollback closing live word before owner ≠ none)
    (rolled : tableAt (replay live word (write before owner key (some output))) owner key = some reverted)
    (related : (TypedCoeffectReplay.setoid (Yield := TypedRegistry.Yield ops) observe).r after reverted) :
    @StageSimulation.Related Name Key A Code PUnit.{u + 1} (TypedCoeffectReplay.setoid observe) Eq
      (write (rollback closing live word before) owner key (some after))
      (rollback closing live word (write before owner key (some output))) := by
  let probe := rollback closing live word before
  let mask := fun name => word.any (Capture.retires live name)
  let middle := write before owner key (some output)
  let moved := write probe owner key (some after)
  let projected := rollback closing live word middle
  letI observed : Setoid A := TypedCoeffectReplay.setoid observe
  have ownerKept : ¬ mask owner = true := fun omitted =>
    liveInProbe (if_pos omitted)
  have tables : StageRecovery.TablesRelated moved projected := by
    intro name query
    change OptionRel observed.r (tableAt (write probe owner key (some after)) name query)
      (tableAt (rollback closing live word middle) name query)
    rw [PartialReplayRegistry.tableAt_write _ _ _ _ _ _ liveInProbe,
      rollback_tableAt closing live word middle name query]
    by_cases selected : name = owner ∧ query = key
    · obtain ⟨rfl, rfl⟩ := selected
      rw [if_pos ⟨rfl, rfl⟩, if_neg ownerKept]
      change tableAt (replay live word middle) name query = some reverted at rolled
      rw [rolled]
      exact related
    · rw [if_neg selected, rollback_tableAt]
      change OptionRel observed.r
        (if mask name then none else tableAt (replay live word before) name query)
        (if mask name then none else tableAt (replay live word middle) name query)
      have same : tableAt before name query = tableAt middle name query := by
        unfold middle
        rw [PartialReplayRegistry.tableAt_write _ _ _ _ _ _ liveInSource, if_neg selected]
      rw [replay_slot_congr live word name query same]
      exact PartialObservedMapClosure.option_refl observed _
  have controls : Transposition.SameControls moved projected :=
    Transposition.controls_trans (Transposition.controls_symm (Transposition.write_controls probe owner key (some after)))
      (rollback_controls closing live word (Transposition.write_controls before owner key (some output)))
  have middleSelf : StageSimulation.Related Eq middle middle :=
    StageSimulation.write_related sourceSelf owner key (Setoid.refl output)
  exact Transposition.related_of_controls_tables controls tables (rollback_self closing live word middleSelf)
private theorem state_after_write (trace : History) (episode : ClosedEpisode trace)
    (observe : ∀ key, Setoid (V key)) {time : Nat} {owner : Name} {key : Key}
    {output after reverted : A}
    {originalPhase replayPhase : Phase Name Key Code (Inverse Name Key A)}
    (different : trace.actor time ≠ episode.name)
    (kept : ¬ withdraws trace episode time (trace.actor time) = true)
    (sourceSelf : @StageSimulation.Related Name Key A Code PUnit.{u + 1}
      (TypedCoeffectReplay.setoid observe) Eq (trace.state time) (trace.state time))
    (phases : @StageSimulation.PhaseRelated Name Key A Code
      (TypedCoeffectReplay.setoid observe) Eq replayPhase originalPhase)
    (liveInSource : trace.state time owner ≠ none)
    (liveInProbe : probeAt trace episode time owner ≠ none)
    (ended : trace.state (time + 1) =
      mark (write (trace.state time) owner key (some output)) (trace.actor time) originalPhase)
    (rolled : tableAt (replay (fun name => birthAt trace.state name time) (track trace.state trace.actor time episode.name)
      (write (trace.state time) owner key (some output))) owner key = some reverted)
    (related : (TypedCoeffectReplay.setoid (Yield := TypedRegistry.Yield ops) observe).r after reverted) :
    @StageSimulation.Related Name Key A Code PUnit.{u + 1} (TypedCoeffectReplay.setoid observe) Eq
      (mark (write (probeAt trace episode time) owner key (some after)) (trace.actor time) replayPhase)
      (probeAt trace episode (time + 1)) := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  have presence (name : Name) : write (trace.state time) owner key (some output) name = none ↔
      trace.state time name = none := by
    by_cases same : name = owner <;> simp [write, Calculus.modify, same]
  have paired := compare_rollback_write observe (trace.state time) episode.name
    (fun name => birthAt trace.state name time) (track trace.state trace.actor time episode.name)
    sourceSelf liveInSource liveInProbe rolled related
  rw [probe_after_foreign_edit trace episode different kept presence ended]
  exact StageSimulation.mark_related paired (trace.actor time) phases

/-- An empty foreign slot has no pending captures, and its new provision
survives the selected actor's rollback. -/
theorem rollback_foreign_provision (meaning : PartialReplayRegistry.Coeffects (encodeProgram program))
    (before : R) (closing actor : Name) (key : Key) (value : A) (live : Name → Option Nat)
    (word : List (Capture Name Key A)) (tokens : word.map Capture.token = saved before closing)
    (scopes : TableFrame.ScopedAccumulators before) (different : actor ≠ closing)
    (history : PartialReplayRegistry.SlotHistory meaning before actor key) (liveActor : before actor ≠ none)
    (tableEmpty : tableAt before actor key = none) :
    tableAt (replay live word (write before actor key (some value))) actor key = some value := by
  let raw := saved before closing
  obtain ⟨pending, aligned, ready⟩ := history
  have pendingEmpty : pending = [] := by simpa only [tableEmpty] using ready
  have noCalls : captures meaning.denote actor key raw = [] := by
    rw [show captures meaning.denote actor key raw = PartialReplayRegistry.ticketsFor pending closing from
      (aligned closing).symm, pendingEmpty]
    rfl
  have noRestriction : Inverse.restrict actor key ∉ raw := by
    cases parentAt : before closing with
    | none => simp [raw, saved, parentAt]
    | some parent =>
      intro member
      exact different (scopes closing parent parentAt (.restrict actor key)
        (by simpa [raw, saved, parentAt] using member))
  have normalized : PartialReplaySlots.slotWord meaning.denote actor key raw = ([], false) := by
    rw [PartialReplaySlots.slotWord_unrestricted _ _ _ _ noRestriction, noCalls]
  have installed : tableAt (write before actor key (some value)) actor key = some value := by
    rw [PartialReplayRegistry.tableAt_write _ _ _ _ _ _ liveActor, if_pos ⟨rfl, rfl⟩]
  apply replay_partial_slot meaning.denote meaning.agrees
  rw [tokens, PartialReplaySlots.slotWord_exact, normalized, installed]
  rfl

private theorem provide_on_rollback (trace : History) (episode : ClosedEpisode trace)
    (maximal : ∀ later : ClosedEpisode trace, ¬ EpisodeEdge episode later)
    (quiet : Progress.Quiet (trace.state last))
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops
      (tableSetoid observe (fun _ => True)) key)
    {time : Nat} (lower : episode.opened ≤ time) (upper : time ≤ episode.closed)
    {entry : RawFiber Name ops Code} {code : Code} {key : Key} {value : A}
    (different : trace.actor time ≠ episode.name)
    (kept : ¬ withdraws trace episode time (trace.actor time) = true)
    (present : trace.state time (trace.actor time) = some entry)
    (action : (encodeProgram program code).action = .provide key value)
    (declared : entry.component.provides key = true) (empty : entry.table key = none) :
    ∃ row, probeAt trace episode time (trace.actor time) = some row ∧ row.phase = entry.phase ∧
      Land (encodeProgram program) (trace.actor time) code (probeAt trace episode time)
        (write (probeAt trace episode time) (trace.actor time) key (some value))
        (.restrict (trace.actor time) key) ((encodeProgram program code).next (.value value)) ∧
      tableAt (replay (fun name => birthAt trace.state name time) (track trace.state trace.actor time episode.name)
        (write (trace.state time) (trace.actor time) key (some value))) (trace.actor time) key = some value := by
  let actor := trace.actor time
  let before := trace.state time
  let meaning := TypedReplayContracts.coeffects ops observe program recovery commutative
  have bounded : time ≤ last := by have := episode.interval.bounded; omega
  have reached := trace.prefixRun time bounded
  have projected := probe_projects trace episode maximal quiet lower upper
  obtain ⟨row, rowAt, fields⟩ := projected.forward_row kept present
  obtain ⟨phaseRow, phaseAt, samePhase⟩ := probe_keeps_phase trace episode different kept present
  have sameRow := Option.some.inj (rowAt.symm.trans phaseAt)
  subst phaseRow
  have marked : Land (encodeProgram program) actor code (probeAt trace episode time)
      (write (probeAt trace episode time) actor key (some value)) (.restrict actor key)
      ((encodeProgram program code).next (.value value)) :=
    .provide _ _ _ row key value action rowAt (by simpa only [← fields.component] using declared)
      ((fields.domain different key).mp empty)
  refine ⟨row, rowAt, samePhase, marked, ?_⟩
  exact rollback_foreign_provision meaning before episode.name actor key value
    (fun name => birthAt trace.state name time) (track trace.state trace.actor time episode.name)
    ((tracked_stack trace time bounded).projects episode.name) (TableFrame.reachable_scoped _ reached) different
    (PartialReplayRegistry.reachable_slot_history meaning reached actor key) (by simp [before, actor, present])
    (by simp [tableAt, before, actor, present, empty])

private theorem source_and_stack_self (trace : History) (time : Nat) (bounded : time ≤ last)
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops
      (tableSetoid observe (fun _ => True)) key)
    {actor : Name} {entry : RawFiber Name ops Code} {code : Code}
    {stack : List (Inverse Name Key A)} {view : View Name Key}
    (present : trace.state time actor = some entry)
    (phase : entry.phase = .reloading code stack view) :
    (letI : Setoid A := TypedCoeffectReplay.setoid observe
     StageSimulation.Related Eq (trace.state time) (trace.state time) ∧
       StageSimulation.StackRelated stack stack) := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  have self := Transposition.reachable_self_related (encodeProgram program)
    (TypedRegistry.encoded_program_callbacks ops observe program recovery commutative) (trace.prefixRun time bounded)
  exact ⟨self, Transposition.self_reloading_stack self actor entry present code stack view phase⟩

/-- The operation branch of Iter or Finish is a native retained step.
Its resulting registry is structurally related to the next rollback probe,
including the saved inverse. The rule and continuation are the original ones. -/
theorem replay_operation_activation (trace : History) (episode : ClosedEpisode trace)
    (maximal : ∀ later : ClosedEpisode trace, ¬ EpisodeEdge episode later)
    (quiet : Progress.Quiet (trace.state last))
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops
      (tableSetoid observe (fun _ => True)) key)
    {time : Nat} (lower : episode.opened ≤ time) (upper : time ≤ episode.closed)
    {owner : Name} {entry : RawFiber Name ops Code}
    (different : trace.actor time ≠ episode.name)
    (kept : ¬ withdraws trace episode time (trace.actor time) = true)
    (present : trace.state time (trace.actor time) = some entry)
    {code : Code} {stack : List (Inverse Name Key A)} {view : View Name Key}
    (phase : entry.phase = .reloading code stack view)
    (target : Target (trace.state time) (trace.actor time) view)
    {key : Key} {call : A → Except PUnit.{u + 1} (A × (A → A) × A)}
    (action : (encodeProgram program code).action = .operate key call)
    {input output outcome : A} {inverse : A → A}
    (located : location (trace.state time) (trace.actor time) key = some (owner, input))
    (performed : call input = .ok (output, inverse, outcome))
    (ended : trace.state (time + 1) =
      mark (write (trace.state time) owner key (some output)) (trace.actor time)
        (Transposition.landedPhase ((encodeProgram program code).next (.value outcome))
          (.operate owner key inverse) stack view)) :
    ∃ replayed,
      Labeled.Step (encodeProgram program)
        (Transposition.landedRule ((encodeProgram program code).next (.value outcome))) (trace.actor time)
        (probeAt trace episode time) replayed ∧
      @StageSimulation.Related Name Key A Code PUnit.{u + 1} (TypedCoeffectReplay.setoid observe) Eq
        replayed (probeAt trace episode (time + 1)) := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  let probe := probeAt trace episode time
  let next := (encodeProgram program code).next (.value outcome)
  obtain ⟨adjusted, after, captured, reverted, routed, _, landed, _, inverseRelated, rolled, related⟩ :=
    operate_on_rollback trace episode maximal quiet observe recovery commutative lower upper different kept
      present action located performed
  obtain ⟨row, holds, samePhase⟩ := probe_keeps_phase trace episode different kept present
  have projected := probe_projects trace episode maximal quiet lower upper
  have avoids := committed_avoids_closing trace episode maximal lower upper present
    (show entry.phase.committed = some view by simp [phase, Phase.committed])
  let replayed := mark (write probe owner key (some after)) (trace.actor time)
    (Transposition.landedPhase next (.operate owner key captured) stack view)
  have actual := Transposition.landed_step (encodeProgram program) row stack view
    holds (samePhase.trans phase) (projected.target_forward kept present view avoids target) landed
  have bounded : time ≤ last := by have := episode.interval.bounded; omega
  obtain ⟨self, oldStack⟩ := source_and_stack_self trace time bounded observe recovery commutative present phase
  have phases := Transposition.landed_phases_related next (.operate owner key inverseRelated) stack oldStack view
  refine ⟨replayed, actual, ?_⟩
  exact state_after_write trace episode observe different kept self phases
    (located_owner_present located) (located_owner_present routed) ended rolled related

/-- If native Divert took its operation landing, replay takes that same
alternative. The original false target is preserved and the operation
contributes a related new capture to the unloading word. -/
theorem replay_operation_divert (trace : History) (episode : ClosedEpisode trace)
    (maximal : ∀ later : ClosedEpisode trace, ¬ EpisodeEdge episode later)
    (quiet : Progress.Quiet (trace.state last))
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops
      (tableSetoid observe (fun _ => True)) key)
    {time : Nat} (lower : episode.opened ≤ time) (upper : time ≤ episode.closed)
    {owner : Name} {entry : RawFiber Name ops Code}
    (different : trace.actor time ≠ episode.name)
    (kept : ¬ withdraws trace episode time (trace.actor time) = true)
    (present : trace.state time (trace.actor time) = some entry)
    {code : Code} {stack : List (Inverse Name Key A)} {view : View Name Key}
    (phase : entry.phase = .reloading code stack view)
    (stale : ¬ Target (trace.state time) (trace.actor time) view)
    {key : Key} {call : A → Except PUnit.{u + 1} (A × (A → A) × A)}
    (action : (encodeProgram program code).action = .operate key call)
    {input output outcome : A} {inverse : A → A}
    (located : location (trace.state time) (trace.actor time) key = some (owner, input))
    (performed : call input = .ok (output, inverse, outcome))
    (ended : trace.state (time + 1) =
      mark (write (trace.state time) owner key (some output)) (trace.actor time)
        (.unloading (.operate owner key inverse :: stack) view)) :
    ∃ replayed,
      Labeled.Step (encodeProgram program) .divert (trace.actor time) (probeAt trace episode time) replayed ∧
      @StageSimulation.Related Name Key A Code PUnit.{u + 1} (TypedCoeffectReplay.setoid observe) Eq
        replayed (probeAt trace episode (time + 1)) := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  let probe := probeAt trace episode time
  obtain ⟨adjusted, after, captured, reverted, routed, _, landed, _, inverseRelated, rolled, related⟩ :=
    operate_on_rollback trace episode maximal quiet observe recovery commutative lower upper different kept
      present action located performed
  obtain ⟨row, holds, samePhase⟩ := probe_keeps_phase trace episode different kept present
  have projected := probe_projects trace episode maximal quiet lower upper
  let replayed := mark (write probe owner key (some after)) (trace.actor time)
    (.unloading (.operate owner key captured :: stack) view)
  have actual : Labeled.Step (encodeProgram program) .divert (trace.actor time) probe replayed :=
    .divert _ _ _ row code stack view [.operate owner key captured] holds (samePhase.trans phase)
      (fun target => stale (projected.target_backward _ _ target)) (.inr ⟨_, _, landed, rfl⟩)
  have bounded : time ≤ last := by have := episode.interval.bounded; omega
  obtain ⟨self, oldStack⟩ := source_and_stack_self trace time bounded observe recovery commutative present phase
  have extended := StageSimulation.StackRelated.cons (.operate owner key inverseRelated) oldStack
  exact ⟨replayed, actual, state_after_write trace episode observe different kept self
    (.unloading view extended) (located_owner_present located) (located_owner_present routed) ended rolled related⟩

/-- The native provision uses the same literal and continuation in Iter
or Finish. A previously empty binding has no pending operation inverses. -/
theorem replay_provision_activation (trace : History) (episode : ClosedEpisode trace)
    (maximal : ∀ later : ClosedEpisode trace, ¬ EpisodeEdge episode later)
    (quiet : Progress.Quiet (trace.state last))
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops
      (tableSetoid observe (fun _ => True)) key)
    {time : Nat} (lower : episode.opened ≤ time) (upper : time ≤ episode.closed)
    {entry : RawFiber Name ops Code} {code : Code} {stack : List (Inverse Name Key A)} {view : View Name Key}
    (different : trace.actor time ≠ episode.name)
    (kept : ¬ withdraws trace episode time (trace.actor time) = true)
    (present : trace.state time (trace.actor time) = some entry)
    (phase : entry.phase = .reloading code stack view)
    (target : Target (trace.state time) (trace.actor time) view)
    {key : Key} {value : A} (action : (encodeProgram program code).action = .provide key value)
    (declared : entry.component.provides key = true) (empty : entry.table key = none)
    (ended : trace.state (time + 1) = mark (write (trace.state time) (trace.actor time) key (some value))
      (trace.actor time) (Transposition.landedPhase ((encodeProgram program code).next (.value value))
        (.restrict (trace.actor time) key) stack view)) :
    ∃ replayed, Labeled.Step (encodeProgram program)
      (Transposition.landedRule ((encodeProgram program code).next (.value value))) (trace.actor time)
      (probeAt trace episode time) replayed ∧
      @StageSimulation.Related Name Key A Code PUnit.{u + 1} (TypedCoeffectReplay.setoid observe) Eq
        replayed (probeAt trace episode (time + 1)) := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  let next := (encodeProgram program code).next (.value value)
  obtain ⟨row, found, aligned, landed, rolled⟩ := provide_on_rollback trace episode maximal quiet observe recovery
    commutative lower upper different kept present action declared empty
  have projection := probe_projects trace episode maximal quiet lower upper
  have avoids := committed_avoids_closing trace episode maximal lower upper present
    (show entry.phase.committed = some view by simp [phase, Phase.committed])
  have actual := Transposition.landed_step (encodeProgram program) row stack view found (aligned.trans phase)
    (projection.target_forward kept present view avoids target) landed
  have bounded : time ≤ last := by have := episode.interval.bounded; omega
  obtain ⟨self, oldStack⟩ := source_and_stack_self trace time bounded observe recovery commutative present phase
  have related := Transposition.landed_phases_related next (.restrict (trace.actor time) key) stack oldStack view
  exact ⟨_, actual, state_after_write trace episode observe different kept self related
    (by simp [present]) (by simp [found]) ended rolled (Setoid.refl value)⟩

/-- Landed Divert supplies the same provision and saves its restriction
when the original selected activation target is stale. -/
theorem replay_provision_divert (trace : History) (episode : ClosedEpisode trace)
    (maximal : ∀ later : ClosedEpisode trace, ¬ EpisodeEdge episode later)
    (quiet : Progress.Quiet (trace.state last))
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops
      (tableSetoid observe (fun _ => True)) key)
    {time : Nat} (lower : episode.opened ≤ time) (upper : time ≤ episode.closed)
    {entry : RawFiber Name ops Code} {code : Code} {stack : List (Inverse Name Key A)} {view : View Name Key}
    (different : trace.actor time ≠ episode.name)
    (kept : ¬ withdraws trace episode time (trace.actor time) = true)
    (present : trace.state time (trace.actor time) = some entry)
    (phase : entry.phase = .reloading code stack view)
    (stale : ¬ Target (trace.state time) (trace.actor time) view)
    {key : Key} {value : A} (action : (encodeProgram program code).action = .provide key value)
    (declared : entry.component.provides key = true) (empty : entry.table key = none)
    (ended : trace.state (time + 1) = mark (write (trace.state time) (trace.actor time) key (some value))
      (trace.actor time) (.unloading (.restrict (trace.actor time) key :: stack) view)) :
    ∃ replayed, Labeled.Step (encodeProgram program) .divert (trace.actor time) (probeAt trace episode time) replayed ∧
      @StageSimulation.Related Name Key A Code PUnit.{u + 1} (TypedCoeffectReplay.setoid observe) Eq
        replayed (probeAt trace episode (time + 1)) := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  obtain ⟨row, found, aligned, landed, rolled⟩ := provide_on_rollback trace episode maximal quiet observe recovery
    commutative lower upper different kept present action declared empty
  have projection := probe_projects trace episode maximal quiet lower upper
  have actual := Labeled.Step.divert _ _ _ row code stack view [.restrict (trace.actor time) key] found
    (aligned.trans phase) (fun target => stale (projection.target_backward _ _ target)) (.inr ⟨_, _, landed, rfl⟩)
  have bounded : time ≤ last := by have := episode.interval.bounded; omega
  obtain ⟨self, oldStack⟩ := source_and_stack_self trace time bounded observe recovery commutative present phase
  exact ⟨_, actual, state_after_write trace episode observe different kept self (.unloading view (.cons (.restrict _ _) oldStack))
    (by simp [present]) (by simp [found]) ended rolled (Setoid.refl value)⟩

/-- Continue a retained replay from the registry produced by the preceding
step, carrying its saved inverses through the comparison at the next cut. -/
theorem replay_from_related_probe (trace : History) (episode : ClosedEpisode trace)
    (observe : ∀ key, Setoid (V key))
    (respect : ∀ key, PaperObservationEquations.OperationRespects ops key (observe key).r)
    {time : Nat} {rule : Labeled.Rule} {state canonicalNext : R}
    (source : @StageSimulation.Related Name Key A Code PUnit.{u + 1} (TypedCoeffectReplay.setoid observe) Eq
      state (probeAt trace episode time))
    (canonical : Labeled.Step (encodeProgram program) rule (trace.actor time)
      (probeAt trace episode time) canonicalNext)
    (endpoint : @StageSimulation.Related Name Key A Code PUnit.{u + 1} (TypedCoeffectReplay.setoid observe) Eq
      canonicalNext (probeAt trace episode (time + 1))) :
    ∃ next, Labeled.Step (encodeProgram program) rule (trace.actor time) state next ∧
      @StageSimulation.Related Name Key A Code PUnit.{u + 1} (TypedCoeffectReplay.setoid observe) Eq
        next (probeAt trace episode (time + 1)) := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  obtain ⟨next, native, paired⟩ := TypedRegistry.encoded_step_simulation ops observe program respect
    (source.symm (fun _ _ eq => eq.symm)) canonical
  exact ⟨next, native, StageSimulation.Related.trans (Q := Eq) (fun a b => a.trans b)
    (paired.symm (fun _ _ eq => eq.symm)) endpoint⟩

end Cordis.Repairs.EpisodeOperationReplay
