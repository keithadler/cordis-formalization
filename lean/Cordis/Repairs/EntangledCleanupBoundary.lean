import Cordis.Repairs.SupportLinearizationExample
import Cordis.Repairs.FrozenGuardedApplications

namespace Cordis.Repairs.EntangledCleanupBoundary
open Calculus Stages LegalHistory GuardedHistory IncarnationReplay
open OperationExample SupportLinearizationExample
universe u

abbrev code := TypedRegistry.encodeProgram program
abbrev source := SupportLinearizationExample.trace.encode

def events : Nat → Event Nat Unit Bool
  | 0 => .command (.insert 0 provider)
  | 1 => .lifecycle .begin 0
  | 2 => .lifecycle .finish 0
  | 3 => .command (.insert 1 consumer)
  | 4 => .lifecycle .begin 1
  | _ => .lifecycle .finish 1

def guarded : Trace code 6 where
  state := source.state
  notes := Vestigial.cutNotes source.state (fun t => Vestigial.eventActor (events t))
  event := events
  start := rfl
  seed := rfl
  step t bounded := by
    refine ⟨?_, rfl⟩
    have cuts : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 := by omega
    rcases cuts with rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨⟨rfl, by simp, fun _ _ => trivial⟩, ?_⟩
      change TypedRegistry.encodeRegistry operations inserted = put (TypedRegistry.encodeRegistry operations empty) 0 (fresh provider none)
      simp only [inserted, TypedRegistry.encode_put, TypedRegistry.encode_fresh]
    · exact source.step 1 (by decide)
    · exact source.step 2 (by decide)
    · refine ⟨⟨rfl, by simp, ?_⟩, ?_⟩
      · intro name key
        split <;> simp [consumer]
      · change TypedRegistry.encodeRegistry operations joined = put (TypedRegistry.encodeRegistry operations active) 1 (fresh consumer none)
        simp only [joined, TypedRegistry.encode_put, TypedRegistry.encode_fresh]
    · exact source.step 4 (by decide)
    · exact source.step 5 (by decide)

/-- The identity cases of Lemma 67 hold on the guarded source. A native
shadow of Unload is used only to classify the label, never as the successor
cut of the guarded history. -/
theorem guarded_identity_cases {Name Key Value Code Error : Type u}
    [DecidableEq Name] [DecidableEq Key]
    {program : Code → Instruction Name Key Value Code Error} {last time : Nat}
    (trace : Trace program last) (bounded : time < last)
    {name : Name} {localRow foreign : Fiber Name Key Value Code (Inverse Name Key Value) Error}
    {view : View Name Key}
    (present : trace.state time name = some localRow)
    (foreignPresent : trace.state time (trace.actor time) = some foreign)
    (different : name ≠ trace.actor time)
    (installed : localRow.phase.committed = some view) :
    let provider := EntangledApplications.ProviderOverlap localRow foreign
    let consumer := EntangledApplications.ProviderOverlap foreign localRow
    (provider ∨ consumer) →
    (provider → trace.rule time = .retire ∨ trace.rule time = .leave) ∧
    ((∃ code word chosen, localRow.phase = .reloading code word chosen) →
      trace.rule time = .retire ∨ trace.rule time = .leave ∨ trace.rule time = .remove) := by
  dsimp only
  intro entangled
  have shadow : ∃ after, Labeled.Step program (trace.rule time) (trace.actor time) (trace.state time) after := by
    rcases transition_cases (trace.step time bounded).1 with native | ⟨actor, event, step⟩
    · exact ⟨_, native⟩
    · obtain ⟨row, chosen, found, phase, free, _⟩ := step
      unfold Trace.rule Trace.actor
      rw [event]
      exact ⟨_, .unload _ _ _ _ chosen found phase free⟩
  obtain ⟨_, native⟩ := shadow
  obtain ⟨owned, disjoint⟩ := trace.ownership time (Nat.le_of_lt bounded)
  have supported := trace.supported time (Nat.le_of_lt bounded)
  have pinned (overlap : EntangledApplications.ProviderOverlap localRow foreign) :
      trace.rule time = .retire ∨ trace.rule time = .leave := by
    obtain ⟨key, provides, requires⟩ := overlap
    exact OrderingIntervals.entangled_provider_rule name (trace.actor time) localRow foreign view key
      supported owned disjoint different present foreignPresent installed provides requires native
  refine ⟨pinned, ?_⟩
  rintro ⟨code, word, chosen, loading⟩
  rcases entangled with provider | ⟨key, provides, overlap⟩
  · exact (pinned provider).imp id Or.inl
  · have requires : foreign.component.requires key = true := by
      rcases overlap with required | conflict
      · exact required
      · exact False.elim (disjoint name (trace.actor time) localRow foreign
          present foreignPresent different key ⟨provides, conflict⟩)
    exact (OrderingIntervals.reloading_consumer_rule (trace.actor time) name foreign localRow key code word chosen
      supported owned disjoint foreignPresent present loading requires provides native).imp id Or.inr

/-- For each of the labels obtained above, the actual selected state map
is definitionally the successful identity, even on counterfactual probes. -/
theorem freeze_identity_of_control {Name Key Value Code Error : Type u}
    [DecidableEq Name] [DecidableEq Key]
    {program : Code → Instruction Name Key Value Code Error}
    (meaning : PartialReplayRegistry.Coeffects program)
    {rule : Labeled.Rule} {actor draw : Name} {use : RuleEvaluation.Use Name Key Value Code}
    {before : Registry Name Key Value Code (Inverse Name Key Value) Error}
    (allowed : use.allowed rule before actor)
    (control : rule = .retire ∨ rule = .leave ∨ rule = .remove)
    (word : List (Capture Name Key Value)) (live : Name → Option Nat) :
    FrozenGuardedApplications.freeze meaning actor draw use word live = some := by
  cases use with
  | identity => rfl
  | iteration _ => rcases control with rfl | rfl | rfl <;> simp [RuleEvaluation.Use.allowed] at allowed
  | accumulator _ => rcases control with rfl | rfl | rfl <;> simp [RuleEvaluation.Use.allowed] at allowed

/-- Changing which retirements fire cannot change any binding in the
completed replay, even when a captured name denotes a later birth. -/
theorem replay_independent_of_birth_test {Name Key Value Code Error : Type u}
    [DecidableEq Name] [DecidableEq Key] (first second : Name → Option Nat)
    (word : List (Capture Name Key Value))
    (state : Registry Name Key Value Code (Inverse Name Key Value) Error) :
    RuleEvaluation.TablesUnchanged (replay first word state) (replay second word state) := by
  intro owner key
  exact (replay_tables first word (fun _ _ => rfl) owner key).symm.trans
    (replay_tables second word (fun _ _ => rfl) owner key)

/-- The strict guarded word has the same success domain and table result
under any retirement matching decisions. -/
theorem strict_replay_independent_of_birth_test {Name Key Value Code Error : Type u}
    [DecidableEq Name] [DecidableEq Key]
    {program : Code → Instruction Name Key Value Code Error}
    (meaning : PartialReplayRegistry.Coeffects program)
    (first second : Name → Option Nat) (word : List (Capture Name Key Value))
    (left right : Registry Name Key Value Code (Inverse Name Key Value) Error)
    (tables : RuleEvaluation.TablesUnchanged left right) :
    ∀ output, ScopedReplayComparison.run meaning first word left = some output →
      ∃ other, ScopedReplayComparison.run meaning second word right = some other ∧
        RuleEvaluation.TablesUnchanged output other := by
  induction word generalizing left right with
  | nil =>
    intro output landed
    cases Option.some.inj landed
    exact ⟨right, rfl, tables⟩
  | cons capture rest ih =>
    intro output landed
    change ((ScopedReplayComparison.runCapture meaning first capture left).bind
      (ScopedReplayComparison.run meaning first rest)) = some output at landed
    obtain ⟨middle, ran, remaining⟩ := Option.bind_eq_some_iff.mp landed
    obtain ⟨ready, rfl⟩ := (ScopedReplayComparison.capture_success_iff meaning first capture left middle).mp ran
    have enabled : ReplayBindingDomains.InverseDefined meaning right capture.token := by
      cases token : capture.token with
      | unit | retire => trivial
      | restrict owner key | operate owner key _ =>
        simpa only [token, ReplayBindingDomains.InverseDefined, ← tables owner key] using ready
    have compared : RuleEvaluation.TablesUnchanged (capture.apply first left) (capture.apply second right) := by
      intro owner key
      exact (replay_tables first [capture] (fun _ _ => rfl : RuleEvaluation.TablesUnchanged left left) owner key).symm.trans
        (replay_tables second [capture] tables owner key)
    obtain ⟨other, ranRest, same⟩ := ih _ _ compared output remaining
    refine ⟨other, ?_, same⟩
    exact Option.bind_eq_some_iff.mpr ⟨_, (ScopedReplayComparison.capture_success_iff meaning second capture right _).mpr
      ⟨enabled, rfl⟩, ranRest⟩

/-- A guarded completion uses the captured birth tests for unload and the
paper's fixed landing map for all primitive applications. -/
noncomputable def completedRevision {Name Key Value Code Error : Type u}
    (use : RuleEvaluation.Use Name Key Value Code) (live : Name → Option Nat)
    (word : List (Capture Name Key Value))
    (native : Registry Name Key Value Code (Inverse Name Key Value) Error →
      Registry Name Key Value Code (Inverse Name Key Value) Error)
    [DecidableEq Name] [DecidableEq Key] :=
  match use with
  | .accumulator _ => replay live word
  | _ => native

private theorem completedRevision_tables {Name Key Value Code Error : Type u}
    [DecidableEq Name] [DecidableEq Key]
    {program : Code → Instruction Name Key Value Code Error} {actor : Name}
    {use : RuleEvaluation.Use Name Key Value Code} {source middle left right : Registry Name Key Value Code
      (Inverse Name Key Value) Error} {native}
    (frozen : EntangledApplications.FrozenApplication program actor use source middle native)
    (live : Name → Option Nat) (word : List (Capture Name Key Value))
    (selected : ∀ tokens, use = .accumulator tokens → word.map Capture.token = tokens)
    (tables : RuleEvaluation.TablesUnchanged left right)
    (presence : ∀ name, left name = none ↔ right name = none) :
    RuleEvaluation.TablesUnchanged (native left) (completedRevision use live word native right) := by
  cases frozen with
  | identity => exact tables
  | accumulator tokens =>
    have same := selected tokens rfl
    rw [← same]
    exact replay_tables live word tables
  | iteration landing =>
    cases landing with
    | unit => exact tables
    | operate =>
      intro owner key
      simp only [completedRevision, InterleavedRecovery.tableAt_transform, tables owner key]
    | provide entry provided value action found legal absent =>
      intro owner key
      simp only [completedRevision]
      by_cases missing : left actor = none
      · by_cases same : owner = actor
        · subst owner
          simp [StageRecovery.tableAt, write, Calculus.modify, missing, (presence actor).mp missing]
        · simpa only [StageRecovery.tableAt, write, Calculus.modify, if_neg same] using tables owner key
      · have liveRight : right actor ≠ none := fun h => missing ((presence actor).mpr h)
        rw [PartialReplayRegistry.tableAt_write _ _ _ _ _ _ missing,
          PartialReplayRegistry.tableAt_write _ _ _ _ _ _ liveRight, tables owner key]
    | instantiate component child action eligible =>
      intro owner key
      by_cases same : owner = child
      · subst owner
        simp [completedRevision, StageRecovery.tableAt, put]
      · simp only [completedRevision, StageRecovery.tableAt, put, if_neg same]
        exact tables owner key

/-- The table square for clause (2), with the actual guarded unload word
and the paper's identity convention at a missing operation binding. The
native frozen witness only selects the primitive or the token sequence. -/
private theorem guarded_table_square {Name Key Value Code Error : Type u}
    [DecidableEq Name] [DecidableEq Key]
    {program : Code → Instruction Name Key Value Code Error} {last time : Nat}
    (trace : Trace program last) (meaning : PartialReplayRegistry.Coeffects program)
    (bounded : time ≤ last) (actor other : Name) (row foreign : Fiber Name Key Value Code
      (Inverse Name Key Value) Error)
    (present : trace.state time actor = some row) (foreignPresent : trace.state time other = some foreign)
    (different : other ≠ actor)
    (separate : ¬ EntangledApplications.ProviderOverlap row foreign)
    {rule : Labeled.Rule} {use : RuleEvaluation.Use Name Key Value Code} {middle native}
    (frozen : EntangledApplications.FrozenApplication program other use (trace.state time) middle native)
    (allowed : use.allowed rule (trace.state time) other) :
    let live := (trace.notes time).1
    let actorWord := (trace.notes time).2 actor
    let revise := completedRevision use live ((trace.notes time).2 other) native
    let before := trace.state time
    ∀ owner key,
      Iterators.OptionRel (meaning.observe key).r
        (StageRecovery.tableAt (replay live actorWord (revise before)) owner key)
        (StageRecovery.tableAt (revise (replay live actorWord before)) owner key) := by
  dsimp only
  have routing : TableFrame.ScopedAccumulators (trace.state time) := by
    intro name fiber found token member
    have route := (trace.invariants time bounded).2 name fiber found token member
    cases token with
    | unit | retire | restrict => exact route
    | operate =>
      exact route.imp id (fun ⟨_, _, required, _⟩ => required)
  have separated key (provided : foreign.component.provides key = true) :
      row.component.requires key = false := by
    cases required : row.component.requires key with
    | false => rfl
    | true => exact False.elim (separate ⟨key, provided, Or.inl required⟩)
  have selected tokens (isWord : use = .accumulator tokens) :
      ((trace.notes time).2 other).map Capture.token = tokens := by
    subst use
    obtain ⟨_, entry, view, found, phase⟩ := allowed
    rw [trace.projects time bounded other]
    simp [PartialReplayRegistry.saved, found, phase, Phase.accumulator]
  have actorWord := trace.projects time bounded actor
  have actual := completedRevision_tables frozen (trace.notes time).1 ((trace.notes time).2 other)
    selected (left := trace.state time) (right := trace.state time) (fun _ _ => rfl) (fun _ => Iff.rfl)
  have firstEndpoint := replay_tables (trace.notes time).1 ((trace.notes time).2 actor) actual
  rw [actorWord] at firstEndpoint
  have replayed := replay_tables (trace.notes time).1 ((trace.notes time).2 actor)
    (left := trace.state time) (right := trace.state time) (fun _ _ => rfl)
  rw [actorWord] at replayed
  have presence name :
      discharge Stages.undo (PartialReplayRegistry.saved (trace.state time) actor) (trace.state time) name = none ↔
      replay (trace.notes time).1 ((trace.notes time).2 actor) (trace.state time) name = none := by
    rw [← replay_native_discharge]
    exact (replay_presence _ _ _ _).trans (replay_presence _ _ _ _).symm
  have secondEndpoint := completedRevision_tables frozen (trace.notes time).1 ((trace.notes time).2 other)
    selected replayed presence
  intro owner key
  obtain ⟨left, right, _, _, first, second, observed⟩ :=
    PartialReplayRegistry.frozen_application_partial_square_of_history meaning
      (trace.slot_history meaning time bounded) routing actor other row foreign present foreignPresent
      different separated frozen allowed owner key
  rw [← firstEndpoint owner key, ← secondEndpoint owner key, first, second]
  exact observed

/-- Clause (2) at an actual guarded cut. The application and control edit
come from the guarded step. Only the application enters the square. -/
theorem guarded_clause_two {Name Key Value Code Error : Type u}
    [DecidableEq Name] [DecidableEq Key]
    {program : Code → Instruction Name Key Value Code Error} {last time : Nat}
    (trace : Trace program last) (meaning : PartialReplayRegistry.Coeffects program)
    (bounded : time < last) (actor : Name) (row foreign : Fiber Name Key Value Code
      (Inverse Name Key Value) Error)
    (present : trace.state time actor = some row)
    (foreignPresent : trace.state time (trace.actor time) = some foreign)
    (different : trace.actor time ≠ actor)
    (separate : ¬ EntangledApplications.ProviderOverlap row foreign) :
    let before := trace.state time
    let notes := trace.notes time
    let rollback := replay notes.1 (notes.2 actor)
    ∃ use middle nativeMiddle native,
      GuardedPartialApplications.Application meaning notes (trace.actor time) use before middle ∧
      EntangledApplications.FrozenApplication program (trace.actor time) use before nativeMiddle native ∧
      use.allowed (trace.rule time) before (trace.actor time) ∧
      let revise := completedRevision use notes.1 (notes.2 (trace.actor time)) native
      RuleEvaluation.TablesUnchanged (revise before) middle ∧
      ∀ owner key, Iterators.OptionRel (meaning.observe key).r
        (StageRecovery.tableAt (rollback (revise before)) owner key)
        (StageRecovery.tableAt (revise (rollback before)) owner key) := by
  dsimp only
  obtain ⟨use, middle, _, actual, allowed, _, _, _, _, _⟩ :=
    GuardedPartialApplications.trace_factorization trace meaning bounded
  have choose : ∃ nativeMiddle native,
      EntangledApplications.FrozenApplication program (trace.actor time) use (trace.state time) nativeMiddle native ∧
      RuleEvaluation.TablesUnchanged
        (completedRevision use (trace.notes time).1 ((trace.notes time).2 (trace.actor time)) native
          (trace.state time)) middle := by
    cases use with
    | identity =>
      cases actual
      exact ⟨_, id, .identity _, fun _ _ => rfl⟩
    | accumulator tokens =>
      exact ⟨_, _, .accumulator tokens _, fun owner key => by rw [actual.2.2]; rfl⟩
    | iteration code =>
      obtain ⟨native, frozen⟩ := EntangledApplications.freeze_application program actual
      refine ⟨middle, native, frozen, ?_⟩
      cases frozen with
      | iteration landing =>
        cases landing with
        | unit | provide | instantiate => exact fun _ _ => rfl
        | operate changed call owner before after inverse outcome action located performed =>
          intro holder key
          simp only [completedRevision]
          rw [InterleavedRecovery.tableAt_transform]
          have live : trace.state time owner ≠ none := by
            intro missing
            have occupied := PartialReplayRegistry.located_value located
            simp [StageRecovery.tableAt, missing] at occupied
          by_cases selected : holder = owner ∧ key = changed
          · obtain ⟨rfl, rfl⟩ := selected
            rw [if_pos ⟨rfl, rfl⟩, PartialReplayRegistry.tableAt_write _ _ _ _ _ _ live, if_pos ⟨rfl, rfl⟩]
            simp [PartialReplayRegistry.located_value located, InterleavedRecovery.callbackMap, performed]
          · rw [if_neg selected, PartialReplayRegistry.tableAt_write _ _ _ _ _ _ live, if_neg selected]
  obtain ⟨nativeMiddle, native, frozen, tables⟩ := choose
  exact ⟨use, middle, nativeMiddle, native, actual, frozen, allowed, tables,
    guarded_table_square trace meaning (Nat.le_of_lt bounded) actor (trace.actor time) row foreign
      present foreignPresent different separate frozen allowed⟩

/-- A strict dependency operation cannot execute after rollback clears
its bound slot, independently of the callback at that key. -/
theorem strict_operation_at_absent_binding {Name Key Value Code Error : Type u}
    [DecidableEq Name] [DecidableEq Key]
    {program : Code → Instruction Name Key Value Code Error} {instruction : Code}
    {actor draw owner : Name} {key : Key} {call} {state : Registry Name Key Value Code (Inverse Name Key Value) Error}
    (operation : (program instruction).action = .operate key call)
    (route : bindingOwner state actor key = some owner)
    (absent : StageRecovery.tableAt state owner key = none) :
    SemanticHead.evaluate program actor draw instruction state = none := by
  cases found : state owner <;>
    simp [SemanticHead.evaluate, operation, location, route, StageRecovery.tableAt, found] at absent ⊢
  simp [absent]

/-- A six-step guarded trace exhibits the difference between the strict
frozen application and the absent-binding convention used on p. 45. -/
theorem strict_square_fails :
    ∀ meaning : PartialReplayRegistry.Coeffects code,
    let before := guarded.state 5
    let notes := guarded.notes 5
    let undo := replay notes.1 (notes.2 0)
    ControlFrame.viewAt before 0 = some view ∧
    (∃ entry, before 0 = some entry ∧ entry.component.provides () = true) ∧
    (∃ entry, before 1 = some entry ∧ entry.component.requires () = true ∧ entry.component.provides () = false) ∧
    (∃ landed, (SemanticHead.evaluate code 1 1 false before).map Prod.fst = some landed ∧
      ScopedReplayComparison.run meaning notes.1 (notes.2 0) landed = some (undo landed) ∧
      StageRecovery.tableAt (undo landed) 0 () = none) ∧
    ScopedReplayComparison.run meaning notes.1 (notes.2 0) before = some (undo before) ∧
    SemanticHead.evaluate code 1 1 false (undo before) = none := by
  intro meaning
  exact ⟨rfl, ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl, rfl⟩, ⟨_, rfl, rfl, rfl⟩, rfl, rfl⟩

end Cordis.Repairs.EntangledCleanupBoundary
