import Cordis.Repairs.GuardedActivationExchange

/-! Group open activations using the actual order in which their views were
installed. Command cuts keep their positions during this phase. -/
namespace Cordis.Repairs.GuardedHistory
open Calculus Stages LegalHistory
open PaperEffectEquations (CoeffectOperations ValueOperationWitness)
open PaperObservationEquations (OperationRespects)
open PartialCoeffectIndependenceContracts (tableSetoid)
open TypedRegistry (encodeProgram Scalar)
open SupportAtQuiescence (TotalProvision)
universe u
variable {Name Key Value Code Error : Type u} [DecidableEq Name] [DecidableEq Key]
variable {program : Code → Instruction Name Key Value Code Error} {last : Nat}

/-- Use the cut at which each actor installed its view as its rank. -/
def openingRanks (trace : Trace program last) : Nat → Name → Nat
  | 0 => fun _ => 0
  | time + 1 =>
    match trace.event time with
    | .lifecycle .begin actor => SupportOrder.advance (openingRanks trace time) actor time
    | _ => openingRanks trace time

theorem openingRanks_bounded (trace : Trace program last) (time : Nat) (name : Name) :
    openingRanks trace time name ≤ time := by
  induction time with
  | zero => exact Nat.le_refl _
  | succ time ih =>
    have prior : openingRanks trace time name ≤ time + 1 := Nat.le_trans ih (Nat.le_succ _)
    cases event : trace.event time with
    | command => simpa [openingRanks, event] using prior
    | lifecycle kind actor =>
      cases kind
      case begin => by_cases same : name = actor <;> simp [openingRanks, event, SupportOrder.advance, same, prior]
      all_goals simpa [openingRanks, event] using prior

private theorem openingRanks_at_begin (trace : Trace program last)
    (openOnly : ¬ Nonempty (ClosedEpisode trace)) {start : Nat} {actor : Name}
    (event : trace.event start = .lifecycle .begin actor) :
    ∀ time, start < time → time ≤ last → openingRanks trace time actor = start + 1 := by
  intro time
  induction time with
  | zero => omega
  | succ time ih =>
    intro earlier bounded
    by_cases same : start = time
    · subst time
      simp [openingRanks, event, SupportOrder.advance]
    · have prior := ih (by omega) (by omega)
      cases later : trace.event time with
      | command => simpa [openingRanks, later] using prior
      | lifecycle kind name =>
        cases kind <;> try (simpa [openingRanks, later] using prior)
        have different : actor ≠ name := by
          intro sameActor
          subst name
          exact same (trace.begin_unique openOnly (by omega) (by omega) event later)
        simpa [openingRanks, later, SupportOrder.advance, different] using prior

/-- A fixed rank follows the order of actual Begin events in this trace. -/
def ChronologicalOpenings (trace : Trace program last) (rank : Name → Nat) : Prop :=
  ∀ {first later : Nat} {left right : Name}, first < later → later < last →
    trace.event first = .lifecycle .begin left → trace.event later = .lifecycle .begin right →
    rank left < rank right

theorem Trace.chronological_openings (trace : Trace program last) (openOnly : ¬ Nonempty (ClosedEpisode trace)) :
    ChronologicalOpenings trace (openingRanks trace last) := by
  intro first later left right asc bounded opened laterOpened
  rw [openingRanks_at_begin trace openOnly opened last (by omega) (Nat.le_refl _),
    openingRanks_at_begin trace openOnly laterOpened last bounded (Nat.le_refl _)]
  omega

/-- The chronological opening ranks satisfy the actual committed demand
and captured child edges at every cut. -/
theorem Trace.opening_ranks_ordered (trace : Trace program last)
    (openOnly : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    (time : Nat) (bounded : time ≤ last) :
    SupportOrder.Ordered (trace.state time) (openingRanks trace time) := by
  induction time with
  | zero =>
    rw [trace.start]
    constructor
    · rintro consumer provider key ⟨_, _, found, _⟩
      cases found
    · intro child row parent view found
      cases found
  | succ time ih =>
    have old := ih (by omega)
    have ordinary {rule : Labeled.Rule} {actor : Name}
        (step : Labeled.Step program rule actor (trace.state time) (trace.state (time + 1)))
        (views : ControlFrame.viewAt (trace.state (time + 1)) = ControlFrame.viewAt (trace.state time))
        (rank : openingRanks trace (time + 1) = openingRanks trace time) :
        SupportOrder.Ordered (trace.state (time + 1)) (openingRanks trace (time + 1)) := by
      rw [rank]
      exact SupportOrder.ordered_of_views program step.toCalculus (fun n _ found => (congrFun views n) ▸ found)
        (openingRanks trace time) old
    cases event : trace.event time with
    | command command =>
      have step := (trace.step time (by omega)).1
      rw [event] at step
      have native := ExchangeReplay.command_labeled (program := program) command step
      have views := ControlFrame.labeled_view_cases program native
      cases command <;> exact ordinary native views (by simp [openingRanks, event])
    | lifecycle kind actor =>
      obtain ⟨live, step⟩ := trace.activation_at openOnly quiet (by omega) event
      cases kind
      case begin =>
        obtain ⟨row, view, found, inactive, _, target, endpoint⟩ := ControlFrame.labeled_view_cases program step
        have run := Results.rootTrace (trace.toIndexed openOnly) (trace.indexed_roots openOnly) time (by omega)
        have captured := ChildProvenance.reachable_captured program run
        rw [endpoint]
        change SupportOrder.Ordered _ (openingRanks trace (time + 1))
        rw [openingRanks, event]
        exact SupportOrder.begin_ordered _ actor row view found inactive target (trace.supported time (by omega))
          captured (openingRanks trace time) time (openingRanks_bounded trace time) old
      case iter => exact ordinary step (ControlFrame.labeled_view_cases program step) (by simp [openingRanks, event])
      case finish => exact ordinary step (ControlFrame.labeled_view_cases program step) (by simp [openingRanks, event])
      all_goals simp [Lifecycle.rule, Transposition.Activation] at live

/-- These same ranks strictly order the active support graph at the quiet
endpoint with total provisions. -/
theorem Trace.opening_ranks_support (trace : Trace program last)
    (openOnly : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    (total : TotalProvision (trace.state last)) {predecessor actor : Name}
    (edge : SupportUniqueness.ActivePredecessor (trace.state last) predecessor actor) :
    openingRanks trace last predecessor < openingRanks trace last actor := by
  have run := Results.rootTrace (trace.toIndexed openOnly) (trace.indexed_roots openOnly) last (Nat.le_refl _)
  have reached := (trace.toIndexed openOnly).prefixRun last (Nat.le_refl _)
  have fixed := SupportAtQuiescence.active_solution_of_capture (ChildProvenance.reachable_captured program run) quiet total
  exact SupportUniqueness.active_edge_decreases _ _ (trace.opening_ranks_ordered openOnly quiet last (Nat.le_refl _))
    (trace.supported last (Nat.le_refl _)) (Transposition.reachable_owned program reached)
    (SupportUniqueness.reachable_disjoint program run) fixed edge

/-- A chronological rank still orders the support graph after the opening
cuts have moved. The actual cuts witness the same strict comparisons. -/
theorem ChronologicalOpenings.support {trace : Trace program last} {rank : Name → Nat}
    (chronological : ChronologicalOpenings trace rank)
    (openOnly : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    (total : TotalProvision (trace.state last)) {predecessor actor : Name}
    (edge : SupportUniqueness.ActivePredecessor (trace.state last) predecessor actor) :
    rank predecessor < rank actor := by
  have opening {name : Name} (active : SupportAtQuiescence.Active (trace.state last) name) :
      ∃ cut, cut < last ∧ trace.event cut = .lifecycle .begin name := by
    obtain ⟨row, found, available⟩ := active
    apply trace.begin_of_installed (Nat.le_refl _)
    cases phase : row.phase <;> simp_all [ControlFrame.viewAt, Phase.available, Phase.committed]
  obtain ⟨first, firstBound, firstEvent⟩ := opening edge.2.1
  obtain ⟨later, laterBound, laterEvent⟩ := opening edge.1
  have order := trace.opening_ranks_support openOnly quiet total edge
  rw [openingRanks_at_begin trace openOnly firstEvent last firstBound (Nat.le_refl _),
    openingRanks_at_begin trace openOnly laterEvent last laterBound (Nat.le_refl _)] at order
  exact chronological (by omega : first < later) laterBound firstEvent laterEvent

theorem ChronologicalOpenings.swap {trace moved : Trace program last} {rank : Name → Nat} {time : Nat}
    (chronological : ChronologicalOpenings trace rank)
    (notBegin : ∀ actor, trace.event (time + 1) ≠ .lifecycle .begin actor)
    (events : ∀ cut, cut < last → moved.event cut =
      if cut = time then trace.event (time + 1) else if cut = time + 1 then trace.event time else trace.event cut) :
    ChronologicalOpenings moved rank := by
  let oldCut (cut : Nat) := if cut = time + 1 then time else cut
  have opening {cut : Nat} {name : Name} (within : cut < last)
      (event : moved.event cut = .lifecycle .begin name) :
      cut ≠ time ∧ oldCut cut < last ∧ trace.event (oldCut cut) = .lifecycle .begin name := by
    have before : cut ≠ time := by
      intro same
      subst cut
      have impossible := (events time (by omega)).symm.trans event
      exact notBegin name (by simpa only [ite_true] using impossible)
    have prior := (events cut within).symm.trans event
    by_cases second : cut = time + 1
    · exact ⟨before, by simp [oldCut, second]; omega, by simpa [oldCut, before, second] using prior⟩
    · exact ⟨before, by simpa [oldCut, second] using within, by simpa [oldCut, before, second] using prior⟩
  intro first laterCut left right asc valid firstEvent secondEvent
  obtain ⟨notFirst, _, firstOpened⟩ := opening (by omega) firstEvent
  obtain ⟨notLater, laterBound, laterOpened⟩ := opening valid secondEvent
  have order : oldCut first < oldCut laterCut := by
    unfold oldCut
    split <;> split <;> omega
  exact chronological order laterBound firstOpened laterOpened

/-- In a command-free run, adjacent activations follow opening rank. -/
def OrderedActivationRuns (trace : Trace program last) (rank : Name → Nat) : Prop :=
  ∀ {time : Nat} {firstKind secondKind : Lifecycle} {first second : Name},
    time + 1 < last → trace.event time = .lifecycle firstKind first →
    trace.event (time + 1) = .lifecycle secondKind second → rank first ≤ rank second

theorem OrderedActivationRuns.rank_between {trace : Trace program last} {rank : Name → Nat}
    (sorted : OrderedActivationRuns trace rank)
    {first later : Nat} (order : first ≤ later) (bounded : later < last)
    (activations : ∀ cut, first ≤ cut → cut ≤ later → ∃ kind actor, trace.event cut = .lifecycle kind actor)
    {aKind bKind : Lifecycle} {a b : Name} (aAt : trace.event first = .lifecycle aKind a)
    (bAt : trace.event later = .lifecycle bKind b) : rank a ≤ rank b := by
  induction later generalizing bKind b with
  | zero =>
    have same : first = 0 := by omega
    have actors := (Event.lifecycle.inj ((same ▸ aAt).symm.trans bAt)).2
    exact Nat.le_of_eq (congrArg rank actors)
  | succ later ih =>
    by_cases same : first = later + 1
    · have actors := (Event.lifecycle.inj ((same ▸ aAt).symm.trans bAt)).2
      exact Nat.le_of_eq (congrArg rank actors)
    · obtain ⟨middleKind, middle, atMiddle⟩ := activations later (by omega) (by omega)
      have through := ih (by omega) (by omega) (fun cut lo hi => activations cut lo (by omega)) atMiddle
      exact Nat.le_trans through (sorted bounded atMiddle bAt)

/-- A single actor's activations are contiguous inside each run between
commands. The result follows from the strict order of distinct openings. -/
theorem OrderedActivationRuns.contiguous {trace : Trace program last} {rank : Name → Nat}
    (sorted : OrderedActivationRuns trace rank) (chronological : ChronologicalOpenings trace rank)
    (openOnly : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    {first middle later : Nat} (lower : first ≤ middle) (upper : middle ≤ later) (bounded : later < last)
    (activations : ∀ cut, first ≤ cut → cut ≤ later → ∃ kind actor, trace.event cut = .lifecycle kind actor)
    {aKind bKind cKind : Lifecycle} {a b : Name} (aAt : trace.event first = .lifecycle aKind a)
    (bAt : trace.event middle = .lifecycle bKind b)
    (cAt : trace.event later = .lifecycle cKind a) : b = a := by
  have left := sorted.rank_between lower (by omega) (fun cut lo hi => activations cut lo (by omega)) aAt bAt
  have right := sorted.rank_between upper bounded (fun cut lo hi => activations cut (by omega) hi) bAt cAt
  obtain ⟨aOpening, aBound, aEvent⟩ := trace.opening_of_activation openOnly quiet (by omega) aAt
  obtain ⟨bOpening, bBound, bEvent⟩ := trace.opening_of_activation openOnly quiet (by omega) bAt
  rcases Nat.lt_trichotomy aOpening bOpening with earlier | same | after
  · exact False.elim ((Nat.not_lt_of_ge right) (chronological earlier (by omega) aEvent bEvent))
  · exact (Event.lifecycle.inj ((same ▸ aEvent).symm.trans bEvent)).2.symm
  · exact False.elim ((Nat.not_lt_of_ge left) (chronological after (by omega) bEvent aEvent))

theorem related_total_provision [Setoid Value] {before after : Registry Name Key Value Code (Inverse Name Key Value) Error}
    (related : StageSimulation.Related Eq before after) (total : TotalProvision before) :
    TotalProvision after := by
  intro name row found active key
  obtain ⟨source, present, fields⟩ := StageSimulation.present_related
    (related.symm (fun _ _ same => same.symm)) name row found
  have wasActive := (GuardObservations.phase_available_iff fields.phase.observed.1).mp active
  have domains := GuardObservations.table_none_iff fields.observed key
  exact (not_congr domains).trans ((total name source present wasActive key).trans (by rw [fields.component.provides]))

private def rankAtEvent (rank : Name → Nat) : Event Name Key Code → Nat
  | .lifecycle _ actor => rank actor
  | .command _ => 0

private def activationCost (trace : Trace program last) (rank : Name → Nat) : Nat :=
  ((List.range last).map fun cut => (last - cut) * rankAtEvent rank (trace.event cut)).sum

private theorem activationCost_decreases {trace moved : Trace program last} {rank : Name → Nat} {time : Nat}
    (bounded : time + 1 < last) {firstKind secondKind : Lifecycle} {first second : Name}
    (firstEvent : trace.event time = .lifecycle firstKind first)
    (secondEvent : trace.event (time + 1) = .lifecycle secondKind second)
    (inverted : rank second < rank first)
    (events : ∀ cut, cut < last → moved.event cut =
      if cut = time then trace.event (time + 1) else if cut = time + 1 then trace.event time else trace.event cut) :
    activationCost moved rank < activationCost trace rank := by
  let contribution (source : Trace program last) (cut : Nat) :=
    (last - cut) * rankAtEvent rank (source.event cut)
  have outside (cut : Nat) (valid : cut < last) (first : cut ≠ time) (second : cut ≠ time + 1) :
      contribution moved cut = contribution trace cut := by
    simp [contribution, events cut valid, first, second]
  have front : (List.range time).map (contribution moved) = (List.range time).map (contribution trace) := by
    apply List.map_congr_left
    intro cut member
    have earlier := List.mem_range.mp member
    exact outside cut (by omega) (by omega) (by omega)
  have suffix : (List.range' (time + 2) (last - (time + 2))).map (contribution moved) =
      (List.range' (time + 2) (last - (time + 2))).map (contribution trace) := by
    apply List.map_congr_left
    intro cut member
    obtain ⟨offset, small, placed⟩ := List.mem_range'.mp member
    simp at placed
    exact outside cut (by omega) (by omega) (by omega)
  have movedEarlier : moved.event time = .lifecycle secondKind second := by
    simp [events time (by omega), secondEvent]
  have movedLater : moved.event (time + 1) = .lifecycle firstKind first := by
    simp [events (time + 1) bounded, firstEvent]
  change ((List.range last).map (contribution moved)).sum < ((List.range last).map (contribution trace)).sum
  rw [cut_range_pair bounded]
  simp only [List.map_append, List.sum_append_nat, List.map_cons, List.sum_cons, front, suffix]
  simp only [contribution, firstEvent, secondEvent, movedEarlier, movedLater, rankAtEvent,
    show last - time = (last - (time + 1)) + 1 by omega, Nat.add_mul, Nat.one_mul]
  omega

section Typed
variable {V : Key → Type u} {ops : CoeffectOperations V}
variable {typedProgram : Code → TypedRegistry.Instruction Name ops Code}
local notation "A" => Scalar ops
local notation "Source" => Trace (encodeProgram typedProgram) last

private theorem Trace.order_activation_runs_by (trace : Source) (rank : Name → Nat)
    (chronological : ChronologicalOpenings trace rank)
    (openOnly : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r) :
    letI : Setoid A := TypedCoeffectReplay.setoid observe
    ∃ moved : Source, OrderedActivationRuns moved rank ∧ ChronologicalOpenings moved rank ∧
      (∀ cut, cut < last → ∀ command : OrchestrationSorting.Command Name Key Code,
        moved.event cut = .command command ↔ trace.event cut = .command command) ∧
      originalRoots moved = originalRoots trace ∧ StageSimulation.Related Eq (trace.state last) (moved.state last) ∧
      (¬ Nonempty (ClosedEpisode moved)) ∧ Progress.Quiet (moved.state last) := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  classical
  generalize measured : activationCost trace rank = cost
  induction cost using Nat.strongRecOn generalizing trace with
  | ind cost ih =>
    by_cases available : ∃ (time : Nat) (firstKind secondKind : Lifecycle) (first second : Name),
        time + 1 < last ∧ trace.event time = .lifecycle firstKind first ∧
        trace.event (time + 1) = .lifecycle secondKind second ∧ rank second < rank first
    · obtain ⟨time, firstKind, secondKind, first, second, bounded, firstEvent, secondEvent, inverted⟩ := available
      have different : first ≠ second := by
        intro same
        exact Nat.lt_irrefl _ (same ▸ inverted)
      have notBegin : secondKind ≠ .begin := by
        intro same
        subst secondKind
        obtain ⟨opens, earlier, firstOpened⟩ := trace.opening_of_activation openOnly quiet (by omega) firstEvent
        have ranked := chronological (by omega : opens < time + 1) bounded firstOpened secondEvent
        omega
      obtain ⟨moved, _, labels, _, suffix, _, roots, stillOpen, stillQuiet⟩ :=
        trace.swap_activations openOnly quiet bounded firstEvent secondEvent different
          (fun impossible => False.elim (notBegin impossible)) observe recovery commutative respect
      have endpoint := (suffix last (by omega) (Nat.le_refl _)).1
      have movedChronological : ChronologicalOpenings moved rank :=
        chronological.swap (fun _ impossible => notBegin (Event.lifecycle.inj (secondEvent.symm.trans impossible)).1)
          labels
      have smaller := activationCost_decreases bounded firstEvent secondEvent inverted labels
      rw [measured] at smaller
      obtain ⟨result, sorted, ordered, resultCommands, resultRoots, resultEndpoint, finalOpen, finalQuiet⟩ :=
        ih _ smaller moved movedChronological stillOpen stillQuiet rfl
      refine ⟨result, sorted, ordered, ?_, resultRoots.trans roots,
        StageSimulation.Related.trans (Q := Eq) (fun a b => a.trans b) endpoint resultEndpoint, finalOpen, finalQuiet⟩
      intro cut valid command
      rw [resultCommands _ valid, labels _ valid]
      by_cases firstCut : cut = time
      · subst cut
        simp [firstEvent, secondEvent]
      by_cases secondCut : cut = time + 1
      · subst cut
        simp [firstEvent, secondEvent]
      · simp [firstCut, secondCut]
    · refine ⟨trace, ?_, chronological, fun _ _ _ => Iff.rfl, rfl, ?_, openOnly, quiet⟩
      · intro time firstKind secondKind first second bounded firstEvent secondEvent
        exact Nat.le_of_not_gt (fun inverted =>
          available ⟨time, firstKind, secondKind, first, second, bounded, firstEvent, secondEvent, inverted⟩)
      · exact trace.self_related last (Nat.le_refl _)
          (TypedRegistry.encoded_program_callbacks ops observe typedProgram recovery commutative)

/-- Order every consecutive run of open activations by the chronological
opening rank. Only different actors' landings move earlier, so every swap
uses guards derived from the actual installed view. -/
theorem Trace.order_activation_runs (trace : Source)
    (openOnly : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r) :
    letI : Setoid A := TypedCoeffectReplay.setoid observe
    let rank := openingRanks trace last
    ∃ moved : Source, OrderedActivationRuns moved rank ∧ ChronologicalOpenings moved rank ∧
      (∀ cut, cut < last → ∀ command : OrchestrationSorting.Command Name Key Code,
        moved.event cut = .command command ↔ trace.event cut = .command command) ∧
      originalRoots moved = originalRoots trace ∧ StageSimulation.Related Eq (trace.state last) (moved.state last) ∧
      (¬ Nonempty (ClosedEpisode moved)) ∧ Progress.Quiet (moved.state last) :=
  trace.order_activation_runs_by _ (trace.chronological_openings openOnly) openOnly quiet
    observe recovery commutative respect

end Typed
end Cordis.Repairs.GuardedHistory
