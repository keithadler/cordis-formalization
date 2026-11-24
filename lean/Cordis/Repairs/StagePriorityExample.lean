import Cordis.Repairs.GuardedCanonicalOrder
import Cordis.Repairs.GuardedCanonicalSchedule
import Cordis.Repairs.GuardedBirthAddresses
import Cordis.Repairs.GuardedScheduleMatching
import Cordis.Repairs.GuardedActivationAlignment
import Cordis.Repairs.GuardedNameExtension

/-! An independent root can execute on either side of a provider and its
consumer. Both schedules are locally ordered by the same root priorities. -/
namespace Cordis.Repairs.StagePriorityExample
open Calculus Stages LegalHistory GuardedHistory GuardedBirthAddresses
open GuardedScheduleMatching (OpenEventsAgree)
open OrchestrationSorting (Command)
open Vestigial (cutNotes eventActor)

abbrev Name := Fin 3
abbrev Values : Unit → Type := fun _ => Nat

def operations : PaperEffectEquations.CoeffectOperations Values where
  Name _ := Empty
  Argument _ action := nomatch action
  Outcome _ action := nomatch action
  operation _ action := nomatch action

abbrev R := TypedRegistry.RawRegistry Name operations Bool
abbrev F := TypedRegistry.RawFiber Name operations Bool
abbrev Ev := Event Name Unit Bool

def component (name : Name) : Component Unit Bool :=
  ⟨fun _ => name == 0, fun _ => name == 2, name == 2⟩

def entry : Bool → TypedRegistry.Instruction Name operations Bool
  | false => ⟨.unit, fun _ => none⟩
  | true => ⟨.provide () 7, fun _ => none⟩

abbrev program := TypedRegistry.encodeProgram entry

def view : View Name Unit := fun _ => 2
def value : TypedRegistry.Scalar operations := TypedCoeffectReplay.pack () 7
def loading (name : Name) : Phase Name Unit Bool (Inverse Name Unit (TypedRegistry.Scalar operations)) :=
  .reloading (component name).entry [] view

def active (name : Name) : Phase Name Unit Bool (Inverse Name Unit (TypedRegistry.Scalar operations)) :=
  .active (if name = 2 then [.restrict name ()] else [.unit]) view

def events (early : Bool) : Nat → Ev
  | 0 => .command (.insert 0 (component 0))
  | 1 => .command (.insert 1 (component 1))
  | 2 => .command (.insert 2 (component 2))
  | 3 => .lifecycle .begin (if early then 1 else 2)
  | 4 => if early then .lifecycle .begin 2 else .lifecycle .finish 2
  | 5 => if early then .lifecycle .finish 2 else .lifecycle .begin 0
  | 6 => if early then .lifecycle .begin 0 else .lifecycle .finish 0
  | 7 => if early then .lifecycle .finish 0 else .lifecycle .begin 1
  | _ => .lifecycle .finish 1

private def applyEvent (source : R) : Ev → R
  | .command command => command.apply source
  | .lifecycle .begin name => mark source name (loading name)
  | .lifecycle .finish name =>
    mark (if name = 2 then write source name () (some value) else source) name (active name)
  | _ => source

def states (early : Bool) : Nat → R
  | 0 => fun _ => none
  | cut + 1 => applyEvent (states early cut) (events early cut)

private theorem names (name : Name) : name = 0 ∨ name = 1 ∨ name = 2 := by
  have within := name.isLt
  have values : name.val = 0 ∨ name.val = 1 ∨ name.val = 2 := by omega
  rcases values with first | second | third
  · exact .inl (Fin.ext first)
  · exact .inr (.inl (Fin.ext second))
  · exact .inr (.inr (Fin.ext third))

private theorem no_parent (name : Name) : (none : Option Name) = some name → False := Option.noConfusion

private theorem first_insertion (early : Bool) : Insertable (states early 0) 0 (component 0) none :=
  ⟨rfl, fun name absent => False.elim (no_parent name absent), fun _ _ => trivial⟩

private theorem second_insertion (early : Bool) : Insertable (states early 1) 1 (component 1) none := by
  refine ⟨rfl, fun name absent => False.elim (no_parent name absent), ?_⟩
  intro name key
  rcases names name with rfl | rfl | rfl
  · exact fun impossible => Bool.noConfusion impossible
  · trivial
  · trivial

private theorem third_insertion (early : Bool) : Insertable (states early 2) 2 (component 2) none := by
  refine ⟨rfl, fun name absent => False.elim (no_parent name absent), ?_⟩
  intro name key
  rcases names name with rfl | rfl | rfl
  · exact fun _ impossible => Bool.noConfusion impossible
  · exact fun _ impossible => Bool.noConfusion impossible
  · trivial

private theorem independent_target {r : R} {name : Name} {row : F}
    (found : r name = some row) (unretired : row.retired = false)
    (requires : row.component.requires () = false) : Target r name view := by
  rw [Target, found]
  refine ⟨unretired, ?_⟩
  intro key needed
  cases key
  exact False.elim (Bool.noConfusion (requires.symm.trans needed))

private theorem consumer_target {r : R} {row provider : F}
    (found : r 0 = some row) (unretired : row.retired = false) (source : r 2 = some provider)
    (available : provider.phase.available) (bound : provider.table () ≠ none) : Target r 0 view := by
  rw [Target, found]
  refine ⟨unretired, ?_⟩
  intro key _
  cases key
  simpa only [view, source] using And.intro available bound

private theorem start_step {early : Bool} {cut : Nat} {name : Name} {row : F}
    (event : events early cut = .lifecycle .begin name)
    (found : states early cut name = some row) (inactive : row.phase = .inactive)
    (entryCode : row.component.entry = (component name).entry) (target : Target (states early cut) name view) :
    GuardedSuffix.Transition program (cutNotes (states early) (fun i => eventActor (events early i)) cut)
      (events early cut) (states early cut) (states early (cut + 1)) := by
  have endpoint : states early (cut + 1) = mark (states early cut) name (loading name) := by
    rw [states, event]
    rfl
  rw [event, endpoint]
  change Labeled.Step program .begin name (states early cut) _
  unfold loading
  rw [← entryCode]
  exact .begin _ _ _ view found inactive (by unfold ErrorFree; rw [found]; exact Option.noConfusion) target

private theorem finish_unit {early : Bool} {cut : Nat} {name : Name} {row : F}
    (event : events early cut = .lifecycle .finish name) (notProvider : name ≠ 2)
    (found : states early cut name = some row) (reloading : row.phase = .reloading false [] view)
    (target : Target (states early cut) name view) :
    GuardedSuffix.Transition program (cutNotes (states early) (fun i => eventActor (events early i)) cut)
      (events early cut) (states early cut) (states early (cut + 1)) := by
  have endpoint : states early (cut + 1) = mark (states early cut) name (.active [.unit] view) := by
    rw [states, event]
    simp [applyEvent, active, notProvider]
  rw [event, endpoint]
  exact Labeled.Step.finish _ _ _ row false [] view .unit found reloading target (.unit _ _ _ rfl)

private theorem finish_provider {early : Bool} {cut : Nat} {row : F}
    (event : events early cut = .lifecycle .finish 2)
    (found : states early cut 2 = some row) (reloading : row.phase = .reloading true [] view)
    (declared : row.component.provides () = true) (vacant : row.table () = none)
    (target : Target (states early cut) 2 view) :
    GuardedSuffix.Transition program (cutNotes (states early) (fun i => eventActor (events early i)) cut)
      (events early cut) (states early cut) (states early (cut + 1)) := by
  have endpoint : states early (cut + 1) =
      mark (write (states early cut) 2 () (some value)) 2 (.active [.restrict 2 ()] view) := by
    rw [states, event]
    rfl
  rw [event, endpoint]
  exact Labeled.Step.finish _ _ _ row true [] view (.restrict 2 ()) found reloading target
    (.provide _ _ _ row () value rfl found declared vacant)

def trace (early : Bool) : Trace program 9 where
  state := states early
  notes := cutNotes (states early) (fun cut => eventActor (events early cut))
  event := events early
  start := rfl
  seed := rfl
  step cut bounded := by
    refine ⟨?_, rfl⟩
    have casesCut : cut = 0 ∨ cut = 1 ∨ cut = 2 ∨ cut = 3 ∨ cut = 4 ∨
        cut = 5 ∨ cut = 6 ∨ cut = 7 ∨ cut = 8 := by omega
    rcases casesCut with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨first_insertion early, rfl⟩
    · exact ⟨second_insertion early, rfl⟩
    · exact ⟨third_insertion early, rfl⟩
    all_goals cases early
    all_goals first
      | exact start_step rfl rfl rfl rfl (independent_target rfl rfl rfl)
      | exact finish_provider rfl rfl rfl rfl rfl (independent_target rfl rfl rfl)
      | exact start_step rfl rfl rfl rfl (consumer_target rfl rfl rfl trivial Option.noConfusion)
      | exact finish_unit rfl (by decide) rfl rfl (consumer_target rfl rfl rfl trivial Option.noConfusion)
      | exact finish_unit rfl (by decide) rfl rfl (independent_target rfl rfl rfl)

/-- The three root insertions give priorities one, two, and three to the
consumer, the independent root, and the provider respectively. -/
def priority (early : Bool) (stamp : Nat) : Nat :=
  match (trace early).event (stamp - 1) with
  | .command _ => 0
  | .lifecycle _ actor => actor.val + 1

private theorem consumer_blocked (early : Bool) :
    ¬ ∃ selected, Target ((trace early).state (if early then 5 else 4)) 0 selected := by
  rintro ⟨selected, target⟩
  have found : (trace early).state (if early then 5 else 4) 0 = some (fresh (component 0) none) := by
    cases early <;> rfl
  rw [Target, found] at target
  have supply := target.2 () rfl
  rcases names (selected ()) with consumer | independent | provider
  · rw [consumer] at supply
    cases early <;> exact supply.1
  · rw [independent] at supply
    cases early <;> exact supply.1
  · rw [provider] at supply
    cases early <;> exact supply.1

/-- All priority inversions in these two histories put the provider's
Finish immediately before the consumer's Begin. That pair cannot reverse. -/
theorem locally_ordered (early : Bool) (cut : Nat) (bounded : cut + 1 < 9)
    (exchange : StageExchange (trace early) cut) : priority early (cut + 1) ≤ priority early (cut + 2) := by
  apply Nat.le_of_not_gt
  intro inverted
  have cuts : cut = 0 ∨ cut = 1 ∨ cut = 2 ∨ cut = 3 ∨ cut = 4 ∨
      cut = 5 ∨ cut = 6 ∨ cut = 7 := by omega
  have only : cut = if early then 5 else 4 := by
    cases early <;> rcases cuts with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | rfl | exact False.elim ((by decide : ¬ (_ < _)) inverted)
  have earlier : (trace early).event cut = .lifecycle .finish 2 := by
    rw [only]
    cases early <;> rfl
  have later : (trace early).event (cut + 1) = .lifecycle .begin 0 := by
    rw [only]
    cases early <;> rfl
  have blocked : ¬ ∃ selected, Target ((trace early).state cut) 0 selected := only.symm ▸ consumer_blocked early
  cases exchange with
  | rootPastActivation _ command _ => rw [later] at command; cases command
  | rootPastChild command _ _ _ _ => rw [earlier] at command; cases command
  | activationPastChild command _ _ _ => rw [earlier] at command; cases command
  | activationPastActivation _ next _ available =>
    rw [later] at next
    cases next
    exact blocked (available rfl)

theorem quiet (early : Bool) : Progress.Quiet ((trace early).state 9) := by
  intro name row found
  cases early <;> rcases names name with rfl | rfl | rfl
  all_goals
    change some _ = some row at found
    cases Option.some.inj found
    first
    | exact consumer_target rfl rfl rfl trivial Option.noConfusion
    | exact independent_target rfl rfl rfl

theorem open_only (early : Bool) : ¬ Nonempty (ClosedEpisode (trace early)) := by
  rintro ⟨episode⟩
  obtain ⟨unload, _⟩ := unload_boundary (trace early) episode.interval
  have bound := episode.interval.bounded
  have cuts : episode.closed = 0 ∨ episode.closed = 1 ∨ episode.closed = 2 ∨ episode.closed = 3 ∨
      episode.closed = 4 ∨ episode.closed = 5 ∨ episode.closed = 6 ∨ episode.closed = 7 ∨ episode.closed = 8 := by omega
  change events early episode.closed = .lifecycle .unload episode.name at unload
  cases early <;> rcases cuts with cut | cut | cut | cut | cut | cut | cut | cut | cut <;>
    simp [cut, events] at unload

private def totalAt (state : R) (name : Name) : Bool :=
  match state name with
  | none => true
  | some row =>
    match row.phase with
    | .active .. => (row.table ()).isSome == row.component.provides ()
    | _ => true

theorem total_at_every_cut (early : Bool) (cut : Nat) (bounded : cut ≤ 9) :
    SupportAtQuiescence.TotalProvision ((trace early).state cut) := by
  intro name row found available key
  cases key
  have certified : (List.range 10).all (fun i => ([0, 1, 2] : List Name).all (totalAt (states early i))) = true := by
    cases early <;> decide
  have member : name ∈ ([0, 1, 2] : List Name) := by rcases names name with rfl | rfl | rfl <;> decide
  have proof := List.all_eq_true.mp (List.all_eq_true.mp certified cut (List.mem_range.mpr (by omega))) name member
  change states early cut name = some row at found
  unfold totalAt at proof
  rw [found] at proof
  cases phase : row.phase <;> simp_all [Phase.available]
  cases bound : row.table () <;> cases declared : row.component.provides () <;> simp_all

def observe (_ : Unit) : Setoid Nat := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩

/-- The locally ordered schedule can still legally exchange the openings
of the independent root and the provider. Their swap raises priority at
the earlier cut, so priority reduction alone never takes it. -/
theorem exchange_independent_openings :
    ∃ moved : Trace program 9, moved.event 3 = .lifecycle .begin 2 ∧ moved.event 4 = .lifecycle .begin 1 ∧
      RetainedEvents (trace true) moved (ExchangeReplay.exchangedIndex 3) ∧ originalRoots moved = originalRoots (trace true) := by
  have available : ∃ selected, Target ((trace true).state 3) 2 selected :=
    ⟨view, independent_target rfl rfl rfl⟩
  obtain ⟨moved, _, labels, _, _, retained, roots, _, _⟩ :=
    (trace true).swap_activations (open_only true) (quiet true) (time := 3) (by decide)
      (firstKind := .begin) (secondKind := .begin) (first := 1) (second := 2) rfl rfl (by decide)
      (fun _ => available) observe (fun _ action => nomatch action) (fun _ action => nomatch action)
      (fun _ action => nomatch action)
  exact ⟨moved, labels 3 (by decide), labels 4 (by decide), retained, roots⟩

/-- Even with the same addressed orchestration input and fixed root
priorities, two legal local normal forms can have different schedules. -/
theorem different_local_orders :
    orchestrationInput (trace true) = orchestrationInput (trace false) ∧
    (∀ early cut, cut + 1 < 9 → StageExchange (trace early) cut →
      priority early (cut + 1) ≤ priority early (cut + 2)) ∧
    (∀ early, Progress.Quiet ((trace early).state 9) ∧ ¬ Nonempty (ClosedEpisode (trace early))) ∧
    (∀ early cut, cut ≤ 9 → SupportAtQuiescence.TotalProvision ((trace early).state cut)) ∧
    scheduledEvents (trace true) ≠ scheduledEvents (trace false) ∧
    ¬ OpenEventsAgree (trace true) (trace false) 3 ∧
    (trace true).state 9 = (trace false).state 9 ∧
    StageRecovery.tableAt ((trace true).state 9) 2 () = some value := by
  refine ⟨rfl, locally_ordered, fun early => ⟨quiet early, open_only early⟩, total_at_every_cut, ?_, ?_, ?_, rfl⟩
  · intro identical
    have opening := congrArg (fun list : List Ev => list[3]?) identical
    cases opening
  · intro matching
    have births : (some 2 : Option Nat) = some 3 := matching.2.2
    cases births
  · funext name
    rcases names name with rfl | rfl | rfl <;> rfl

/-- The two different local orders have an actual common addressed schedule.
Aligning the first opening moves it across four provider and consumer events. -/
theorem align_independent_schedules :
    letI : Setoid (TypedRegistry.Scalar operations) := TypedCoeffectReplay.setoid observe
    ∃ (moved : Trace program 9) (expand : Nat → Nat),
      GuardedActivationAlignment.ActivationExchangePath (trace false) moved expand ∧
      (∀ cut, cut < 9 → GuardedAddressSchedule.addressedEventAt (trace true) cut =
        GuardedAddressSchedule.addressedEventAt moved cut) ∧
      GuardedScheduleMatching.CutAgreement (trace true) moved 9 ∧
      orchestrationInput moved = orchestrationInput (trace false) ∧
      StageSimulation.Related Eq ((trace false).state 9) (moved.state 9) := by
  have prefixAgreement : ∀ cut, cut < 3 → OpenEventsAgree (trace true) (trace false) cut := by
    intro cut within
    have possible : cut = 0 ∨ cut = 1 ∨ cut = 2 := by omega
    rcases possible with rfl | rfl | rfl <;> rfl
  have prefixAddress : ∀ cut, cut < 3 → GuardedAddressSchedule.addressedEventAt (trace true) cut =
      GuardedAddressSchedule.addressedEventAt (trace false) cut := by
    intro cut within
    have possible : cut = 0 ∨ cut = 1 ∨ cut = 2 := by omega
    rcases possible with rfl | rfl | rfl <;> rfl
  have stable : GuardedLandingMatching.ChildContinuations program := by
    intro code _ _ _ _
    cases code <;> rfl
  have atCut := GuardedScheduleMatching.match_open_prefix (trace true) (trace false) stable 3
    (by decide) (by decide) prefixAgreement
  have commandFree (cut : Nat) (later : 3 ≤ cut) (inside : cut < 9) :
      ∃ kind actor, (trace true).event cut = .lifecycle kind actor := by
    have possible : cut = 3 ∨ cut = 4 ∨ cut = 5 ∨ cut = 6 ∨ cut = 7 ∨ cut = 8 := by omega
    rcases possible with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, _, rfl⟩
  obtain ⟨moved, expand, _, _, ordered, matched, input, endpoint, _, _, path⟩ :=
    GuardedActivationAlignment.align_command_free_suffix (trace true) (trace false) (by decide) (by decide)
      (open_only true) (quiet true) (open_only false) (quiet false) atCut stable prefixAddress rfl commandFree
      observe (fun _ action => nomatch action) (fun _ action => nomatch action) (fun _ action => nomatch action)
  exact ⟨moved, expand, path, ordered, matched, input, endpoint⟩

/-- All three original names are occupied. The endpoint theorem still
compares the two actual histories in the original name set. -/
theorem confluence_with_all_names_occupied :
    letI : Setoid (TypedRegistry.Scalar operations) := TypedCoeffectReplay.setoid observe
    (∀ name, (trace true).state 9 name ≠ none ∧ (trace false).state 9 name ≠ none) ∧
      GuardedCutState.ProjectedAgreement ((trace true).state 9) ((trace false).state 9) := by
  have stable : GuardedLandingMatching.ChildContinuations program := by
    intro code _ _ _ _
    cases code <;> rfl
  have compared := (GuardedNameExtension.compare_open_endpoints (trace true) (trace false)
    (open_only true) (quiet true) (open_only false) (quiet false) stable rfl observe
    (fun _ action => nomatch action) (fun _ action => nomatch action) (fun _ action => nomatch action)).2.1
  refine ⟨?_, compared⟩
  intro name
  rcases names name with rfl | rfl | rfl <;>
    constructor <;> intro absent <;> cases absent

/-- From a local optimum on the three occupied names, move the independent
Begin before the provider. The first exchange crosses the consumer's
Finish and raises priority; the complete path gives a smaller word. -/
theorem better_order_from_local_optimum :
    letI : Setoid (TypedRegistry.Scalar operations) := TypedCoeffectReplay.setoid observe
    ∃ moved : Trace program 9, ∃ expand : Nat → Nat,
      ExchangePath (trace false) moved expand ∧ moved.event 3 = .lifecycle .begin 1 ∧
      exchangePriorityWord 9 (priority false) expand < exchangePriorityWord 9 (priority false) id := by
  letI : Setoid (TypedRegistry.Scalar operations) := TypedCoeffectReplay.setoid observe
  have self := (trace false).self_related 9 (Nat.le_refl _)
    (TypedRegistry.encoded_program_callbacks operations observe entry
      (fun _ action => nomatch action) (fun _ action => nomatch action))
  have earlierStages (cut : Nat) (lower : 3 ≤ cut) (upper : cut ≤ 6) :
      (∃ kind actor, (trace false).event cut = .lifecycle kind actor ∧ actor ≠ 1) ∧
      Target ((trace false).state cut) 1 view := by
    have atCut : cut = 3 ∨ cut = 4 ∨ cut = 5 ∨ cut = 6 := by omega
    rcases atCut with rfl | rfl | rfl | rfl
    all_goals exact ⟨⟨_, _, rfl, by decide⟩, independent_target rfl rfl rfl⟩
  have pull (steps : Nat) (bounded : steps ≤ 4) :
      ∃ (moved : Trace program 9) (expand : Nat → Nat),
        ExchangePath (trace false) moved expand ∧
        (∀ cut, cut ≤ 7 - steps → moved.state cut = (trace false).state cut) ∧
        (∀ stamp, stamp ≤ 7 - steps → expand stamp = stamp) ∧
        expand (7 - steps + 1) = 8 ∧ moved.event (7 - steps) = .lifecycle .begin 1 := by
    induction steps with
    | zero => exact ⟨trace false, id, .refl, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩
    | succ steps ih =>
      obtain ⟨before, stamp, path, states, initialStamps, atOpening, opening⟩ := ih (by omega)
      obtain ⟨stable, _, _, opened, settled⟩ := path.preserves self (open_only false) (quiet false)
      let point := 7 - (steps + 1)
      have location : point + 1 = 7 - steps := by dsimp [point]; omega
      have boundedPair : point + 1 < 9 := by omega
      obtain ⟨⟨kind, actor, first, different⟩, target⟩ := earlierStages point (by dsimp [point]; omega) (by omega)
      have earlier : before.event point = .lifecycle kind actor := by
        rw [stable.retained.label point (by omega), initialStamps _ (by omega), Nat.add_sub_cancel, first]
      have exchange : StageExchange before point := .activationPastActivation earlier (location.symm ▸ opening)
        different (fun _ => ⟨view, (states point (by omega)).symm ▸ target⟩)
      obtain ⟨moved, layout, classified, roots, endpoint, movedOpen, movedQuiet, kept, prefixState⟩ :=
        exchange.perform before boundedPair opened settled observe
          (fun _ action => nomatch action) (fun _ action => nomatch action) (fun _ action => nomatch action)
      refine ⟨moved, stamp ∘ ExchangeReplay.exchangedIndex point,
        path.swap boundedPair exchange (exchange.stable_addresses boundedPair kept) classified roots endpoint movedOpen movedQuiet,
        fun cut earlier => (prefixState cut earlier).trans (states cut (by omega)), ?_, ?_, ?_⟩
      · intro index earlier
        rw [Function.comp_apply, ExchangeReplay.exchangedIndex_other (by omega) (by omega), initialStamps _ (by omega)]
      · rw [Function.comp_apply, ExchangeReplay.exchangedIndex_first, show point + 2 = (7 - steps) + 1 by omega, atOpening]
      · rw [layout point (by omega), ExchangeReplay.exchangedCut, if_pos rfl, location]
        exact opening
  obtain ⟨moved, expand, path, _, stamps, placed, event⟩ := pull 4 (by decide)
  refine ⟨moved, expand, path, event, exchangePriorityWord_lt_at (point := 3) (by decide) ?_ ?_ ?_⟩
  · intro cut earlier
    exact stamps _ (by omega)
  · rw [placed]
    decide
  · rw [placed]
    decide

/-- Both locally distinct histories admit the same canonical addressed
order over Fin 3, with all names still occupied at the new endpoints. -/
theorem common_canonical_order_with_all_names_occupied :
    letI : Setoid (TypedRegistry.Scalar operations) := TypedCoeffectReplay.setoid observe
    ∃ first second : Trace program 9,
      GuardedCanonicalSchedule.Canonical (orchestrationInput (trace true)) first ∧
      GuardedCanonicalSchedule.Canonical (orchestrationInput (trace true)) second ∧
      GuardedCompleteAlignment.ScheduleAlignmentPath (trace true) first ∧
      GuardedCompleteAlignment.ScheduleAlignmentPath (trace false) second ∧
      (∀ cut, cut < 9 → GuardedAddressSchedule.addressedEventAt first cut = GuardedAddressSchedule.addressedEventAt second cut) ∧
      (∀ name, first.state 9 name ≠ none ∧ second.state 9 name ≠ none) := by
  letI : Setoid (TypedRegistry.Scalar operations) := TypedCoeffectReplay.setoid observe
  have stable : GuardedLandingMatching.ChildContinuations program := by
    intro code _ _ _ _
    cases code <;> rfl
  obtain ⟨first, firstForm, firstPath⟩ := GuardedCanonicalSchedule.canonical_path_in_original_names
    (trace true) (open_only true) (quiet true) stable observe
    (fun _ action => nomatch action) (fun _ action => nomatch action) (fun _ action => nomatch action)
  obtain ⟨second, secondForm, secondPath⟩ := GuardedCanonicalSchedule.canonical_path_in_original_names
    (trace false) (open_only false) (quiet false) stable observe
    (fun _ action => nomatch action) (fun _ action => nomatch action) (fun _ action => nomatch action)
  have input : orchestrationInput (trace true) = orchestrationInput (trace false) := different_local_orders.1
  have secondForm' : GuardedCanonicalSchedule.Canonical (orchestrationInput (trace true)) second := input.symm ▸ secondForm
  have full (early : Bool) (result : Trace program 9)
      (path : GuardedCompleteAlignment.ScheduleAlignmentPath (trace early) result)
      (name : Name) : result.state 9 name ≠ none := by
    obtain ⟨⟨perm, compared⟩, _⟩ := path.preserves
    obtain ⟨oldName, rfl⟩ := perm.surjective name
    have occupied : (trace early).state 9 oldName ≠ none := by
      cases early
      · exact (confluence_with_all_names_occupied.1 oldName).2
      · exact (confluence_with_all_names_occupied.1 oldName).1
    intro vacant
    have here := compared (perm.toFun oldName)
    rw [Renaming.registry_at, (GuardedCutState.project_present (result.state 9) (perm.toFun oldName)).mpr vacant] at here
    cases found : GuardedCutState.project ((trace early).state 9) oldName with
    | none => exact occupied ((GuardedCutState.project_present ((trace early).state 9) oldName).mp found)
    | some row => simp [found, Iterators.OptionRel] at here
  exact ⟨first, second, firstForm, secondForm', firstPath, secondPath, firstForm.unique_order secondForm',
    fun name => ⟨full true first firstPath name, full false second secondPath name⟩⟩

end Cordis.Repairs.StagePriorityExample
