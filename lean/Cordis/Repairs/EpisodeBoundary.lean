import Cordis.Repairs.EpisodeSelection
import Cordis.Repairs.EpisodeDependencies

/-! The capture produced by a child birth survives to the closing unload of
the creating episode. Retirement at that boundary follows from the native
word and from the birth-checked word for the same live incarnation. -/
namespace Cordis.Repairs.EpisodeBoundary
open Calculus Stages Indexed EpisodeDependencies Incarnation IncarnationReplay
open PartialReplayRegistry (saved)
universe u
variable {Name Key Value Code Error : Type u} [DecidableEq Name] [DecidableEq Key]
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
local notation "C" => Capture Name Key Value
local notation "Program" => Code → Instruction Name Key Value Code Error
variable {program : Code → Instruction Name Key Value Code Error} {last : Nat}
local notation "History" => Trace program (fun _ => none : R) last

/-- A birth on Iter, Finish, or Divert puts a stamp on the creator's
actual stack. Every remaining step in its installed interval keeps it. -/
theorem birth_capture_at_cut (trace : History) (episode : ClosedEpisode trace)
    {birthStep time : Nat} {child : Name}
    (lower : episode.opened ≤ birthStep) (earlier : birthStep < time) (upper : time ≤ episode.closed)
    (creator : trace.actor birthStep = episode.name)
    (birthRule : EpisodeSelection.canBirth (trace.rule birthStep) = true)
    (vacant : trace.state birthStep child = none) (born : trace.state (birthStep + 1) child ≠ none) :
    (⟨.retire child, birthStep + 1⟩ : C) ∈ track trace.state trace.actor time episode.name := by
  have bound := episode.interval.bounded
  have step := trace.step birthStep (by omega)
  have pushed := (EpisodeSelection.actual_child_birth step birthRule vacant born).2
  have recorded : (⟨.retire child, birthStep + 1⟩ : C) ∈
      track trace.state trace.actor (birthStep + 1) episode.name := by
    change _ ∈ advance (trace.state birthStep) (trace.state (birthStep + 1)) (trace.actor birthStep)
      (birthStep + 1) (track trace.state trace.actor birthStep) episode.name
    rw [advance_capture _ _ _ _ pushed]
    simp [creator]
  exact capture_through_interval trace episode.name (by omega) (by omega)
    (fun point afterBirth beforeCut => episode.interval.installed point (by omega) (by omega)) recorded

theorem birth_capture_at_closure (trace : History) (episode : ClosedEpisode trace)
    {birthStep : Nat} {child : Name}
    (lower : episode.opened ≤ birthStep) (upper : birthStep < episode.closed)
    (creator : trace.actor birthStep = episode.name)
    (birthRule : EpisodeSelection.canBirth (trace.rule birthStep) = true)
    (vacant : trace.state birthStep child = none) (born : trace.state (birthStep + 1) child ≠ none) :
    (⟨.retire child, birthStep + 1⟩ : C) ∈ track trace.state trace.actor episode.closed episode.name :=
  birth_capture_at_cut trace episode lower upper (Nat.le_refl _) creator birthRule vacant born

/-- The exact child born in this episode is retired by either discharge at
its closing boundary if it still lives there. Older or intervening uses of
the same name play no role in the proof of the corrected retirement. -/
theorem child_retired_at_closure (trace : History) (episode : ClosedEpisode trace)
    {birthStep : Nat} {child : Name}
    (lower : episode.opened ≤ birthStep) (upper : birthStep < episode.closed)
    (creator : trace.actor birthStep = episode.name)
    (birthRule : EpisodeSelection.canBirth (trace.rule birthStep) = true)
    (lives : Residency trace.state child (birthStep + 1) episode.closed) :
    let word := track trace.state trace.actor episode.closed episode.name
    let corrected := mark (replayAt trace.state episode.closed word) episode.name .inactive
    (trace.state (episode.closed + 1) child).map Fiber.retired = some true ∧
      (corrected child).map Fiber.retired = some true := by
  dsimp only
  have vacant : trace.state birthStep child = none := by
    simpa using lives.boundary.resolve_left (by omega)
  have born := lives.present (birthStep + 1) (Nat.le_refl _) lives.ordered
  have still := lives.present episode.closed lives.ordered (Nat.le_refl _)
  have recorded := birth_capture_at_closure trace episode lower upper creator birthRule vacant born
  have installed := episode.interval.installed birthStep lower (by omega)
  have distinct : child ≠ episode.name := by
    intro same
    have empty : trace.state birthStep episode.name = none := same ▸ vacant
    exact installed (by simp [ControlFrame.viewAt, empty])
  have currentBirth := birthAt_eq_some.mpr lives
  obtain ⟨parent, raw, view, parentAt, unloading, _, after⟩ := unload_boundary trace episode.interval
  have stacks := tracked_stack trace episode.closed (by have := episode.interval.bounded; omega)
  have rawMember : (.retire child : Inverse Name Key Value) ∈ raw := by
    have carries := List.mem_map_of_mem (f := Capture.token) recorded
    rw [stacks.projects] at carries
    simpa [saved, parentAt, unloading, Phase.accumulator] using carries
  cases childAt : trace.state episode.closed child with
  | none => exact False.elim (still childAt)
  | some before =>
    obtain ⟨row, discharged, _⟩ := Ordering.discharge_existing_phases _ raw child before childAt
    have retired := ChildProvenance.discharge_retires_member _ raw child before row childAt discharged rawMember
    constructor
    · rw [after, Transposition.mark_other _ _ _ _ distinct, discharged]
      exact congrArg some retired
    · rw [Transposition.mark_other _ _ _ _ distinct, replayAt, replay_retired, childAt]
      have matchesAny : (track trace.state trace.actor episode.closed episode.name).any
          (Capture.retires (fun name => birthAt trace.state name episode.closed) child) = true := by
        apply List.any_eq_true.mpr
        exact ⟨_, recorded, by simp [Capture.retires, currentBirth]⟩
      simp [matchesAny]

omit [DecidableEq Name] [DecidableEq Key] in
theorem prefix_since_absence (states : Nat → R) (name : Name) {first time : Nat}
    (lower : first ≤ time) (bounded : time ≤ last)
    (absent : ControlFrame.viewAt (states first) name = none)
    (installed : ControlFrame.viewAt (states time) name ≠ none) :
    ∃ opened, first < opened ∧ EpisodePrefixOn states last name opened time := by
  induction time with
  | zero =>
    have same : first = 0 := by omega
    exact False.elim (installed (same ▸ absent))
  | succ time ih =>
    by_cases same : first = time + 1
    · exact False.elim (installed (same ▸ absent))
    have earlier : first ≤ time := by omega
    by_cases previous : ControlFrame.viewAt (states time) name = none
    · refine ⟨time + 1, by omega, by omega, Nat.le_refl _, bounded, ?_, by simpa using previous⟩
      intro point begin finish
      have equal : point = time + 1 := by omega
      exact equal ▸ installed
    · obtain ⟨opened, afterFirst, segment⟩ := ih earlier (by omega) previous
      refine ⟨opened, afterFirst, segment.positive, by have := segment.ordered; omega, bounded, ?_, segment.before⟩
      intro point begin finish
      by_cases final : point = time + 1
      · exact final ▸ installed
      · exact segment.installed point begin (by omega)

omit [DecidableEq Name] [DecidableEq Key] in
theorem prefix_closes_or_extends (states : Nat → R) {name : Name} {opened time : Nat}
    (current : EpisodePrefixOn states last name opened time) :
    (∃ closed, time ≤ closed ∧ EpisodeAtOn states last name opened closed) ∨ EpisodePrefixOn states last name opened last := by
  have advance (remaining : Nat) {time : Nat} (endIndex : time + remaining = last)
      (segment : EpisodePrefixOn states last name opened time) :
      (∃ closed, time ≤ closed ∧ EpisodeAtOn states last name opened closed) ∨ EpisodePrefixOn states last name opened last := by
    induction remaining generalizing time with
    | zero => exact .inr (by simpa only [Nat.add_zero] using endIndex ▸ segment)
    | succ remaining ih =>
      by_cases closes : ControlFrame.viewAt (states (time + 1)) name = none
      · exact .inl ⟨time, Nat.le_refl _, segment.positive, segment.ordered, by omega,
          segment.installed, segment.before, closes⟩
      · have next : EpisodePrefixOn states last name opened (time + 1) := by
          refine ⟨segment.positive, by have := segment.ordered; omega, by omega, ?_, segment.before⟩
          intro point begin finish
          by_cases final : point = time + 1
          · exact final ▸ closes
          · exact segment.installed point begin (by omega)
        rcases ih (by omega) next with ⟨closed, later, ends⟩ | opened
        · exact .inl ⟨closed, by omega, ends⟩
        · exact .inr opened
  exact advance (last - time) (by have := current.bounded; omega) current

omit [DecidableEq Name] [DecidableEq Key] in
theorem retired_through_residency (states : Nat → R)
    (stable : ∀ time, time < last → Frame.Stable (states time) (states (time + 1))) {name : Name} {birth first time : Nat}
    (interval : Residency states name birth time) (start : birth ≤ first) (order : first ≤ time)
    (bounded : time ≤ last)
    (retired : (states first name).map Fiber.retired = some true) :
    (states time name).map Fiber.retired = some true := by
  induction time with
  | zero =>
    have same : first = 0 := by omega
    exact same ▸ retired
  | succ time ih =>
    by_cases same : first = time + 1
    · exact same ▸ retired
    have earlier : birth ≤ time := by omega
    have wasRetired := ih (interval.prefix time earlier (by omega)) (by omega) (by omega)
    cases before : states time name with
    | none => simp [before] at wasRetired
    | some old =>
      cases after : states (time + 1) name with
      | none => exact False.elim (interval.present _ interval.ordered (Nat.le_refl _) after)
      | some row =>
        have flag : old.retired = true := by simpa [before] using wasRetired
        have retained := (stable time (by omega) name old row before after).2.2 flag
        exact congrArg some retained

/-- For the episode selected by the closing-order argument, a child from
that episode cannot install a view while it is in the same incarnation.
It would either supply a forbidden closing edge or remain installed and
retired at the quiet endpoint. -/
theorem child_never_installed (trace : History) (episode : ClosedEpisode trace)
    (maximal : ∀ later : ClosedEpisode trace, ¬ EpisodeEdge episode later)
    (quiet : Progress.Quiet (trace.state last))
    {birthStep time : Nat} {child : Name}
    (lower : episode.opened ≤ birthStep) (upper : birthStep < episode.closed)
    (creator : trace.actor birthStep = episode.name)
    (birthRule : EpisodeSelection.canBirth (trace.rule birthStep) = true)
    (bounded : time ≤ last) (lives : Residency trace.state child (birthStep + 1) time) :
    ControlFrame.viewAt (trace.state time) child = none := by
  apply Classical.byContradiction
  intro installed
  have bound := episode.interval.bounded
  have vacant : trace.state birthStep child = none := by
    simpa using lives.boundary.resolve_left (by omega)
  have born := lives.present (birthStep + 1) (Nat.le_refl _) lives.ordered
  have creation := (EpisodeSelection.actual_child_birth (trace.step birthStep (by omega)) birthRule vacant born).1
  rw [creator] at creation
  have inertAtBirth : ControlFrame.viewAt (trace.state (birthStep + 1)) child = none := by
    obtain ⟨code, component, phase, action, allowed, endpoint⟩ := creation
    have distinct : child ≠ episode.name := fun same => allowed.2.1 _ rfl (same ▸ vacant)
    rw [endpoint]
    unfold ControlFrame.viewAt
    rw [Transposition.mark_other _ _ _ _ distinct, put_self]
    rfl
  obtain ⟨opened, earliest, segment⟩ :=
    prefix_since_absence (last := last) trace.state child lives.ordered bounded inertAtBirth installed
  rcases prefix_closes_or_extends (last := last) trace.state segment with ⟨closed, _, closedEpisode⟩ | openEpisode
  · apply maximal ⟨child, opened, closed, closedEpisode⟩
    exact .inr ⟨birthStep, lower, by omega, creation, lives.prefix opened (by omega) segment.ordered⟩
  · have livesToEnd : Residency trace.state child (birthStep + 1) last := by
      refine ⟨by have := lives.ordered; omega, ?_, lives.boundary⟩
      intro point earlier within missing
      by_cases before : point ≤ time
      · exact lives.present point earlier before missing
      · exact openEpisode.installed point (by have := segment.ordered; omega) within
          (by simp [ControlFrame.viewAt, missing])
    have flagAtClosure := (child_retired_at_closure trace episode lower upper creator birthRule
      (livesToEnd.prefix episode.closed (by omega) (by omega))).1
    have finalRetired := retired_through_residency (last := last) trace.state
      (fun time bounded => Frame.step_stable program (trace.step time bounded).toCalculus) livesToEnd (by omega) (by omega)
      (Nat.le_refl _) flagAtClosure
    obtain ⟨row, found, notInactive⟩ := (ControlFrame.viewAt_present_iff _ _).mp
      (openEpisode.installed last openEpisode.ordered (Nat.le_refl _))
    have retired : row.retired = true := by simpa [found] using finalRetired
    have stable := quiet child row found
    cases phase : row.phase with
    | inactive => exact notInactive phase
    | active => simp [phase, Target, found, retired] at stable
    | reloading => simp [phase] at stable
    | unloading => simp [phase] at stable

/-- No installed consumer has an actual committed dependency on the
selected closing fiber during its episode. A closing consumer would give
an outgoing episode edge. An open one would block the recorded unload. -/
theorem no_demand_on_closing (trace : History) (episode : ClosedEpisode trace)
    (maximal : ∀ later : ClosedEpisode trace, ¬ EpisodeEdge episode later)
    {consumer : Name} {key : Key} {time : Nat}
    (lower : episode.opened ≤ time) (upper : time ≤ episode.closed) :
    ¬ Ordering.Demand (trace.state time) consumer episode.name key := by
  intro demand
  have bound := episode.interval.bounded
  have installed : ControlFrame.viewAt (trace.state time) consumer ≠ none := by
    obtain ⟨fiber, view, present, _, committed, _⟩ := demand
    simp [ControlFrame.viewAt, present, committed]
  have absent : ControlFrame.viewAt (trace.state 0) consumer = none := by
    simp [trace.start, ControlFrame.viewAt]
  obtain ⟨opened, _, segment⟩ := prefix_since_absence (last := last) trace.state consumer (Nat.zero_le _) (by omega) absent installed
  rcases prefix_closes_or_extends (last := last) trace.state segment with ⟨closed, later, clipped⟩ | full
  · exact maximal ⟨consumer, opened, closed, clipped⟩
      (.inl ⟨time, key, lower, upper, segment.ordered, later, demand⟩)
  · have atUnload := (demand_through_installation trace upper (by omega)
      (fun point after before => full.installed point (by have := segment.ordered; omega) (by omega))).mp demand
    obtain ⟨different, _⟩ :=
      supported_at trace episode.closed (by omega) consumer episode.name key atUnload
    obtain ⟨_, _, _, _, _, free, _⟩ := unload_boundary trace episode.interval
    exact free (Ordering.demand_relied _ consumer _ key atUnload different)

theorem not_relied_in_closing (trace : History) (episode : ClosedEpisode trace)
    (maximal : ∀ later : ClosedEpisode trace, ¬ EpisodeEdge episode later)
    {time : Nat} (lower : episode.opened ≤ time) (upper : time ≤ episode.closed) :
    ¬ Relied (trace.state time) episode.name := by
  rintro ⟨consumer, _, selected⟩
  cases present : trace.state time consumer with
  | none => simp [present] at selected
  | some fiber =>
    cases view : fiber.phase.committed with
    | none => simp [present, view] at selected
    | some chosen =>
      obtain ⟨key, req, provider⟩ := by simpa [present, view] using selected
      exact no_demand_on_closing trace episode maximal lower upper
        ⟨fiber, chosen, present, req, view, provider⟩

theorem born_row {before after : R} {actor child : Name}
    (vacant : before child = none)
    (creation : Transposition.CreatesChild program actor before after child) :
    ∃ component, after child = some (fresh component (some actor)) := by
  obtain ⟨_, component, _, _, ready, endpoint⟩ := creation
  have different : child ≠ actor := fun same => ready.2.1 actor rfl (same ▸ vacant)
  exact ⟨component, by rw [endpoint, Transposition.mark_other _ _ _ _ different, put_self]⟩

private theorem birth_requires_view {before after : R} {actor : Name} {rule : Labeled.Rule}
    (step : Labeled.Step program rule actor before after)
    (birthRule : EpisodeSelection.canBirth rule = true) :
    ControlFrame.viewAt before actor ≠ none := by
  cases step with
  | iter _ _ _ _ _ _ _ _ _ found phase _ _
  | finish _ _ _ _ _ _ _ _ found phase _ _
  | divert _ _ _ _ _ _ _ _ found phase _ _ =>
    simp [ControlFrame.viewAt, found, phase, Phase.committed]
  | _ => simp [EpisodeSelection.canBirth] at birthRule

/-- A newly present row is either this step's external insertion or the
result of a lifecycle rule that admits an actual birth landing. -/
theorem new_entry_rule {before after : R} {actor child : Name}
    {rule : Labeled.Rule} (step : Labeled.Step program rule actor before after)
    (vacant : before child = none) (born : after child ≠ none) :
    (rule = .insert ∧ child = actor) ∨ EpisodeSelection.canBirth rule = true := by
  cases step with
  | insert _ _ component parent _ =>
    by_cases same : child = actor
    · exact .inl ⟨rfl, same⟩
    · have vacantAfter : put before actor (fresh component parent) child = none := by
        simp [put, same, vacant]
      exact False.elim (born vacantAfter)
  | retire => exact False.elim (born ((Transposition.retire_presence _ _ _).mpr vacant))
  | remove =>
    have vacantAfter : erase before actor child = none := by
      by_cases same : child = actor <;> simp [erase, same, vacant]
    exact False.elim (born vacantAfter)
  | iter | finish | divert => exact .inr rfl
  | begin | leave =>
    exact False.elim (born ((Transposition.mark_presence _ _ _ _).mpr vacant))
  | unload _ _ _ word _ _ _ _ =>
    exact False.elim (born ((Transposition.mark_presence _ _ _ _).mpr
      (EntangledApplications.discharge_preserves_absence word before child vacant)))

def Leaf (state : R) (name : Name) : Prop :=
  ∀ other row, state other = some row → row.parent ≠ some name

theorem new_parent_requires_view {before after : R} {actor parent : Name} {rule : Labeled.Rule}
    (step : Labeled.Step program rule actor before after)
    (root : rule = .insert → ∃ row : F, after actor = some row ∧ row.parent = none)
    (inactive : ControlFrame.viewAt before parent = none) (old : Leaf before parent) :
    Leaf after parent := by
  intro other row found parentOf
  cases previous : before other with
  | some prior =>
    have parentEq := (Frame.step_stable program step.toCalculus other prior row previous found).2.1
    exact old other prior previous (parentEq.trans parentOf)
  | none =>
    have present : after other ≠ none := by simp [found]
    rcases new_entry_rule step previous present with ⟨insert, rfl⟩ | landed
    · obtain ⟨entry, exactRow, noParent⟩ := root insert
      have same := Option.some.inj (exactRow.symm.trans found)
      subst entry
      rw [noParent] at parentOf
      cases parentOf
    · have creation := (EpisodeSelection.actual_child_birth step landed previous present).1
      obtain ⟨component, exactRow⟩ := born_row previous creation
      have same := Option.some.inj (exactRow.symm.trans found)
      subst row
      have owner : actor = parent := Option.some.inj parentOf
      exact (birth_requires_view step landed) (owner ▸ inactive)

private theorem parent_closed_at (trace : History) (time : Nat) (bounded : time ≤ last) :
    Safety.ParentClosed (trace.state time) := by
  induction time with
  | zero => rw [trace.start]; exact Safety.empty_parentClosed
  | succ time ih =>
    exact Safety.step_parentClosed program (trace.step time (by omega)).toCalculus (ih (by omega))

theorem leaf_at_birth {before after : R} {parent child : Name}
    (parentClosed : Safety.ParentClosed before) (vacant : before child = none)
    (creation : Transposition.CreatesChild program parent before after child) : Leaf after child := by
  obtain ⟨_, component, phase, _, enabled, endpoint⟩ := creation
  have distinct : parent ≠ child := fun same => enabled.2.1 parent rfl (same.symm ▸ vacant)
  intro other row found parentOf
  rw [endpoint] at found
  obtain ⟨prior, placed, _⟩ := WellFormed.modify_origins
    (put (before) child (fresh component (some parent))) parent
    (fun row => { row with phase := phase }) (fun row => rfl) other row found
  have actualParent := (Frame.mark_stable _ parent phase other prior row placed found).2.1
  have pointsToChild := actualParent.trans parentOf
  by_cases own : other = child
  · subst other
    rw [put_self] at placed
    have same := Option.some.inj placed
    subst prior
    exact distinct (Option.some.inj pointsToChild)
  · simp only [put, if_neg own] at placed
    exact parentClosed other prior child placed pointsToChild vacant

private theorem leaf_from_birth (trace : History)
    (roots : PaperLifecycleClaims.RootInsertions trace)
    {birthStep time : Nat} {parent child : Name}
    (earlier : birthStep < time) (bounded : time ≤ last)
    (vacant : trace.state birthStep child = none)
    (creation : Transposition.CreatesChild program parent (trace.state birthStep)
      (trace.state (birthStep + 1)) child)
    (noView : ∀ t, birthStep < t → t ≤ time → ControlFrame.viewAt (trace.state t) child = none) :
    Leaf (trace.state time) child := by
  induction time with
  | zero => omega
  | succ time ih =>
    by_cases first : time = birthStep
    · subst time
      have parentClosed := parent_closed_at trace birthStep (by omega)
      exact leaf_at_birth parentClosed vacant creation
    · have previous := ih (by omega) (by omega) (fun t lo hi => noView t lo (by omega))
      exact new_parent_requires_view (trace.step time (by omega)) (roots time (by omega))
        (noView time (by omega) (by omega)) previous

theorem empty_table_during_inactivity {before after : R} {actor child : Name}
    {rule : Labeled.Rule} {old row : F} (step : Labeled.Step program rule actor before after)
    (scope : TableFrame.ScopedAccumulators before)
    (beforeHere : before child = some old) (afterHere : after child = some row)
    (inactiveBefore : ControlFrame.viewAt before child = none)
    (inactiveAfter : ControlFrame.viewAt after child = none) (empty : ∀ key, old.table key = none) :
    ∀ key, row.table key = none := by
  by_cases own : child = actor
  · subst child
    cases step with
    | insert _ _ _ _ ready => cases beforeHere.symm.trans ready.1
    | retire =>
      have same := Option.some.inj (show
          some {old with retired := true} = some row by
        simpa [Calculus.retire, Calculus.modify, beforeHere] using afterHere)
      subst row
      exact empty
    | remove => simp [erase] at afterHere
    | begin _ _ entry view present _ _ _ =>
      rw [ControlFrame.mark_viewAt _ _ _ _ present, if_pos rfl] at inactiveAfter
      cases inactiveAfter
    | iter _ _ _ _ _ _ _ _ _ present phase _ _
    | finish _ _ _ _ _ _ _ _ present phase _ _
    | divert _ _ _ _ _ _ _ _ present phase _ _
    | leave _ _ _ _ _ present phase _
    | unload _ _ _ _ _ present phase _ =>
      simp [ControlFrame.viewAt, present, phase, Phase.committed] at inactiveBefore
  · cases actorAt : before actor with
    | some entry =>
      intro key
      exact ((TableFrame.step_frame program step scope entry actorAt child old row beforeHere afterHere own key).1).mp
        (empty key)
    | none =>
      cases step with
      | insert _ _ _ _ _ =>
        have same := Option.some.inj (show some old = some row by
          simpa [put, own, beforeHere] using afterHere)
        subst row
        exact empty
      | retire _ _ present => exact False.elim (present actorAt)
      | remove _ _ ready => exact False.elim (Transposition.removable_present _ _ ready actorAt)
      | _ => simp_all

private theorem empty_table_from_birth (trace : History) {birthStep time : Nat} {parent child : Name}
    (bounded : time ≤ last) (lives : Residency trace.state child (birthStep + 1) time)
    (vacant : trace.state birthStep child = none)
    (creation : Transposition.CreatesChild program parent (trace.state birthStep)
      (trace.state (birthStep + 1)) child)
    (noView : ∀ t, birthStep < t → t ≤ time → ControlFrame.viewAt (trace.state t) child = none)
    {row : F} (found : trace.state time child = some row) : ∀ key, row.table key = none := by
  induction time generalizing row with
  | zero => have := lives.ordered; omega
  | succ time ih =>
    by_cases first : time = birthStep
    · subst time
      obtain ⟨component, new⟩ := born_row vacant creation
      have same := Option.some.inj (new.symm.trans found)
      subst row
      intro key
      rfl
    · have birthBefore : birthStep + 1 ≤ time := by have := lives.ordered; omega
      cases before : trace.state time child with
      | none => exact False.elim (lives.present time birthBefore (by omega) before)
      | some old =>
        have earlier := ih (by omega) (lives.prefix time birthBefore (by omega))
          (fun t lo hi => noView t lo (by omega)) before
        exact empty_table_during_inactivity (trace.step time (by omega))
          (TableFrame.reachable_scoped program (trace.prefixRun time (by omega))) before found
          (noView time (by omega) (by omega)) (noView (time + 1) (by omega) (by omega)) earlier

/-- The vestige premise of the suffix deletion theorem follows for every
surviving child born in this selected closing episode. In particular a
foreign actor cannot populate its empty table or become its child. -/
theorem closing_child_is_vestigial (trace : History) (episode : ClosedEpisode trace)
    (roots : PaperLifecycleClaims.RootInsertions trace)
    (maximal : ∀ later : ClosedEpisode trace, ¬ EpisodeEdge episode later)
    (quiet : Progress.Quiet (trace.state last))
    {birthStep : Nat} {child : Name}
    (lower : episode.opened ≤ birthStep) (upper : birthStep < episode.closed)
    (creator : trace.actor birthStep = episode.name)
    (birthRule : EpisodeSelection.canBirth (trace.rule birthStep) = true)
    (lives : Residency trace.state child (birthStep + 1) episode.closed) :
    Removable (trace.state (episode.closed + 1)) child ∧
      LegalHistory.rootAt (trace.state (episode.closed + 1)) child = false := by
  have bound := episode.interval.bounded
  have vacant : trace.state birthStep child = none := by
    simpa using lives.boundary.resolve_left (by omega)
  have born := lives.present (birthStep + 1) (Nat.le_refl _) lives.ordered
  have creation := (EpisodeSelection.actual_child_birth (trace.step birthStep (by omega)) birthRule vacant born).1
  rw [creator] at creation
  have flag := (child_retired_at_closure trace episode lower upper creator birthRule lives).1
  cases after : trace.state (episode.closed + 1) child with
  | none => simp [after] at flag
  | some row =>
    have continued : Residency trace.state child (birthStep + 1) (episode.closed + 1) := by
      refine ⟨by omega, ?_, lives.boundary⟩
      intro time bornAt latest vacantAt
      by_cases before : time ≤ episode.closed
      · exact lives.present time bornAt before vacantAt
      · have lastCut : time = episode.closed + 1 := by omega
        rw [lastCut, after] at vacantAt
        cases vacantAt
    have inert (time : Nat) (early : birthStep < time) (late : time ≤ episode.closed + 1) :
        ControlFrame.viewAt (trace.state time) child = none :=
      child_never_installed trace episode maximal quiet lower upper creator birthRule (by omega)
        (continued.prefix time (by omega) late)
    have inactive := inert (episode.closed + 1) (by omega) (Nat.le_refl _)
    have phase : row.phase = .inactive := by
      cases current : row.phase <;> simp [ControlFrame.viewAt, after, current, Phase.committed] at inactive ⊢
    have empty := empty_table_from_birth trace (by omega) continued vacant creation inert after
    have leaf := leaf_from_birth trace roots (by omega) (by omega) vacant creation inert
    obtain ⟨component, start⟩ := born_row vacant creation
    have parent := (continued.metadata trace (by omega) start after).2.symm
    constructor
    · rw [Removable, after]
      refine ⟨by simpa [after] using flag, phase, empty, ?_⟩
      intro other
      cases found : trace.state (episode.closed + 1) other with
      | none => trivial
      | some entry => exact leaf other entry found
    · simp [LegalHistory.rootAt, after, parent, fresh]

end Cordis.Repairs.EpisodeBoundary
