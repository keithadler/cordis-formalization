import Cordis.Repairs.GuardedBirthAddresses
import Cordis.Repairs.GuardedScheduleMatching

/-! Compare scheduled events by their actual birth paths. A jointly
ordered address sequence determines the stamps required by cut matching. -/
namespace Cordis.Repairs.GuardedAddressSchedule
open Calculus Stages LegalHistory GuardedHistory GuardedBirthAddresses GuardedBirthMatching
open GuardedScheduleMatching
open GuardedLandingMatching (ChildContinuations)

universe u
variable {Name Key Value Code Error : Type u} [DecidableEq Name] [DecidableEq Key]
variable {program : Code → Instruction Name Key Value Code Error} {last : Nat}

inductive AddressedEvent (Key Code : Type u) where
  | insert (component : Component Key Code)
  | retire (actor : Address)
  | remove (actor : Address)
  | lifecycle (kind : Lifecycle) (actor : Address)

noncomputable def actorAddress (trace : Trace program last) (cut : Nat) : Option Address :=
  ((trace.notes cut).1 (trace.actor cut)).bind (addressOf trace)

theorem actorAddress_eq_some (trace : Trace program last) {cut : Nat} {path : Address} :
    actorAddress trace cut = some path ↔
      ∃ birth, (trace.notes cut).1 (trace.actor cut) = some birth ∧ Addressed trace birth path := by
  simp only [actorAddress, Option.bind_eq_some_iff, addressOf_eq_some]

noncomputable def addressedEventAt (trace : Trace program last) (cut : Nat) : Option (AddressedEvent Key Code) :=
  match trace.event cut with
  | .command (.insert _ component) => some (.insert component)
  | .command (.retire _) => (actorAddress trace cut).map .retire
  | .command (.remove _) => (actorAddress trace cut).map .remove
  | .lifecycle kind _ => (actorAddress trace cut).map (.lifecycle kind)

def commandEventAddress : AddressedCommand Name Key Code → AddressedEvent Key Code
  | .insert _ component => .insert component
  | .retire path _ => .retire path
  | .remove path _ => .remove path

theorem addressedEventAt_of_command (trace : Trace program last) {cut : Nat} (bounded : cut < last)
    {command : OrchestrationSorting.Command Name Key Code} (event : trace.event cut = .command command) :
    addressedEventAt trace cut = (commandAt trace cut).map commandEventAddress := by
  have resolved {name : Name} {path : Address} {component : Component Key Code}
      (actor : trace.actor cut = name) (target : targetAt trace cut name = some (path, component)) :
      actorAddress trace cut = some path := by
    obtain ⟨birth, _, recorded, address, _, _⟩ := (targetAt_eq_some trace).mp target
    exact (actorAddress_eq_some trace).mpr ⟨birth, actor.symm ▸ recorded, address⟩
  cases command with
  | insert => simp [addressedEventAt, commandAt, event, commandEventAddress]
  | retire name =>
    obtain ⟨path, part, target⟩ := targetAt_command trace bounded (.inl event)
    have pathEq := resolved (by simp [Trace.actor, event, Vestigial.eventActor, OrchestrationSorting.Command.actor]) target
    simp [addressedEventAt, commandAt, event, target, pathEq, commandEventAddress]
  | remove name =>
    obtain ⟨path, part, target⟩ := targetAt_command trace bounded (.inr event)
    have pathEq := resolved (by simp [Trace.actor, event, Vestigial.eventActor, OrchestrationSorting.Command.actor]) target
    simp [addressedEventAt, commandAt, event, target, pathEq, commandEventAddress]

theorem stable_actor_address {first second : Nat} {original : Trace program first} {moved : Trace program second}
    {expand : Nat → Nat} (stable : StableActorAddresses original moved expand) {cut : Nat} (bound : cut < second) :
    actorAddress moved cut = actorAddress original (expand (cut + 1) - 1) := by
  let source := expand (cut + 1) - 1
  have exactTag := (stable.retained.actor_birth bound).symm
  change (original.notes source).1 (original.actor source) = _ at exactTag
  change actorAddress moved cut = actorAddress original source
  cases tag : (moved.notes cut).1 (moved.actor cut) with
  | none => simp only [actorAddress, exactTag, tag, Option.map_none, Option.bind_none]
  | some birth =>
    obtain ⟨path, here⟩ := exists_address moved (recorded_birth moved (Nat.le_of_lt bound) tag).1
    have there := stable.address bound tag here
    exact ((actorAddress_eq_some moved).mpr ⟨birth, tag, here⟩).trans
      ((actorAddress_eq_some original).mpr ⟨expand birth, exactTag.trans (by simp only [tag, Option.map_some]), there⟩).symm

theorem stable_addressed_event {first second : Nat} {original : Trace program first} {moved : Trace program second}
    {expand : Nat → Nat} (stable : StableActorAddresses original moved expand) {cut : Nat} (bound : cut < second) :
    addressedEventAt moved cut = addressedEventAt original (expand (cut + 1) - 1) := by
  simp only [addressedEventAt, stable.retained.label cut bound, stable_actor_address stable bound]

/-- A particular active endpoint row, identified by its birth address. -/
def ActiveEndpoint (trace : Trace program last) (address : Address) (name : Name)
    (row : Fiber Name Key Value Code (Inverse Name Key Value) Error) : Prop :=
  trace.state last name = some row ∧ row.phase.available ∧
    ∃ birth, (trace.notes last).1 name = some birth ∧ Addressed trace birth address

theorem ActiveEndpoint.unique {trace : Trace program last} {address : Address} {name peer : Name}
    {row other : Fiber Name Key Value Code (Inverse Name Key Value) Error}
    (first : ActiveEndpoint trace address name row) (second : ActiveEndpoint trace address peer other) :
    name = peer ∧ row = other := by
  obtain ⟨birth, tag, path⟩ := first.2.2
  obtain ⟨otherBirth, otherTag, otherPath⟩ := second.2.2
  have same := path.injective otherPath rfl
  have names := live_stamp_unique trace (Nat.le_refl _) tag (same.symm ▸ otherTag)
  exact ⟨names, Option.some.inj (first.1.symm.trans (names.symm ▸ second.1))⟩

/-- An available row at an earlier cut determines an active endpoint
with its actual birth address, component, and binding domain. -/
theorem active_endpoint_of_cut (trace : Trace program last)
    (opened : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    {cut : Nat} (bounded : cut ≤ last) {name : Name}
    {row : Fiber Name Key Value Code (Inverse Name Key Value) Error}
    (found : trace.state cut name = some row) (active : row.phase.available) :
    ∃ birth address later, (trace.notes cut).1 name = some birth ∧ Addressed trace birth address ∧
      ActiveEndpoint trace address name later ∧ later.component = row.component ∧
        ∀ key, later.table key = none ↔ row.table key = none := by
  obtain ⟨later, present, phase, component, stamp, domain⟩ :=
    trace.active_row_survives opened quiet bounded (Nat.le_refl _) found active
  cases tag : (trace.notes cut).1 name with
  | none =>
    have vacant := (trace.births_agree cut bounded name).mp tag
    rw [found] at vacant
    cases vacant
  | some birth =>
    obtain ⟨address, addressed⟩ := exists_address trace (recorded_birth trace bounded tag).1
    exact ⟨birth, address, later, rfl, addressed,
      ⟨present, phase.symm ▸ active, birth, stamp.trans tag, addressed⟩, component, domain⟩

/-- An installed incarnation is active by a quiet open endpoint, with
the declaration and birth address of its earlier installed row. -/
theorem active_endpoint_of_installed (trace : Trace program last)
    (opened : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    {cut birth : Nat} (bounded : cut ≤ last) {name : Name} {view : View Name Key} {address : Address}
    {row : Fiber Name Key Value Code (Inverse Name Key Value) Error}
    (found : trace.state cut name = some row) (installed : row.phase.committed = some view)
    (tag : (trace.notes cut).1 name = some birth) (known : Addressed trace birth address) :
    ∃ later, ActiveEndpoint trace address name later ∧ later.component = row.component := by
  have original : ControlFrame.viewAt (trace.state cut) name = some view := by
    simpa [ControlFrame.viewAt, found] using installed
  have retained (time : Nat) (lower : cut ≤ time) (upper : time ≤ last) :
      ControlFrame.viewAt (trace.state time) name = some view :=
    (trace.installed_through opened name lower upper (by simp [original])).trans original
  obtain ⟨later, present, component, stamp, _⟩ := trace.installed_row_through opened
    bounded (Nat.le_refl _) found (by simp [original])
  rw [tag] at stamp
  have terminal := quiet name later present
  have viewAt := retained last bounded (Nat.le_refl _)
  have available : later.phase.available := by
    cases phase : later.phase <;> simp [phase, Phase.available, ControlFrame.viewAt, present, Phase.committed] at viewAt terminal ⊢
  exact ⟨later, ⟨present, available, birth, stamp, known⟩, component⟩

/-- The actor of an actual activation reaches a quiet open endpoint at
the same birth address and with the same component. -/
theorem active_endpoint_of_activation (trace : Trace program last)
    (opened : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    {cut : Nat} (bounded : cut < last) {kind : Lifecycle} {name : Name}
    (event : trace.event cut = .lifecycle kind name) :
    ∃ row address, ActiveEndpoint trace address name row ∧ actorAddress trace cut = some address ∧
      ∀ source, trace.state cut name = some source → row.component = source.component := by
  obtain ⟨activation, step⟩ := trace.activation_at opened quiet bounded event
  obtain ⟨row, _, found, _, _⟩ := Transposition.activation_source program step activation
  have installed := activation_installs_view step activation
  have actor : trace.actor cut = name := by simp [Trace.actor, Vestigial.eventActor, event]
  cases stamp : (trace.notes cut).1 name with
  | none =>
    have vacant := (trace.births_agree cut (Nat.le_of_lt bounded) name).mp stamp
    rw [found] at vacant
    cases vacant
  | some birth =>
    obtain ⟨address, known⟩ := exists_address trace (recorded_birth trace (Nat.le_of_lt bounded) stamp).1
    have tag := trace.activation_stamp_through opened quiet bounded (Nat.le_succ _)
      (Nat.succ_le_of_lt bounded) event
    cases next : trace.state (cut + 1) name with
    | none => simp [ControlFrame.viewAt, next] at installed
    | some current =>
      cases committed : current.phase.committed with
      | none => simp [ControlFrame.viewAt, next, committed] at installed
      | some view =>
        obtain ⟨later, endpoint, component⟩ := active_endpoint_of_installed trace opened quiet
          (Nat.succ_le_of_lt bounded) next committed (tag.symm.trans stamp) known
        refine ⟨later, address, endpoint, (actorAddress_eq_some trace).mpr ⟨birth, actor.symm ▸ stamp, known⟩, ?_⟩
        intro source present
        have stable := transition_stable (trace.step cut bounded).1 name source current present next
        exact component.trans stable.1.symm

/-- A child's actual allocating stage has a valid target at the
preceding cut, with the parent's installed view and birth address. -/
theorem allocating_parent_target {trace : Trace program last}
    (opened : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    {birth ordinal : Nat} {parent : Address} (born : Addressed trace birth (.child parent ordinal)) :
    ∃ cut actor parentBirth row view, birth = cut + 1 ∧ cut < last ∧
      trace.state cut actor = some row ∧ row.phase.committed = some view ∧
      (trace.notes cut).1 actor = some parentBirth ∧ Addressed trace parentBirth parent ∧
      Target (trace.state cut) actor view := by
  have birthRule : EpisodeSelection.canBirth (trace.rule (birth - 1)) = true := by
    cases born with
    | child _ rule _ _ _ _ => simpa using rule
  obtain ⟨cut, parentBirth, kind, actor, placed, bounded, event, tag, known⟩ := born.allocating_event
  have capable : EpisodeSelection.canBirth kind.rule = true := by
    simpa [placed, Trace.rule, event, eventRule] using birthRule
  obtain ⟨activation, step⟩ := trace.activation_at opened quiet bounded event
  generalize trace.state (cut + 1) = after at step
  cases kind <;> simp [Lifecycle.rule, EpisodeSelection.canBirth, Transposition.Activation] at capable activation
  case iter =>
    cases step with
    | iter _ _ _ row _ _ view _ _ found reloading target _ =>
      exact ⟨cut, actor, parentBirth, row, view, placed, bounded, found,
        by simp [reloading, Phase.committed], tag, known, target⟩
  case finish =>
    cases step with
    | finish _ _ _ row _ _ view _ found reloading target _ =>
      exact ⟨cut, actor, parentBirth, row, view, placed, bounded, found,
        by simp [reloading, Phase.committed], tag, known, target⟩

/-- An active endpoint row of an exchanged schedule has the same
birth address at the same raw name in the original schedule. The
retained Finish event identifies the corresponding incarnation. -/
theorem stable_active_endpoint_address {original moved : Trace program last} {expand : Nat → Nat}
    (stable : StableActorAddresses original moved expand)
    (originalOpen : ¬ Nonempty (ClosedEpisode original)) (originalQuiet : Progress.Quiet (original.state last))
    (movedOpen : ¬ Nonempty (ClosedEpisode moved)) (movedQuiet : Progress.Quiet (moved.state last))
    {name : Name} {row : Fiber Name Key Value Code (Inverse Name Key Value) Error}
    (found : moved.state last name = some row) (active : row.phase.available) :
    ∃ originalRow birth movedBirth address,
      original.state last name = some originalRow ∧ originalRow.phase.available ∧
      (original.notes last).1 name = some birth ∧ (moved.notes last).1 name = some movedBirth ∧
      Addressed original birth address ∧ Addressed moved movedBirth address := by
  obtain ⟨cut, bounded, event, stamp⟩ := moved.active_row_has_finish movedOpen movedQuiet
    (Nat.le_refl _) found active
  cases tag : (moved.notes last).1 name with
  | none =>
    have vacant := (moved.births_agree last (Nat.le_refl _) name).mp tag
    rw [found] at vacant
    cases vacant
  | some movedBirth =>
    have atFinish : (moved.notes cut).1 name = some movedBirth := stamp.trans tag
    have movedActor : moved.actor cut = name := by simp [Trace.actor, Vestigial.eventActor, event]
    obtain ⟨address, movedAddress⟩ :=
      exists_address moved (recorded_birth moved (Nat.le_of_lt bounded) atFinish).1
    have originalAddress := stable.address bounded (movedActor.symm ▸ atFinish) movedAddress
    let originalCut := expand (cut + 1) - 1
    have inside : originalCut < last := by
      have := (stable.retained.stamp cut bounded).2
      dsimp [originalCut]
      omega
    have originalEvent : original.event originalCut = .lifecycle .finish name :=
      (stable.retained.label cut bounded).symm.trans event
    have originalActor : original.actor originalCut = name := by
      simp [Trace.actor, Vestigial.eventActor, originalEvent]
    have originalTag : (original.notes originalCut).1 name = some (expand movedBirth) := by
      have maps := stable.retained.actor_birth bounded
      change ((moved.notes cut).1 (moved.actor cut)).map expand = (original.notes originalCut).1 (original.actor originalCut) at maps
      rw [movedActor, originalActor, atFinish] at maps
      exact maps.symm
    obtain ⟨originalRow, rowFound, rowActive, sameStamp⟩ :=
      original.finished_row_at_cut originalOpen originalQuiet inside (Nat.le_refl _) originalEvent
    exact ⟨originalRow, expand movedBirth, movedBirth, address, rowFound, rowActive,
      sameStamp.trans originalTag, rfl, originalAddress, movedAddress⟩

/-- Matching active endpoints at one address compare the actual rows
and table values at a fixed-name exchange, including absent bindings. -/
theorem stable_active_endpoint_payload [Setoid Value]
    {original moved : Trace program last} {expand : Nat → Nat}
    (stable : StableActorAddresses original moved expand)
    (related : StageSimulation.Related Eq (GuardedCutState.project (original.state last))
      (GuardedCutState.project (moved.state last)))
    (originalOpen : ¬ Nonempty (ClosedEpisode original)) (originalQuiet : Progress.Quiet (original.state last))
    (movedOpen : ¬ Nonempty (ClosedEpisode moved)) (movedQuiet : Progress.Quiet (moved.state last))
    {address : Address} {name peer : Name}
    {row other : Fiber Name Key Value Code (Inverse Name Key Value) Error}
    (first : ActiveEndpoint original address name row) (second : ActiveEndpoint moved address peer other) :
    row.component = other.component ∧
      ∀ key, Iterators.OptionRel (fun a b : Value => a ≈ b) (row.table key) (other.table key) := by
  obtain ⟨foundRow, birth, movedBirth, path, present, ready, tag, movedTag, addressed, movedAddressed⟩ :=
    stable_active_endpoint_address stable originalOpen originalQuiet movedOpen movedQuiet second.1 second.2.1
  obtain ⟨givenBirth, givenTag, givenAddress⟩ := second.2.2
  have stamps := Option.some.inj (movedTag.symm.trans givenTag)
  have paths := movedAddressed.unique (stamps.symm ▸ givenAddress)
  have names := (first.unique (show ActiveEndpoint original address peer foundRow from
    ⟨present, ready, birth, tag, paths ▸ addressed⟩)).1
  subst peer
  have fields := related name
  simp only [GuardedCutState.project, first.1, second.1, Option.map_some, Iterators.OptionRel] at fields
  exact ⟨fields.component.eq_of_codes, fields.table⟩

noncomputable def addressedEvents (trace : Trace program last) : List (Option (AddressedEvent Key Code)) :=
  (List.range last).map (addressedEventAt trace)

/-- An unload has a present actor, so addressing the event cannot hide it. -/
theorem addressed_unload_of_closed (trace : Trace program last) (episode : ClosedEpisode trace) :
    ∃ address, some (.lifecycle .unload address) ∈ addressedEvents trace := by
  obtain ⟨event, unload⟩ := unload_boundary trace episode.interval
  obtain ⟨row, _, found, _, _, _⟩ := unload
  have bounded := episode.interval.bounded
  have actor : trace.actor episode.closed = episode.name := by
    simp [Trace.actor, Vestigial.eventActor, event]
  cases tag : (trace.notes episode.closed).1 (trace.actor episode.closed) with
  | none =>
    have vacant := (trace.births_agree episode.closed (Nat.le_of_lt bounded) (trace.actor episode.closed)).mp tag
    rw [actor, found] at vacant
    cases vacant
  | some birth =>
    obtain ⟨address, addressed⟩ := exists_address trace (recorded_birth trace (Nat.le_of_lt bounded) tag).1
    have resolved := (actorAddress_eq_some trace).mpr ⟨birth, tag, addressed⟩
    refine ⟨address, List.mem_map.mpr ⟨episode.closed, List.mem_range.mpr bounded, ?_⟩⟩
    simp [addressedEventAt, event, resolved]

theorem open_of_addressed_events_perm {original moved : Trace program last}
    (events : (addressedEvents moved).Perm (addressedEvents original))
    (openOnly : ¬ Nonempty (ClosedEpisode original)) : ¬ Nonempty (ClosedEpisode moved) := by
  rintro ⟨episode⟩
  obtain ⟨address, member⟩ := addressed_unload_of_closed moved episode
  obtain ⟨cut, inside, addressed⟩ := List.mem_map.mp (events.mem_iff.mp member)
  cases event : original.event cut with
  | command command =>
    cases command <;> simp [addressedEventAt, event, Option.map_eq_some_iff] at addressed
  | lifecycle kind actor =>
    obtain ⟨_, _, same⟩ := Option.map_eq_some_iff.mp (by simpa only [addressedEventAt, event] using addressed)
    have kindEq := (AddressedEvent.lifecycle.inj same).1
    exact original.no_unload openOnly (List.mem_range.mp inside) (kindEq ▸ event)

/-- An addressed Finish records the actual actor and its live stamp. -/
theorem addressed_finish_at (trace : Trace program last) {cut : Nat} {address : Address} :
    addressedEventAt trace cut = some (.lifecycle .finish address) ↔
      ∃ name birth, trace.event cut = .lifecycle .finish name ∧
        (trace.notes cut).1 name = some birth ∧ Addressed trace birth address := by
  constructor
  · intro addressed
    cases event : trace.event cut with
    | command command =>
      cases command <;> simp [addressedEventAt, event, Option.map_eq_some_iff] at addressed
    | lifecycle kind name =>
      obtain ⟨actorPath, resolved, same⟩ := Option.map_eq_some_iff.mp
        (by simpa only [addressedEventAt, event] using addressed)
      obtain ⟨rfl, rfl⟩ := AddressedEvent.lifecycle.inj same
      have actor : trace.actor cut = name := by simp [Trace.actor, Vestigial.eventActor, event]
      obtain ⟨birth, tag, path⟩ := (actorAddress_eq_some trace).mp resolved
      exact ⟨name, birth, rfl, actor ▸ tag, path⟩
  · rintro ⟨name, birth, event, tag, path⟩
    have actor : trace.actor cut = name := by simp [Trace.actor, Vestigial.eventActor, event]
    have resolved := (actorAddress_eq_some trace).mpr ⟨birth, actor.symm ▸ tag, path⟩
    simp [addressedEventAt, event, resolved]

/-- In a quiet open history, the addressed Finish events identify
exactly the active incarnations at the endpoint. -/
theorem addressed_finish_iff_active (trace : Trace program last)
    (openOnly : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    (address : Address) :
    some (.lifecycle .finish address) ∈ addressedEvents trace ↔
      ∃ name row birth, trace.state last name = some row ∧ row.phase.available ∧
        (trace.notes last).1 name = some birth ∧ Addressed trace birth address := by
  constructor
  · intro member
    obtain ⟨cut, inside, addressed⟩ := List.mem_map.mp member
    obtain ⟨name, birth, event, tag, path⟩ := (addressed_finish_at trace).mp addressed
    obtain ⟨row, present, ready, stamp⟩ :=
      trace.finished_row_at_cut openOnly quiet (List.mem_range.mp inside) (Nat.le_refl _) event
    exact ⟨name, row, birth, present, ready, stamp.trans tag, path⟩
  · rintro ⟨name, row, birth, present, ready, tag, path⟩
    obtain ⟨cut, bounded, event, stamp⟩ :=
      trace.active_row_has_finish openOnly quiet (Nat.le_refl _) present ready
    exact List.mem_map.mpr ⟨cut, List.mem_range.mpr bounded,
      (addressed_finish_at trace).mpr ⟨name, birth, event, stamp.trans tag, path⟩⟩

/-- Once an incarnation finishes in a quiet open history, it remains
active. The same addressed incarnation cannot finish again. -/
theorem addressed_finish_unique (trace : Trace program last)
    (opened : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    {first second : Nat} (firstBound : first < last) (secondBound : second < last) {address : Address}
    (firstFinish : addressedEventAt trace first = some (.lifecycle .finish address))
    (secondFinish : addressedEventAt trace second = some (.lifecycle .finish address)) :
    first = second := by
  have cannot {a b : Nat} (order : a < b) (bBound : b < last)
      (earlier : addressedEventAt trace a = some (.lifecycle .finish address))
      (later : addressedEventAt trace b = some (.lifecycle .finish address)) : False := by
    obtain ⟨name, birth, event, tag, known⟩ := (addressed_finish_at trace).mp earlier
    obtain ⟨peer, otherBirth, otherEvent, otherTag, otherKnown⟩ := (addressed_finish_at trace).mp later
    have stamps := known.injective otherKnown rfl
    have actors := born_unique trace (recorded_birth trace (by omega : a ≤ last) tag).1
      (recorded_birth trace (Nat.le_of_lt bBound) (stamps.symm ▸ otherTag)).1
    subst peer
    obtain ⟨row, present, ready, _⟩ := trace.finished_row_at_cut opened quiet order (Nat.le_of_lt bBound) event
    obtain ⟨activation, step⟩ := trace.activation_at opened quiet bBound otherEvent
    obtain ⟨source, _, found, unavailable, _⟩ := Transposition.activation_source program step activation
    exact unavailable (Option.some.inj (present.symm.trans found) ▸ ready)
  rcases Nat.lt_trichotomy first second with earlier | same | later
  · exact False.elim (cannot earlier secondBound firstFinish secondFinish)
  · exact same
  · exact False.elim (cannot later firstBound secondFinish firstFinish)

/-- The Finish of a frontier activation's incarnation is determined by
the actual quiet open history and cannot precede the activation. -/
theorem finish_of_activation (trace : Trace program last)
    (opened : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    {cut : Nat} (bounded : cut < last) {kind : Lifecycle} {name : Name} {address : Address}
    (event : trace.event cut = .lifecycle kind name) (addressed : actorAddress trace cut = some address) :
    ∃ finish, cut ≤ finish ∧ finish < last ∧ trace.event finish = .lifecycle .finish name ∧
      addressedEventAt trace finish = some (.lifecycle .finish address) := by
  obtain ⟨row, actualAddress, endpoint, resolved, _⟩ :=
    active_endpoint_of_activation trace opened quiet bounded event
  have same := Option.some.inj (addressed.symm.trans resolved)
  subst actualAddress
  obtain ⟨birth, tag, known⟩ := endpoint.2.2
  obtain ⟨finish, inside, label, stamp⟩ :=
    trace.active_row_has_finish opened quiet (Nat.le_refl _) endpoint.1 endpoint.2.1
  have lower : cut ≤ finish := by
    apply Nat.le_of_not_gt
    intro earlier
    obtain ⟨previous, present, ready, _⟩ :=
      trace.finished_row_at_cut opened quiet earlier (Nat.le_of_lt bounded) label
    obtain ⟨activation, step⟩ := trace.activation_at opened quiet bounded event
    obtain ⟨source, _, found, unavailable, _⟩ := Transposition.activation_source program step activation
    exact unavailable (Option.some.inj (present.symm.trans found) ▸ ready)
  exact ⟨finish, lower, inside, label, (addressed_finish_at trace).mpr
    ⟨name, birth, label, stamp.trans tag, known⟩⟩

/-- A pending addressed Finish in the reference cannot already have
occurred in the peer's matching prefix. -/
theorem finish_after_matched_prefix {otherLast : Nat}
    {reference : Trace program last} {peer : Trace program otherLast}
    (opened : ¬ Nonempty (ClosedEpisode reference)) (quiet : Progress.Quiet (reference.state last))
    {start referenceCut peerCut : Nat} (pending : start ≤ referenceCut) (bounded : referenceCut < last)
    (past : ∀ i, i < start → addressedEventAt reference i = addressedEventAt peer i)
    {address : Address}
    (leftFinish : addressedEventAt reference referenceCut = some (.lifecycle .finish address))
    (rightFinish : addressedEventAt peer peerCut = some (.lifecycle .finish address)) :
    start ≤ peerCut := by
  apply Nat.le_of_not_gt
  intro earlier
  have copied := (past peerCut earlier).trans rightFinish
  have same := addressed_finish_unique reference opened quiet bounded (by omega) leftFinish copied
  omega

/-- Addressed endpoint agreement determines the providers at arbitrary
earlier cuts, because an available reservation survives to the endpoint. -/
theorem available_providers_of_endpoint_comparison {otherLast : Nat}
    {before : Trace program last} {after : Trace program otherLast}
    (opened : ¬ Nonempty (ClosedEpisode before)) (quiet : Progress.Quiet (before.state last))
    (afterOpen : ¬ Nonempty (ClosedEpisode after)) (afterQuiet : Progress.Quiet (after.state otherLast))
    (events : (addressedEvents before).Perm (addressedEvents after))
    (components : ∀ {address name peer row other},
      ActiveEndpoint before address name row → ActiveEndpoint after address peer other → row.component = other.component)
    {leftCut rightCut : Nat} (leftBound : leftCut ≤ last) (rightBound : rightCut ≤ otherLast)
    {name peer : Name} {key : Key}
    {row other : Fiber Name Key Value Code (Inverse Name Key Value) Error}
    (found : before.state leftCut name = some row) (active : row.phase.available)
    (reserves : row.component.provides key = true)
    (otherFound : after.state rightCut peer = some other) (otherActive : other.phase.available)
    (otherReserves : other.component.provides key = true) :
    ∃ address birth otherBirth, (before.notes leftCut).1 name = some birth ∧
      (after.notes rightCut).1 peer = some otherBirth ∧
      Addressed before birth address ∧ Addressed after otherBirth address := by
  obtain ⟨birth, address, leftRow, tag, known, leftEndpoint, leftComponent, _⟩ :=
    active_endpoint_of_cut before opened quiet leftBound found active
  obtain ⟨otherBirth, otherAddress, rightRow, otherTag, otherKnown, rightEndpoint, rightComponent, _⟩ :=
    active_endpoint_of_cut after afterOpen afterQuiet rightBound otherFound otherActive
  obtain ⟨leftStamp, leftTag, leftKnown⟩ := leftEndpoint.2.2
  obtain ⟨target, movedRow, movedBirth, movedPresent, movedReady, movedStamp, movedAddress⟩ :=
    (addressed_finish_iff_active after afterOpen afterQuiet address).mp
      (events.mem_iff.mp ((addressed_finish_iff_active before opened quiet address).mpr
        ⟨name, leftRow, leftStamp, leftEndpoint.1, leftEndpoint.2.1, leftTag, leftKnown⟩))
  have movedEndpoint : ActiveEndpoint after address target movedRow :=
    ⟨movedPresent, movedReady, movedBirth, movedStamp, movedAddress⟩
  have component := components leftEndpoint movedEndpoint
  have movedReserves : movedRow.component.provides key = true := by rwa [← component, leftComponent]
  have rightReserves : rightRow.component.provides key = true := by rwa [rightComponent]
  have targets : target = peer := by
    apply Classical.byContradiction
    intro different
    exact (after.ownership otherLast (Nat.le_refl _)).2 target peer movedRow rightRow
      movedPresent rightEndpoint.1 different key ⟨movedReserves, rightReserves⟩
  have sameBirth : movedBirth = otherBirth := by
    obtain ⟨endpointBirth, endpointStamp, endpointAddress⟩ := rightEndpoint.2.2
    have same := endpointAddress.injective otherKnown rfl
    exact (Option.some.inj (movedStamp.symm.trans (targets.symm ▸ endpointStamp))).trans same
  have sameAddress := movedAddress.unique (sameBirth.symm ▸ otherKnown)
  exact ⟨address, birth, otherBirth, tag, otherTag, known, sameAddress.symm ▸ otherKnown⟩

theorem selected_provider_at_cut {trace : Trace program last} {cut : Nat} (bounded : cut ≤ last) {key : Key}
    {actor : Name} {view : View Name Key} {consumer : Fiber Name Key Value Code (Inverse Name Key Value) Error}
    (present : trace.state cut actor = some consumer) (required : consumer.component.requires key = true)
    (valid : Target (trace.state cut) actor view) :
    ∃ provider, trace.state cut (view key) = some provider ∧ provider.phase.available ∧
      provider.component.provides key = true := by
  simp only [Target, present] at valid
  have binding := valid.2 key required
  cases providerAt : trace.state cut (view key) with
  | none => simp [providerAt] at binding
  | some provider =>
    simp only [providerAt] at binding
    exact ⟨provider, rfl, binding.1, (trace.ownership cut bounded).1 _ provider key providerAt binding.2⟩

/-- A Finish has the installed target of its reloading source row. -/
theorem finish_source_target {trace : Trace program last} {cut : Nat} (bounded : cut < last)
    {name : Name} (event : trace.event cut = .lifecycle .finish name) :
    ∃ row view, trace.state cut name = some row ∧ row.phase.committed = some view ∧
      Target (trace.state cut) name view := by
  have step := (trace.step cut bounded).1
  rw [event] at step
  change Labeled.Step program .finish name (trace.state cut) (trace.state (cut + 1)) at step
  generalize trace.state (cut + 1) = after at step
  cases step with
  | finish _ _ _ row _ _ view _ found reloading target _ =>
    exact ⟨row, view, found, by simp [reloading, Phase.committed], target⟩

/-- A Begin chooses a valid target and installs that exact view. -/
theorem begin_source_target {trace : Trace program last} {cut : Nat} (bounded : cut < last)
    {name : Name} (event : trace.event cut = .lifecycle .begin name) :
    ∃ row next view, trace.state cut name = some row ∧ Target (trace.state cut) name view ∧
      trace.state (cut + 1) name = some next ∧ next.phase.committed = some view ∧
      next.component = row.component := by
  have step := (trace.step cut bounded).1
  rw [event] at step
  change Labeled.Step program .begin name (trace.state cut) (trace.state (cut + 1)) at step
  generalize result : trace.state (cut + 1) = after at step
  cases step with
  | begin _ _ row view found _ _ target =>
    exact ⟨row, _, view, found, target, mark_self _ _ _ _ found, rfl, rfl⟩

/-- The endpoint row declaring a selected key must already have
finished by the time an actual target can use its binding. -/
theorem finish_of_endpoint_provider_at_target (trace : Trace program last)
    (opened : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    {provider : Address} {name consumer : Name} {key : Key}
    {row source : Fiber Name Key Value Code (Inverse Name Key Value) Error}
    (first : ActiveEndpoint trace provider name row) (provides : row.component.provides key = true)
    {secondCut : Nat} (secondBound : secondCut ≤ last) {view : View Name Key}
    (found : trace.state secondCut consumer = some source) (needed : source.component.requires key = true)
    (target : Target (trace.state secondCut) consumer view) :
    ∃ earlier, earlier < secondCut ∧ addressedEventAt trace earlier = some (.lifecycle .finish provider) := by
  obtain ⟨actual, present, active, declared⟩ := selected_provider_at_cut secondBound found needed target
  obtain ⟨birth, address, available, live, actualAddress, endpoint, declaration, _⟩ :=
    active_endpoint_of_cut trace opened quiet secondBound present active
  have sameName : name = view key := by
    apply Classical.byContradiction
    intro different
    exact (trace.ownership last (Nat.le_refl _)).2 name (view key) row available
      first.1 endpoint.1 different key ⟨provides, declaration ▸ declared⟩
  obtain ⟨priorBirth, endpointTag, endpointAddress⟩ := first.2.2
  obtain ⟨currentBirth, currentTag, currentAddress⟩ := endpoint.2.2
  have sameBirth := Option.some.inj ((sameName ▸ endpointTag).symm.trans currentTag)
  have sameAddress := endpointAddress.unique (sameBirth.symm ▸ currentAddress)
  have knownProvider : Addressed trace birth provider := sameAddress.symm ▸ actualAddress
  obtain ⟨earlier, before, finish, saved⟩ :=
    trace.active_row_has_finish opened quiet secondBound present active
  have prior := (addressed_finish_at trace).mpr ⟨_, birth, finish, saved.trans live, knownProvider⟩
  exact ⟨earlier, before, prior⟩

/-- A provider of an installed consumer must finish before the cut
where the consumer uses its committed target. -/
theorem addressed_finish_lt_of_installed_consumer (trace : Trace program last)
    (opened : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    {provider consumer : Address} {name actor : Name} {key : Key}
    {row other source : Fiber Name Key Value Code (Inverse Name Key Value) Error}
    (first : ActiveEndpoint trace provider name row) (second : ActiveEndpoint trace consumer actor other)
    (provides : row.component.provides key = true) (requires : other.component.requires key = true)
    {firstCut secondCut : Nat} (firstBound : firstCut < last) (secondBound : secondCut ≤ last)
    (firstFinish : addressedEventAt trace firstCut = some (.lifecycle .finish provider))
    {consumerName : Name} {stamp : Nat} {view : View Name Key}
    (found : trace.state secondCut consumerName = some source) (installed : source.phase.committed = some view)
    (target : Target (trace.state secondCut) consumerName view)
    (tag : (trace.notes secondCut).1 consumerName = some stamp) (known : Addressed trace stamp consumer) :
    firstCut < secondCut := by
  obtain ⟨lastRow, atEnd, component⟩ :=
    active_endpoint_of_installed trace opened quiet secondBound found installed tag known
  have sameRow := (second.unique atEnd).2
  have needed : source.component.requires key = true := by rwa [← component, ← sameRow]
  obtain ⟨earlier, before, prior⟩ :=
    finish_of_endpoint_provider_at_target trace opened quiet first provides secondBound found needed target
  have equal := addressed_finish_unique trace opened quiet firstBound (by omega) firstFinish prior
  omega

/-- A shared required and provided key at a quiet open endpoint forces
the provider's addressed Finish to precede the consumer's Finish. -/
theorem addressed_finish_lt_of_provider (trace : Trace program last)
    (opened : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    {provider consumer : Address} {name actor : Name} {key : Key}
    {row other : Fiber Name Key Value Code (Inverse Name Key Value) Error}
    (first : ActiveEndpoint trace provider name row) (second : ActiveEndpoint trace consumer actor other)
    (provides : row.component.provides key = true) (requires : other.component.requires key = true)
    {firstCut secondCut : Nat} (firstBound : firstCut < last) (secondBound : secondCut < last)
    (firstFinish : addressedEventAt trace firstCut = some (.lifecycle .finish provider))
    (secondFinish : addressedEventAt trace secondCut = some (.lifecycle .finish consumer)) :
    firstCut < secondCut := by
  obtain ⟨consumerName, stamp, event, tag, known⟩ := (addressed_finish_at trace).mp secondFinish
  obtain ⟨source, view, found, installed, target⟩ := finish_source_target secondBound event
  exact addressed_finish_lt_of_installed_consumer trace opened quiet first second provides requires firstBound
    (Nat.le_of_lt secondBound) firstFinish found installed target tag known

/-- A provider edge between active endpoint incarnations is witnessed
by a shared declared key. Disjointness determines the actual provider. -/
def EndpointProvider (trace : Trace program last) (provider consumer : Address) : Prop :=
  ∃ name actor row other key, ActiveEndpoint trace provider name row ∧
    ActiveEndpoint trace consumer actor other ∧
    row.component.provides key = true ∧ other.component.requires key = true

/-- A provider prerequisite also precedes a consumer's Begin. Use the
target of the actual activation, including when the view is newly installed. -/
theorem provider_finish_before_activation (trace : Trace program last)
    (opened : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    {cut : Nat} (bounded : cut < last) {provider consumer : Address} {kind : Lifecycle} {name : Name}
    (event : trace.event cut = .lifecycle kind name) (addressed : actorAddress trace cut = some consumer)
    (edge : EndpointProvider trace provider consumer) :
    ∃ earlier, earlier < cut ∧ addressedEventAt trace earlier = some (.lifecycle .finish provider) := by
  obtain ⟨_, _, _, _, _, first, second, provides, requires⟩ := edge
  obtain ⟨row, address, endpoint, resolved, component⟩ :=
    active_endpoint_of_activation trace opened quiet bounded event
  have equal := Option.some.inj (addressed.symm.trans resolved)
  subst address
  have same := (second.unique endpoint).2
  obtain ⟨activation, step⟩ := trace.activation_at opened quiet bounded event
  obtain ⟨source, view, present, _, target⟩ := Transposition.activation_source program step activation
  exact finish_of_endpoint_provider_at_target trace opened quiet first provides (Nat.le_of_lt bounded)
    present ((component source present) ▸ (same ▸ requires)) target

/-- A key selected by an actual installed target gives an addressed
provider edge, with the provider's stamp from the lookup cut. -/
theorem endpoint_provider_of_installed_target (trace : Trace program last)
    (opened : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    {cut : Nat} (bounded : cut ≤ last) {actor : Name} {birth : Nat} {address : Address}
    {view : View Name Key} {key : Key}
    {row : Fiber Name Key Value Code (Inverse Name Key Value) Error}
    (found : trace.state cut actor = some row) (installed : row.phase.committed = some view)
    (target : Target (trace.state cut) actor view) (required : row.component.requires key = true)
    (tag : (trace.notes cut).1 actor = some birth) (known : Addressed trace birth address) :
    ∃ provider stamp, (trace.notes cut).1 (view key) = some stamp ∧ Addressed trace stamp provider ∧
      EndpointProvider trace provider address := by
  obtain ⟨_, present, active, declared⟩ := selected_provider_at_cut bounded found required target
  obtain ⟨stamp, provider, later, live, path, source, component, _⟩ :=
    active_endpoint_of_cut trace opened quiet bounded present active
  obtain ⟨consumer, destination, declaration⟩ :=
    active_endpoint_of_installed trace opened quiet bounded found installed tag known
  exact ⟨provider, stamp, live, path, view key, actor, later, consumer, key, source, destination,
    component.symm ▸ declared, declaration.symm ▸ required⟩

/-- Every link of an endpoint provider chain orders actual Finish events. -/
theorem addressed_finish_lt_of_provider_chain (trace : Trace program last)
    (opened : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    {provider consumer : Address} (chain : Relation.TransGen (EndpointProvider trace) provider consumer)
    {firstCut secondCut : Nat} (firstBound : firstCut < last) (secondBound : secondCut < last)
    (firstFinish : addressedEventAt trace firstCut = some (.lifecycle .finish provider))
    (secondFinish : addressedEventAt trace secondCut = some (.lifecycle .finish consumer)) :
    firstCut < secondCut := by
  induction chain generalizing secondCut with
  | single edge =>
    obtain ⟨_, _, _, _, _, source, target, provides, requires⟩ := edge
    exact addressed_finish_lt_of_provider trace opened quiet source target provides requires
      firstBound secondBound firstFinish secondFinish
  | @tail middle consumer prior edge ih =>
    obtain ⟨name, actor, row, other, key, source, target, provides, requires⟩ := edge
    obtain ⟨birth, tag, addressed⟩ := source.2.2
    obtain ⟨cut, bounded, event, stamp⟩ := trace.active_row_has_finish opened quiet (Nat.le_refl _) source.1 source.2.1
    have atMiddle := (addressed_finish_at trace).mpr ⟨name, birth, event, stamp.trans tag, addressed⟩
    exact Nat.lt_trans (ih bounded atMiddle)
      (addressed_finish_lt_of_provider trace opened quiet source target provides requires
        bounded secondBound atMiddle secondFinish)

/-- A chain of providers finishes before its final consumer can use its
installed view, even while that consumer is still reloading. -/
theorem addressed_finish_lt_of_provider_chain_at_installed (trace : Trace program last)
    (opened : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    {provider consumer : Address} (chain : Relation.TransGen (EndpointProvider trace) provider consumer)
    {firstCut secondCut : Nat} (firstBound : firstCut < last) (secondBound : secondCut ≤ last)
    (firstFinish : addressedEventAt trace firstCut = some (.lifecycle .finish provider))
    {actor : Name} {birth : Nat} {view : View Name Key}
    {row : Fiber Name Key Value Code (Inverse Name Key Value) Error}
    (found : trace.state secondCut actor = some row) (installed : row.phase.committed = some view)
    (target : Target (trace.state secondCut) actor view)
    (tag : (trace.notes secondCut).1 actor = some birth) (known : Addressed trace birth consumer) :
    firstCut < secondCut := by
  have finalEdge {address : Address} (edge : EndpointProvider trace address consumer)
      {cut : Nat} (bounded : cut < last)
      (finished : addressedEventAt trace cut = some (.lifecycle .finish address)) : cut < secondCut := by
    obtain ⟨_, _, _, _, _, source, destination, provides, requires⟩ := edge
    exact addressed_finish_lt_of_installed_consumer trace opened quiet source destination provides requires
      bounded secondBound finished found installed target tag known
  cases chain with
  | single edge => exact finalEdge edge firstBound firstFinish
  | @tail middle consumer prior edge =>
    have lastEdge := edge
    obtain ⟨name, _, _, _, _, source, _, _, _⟩ := edge
    obtain ⟨stamp, live, addressed⟩ := source.2.2
    obtain ⟨cut, bounded, event, saved⟩ :=
      trace.active_row_has_finish opened quiet (Nat.le_refl _) source.1 source.2.1
    have finished := (addressed_finish_at trace).mpr ⟨name, stamp, event, saved.trans live, addressed⟩
    exact Nat.lt_trans
      (addressed_finish_lt_of_provider_chain trace opened quiet prior firstBound bounded firstFinish finished)
      (finalEdge lastEdge bounded finished)

theorem endpoint_provider_of_comparison {otherLast : Nat}
    {left : Trace program last} {right : Trace program otherLast}
    (leftOpen : ¬ Nonempty (ClosedEpisode left)) (leftQuiet : Progress.Quiet (left.state last))
    (rightOpen : ¬ Nonempty (ClosedEpisode right)) (rightQuiet : Progress.Quiet (right.state otherLast))
    (events : (addressedEvents left).Perm (addressedEvents right))
    (components : ∀ {address name peer row other},
      ActiveEndpoint left address name row → ActiveEndpoint right address peer other → row.component = other.component)
    {provider consumer : Address} (edge : EndpointProvider left provider consumer) :
    EndpointProvider right provider consumer := by
  have matched {address name row} (active : ActiveEndpoint left address name row) :
      ∃ peer other, ActiveEndpoint right address peer other := by
    obtain ⟨birth, tag, known⟩ := active.2.2
    have member := (addressed_finish_iff_active left leftOpen leftQuiet address).mpr
      ⟨name, row, birth, active.1, active.2.1, tag, known⟩
    obtain ⟨peer, other, otherBirth, present, ready, stamp, addressed⟩ :=
      (addressed_finish_iff_active right rightOpen rightQuiet address).mp (events.mem_iff.mp member)
    exact ⟨peer, other, present, ready, otherBirth, stamp, addressed⟩
  obtain ⟨name, actor, row, other, key, source, target, provides, requires⟩ := edge
  obtain ⟨peer, peerRow, first⟩ := matched source
  obtain ⟨consumerPeer, consumerRow, second⟩ := matched target
  exact ⟨peer, consumerPeer, peerRow, consumerRow, key, first, second,
    (components source first) ▸ provides, (components target second) ▸ requires⟩

theorem endpoint_provider_chain_of_comparison {otherLast : Nat}
    {left : Trace program last} {right : Trace program otherLast}
    (leftOpen : ¬ Nonempty (ClosedEpisode left)) (leftQuiet : Progress.Quiet (left.state last))
    (rightOpen : ¬ Nonempty (ClosedEpisode right)) (rightQuiet : Progress.Quiet (right.state otherLast))
    (events : (addressedEvents left).Perm (addressedEvents right))
    (components : ∀ {address name peer row other},
      ActiveEndpoint left address name row → ActiveEndpoint right address peer other → row.component = other.component)
    {provider consumer : Address} (chain : Relation.TransGen (EndpointProvider left) provider consumer) :
    Relation.TransGen (EndpointProvider right) provider consumer := by
  have transport {source target} (edge : EndpointProvider left source target) :
      EndpointProvider right source target :=
    endpoint_provider_of_comparison leftOpen leftQuiet rightOpen rightQuiet events components edge
  induction chain with
  | single edge => exact .single (transport edge)
  | tail _ edge ih => exact .tail ih (transport edge)

theorem addressedEvents_congr (first second : Trace program last)
    (agrees : ∀ cut, cut < last → addressedEventAt first cut = addressedEventAt second cut) :
    addressedEvents first = addressedEvents second := by
  exact List.map_congr_left (fun cut member => agrees cut (List.mem_range.mp member))

private theorem perm_of_nodup_subset_same_length {α : Type u} {first second : List α}
    (distinct : first.Nodup) (included : first ⊆ second) (size : first.length = second.length) : first.Perm second := by
  induction first generalizing second with
  | nil => exact (List.length_eq_zero_iff.mp size.symm).symm ▸ .rfl
  | cons event rest ih =>
    obtain ⟨prefixCuts, suffixCuts, places⟩ := List.append_of_mem (included List.mem_cons_self)
    obtain ⟨newEvent, tailDistinct⟩ := List.nodup_cons.mp distinct
    have tailIncluded : rest ⊆ prefixCuts ++ suffixCuts := by
      intro item seen
      have member := included (List.mem_cons_of_mem _ seen)
      rw [places, List.mem_append, List.mem_cons] at member
      rcases member with prefixMember | same | suffixMember
      · exact List.mem_append_left _ prefixMember
      · exact False.elim (newEvent (same ▸ seen))
      · exact List.mem_append_right _ suffixMember
    have tailSize : rest.length = (prefixCuts ++ suffixCuts).length := by
      rw [places, List.length_append] at size
      simp at size ⊢
      omega
    rw [places]
    exact (List.Perm.cons event (ih tailDistinct tailIncluded tailSize)).trans List.perm_middle.symm

/-- An injective source-stamp map at the same length preserves each
addressed event occurrence, including repeated labels. -/
theorem addressedEvents_perm_of_stable {original moved : Trace program last} {expand : Nat → Nat}
    (stable : StableActorAddresses original moved expand) : (addressedEvents moved).Perm (addressedEvents original) := by
  let source (cut : Nat) := expand (cut + 1) - 1
  have bounded (cut : Nat) (inside : cut < last) : source cut < last := by
    obtain ⟨positive, upper⟩ := stable.retained.stamp cut inside
    dsimp [source]
    omega
  have once : ((List.range last).map source).Nodup := by
    apply List.pairwise_map.mpr
    refine List.Pairwise.imp_of_mem ?_ (List.nodup_range (n := last))
    intro a b first second distinct same
    obtain ⟨positiveA, _⟩ := stable.retained.stamp a (List.mem_range.mp first)
    obtain ⟨positiveB, _⟩ := stable.retained.stamp b (List.mem_range.mp second)
    have stamps := stable.retained.injective (by dsimp [source] at same; omega : expand (a + 1) = expand (b + 1))
    exact distinct (Nat.add_right_cancel stamps)
  have indices : ((List.range last).map source).Perm (List.range last) := by
    apply perm_of_nodup_subset_same_length once (fun i member => ?_) (List.length_map _)
    obtain ⟨cut, inside, rfl⟩ := List.mem_map.mp member
    exact List.mem_range.mpr (bounded cut (List.mem_range.mp inside))
  have labels : addressedEvents moved = ((List.range last).map source).map (addressedEventAt original) := by
    unfold addressedEvents
    rw [List.map_map]
    apply List.map_congr_left
    intro cut inside
    exact stable_addressed_event stable (List.mem_range.mp inside)
  rw [labels]
  exact indices.map _

private theorem actor_target (trace : Trace program last) (cut : Nat) :
    targetAt trace cut (trace.actor cut) = (actorAddress trace cut).bind (fun path =>
      ((trace.state cut (trace.actor cut)).map Fiber.component).map (fun component => (path, component))) := by
  unfold targetAt actorAddress
  cases tag : (trace.notes cut).1 (trace.actor cut) with
  | none => rfl
  | some birth =>
    cases addressOf trace birth <;> cases trace.state cut (trace.actor cut) <;> rfl

/-- The addressed commands retain both their recursive targets and the
entire component payload at each exchanged cut. -/
theorem stable_addressed_command {first second : Nat} {original : Trace program first} {moved : Trace program second}
    {expand : Nat → Nat} (stable : StableActorAddresses original moved expand) {cut : Nat} (bound : cut < second) :
    commandAt moved cut = commandAt original (expand (cut + 1) - 1) := by
  let source := expand (cut + 1) - 1
  have label : moved.event cut = original.event source := stable.retained.label cut bound
  have components := congrArg Prod.snd (stable.retained.actor cut bound)
  change (moved.state cut (moved.actor cut)).map Fiber.component =
    (original.state source (original.actor source)).map Fiber.component at components
  have addresses : actorAddress moved cut = actorAddress original source := stable_actor_address stable bound
  have targets : targetAt moved cut (moved.actor cut) = targetAt original source (original.actor source) := by
    rw [actor_target, actor_target, addresses, components]
  change commandAt moved cut = commandAt original source
  unfold commandAt
  rw [label]
  cases event : original.event source with
  | lifecycle => rfl
  | command command =>
    have leftActor : moved.actor cut = command.actor := by simp [Trace.actor, label, event, Vestigial.eventActor]
    have rightActor : original.actor source = command.actor := by simp [Trace.actor, event, Vestigial.eventActor]
    rw [leftActor, rightActor] at targets
    cases command with
    | insert => rfl
    | retire => exact congrArg (Option.map (fun target => AddressedCommand.retire target.1 target.2)) targets
    | remove => exact congrArg (Option.map (fun target => AddressedCommand.remove target.1 target.2)) targets

private def isInsertion : Option (AddressedEvent Key Code) → Bool
  | some (.insert _) => true
  | _ => false

private theorem insertion_test (trace : Trace program last) (cut : Nat) :
    isInsertion (addressedEventAt trace cut) = isRootInsertion trace cut := by
  cases event : trace.event cut with
  | lifecycle kind actor =>
    cases tag : actorAddress trace cut <;> simp [isInsertion, isRootInsertion, addressedEventAt, event, tag]
  | command command =>
    cases command <;> cases tag : actorAddress trace cut <;> simp [isInsertion, isRootInsertion, addressedEventAt, event, tag]

private def isStageOf (path : Address) : Option (AddressedEvent Key Code) → Bool
  | some (.lifecycle kind actor) => EpisodeSelection.canBirth kind.rule && actor == path
  | _ => false

private theorem stage_test (trace : Trace program last) {birth : Nat} {path : Address} (address : Addressed trace birth path)
    {cut : Nat} (bounded : cut < last) :
    isStageOf path (addressedEventAt trace cut) = isParentStage trace birth cut := by
  cases label : trace.event cut with
  | command command =>
    cases command <;> cases tag : actorAddress trace cut <;>
      simp [isStageOf, addressedEventAt, isParentStage, Trace.rule, label, tag, eventRule,
        ExchangeReplay.commandRule, EpisodeSelection.canBirth]
  | lifecycle kind actor =>
    simp only [addressedEventAt, label]
    have stepKind : trace.rule cut = kind.rule := by simp [Trace.rule, label, eventRule]
    rw [isParentStage, stepKind]
    cases tagged : (trace.notes cut).1 (trace.actor cut) with
    | none => simp [isStageOf, actorAddress, tagged]
    | some recorded =>
      obtain ⟨other, actual⟩ := exists_address trace (recorded_birth trace (Nat.le_of_lt bounded) tagged).1
      have actorPath := (actorAddress_eq_some trace).mpr ⟨recorded, tagged, actual⟩
      rw [actorPath]
      by_cases equal : recorded = birth
      · subst recorded
        rw [actual.unique address]
        simp [isStageOf]
      · have different : other ≠ path := fun same => equal (actual.injective address same)
        simp [isStageOf, beq_eq_false_iff_ne.mpr equal, beq_eq_false_iff_ne.mpr different]

private theorem count_congr {left right : Nat → Bool} {time : Nat} (agrees : ∀ i, i < time → left i = right i) :
    occurrencesBefore left time = occurrencesBefore right time := by
  induction time with
  | zero => rfl
  | succ time ih =>
    rw [occurrencesBefore, occurrencesBefore, ih (fun i inside => agrees i (by omega)), agrees time (by omega)]

/-- The matched prefix counts the same allocating stages of a parent,
even if the live names or birth indices are different. -/
theorem parent_stage_count_of_matched_prefix {rightLength common : Nat}
    (left : Trace program last) (right : Trace program rightLength)
    (leftBound : common ≤ last) (rightBound : common ≤ rightLength)
    (schedule : ∀ i, i < common → addressedEventAt left i = addressedEventAt right i)
    {first second : Nat} {path : Address} (a : Addressed left first path) (b : Addressed right second path) :
    occurrencesBefore (isParentStage left first) common = occurrencesBefore (isParentStage right second) common := by
  apply count_congr
  intro cut inside
  rw [← stage_test left a (by omega), ← stage_test right b (by omega), schedule cut inside]

private theorem same_occurrence {left right : Nat → Bool} {i j limit : Nat}
    (agrees : ∀ t, t < limit → left t = right t) (ro : j < limit)
    (leftHit : left i = true) (rightHit : right j = true)
    (ordinals : occurrencesBefore left i = occurrencesBefore right j) : i = j := by
  have counts : occurrencesBefore left j = occurrencesBefore right j :=
    count_congr (fun t earlier => agrees t (by omega))
  exact occurrence_unique left leftHit ((agrees j ro).trans rightHit) (ordinals.trans counts.symm)

/-- An ordered address sequence determines every actual birth stamp. For
children it identifies the allocating stage by its parent's address and
the stage ordinal, even when the two names drawn at that stage differ. -/
theorem birth_stamp_of_ordered_addresses {rightLength common : Nat} (left : Trace program last)
    (right : Trace program rightLength) (leftBound : common ≤ last) (rightBound : common ≤ rightLength)
    (schedule : ∀ cut, cut < common → addressedEventAt left cut = addressedEventAt right cut)
    {first second : Nat} {path : Address} (a : Addressed left first path) (b : Addressed right second path)
    (within : second ≤ common) :
    first = second := by
  generalize pathEq : path = otherPath at b
  cases a with
  | @root i _ _ bounded event =>
    cases b with
    | @root j _ _ later newEvent =>
      have ordinal : i = j := same_occurrence (limit := common)
        (fun t inside => by rw [← insertion_test left, ← insertion_test right, schedule t inside]) (by omega : j < common)
        (by simp [isRootInsertion, event]) (by simp [isRootInsertion, newEvent]) (Address.root.inj pathEq)
      exact congrArg Nat.succ ordinal
    | child => cases pathEq
  | @child i parentBirth _ parent bounded rule _ _ tag known =>
    cases b with
    | @child j otherBirth _ otherParent later otherRule _ _ otherTag otherKnown =>
      obtain ⟨rfl, same⟩ := Address.child.inj pathEq
      have ordinal : i = j := same_occurrence (limit := common)
        (fun t inside => by
          rw [← stage_test left known (by omega), ← stage_test right otherKnown (by omega), schedule t inside])
        (by omega : j < common) (by simp [isParentStage, rule, tag]) (by simp [isParentStage, otherRule, otherTag]) same
      exact congrArg Nat.succ ordinal
    | root => cases pathEq

omit [DecidableEq Key] in
private theorem stage_owner_unique {event : Option (AddressedEvent Key Code)} {a b : Address}
    (left : isStageOf a event = true) (right : isStageOf b event = true) : a = b := by
  cases event with
  | none => cases left
  | some event =>
    cases event <;> simp [isStageOf, Bool.and_eq_true, beq_iff_eq] at left right
    exact left.2.symm.trans right.2

omit [DecidableEq Key] in
private theorem insertion_excludes_stage {event : Option (AddressedEvent Key Code)} {path : Address}
    (inserted : isInsertion event = true) (performed : isStageOf path event = true) : False := by
  cases event with
  | none => cases inserted
  | some event => cases event <;> simp [isInsertion, isStageOf] at inserted performed

/-- Two equal addressed prefixes assign the same address to a birth at
the same position. This also identifies live targets before their next
command has moved into the matched prefix. -/
theorem address_of_matched_birth {rightLength common : Nat} (left : Trace program last)
    (right : Trace program rightLength)
    (schedule : ∀ i, i < common → addressedEventAt left i = addressedEventAt right i)
    {stamp : Nat} {a b : Address} (within : stamp ≤ common)
    (first : Addressed left stamp a) (second : Addressed right stamp b) : a = b := by
  generalize indexEq : stamp = otherStamp at second
  cases first with
  | @root i _ _ bounded event =>
    cases second with
    | @root j _ _ later otherEvent =>
      have same : i = j := Nat.succ.inj indexEq
      subst j
      apply congrArg Address.root
      exact count_congr (fun cut inside => by
        rw [← insertion_test left, ← insertion_test right, schedule cut (by omega)])
    | @child j birth _ path later rule _ _ tag known =>
      have same : i = j := Nat.succ.inj indexEq
      subst j
      have insertion : isInsertion (addressedEventAt left i) = true := by rw [insertion_test]; simp [isRootInsertion, event]
      have stage : isStageOf path (addressedEventAt right i) = true := by
        rw [stage_test right known later]
        simp [isParentStage, rule, tag]
      rw [schedule i (by omega)] at insertion
      exact False.elim (insertion_excludes_stage insertion stage)
  | @child i birth _ path bounded rule _ _ tag known =>
    have stage : isStageOf path (addressedEventAt left i) = true := by
      rw [stage_test left known bounded]
      simp [isParentStage, rule, tag]
    cases second with
    | @root j _ _ later otherEvent =>
      have same : i = j := Nat.succ.inj indexEq
      subst j
      have insertion : isInsertion (addressedEventAt right i) = true := by rw [insertion_test]; simp [isRootInsertion, otherEvent]
      rw [schedule i (by omega)] at stage
      exact False.elim (insertion_excludes_stage insertion stage)
    | @child j otherBirth _ otherPath later otherRule _ _ otherTag otherKnown =>
      have same : i = j := Nat.succ.inj indexEq
      subst j
      have otherStage : isStageOf otherPath (addressedEventAt right i) = true := by
        rw [stage_test right otherKnown later]
        simp [isParentStage, otherRule, otherTag]
      rw [schedule i (by omega)] at stage
      have samePath := stage_owner_unique stage otherStage
      subst otherPath
      apply congrArg (Address.child path)
      exact count_congr (fun cut inside => by
        rw [← stage_test left known (by omega), ← stage_test right otherKnown (by omega), schedule cut (by omega)])

/-- A matched full schedule transports an active endpoint row at its
birth address, keeping the declaration and the exact table. -/
theorem active_endpoint_of_matched_schedule {left right : Trace program last}
    (order : ∀ i, i < last → addressedEventAt left i = addressedEventAt right i)
    (agreement : CutAgreement left right last) {address : Address} {name : Name}
    {row : Fiber Name Key Value Code (Inverse Name Key Value) Error}
    (first : ActiveEndpoint left address name row) :
    ∃ peer other, ActiveEndpoint right address peer other ∧
      row.component = other.component ∧ row.table = other.table := by
  obtain ⟨names, states, tags, _⟩ := agreement
  obtain ⟨birth, stamp, known⟩ := first.2.2
  have present := first.1
  have available := first.2.1
  have compared := congrFun states (names.toFun name)
  rw [Renaming.registry_at] at compared
  cases found : right.state last (names.toFun name) with
  | none => simp [GuardedCutState.project, present, found] at compared
  | some other =>
    have rows : Renaming.fiber names (GuardedCutState.projectFiber name row) =
        GuardedCutState.projectFiber (names.toFun name) other := by
      simpa [GuardedCutState.project, present, found] using compared
    have phase := congrArg Fiber.phase rows
    have ready : other.phase.available := by
      cases old : row.phase <;> cases new : other.phase <;>
        simp [Phase.available, GuardedCutState.projectFiber, GuardedCutState.projectPhase,
          Renaming.fiber, Renaming.phase, old, new] at available phase ⊢
    have movedStamp := (tags name).trans stamp
    obtain ⟨otherAddress, addressed⟩ := exists_address right (recorded_birth right (Nat.le_refl _) movedStamp).1
    have same := address_of_matched_birth left right order
      (recorded_birth left (Nat.le_refl _) stamp).2 known addressed
    have components := congrArg Fiber.component rows
    have tables := congrArg Fiber.table rows
    exact ⟨names.toFun name, other, ⟨found, ready, birth, movedStamp, same.symm ▸ addressed⟩, components, tables⟩

private inductive AddressedCut (trace : Trace program last) (cut : Nat) : AddressedEvent Key Code → Prop
  | insert {name component} : trace.event cut = .command (.insert name component) → AddressedCut trace cut (.insert component)
  | retire {name birth path} : trace.event cut = .command (.retire name) →
      (trace.notes cut).1 name = some birth → Addressed trace birth path → AddressedCut trace cut (.retire path)
  | remove {name birth path} : trace.event cut = .command (.remove name) →
      (trace.notes cut).1 name = some birth → Addressed trace birth path → AddressedCut trace cut (.remove path)
  | lifecycle {name birth path kind} : trace.event cut = .lifecycle kind name → Transposition.Activation kind.rule →
      (trace.notes cut).1 name = some birth → Addressed trace birth path → AddressedCut trace cut (.lifecycle kind path)

private theorem addressed_cut (trace : Trace program last) {cut : Nat} (bounded : cut < last)
    (activation : ∀ {kind name}, trace.event cut = .lifecycle kind name → Transposition.Activation kind.rule) :
    ∃ event, addressedEventAt trace cut = some event ∧ AddressedCut trace cut event := by
  have known {name : Name} {birth : Nat} (actor : trace.actor cut = name) (tag : (trace.notes cut).1 name = some birth) :
      ∃ path, Addressed trace birth path ∧ actorAddress trace cut = some path := by
    obtain ⟨path, address⟩ := exists_address trace (recorded_birth trace (Nat.le_of_lt bounded) tag).1
    exact ⟨path, address, (actorAddress_eq_some trace).mpr ⟨birth, actor.symm ▸ tag, address⟩⟩
  cases event : trace.event cut with
  | command command =>
    have actor : trace.actor cut = command.actor := by simp [Trace.actor, event, Vestigial.eventActor]
    cases command with
    | insert name component => exact ⟨_, by simp [addressedEventAt, event], .insert event⟩
    | retire name =>
      obtain ⟨_, _, _, _, _, tag, _⟩ := trace.retire_remove_birth bounded (.inl event)
      obtain ⟨_, address, resolved⟩ := known actor tag
      exact ⟨_, by simp [addressedEventAt, event, resolved], .retire event tag address⟩
    | remove name =>
      obtain ⟨_, _, _, _, _, tag, _⟩ := trace.retire_remove_birth bounded (.inr event)
      obtain ⟨_, address, resolved⟩ := known actor tag
      exact ⟨_, by simp [addressedEventAt, event, resolved], .remove event tag address⟩
  | lifecycle kind name =>
    have active := activation event
    have ran := (trace.step cut bounded).1
    rw [event] at ran
    have step : Labeled.Step program kind.rule name (trace.state cut) (trace.state (cut + 1)) := by
      cases kind <;> first | exact ran | simp [Lifecycle.rule, Transposition.Activation] at active
    obtain ⟨row, _, found, _, _⟩ := Transposition.activation_source program step active
    have actor : trace.actor cut = name := by simp [Trace.actor, event, Vestigial.eventActor]
    cases tag : (trace.notes cut).1 name with
    | none =>
      have vacant := (trace.births_agree cut (Nat.le_of_lt bounded) name).mp tag
      rw [found] at vacant
      cases vacant
    | some birth =>
      obtain ⟨_, address, resolved⟩ := known actor tag
      exact ⟨_, by simp [addressedEventAt, event, resolved], .lifecycle event active tag address⟩

/-- Two aligned prefixes determine the correspondence at their next
addressed event. Every actor tested there was born during the prefix. -/
theorem match_addressed_event {rightLength cut : Nat} (left : Trace program last) (right : Trace program rightLength)
    (leftBound : cut < last) (rightBound : cut < rightLength)
    (leftActivation : ∀ {kind name}, left.event cut = .lifecycle kind name → Transposition.Activation kind.rule)
    (rightActivation : ∀ {kind name}, right.event cut = .lifecycle kind name → Transposition.Activation kind.rule)
    (past : ∀ i, i < cut → addressedEventAt left i = addressedEventAt right i)
    (current : addressedEventAt left cut = addressedEventAt right cut) : OpenEventsAgree left right cut := by
  obtain ⟨key, found, first⟩ := addressed_cut left leftBound leftActivation
  obtain ⟨other, present, second⟩ := addressed_cut right rightBound rightActivation
  have same := Option.some.inj (found.symm.trans (current.trans present))
  subst other
  have birth {l r : Nat} {path : Address} {name : Name} (a : Addressed left l path) (b : Addressed right r path)
      (tag : (right.notes cut).1 name = some r) : l = r :=
    birth_stamp_of_ordered_addresses left right (Nat.le_of_lt leftBound) (Nat.le_of_lt rightBound) past a b
      (recorded_birth right (Nat.le_of_lt rightBound) tag).2
  cases first with
  | insert event =>
    cases second with
    | insert later => simp [OpenEventsAgree, event, later]
  | retire event tag known =>
    cases second with
    | retire later otherTag otherKnown => simp [OpenEventsAgree, event, later, tag, otherTag, birth known otherKnown otherTag]
  | remove event tag known =>
    cases second with
    | remove later otherTag otherKnown => simp [OpenEventsAgree, event, later, tag, otherTag, birth known otherKnown otherTag]
  | lifecycle event active tag known =>
    cases second with
    | lifecycle later _ otherTag otherKnown =>
      simp [OpenEventsAgree, event, later, active, tag, otherTag, birth known otherKnown otherTag]

/-- An addressed event order supplies the schedule premise of cut matching. -/
theorem match_addressed_events (left right : Trace program last)
    (leftActivation : ∀ {cut kind name}, cut < last → left.event cut = .lifecycle kind name → Transposition.Activation kind.rule)
    (rightActivation : ∀ {cut kind name}, cut < last → right.event cut = .lifecycle kind name → Transposition.Activation kind.rule)
    (ordered : ∀ cut, cut < last → addressedEventAt left cut = addressedEventAt right cut) :
    ∀ cut, cut < last → OpenEventsAgree left right cut := by
  intro cut bounded
  exact match_addressed_event left right bounded bounded (leftActivation bounded) (rightActivation bounded)
    (fun i prior => ordered i (Nat.lt_trans prior bounded)) (ordered cut bounded)

/-- Extend the actual matched cuts after identifying one more event by
its address. The fresh-name permutation may change at the new cut. -/
theorem advance_addressed_cut {rightLength cut : Nat} (left : Trace program last) (right : Trace program rightLength)
    (leftBound : cut < last) (rightBound : cut < rightLength) (related : CutAgreement left right cut)
    (stable : ChildContinuations program)
    (leftActivation : ∀ {kind name}, left.event cut = .lifecycle kind name → Transposition.Activation kind.rule)
    (rightActivation : ∀ {kind name}, right.event cut = .lifecycle kind name → Transposition.Activation kind.rule)
    (past : ∀ i, i < cut → addressedEventAt left i = addressedEventAt right i)
    (current : addressedEventAt left cut = addressedEventAt right cut) : CutAgreement left right (cut + 1) :=
  CutAgreement.advance left right leftBound rightBound related
    (match_addressed_event left right leftBound rightBound leftActivation rightActivation past current) stable

theorem open_events_of_ordered_addresses (left right : Trace program last)
    (leftOpen : ¬ Nonempty (ClosedEpisode left)) (rightOpen : ¬ Nonempty (ClosedEpisode right))
    (leftQuiet : Progress.Quiet (left.state last)) (rightQuiet : Progress.Quiet (right.state last))
    (ordered : ∀ cut, cut < last → addressedEventAt left cut = addressedEventAt right cut) :
    ∀ cut, cut < last → OpenEventsAgree left right cut :=
  match_addressed_events left right (fun bounded event => (left.activation_at leftOpen leftQuiet bounded event).1)
    (fun bounded event => (right.activation_at rightOpen rightQuiet bounded event).1) ordered

end Cordis.Repairs.GuardedAddressSchedule
