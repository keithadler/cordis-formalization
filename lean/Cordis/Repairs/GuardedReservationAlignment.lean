import Cordis.Repairs.GuardedAddressSchedule
import Cordis.Repairs.GuardedReservationOrder
import Cordis.Repairs.GuardedActivationOccurrence

/-! A matching birth at the next cut rules out a later release of a
competing key as a prerequisite of that birth in the other schedule. -/
namespace Cordis.Repairs.GuardedReservationAlignment
open Calculus Stages LegalHistory GuardedHistory GuardedBirthAddresses GuardedAddressSchedule
open GuardedReservationOrder
open GuardedBirthMatching (recorded_birth born_unique)
open GuardedLandingMatching (activation_landing)
open GuardedScheduleMatching (CutAgreement)

universe u
variable {Name Key Value Code Error : Type u} [DecidableEq Name] [DecidableEq Key]
variable {program : Code → Instruction Name Key Value Code Error} {last otherLast : Nat}
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error

private def eventRemoval : Option (AddressedEvent Key Code) → Option Address
  | some (.remove address) => some address
  | _ => none

private theorem release_of_addressed_event (trace : Trace program last) {cut : Nat} (bounded : cut < last) :
    eventRemoval (addressedEventAt trace cut) = removalAddress trace cut := by
  cases event : trace.event cut with
  | lifecycle kind name =>
    cases tag : actorAddress trace cut <;> simp [eventRemoval, addressedEventAt, removalAddress, commandAt, event, tag]
  | command command =>
    rw [addressedEventAt_of_command trace bounded event]
    unfold removalAddress
    cases entry : commandAt trace cut with
    | none => rfl
    | some key => cases key <;> rfl

/-- Matched addressed prefixes have exactly the same releases. -/
theorem releases_of_matched_prefix (left : Trace program last) (right : Trace program otherLast) {cut : Nat}
    (leftBound : cut ≤ last) (rightBound : cut ≤ otherLast)
    (past : ∀ time, time < cut → addressedEventAt left time = addressedEventAt right time) :
    releasesBefore left cut = releasesBefore right cut := by
  unfold releasesBefore
  have mapEq : (List.range cut).map (removalAddress left) = (List.range cut).map (removalAddress right) := by
    apply List.map_congr_left
    intro time member
    have inside := List.mem_range.mp member
    rw [← release_of_addressed_event left (by omega), ← release_of_addressed_event right (by omega), past time inside]
  simpa only [List.filterMap_map, Function.id_comp] using congrArg (List.filterMap id) mapEq

/-- A matched prefix contains the exact same addressed release required
by a reused draw, even if the other history names the row differently. -/
theorem shared_release_before_reuse (left : Trace program last) (right : Trace program otherLast)
    {first next : Nat} {name : Name}
    (earlier : GuardedBirthMatching.BornAt left name first)
    (replacement : GuardedBirthMatching.BornAt left name next) (ordered : first < next)
    (rightBound : next - 1 ≤ otherLast)
    (past : ∀ time, time < next - 1 → addressedEventAt left time = addressedEventAt right time) :
    ∃ final address, final < next - 1 ∧ Addressed left first address ∧
      removalAddress left final = some address ∧ removalAddress right final = some address := by
  obtain ⟨final, address, before, origin, released, _⟩ :=
    addressed_release_before_reuse left earlier replacement ordered
  have leftBound := replacement.2.1
  have same : removalAddress left final = removalAddress right final := by
    rw [← release_of_addressed_event left (by omega), ← release_of_addressed_event right (by omega),
      past final before]
  exact ⟨final, address, before, origin, released, same.symm.trans released⟩

omit [DecidableEq Name] [DecidableEq Key] in
/-- Renaming the projected registry preserves vacancies. -/
theorem vacancy_of_renamed_cut {before after : R} {p : Renaming.Permutation Name}
    (states : Renaming.registry p (GuardedCutState.project before) = GuardedCutState.project after)
    (name : Name) : after (p.toFun name) = none ↔ before name = none := by
  rw [← GuardedCutState.project_present, ← states, Renaming.registry_at]
  cases found : before name <;> simp [GuardedCutState.project, found]

/-- Renaming a matched cut cannot change its available capacity. -/
theorem vacancy_of_matched_cut (left : Trace program last) (right : Trace program otherLast)
    {cut : Nat} (agreement : CutAgreement left right cut) :
    (∃ name, left.state cut name = none) ↔ (∃ name, right.state cut name = none) := by
  obtain ⟨p, states, _, _⟩ := agreement
  constructor
  · rintro ⟨name, vacant⟩
    exact ⟨p.toFun name, (vacancy_of_renamed_cut states name).mpr vacant⟩
  · rintro ⟨name, vacant⟩
    exact ⟨p.invFun name, (vacancy_of_renamed_cut states _).mp (by simpa only [p.right_inv] using vacant)⟩

/-- A command-free block retains the actual incarnation and declaration
of every row present at its beginning. -/
theorem reservation_survives_activation_block (trace : Trace program last)
    {start span : Nat} (bounded : start + span ≤ last)
    (block : ∀ i, start ≤ i → i < start + span → ∃ kind actor, trace.event i = .lifecycle kind actor)
    {name : Name} {row : F} (found : trace.state start name = some row) :
    ∃ later, trace.state (start + span) name = some later ∧ row.component = later.component ∧
      (trace.notes (start + span)).1 name = (trace.notes start).1 name := by
  induction span with
  | zero => exact ⟨row, found, rfl, rfl⟩
  | succ span ih =>
    obtain ⟨prior, priorAt, component, tag⟩ := ih (by omega) (fun i lo hi => block i lo (by omega))
    have inside : start + span < last := by omega
    have present : trace.state (start + span + 1) name ≠ none := by
      intro absent
      have removal := removal_at_gap trace inside (by simp [priorAt]) absent
      obtain ⟨kind, actor, event⟩ := block (start + span) (by omega) (by omega)
      rw [event] at removal
      cases removal
    cases nextAt : trace.state (start + span + 1) name with
    | none => exact False.elim (present nextAt)
    | some later =>
      have same := transition_stable (trace.step (start + span) inside).1 name prior later priorAt nextAt
      have stamp : (trace.notes (start + span + 1)).1 name = (trace.notes (start + span)).1 name := by
        rw [trace.notes_eq _ (by omega), trace.notes_eq (start + span) (by omega)]
        exact Incarnation.birth_stays trace.state name (start + span) (by simp [priorAt]) present
      exact ⟨later, nextAt, component.trans same.1, stamp.trans tag⟩

/-- A disabled Begin in a command-free block exposes the actual
provider edge that enabled its selected target before it ran. -/
theorem delayed_begin_provider_edge (trace : Trace program last)
    (opened : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    {start span : Nat} (bounded : start + span < last) {actor : Name} {row : F}
    (found : trace.state start actor = some row)
    (disabled : ∀ view, ¬ Target (trace.state start) actor view)
    (event : trace.event (start + span) = .lifecycle .begin actor)
    (block : ∀ i, start ≤ i → i < start + span →
      ∃ kind name, trace.event i = .lifecycle kind name ∧ actor ≠ name) :
    ∃ cut provider consumer, start ≤ cut ∧ cut < start + span ∧
      addressedEventAt trace cut = some (.lifecycle .finish provider) ∧
      actorAddress trace (start + span) = some consumer ∧ EndpointProvider trace provider consumer := by
  obtain ⟨before, after, view, beforeAt, ready, afterAt, committed, same⟩ := begin_source_target bounded event
  obtain ⟨cut, current, key, lower, upper, finish, currentAt, required, _, target⟩ :=
    trace.selected_target_requires_provider_finish opened quiet (Nat.le_of_lt bounded)
      (by simp [found]) (disabled view) ready block
  obtain ⟨earlier, present, prior, _⟩ := reservation_survives_activation_block trace
    (span := cut + 1 - start) (by omega)
    (fun i lo hi => by
      obtain ⟨kind, name, label, _⟩ := block i lo (by omega)
      exact ⟨kind, name, label⟩) found
  have atCut : start + (cut + 1 - start) = cut + 1 := by omega
  rw [atCut] at present
  have currentPart : row.component = current.component := prior.trans
    (congrArg Fiber.component (Option.some.inj (present.symm.trans currentAt)))
  obtain ⟨later, laterAt, laterPart, _⟩ := reservation_survives_activation_block trace
    (Nat.le_of_lt bounded) (fun i lo hi => by
      obtain ⟨kind, name, label, _⟩ := block i lo hi
      exact ⟨kind, name, label⟩) found
  have beforePart := laterPart.trans
    (congrArg Fiber.component (Option.some.inj (laterAt.symm.trans beforeAt)))
  have needs : before.component.requires key = true := beforePart ▸ (currentPart.symm ▸ required)
  obtain ⟨_, consumer, _, resolved, _⟩ := active_endpoint_of_activation trace opened quiet bounded event
  obtain ⟨birth, resolvedAt, known⟩ := (actorAddress_eq_some trace).mp resolved
  have actorEq : trace.actor (start + span) = actor := by simp [Trace.actor, Vestigial.eventActor, event]
  have stamp := trace.activation_stamp_through opened quiet bounded (Nat.le_succ _) (Nat.succ_le_of_lt bounded) event
  have afterTag := stamp.symm.trans (actorEq ▸ resolvedAt)
  obtain ⟨endpoint, consumerActive, component⟩ :=
    active_endpoint_of_installed trace opened quiet (Nat.succ_le_of_lt bounded) afterAt committed afterTag known
  obtain ⟨_, providerAt, available, provision⟩ :=
    selected_provider_at_cut (by omega : cut + 1 ≤ last) currentAt required target
  obtain ⟨providerBirth, provider, providerRow, tag, address, providerActive, declaration, _⟩ :=
    active_endpoint_of_cut trace opened quiet (by omega : cut + 1 ≤ last) providerAt available
  obtain ⟨_, _, _, sameBirth⟩ := trace.finished_row_at_cut opened quiet
    (Nat.lt_succ_self cut) (by omega : cut + 1 ≤ last) finish
  exact ⟨cut, provider, _, lower, upper,
    (addressed_finish_at trace).mpr ⟨_, providerBirth, finish, sameBirth.symm.trans tag, address⟩,
    (actorAddress_eq_some trace).mpr ⟨birth, resolvedAt, known⟩,
    view key, actor, providerRow, endpoint, key, providerActive, consumerActive,
    declaration.symm ▸ provision, (component.trans same).symm ▸ needs⟩

/-- An actor present but disabled at the start of a command-free
block has an intervening provider Finish before a later activation. -/
theorem disabled_activation_provider (trace : Trace program last)
    (opened : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    {start alloc parentBirth : Nat} {parent : Address} {actor : Name} {kind : Lifecycle}
    (lower : start ≤ alloc) (bounded : alloc < last)
    (event : trace.event alloc = .lifecycle kind actor)
    (tag : (trace.notes alloc).1 actor = some parentBirth) (known : Addressed trace parentBirth parent)
    {row : F} (found : trace.state start actor = some row)
    (disabled : ∀ view, ¬ Target (trace.state start) actor view)
    (block : ∀ i, start ≤ i → i < alloc → ∃ kind name, trace.event i = .lifecycle kind name) :
    ∃ cut provider, start ≤ cut ∧ cut < alloc ∧
      addressedEventAt trace cut = some (.lifecycle .finish provider) ∧ EndpointProvider trace provider parent := by
  obtain ⟨opening, before, begins⟩ := trace.opening_of_activation opened quiet bounded event
  have afterStart : start ≤ opening := by
    apply Nat.le_of_not_gt
    intro earlier
    obtain ⟨activation, step⟩ := trace.activation_at opened quiet (by omega : opening < last) begins
    have installed := activation_installs_view step activation
    have retained := trace.installed_through opened actor (by omega : opening + 1 ≤ start)
      (by omega : start ≤ last) installed
    obtain ⟨view, target⟩ := trace.installed_has_target opened quiet (by omega : start ≤ last)
      (fun absent => installed (retained.symm.trans absent))
    exact disabled view target
  have beginsAt : start + (opening - start) = opening := by omega
  have foreignBlock (i : Nat) (lo : start ≤ i) (hi : i < opening) :
      ∃ label name, trace.event i = .lifecycle label name ∧ actor ≠ name := by
    obtain ⟨label, name, step⟩ := block i lo (by omega)
    refine ⟨label, name, step, ?_⟩
    rintro rfl
    obtain ⟨other, earlier, openingEvent⟩ := trace.opening_of_activation opened quiet (by omega : i < last) step
    have same := trace.begin_unique opened (by omega) (by omega) openingEvent begins
    omega
  obtain ⟨finish, provider, consumer, fromStart, beforeBegin, addressed, resolved, edge⟩ :=
    delayed_begin_provider_edge trace opened quiet (span := opening - start) (by omega)
      found disabled (by simpa only [beginsAt] using begins)
      (fun i lo hi => foreignBlock i lo (by omega))
  rw [beginsAt] at resolved beforeBegin
  have sameStamp := trace.activation_stamp_through opened quiet (by omega : opening < last)
    before (Nat.le_of_lt bounded) begins
  have atBegin : trace.actor opening = actor := by simp [Trace.actor, Vestigial.eventActor, begins]
  have named := (actorAddress_eq_some trace).mpr ⟨parentBirth, atBegin.symm ▸ (sameStamp.trans tag), known⟩
  have same := Option.some.inj (resolved.symm.trans named)
  exact ⟨finish, provider, fromStart, by omega, addressed, same ▸ edge⟩

/-- If an allocating parent is present but disabled at the matched cut,
its actual allocation traces back to an intervening enabling provider. -/
theorem disabled_allocating_parent_provider (trace : Trace program last)
    (opened : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    {start birth ordinal : Nat} {parent : Address} (child : Addressed trace birth (.child parent ordinal))
    (lower : start ≤ birth - 1) {row : F}
    (found : trace.state start (trace.actor (birth - 1)) = some row)
    (disabled : ∀ view, ¬ Target (trace.state start) (trace.actor (birth - 1)) view)
    (block : ∀ i, start ≤ i → i < birth - 1 →
      ∃ kind actor, trace.event i = .lifecycle kind actor) :
    ∃ cut provider, start ≤ cut ∧ cut < birth - 1 ∧
      addressedEventAt trace cut = some (.lifecycle .finish provider) ∧ EndpointProvider trace provider parent := by
  obtain ⟨alloc, parentBirth, kind, actor, placed, bounded, event, tag, known⟩ := child.allocating_event
  have cut : alloc = birth - 1 := by omega
  have acting : trace.actor (birth - 1) = actor := by
    rw [← cut]
    simp [Trace.actor, Vestigial.eventActor, event]
  rw [acting] at found disabled
  obtain ⟨finish, provider, fromStart, earlier, addressed, edge⟩ :=
    disabled_activation_provider trace opened quiet (by omega : start ≤ alloc) bounded event tag known
      found disabled (fun i lo hi => block i lo (by omega))
  exact ⟨finish, provider, fromStart, by omega, addressed, edge⟩

/-- Follow disabled activations back through actual enabling Finishes.
The chain ends at an actor already enabled at the starting cut or at
an actor whose birth must be found inside the block. -/
theorem provider_chain_to_ready_or_birth (trace : Trace program last)
    (opened : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    {start limit : Nat} (lower : start ≤ limit) (bounded : limit < last)
    {kind : Lifecycle} {actor : Name} {consumer : Address}
    (event : trace.event limit = .lifecycle kind actor)
    (addressed : actorAddress trace limit = some consumer)
    (block : ∀ i, start ≤ i → i < limit → ∃ kind name, trace.event i = .lifecycle kind name) :
    ∃ cut label name address, start ≤ cut ∧ cut ≤ limit ∧
      trace.event cut = .lifecycle label name ∧ actorAddress trace cut = some address ∧
      (address = consumer ∨ Relation.TransGen (EndpointProvider trace) address consumer) ∧
      (trace.state start name = none ∨ ∃ view, Target (trace.state start) name view) := by
  induction limit using Nat.strongRecOn generalizing kind actor consumer with
  | ind limit ih =>
    by_cases terminal : trace.state start actor = none ∨ ∃ view, Target (trace.state start) actor view
    · exact ⟨limit, kind, actor, consumer, lower, Nat.le_refl _, event, addressed, .inl rfl, terminal⟩
    · cases found : trace.state start actor with
      | none => exact False.elim (terminal (.inl found))
      | some row =>
        have disabled : ∀ view, ¬ Target (trace.state start) actor view :=
          fun view valid => terminal (.inr ⟨view, valid⟩)
        obtain ⟨birth, tag, path⟩ := (actorAddress_eq_some trace).mp addressed
        have owner : trace.actor limit = actor := by simp [Trace.actor, Vestigial.eventActor, event]
        obtain ⟨finish, provider, fromStart, earlier, label, edge⟩ :=
          disabled_activation_provider trace opened quiet lower bounded event (owner ▸ tag) path found disabled block
        obtain ⟨providerName, providerBirth, actual, stamp, providerPath⟩ := (addressed_finish_at trace).mp label
        have providerOwner : trace.actor finish = providerName := by simp [Trace.actor, Vestigial.eventActor, actual]
        have resolved := (actorAddress_eq_some trace).mpr ⟨providerBirth, providerOwner.symm ▸ stamp, providerPath⟩
        obtain ⟨cut, label, name, address, afterStart, beforeFinish, step, atAddress, chain, ready⟩ :=
          ih finish earlier fromStart (by omega) actual resolved (fun i lo hi => block i lo (by omega))
        refine ⟨cut, label, name, address, afterStart, by omega, step, atAddress, .inr ?_, ready⟩
        rcases chain with rfl | chain
        · exact .single edge
        · exact .tail chain edge

/-- An actor absent at the start of a command-free block was born at an
actual allocating activation earlier in that block. -/
theorem allocation_before_unborn_activation (trace : Trace program last)
    {start limit : Nat} (lower : start ≤ limit) (bounded : limit < last)
    {kind : Lifecycle} {actor : Name} {address : Address}
    (event : trace.event limit = .lifecycle kind actor)
    (addressed : actorAddress trace limit = some address)
    (absent : trace.state start actor = none)
    (block : ∀ i, start ≤ i → i < limit → ∃ kind name, trace.event i = .lifecycle kind name) :
    ∃ cut label name parent ordinal,
      start ≤ cut ∧ cut < limit ∧ trace.event cut = .lifecycle label name ∧
      actorAddress trace cut = some parent ∧ address = .child parent ordinal ∧
      Addressed trace (cut + 1) address := by
  obtain ⟨birth, tag, path⟩ := (actorAddress_eq_some trace).mp addressed
  have owner : trace.actor limit = actor := by simp [Trace.actor, Vestigial.eventActor, event]
  have recorded : Incarnation.birthAt trace.state actor limit = some birth := by
    have live : (trace.notes limit).1 actor = some birth := owner ▸ tag
    rwa [trace.notes_eq limit (Nat.le_of_lt bounded)] at live
  have residency := Incarnation.resident_of_birthAt recorded
  have later : start < birth := Nat.lt_of_not_ge
    (fun early => residency.present start early lower absent)
  have before := residency.ordered
  have child : ∃ parent ordinal, address = .child parent ordinal := by
    cases path with
    | @root time name component valid insert =>
      obtain ⟨label, name, step⟩ := block time (by omega) (by omega)
      rw [insert] at step
      cases step
    | child => exact ⟨_, _, rfl⟩
  obtain ⟨parent, ordinal, rfl⟩ := child
  obtain ⟨cut, parentBirth, label, name, placed, _, allocated, parentTag, parentPath⟩ := path.allocating_event
  have parentActor : trace.actor cut = name := by simp [Trace.actor, Vestigial.eventActor, allocated]
  exact ⟨cut, label, name, parent, ordinal, by omega, by omega, allocated,
    (actorAddress_eq_some trace).mpr ⟨parentBirth, parentActor.symm ▸ parentTag, parentPath⟩, rfl, placed ▸ path⟩

/-- A prerequisite connects actual activation cuts by a provider Finish
or by the birth of the later actor at the earlier activation. -/
def ActivationPrerequisite (trace : Trace program last) (earlier later : Nat) : Prop :=
  earlier < later ∧
  ((∃ provider consumer, addressedEventAt trace earlier = some (.lifecycle .finish provider) ∧
    actorAddress trace later = some consumer ∧ EndpointProvider trace provider consumer) ∨
  (∃ parent ordinal, actorAddress trace earlier = some parent ∧
    actorAddress trace later = some (.child parent ordinal) ∧
    Addressed trace (earlier + 1) (.child parent ordinal)))

/-- A prerequisite after the matched cut transfers to the peer before
the corresponding later actor runs. Child allocation uses its ordinal;
provider Finish uses the actual target at the peer activation. -/
theorem ActivationPrerequisite.peer {left : Trace program last} {right : Trace program otherLast}
    (leftOpen : ¬ Nonempty (ClosedEpisode left)) (leftQuiet : Progress.Quiet (left.state last))
    (rightOpen : ¬ Nonempty (ClosedEpisode right)) (rightQuiet : Progress.Quiet (right.state otherLast))
    (events : (addressedEvents left).Perm (addressedEvents right))
    (components : ∀ {address name peer row other},
      ActiveEndpoint left address name row → ActiveEndpoint right address peer other → row.component = other.component)
    {start earlier later limit : Nat} (lower : start ≤ earlier) (leftBound : earlier < last)
    (rightStart : start ≤ limit) (rightBound : limit < otherLast)
    (past : ∀ i, i < start → addressedEventAt left i = addressedEventAt right i)
    {kind : Lifecycle} {actor : Name} (event : right.event limit = .lifecycle kind actor)
    (actors : actorAddress left later = actorAddress right limit)
    (edge : ActivationPrerequisite left earlier later) :
    ∃ cut label name, start ≤ cut ∧ cut < limit ∧ right.event cut = .lifecycle label name ∧
      actorAddress left earlier = actorAddress right cut ∧ ActivationPrerequisite right cut limit := by
  rcases edge.2 with provider | allocation
  · obtain ⟨provider, consumer, finished, consumes, supplied⟩ := provider
    have peerEdge := endpoint_provider_of_comparison leftOpen leftQuiet rightOpen rightQuiet events components supplied
    have consumerAt := actors.symm.trans consumes
    obtain ⟨cut, before, peerFinish⟩ :=
      provider_finish_before_activation right rightOpen rightQuiet rightBound event consumerAt peerEdge
    have afterStart := finish_after_matched_prefix leftOpen leftQuiet lower leftBound past finished peerFinish
    obtain ⟨leftName, leftBirth, label, live, path⟩ := (addressed_finish_at left).mp finished
    obtain ⟨name, birth, step, tag, known⟩ := (addressed_finish_at right).mp peerFinish
    have leftActor : left.actor earlier = leftName := by simp [Trace.actor, Vestigial.eventActor, label]
    have rightActor : right.actor cut = name := by simp [Trace.actor, Vestigial.eventActor, step]
    have leftAddress := (actorAddress_eq_some left).mpr ⟨leftBirth, leftActor.symm ▸ live, path⟩
    have rightAddress := (actorAddress_eq_some right).mpr ⟨birth, rightActor.symm ▸ tag, known⟩
    exact ⟨cut, .finish, name, afterStart, before, step, leftAddress.trans rightAddress.symm,
      ⟨before, .inl ⟨provider, consumer, peerFinish, consumerAt, peerEdge⟩⟩⟩
  · obtain ⟨parent, ordinal, owner, child, born⟩ := allocation
    have childAt := actors.symm.trans child
    obtain ⟨birth, tag, known⟩ := (actorAddress_eq_some right).mp childAt
    have inside := (recorded_birth right (Nat.le_of_lt rightBound) tag).2
    obtain ⟨cut, parentBirth, label, name, placed, _, allocated, parentTag, parentPath⟩ := known.allocating_event
    have afterStart : start ≤ cut := by
      apply Nat.le_of_not_gt
      intro early
      have same := birth_stamp_of_ordered_addresses left right (by omega : start ≤ last)
        (by omega : start ≤ otherLast) past born known (by omega)
      omega
    have parentActor : right.actor cut = name := by simp [Trace.actor, Vestigial.eventActor, allocated]
    have resolved := (actorAddress_eq_some right).mpr ⟨parentBirth, parentActor.symm ▸ parentTag, parentPath⟩
    exact ⟨cut, label, name, afterStart, by omega, allocated, owner.trans resolved.symm,
      ⟨by omega, .inr ⟨parent, ordinal, resolved, childAt, placed ▸ known⟩⟩⟩

theorem ActivationPrerequisite.chain_lt {trace : Trace program last} {earlier later : Nat}
    (chain : Relation.TransGen (ActivationPrerequisite trace) earlier later) : earlier < later := by
  induction chain with
  | single edge => exact edge.1
  | tail _ edge ih => exact Nat.lt_trans ih edge.1

/-- A chain transfers backwards from a peer activation even when
provider and child-birth prerequisites alternate. -/
theorem ActivationPrerequisite.peer_chain {left : Trace program last} {right : Trace program otherLast}
    (leftOpen : ¬ Nonempty (ClosedEpisode left)) (leftQuiet : Progress.Quiet (left.state last))
    (rightOpen : ¬ Nonempty (ClosedEpisode right)) (rightQuiet : Progress.Quiet (right.state otherLast))
    (events : (addressedEvents left).Perm (addressedEvents right))
    (components : ∀ {address name peer row other},
      ActiveEndpoint left address name row → ActiveEndpoint right address peer other → row.component = other.component)
    {start earlier later limit : Nat} (lower : start ≤ earlier) (leftBound : later < last)
    (rightStart : start ≤ limit) (rightBound : limit < otherLast)
    (past : ∀ i, i < start → addressedEventAt left i = addressedEventAt right i)
    {kind : Lifecycle} {actor : Name} (event : right.event limit = .lifecycle kind actor)
    (actors : actorAddress left later = actorAddress right limit)
    (chain : Relation.TransGen (ActivationPrerequisite left) earlier later) :
    ∃ cut label name, start ≤ cut ∧ cut < limit ∧ right.event cut = .lifecycle label name ∧
      actorAddress left earlier = actorAddress right cut ∧
      Relation.TransGen (ActivationPrerequisite right) cut limit := by
  induction chain generalizing limit kind actor with
  | single edge =>
    obtain ⟨cut, label, name, fromStart, before, step, address, peerEdge⟩ :=
      edge.peer leftOpen leftQuiet rightOpen rightQuiet events components lower (by have := edge.1; omega)
        rightStart rightBound past event actors
    exact ⟨cut, label, name, fromStart, before, step, address, .single peerEdge⟩
  | @tail middle later prior edge ih =>
    have priorOrder := ActivationPrerequisite.chain_lt prior
    have finalOrder := edge.1
    obtain ⟨cut, label, name, fromStart, before, step, address, peerEdge⟩ :=
      edge.peer leftOpen leftQuiet rightOpen rightQuiet events components (by omega) (by omega)
        rightStart rightBound past event actors
    obtain ⟨first, firstLabel, firstName, afterStart, earlierCut, firstStep, firstAddress, peerPrior⟩ :=
      ih (by omega) fromStart (by omega) step address
    exact ⟨first, firstLabel, firstName, afterStart, by omega, firstStep, firstAddress, .tail peerPrior peerEdge⟩

/-- Follow actual provider and child-birth prerequisites to an actor
with a valid target at the starting cut. Every recursive link is
strictly earlier in the same command-free block. -/
theorem activation_prerequisites_to_ready (trace : Trace program last)
    (opened : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    {start limit : Nat} (lower : start ≤ limit) (bounded : limit < last)
    {kind : Lifecycle} {actor : Name} {consumer : Address}
    (event : trace.event limit = .lifecycle kind actor)
    (addressed : actorAddress trace limit = some consumer)
    (block : ∀ i, start ≤ i → i < limit → ∃ kind name, trace.event i = .lifecycle kind name) :
    ∃ cut label name address view, start ≤ cut ∧ cut ≤ limit ∧
      trace.event cut = .lifecycle label name ∧ actorAddress trace cut = some address ∧
      Target (trace.state start) name view ∧
      (cut = limit ∨ Relation.TransGen (ActivationPrerequisite trace) cut limit) := by
  induction limit using Nat.strongRecOn generalizing kind actor consumer with
  | ind limit ih =>
    by_cases ready : ∃ view, Target (trace.state start) actor view
    · obtain ⟨view, target⟩ := ready
      exact ⟨limit, kind, actor, consumer, view, lower, Nat.le_refl _, event, addressed, target, .inl rfl⟩
    · have predecessor : ∃ earlier label name address, start ≤ earlier ∧ earlier < limit ∧
          trace.event earlier = .lifecycle label name ∧ actorAddress trace earlier = some address ∧
          ActivationPrerequisite trace earlier limit := by
        cases found : trace.state start actor with
        | none =>
          obtain ⟨cut, label, name, parent, ordinal, fromStart, earlier, allocated, atParent, rfl, born⟩ :=
            allocation_before_unborn_activation trace lower bounded event addressed found block
          exact ⟨cut, label, name, parent, fromStart, earlier, allocated, atParent,
            ⟨earlier, .inr ⟨parent, ordinal, atParent, addressed, born⟩⟩⟩
        | some row =>
          obtain ⟨birth, tag, path⟩ := (actorAddress_eq_some trace).mp addressed
          have owner : trace.actor limit = actor := by simp [Trace.actor, Vestigial.eventActor, event]
          obtain ⟨cut, provider, fromStart, earlier, finish, edge⟩ :=
            disabled_activation_provider trace opened quiet lower bounded event (owner ▸ tag) path found
              (fun view valid => ready ⟨view, valid⟩) block
          obtain ⟨name, stamp, step, live, known⟩ := (addressed_finish_at trace).mp finish
          have actorAt : trace.actor cut = name := by simp [Trace.actor, Vestigial.eventActor, step]
          have resolved := (actorAddress_eq_some trace).mpr ⟨stamp, actorAt.symm ▸ live, known⟩
          exact ⟨cut, .finish, name, provider, fromStart, earlier, step, resolved,
            ⟨earlier, .inl ⟨provider, consumer, finish, addressed, edge⟩⟩⟩
      obtain ⟨earlier, label, name, address, fromStart, beforeLimit, step, atAddress, edge⟩ := predecessor
      obtain ⟨cut, kind, name, address, view, entry, before, actual, resolved, target, chain⟩ :=
        ih earlier beforeLimit fromStart (by omega) step atAddress (fun i lo hi => block i lo (by omega))
      refine ⟨cut, kind, name, address, view, entry, by omega, actual, resolved, target, .inr ?_⟩
      rcases chain with rfl | path
      · exact .single edge
      · exact .tail path edge

/-- A provider declared at the start of a command-free block is the
only provider that any later valid target can select for that key. -/
theorem selected_provider_of_surviving_reservation (trace : Trace program last)
    {start span : Nat} (bounded : start + span ≤ last)
    (block : ∀ i, start ≤ i → i < start + span → ∃ kind actor, trace.event i = .lifecycle kind actor)
    {name consumer : Name} {row consumerRow : F} {key : Key} {view : View Name Key}
    (found : trace.state start name = some row) (declared : row.component.provides key = true)
    (consumerAt : trace.state (start + span) consumer = some consumerRow)
    (required : consumerRow.component.requires key = true)
    (target : Target (trace.state (start + span)) consumer view) :
    view key = name ∧ (trace.notes (start + span)).1 (view key) = (trace.notes start).1 name := by
  obtain ⟨retained, retainedAt, component, stamp⟩ := reservation_survives_activation_block trace bounded block found
  obtain ⟨owned, disjoint⟩ := trace.ownership (start + span) bounded
  simp only [Target, consumerAt] at target
  have selected := target.2 key required
  cases providerAt : trace.state (start + span) (view key) with
  | none => simp [providerAt] at selected
  | some provider =>
    simp only [providerAt] at selected
    have equal : view key = name := by
      apply Classical.byContradiction
      intro different
      exact disjoint (view key) name provider retained providerAt retainedAt different key
        ⟨owned _ provider key providerAt selected.2, component ▸ declared⟩
    exact ⟨equal, by rw [equal]; exact stamp⟩

/-- Selected providers agree across two activation blocks when the
key already had a reservation at their matched starting cut. Both
later views select the same birth, even under different raw names. -/
theorem selected_providers_match_by_starting_reservation
    (left : Trace program last) (right : Trace program otherLast)
    {start leftSpan rightSpan : Nat}
    (leftBound : start + leftSpan ≤ last) (rightBound : start + rightSpan ≤ otherLast)
    (agreement : CutAgreement left right start)
    (leftBlock : ∀ i, start ≤ i → i < start + leftSpan → ∃ kind actor, left.event i = .lifecycle kind actor)
    (rightBlock : ∀ i, start ≤ i → i < start + rightSpan → ∃ kind actor, right.event i = .lifecycle kind actor)
    {name first second : Name} {row leftRow rightRow : F} {key : Key} {leftView rightView : View Name Key}
    (found : left.state start name = some row) (declared : row.component.provides key = true)
    (leftConsumer : left.state (start + leftSpan) first = some leftRow)
    (rightConsumer : right.state (start + rightSpan) second = some rightRow)
    (leftRequired : leftRow.component.requires key = true) (rightRequired : rightRow.component.requires key = true)
    (leftTarget : Target (left.state (start + leftSpan)) first leftView)
    (rightTarget : Target (right.state (start + rightSpan)) second rightView) :
    ∃ names : Renaming.Permutation Name,
      Renaming.registry names (GuardedCutState.project (left.state start)) = GuardedCutState.project (right.state start) ∧
      leftView key = name ∧ rightView key = names.toFun name ∧
      (left.notes (start + leftSpan)).1 (leftView key) =
        (right.notes (start + rightSpan)).1 (rightView key) := by
  obtain ⟨names, states, live, _⟩ := agreement
  have image := congrFun states (names.toFun name)
  rw [Renaming.registry_at] at image
  cases matching : right.state start (names.toFun name) with
  | none => simp [GuardedCutState.project, found, matching] at image
  | some peer =>
    have moved : Renaming.fiber names (GuardedCutState.projectFiber name row) =
        GuardedCutState.projectFiber (names.toFun name) peer := by
      simpa [GuardedCutState.project, found, matching] using image
    have parts := congrArg Fiber.component moved
    have component : row.component = peer.component := parts
    obtain ⟨leftName, leftStamp⟩ := selected_provider_of_surviving_reservation left leftBound leftBlock
      found declared leftConsumer leftRequired leftTarget
    obtain ⟨rightName, rightStamp⟩ := selected_provider_of_surviving_reservation right rightBound rightBlock
      matching (component ▸ declared) rightConsumer rightRequired rightTarget
    exact ⟨names, states, leftName, rightName, leftStamp.trans ((live name).symm.trans rightStamp.symm)⟩

/-- A replacement birth cannot cross a full pre-removal cut by redrawing
names or changing the next transition while retaining the matched cut. -/
theorem no_birth_at_matched_full_cut (source : Trace program last) (moved : Trace program otherLast)
    {cut : Nat} (agreement : CutAgreement source moved cut)
    (full : ∀ name, source.state cut name ≠ none) {draw : Name} :
    ¬ GuardedBirthMatching.BornAt moved draw (cut + 1) := by
  intro born
  obtain ⟨name, vacant⟩ := (vacancy_of_matched_cut source moved agreement).mpr
    ⟨draw, by simpa only [Nat.add_sub_cancel] using born.2.2.1⟩
  exact full name vacant

/-- If a birth can start at one of two matching cuts, but the other
history fills every name by a later cut, a specific intervening birth
has consumed the corresponding vacancy. -/
theorem birth_consumes_matched_vacancy (left : Trace program last) (right : Trace program otherLast)
    {start cut : Nat} (agreement : CutAgreement left right start)
    (ordered : start ≤ cut) (bounded : cut ≤ otherLast)
    {child : Name} (vacant : left.state start child = none)
    (full : ∀ name, right.state cut name ≠ none) :
    ∃ p : Renaming.Permutation Name,
      Renaming.registry p (GuardedCutState.project (left.state start)) =
        GuardedCutState.project (right.state start) ∧
      right.state start (p.toFun child) = none ∧
      ∃ birth address, start < birth ∧ birth ≤ cut ∧
        GuardedBirthMatching.BornAt right (p.toFun child) birth ∧
        Incarnation.Residency right.state (p.toFun child) birth cut ∧
        Addressed right birth address := by
  obtain ⟨p, states, _, _⟩ := agreement
  have empty := (vacancy_of_renamed_cut states child).mpr vacant
  refine ⟨p, states, empty, ?_⟩
  have occupied := full (p.toFun child)
  cases stamp : (right.notes cut).1 (p.toFun child) with
  | none => exact False.elim (occupied ((right.births_agree cut bounded _).mp stamp))
  | some birth =>
    obtain ⟨born, before⟩ := recorded_birth right bounded stamp
    rw [right.notes_eq cut bounded] at stamp
    have resident := Incarnation.resident_of_birthAt stamp
    have after : start < birth :=
      Nat.lt_of_not_ge fun early => resident.present start early ordered empty
    obtain ⟨address, addressed⟩ := exists_address right born
    exact ⟨birth, address, after, before, born, resident, addressed⟩

/-- In the pinned-name obstruction, a vacancy at the matched cut belongs
either to the incarnation born after the matched cut and targeted by
the removal, or to a root inserted before the removal. -/
theorem pinned_reuse_vacancy (right : Trace program otherLast)
    {start cut : Nat} (ordered : start ≤ cut) (bounded : cut < otherLast)
    {old available parent : Name} {kind : Lifecycle}
    (vacant : right.state start available = none)
    (removal : right.event cut = .command (.remove old))
    (activation : right.event (cut + 1) = .lifecycle kind parent)
    (pinned : ∀ name, name ≠ old → ∃ inserted component,
      inserted < cut + 2 ∧ right.event inserted = .command (.insert name component) ∧
      ∀ time, inserted < time → time ≤ cut + 2 → right.state time name ≠ none) :
    (available = old ∧ ∃ birth address component, start < birth ∧
      Lifetime right old birth cut ∧ Addressed right birth address ∧
      targetAt right cut old = some (address, component)) ∨
    (∃ inserted component, start ≤ inserted ∧ inserted < cut ∧
      right.event inserted = .command (.insert available component)) := by
  by_cases same : available = old
  · subst available
    obtain ⟨address, component, target⟩ := targetAt_command right bounded (.inr removal)
    obtain ⟨birth, _, tag, addressed, _, _⟩ := (targetAt_eq_some right).mp target
    have life := lifetime_of_removal right bounded removal tag
    have after : start < birth := by
      apply Nat.lt_of_not_ge
      intro early
      exact life.resident.present start early ordered vacant
    exact .inl ⟨rfl, birth, address, component, after, life, addressed, target⟩
  · obtain ⟨inserted, component, within, event, resident⟩ := pinned available same
    have after : start ≤ inserted := by
      apply Nat.le_of_not_gt
      intro earlier
      exact resident start earlier (by omega) vacant
    have beforeRemoval : inserted ≠ cut := by
      rintro rfl
      rw [removal] at event
      cases event
    have beforeActivation : inserted ≠ cut + 1 := by
      rintro rfl
      rw [activation] at event
      cases event
    exact .inr ⟨inserted, component, after, by omega, event⟩

theorem removal_from_input (trace : Trace program last) {path : Address} {component : Component Key Code}
    (member : .remove path component ∈ orchestrationInput trace) :
    ∃ cut name birth row, cut < last ∧ trace.event cut = .command (.remove name) ∧
      trace.state cut name = some row ∧ row.component = component ∧
      (trace.notes cut).1 name = some birth ∧ Addressed trace birth path := by
  obtain ⟨cut, placed, key⟩ := List.mem_filterMap.mp member
  have bounded := List.mem_range.mp placed
  cases event : trace.event cut with
  | lifecycle => simp [commandAt, event] at key
  | command command =>
    cases command with
    | insert => simp [commandAt, event] at key
    | retire name =>
      obtain ⟨_, _, found⟩ := targetAt_command trace bounded (.inl event)
      simp [commandAt, event, found] at key
    | remove name =>
      obtain ⟨target, part, found⟩ := targetAt_command trace bounded (.inr event)
      have equal : AddressedCommand.remove (Name := Name) target part = .remove path component :=
        Option.some.inj (by simpa [commandAt, event, found] using key)
      obtain ⟨rfl, rfl⟩ := AddressedCommand.remove.inj equal
      obtain ⟨birth, row, tag, address, rowFound, componentEq⟩ := (targetAt_eq_some trace).mp found
      exact ⟨cut, name, birth, row, bounded, event, rowFound, componentEq, tag, address⟩

/-- The other trace releases the same declared key at the matching
address. The command records the actual component of the released row. -/
theorem matching_input_releases_reservation (left : Trace program last) (right : Trace program otherLast)
    (input : orchestrationInput left = orchestrationInput right)
    {cut : Nat} (bounded : cut < otherLast) {name : Name} {key : Key}
    (event : right.event cut = .command (.remove name))
    {row : Fiber Name Key Value Code (Inverse Name Key Value) Error}
    (found : right.state cut name = some row) (declared : row.component.provides key = true) :
    ∃ (first : Reservation left key) (second : Reservation right key), first.address = second.address ∧ second.final = cut := by
  obtain ⟨path, part, target⟩ := targetAt_command right bounded (.inr event)
  obtain ⟨birth, actual, tag, address, actualFound, payload⟩ := (targetAt_eq_some right).mp target
  have rowEq := Option.some.inj (actualFound.symm.trans found)
  subst actual
  have member : .remove path part ∈ orchestrationInput right :=
    List.mem_filterMap.mpr ⟨cut, List.mem_range.mpr bounded, by simp [commandAt, event, target]⟩
  obtain ⟨time, earlierName, earlierBirth, earlierRow, within, removal, earlierFound, earlierPart, earlierTag, earlierPath⟩ :=
    removal_from_input left (input.symm ▸ member)
  obtain ⟨first, _, _, firstPath, _⟩ := reservation_of_removal left within removal earlierFound earlierTag earlierPath
    (earlierPart.trans payload.symm ▸ declared)
  obtain ⟨second, _, _, secondPath, secondEnd⟩ := reservation_of_removal right bounded event found tag address declared
  exact ⟨first, second, firstPath.trans secondPath.symm, secondEnd⟩

private theorem no_earlier_rank_for_paired_live_reservations
    (left : Trace program last) (right : Trace program otherLast)
    {start leftCut rightCut : Nat} (leftStart : start ≤ leftCut) (rightStart : start ≤ rightCut)
    (past : ∀ i, i < start → addressedEventAt left i = addressedEventAt right i)
    (input : orchestrationInput left = orchestrationInput right)
    {key : Key} (first : Reservation left key) (second : Reservation right key)
    (leftLive : first.birth ≤ leftCut ∧ leftCut ≤ first.final)
    (rightLive : second.birth ≤ rightCut ∧ rightCut ≤ second.final)
    (rightBlock : ∀ i, start ≤ i → i < rightCut → ∃ kind actor, right.event i = .lifecycle kind actor) :
    ¬ releaseRank left first.address < releaseRank right second.address := by
  intro earlier
  have releases : releasesBefore left last = releasesBefore right otherLast := by
    rw [releases_of_input, releases_of_input, input]
  have rightRank : releaseRank right second.address ≤ (releasesBefore right otherLast).length :=
    List.idxOf_le_length
  have beforeLast : first.final < last := (first.life.released_before first.addressed (Nat.le_refl _)).mpr
    (by rw [releases]; omega)
  obtain ⟨event, tag⟩ := first.life.release beforeLast
  have source := first.life.resident.present first.final first.life.resident.ordered (Nat.le_refl _)
  cases found : left.state first.final first.name with
  | none => exact False.elim (source found)
  | some row =>
    obtain ⟨initial, placed, supply⟩ := first.reserves
    have component := (first.life.resident.metadata_of_stable
      (fun i valid => transition_stable (left.step i valid).1) (Nat.le_of_lt beforeLast) placed found).1
    obtain ⟨released, counterpart, sameAddress, sameFinal⟩ :=
      matching_input_releases_reservation right left input.symm beforeLast event found (component ▸ supply)
    have firstCandidate : counterpart.address = first.address := by
      have equal : counterpart.final = first.final := sameFinal
      have firstAt := (removalAddress_eq_some left).mpr ⟨first.name, first.birth, event, tag, first.addressed, source⟩
      obtain ⟨otherEvent, otherTag⟩ := counterpart.life.release (equal.symm ▸ beforeLast)
      have otherAt := (removalAddress_eq_some left).mpr ⟨counterpart.name, counterpart.birth, otherEvent, otherTag,
        counterpart.addressed, counterpart.life.resident.present _ counterpart.life.resident.ordered (Nat.le_refl _)⟩
      rw [equal, firstAt] at otherAt
      exact (Option.some.inj otherAt).symm
    have same := sameAddress.trans firstCandidate
    have rank : releaseRank right released.address < releaseRank right second.address := by
      rw [same]
      simpa only [releaseRank, releases] using earlier
    have different : released.address ≠ second.address := by
      intro equal
      rw [equal] at rank
      exact Nat.lt_irrefl _ rank
    have birthOrder := (released.birth_order second different).mpr rank
    obtain ⟨releaseBefore, removed, _⟩ := released.release_before_birth second birthOrder
    have releaseBeforeStart : released.final < start := by
      apply Nat.lt_of_not_ge
      intro inBlock
      obtain ⟨kind, actor, label⟩ := rightBlock released.final inBlock (by omega)
      rw [removed] at label
      cases label
    have priorReleases := releases_of_matched_prefix left right (by have := first.life.bounded; omega)
      (by have := second.life.bounded; omega) past
    have beforeRank := (released.life.released_before released.addressed (by have := second.life.bounded; omega)).mp releaseBeforeStart
    rw [← priorReleases, same] at beforeRank
    have beforeLeft : releaseRank left first.address < (releasesBefore left start).length := by
      simpa only [releaseRank, releases] using beforeRank
    have earlier := (first.life.released_before first.addressed (by have := first.life.bounded; omega)).mpr beforeLeft
    omega

/-- Two witnessed reservations of the same key at the ends of
command-free blocks must have the same address if either has a recorded
release. A larger release rank would require an earlier removal inside
one of the blocks or before a still-live reservation. -/
theorem live_reservations_match_if_released
    (left : Trace program last) (right : Trace program otherLast)
    {start leftCut rightCut : Nat} (leftStart : start ≤ leftCut) (rightStart : start ≤ rightCut)
    (past : ∀ i, i < start → addressedEventAt left i = addressedEventAt right i)
    (input : orchestrationInput left = orchestrationInput right)
    {key : Key} (first : Reservation left key) (second : Reservation right key)
    (leftLive : first.birth ≤ leftCut ∧ leftCut ≤ first.final)
    (rightLive : second.birth ≤ rightCut ∧ rightCut ≤ second.final)
    (leftBlock : ∀ i, start ≤ i → i < leftCut → ∃ kind actor, left.event i = .lifecycle kind actor)
    (rightBlock : ∀ i, start ≤ i → i < rightCut → ∃ kind actor, right.event i = .lifecycle kind actor)
    (released : first.final < last ∨ second.final < otherLast) :
    first.address = second.address := by
  have equalRank := Nat.le_antisymm
    (Nat.le_of_not_gt (no_earlier_rank_for_paired_live_reservations right left rightStart leftStart
      (fun i earlier => (past i earlier).symm) input.symm second first rightLive leftLive leftBlock))
    (Nat.le_of_not_gt (no_earlier_rank_for_paired_live_reservations left right leftStart rightStart
      past input first second leftLive rightLive rightBlock))
  have releases : releasesBefore left last = releasesBefore right otherLast := by
    rw [releases_of_input, releases_of_input, input]
  have sameRank : (releasesBefore left last).idxOf first.address = (releasesBefore left last).idxOf second.address := by
    simpa only [releaseRank, ← releases] using equalRank
  have inRange : (releasesBefore left last).idxOf first.address < (releasesBefore left last).length := by
    rcases released with firstReleased | secondReleased
    · exact (first.life.released_before first.addressed (Nat.le_refl _)).mp firstReleased
    · rw [sameRank, releases]
      exact (second.life.released_before second.addressed (Nat.le_refl _)).mp secondReleased
  let word := releasesBefore left last
  have firstIndex : word.idxOf first.address < word.length := inRange
  have secondIndex : word.idxOf second.address < word.length := sameRank ▸ inRange
  have atIndex (address : Address) (inside : word.idxOf address < word.length) :
      word[word.idxOf address] = address := by
    unfold List.idxOf at inside ⊢
    exact beq_iff_eq.mp (List.findIdx_getElem (w := inside))
  have equalReads := congrArg (fun i => word[i]?) sameRank
  change word[word.idxOf first.address]? = word[word.idxOf second.address]? at equalReads
  rw [List.getElem?_eq_getElem firstIndex, List.getElem?_eq_getElem secondIndex,
    atIndex first.address firstIndex, atIndex second.address secondIndex] at equalReads
  exact Option.some.inj equalReads

/-- Suppose the left trace allocates a key at the first unmatched event
and the right trace has the corresponding birth later. No intervening
removal in the right trace can release an older reservation of that key.
It would have to release the matching reservation before the left birth,
contrary to the matched prefix. -/
theorem no_later_release_of_birth_key (left : Trace program last) (right : Trace program otherLast)
    {start cut : Nat} (leftBound : start < last) (rightBound : start ≤ cut) (cutBound : cut < otherLast)
    (past : ∀ time, time < start → addressedEventAt left time = addressedEventAt right time)
    (input : orchestrationInput left = orchestrationInput right)
    {key : Key} (leftBirth : Reservation left key) (rightBirth : Reservation right key)
    (first : leftBirth.birth = start + 1) (later : cut < rightBirth.birth)
    (same : leftBirth.address = rightBirth.address)
    {name : Name} (removal : right.event cut = .command (.remove name))
    {row : Fiber Name Key Value Code (Inverse Name Key Value) Error}
    (found : right.state cut name = some row) : row.component.provides key ≠ true := by
  intro declared
  obtain ⟨leftBlock, rightBlock, blockerAddress, endAt⟩ :=
    matching_input_releases_reservation left right input cutBound removal found declared
  have rightOrder : rightBlock.birth < rightBirth.birth := by
    have birthBeforeEnd := rightBlock.life.resident.ordered
    omega
  have different : leftBlock.address ≠ leftBirth.address := by
    intro equal
    have tags := rightBlock.addressed.injective rightBirth.addressed (blockerAddress.symm.trans (equal.trans same))
    omega
  have leftOrder := (matching_commands_fix_birth_order input leftBlock leftBirth rightBlock rightBirth blockerAddress same different).mpr rightOrder
  have leftRelease := (leftBlock.release_before_birth leftBirth leftOrder).1
  have beforePrefix : leftBlock.final < start := by omega
  have beforeRank := (leftBlock.life.released_before leftBlock.addressed (Nat.le_of_lt leftBound)).mp beforePrefix
  have priorReleases := releases_of_matched_prefix left right (Nat.le_of_lt leftBound) (by omega : start ≤ otherLast) past
  have word : releasesBefore left last = releasesBefore right otherLast := by
    rw [releases_of_input, releases_of_input, input]
  unfold releaseRank at beforeRank
  rw [priorReleases, word, blockerAddress] at beforeRank
  have rightRelease : rightBlock.final < start :=
    (rightBlock.life.released_before rightBlock.addressed (by omega : start ≤ otherLast)).mpr beforeRank
  omega

private theorem no_parent_stage_before_first {trace : Trace program last} {start time birth : Nat} {actor : Name}
    (bounded : time < last) (order : start ≤ time) (tag : (trace.notes time).1 actor = some birth)
    (first : ∀ cut, start ≤ cut → cut < time → ∀ k, trace.event cut ≠ .lifecycle k actor) :
    occurrencesBefore (isParentStage trace birth) time = occurrencesBefore (isParentStage trace birth) start := by
  have doesNotStage (cut : Nat) (lower : start ≤ cut) (earlier : cut < time) : isParentStage trace birth cut = false := by
    apply Bool.eq_false_iff.mpr
    intro hit
    simp only [isParentStage, Bool.and_eq_true, beq_iff_eq] at hit
    have sameBirth : (trace.notes cut).1 (trace.actor cut) = some birth := hit.2
    have same := born_unique trace (recorded_birth trace (by omega) sameBirth).1
      (recorded_birth trace (Nat.le_of_lt bounded) tag).1
    cases event : trace.event cut with
    | lifecycle kind name =>
      have nameEq : name = actor := by simpa [Trace.actor, Vestigial.eventActor, event] using same
      exact first cut lower earlier kind (nameEq ▸ event)
    | command command =>
      cases command <;> simp [Trace.rule, eventRule, ExchangeReplay.commandRule, EpisodeSelection.canBirth, event] at hit
  have constant (span : Nat) (earlier : start + span ≤ time) :
      occurrencesBefore (isParentStage trace birth) (start + span) = occurrencesBefore (isParentStage trace birth) start := by
    induction span with
    | zero => rfl
    | succ span ih =>
      change occurrencesBefore (isParentStage trace birth) ((start + span) + 1) = _
      rw [occurrencesBefore, doesNotStage (start + span) (by omega) (by omega), ih (by omega)]
      rfl
  simpa only [Nat.add_sub_of_le order] using constant (time - start) (by omega)

private theorem landing_when_reloading (trace : Trace program last)
    (openOnly : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    {cut : Nat} (bounded : cut < last) {kind : Lifecycle} {actor : Name}
    (event : trace.event cut = .lifecycle kind actor) {row : F} (found : trace.state cut actor = some row)
    {code word view} (phase : row.phase = .reloading code word view) :
    (trace.event cut = .lifecycle .iter actor ∨ trace.event cut = .lifecycle .finish actor) ∧
      EpisodeSelection.canBirth (trace.rule cut) = true := by
  obtain ⟨active, step⟩ := trace.activation_at openOnly quiet bounded event
  cases kind with
  | iter => exact ⟨.inl event, by simp [Trace.rule, eventRule, Lifecycle.rule, event, EpisodeSelection.canBirth]⟩
  | finish => exact ⟨.inr event, by simp [Trace.rule, eventRule, Lifecycle.rule, event, EpisodeSelection.canBirth]⟩
  | begin =>
    generalize ending : trace.state (cut + 1) = after at step
    cases step with
    | begin _ _ entry _ present inactive _ _ =>
      obtain rfl : row = entry := Option.some.inj (found.symm.trans present)
      rw [phase] at inactive
      cases inactive
  | divert | leave | unload => simp [Transposition.Activation, Lifecycle.rule] at active

private theorem landing_when_creating (trace : Trace program last)
    (openOnly : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    {cut : Nat} (bounded : cut < last) {kind : Lifecycle} {actor child : Name}
    (event : trace.event cut = .lifecycle kind actor) (vacant : trace.state cut child = none)
    (born : trace.state (cut + 1) child ≠ none) :
    (trace.event cut = .lifecycle .iter actor ∨ trace.event cut = .lifecycle .finish actor) ∧
      EpisodeSelection.canBirth (trace.rule cut) = true := by
  obtain ⟨active, step⟩ := trace.activation_at openOnly quiet bounded event
  cases kind with
  | iter => exact ⟨.inl event, by simp [Trace.rule, eventRule, Lifecycle.rule, event, EpisodeSelection.canBirth]⟩
  | finish => exact ⟨.inr event, by simp [Trace.rule, eventRule, Lifecycle.rule, event, EpisodeSelection.canBirth]⟩
  | begin =>
    generalize ending : trace.state (cut + 1) = after at step born
    cases step with
    | begin _ _ _ _ _ _ _ _ => exact False.elim (born ((Transposition.mark_presence _ _ _ _).mpr vacant))
  | divert | leave | unload => simp [Transposition.Activation, Lifecycle.rule] at active

omit [DecidableEq Name] [DecidableEq Key] in
private theorem reloading_code_transport {left right : R} (p : Renaming.Permutation Name) {actor : Name}
    (states : Renaming.registry p (GuardedCutState.project left) = GuardedCutState.project right)
    {row : F} (found : left actor = some row) {code word view} (phase : row.phase = .reloading code word view) :
    ∃ entry otherWord otherView, right (p.toFun actor) = some entry ∧ entry.phase = .reloading code otherWord otherView := by
  have rows := congrFun states (p.toFun actor)
  rw [Renaming.registry_at] at rows
  cases other : right (p.toFun actor) with
  | none => simp [GuardedCutState.project, found, other] at rows
  | some entry =>
    have rowEq : Renaming.fiber p (GuardedCutState.projectFiber actor row) =
        GuardedCutState.projectFiber (p.toFun actor) entry := by
      simpa [GuardedCutState.project, found, other] using rows
    have phases := congrArg Fiber.phase rowEq
    cases entryPhase : entry.phase with
    | reloading otherCode acc selected =>
      simp [GuardedCutState.projectFiber, GuardedCutState.projectPhase, Renaming.fiber, Renaming.phase,
        phase, entryPhase] at phases
      exact ⟨entry, acc, selected, rfl, phases.1.symm ▸ entryPhase⟩
    | inactive | active | unloading =>
      simp [GuardedCutState.projectFiber, GuardedCutState.projectPhase, Renaming.fiber, Renaming.phase,
        phase, entryPhase] at phases

private theorem child_of_instantiation {before after : R} {actor : Name} {code : Code} {token next}
    (landed : Land program actor code before after token next) {component : Component Key Code}
    (action : (program code).action = .instantiate component) :
    ∃ child, before child = none ∧ after = put before child (fresh component (some actor)) := by
  cases landed with
  | unit _ _ _ chosen => rw [action] at chosen; cases chosen
  | provide _ _ _ _ _ _ chosen _ _ _ => rw [action] at chosen; cases chosen
  | operate _ _ _ _ _ _ _ _ _ _ chosen _ _ => rw [action] at chosen; cases chosen
  | instantiate _ _ _ actual child chosen ready =>
    have same := Action.instantiate.inj (chosen.symm.trans action)
    subst actual
    exact ⟨child, ready.1, rfl⟩

/-- If the first activation of the waiting incarnation allocates a child,
the paired activation at the matched cut allocates the same component and
birth address. Their stages use the same current code. -/
theorem matched_child_birth_for_waiting_actor (left : Trace program last) (right : Trace program otherLast)
    {start time parentBirth : Nat} (leftBound : start < last) (rightBound : time < otherLast) (order : start ≤ time)
    (leftOpen : ¬ Nonempty (ClosedEpisode left)) (leftQuiet : Progress.Quiet (left.state last))
    (rightOpen : ¬ Nonempty (ClosedEpisode right)) (rightQuiet : Progress.Quiet (right.state otherLast))
    (current : CutAgreement left right start)
    (past : ∀ cut, cut < start → addressedEventAt left cut = addressedEventAt right cut)
    {leftKind rightKind : Lifecycle} {actor other : Name} (leftEvent : left.event start = .lifecycle leftKind actor)
    (rightEvent : right.event time = .lifecycle rightKind other)
    (leftTag : (left.notes start).1 actor = some parentBirth) (rightTag : (right.notes start).1 other = some parentBirth)
    (laterTag : (right.notes time).1 other = some parentBirth)
    {path : Address} (leftPath : Addressed left parentBirth path) (rightPath : Addressed right parentBirth path)
    (waiting : (right.state time other).map Fiber.phase = (right.state start other).map Fiber.phase)
    (first : ∀ cut, start ≤ cut → cut < time → ∀ k, right.event cut ≠ .lifecycle k other)
    {child : Name} (vacant : right.state time child = none) {row : F}
    (born : right.state (time + 1) child = some row) :
    ∃ name childPath, left.state start name = none ∧
      left.state (start + 1) name = some (fresh row.component (some actor)) ∧
      Addressed left (start + 1) childPath ∧ Addressed right (time + 1) childPath := by
  obtain ⟨rightLanding, rightStage⟩ := landing_when_creating right rightOpen rightQuiet rightBound rightEvent vacant (by simp [born])
  obtain ⟨rSource, code, word, view, middle, token, next, rightFound, rightPhase, landed, rightEnd, _⟩ :=
    activation_landing right rightBound rightLanding
  have middlePresent : middle child ≠ none := by
    intro absent
    rw [rightEnd, (Transposition.mark_presence _ _ _ _).mpr absent] at born
    cases born
  obtain ⟨component, action, _, putChild⟩ := Transposition.land_new_name program landed child vacant middlePresent
  have otherChild : child ≠ other := by
    intro same
    rw [same, rightFound] at vacant
    cases vacant
  have freshRight : right.state (time + 1) child = some (fresh component (some other)) := by
    rw [rightEnd, Transposition.mark_other _ _ _ _ otherChild, putChild, put_self]
  have partEq : row.component = component := congrArg Fiber.component (Option.some.inj (born.symm.trans freshRight))
  obtain ⟨p, registry, live, _⟩ := current
  have sameActor := born_unique right (recorded_birth right (by omega : start ≤ otherLast) ((live actor).trans leftTag)).1
    (recorded_birth right (by omega : start ≤ otherLast) rightTag).1
  have otherAtStart : ∃ original, right.state start other = some original ∧ original.phase = .reloading code word view := by
    cases initial : right.state start other with
    | none => simp [rightFound, rightPhase, initial] at waiting
    | some original =>
      have keep : .reloading code word view = original.phase := Option.some.inj (by simpa [rightFound, rightPhase, initial] using waiting)
      exact ⟨original, rfl, keep.symm⟩
  obtain ⟨original, originalFound, originalPhase⟩ := otherAtStart
  have backRegistry : Renaming.registry p.symm (GuardedCutState.project (right.state start)) =
      GuardedCutState.project (left.state start) := by rw [← registry, Renaming.registry_symm]
  obtain ⟨lSource, lWord, lView, lFound, lPhase⟩ := reloading_code_transport p.symm backRegistry originalFound originalPhase
  have invActor : p.symm.toFun other = actor := by rw [← sameActor]; exact p.inv_to actor
  rw [invActor] at lFound
  obtain ⟨leftLanding, leftStage⟩ := landing_when_reloading left leftOpen leftQuiet leftBound leftEvent lFound lPhase
  obtain ⟨startRow, startCode, startWord, startView, beforeMark, startToken, startNext, startFound,
    startPhase, leftLand, leftEnd, _⟩ := activation_landing left leftBound leftLanding
  have rowEq := Option.some.inj (lFound.symm.trans startFound)
  subst startRow
  have sameCode := (Phase.reloading.inj (startPhase.symm.trans lPhase)).1
  subst startCode
  obtain ⟨name, empty, created⟩ := child_of_instantiation leftLand action
  have different : name ≠ actor := by
    intro same
    rw [same, startFound] at empty
    cases empty
  have freshLeft : left.state (start + 1) name = some (fresh component (some actor)) := by
    rw [leftEnd, Transposition.mark_other _ _ _ _ different, created, put_self]
  have leftActor : left.actor start = actor := by simp [Trace.actor, Vestigial.eventActor, leftEvent]
  have rightActor : right.actor time = other := by simp [Trace.actor, Vestigial.eventActor, rightEvent]
  have firstAddress := Addressed.child leftBound leftStage empty (by simp [freshLeft]) (leftActor.symm ▸ leftTag) leftPath
  have secondAddress := Addressed.child rightBound rightStage vacant (by simp [born]) (rightActor.symm ▸ laterTag) rightPath
  have sameCount := parent_stage_count_of_matched_prefix left right (Nat.le_of_lt leftBound) (by omega) past leftPath rightPath
  have delayCount := no_parent_stage_before_first rightBound order laterTag first
  exact ⟨name, _, empty, partEq.symm ▸ freshLeft, firstAddress, (delayCount.trans sameCount.symm) ▸ secondAddress⟩

/-- If the reference allocates now, the same addressed allocation
in the peer is its parent's first pending activation. A loading parent
cannot begin again or pass another allocating-stage ordinal first. -/
theorem addressed_allocation_is_first_pending (left : Trace program last) (right : Trace program otherLast)
    {start time : Nat} (leftBound : start < last) (rightBound : time < otherLast) (order : start ≤ time)
    (leftOpen : ¬ Nonempty (ClosedEpisode left)) (leftQuiet : Progress.Quiet (left.state last))
    (rightOpen : ¬ Nonempty (ClosedEpisode right)) (rightQuiet : Progress.Quiet (right.state otherLast))
    (current : CutAgreement left right start)
    (past : ∀ i, i < start → addressedEventAt left i = addressedEventAt right i)
    (input : orchestrationInput left = orchestrationInput right)
    {kind otherKind : Lifecycle} {actor other child drawn : Name} {address : Address}
    (first : left.event start = .lifecycle kind actor)
    (later : right.event time = .lifecycle otherKind other)
    (leftBorn : GuardedBirthMatching.BornAt left child (start + 1))
    (rightBorn : GuardedBirthMatching.BornAt right drawn (time + 1))
    (leftAddress : Addressed left (start + 1) address) (rightAddress : Addressed right (time + 1) address) :
    ∃ birth parent,
      (left.notes start).1 actor = some birth ∧ (right.notes start).1 other = some birth ∧
      (right.notes time).1 other = some birth ∧ Addressed left birth parent ∧ Addressed right birth parent ∧
      ∀ i, start ≤ i → i < time → ∀ stage, right.event i ≠ .lifecycle stage other := by
  obtain ⟨next, nextKind, nextActor, birth, parent, lower, within, nextEvent, leftTag, rightTag, nextTag,
      leftParent, rightParent, samePhase, _, earliest⟩ :=
    GuardedActivationOccurrence.pending_activation_occurs left right leftBound (by omega) leftOpen leftQuiet
      rightOpen rightQuiet current past input first
  obtain ⟨leftBirth, leftPath, leftRecorded, leftAddressed, leftOrdinal⟩ := leftAddress.parent_of_lifecycle first
  obtain ⟨rightBirth, rightPath, rightRecorded, rightAddressed, rightOrdinal⟩ := rightAddress.parent_of_lifecycle later
  have leftEqual := Option.some.inj (leftTag.symm.trans leftRecorded)
  subst leftBirth
  have leftPathEq := leftAddressed.unique leftParent
  subst leftPath
  obtain ⟨pathEq, sameOrdinal⟩ := Address.child.inj (leftOrdinal.symm.trans rightOrdinal)
  subst rightPath
  have birthEq := rightAddressed.injective rightParent rfl
  subst rightBirth
  have actorEq := born_unique right (recorded_birth right (by omega : time ≤ otherLast) rightRecorded).1
    (recorded_birth right (by omega : next ≤ otherLast) nextTag).1
  subst other
  obtain ⟨landing, _⟩ := landing_when_creating left leftOpen leftQuiet leftBound first
    (by simpa only [Nat.add_sub_cancel] using leftBorn.2.2.1) leftBorn.2.2.2
  obtain ⟨row, code, word, view, _, _, _, found, phase, _, _, _⟩ := activation_landing left leftBound landing
  obtain ⟨p, registry, live, _⟩ := current
  have image := born_unique right
    (recorded_birth right (by omega : start ≤ otherLast) ((live actor).trans leftTag)).1
    (recorded_birth right (by omega : start ≤ otherLast) rightTag).1
  obtain ⟨entry, otherWord, otherView, atStart, loading⟩ := reloading_code_transport p registry found phase
  rw [image] at atStart
  have reloading : ∃ entry, right.state next nextActor = some entry ∧ entry.phase = .reloading code otherWord otherView := by
    rw [atStart, Option.map_some, loading] at samePhase
    exact Option.map_eq_some_iff.mp samePhase
  obtain ⟨nextRow, nextFound, nextPhase⟩ := reloading
  have nextStage : isParentStage right birth next = true := by
    have legal := (landing_when_reloading right rightOpen rightQuiet within nextEvent nextFound nextPhase).2
    simp [isParentStage, legal, Trace.actor, Vestigial.eventActor, nextEvent, nextTag]
  have laterStage : isParentStage right birth time = true := by
    have legal := (landing_when_creating right rightOpen rightQuiet rightBound later
      (by simpa only [Nat.add_sub_cancel] using rightBorn.2.2.1) rightBorn.2.2.2).2
    simp [isParentStage, legal, Trace.actor, Vestigial.eventActor, later, rightRecorded]
  have count := parent_stage_count_of_matched_prefix left right (Nat.le_of_lt leftBound) (by omega) past leftParent rightParent
  have nextTime := occurrence_unique (isParentStage right birth) nextStage laterStage
    ((no_parent_stage_before_first within lower nextTag earliest).trans (count.symm.trans sameOrdinal))
  subst next
  exact ⟨birth, parent, leftTag, rightTag, nextTag, leftParent, rightParent, earliest⟩

/-- A waiting birth that reuses the name freed by its preceding removal
has a vacancy at the matched starting cut. If the right history is full
by the removal, a different addressed birth consumed that vacancy. -/
theorem waiting_reuse_capacity (left : Trace program last) (right : Trace program otherLast)
    {start cut parentBirth : Nat} (leftBound : start < last) (rightBound : cut + 1 < otherLast) (order : start ≤ cut)
    (leftOpen : ¬ Nonempty (ClosedEpisode left)) (leftQuiet : Progress.Quiet (left.state last))
    (rightOpen : ¬ Nonempty (ClosedEpisode right)) (rightQuiet : Progress.Quiet (right.state otherLast))
    (current : CutAgreement left right start)
    (past : ∀ time, time < start → addressedEventAt left time = addressedEventAt right time)
    {leftKind rightKind : Lifecycle} {actor other removed : Name}
    (leftEvent : left.event start = .lifecycle leftKind actor)
    (rightEvent : right.event (cut + 1) = .lifecycle rightKind other)
    (leftTag : (left.notes start).1 actor = some parentBirth) (rightTag : (right.notes start).1 other = some parentBirth)
    (laterTag : (right.notes (cut + 1)).1 other = some parentBirth)
    {path : Address} (leftPath : Addressed left parentBirth path) (rightPath : Addressed right parentBirth path)
    (waiting : (right.state (cut + 1) other).map Fiber.phase = (right.state start other).map Fiber.phase)
    (first : ∀ time, start ≤ time → time < cut + 1 → ∀ k, right.event time ≠ .lifecycle k other)
    (removal : right.event cut = .command (.remove removed))
    (rebound : right.state (cut + 2) removed ≠ none) :
    ∃ draw childAddress, GuardedBirthMatching.BornAt left draw (start + 1) ∧
      Addressed left (start + 1) childAddress ∧ Addressed right (cut + 2) childAddress ∧
      (∃ spare, right.state start spare = none) ∧
      ((∀ name, right.state cut name ≠ none) →
        ∃ spare birth address, right.state start spare = none ∧ start < birth ∧ birth ≤ cut ∧
          GuardedBirthMatching.BornAt right spare birth ∧
          Incarnation.Residency right.state spare birth cut ∧ Addressed right birth address ∧ address ≠ childAddress) := by
  have step := (right.step cut (by omega)).1
  rw [removal] at step
  have vacant : right.state (cut + 1) removed = none := by
    rw [step.2]
    simp [OrchestrationSorting.Command.apply, erase]
  cases found : right.state (cut + 2) removed with
  | none => exact False.elim (rebound found)
  | some row =>
    obtain ⟨draw, childAddress, empty, fresh, leftAddress, rightAddress⟩ :=
      matched_child_birth_for_waiting_actor left right leftBound rightBound (by omega)
        leftOpen leftQuiet rightOpen rightQuiet current past leftEvent rightEvent
        leftTag rightTag laterTag leftPath rightPath waiting first vacant found
    have born : GuardedBirthMatching.BornAt left draw (start + 1) :=
      ⟨by omega, by omega, by simpa only [Nat.add_sub_cancel] using empty, by simp [fresh]⟩
    refine ⟨draw, childAddress, born, leftAddress, rightAddress,
      (vacancy_of_matched_cut left right current).mp ⟨draw, empty⟩, ?_⟩
    intro full
    obtain ⟨names, _, free, birth, address, afterStart, beforeRemoval, new, live, addressed⟩ :=
      birth_consumes_matched_vacancy left right current order (by omega) empty full
    refine ⟨names.toFun draw, birth, address, free, afterStart, beforeRemoval, new, live, addressed, ?_⟩
    intro equal
    have sameBirth := addressed.injective rightAddress equal
    omega

/-- At a matched cut, a waiting activation can cross its immediately
preceding removal exactly when it did not allocate the removed raw name.
The shared surviving input excludes a conflicting provision reservation. -/
theorem waiting_activation_crosses_removal_iff (left : Trace program last) (right : Trace program otherLast)
    {start cut parentBirth : Nat} (leftBound : start < last) (rightBound : cut + 1 < otherLast) (order : start ≤ cut)
    (leftOpen : ¬ Nonempty (ClosedEpisode left)) (leftQuiet : Progress.Quiet (left.state last))
    (rightOpen : ¬ Nonempty (ClosedEpisode right)) (rightQuiet : Progress.Quiet (right.state otherLast))
    (current : CutAgreement left right start)
    (past : ∀ time, time < start → addressedEventAt left time = addressedEventAt right time)
    (input : orchestrationInput left = orchestrationInput right)
    {leftKind rightKind : Lifecycle} {actor other : Name} (leftEvent : left.event start = .lifecycle leftKind actor)
    (rightEvent : right.event (cut + 1) = .lifecycle rightKind other)
    (leftTag : (left.notes start).1 actor = some parentBirth) (rightTag : (right.notes start).1 other = some parentBirth)
    (laterTag : (right.notes (cut + 1)).1 other = some parentBirth)
    {path : Address} (leftPath : Addressed left parentBirth path) (rightPath : Addressed right parentBirth path)
    (waiting : (right.state (cut + 1) other).map Fiber.phase = (right.state start other).map Fiber.phase)
    (first : ∀ time, start ≤ time → time < cut + 1 → ∀ k, right.event time ≠ .lifecycle k other)
    {removed : Name} (removal : right.event cut = .command (.remove removed)) :
    Vestigial.CompatibleBirths (right.state cut) (right.state (cut + 2)) removed ↔
      right.state (cut + 2) removed = none := by
  have valid : cut < otherLast := by omega
  have removedStep := (right.step cut valid).1
  rw [removal] at removedStep
  have afterRemoval : right.state (cut + 1) = erase (right.state cut) removed := removedStep.2
  constructor
  · intro compatible
    cases result : right.state (cut + 2) removed with
    | none => rfl
    | some row =>
      have fresh : erase (right.state cut) removed removed = none := by simp [erase]
      exact False.elim ((compatible removed row fresh result).1 rfl)
  · intro noReuse child row vacant born
    have vacantAfter : right.state (cut + 1) child = none := by rw [afterRemoval]; exact vacant
    refine ⟨?_, ?_⟩
    · intro equal
      rw [equal, noReuse] at born
      cases born
    · intro old found key reserves
      obtain ⟨newName, childPath, empty, fresh, leftAddress, rightAddress⟩ := matched_child_birth_for_waiting_actor
        left right leftBound rightBound (by omega) leftOpen leftQuiet rightOpen rightQuiet current past leftEvent rightEvent
        leftTag rightTag laterTag leftPath rightPath waiting first vacantAfter born
      have bornLeft : GuardedBirthMatching.BornAt left newName (start + 1) :=
        ⟨by omega, by omega, by simpa only [Nat.add_sub_cancel] using empty, by simp [fresh]⟩
      have bornRight : GuardedBirthMatching.BornAt right child (cut + 1 + 1) :=
        ⟨by omega, by omega, by simpa only [Nat.add_sub_cancel] using vacantAfter, by simp [born]⟩
      obtain ⟨leftEnd, leftLife⟩ := lifetime_of_birth left bornLeft
      obtain ⟨rightEnd, rightLife⟩ := lifetime_of_birth right bornRight
      let leftBirth : Reservation left key :=
        ⟨newName, start + 1, leftEnd, childPath, leftLife, leftAddress, _, fresh, reserves⟩
      let rightBirth : Reservation right key :=
        ⟨child, cut + 1 + 1, rightEnd, childPath, rightLife, rightAddress, row, born, reserves⟩
      exact no_later_release_of_birth_key left right leftBound order valid past input leftBirth rightBirth rfl
        (by dsimp only [rightBirth]; omega) rfl removal found

end Cordis.Repairs.GuardedReservationAlignment
