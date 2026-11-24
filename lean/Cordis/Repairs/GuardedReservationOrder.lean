import Cordis.Repairs.GuardedBirthAddresses

/-! A provision declaration reserves its key until the actual removal of
that incarnation. Two conflicting reservations cannot overlap. -/
namespace Cordis.Repairs.GuardedReservationOrder
open Calculus Stages GuardedHistory LegalHistory Incarnation IncarnationReplay
open GuardedBirthMatching GuardedBirthAddresses

universe u
variable {Name Key Value Code Error : Type u} [DecidableEq Name] [DecidableEq Key]
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
variable {program : Code → Instruction Name Key Value Code Error} {last : Nat}

private theorem native_loses_only_remove {rule : Labeled.Rule} {actor : Name} {before after : R}
    (step : Labeled.Step program rule actor before after)
    {name : Name} {row : F} (present : before name = some row) (missing : after name = none) :
    rule = .remove := by
  have landed {mid : R} {code : Code} {token : Inverse Name Key Value} {next : Option Code} {phase}
      (land : Land program actor code before mid token next)
      (absent : mark mid actor phase name = none) : False := by
    obtain ⟨entry, current, _, _⟩ := Ordering.land_existing_control program land name row present
    have vacant := (Transposition.mark_presence _ _ _ _).mp absent
    rw [current] at vacant
    cases vacant
  cases step with
  | remove => rfl
  | insert =>
    by_cases same : name = actor <;> simp [put, same, present] at missing
  | retire =>
    have absent := (Transposition.retire_presence _ _ _).mp missing
    rw [present] at absent
    cases absent
  | begin | leave =>
    have absent := (Transposition.mark_presence _ _ _ _).mp missing
    rw [present] at absent
    cases absent
  | iter _ _ _ _ _ _ _ _ _ _ _ _ step
  | finish _ _ _ _ _ _ _ _ _ _ _ step =>
    exact False.elim (landed step missing)
  | divert _ _ _ _ _ _ _ _ _ _ _ alternative =>
    rcases alternative with ⟨rfl, rfl⟩ | ⟨_, _, performed, rfl⟩
    · have absent := (Transposition.mark_presence _ _ _ _).mp missing
      rw [present] at absent
      cases absent
    · exact False.elim (landed performed missing)
  | unload _ _ _ word _ _ _ _ =>
    obtain ⟨entry, current, _⟩ := Ordering.discharge_existing_phases before word name row present
    have absent := (Transposition.mark_presence _ _ _ _).mp missing
    rw [current] at absent
    cases absent

/-- Disappearance in an actual guarded step identifies its removal
command, including its exact target. -/
theorem removal_at_gap (trace : Trace program last) {time : Nat} (bounded : time < last)
    {name : Name} (present : trace.state time name ≠ none) (absent : trace.state (time + 1) name = none) :
    trace.event time = .command (.remove name) := by
  rcases transition_cases (trace.step time bounded).1 with native | ⟨actor, event, step⟩
  · cases found : trace.state time name with
    | none => exact False.elim (present found)
    | some row =>
      have rule := native_loses_only_remove native found absent
      cases event : trace.event time with
      | lifecycle kind actor => cases kind <;> simp [event, eventRule, Lifecycle.rule] at rule
      | command command =>
        cases command with
        | insert | retire => simp [event, eventRule, ExchangeReplay.commandRule] at rule
        | remove target =>
          have source := (trace.step time bounded).1
          rw [event] at source
          have endpoint : trace.state (time + 1) = erase (trace.state time) target := source.2
          by_cases same : name = target
          · simp [same]
          · simp [endpoint, erase, same, found] at absent
  · obtain ⟨_, _, _, _, _, endpoint⟩ := step
    rw [endpoint, Transposition.mark_presence, replay_presence] at absent
    exact False.elim (present absent)

structure Lifetime (trace : Trace program last) (name : Name) (birth final : Nat) : Prop where
  resident : Residency trace.state name birth final
  bounded : final ≤ last
  gone : final < last → trace.state (final + 1) name = none

theorem Lifetime.unique {trace : Trace program last} {name : Name} {birth first second : Nat}
    (left : Lifetime trace name birth first) (right : Lifetime trace name birth second) : first = second := by
  rcases Nat.lt_trichotomy first second with before | equal | after
  · have lower := left.resident.ordered
    have bound := right.bounded
    exact False.elim (right.resident.present (first + 1) (by omega) (by omega) (left.gone (by omega)))
  · exact equal
  · have lower := right.resident.ordered
    have bound := left.bounded
    exact False.elim (left.resident.present (second + 1) (by omega) (by omega) (right.gone (by omega)))

/-- Extend a birth through its maximal uninterrupted presence. A later
reuse of the name belongs to a different interval. -/
theorem lifetime_of_birth (trace : Trace program last) {name : Name} {birth : Nat}
    (born : BornAt trace name birth) : ∃ final, Lifetime trace name birth final := by
  have extend (remaining : Nat) {current : Nat} (endAt : current + remaining = last)
      (lives : Residency trace.state name birth current) : ∃ final, Lifetime trace name birth final := by
    induction remaining generalizing current with
    | zero =>
      exact ⟨current, lives, by omega, fun early => False.elim (by omega)⟩
    | succ remaining ih =>
      cases found : trace.state (current + 1) name with
      | none => exact ⟨current, lives, by omega, fun _ => found⟩
      | some row =>
        have started := lives.ordered
        apply ih (current := current + 1) (by omega)
        refine ⟨by omega, ?_, lives.boundary⟩
        intro cut lower upper
        by_cases final : cut = current + 1
        · simp [final, found]
        · exact lives.present cut lower (by omega)
  have ⟨positive, bounded, vacant, current⟩ := born
  exact extend (last - birth) (by omega)
    ⟨Nat.le_refl _, fun cut lower upper => (show cut = birth by omega) ▸ current, .inr vacant⟩

theorem Lifetime.release {trace : Trace program last} {name : Name} {birth final : Nat}
    (life : Lifetime trace name birth final) (ended : final < last) :
    trace.event final = .command (.remove name) ∧ (trace.notes final).1 name = some birth := by
  have live := life.resident.present final life.resident.ordered (Nat.le_refl _)
  refine ⟨removal_at_gap trace ended live (life.gone ended), ?_⟩
  rw [trace.notes_eq final life.bounded]
  exact birthAt_eq_some.mpr life.resident

/-- Reusing a name requires a prior removal of the earlier incarnation,
even when the two components have disjoint provision declarations. -/
theorem Lifetime.release_before_reuse {trace : Trace program last} {name : Name}
    {first final next : Nat} (life : Lifetime trace name first final)
    (replacement : BornAt trace name next) (later : first < next) :
    final < next - 1 ∧ trace.event final = .command (.remove name) ∧
      (trace.notes final).1 name = some first := by
  have releaseEarlier : final < next - 1 := by
    apply Nat.lt_of_not_ge
    intro held
    exact life.resident.present (next - 1) (by omega) held replacement.2.2.1
  exact ⟨releaseEarlier, life.release (by have := replacement.2.1; omega)⟩

/-- An actual removal certifies the last cut of precisely the targeted
incarnation, by its pre-command stamp. -/
theorem lifetime_of_removal (trace : Trace program last) {time : Nat} (bounded : time < last)
    {name : Name} {birth : Nat} (event : trace.event time = .command (.remove name))
    (stamp : (trace.notes time).1 name = some birth) :
    Lifetime trace name birth time := by
  have step := (trace.step time bounded).1
  rw [event] at step
  refine ⟨?_, Nat.le_of_lt bounded, fun _ => ?_⟩
  · rw [trace.notes_eq time (Nat.le_of_lt bounded)] at stamp
    exact resident_of_birthAt stamp
  · have endpoint : trace.state (time + 1) = erase (trace.state time) name := step.2
    simp [endpoint, erase]

/-- Two distinct incarnations with a common declared provision occupy
disjoint intervals. This holds for inactive and retired rows as well. -/
theorem conflicting_lifetimes (trace : Trace program last)
    {first second : Name} {a b endA endB : Nat}
    (left : Lifetime trace first a endA) (right : Lifetime trace second b endB)
    (different : a ≠ b) {row other : F}
    (original : trace.state a first = some row) (otherOriginal : trace.state b second = some other)
    (key : Key) (reserves : row.component.provides key = true) (otherReserves : other.component.provides key = true) :
    endA < b ∨ endB < a := by
  by_cases separated : endA < b
  · exact .inl separated
  by_cases otherSeparated : endB < a
  · exact .inr otherSeparated
  exfalso
  let time := max a b
  have aa := left.resident.ordered
  have bb := right.resident.ordered
  have within : time ≤ last := by have := left.bounded; omega
  have sideA := left.resident.prefix time (by omega) (by omega)
  have sideB := right.resident.prefix time (by omega) (by omega)
  have names : first ≠ second := by
    intro same
    subst second
    exact different (sideA.unique sideB)
  have stable (point : Nat) (valid : point < last) : Frame.Stable (trace.state point) (trace.state (point + 1)) :=
    transition_stable (trace.step point valid).1
  cases firstAt : trace.state time first with
  | none => exact sideA.present time sideA.ordered (Nat.le_refl _) firstAt
  | some current =>
    cases secondAt : trace.state time second with
    | none => exact sideB.present time sideB.ordered (Nat.le_refl _) secondAt
    | some otherCurrent =>
      have sameA := (sideA.metadata_of_stable stable within original firstAt).1
      have sameB := (sideB.metadata_of_stable stable within otherOriginal secondAt).1
      exact (trace.ownership time within).2 first second current otherCurrent firstAt secondAt names key
        ⟨sameA ▸ reserves, sameB ▸ otherReserves⟩

/-- For conflicting reservations the birth order is recovered from the
order of their removal cuts, treating the endpoint as the last cut of a
surviving incarnation. -/
theorem conflicting_birth_order (trace : Trace program last)
    {first second : Name} {a b endA endB : Nat}
    (left : Lifetime trace first a endA) (right : Lifetime trace second b endB)
    (different : a ≠ b) {row other : F}
    (original : trace.state a first = some row) (otherOriginal : trace.state b second = some other)
    (key : Key) (reserves : row.component.provides key = true) (otherReserves : other.component.provides key = true) :
    a < b ↔ endA < endB := by
  have earlier := left.resident.ordered
  have later := right.resident.ordered
  rcases conflicting_lifetimes trace left right different original otherOriginal key reserves otherReserves with
    leftFirst | rightFirst <;> omega

def releasedAddress : AddressedCommand Name Key Code → Option Address
  | .remove address _ => some address
  | _ => none

/-- The removal component of the addressed orchestration input. -/
noncomputable def removalAddress (trace : Trace program last) (time : Nat) : Option Address :=
  (commandAt trace time).bind releasedAddress

theorem removalAddress_eq_some (trace : Trace program last) {time : Nat} {address : Address} :
    removalAddress trace time = some address ↔
      ∃ name birth, trace.event time = .command (.remove name) ∧
        (trace.notes time).1 name = some birth ∧ Addressed trace birth address ∧
        trace.state time name ≠ none := by
  cases event : trace.event time with
  | lifecycle => simp [removalAddress, commandAt, event]
  | command command =>
    cases command with
    | insert => simp [removalAddress, commandAt, releasedAddress, event]
    | retire name =>
      cases target : targetAt trace time name <;> simp [removalAddress, commandAt, releasedAddress, event, target]
    | remove name =>
      constructor
      · intro found
        cases target : targetAt trace time name with
        | none => simp [removalAddress, commandAt, event, target] at found
        | some value =>
          obtain ⟨other, component⟩ := value
          have same : other = address := by simpa [removalAddress, commandAt, releasedAddress, event, target] using found
          subst other
          obtain ⟨birth, row, tag, path, actual, _⟩ := (targetAt_eq_some trace).mp target
          exact ⟨name, birth, rfl, tag, path, by simp [actual]⟩
      · rintro ⟨who, birth, equal, tag, path, present⟩
        have same : name = who := (OrchestrationSorting.Command.remove.inj (Event.command.inj equal))
        subst who
        cases actual : trace.state time name with
        | none => exact False.elim (present actual)
        | some row =>
          have target := (targetAt_eq_some trace).mpr ⟨birth, row, tag, path, actual, rfl⟩
          simp [removalAddress, commandAt, releasedAddress, event, target]

noncomputable def releasesBefore (trace : Trace program last) (time : Nat) : List Address :=
  (List.range time).filterMap (removalAddress trace)

theorem releases_of_input (trace : Trace program last) :
    releasesBefore trace last = (orchestrationInput trace).filterMap releasedAddress := by
  rw [orchestrationInput, List.filterMap_filterMap]
  rfl

private theorem releases_length_le (trace : Trace program last) {first later : Nat} (ordered : first ≤ later) :
    (releasesBefore trace first).length ≤ (releasesBefore trace later).length := by
  have split : List.range later =
      List.range first ++ (List.range (later - first)).map (fun offset => first + offset) := by
    simpa only [Nat.add_sub_of_le ordered] using (List.range_add (n := first) (m := later - first))
  unfold releasesBefore
  rw [split, List.filterMap_append, List.length_append]
  omega

/-- A surviving reservation has rank after all recorded removals. -/
noncomputable def releaseRank (trace : Trace program last) (address : Address) : Nat :=
  (releasesBefore trace last).idxOf address

private theorem Lifetime.born {trace : Trace program last} {name : Name} {birth final : Nat}
    (life : Lifetime trace name birth final) : BornAt trace name birth := by
  have starts := life.resident.ordered
  have bounded := life.bounded
  have positive : birth ≠ 0 := by
    intro zero
    have live := life.resident.present 0 (by omega) (by omega)
    exact live (congrFun trace.start name)
  exact ⟨by omega, by omega, life.resident.boundary.resolve_left positive,
    life.resident.present birth (Nat.le_refl _) starts⟩

private theorem removalAddress_unique (trace : Trace program last) {name : Name} {birth final : Nat}
    (life : Lifetime trace name birth final) {address : Address} (addressed : Addressed trace birth address)
    {time : Nat} (valid : time < last) (found : removalAddress trace time = some address) :
    time = final := by
  obtain ⟨target, stamp, event, tag, path, _⟩ := (removalAddress_eq_some trace).mp found
  have sameBirth := path.injective addressed rfl
  subst stamp
  have sameName := born_unique trace (recorded_birth trace (Nat.le_of_lt valid) tag).1 life.born
  subst target
  exact (lifetime_of_removal trace valid event tag).unique life

theorem Lifetime.release_rank {trace : Trace program last} {name : Name} {birth final : Nat}
    (life : Lifetime trace name birth final) {address : Address} (addressed : Addressed trace birth address) :
    releaseRank trace address = (releasesBefore trace final).length := by
  have noEarly : address ∉ releasesBefore trace final := by
    intro member
    obtain ⟨time, atCut, found⟩ := List.mem_filterMap.mp member
    have before := List.mem_range.mp atCut
    have exactCut := removalAddress_unique trace life addressed (Nat.lt_of_lt_of_le before life.bounded) found
    omega
  cases Nat.eq_or_lt_of_le life.bounded with
  | inl held =>
    rw [held] at noEarly ⊢
    exact List.idxOf_eq_length noEarly
  | inr released =>
    obtain ⟨event, stamp⟩ := life.release released
    have present := life.resident.present final life.resident.ordered (Nat.le_refl _)
    have tag := (removalAddress_eq_some trace).mpr ⟨name, birth, event, stamp, addressed, present⟩
    have split : List.range last = (List.range final ++ [final]) ++
        (List.range (last - (final + 1))).map (fun offset => final + 1 + offset) := by
      have bounded : final + 1 ≤ last := by omega
      simpa only [Nat.add_sub_of_le bounded, List.range_succ (n := final)] using
        (List.range_add (n := final + 1) (m := last - (final + 1)))
    unfold releaseRank
    unfold releasesBefore at *
    rw [split, List.filterMap_append, List.filterMap_append, List.append_assoc]
    simp [tag, List.idxOf_append, noEarly]

/-- A particular incarnation was released before a cut exactly when its
address appears before the cut's count of releases. A row that survives
the whole history has rank equal to the final count. -/
theorem Lifetime.released_before {trace : Trace program last} {name : Name} {birth final cut : Nat}
    (life : Lifetime trace name birth final) {address : Address} (addressed : Addressed trace birth address)
    (bounded : cut ≤ last) : final < cut ↔ releaseRank trace address < (releasesBefore trace cut).length := by
  rw [life.release_rank addressed]
  refine ⟨?_, fun earlier => Nat.lt_of_not_ge (fun later => Nat.not_lt_of_ge (releases_length_le trace later) earlier)⟩
  intro earlier
  obtain ⟨event, tag⟩ := life.release (by omega)
  have found := (removalAddress_eq_some trace).mpr
    ⟨name, birth, event, tag, addressed, life.resident.present final life.resident.ordered (Nat.le_refl _)⟩
  have added : (releasesBefore trace (final + 1)).length = (releasesBefore trace final).length + 1 := by
    simp [releasesBefore, List.range_succ, List.filterMap_append, found]
  have through := releases_length_le trace (Nat.succ_le_of_lt earlier)
  change (releasesBefore trace (final + 1)).length ≤ (releasesBefore trace cut).length at through
  omega

/-- Any birth at a previously occupied name follows the addressed removal
of the earlier incarnation, already recorded in the command prefix. -/
theorem addressed_release_before_reuse (trace : Trace program last)
    {name : Name} {first next : Nat}
    (earlier : BornAt trace name first) (replacement : BornAt trace name next) (ordered : first < next) :
    ∃ final address, final < next - 1 ∧ Addressed trace first address ∧
      removalAddress trace final = some address ∧ address ∈ releasesBefore trace (next - 1) := by
  obtain ⟨final, lifetime⟩ := lifetime_of_birth trace earlier
  obtain ⟨released, event, stamp⟩ := lifetime.release_before_reuse replacement ordered
  have before : final < next - 1 := released
  obtain ⟨address, addressed⟩ := exists_address trace earlier
  have found := (removalAddress_eq_some trace).mpr
    ⟨name, first, event, stamp, addressed, lifetime.resident.present final lifetime.resident.ordered (Nat.le_refl _)⟩
  exact ⟨final, address, before, addressed, found, List.mem_filterMap.mpr ⟨final, List.mem_range.mpr before, found⟩⟩

/-- A root insertion at a previously occupied name follows the addressed
removal of that earlier incarnation. The release has already occurred in
the input prefix at the insertion cut. -/
theorem addressed_release_before_root_reinsertion (trace : Trace program last)
    {name : Name} {first cut : Nat} {component : Component Key Code}
    (earlier : BornAt trace name first) (ordered : first ≤ cut) (bounded : cut < last)
    (insertion : trace.event cut = .command (.insert name component)) :
    ∃ final address, final < cut ∧ Addressed trace first address ∧
      removalAddress trace final = some address ∧ address ∈ releasesBefore trace cut := by
  have step := (trace.step cut bounded).1
  rw [insertion] at step
  have nextPresent : trace.state (cut + 1) name ≠ none := by
    rw [step.2, OrchestrationSorting.Command.apply, put_self]
    exact Option.noConfusion
  have replacement : BornAt trace name (cut + 1) :=
    ⟨by omega, by omega, by simpa using step.1.1, nextPresent⟩
  simpa using addressed_release_before_reuse trace earlier replacement (by omega)

private theorem release_ranks_ordered (trace : Trace program last)
    {first second : Name} {a b endA endB : Nat} {address otherAddress : Address}
    (left : Lifetime trace first a endA) (right : Lifetime trace second b endB)
    (addressed : Addressed trace a address) (otherAddressed : Addressed trace b otherAddress) :
    endA < endB ↔ releaseRank trace address < releaseRank trace otherAddress := by
  rw [left.release_rank addressed, right.release_rank otherAddressed]
  refine ⟨?_, fun earlier => Nat.lt_of_not_ge (fun late =>
    Nat.not_lt_of_ge (releases_length_le trace late) earlier)⟩
  intro order
  have valid := Nat.lt_of_lt_of_le order right.bounded
  obtain ⟨event, stamp⟩ := left.release valid
  have tag := (removalAddress_eq_some trace).mpr
    ⟨first, a, event, stamp, addressed, left.resident.present endA left.resident.ordered (Nat.le_refl _)⟩
  have plusOne : (releasesBefore trace (endA + 1)).length = (releasesBefore trace endA).length + 1 := by
    simp [releasesBefore, List.range_succ, List.filterMap_append, tag]
  have through : (releasesBefore trace (endA + 1)).length ≤ (releasesBefore trace endB).length :=
    releases_length_le trace (Nat.succ_le_of_lt order)
  omega

structure Reservation (trace : Trace program last) (key : Key) where
  name : Name
  birth : Nat
  final : Nat
  address : Address
  life : Lifetime trace name birth final
  addressed : Addressed trace birth address
  reserves : ∃ row, trace.state birth name = some row ∧ row.component.provides key = true

/-- Construct a reservation from the row that an actual removal releases.
The same component reserved the key throughout its uninterrupted lifetime. -/
theorem reservation_of_removal (trace : Trace program last) {cut : Nat} (bounded : cut < last)
    {name : Name} {row : F} {key : Key} {path : Address} {birth : Nat}
    (event : trace.event cut = .command (.remove name)) (found : trace.state cut name = some row)
    (tag : (trace.notes cut).1 name = some birth) (addressed : Addressed trace birth path)
    (reserves : row.component.provides key = true) :
    ∃ r : Reservation trace key, r.name = name ∧ r.birth = birth ∧ r.address = path ∧ r.final = cut := by
  have life := lifetime_of_removal trace bounded event tag
  have born := life.born
  cases initial : trace.state birth name with
  | none => exact False.elim (born.2.2.2 initial)
  | some first =>
    have part := (life.resident.metadata_of_stable
      (fun i valid => transition_stable (trace.step i valid).1) (Nat.le_of_lt bounded) initial found).1
    exact ⟨⟨name, birth, cut, path, life, addressed, first, initial, part.symm ▸ reserves⟩, rfl, rfl, rfl, rfl⟩

/-- A row observed at an actual cut witnesses the reservation of its
current incarnation, with the declaration from its birth. -/
theorem reservation_at_cut (trace : Trace program last) {cut : Nat} (bounded : cut ≤ last)
    {name : Name} {row : F} {key : Key}
    (found : trace.state cut name = some row) (reserves : row.component.provides key = true) :
    ∃ r : Reservation trace key, r.name = name ∧ r.birth ≤ cut ∧ cut ≤ r.final ∧
      (trace.notes cut).1 name = some r.birth := by
  cases tag : (trace.notes cut).1 name with
  | none =>
    have vacant := (trace.births_agree cut bounded name).mp tag
    rw [found] at vacant
    cases vacant
  | some birth =>
    obtain ⟨born, before⟩ := recorded_birth trace bounded tag
    obtain ⟨final, life⟩ := lifetime_of_birth trace born
    have resident := Incarnation.resident_of_birthAt (by rwa [trace.notes_eq cut bounded] at tag : _)
    have through : cut ≤ final := by
      apply Nat.le_of_not_gt
      intro after
      exact resident.present (final + 1) (by have := life.resident.ordered; omega) (by omega) (life.gone (by omega))
    obtain ⟨address, addressed⟩ := exists_address trace born
    cases initial : trace.state birth name with
    | none => exact False.elim (born.2.2.2 initial)
    | some first =>
      have component := (resident.metadata_of_stable
        (fun i valid => transition_stable (trace.step i valid).1) bounded initial found).1
      exact ⟨⟨name, birth, final, address, life, addressed, first, initial, component.symm ▸ reserves⟩,
        rfl, before, through, rfl⟩

theorem Reservation.birth_order {trace : Trace program last} {key : Key}
    (left right : Reservation trace key) (different : left.address ≠ right.address) :
    left.birth < right.birth ↔ releaseRank trace left.address < releaseRank trace right.address := by
  have births : left.birth ≠ right.birth := by
    intro same
    exact different (left.addressed.unique (same.symm ▸ right.addressed))
  obtain ⟨row, actual, reserved⟩ := left.reserves
  obtain ⟨other, otherActual, otherReserved⟩ := right.reserves
  exact (conflicting_birth_order trace left.life right.life births actual otherActual key reserved otherReserved).trans
    (release_ranks_ordered trace left.life right.life left.addressed right.addressed)

/-- The earlier reservation has an actual O-Remove event strictly before
the later allocation. Its stamp identifies exactly the old incarnation. -/
theorem Reservation.release_before_birth {trace : Trace program last} {key : Key}
    (left right : Reservation trace key) (earlier : left.birth < right.birth) :
    left.final < right.birth - 1 ∧ trace.event left.final = .command (.remove left.name) ∧
      (trace.notes left.final).1 left.name = some left.birth := by
  obtain ⟨row, actual, reserves⟩ := left.reserves
  obtain ⟨other, otherActual, otherReserves⟩ := right.reserves
  have first := left.life.resident.ordered
  have earlierEnd : left.final < right.birth := by
    rcases conflicting_lifetimes trace left.life right.life (Nat.ne_of_lt earlier)
      actual otherActual key reserves otherReserves with before | after
    · exact before
    · have := right.life.resident.ordered
      omega
  have within := right.life.born.2.1
  have bounded : left.final < last := by omega
  have ⟨removed, pinned⟩ := left.life.release bounded
  refine ⟨?_, removed, pinned⟩
  apply Nat.lt_of_le_of_ne (by omega)
  intro same
  have step := (trace.step left.final bounded).1
  rw [removed] at step
  have endpoint : trace.state (left.final + 1) = erase (trace.state left.final) left.name := step.2
  have before := right.life.born.2.2.1
  rw [← same] at before
  have absent : trace.state (left.final + 1) right.name = none := by
    by_cases sameName : right.name = left.name <;> simp [endpoint, erase, sameName, before]
  have cut : left.final + 1 = right.birth := by omega
  exact right.life.born.2.2.2 (cut ▸ absent)

/-- The same ordered removals, compared by birth address, force the same
order of any two competing reservations in independently scheduled runs. -/
theorem matching_releases_fix_birth_order {otherProgram : Code → Instruction Name Key Value Code Error} {otherLast : Nat}
    {trace : Trace program last} {other : Trace otherProgram otherLast} {key : Key}
    (sameReleases : releasesBefore trace last = releasesBefore other otherLast)
    (left right : Reservation trace key) (newLeft newRight : Reservation other key)
    (matchesLeft : left.address = newLeft.address) (matchesRight : right.address = newRight.address)
    (different : left.address ≠ right.address) :
    left.birth < right.birth ↔ newLeft.birth < newRight.birth := by
  rw [left.birth_order right different,
    newLeft.birth_order newRight (by rwa [← matchesLeft, ← matchesRight])]
  unfold releaseRank
  rw [sameReleases, matchesLeft, matchesRight]

theorem matching_commands_fix_birth_order {otherProgram : Code → Instruction Name Key Value Code Error} {otherLast : Nat}
    {trace : Trace program last} {other : Trace otherProgram otherLast} {key : Key}
    (commands : orchestrationInput trace = orchestrationInput other)
    (left right : Reservation trace key) (newLeft newRight : Reservation other key)
    (matchesLeft : left.address = newLeft.address) (matchesRight : right.address = newRight.address)
    (different : left.address ≠ right.address) :
    left.birth < right.birth ↔ newLeft.birth < newRight.birth :=
  matching_releases_fix_birth_order (by rw [releases_of_input, releases_of_input, commands])
    left right newLeft newRight matchesLeft matchesRight different

end Cordis.Repairs.GuardedReservationOrder
