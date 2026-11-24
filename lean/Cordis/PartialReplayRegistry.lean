import Cordis.PartialReplaySlots
import Cordis.Ordering
import Cordis.PartialReplayRouting
import Cordis.EntangledApplications

/-! Extract the operation captures and discharges from the nine registry rules.
One slot's pending words can then follow the actual actor accumulators. -/
namespace Cordis.PartialReplayRegistry

open Calculus Stages StageRecovery
open PartialCoeffectLifting (PartialMap compose)
open PartialReplaySlots (InverseMeaning Agrees captures)
open PartialReplayHistory (History KeyLaws run keepMissing eraseAfter)
open Iterators (OptionRel)
universe u
variable {Name Key Value Code Error : Type u} [DecidableEq Name]
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
local notation "I" => Inverse Name Key Value
local notation "Program" => Code → Instruction Name Key Value Code Error

def saved (state : R) (actor : Name) : List I :=
  ((state actor).map fun fiber => fiber.phase.accumulator).getD []

private theorem saved_modify (state : R) (actor : Name) (change : F → F)
    (phase : ∀ fiber, (change fiber).phase = fiber.phase) :
    saved (Calculus.modify state actor change) = saved state := by
  funext name
  by_cases same : name = actor
  · subst name
    cases present : state actor <;> simp [saved, Calculus.modify, present, phase]
  · simp [saved, Calculus.modify, same]

private theorem saved_insert (state : R) (actor : Name) (child : F)
    (freshSlot : state actor = none) (stack : child.phase.accumulator = []) :
    saved (put state actor child) = saved state := by
  funext name
  by_cases isActor : name = actor
  · subst name
    simp [saved, put, freshSlot, stack]
  · simp [saved, put, isActor]

private theorem saved_erase (state : R) (actor : Name) (empty : saved state actor = []) :
    saved (erase state actor) = saved state := by
  funext name
  by_cases isActor : name = actor
  · subst name
    simpa [saved, erase] using empty.symm
  · simp [saved, erase, isActor]

theorem saved_mark (state : R) (actor : Name) (fiber : F)
    (present : state actor = some fiber) (phase : Phase Name Key Code I) (reader : Name) :
    saved (mark state actor phase) reader =
      if reader = actor then phase.accumulator else saved state reader := by
  by_cases same : reader = actor
  · subst reader
    simp [saved, mark, Calculus.modify, present]
  · simp [saved, mark, Calculus.modify, same]

variable [DecidableEq Key]

private theorem saved_land (program : Program) {actor : Name} {code : Code} {r s : R}
    {inverse : I} {next : Option Code} (land : Land program actor code r s inverse next) :
    saved s = saved r := by
  cases land with
  | unit => rfl
  | provide => exact saved_modify _ _ _ (fun _ => rfl)
  | operate => exact saved_modify _ _ _ (fun _ => rfl)
  | instantiate _ _ _ component child _ allowed =>
    exact saved_insert r child (fresh component (some actor)) allowed.1 rfl

private theorem saved_undo (state : R) (inverse : I) :
    saved (Stages.undo inverse state) = saved state := by
  cases inverse with
  | unit => rfl
  | restrict => exact saved_modify _ _ _ (fun _ => rfl)
  | operate => exact saved_modify _ _ _ (fun _ => rfl)
  | retire => exact saved_modify _ _ _ (fun _ => rfl)

theorem saved_discharge (state : R) (word : List I) :
    saved (discharge Stages.undo word state) = saved state := by
  induction word generalizing state with
  | nil => rfl
  | cons inverse rest earlier =>
    exact (earlier (Stages.undo inverse state)).trans (saved_undo _ _)

inductive ReplayEvent (program : Program) (actor : Name) : R → R → Prop where
  | control {r s} :
      RuleEvaluation.TablesUnchanged r s →
      saved s = saved r →
      ReplayEvent program actor r s
  | capture {r middle s code inverse next}
      (landed : Land program actor code r middle inverse next)
      (tables : RuleEvaluation.TablesUnchanged middle s)
      (pushed : ∀ n, saved s n = if n = actor then inverse :: saved r n else saved r n)
      (presence : ∀ n, s n = none ↔ middle n = none) :
      ReplayEvent program actor r s
  | cleanup {r s word}
      (selected : saved r actor = word)
      (free : ¬ Relied r actor)
      (tables : RuleEvaluation.TablesUnchanged (discharge Stages.undo word r) s)
      (cleared : ∀ n, saved s n = if n = actor then [] else saved r n)
      (closed : ControlFrame.viewAt s actor = none) :
      ReplayEvent program actor r s

theorem saved_after_landing (program : Program) {actor : Name} {code : Code} {r s : R}
    {inverse : I} {next : Option Code} (land : Land program actor code r s inverse next)
    (fiber : F) (present : r actor = some fiber) (phase : Phase Name Key Code I)
    (stack : phase.accumulator = inverse :: fiber.phase.accumulator) :
    ∀ name, saved (mark s actor phase) name =
      if name = actor then inverse :: saved r name else saved r name := by
  obtain ⟨after, landed, _⟩ := Ordering.land_existing_phases program land actor fiber present
  intro name
  rw [saved_mark s actor after landed, saved_land program land, stack]
  by_cases isActor : name = actor
  · subst name
    simp [saved, present]
  · simp [isActor]

private theorem landing_event (program : Program) {actor : Name} {code : Code} {r s : R}
    {inverse : I} {next : Option Code} (land : Land program actor code r s inverse next)
    (fiber : F) (present : r actor = some fiber) (phase : Phase Name Key Code I)
    (stack : phase.accumulator = inverse :: fiber.phase.accumulator) :
    ReplayEvent program actor r (mark s actor phase) := by
  obtain ⟨after, landed, _⟩ := Ordering.land_existing_phases program land actor fiber present
  apply ReplayEvent.capture land
  · intro owner key
    exact (tableAt_mark s actor owner key phase).symm
  · exact saved_after_landing program land fiber present phase stack
  · intro name
    by_cases same : name = actor
    · subst name
      simp [mark, Calculus.modify, landed]
    · simp [mark, Calculus.modify, same]

private theorem mark_control (program : Program) {actor : Name} {state : R}
    (fiber : F) (present : state actor = some fiber) (phase : Phase Name Key Code I)
    (stack : phase.accumulator = fiber.phase.accumulator) :
    ReplayEvent program actor state (mark state actor phase) := by
  apply ReplayEvent.control
  · intro owner key
    exact (tableAt_mark state actor owner key phase).symm
  · funext name
    rw [saved_mark state actor fiber present, stack]
    by_cases isActor : name = actor
    · subst name
      simp [saved, present]
    · simp [isActor]

theorem saved_of_command (program : Program) {rule : Labeled.Rule} {actor : Name} {r s : R}
    (step : Labeled.Step program rule actor r s)
    (command : rule = .insert ∨ rule = .retire ∨ rule = .remove) : saved s = saved r := by
  cases step with
  | insert _ _ component parent ready => exact saved_insert r actor _ ready.1 rfl
  | retire => exact saved_modify r actor _ (fun _ => rfl)
  | remove _ _ ready =>
    apply saved_erase
    cases lookup : r actor with
    | none => simp [saved, lookup]
    | some fiber =>
      simp only [Removable, lookup] at ready
      simp [saved, lookup, ready.2.1, Phase.accumulator]
  | _ => simp at command

/-- All nine rules either preserve the pending stack at each actor, push one
actual capture, or clear the entire actual stack of the unloading actor. -/
theorem event_of_step (program : Program) {rule : Labeled.Rule} {actor : Name} {r s : R}
    (step : Labeled.Step program rule actor r s) : ReplayEvent program actor r s := by
  cases step with
  | insert _ _ component parent ready =>
    exact .control ((RuleEvaluation.Edit.insert actor component parent).preserves_tables r ready.1)
      (saved_insert r actor _ ready.1 rfl)
  | retire _ _ _ =>
    exact .control ((RuleEvaluation.Edit.retire actor).preserves_tables r True.intro)
      (saved_modify r actor _ (fun _ => rfl))
  | remove _ _ ready =>
    cases lookup : r actor with
    | none => simp [Removable, lookup] at ready
    | some fiber =>
      simp only [Removable, lookup] at ready
      refine .control ((RuleEvaluation.Edit.remove actor).preserves_tables r ?_) (saved_erase r actor ?_)
      · intro key
        simpa only [tableAt, lookup, Option.bind_some] using ready.2.2.1 key
      · simp [saved, lookup, ready.2.1, Phase.accumulator]
  | begin _ _ fiber view present inactive _ _ =>
    exact mark_control program fiber present _ (by simp [inactive, Phase.accumulator])
  | iter _ middle _ fiber code word view inverse next present reloading _ landed =>
    exact landing_event program landed fiber present _ (by simp [reloading, Phase.accumulator])
  | finish _ middle _ fiber code word view inverse present reloading _ landed =>
    exact landing_event program landed fiber present _ (by simp [reloading, Phase.accumulator])
  | divert _ middle _ fiber code word view tail present reloading _ branch =>
    rcases branch with ⟨rfl, rfl⟩ | ⟨inverse, next, landed, rfl⟩
    · exact mark_control program fiber present _ (by simp [reloading, Phase.accumulator])
    · exact landing_event program landed fiber present _ (by simp [reloading, Phase.accumulator])
  | leave _ _ fiber word view present phase _ =>
    exact mark_control program fiber present _ (by simp [phase, Phase.accumulator])
  | unload _ _ fiber word view present phase free =>
    obtain ⟨after, landed, _⟩ := Ordering.discharge_existing_phases r word actor fiber present
    exact .cleanup (by simp [saved, present, phase, Phase.accumulator]) free
      (fun owner key => (tableAt_mark _ actor owner key .inactive).symm)
      (fun name => by rw [saved_mark _ actor after landed, saved_discharge]; rfl)
      (by rw [ControlFrame.mark_viewAt _ _ _ _ landed, if_pos rfl]; rfl)

private theorem event_of_calculus_step (program : Program) {r s : R}
    (step : Calculus.Step (Land program) Stages.undo r s) :
    ∃ actor, ReplayEvent program actor r s := by
  obtain ⟨_, actor, labeled⟩ := Labeled.Step.ofCalculus step
  exact ⟨actor, event_of_step program labeled⟩

/-- Partial denotations for the coeffect operations of the ordinary
calculus. The total inverse function carried by a syntax token is an
implementation representative; only defined calls are used. -/
structure Coeffects (program : Program) where
  denote : InverseMeaning Key Value
  agrees : Agrees denote
  admitted : Key → PartialMap Value → Prop
  observe : Key → Setoid Value
  laws : ∀ key, KeyLaws (observe key) (admitted key)
  captured : ∀ code key call,
    (program code).action = .operate key call →
    ∀ before after inverse result, call before = .ok (after, inverse, result) →
    admitted key (denote key inverse) ∧ denote key inverse after = some before
  forward : ∀ code key call, (program code).action = .operate key call →
    admitted key (fun value => (call value).toOption.map Prod.fst)

private def asOperation (denote : InverseMeaning Key Value) (key : Key)
    (call : Value → Except Error (Value × (Value → Value) × Value)) :
    PartialInverseObservation.Operation Value Value where
  run value :=
    match call value with
    | .ok (after, inverse, result) => some (after, denote key inverse, result)
    | .error _ => none

omit [DecidableEq Name] [DecidableEq Key] in
theorem located_value {r : R} {actor owner : Name} {key : Key} {value : Value}
    (located : location r actor key = some (owner, value)) : tableAt r owner key = some value := by
  obtain ⟨selected, _, found⟩ := Option.bind_eq_some_iff.mp located
  obtain ⟨loaded, loadedValue, equal⟩ := Option.map_eq_some_iff.mp found
  cases equal
  exact loadedValue

theorem tableAt_write (r : R) (owner reader : Name) (key selected : Key) (value : Value)
    (liveOwner : r owner ≠ none) :
    tableAt (write r owner key (some value)) reader selected =
      if reader = owner ∧ selected = key then some value else tableAt r reader selected := by
  by_cases same : reader = owner
  · subst reader
    cases present : r owner with
    | none => exact False.elim (liveOwner present)
    | some fiber =>
      by_cases sameKey : selected = key <;> simp [tableAt, write, Calculus.modify, sameKey, present]
  · simp [tableAt, write, Calculus.modify, same]

private inductive SlotLanding {program : Program} (meaning : Coeffects program) (owner : Name) (key : Key) :
    Option Value → Option Value → List (PartialMap Value) → Prop
  | unchanged (value) : SlotLanding meaning owner key value value []
  | provision (value) : SlotLanding meaning owner key none (some value) []
  | operation {before after : Value} {inverse : PartialMap Value} (call : PartialInverseObservation.Operation Value Value)
      (result : Value) :
      call.run before = some (after, inverse, result) →
      meaning.admitted key inverse → inverse after = some before →
      SlotLanding meaning owner key (some before) (some after) [inverse]

private theorem project_landing {program : Program} (meaning : Coeffects program)
    (owner : Name) (key : Key) {actor : Name} {code : Code} {r s : R} {inverse : I}
    {next : Option Code} (land : Land program actor code r s inverse next) :
    SlotLanding meaning owner key (tableAt r owner key) (tableAt s owner key)
      (captures meaning.denote owner key [inverse]) := by
  cases land with
  | unit => exact .unchanged _
  | instantiate _ _ _ component child _ allowed =>
    have still := (RuleEvaluation.Edit.insert child component (some actor)).preserves_tables r allowed.1 owner key
    change tableAt r owner key = tableAt (put r child (fresh component (some actor))) owner key at still
    rw [← still]
    exact .unchanged _
  | provide _ _ _ fiber provided value _ present _ absent =>
    rw [tableAt_write _ _ _ _ _ _ (by simp [present])]
    by_cases selected : owner = actor ∧ key = provided
    · obtain ⟨rfl, rfl⟩ := selected
      simp only [tableAt, present, Option.bind_some, absent, true_and, if_pos]
      exact .provision _
    · rw [if_neg selected]
      exact .unchanged _
  | operate _ _ _ changed callback writer before after inverse result codeIs located called =>
    have bound : tableAt r writer changed = some before := located_value located
    have liveOwner : r writer ≠ none := by
      intro absent
      simp [tableAt, absent] at bound
    rw [tableAt_write _ _ _ _ _ _ liveOwner]
    by_cases selected : owner = writer ∧ key = changed
    · obtain ⟨rfl, rfl⟩ := selected
      have recognized := meaning.captured _ _ _ codeIs before after inverse result called
      rw [bound, if_pos ⟨rfl, rfl⟩]
      simpa [captures] using SlotLanding.operation (meaning := meaning) (owner := owner)
        (key := key) (asOperation meaning.denote key callback) result
        (by simp [asOperation, called]) recognized.1 recognized.2
    · simp only [if_neg selected, captures, List.filterMap_cons_none, List.filterMap_nil]
      exact .unchanged _

abbrev Ticket (Name Value : Type u) := Name × PartialMap Value

def ticketsFor (tickets : List (Ticket Name Value)) (actor : Name) : List (PartialMap Value) :=
  (tickets.filter fun ticket => decide (ticket.1 = actor)).map Prod.snd

def remaining (tickets : List (Ticket Name Value)) (actor : Name) : List (Ticket Name Value) :=
  tickets.filter fun ticket => !(decide (ticket.1 = actor))

theorem ticket_partition (tickets : List (Ticket Name Value)) (actor : Name) :
    (ticketsFor tickets actor ++ (remaining tickets actor).map Prod.snd).Perm (tickets.map Prod.snd) := by
  simpa only [List.map_append] using
    (List.filter_append_perm (fun (ticket : Ticket Name Value) => decide (ticket.1 = actor)) tickets).map Prod.snd

private theorem ticketsFor_remaining (tickets : List (Ticket Name Value)) (actor reader : Name) :
    ticketsFor (remaining tickets actor) reader =
      if reader = actor then [] else ticketsFor tickets reader := by
  by_cases same : reader = actor
  · subst reader
    simp [ticketsFor, remaining, List.filter_filter, Bool.and_not_self]
  · rw [if_neg same]
    unfold ticketsFor remaining
    rw [List.filter_filter]
    congr 1
    apply congrArg (fun select => tickets.filter select)
    funext pair
    by_cases equal : pair.1 = reader
    · simp [equal, same]
    · simp [equal]

private theorem remaining_nil (tickets : List (Ticket Name Value)) (actor : Name)
    (noOthers : ∀ reader, reader ≠ actor → ticketsFor tickets reader = []) :
    remaining tickets actor = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro ticket member selected
  have different : ticket.1 ≠ actor := by simpa using selected
  have found : ticket.2 ∈ ticketsFor tickets ticket.1 :=
    List.mem_map.mpr ⟨ticket, List.mem_filter.mpr ⟨member, by simp⟩, rfl⟩
  rw [noOthers ticket.1 different] at found
  exact List.not_mem_nil found

def SlotHistory {program : Program} (meaning : Coeffects program) (state : R) (owner : Name) (key : Key) : Prop :=
  ∃ pending : List (Ticket Name Value),
    (∀ actor, ticketsFor pending actor = captures meaning.denote owner key (saved state actor)) ∧
    match tableAt state owner key with
    | none => pending = []
    | some value => History (meaning.admitted key) value (pending.map Prod.snd)

private theorem step_capture_history {program : Program} (meaning : Coeffects program)
    {r s middle : R} {actor owner : Name} {key : Key} {inverse : I} {code : Code} {next : Option Code}
    (land : Land program actor code r middle inverse next)
    (tables : RuleEvaluation.TablesUnchanged middle s)
    (pushed : ∀ n, saved s n = if n = actor then inverse :: saved r n else saved r n)
    (history : SlotHistory meaning r owner key) : SlotHistory meaning s owner key := by
  obtain ⟨pending, aligned, lived⟩ := history
  let added := captures meaning.denote owner key [inverse]
  have addOne (n : Name) :
      captures meaning.denote owner key (saved s n) =
      (if n = actor then added else []) ++ captures meaning.denote owner key (saved r n) := by
    rw [pushed n]
    by_cases same : n = actor
    · subst n
      simp only [eq_self, if_true]
      change captures meaning.denote owner key ([inverse] ++ saved r actor) = _
      simp only [added, captures, List.filterMap_append]
    · simp [same]
  refine ⟨(added.map (Prod.mk actor)) ++ pending, ?_, ?_⟩
  · intro n
    rw [addOne n, ← aligned n]
    by_cases same : actor = n
    · subst n
      simp [ticketsFor, List.filter_append, List.filter_map, List.map_map, Function.comp_def]
    · simp [ticketsFor, List.filter_append, List.filter_map, same, Ne.symm same]
  rw [← tables owner key]
  have projection := project_landing meaning owner key land
  change SlotLanding meaning owner key (tableAt r owner key) (tableAt middle owner key) added at projection
  revert lived
  generalize tableAt r owner key = original, tableAt middle owner key = changed,
    added = addedTickets at projection ⊢
  intro lived
  cases projection with
  | unchanged value =>
    simpa using lived
  | provision value =>
    have empty : pending = [] := lived
    simpa [empty] using (History.provide (admitted := meaning.admitted key) value)
  | operation call outcome performed allowed recovered =>
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    exact .acquire call lived performed allowed recovered

theorem saved_restriction_owner {state : R} (routed : PartialReplayRouting.ScopedAccumulators state)
    {actor owner : Name} {key : Key} (member : Inverse.restrict owner key ∈ saved state actor) : owner = actor := by
  cases present : state actor with
  | none => simp [saved, present] at member
  | some fiber =>
    exact PartialReplayRouting.restriction_owner state routed actor owner key fiber present
      (by simpa [saved, present] using member)

/-- If unload is permitted, other actors have no saved map on the
unloader's own binding, even when the map would return the same value. -/
theorem saved_avoids_unloader (state : R) (owner : Name) (key : Key)
    (routed : PartialReplayRouting.ScopedAccumulators state)
    (free : ¬ Relied state owner) (actor : Name) (different : actor ≠ owner)
    (token : I) (member : token ∈ saved state actor) :
    InterleavedRecovery.Avoids owner key token := by
  cases token with
  | unit | retire => trivial
  | restrict holder slot =>
    intro selected
    exact different ((saved_restriction_owner routed member).symm.trans selected.1)
  | operate holder slot undo =>
    intro same
    obtain ⟨rfl, rfl⟩ := same
    cases present : state actor with
    | none => simp [saved, present] at member
    | some fiber =>
      have stored : .operate holder slot undo ∈ fiber.phase.accumulator := by
        simpa [saved, present] using member
      rcases PartialReplayRouting.operation_owner state routed actor holder slot undo fiber present stored with
        self | ⟨view, committed, requires, resolves⟩
      · exact different self.symm
      · exact free (Ordering.demand_relied state actor holder slot
          ⟨fiber, view, present, requires, committed, resolves⟩ different)

private theorem no_foreign_captures {program : Program} (meaning : Coeffects program)
    (state : R) (owner : Name) (key : Key) (routed : PartialReplayRouting.ScopedAccumulators state)
    (free : ¬ Relied state owner) (actor : Name) (different : actor ≠ owner) :
    captures meaning.denote owner key (saved state actor) = [] := by
  apply List.filterMap_eq_nil_iff.mpr
  intro inverse member
  have avoids := saved_avoids_unloader state owner key routed free actor different inverse member
  cases inverse with
  | unit | restrict | retire => rfl
  | operate holder slot undo =>
    exact if_neg (fun same => avoids ⟨same.1.symm, same.2.symm⟩)

private theorem step_cleanup_history {program : Program} (meaning : Coeffects program)
    {r s : R} {actor owner : Name} {key : Key} {word : List I}
    (routed : PartialReplayRouting.ScopedAccumulators r)
    (selected : saved r actor = word) (free : ¬ Relied r actor)
    (tables : RuleEvaluation.TablesUnchanged (discharge Stages.undo word r) s)
    (cleared : ∀ n, saved s n = if n = actor then [] else saved r n)
    (history : SlotHistory meaning r owner key) : SlotHistory meaning s owner key := by
  obtain ⟨pending, aligned, lived⟩ := history
  refine ⟨remaining pending actor, ?_, ?_⟩
  · intro name
    rw [ticketsFor_remaining, cleared name, aligned name]
    by_cases same : name = actor <;> simp [same, captures]
  have partition := ticket_partition pending actor
  rw [aligned actor, selected] at partition
  have output_exact (result : Option Value)
      (performed : PartialReplaySlots.interpret (PartialReplaySlots.slotWord meaning.denote owner key word)
        (tableAt r owner key) = some result) : tableAt s owner key = result := by
    rw [← tables owner key]
    apply PartialReplaySlots.project_word meaning.denote meaning.agrees
    rw [PartialReplaySlots.slotWord_exact]
    exact performed
  cases input : tableAt r owner key with
  | none =>
    have empty : pending = [] := by simpa only [input] using lived
    rcases normalized : PartialReplaySlots.slotWord meaning.denote owner key word with ⟨operations, erases⟩
    have result : tableAt s owner key = none := output_exact none (by
      rw [input, normalized]
      cases erases <;> rfl)
    simp [result, empty, remaining]
  | some value =>
    have active : History (meaning.admitted key) value (pending.map Prod.snd) := by
      simpa only [input] using lived
    rcases normalized : PartialReplaySlots.slotWord meaning.denote owner key word with ⟨operations, erases⟩
    cases erases with
    | false =>
      have unrestricted : Inverse.restrict owner key ∉ word := by
        intro member
        have flag := (PartialReplaySlots.slotWord_erases_iff meaning.denote owner key word).mpr member
        simp [normalized] at flag
      have operations_eq : operations = captures meaning.denote owner key word := by
        have exactWord := PartialReplaySlots.slotWord_unrestricted meaning.denote owner key word unrestricted
        rw [normalized] at exactWord
        exact congrArg Prod.fst exactWord
      obtain ⟨result, performed⟩ := PartialReplayHistory.subword_ready (meaning.laws key) active partition
      have endpoint : tableAt s owner key = some result := output_exact (some result) (by
        simp [normalized, input, PartialReplaySlots.interpret, PartialReplayHistory.keepMissing,
          operations_eq, performed])
      rw [endpoint]
      exact History.discharge active partition performed
    | true =>
      have ownerIsActor : owner = actor := by
        have restricts : Inverse.restrict owner key ∈ word :=
          (PartialReplaySlots.slotWord_erases_iff meaning.denote owner key word).mp (by rw [normalized])
        cases actorEntry : r actor with
        | none => simp [← selected, saved, actorEntry] at restricts
        | some fiber =>
          rw [← selected] at restricts
          exact PartialReplayRouting.restriction_owner r routed actor owner key fiber actorEntry
            (by simpa [saved, actorEntry] using restricts)
      have ready : List.Sublist operations (captures meaning.denote owner key word) := by
        simpa [normalized] using PartialReplaySlots.slotWord_captures meaning.denote owner key word
      obtain ⟨extra, selectedOperations⟩ := ready.exists_perm_append
      have readyPartition : (operations ++ (extra ++ (remaining pending actor).map Prod.snd)).Perm
          (pending.map Prod.snd) := by
        simpa only [List.append_assoc] using
          (selectedOperations.symm.append_right ((remaining pending actor).map Prod.snd)).trans partition
      obtain ⟨result, performed⟩ := PartialReplayHistory.subword_ready (meaning.laws key) active readyPartition
      have endpoint : tableAt s owner key = none := output_exact none (by
        simp [normalized, input, PartialReplaySlots.interpret, PartialReplayHistory.eraseAfter,
          PartialReplayHistory.keepMissing, performed])
      rw [endpoint]
      apply remaining_nil pending actor
      intro reader different
      rw [aligned reader, ownerIsActor]
      exact no_foreign_captures meaning r actor key routed free reader different

theorem slot_history_empty {program : Program} (meaning : Coeffects program) (owner : Name) (key : Key) :
    SlotHistory meaning (fun _ => none) owner key :=
  ⟨[], by intro actor; rfl, rfl⟩

/-- The slot history needs the actual landing or discharge summary and
the scoping of saved inverses at the source of the event. -/
theorem slot_history_step {program : Program} (meaning : Coeffects program)
    {state after : R} {actor owner : Name} {key : Key}
    (event : ReplayEvent program actor state after) (routed : PartialReplayRouting.ScopedAccumulators state)
    (earlier : SlotHistory meaning state owner key) : SlotHistory meaning after owner key := by
  cases event with
  | control tables stable =>
    obtain ⟨pending, aligned, lived⟩ := earlier
    refine ⟨pending, fun name => by rw [stable]; exact aligned name, ?_⟩
    rw [← tables owner key]
    exact lived
  | capture landed tables pushed _ => exact step_capture_history meaning landed tables pushed earlier
  | cleanup selected free tables cleared _ => exact step_cleanup_history meaning routed selected free tables cleared earlier

/-- The joint per-slot histories are derived from every ordinary run.
Only coeffect denotation, primitive recovery and key commutation are required. -/
theorem reachable_slot_history {program : Program} (meaning : Coeffects program)
    {state : R} (reached : WellFormed.Run program (fun _ => none) state)
    (owner : Name) (key : Key) : SlotHistory meaning state owner key := by
  induction reached with
  | refl => exact slot_history_empty meaning owner key
  | step reached step earlier =>
    obtain ⟨actor, event⟩ := event_of_calculus_step program step
    exact slot_history_step meaning event (PartialReplayRouting.reachable_scoped program reached) earlier

private theorem pair_partition (pending : List (Ticket Name Value)) (first second : Name)
    (different : first ≠ second) :
    ∃ rest, (ticketsFor pending first ++ ticketsFor pending second ++ rest).Perm (pending.map Prod.snd) := by
  have prior := ticket_partition pending first
  have later := ticket_partition (remaining pending first) second
  rw [ticketsFor_remaining pending first second, if_neg (Ne.symm different)] at later
  exact ⟨(remaining (remaining pending first) second).map Prod.snd,
    by simpa only [List.append_assoc] using (later.append_left (ticketsFor pending first)).trans prior⟩

private theorem retain_subwords (actualFirst actualSecond replayFirst replaySecond rest total : List (PartialMap Value))
    (first : List.Sublist replayFirst actualFirst) (second : List.Sublist replaySecond actualSecond)
    (source : (actualFirst ++ actualSecond ++ rest).Perm total) :
    ∃ residue, (replayFirst ++ replaySecond ++ residue).Perm total := by
  obtain ⟨firstRest, firstReordered⟩ := first.exists_perm_append
  obtain ⟨secondRest, secondReordered⟩ := second.exists_perm_append
  have normalized :=
    ((firstReordered.symm.append secondReordered.symm).append_right rest).trans source
  have middleSwap := (List.perm_append_comm (l₁ := replaySecond) (l₂ := firstRest)).append_right (secondRest ++ rest)
  have adjusted := (middleSwap.append_left replayFirst).trans
    (by simpa only [List.append_assoc] using normalized)
  exact ⟨firstRest ++ secondRest ++ rest,
    by simpa only [List.append_assoc] using adjusted⟩

private theorem compare_slot_words {observe : Setoid Value} {admitted : PartialMap Value → Prop}
    (laws : KeyLaws observe admitted) {input : Value}
    {pending first second rest : List (PartialMap Value)}
    (history : History admitted input pending)
    (selection : (first ++ second ++ rest).Perm pending) (firstErases secondErases : Bool) :
    ∃ left right : Option Value,
      compose (PartialReplaySlots.interpret (second, secondErases))
        (PartialReplaySlots.interpret (first, firstErases)) (some input) = some left ∧
      compose (PartialReplaySlots.interpret (first, firstErases))
        (PartialReplaySlots.interpret (second, secondErases)) (some input) = some right ∧
      OptionRel observe.r left right := by
  have reversed : (second ++ first ++ rest).Perm pending :=
    (List.perm_append_comm.append_right rest).trans selection
  cases firstErases <;> cases secondErases
  · obtain ⟨left, right, leftOrder, rightOrder, related⟩ := PartialReplayHistory.pending_commute laws history selection
    have lifted (earlier later : List (PartialMap Value)) :
        compose (keepMissing (run later)) (keepMissing (run earlier)) (some input) =
          (run (earlier ++ later) input).map some := by
      rw [PartialReplayHistory.run_append]
      simp only [compose, keepMissing]
      cases run earlier input <;> rfl
    exact ⟨some left, some right,
      by simp only [PartialReplaySlots.interpret, Bool.false_eq_true, if_false, lifted, leftOrder, Option.map_some],
      by simp only [PartialReplaySlots.interpret, Bool.false_eq_true, if_false, lifted, rightOrder, Option.map_some],
      related⟩
  · obtain ⟨firstThenSecond, secondThenFirst⟩ := PartialReplayHistory.erase_commutes_with_pending laws history reversed
    exact ⟨none, none, firstThenSecond, secondThenFirst, True.intro⟩
  · obtain ⟨secondThenFirst, firstThenSecond⟩ := PartialReplayHistory.erase_commutes_with_pending laws history selection
    exact ⟨none, none, firstThenSecond, secondThenFirst, True.intro⟩
  · obtain ⟨left, leftSuccess⟩ := PartialReplayHistory.subword_ready laws history
      (by simpa only [List.append_assoc] using selection)
    obtain ⟨right, rightSuccess⟩ := PartialReplayHistory.subword_ready laws history
      (by simpa only [List.append_assoc] using reversed)
    exact ⟨none, none,
      by simp [compose, PartialReplaySlots.interpret, eraseAfter, keepMissing, leftSuccess],
      by simp [compose, PartialReplaySlots.interpret, eraseAfter, keepMissing, rightSuccess], True.intro⟩

/-- The two actual saved words of distinct actors replay successfully in either
order at every registry slot. The resulting optional values agree up to the
key observation. This includes slots erased by the provider's word. -/
theorem saved_words_commute_of_history {program : Program} (meaning : Coeffects program)
    {state : R} (first second owner : Name) (different : first ≠ second) (key : Key)
    (history : SlotHistory meaning state owner key) :
    let replay := fun word => run (word.map (PartialReplaySlots.project meaning.denote owner key))
    ∃ left right : Option Value,
      replay (saved state first ++ saved state second) (tableAt state owner key) = some left ∧
      replay (saved state second ++ saved state first) (tableAt state owner key) = some right ∧
      OptionRel (meaning.observe key).r left right := by
  let firstWord := saved state first
  let secondWord := saved state second
  let normalize := PartialReplaySlots.slotWord meaning.denote owner key
  let replay := fun (word : List I) => run (word.map (PartialReplaySlots.project meaning.denote owner key))
  have composition (a b : List I) (input : Option Value) :
      replay (a ++ b) input =
        compose (PartialReplaySlots.interpret (normalize b)) (PartialReplaySlots.interpret (normalize a)) input := by
    have factor (word : List I) : replay word = PartialReplaySlots.interpret (normalize word) :=
      funext (PartialReplaySlots.slotWord_exact meaning.denote owner key word)
    have append : replay (a ++ b) input = (replay a input).bind (replay b) := by
      simp only [replay, List.map_append, PartialReplayHistory.run_append]
    rw [append, factor a, factor b]
    rfl
  change ∃ left right : Option Value,
    replay (firstWord ++ secondWord) (tableAt state owner key) = some left ∧
    replay (secondWord ++ firstWord) (tableAt state owner key) = some right ∧
    OptionRel (meaning.observe key).r left right
  obtain ⟨pending, aligned, lived⟩ := history
  rcases firstForm : normalize firstWord with ⟨earlier, firstErases⟩
  rcases secondForm : normalize secondWord with ⟨later, secondErases⟩
  rw [composition, composition, firstForm, secondForm]
  cases initial : tableAt state owner key with
  | none => cases firstErases <;> cases secondErases <;> exact ⟨none, none, rfl, rfl, True.intro⟩
  | some value =>
    have history : History (meaning.admitted key) value (pending.map Prod.snd) := by
      simpa only [initial] using lived
    obtain ⟨other, partition⟩ := pair_partition pending first second different
    rw [aligned first, aligned second] at partition
    have firstPrefix := PartialReplaySlots.slotWord_captures meaning.denote owner key firstWord
    have secondPrefix := PartialReplaySlots.slotWord_captures meaning.denote owner key secondWord
    change List.Sublist (normalize firstWord).1 _ at firstPrefix
    change List.Sublist (normalize secondWord).1 _ at secondPrefix
    rw [firstForm] at firstPrefix
    rw [secondForm] at secondPrefix
    obtain ⟨rest, selected⟩ := retain_subwords _ _ earlier later other _ firstPrefix secondPrefix partition
    exact compare_slot_words (meaning.laws key) history selected firstErases secondErases

theorem reachable_saved_words_commute {program : Program} (meaning : Coeffects program)
    {state : R} (reached : WellFormed.Run program (fun _ => none) state)
    (first second owner : Name) (different : first ≠ second) (key : Key) :
    let replay := fun word => run (word.map (PartialReplaySlots.project meaning.denote owner key))
    ∃ left right : Option Value,
      replay (saved state first ++ saved state second) (tableAt state owner key) = some left ∧
      replay (saved state second ++ saved state first) (tableAt state owner key) = some right ∧
      OptionRel (meaning.observe key).r left right :=
  saved_words_commute_of_history meaning first second owner different key
    (reachable_slot_history meaning reached owner key)

/-- The key-local partial forward selected by a successful landing. -/
def operationMap (call : Value → Except Error (Value × (Value → Value) × Value)) :
    PartialMap (Option Value) :=
  keepMissing (fun value => (call value).toOption.map Prod.fst)

/-- At the occupied slot of a foreign operation, its actual successful
forward application and an actor's accumulated word replay in both orders.
The history and successful landing are supplied at the source cut. -/
private theorem operate_commutes_of_history {program : Program} (meaning : Coeffects program)
    {state : R}
    (actor owner : Name) (key : Key) (history : SlotHistory meaning state owner key) {code : Code} {call}
    (operation : (program code).action = .operate key call)
    {input output outcome : Value} {inverse : Value → Value}
    (occupied : tableAt state owner key = some input)
    (performed : call input = .ok (output, inverse, outcome)) :
    let replay := run ((saved state actor).map (PartialReplaySlots.project meaning.denote owner key))
    ∃ left right : Option Value,
      compose replay (operationMap call) (some input) = some left ∧
      compose (operationMap call) replay (some input) = some right ∧
      OptionRel (meaning.observe key).r left right := by
  let word := saved state actor
  let replay := run (word.map (PartialReplaySlots.project meaning.denote owner key))
  have normalized : replay = PartialReplaySlots.interpret (PartialReplaySlots.slotWord meaning.denote owner key word) :=
    funext (PartialReplaySlots.slotWord_exact meaning.denote owner key word)
  change ∃ left right : Option Value, compose replay (operationMap call) (some input) = some left ∧
    compose (operationMap call) replay (some input) = some right ∧ OptionRel (meaning.observe key).r left right
  obtain ⟨pending, alignment, lived⟩ := history
  have history : History (meaning.admitted key) input (pending.map Prod.snd) := by
    simpa only [occupied] using lived
  have partition := ticket_partition pending actor
  rw [alignment actor] at partition
  rcases form : PartialReplaySlots.slotWord meaning.denote owner key word with ⟨operations, erases⟩
  have retained := PartialReplaySlots.slotWord_captures meaning.denote owner key word
  rw [form] at retained
  obtain ⟨skipped, subword⟩ := retained.exists_perm_append
  have selected : (operations ++ (skipped ++ (remaining pending actor).map Prod.snd)).Perm (pending.map Prod.snd) := by
    simpa only [List.append_assoc] using
      (subword.symm.append_right ((remaining pending actor).map Prod.snd)).trans partition
  obtain ⟨valid, recovered⟩ := meaning.captured code key call operation input output inverse outcome performed
  let localCall := asOperation meaning.denote key call
  have localRun : localCall.run input = some (output, meaning.denote key inverse, outcome) := by
    simp [localCall, asOperation, performed]
  have firstMap : (fun value => (localCall.run value).map Prod.fst) =
      (fun value => (call value).toOption.map Prod.fst) := by
    funext value
    cases called : call value <;> simp [localCall, asOperation, called, Except.toOption]
  rw [normalized, form]
  cases erases with
  | true =>
    have absorbed := PartialReplayHistory.erase_commutes_with_forward (meaning.laws key) history selected
      localCall outcome (meaning.denote key inverse) localRun valid recovered
    dsimp only at absorbed
    rw [firstMap] at absorbed
    exact ⟨none, none, absorbed.1, absorbed.2, True.intro⟩
  | false =>
    have forwardValid : meaning.admitted key (fun value => (localCall.run value).map Prod.fst) := by
      rw [firstMap]
      exact meaning.forward code key call operation
    have compared := PartialReplayHistory.forward_commutes_with_pending (meaning.laws key) history selected
      localCall outcome (meaning.denote key inverse) localRun valid recovered forwardValid
    dsimp only at compared
    rw [firstMap] at compared
    obtain ⟨left, right, leftOrder, rightOrder, observed⟩ := compared
    have lifted (first second : PartialMap Value) :
        compose (keepMissing second) (keepMissing first) (some input) =
          (compose second first input).map some := by
      simp only [compose, keepMissing]
      cases first input <;> rfl
    exact ⟨some left, some right,
      by simp only [PartialReplaySlots.interpret, Bool.false_eq_true, if_false, operationMap,
        lifted, leftOrder, Option.map_some],
      by simp only [PartialReplaySlots.interpret, Bool.false_eq_true, if_false, operationMap,
        lifted, rightOrder, Option.map_some], observed⟩

theorem reachable_operate_commutes {program : Program} (meaning : Coeffects program)
    {state : R} (reached : WellFormed.Run program (fun _ => none) state)
    (actor owner : Name) (key : Key) {code : Code} {call}
    (operation : (program code).action = .operate key call)
    {input output outcome : Value} {inverse : Value → Value}
    (occupied : tableAt state owner key = some input)
    (performed : call input = .ok (output, inverse, outcome)) :
    let replay := run ((saved state actor).map (PartialReplaySlots.project meaning.denote owner key))
    ∃ left right : Option Value,
      compose replay (operationMap call) (some input) = some left ∧
      compose (operationMap call) replay (some input) = some right ∧
      OptionRel (meaning.observe key).r left right :=
  operate_commutes_of_history meaning actor owner key (reachable_slot_history meaning reached owner key)
    operation occupied performed

/-- At an occupied slot, extract the actual pending inverse maps of one
actor and replay them on both sides of a successful operation. The orbit
membership and partial success both come from the reachable slot history. -/
theorem operation_through_captures_of_history {program : Program} (meaning : Coeffects program)
    {state : R}
    (actor owner : Name) (key : Key) {code : Code} {call}
    (history : SlotHistory meaning state owner key)
    (operation : (program code).action = .operate key call)
    {input output outcome : Value} {inverse : Value → Value}
    (occupied : tableAt state owner key = some input)
    (performed : call input = .ok (output, inverse, outcome)) :
    let word := captures meaning.denote owner key (saved state actor)
    ∃ adjusted reverted result,
      (∀ map ∈ word, meaning.admitted key map) ∧
      run word input = some adjusted ∧ run word output = some reverted ∧
      (call adjusted).toOption.map Prod.fst = some result ∧ (meaning.observe key).r reverted result := by
  let word := captures meaning.denote owner key (saved state actor)
  obtain ⟨pending, aligned, lived⟩ := history
  have history : History (meaning.admitted key) input (pending.map Prod.snd) := by
    simpa only [occupied] using lived
  have partition := ticket_partition pending actor
  rw [aligned actor] at partition
  change (word ++ (remaining pending actor).map Prod.snd).Perm (pending.map Prod.snd) at partition
  have laws := meaning.laws key
  have valid : ∀ map ∈ word, meaning.admitted key map := by
    intro map member
    exact (PartialReplayHistory.replay_ready laws history).1 map
      (partition.mem_iff.mp (List.mem_append_left _ member))
  obtain ⟨adjusted, before⟩ := PartialReplayHistory.subword_ready laws history partition
  obtain ⟨accepted, recovers⟩ := meaning.captured code key call operation input output inverse outcome performed
  let localCall := asOperation meaning.denote key call
  have original : localCall.run input = some (output, meaning.denote key inverse, outcome) := by
    simp [localCall, asOperation, performed]
  have forward : (fun value => (localCall.run value).map Prod.fst) =
      (fun value => (call value).toOption.map Prod.fst) := by
    funext value
    cases called : call value <;> simp [localCall, asOperation, called, Except.toOption]
  have forwardAllowed : meaning.admitted key (fun value => (localCall.run value).map Prod.fst) := by
    rw [forward]
    exact meaning.forward code key call operation
  obtain ⟨left, right, first, second, related⟩ :=
    PartialReplayHistory.forward_commutes_with_pending laws history partition localCall outcome
      (meaning.denote key inverse) original accepted recovers forwardAllowed
  simp only [compose, original, Option.map_some, Option.bind_some] at first
  simp only [compose, before, Option.bind_some] at second
  rw [congrFun forward adjusted] at second
  exact ⟨adjusted, left, right, valid, before, first, second, related⟩

theorem reachable_operation_through_captures {program : Program} (meaning : Coeffects program)
    {state : R} (reached : WellFormed.Run program (fun _ => none) state)
    (actor owner : Name) (key : Key) {code : Code} {call}
    (operation : (program code).action = .operate key call)
    {input output outcome : Value} {inverse : Value → Value}
    (occupied : tableAt state owner key = some input)
    (performed : call input = .ok (output, inverse, outcome)) :
    let word := captures meaning.denote owner key (saved state actor)
    ∃ adjusted reverted result,
      (∀ map ∈ word, meaning.admitted key map) ∧
      run word input = some adjusted ∧ run word output = some reverted ∧
      (call adjusted).toOption.map Prod.fst = some result ∧ (meaning.observe key).r reverted result :=
  operation_through_captures_of_history meaning actor owner key (reachable_slot_history meaning reached owner key)
    operation occupied performed

theorem saved_subword_defined_of_history {program : Program} (meaning : Coeffects program)
    {state : R} (actor owner : Name) (key : Key) (lived : SlotHistory meaning state owner key)
    {word : List I} (selectedWord : word.Sublist (saved state actor)) :
    ∃ output, run (word.map (PartialReplaySlots.project meaning.denote owner key))
      (tableAt state owner key) = some output := by
  rw [PartialReplaySlots.slotWord_exact]
  obtain ⟨pending, aligned, historyAtSlot⟩ := lived
  rcases form : PartialReplaySlots.slotWord meaning.denote owner key word with ⟨operations, erases⟩
  cases initial : tableAt state owner key with
  | none => cases erases <;> exact ⟨none, rfl⟩
  | some value =>
    have history : History (meaning.admitted key) value (pending.map Prod.snd) := by
      simpa only [initial] using historyAtSlot
    have partition := ticket_partition pending actor
    rw [aligned actor] at partition
    have opPrefix := PartialReplaySlots.slotWord_captures meaning.denote owner key word
    rw [form] at opPrefix
    have subset : List.Sublist (captures meaning.denote owner key word)
        (captures meaning.denote owner key (saved state actor)) := selectedWord.filterMap _
    obtain ⟨skipped, reordered⟩ := (opPrefix.trans subset).exists_perm_append
    have selected : (operations ++ (skipped ++ (remaining pending actor).map Prod.snd)).Perm (pending.map Prod.snd) := by
      simpa only [List.append_assoc] using
        (reordered.symm.append_right ((remaining pending actor).map Prod.snd)).trans partition
    obtain ⟨output, replayed⟩ := PartialReplayHistory.subword_ready (meaning.laws key) history selected
    cases erases with
    | false => exact ⟨some output, by simp [PartialReplaySlots.interpret, keepMissing, replayed]⟩
    | true => exact ⟨none, by simp [PartialReplaySlots.interpret, eraseAfter, keepMissing, replayed]⟩

private theorem saved_word_defined_of_history {program : Program} (meaning : Coeffects program)
    {state : R}
    (actor owner : Name) (key : Key) (history : SlotHistory meaning state owner key) :
    ∃ output, run ((saved state actor).map (PartialReplaySlots.project meaning.denote owner key))
      (tableAt state owner key) = some output :=
  saved_subword_defined_of_history meaning actor owner key history
    (List.Sublist.refl _)

theorem discharge_append (state : R) (first second : List I) :
    discharge Stages.undo (first ++ second) state = discharge Stages.undo second (discharge Stages.undo first state) := by
  induction first generalizing state with
  | nil => rfl
  | cons inverse rest earlier => exact earlier (Stages.undo inverse state)

private theorem operated_slot_exact (state : R) (owner : Name) (key : Key)
    (call : Value → Except Error (Value × (Value → Value) × Value)) (result : Option Value)
    (applied : operationMap call (tableAt state owner key) = some result) :
    tableAt (InterleavedRecovery.transform owner key (InterleavedRecovery.callbackMap call) state) owner key = result := by
  rw [InterleavedRecovery.tableAt_transform, if_pos ⟨rfl, rfl⟩]
  cases present : tableAt state owner key with
  | none => simpa [operationMap, keepMissing, present] using applied
  | some value =>
    cases called : call value with
    | error error => simp [operationMap, keepMissing, present, called, Except.toOption] at applied
    | ok answer =>
      simpa [operationMap, keepMissing, present, called, Except.toOption, InterleavedRecovery.callbackMap] using applied

/-- The counterfactual inverse and frozen state application evaluated at a
single registry slot. Both compositions have successful partial replays,
agree up to the key observation, and denote the stated ordinary endpoints. -/
def SlotSquare {program : Program} (meaning : Coeffects program)
    (word : List I) (effect : R → R) (state : R) (owner : Name) (key : Key)
    (forward : PartialMap (Option Value)) : Prop :=
  let inverse := run (word.map (PartialReplaySlots.project meaning.denote owner key))
  ∃ left right : Option Value,
    compose inverse forward (tableAt state owner key) = some left ∧
    compose forward inverse (tableAt state owner key) = some right ∧
    tableAt (discharge Stages.undo word (effect state)) owner key = left ∧
    tableAt (effect (discharge Stages.undo word state)) owner key = right ∧
    OptionRel (meaning.observe key).r left right

private def provisionMap (value : Value) : PartialMap (Option Value)
  | none => some (some value)
  | some _ => none

/-- The selected state application restricted to one slot. The operation
owner is resolved once in the actual source state and held fixed in replay. -/
def projectApplication {program : Program} (meaning : Coeffects program)
    (state : R) (other : Name) (use : RuleEvaluation.Use Name Key Value Code)
    (owner : Name) (key : Key) : PartialMap (Option Value) :=
  match use with
  | .identity => some
  | .accumulator word => run (word.map (PartialReplaySlots.project meaning.denote owner key))
  | .iteration code =>
    match (program code).action with
    | .unit | .instantiate _ => some
    | .provide provided value =>
      if owner = other ∧ key = provided then provisionMap value else some
    | .operate operated call =>
      if (location state other operated).map Prod.fst = some owner ∧ key = operated
      then operationMap call else some

/-- The partial projection of a frozen successful landing returns the
actual value at every slot. The landing supplies its route and domain. -/
theorem projectApplication_landing {program : Program} (meaning : Coeffects program)
    {actor : Name} {code : Code} {before after : R} {token : I} {next : Option Code}
    (land : Land program actor code before after token next) (owner : Name) (key : Key) :
    projectApplication meaning before actor (.iteration code) owner key (tableAt before owner key) =
      some (tableAt after owner key) := by
  cases land with
  | unit _ _ _ action => simp [projectApplication, action]
  | instantiate _ _ _ component child action insertable =>
    have tables := (RuleEvaluation.Edit.insert child component (some actor)).preserves_tables before
      insertable.1 owner key
    simpa [projectApplication, action, RuleEvaluation.Edit.apply] using congrArg some tables
  | provide _ _ _ row provided value action present _ vacant =>
    rw [tableAt_write _ _ _ _ _ _ (by simp [present])]
    by_cases selected : owner = actor ∧ key = provided
    · obtain ⟨rfl, rfl⟩ := selected
      simp [projectApplication, action, tableAt, present, vacant, provisionMap]
    · simp [projectApplication, action, selected]
  | operate _ _ _ operated call holder input output inverse reply action located called =>
    have binding := located_value located
    have live : before holder ≠ none := by
      intro absent
      simp [tableAt, absent] at binding
    rw [tableAt_write _ _ _ _ _ _ live]
    by_cases selected : owner = holder ∧ key = operated
    · obtain ⟨rfl, rfl⟩ := selected
      simp [projectApplication, action, located, binding, operationMap, keepMissing, called, Except.toOption]
    · have other : ¬ (holder = owner ∧ key = operated) :=
        fun identity => selected ⟨identity.1.symm, identity.2⟩
      simp [projectApplication, action, located, selected, other]

private theorem neutral_square {program : Program} (meaning : Coeffects program)
    {state : R} (actor owner : Name) (key : Key) (history : SlotHistory meaning state owner key)
    (revision : R → R) (current : tableAt (revision state) owner key = tableAt state owner key)
    (afterUndo : tableAt (revision (discharge Stages.undo (saved state actor) state)) owner key =
      tableAt (discharge Stages.undo (saved state actor) state) owner key) :
    SlotSquare meaning (saved state actor) revision state owner key some := by
  obtain ⟨value, success⟩ := saved_word_defined_of_history meaning actor owner key history
  have agrees : ∀ source : R, tableAt source owner key = tableAt state owner key →
      tableAt (discharge Stages.undo (saved state actor) source) owner key = value := by
    intro source same
    apply PartialReplaySlots.project_word meaning.denote meaning.agrees
    rw [same]
    exact success
  exact ⟨value, value, success, by simp only [compose, success, Option.bind_some],
    agrees (revision state) current, afterUndo.trans (agrees state rfl),
    PartialObservedMapClosure.option_refl (meaning.observe key) value⟩

private theorem operation_square {program : Program} (meaning : Coeffects program)
    {state : R} (actor owner : Name) (key : Key) (history : SlotHistory meaning state owner key)
    {code : Code} {call}
    (operation : (program code).action = .operate key call)
    {input output outcome : Value} {inverse : Value → Value}
    (occupied : tableAt state owner key = some input)
    (performed : call input = .ok (output, inverse, outcome)) :
    SlotSquare meaning (saved state actor)
      (InterleavedRecovery.transform owner key (InterleavedRecovery.callbackMap call))
      state owner key (operationMap call) := by
  obtain ⟨left, right, leftOrder, rightOrder, relation⟩ :=
    operate_commutes_of_history meaning actor owner key history operation occupied performed
  refine ⟨left, right, ?_, ?_, ?_, ?_, relation⟩
  · rw [occupied]
    exact leftOrder
  · rw [occupied]
    exact rightOrder
  · have applied : operationMap call (some input) = some (some output) := by
      simp [operationMap, keepMissing, performed, Except.toOption]
    have current := operated_slot_exact state owner key call (some output) (by rw [occupied]; exact applied)
    apply PartialReplaySlots.project_word meaning.denote meaning.agrees
    rw [current]
    simpa only [compose, applied, Option.bind_some] using leftOrder
  · obtain ⟨value, replayed⟩ := saved_word_defined_of_history meaning actor owner key history
    have initial := PartialReplaySlots.project_word meaning.denote meaning.agrees
      owner key _ state value replayed
    apply operated_slot_exact
    rw [initial]
    rw [occupied] at replayed
    simpa only [compose, replayed, Option.bind_some] using rightOrder

private theorem avoids_projection (denote : InverseMeaning Key Value) (owner : Name) (key : Key)
    (word : List I) (avoids : ∀ token ∈ word, InterleavedRecovery.Avoids owner key token) :
    run (word.map (PartialReplaySlots.project denote owner key)) = some := by
  induction word with
  | nil => rfl
  | cons token rest prior =>
    have current := avoids token List.mem_cons_self
    have atom : PartialReplaySlots.project denote owner key token = some := by
      cases token with
      | unit => rfl
      | retire => rfl
      | restrict src slot => exact if_neg (fun both => current ⟨both.1.symm, both.2.symm⟩)
      | operate src slot inverse => exact if_neg (fun both => current ⟨both.1.symm, both.2.symm⟩)
    funext input
    rw [List.map_cons, PartialReplayHistory.run_cons, atom, Option.bind_some]
    exact congrFun (prior (fun inv member => avoids inv (List.mem_cons_of_mem _ member))) input

/-- All ordinary applications admit the partial per-slot replay square
where the foreign provisions are disjoint from the episode actor's interface.
The two saved-word and foreign-operation cases have genuine partial domains;
success of the alternative replay order follows from the supplied slot histories. -/
theorem frozen_application_partial_square_of_history {program : Program} (meaning : Coeffects program)
    {rule : Labeled.Rule} {state middle : R}
    (history : ∀ owner key, SlotHistory meaning state owner key)
    (routing : TableFrame.ScopedAccumulators state)
    (actor other : Name) (fiber foreign : F)
    (present : state actor = some fiber) (foreignPresent : state other = some foreign)
    (different : other ≠ actor)
    (separate : ∀ key, foreign.component.provides key = true → fiber.component.requires key = false)
    {use : RuleEvaluation.Use Name Key Value Code} {revision : R → R}
    (frozen : EntangledApplications.FrozenApplication program other use state middle revision)
    (allowed : use.allowed rule state other) :
    ∀ owner key, SlotSquare meaning (saved state actor) revision state owner key
      (projectApplication meaning state other use owner key) := by
  intro holder key
  cases frozen with
  | identity => exact neutral_square meaning actor holder key (history holder key) id rfl rfl
  | accumulator word state =>
    obtain ⟨_, entry, view, found, phase⟩ := allowed
    have selected : saved state other = word := by simp [saved, found, phase, Phase.accumulator]
    obtain ⟨left, right, leftOrder, rightOrder, observed⟩ :=
      saved_words_commute_of_history meaning other actor holder different key (history holder key)
    rw [selected] at leftOrder rightOrder
    refine ⟨left, right,
      ?_, ?_, ?_, ?_, observed⟩
    · simpa only [compose, List.map_append, PartialReplayHistory.run_append] using leftOrder
    · simpa only [compose, List.map_append, PartialReplayHistory.run_append] using rightOrder
    · rw [← discharge_append]
      exact PartialReplaySlots.project_word meaning.denote meaning.agrees holder key _ state left leftOrder
    · rw [← discharge_append]
      exact PartialReplaySlots.project_word meaning.denote meaning.agrees holder key _ state right rightOrder
  | iteration landing =>
    cases landing with
    | unit action =>
      simpa only [projectApplication, action] using neutral_square meaning actor holder key (history holder key) id rfl rfl
    | instantiate component child action eligible =>
      let beforeUndo := discharge Stages.undo (saved state actor) state
      have childAbsent : beforeUndo child = none :=
        EntangledApplications.discharge_preserves_absence _ _ _ eligible.1
      have unchanged (r : R) (absent : r child = none) :
          tableAt (put r child (fresh component (some other))) holder key = tableAt r holder key :=
        ((RuleEvaluation.Edit.insert child component (some other)).preserves_tables r absent holder key).symm
      simpa only [projectApplication, action] using
        neutral_square meaning actor holder key (history holder key) _ (unchanged _ eligible.1) (unchanged beforeUndo childAbsent)
    | operate changed call owner before after inverse outcome action located performed =>
      by_cases selected : holder = owner ∧ key = changed
      · obtain ⟨rfl, rfl⟩ := selected
        simpa only [projectApplication, action, located, Option.map_some, Prod.fst, Option.some.injEq, and_self, if_true] using
          operation_square meaning actor holder key (history holder key) action (located_value located) performed
      · let map : R → R := InterleavedRecovery.transform owner changed (InterleavedRecovery.callbackMap call)
        have unchanged (r : R) : tableAt (map r) holder key = tableAt r holder key := by
          rw [InterleavedRecovery.tableAt_transform, if_neg selected]
        have notAtSlot : ¬ ((location state other changed).map Prod.fst = some holder ∧ key = changed) := by
          simpa only [located, Option.map_some, Prod.fst, Option.some.injEq, eq_comm] using selected
        simpa only [projectApplication, action, if_neg notAtSlot] using
          neutral_square meaning actor holder key (history holder key) map (unchanged _) (unchanged _)
    | provide entry provided value action found legal absent =>
      have sameEntry : entry = foreign := Option.some.inj (found.symm.trans foreignPresent)
      subst entry
      let beforeUndo := discharge Stages.undo (saved state actor) state
      obtain ⟨stillThere, retained, _⟩ := Ordering.discharge_existing_phases state (saved state actor)
        other foreign foreignPresent
      have sourcePresent : state other ≠ none := by simp [foreignPresent]
      have replayPresent : beforeUndo other ≠ none := by
        change beforeUndo other = some stillThere at retained
        simp [retained]
      by_cases selected : holder = other ∧ key = provided
      · obtain ⟨rfl, rfl⟩ := selected
        have avoids : ∀ inv ∈ saved state actor, InterleavedRecovery.Avoids holder key inv := by
          intro inv member
          refine EntangledApplications.scoped_avoids actor holder fiber.component.requires key different
            (separate key legal) inv ?_
          exact routing actor fiber present inv
            (by simpa [saved, present] using member)
        have replay := avoids_projection meaning.denote holder key (saved state actor) avoids
        have changed : tableAt (write state holder key (some value)) holder key = some value := by
          rw [tableAt_write _ _ _ _ _ _ sourcePresent, if_pos ⟨rfl, rfl⟩]
        have firstEndpoint : tableAt (discharge Stages.undo (saved state actor)
            (write state holder key (some value))) holder key = some value := by
          apply PartialReplaySlots.project_word meaning.denote meaning.agrees
          rw [changed, replay]
        have secondEndpoint : tableAt (write beforeUndo holder key (some value)) holder key = some value := by
          rw [tableAt_write _ _ _ _ _ _ replayPresent, if_pos ⟨rfl, rfl⟩]
        have before : tableAt state holder key = none := by simp [tableAt, foreignPresent, absent]
        simp only [projectApplication, action, eq_self, and_self, if_true]
        exact ⟨some value, some value,
          by simp only [compose, before, provisionMap, replay, Option.bind_some],
          by simp only [compose, before, provisionMap, replay, Option.bind_some], firstEndpoint, secondEndpoint,
          (meaning.observe key).refl value⟩
      · have unchanged (r : R) (live : r other ≠ none) :
            tableAt (write r other provided (some value)) holder key = tableAt r holder key := by
          rw [tableAt_write _ _ _ _ _ _ live, if_neg selected]
        simpa only [projectApplication, action, if_neg selected] using
          neutral_square meaning actor holder key (history holder key) _
            (unchanged state sourcePresent) (unchanged beforeUndo replayPresent)

theorem frozen_application_partial_square {program : Program} (meaning : Coeffects program)
    {rule : Labeled.Rule} {state middle : R} (reached : WellFormed.Run program (fun _ => none) state)
    (actor other : Name) (fiber foreign : F)
    (present : state actor = some fiber) (foreignPresent : state other = some foreign)
    (different : other ≠ actor)
    (separate : ∀ key, foreign.component.provides key = true → fiber.component.requires key = false)
    {use : RuleEvaluation.Use Name Key Value Code} {revision : R → R}
    (frozen : EntangledApplications.FrozenApplication program other use state middle revision)
    (allowed : use.allowed rule state other) :
    ∀ owner key, SlotSquare meaning (saved state actor) revision state owner key
      (projectApplication meaning state other use owner key) :=
  frozen_application_partial_square_of_history meaning (reachable_slot_history meaning reached)
    (TableFrame.reachable_scoped program reached) actor other fiber foreign present foreignPresent
    different separate frozen allowed

end Cordis.PartialReplayRegistry
