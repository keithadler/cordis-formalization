import Cordis.Repairs.Vestigial
import Cordis.Repairs.IncarnationReplay
import Cordis.PaperLifecycleClaims

/-! The indexed suffix of Lemmas 62 and 79. An omitted child is tracked by
the birth present at the cut. The transformed suffix uses original event
indices as stamps, with an explicit stutter at each omitted command. -/
namespace Cordis.Repairs.Vestigial
open Calculus Stages Incarnation IncarnationReplay
open PartialReplayRegistry (saved event_of_step)
open PaperLifecycleClaims (RootInsertions)
universe u
variable {Name Key Value Code Error : Type u} [DecidableEq Name] [DecidableEq Key]
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "C" => Capture Name Key Value
local notation "Program" => Code → Instruction Name Key Value Code Error

/-- Removing the row and retaining old saved words does not redirect a
retirement. The only retirement guard whose answer can change is at the
erased row itself, where either answer has the same projected effect. -/
theorem replay_erase (state : R) (name : Name) {live projected : Name → Option Nat}
    (other : ∀ child, child ≠ name → projected child = live child) (word : List C) :
    replay projected word (erase state name) = erase (replay live word state) name := by
  have step (state : R) (entry : C) :
      entry.apply projected (erase state name) = erase (entry.apply live state) name := by
    rcases entry with ⟨token, index⟩
    cases token with
    | unit => rfl
    | restrict owner key => exact undo_erase state name (.restrict owner key)
    | operate owner key callback => exact undo_erase state name (.operate owner key callback)
    | retire child =>
      by_cases same : child = name
      · subst child
        have noWrite : retire (erase state name) name = erase state name := by
          funext query
          by_cases matchName : query = name <;> simp [erase, retire, Calculus.modify, matchName]
        have projectedWrite : erase (retire state name) name = erase state name :=
          (modify_erase state name name _).symm.trans noWrite
        by_cases isLive : live name = some index <;>
          simp [Capture.apply, noWrite, projectedWrite, isLive]
      · by_cases isLive : live child = some index
        · simpa only [Capture.apply, other child same, if_pos isLive] using
            undo_erase state name (.retire child)
        · simp [Capture.apply, other child same, isLive]
  induction word generalizing state with
  | nil => rfl
  | cons capture rest ih => rw [replay, replay, step, ih]

variable {program : Code → Instruction Name Key Value Code Error} {last : Nat}
local notation "Trace" => Indexed.Trace program (fun _ => none : R) last

/-- The original incarnation is omitted between the cut and its own
removal. The definition uses the birth, so later reuse cannot restart it. -/
def withdrawnAt (trace : Trace) (name : Name) (cut time : Nat) : Prop :=
  cut ≤ time ∧ birthAt trace.state name time = birthAt trace.state name cut

instance (trace : Trace) (name : Name) (cut time : Nat) : Decidable (withdrawnAt trace name cut time) :=
  inferInstanceAs (Decidable (_ ∧ _ = _))

def projectedState (trace : Trace) (name : Name) (cut time : Nat) : R :=
  if withdrawnAt trace name cut time then erase (trace.state time) name else trace.state time

omit [DecidableEq Name] [DecidableEq Key] in
omit [DecidableEq Name] [DecidableEq Key] in
private theorem birth_exists {state : Nat → R} {name : Name} {time : Nat}
    (present : state time name ≠ none) : ∃ birth, birthAt state name time = some birth := by
  cases found : birthAt state name time with
  | none => exact False.elim (present (birthAt_none.mp found))
  | some birth => exact ⟨birth, rfl⟩

private theorem withdrawn_previous (trace : Trace) {name : Name} {cut time : Nat}
    (ready : Removable (trace.state cut) name) (later : cut ≤ time)
    (next : withdrawnAt trace name cut (time + 1)) :
    withdrawnAt trace name cut time := by
  have present : trace.state cut name ≠ none := fun missing =>
    Transposition.removable_present _ _ ready missing
  obtain ⟨birth, born⟩ := birth_exists present
  have current : birthAt trace.state name (time + 1) = some birth := next.2.trans born
  have bound := (resident_of_birthAt born).ordered
  have earlier := (resident_of_birthAt current).prefix time (by omega) (by omega)
  exact ⟨later, birthAt_eq_some.mpr earlier |>.trans born.symm⟩

/-- Every original row still masked by the withdrawal remains a vestige.
This is derived from the native steps since the cut. -/
theorem withdrawn_removable (trace : Trace) (roots : RootInsertions trace)
    {name : Name} {cut time : Nat} (ready : Removable (trace.state cut) name)
    (bounded : time ≤ last) (withdrawn : withdrawnAt trace name cut time) :
    Removable (trace.state time) name := by
  induction time with
  | zero =>
    have hc : cut = 0 := by have := withdrawn.1; omega
    simpa [hc] using ready
  | succ time ih =>
    by_cases same : cut = time + 1
    · simpa [same] using ready
    have earlier : cut ≤ time := by have := withdrawn.1; omega
    have previous := ih (by omega) (withdrawn_previous trace ready earlier withdrawn)
    have step := trace.step time (by omega)
    by_cases own : trace.actor time = name
    · rw [own] at step
      rcases steps_at_vestige previous step with ⟨_, unchanged⟩ | ⟨_, removed⟩
      · exact unchanged ▸ previous
      · exfalso
        have missing : trace.state (time + 1) name = none := by simp [removed, erase]
        have absent := birthAt_none.mpr missing
        have initially : birthAt trace.state name cut = none := withdrawn.2.symm.trans absent
        exact Transposition.removable_present _ _ ready (birthAt_none.mp initially)
    · exact (labeled_erase step own previous (roots time (by omega))).1

/-- A source step either survives with the same label and actor, or is a
Retire/Remove on the withdrawn child and its projection stutters. The
indices here refer to the original trace. -/
theorem projected_step (trace : Trace) (roots : RootInsertions trace)
    {name : Name} {cut time : Nat} (ready : Removable (trace.state cut) name)
    (afterCut : cut ≤ time) (bounded : time < last) :
    if withdrawnAt trace name cut time ∧ trace.actor time = name then
      (trace.rule time = .retire ∨ trace.rule time = .remove) ∧
        projectedState trace name cut (time + 1) = projectedState trace name cut time
    else
      Labeled.Step program (trace.rule time) (trace.actor time)
        (projectedState trace name cut time) (projectedState trace name cut (time + 1)) := by
  have step := trace.step time bounded
  by_cases withdrawn : withdrawnAt trace name cut time
  · have before := withdrawn_removable trace roots ready (by omega) withdrawn
    by_cases own : trace.actor time = name
    · rw [own] at step
      simp only [if_pos (And.intro withdrawn own), projectedState, if_pos withdrawn]
      rcases steps_at_vestige before step with ⟨retired, unchanged⟩ | ⟨removed, erased⟩
      · have present : trace.state time name ≠ none := fun missing =>
          Transposition.removable_present _ _ before missing
        have atNext : withdrawnAt trace name cut (time + 1) :=
          ⟨by omega, (birth_stays trace.state name time present (by simpa [unchanged] using present)).trans
            withdrawn.2⟩
        exact ⟨.inl retired, by rw [if_pos atNext, unchanged]⟩
      · have atNext : ¬ withdrawnAt trace name cut (time + 1) := by
          intro mask
          have missing : trace.state (time + 1) name = none := by simp [erased, erase]
          have initial : birthAt trace.state name cut = none := mask.2.symm.trans (birthAt_none.mpr missing)
          exact Transposition.removable_present _ _ ready (birthAt_none.mp initial)
        exact ⟨.inr removed, by rw [if_neg atNext, erased]⟩
    · have notDropped : ¬ (withdrawnAt trace name cut time ∧ trace.actor time = name) :=
        fun drops => own drops.2
      obtain ⟨after, replayed⟩ := labeled_erase step own before (roots time bounded)
      have beforeHere : trace.state time name ≠ none := fun missing =>
        Transposition.removable_present _ _ before missing
      have afterHere : trace.state (time + 1) name ≠ none := fun missing =>
        Transposition.removable_present _ _ after missing
      have atNext : withdrawnAt trace name cut (time + 1) :=
        ⟨by omega, (birth_stays trace.state name time beforeHere afterHere).trans withdrawn.2⟩
      simpa only [if_neg notDropped, projectedState, if_pos withdrawn, if_pos atNext] using replayed
  · have atNext : ¬ withdrawnAt trace name cut (time + 1) := fun next =>
      withdrawn (withdrawn_previous trace ready afterCut next)
    have notDropped : ¬ (withdrawnAt trace name cut time ∧ trace.actor time = name) :=
      fun drops => withdrawn drops.1
    simpa only [if_neg notDropped, projectedState, if_neg withdrawn, if_neg atNext] using step

private theorem projected_row {trace : Trace} {name query : Name} {cut time : Nat}
    (kept : query ≠ name ∨ ¬ withdrawnAt trace name cut time) :
    projectedState trace name cut time query = trace.state time query := by
  rcases kept with other | notWithdrawn
  · by_cases withdrawn : withdrawnAt trace name cut time <;>
      simp [projectedState, withdrawn, erase, other]
  · simp [projectedState, notWithdrawn]

private theorem projected_absent {trace : Trace} {name query : Name} {cut time : Nat}
    (absent : trace.state time query = none) : projectedState trace name cut time query = none := by
  by_cases withdrawn : withdrawnAt trace name cut time
  · by_cases same : query = name <;> simp [projectedState, withdrawn, erase, same, absent]
  · simp [projectedState, withdrawn, absent]

/-- Every retained incarnation keeps its original birth stamp. The proof
uses the entire actual residency interval, including the absence at birth. -/
theorem projected_birth (trace : Trace) (name query : Name) (cut time : Nat) :
    birthAt (projectedState trace name cut) query time =
      if query = name ∧ withdrawnAt trace name cut time then none else birthAt trace.state query time := by
  by_cases omitted : query = name ∧ withdrawnAt trace name cut time
  · obtain ⟨rfl, withdrawn⟩ := omitted
    rw [if_pos ⟨rfl, withdrawn⟩]
    exact birthAt_none.mpr (by simp [projectedState, withdrawn, erase])
  rw [if_neg omitted]
  cases born : birthAt trace.state query time with
  | none => exact birthAt_none.mpr (projected_absent (birthAt_none.mp born))
  | some birth =>
    have interval := resident_of_birthAt born
    apply birthAt_eq_some.mpr
    refine ⟨interval.ordered, ?_, ?_⟩
    · intro index lower upper absent
      have kept : query ≠ name ∨ ¬ withdrawnAt trace name cut index := by
        by_cases same : query = name
        · subst query
          right
          intro withdrawn
          have previous := birthAt_eq_some.mpr (interval.prefix index lower upper)
          exact omitted ⟨rfl, Nat.le_trans withdrawn.1 upper,
            born.trans (previous.symm.trans withdrawn.2)⟩
        · exact .inl same
      exact interval.present index lower upper ((projected_row kept).symm.trans absent)
    · rcases interval.boundary with zero | absent
      · exact .inl zero
      · exact .inr (projected_absent absent)

private theorem saved_projected (trace : Trace) (roots : RootInsertions trace)
    {name : Name} {cut time : Nat} (ready : Removable (trace.state cut) name)
    (bounded : time ≤ last) : saved (projectedState trace name cut time) = saved (trace.state time) := by
  funext actor
  by_cases same : actor = name
  · subst actor
    by_cases withdrawn : withdrawnAt trace name cut time
    · have leaf := withdrawn_removable trace roots ready bounded withdrawn
      cases found : trace.state time name with
      | none => simp [Removable, found] at leaf
      | some row =>
        simp only [Removable, found] at leaf
        simp [saved, projectedState, withdrawn, erase, found, leaf.2.1, Phase.accumulator]
    · unfold saved
      rw [projected_row (.inr withdrawn)]
  · unfold saved
    rw [projected_row (.inl same)]

/-- Recording the actual retained steps at their original indices leaves
every saved word unchanged. The omitted name has no saved word while
masked, and a dropped command makes no push. -/
theorem projected_track (trace : Trace) (roots : RootInsertions trace)
    {name : Name} {cut : Nat} (ready : Removable (trace.state cut) name)
    (time : Nat) (bounded : time ≤ last) :
    track (projectedState trace name cut) trace.actor time = track trace.state trace.actor time := by
  induction time with
  | zero => rfl
  | succ time ih =>
    unfold track
    rw [ih (by omega)]
    unfold advance
    rw [saved_projected trace roots ready bounded, saved_projected trace roots ready (by omega)]

/-- An original saved word gives exactly the projected incarnation-safe
replay at a corresponding cut. Captured words can still refer to the
omitted name. They cannot affect any later reissue under that name. -/
theorem projected_replayAt (trace : Trace) (roots : RootInsertions trace)
    {name : Name} {cut : Nat} (ready : Removable (trace.state cut) name)
    (time : Nat) (bounded : time ≤ last) (actor : Name) :
    let states := projectedState trace name cut
    let result := replayAt trace.state time (track trace.state trace.actor time actor)
    replayAt states time (track states trace.actor time actor) =
      if withdrawnAt trace name cut time then erase result name else result := by
  dsimp only
  rw [projected_track trace roots ready time bounded]
  unfold replayAt
  by_cases withdrawn : withdrawnAt trace name cut time
  · rw [if_pos withdrawn]
    have current : projectedState trace name cut time = erase (trace.state time) name :=
      if_pos withdrawn
    rw [current]
    apply replay_erase
    intro child other
    rw [projected_birth, if_neg (fun omitted => other omitted.1)]
  · rw [if_neg withdrawn]
    have current : projectedState trace name cut time = trace.state time := if_neg withdrawn
    rw [current]
    have equal : (fun child => birthAt (projectedState trace name cut) child time) =
        (fun child => birthAt trace.state child time) := by
      funext child
      rw [projected_birth, if_neg (fun omitted => withdrawn omitted.2)]
    rw [equal]

/-- The omitted child cannot be a root later in the same incarnation. -/
theorem withdrawn_child (trace : Trace) {name : Name} {cut time : Nat}
    (ready : Removable (trace.state cut) name) (child : LegalHistory.rootAt (trace.state cut) name = false)
    (bounded : time ≤ last) (withdrawn : withdrawnAt trace name cut time) :
    LegalHistory.rootAt (trace.state time) name = false := by
  have present : trace.state cut name ≠ none := fun missing =>
    Transposition.removable_present _ _ ready missing
  obtain ⟨birth, born⟩ := birth_exists present
  have cutLife := resident_of_birthAt born
  have currentLife := resident_of_birthAt (withdrawn.2.trans born)
  cases first : trace.state birth name with
  | none => exact False.elim (cutLife.present birth (Nat.le_refl _) cutLife.ordered first)
  | some original =>
    cases atCut : trace.state cut name with
    | none => exact False.elim (present atCut)
    | some old =>
      cases current : trace.state time name with
      | none => exact False.elim (currentLife.present time currentLife.ordered (Nat.le_refl _) current)
      | some row =>
        have oldParent := (cutLife.metadata trace (Nat.le_trans withdrawn.1 bounded) first atCut).2
        have currentParent := (currentLife.metadata trace bounded first current).2
        simpa [LegalHistory.rootAt, current, ← currentParent, oldParent] using
          (show old.parent.isNone = false by simpa [LegalHistory.rootAt, atCut] using child)

theorem projected_rootAt (trace : Trace) {name : Name} {cut time : Nat}
    (ready : Removable (trace.state cut) name) (child : LegalHistory.rootAt (trace.state cut) name = false)
    (bounded : time ≤ last) (actor : Name) :
    LegalHistory.rootAt (projectedState trace name cut time) actor =
      LegalHistory.rootAt (trace.state time) actor := by
  by_cases omitted : actor = name ∧ withdrawnAt trace name cut time
  · obtain ⟨rfl, withdrawn⟩ := omitted
    rw [withdrawn_child trace ready child bounded withdrawn]
    simp [LegalHistory.rootAt, projectedState, withdrawn, erase]
  · have kept : actor ≠ name ∨ ¬ withdrawnAt trace name cut time := by
      by_cases same : actor = name
      · exact .inr (fun mask => omitted ⟨same, mask⟩)
      · exact .inl same
    unfold LegalHistory.rootAt
    rw [projected_row kept]

theorem dropped_child_command (trace : Trace)
    {name : Name} {cut time : Nat} (ready : Removable (trace.state cut) name)
    (child : LegalHistory.rootAt (trace.state cut) name = false)
    (bounded : time < last) (withdrawn : withdrawnAt trace name cut time)
    (own : trace.actor time = name) (roots : RootInsertions trace) :
    (trace.rule time = .retire ∨ trace.rule time = .remove) ∧
      LegalHistory.rootAt (trace.state time) (trace.actor time) = false := by
  have event := projected_step trace roots ready withdrawn.1 bounded
  rw [if_pos ⟨withdrawn, own⟩] at event
  exact ⟨event.1, own ▸ withdrawn_child trace ready child (by omega) withdrawn⟩

def retainedFrom (trace : Trace) (name : Name) (cut start length : Nat) : List Nat :=
  (List.range' start length).filter fun time =>
    decide (¬ (withdrawnAt trace name cut time ∧ trace.actor time = name))

abbrev CutNotes (Name Key Value : Type u) := (Name → Option Nat) × (Name → List (Capture Name Key Value))
local notation "Notes" => CutNotes Name Key Value

def cutNotes (states : Nat → R) (actors : Nat → Name) (time : Nat) : Notes :=
  (fun name => birthAt states name time, track states actors time)

def noteStep (before after : R) (actor : Name) (stamp : Nat) (notes : Notes) : Notes :=
  (fun name => (after name).map (fun _ => (notes.1 name).getD stamp),
    advance before after actor stamp notes.2)

/-- Record a native suffix from a supplied cut. The list gives the retained
source events in dense execution order. Each step takes its source stamp
and obtains births and captures from its own actual endpoints. -/
def recordSuffix (states : Nat → R) (actors : Nat → Name) :
    Nat → List Nat → Notes → Notes
  | _, [], notes => notes
  | index, old :: rest, notes =>
    recordSuffix states actors (index + 1) rest
      (noteStep (states index) (states (index + 1)) (actors index) (old + 1) notes)

/-- Recording a legal step projects to the actual new raw word. The proof
is independent of the numerical stamp assigned to that step. -/
theorem noteStep_projects {before after : R} {rule : Labeled.Rule} {actor : Name}
    (step : Labeled.Step program rule actor before after) (stamp : Nat) (notes : Notes)
    (projects : ∀ name, (notes.2 name).map Capture.token = saved before name) :
    ∀ name, ((noteStep before after actor stamp notes).2 name).map Capture.token = saved after name := by
  intro name
  change (advance before after actor stamp notes.2 name).map Capture.token = saved after name
  cases event_of_step program step with
  | control _ stable => rw [advance_control _ _ _ projects stable, stable, projects name]
  | capture _ _ pushed _ =>
    rw [advance_capture _ _ _ _ pushed, pushed]
    by_cases acts : name = actor <;> simp [acts, projects]
  | cleanup _ _ _ cleared _ =>
    rw [advance, cleared]
    by_cases acts : name = actor <;> simp [acts, projects name]

/-- The recorded stack comes from the actual indexed replay endpoint,
including when source indices were compressed. -/
theorem recordSuffix_projects {initial : R} {length : Nat}
    (trace : Indexed.Trace program initial length) (index : Nat) (events : List Nat)
    (bounded : index + events.length ≤ length) (notes : Notes)
    (projects : ∀ name, (notes.2 name).map Capture.token = saved (trace.state index) name) :
    ∀ name, ((recordSuffix trace.state trace.actor index events notes).2 name).map Capture.token =
      saved (trace.state (index + events.length)) name := by
  induction events generalizing index notes with
  | nil => exact projects
  | cons old rest ih =>
    have step := trace.step index (by simp only [List.length_cons] at bounded; omega)
    have advanced := noteStep_projects step (old + 1) notes projects
    have endpoint := ih (index + 1) (by simp only [List.length_cons] at bounded; omega) _ advanced
    simpa only [recordSuffix, List.length_cons, Nat.add_assoc, Nat.add_comm 1] using endpoint

omit [DecidableEq Key] in
theorem record_shift (states : Nat → R) (actors : Nat → Name) (index : Nat)
    (events : List Nat) (notes : Notes) :
    recordSuffix states actors (index + 1) events notes =
      recordSuffix (fun i => states (i + 1)) (fun i => actors (i + 1)) index events notes := by
  induction events generalizing index notes with
  | nil => rfl
  | cons old rest ih => simpa only [recordSuffix] using ih (index + 1) _

private theorem stutter_notes (trace : Trace) (roots : RootInsertions trace)
    {name : Name} {cut time : Nat} (ready : Removable (trace.state cut) name)
    (bounded : time < last)
    (unchanged : projectedState trace name cut (time + 1) = projectedState trace name cut time) :
    cutNotes (projectedState trace name cut) trace.actor (time + 1) =
      cutNotes (projectedState trace name cut) trace.actor time := by
  apply Prod.ext
  · funext query
    change birthAt (projectedState trace name cut) query (time + 1) =
      birthAt (projectedState trace name cut) query time
    by_cases absent : projectedState trace name cut time query = none
    · exact (birthAt_none.mpr (by rwa [unchanged])).trans (birthAt_none.mpr absent).symm
    · exact birth_stays _ query time absent (by rwa [unchanged])
  · change advance _ _ _ _ _ = _
    apply advance_control
    · rw [projected_track trace roots ready time (by omega), saved_projected trace roots ready (by omega)]
      exact (tracked_stack trace time (by omega)).projects
    · rw [unchanged]

def prepend {before middle : R} {length : Nat} {rule : Labeled.Rule} {actor : Name}
    (first : Labeled.Step program rule actor before middle)
    (rest : Indexed.Trace program middle length) :
    Indexed.Trace program before (length + 1) where
  state
    | 0 => before
    | i + 1 => rest.state i
  rule
    | 0 => rule
    | i + 1 => rest.rule i
  actor
    | 0 => actor
    | i + 1 => rest.actor i
  start := rfl
  step time valid := by
    cases time with
    | zero =>
      change Labeled.Step program rule actor before (rest.state 0)
      rw [rest.start]
      exact first
    | succ time => exact rest.step time (by omega)

/-- Compress the stutters to a native indexed suffix. The two endpoints
of each retained step are the projected cuts of that very source event. -/
theorem compress_suffix (trace : Trace) (roots : RootInsertions trace)
    {name : Name} {cut : Nat} (ready : Removable (trace.state cut) name)
    (start length : Nat) (afterCut : cut ≤ start) (bounded : start + length ≤ last) :
    let kept := retainedFrom trace name cut start length
    ∃ moved : Indexed.Trace program (projectedState trace name cut start) kept.length,
      moved.state kept.length = projectedState trace name cut (start + length) ∧
      (∀ index (valid : index < kept.length),
        let old := kept[index]
        moved.rule index = trace.rule old ∧ moved.actor index = trace.actor old ∧
          moved.state index = projectedState trace name cut old ∧
          moved.state (index + 1) = projectedState trace name cut (old + 1)) ∧
      recordSuffix moved.state moved.actor 0 kept (cutNotes (projectedState trace name cut) trace.actor start) =
        cutNotes (projectedState trace name cut) trace.actor (start + length) := by
  dsimp only
  induction length generalizing start with
  | zero =>
    exact ⟨⟨fun _ => projectedState trace name cut start, trace.rule, trace.actor, rfl,
      fun time valid => False.elim (Nat.not_lt_zero time valid)⟩, rfl,
      (fun time valid => False.elim (Nat.not_lt_zero time valid)), rfl⟩
  | succ length ih =>
    have event := projected_step trace roots ready afterCut (by omega)
    obtain ⟨rest, endpoint, events, notes⟩ := ih (start + 1) (by omega) (by omega)
    have endIndex : start + 1 + length = start + (length + 1) := by omega
    rw [endIndex] at endpoint
    by_cases drops : withdrawnAt trace name cut start ∧ trace.actor start = name
    · rw [if_pos drops] at event
      have retained : retainedFrom trace name cut start (length + 1) =
          retainedFrom trace name cut (start + 1) length := by
        unfold retainedFrom
        rw [List.range'_succ, List.filter_cons_of_neg (fun kept =>
          (of_decide_eq_true kept) drops)]
      rw [retained]
      rw [← event.2]
      refine ⟨rest, endpoint, events, ?_⟩
      rw [← stutter_notes trace roots ready (by omega) event.2]
      simpa only [endIndex] using notes
    · rw [if_neg drops] at event
      have retained : retainedFrom trace name cut start (length + 1) =
          start :: retainedFrom trace name cut (start + 1) length := by
        unfold retainedFrom
        rw [List.range'_succ, List.filter_cons_of_pos
          (p := fun time => decide (¬ (withdrawnAt trace name cut time ∧ trace.actor time = name)))
          (decide_eq_true drops)]
      rw [retained]
      refine ⟨prepend event rest, endpoint, ?_, ?_⟩
      · intro index valid
        cases index with
        | zero => exact ⟨rfl, rfl, rfl, rest.start⟩
        | succ index =>
          rw [List.length_cons] at valid
          exact events index (by omega)
      · rw [recordSuffix, record_shift]
        change recordSuffix rest.state rest.actor 0 (retainedFrom trace name cut (start + 1) length)
          (noteStep (projectedState trace name cut start) (rest.state 0) (trace.actor start) (start + 1)
            (cutNotes (projectedState trace name cut) trace.actor start)) = _
        rw [rest.start]
        simpa only [endIndex] using notes

end Cordis.Repairs.Vestigial
