import Cordis.Repairs.GuardedCutState
import Cordis.Repairs.ReplayBindingDomains
import Cordis.ObservationLifting

/-! Saved retirements are paired by their capture events. They need only
agree with the current permutation when the captured child still lives. -/
namespace Cordis.Repairs.GuardedBirthReplay
open Calculus Stages GuardedHistory IncarnationReplay GuardedBirthMatching
open ObservationLifting (ListRelated)
open GuardedCutState

universe u
variable {Name Key Value Code Error : Type u} [DecidableEq Name] [DecidableEq Key]
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "C" => Capture Name Key Value
local notation "P" => Renaming.Permutation Name

private theorem project_undo (state : R) (token : Inverse Name Key Value) :
    project (Stages.undo token state) = Stages.undo token (project state) := by
  cases token with
  | unit => rfl
  | restrict => exact project_modify _ _ _ (fun _ => rfl)
  | operate => exact project_modify _ _ _ (fun _ => rfl)
  | retire => exact project_modify _ _ _ (fun _ => rfl)

private theorem project_apply (live : Name → Option Nat) (capture : C) (state : R) :
    project (capture.apply live state) = capture.apply live (project state) := by
  rcases capture with ⟨token, index⟩
  cases token with
  | unit => rfl
  | restrict owner key => exact project_undo state (.restrict owner key)
  | operate owner key inverse => exact project_undo state (.operate owner key inverse)
  | retire child =>
    by_cases current : live child = some index
    · simpa only [Capture.apply, if_pos current] using project_undo state (.retire child)
    · simp only [Capture.apply, if_neg current]

theorem project_replay (live : Name → Option Nat) (word : List C) (state : R) :
    project (replay live word state) = replay live word (project state) := by
  induction word generalizing state with
  | nil => rfl
  | cons capture rest ih => simp only [replay, ih, project_apply]

variable [Setoid Value]

/-- Ordinary actions are in the current namespace. Saved child retirements
can still carry the original raw names from their respective birth events. -/
inductive CapturePair (p : P) (stamp : Nat → Nat) : C → C → Prop
  | unit (birth) : CapturePair p stamp ⟨.unit, birth⟩ ⟨.unit, stamp birth⟩
  | restrict (owner key birth) :
      CapturePair p stamp ⟨.restrict owner key, birth⟩ ⟨.restrict (p.toFun owner) key, stamp birth⟩
  | operate (owner key birth) {f g : Value → Value} (related : Effects.Related f g) :
      CapturePair p stamp ⟨.operate owner key f, birth⟩ ⟨.operate (p.toFun owner) key g, stamp birth⟩
  | retire (child otherChild birth) :
      CapturePair p stamp ⟨.retire child, birth⟩ ⟨.retire otherChild, stamp birth⟩

variable {program otherProgram : Code → Instruction Name Key Value Code Error} {last otherLast : Nat}

def SavedMatch (left : Trace program last) (right : Trace otherProgram otherLast) (i j : Nat)
    (p : P) (stamp : Nat → Nat) : Prop :=
  ∀ name, ListRelated (CapturePair p stamp) ((left.notes i).2 name) ((right.notes j).2 (p.toFun name))

omit [DecidableEq Name] [DecidableEq Key] in
theorem CapturePair.of_inverse (p : P) (stamp : Nat → Nat) (index : Nat) (token : Inverse Name Key Value)
    (respect : ∀ owner key inverse, token = .operate owner key inverse → Effects.Related inverse inverse) :
    CapturePair p stamp ⟨token, index⟩ ⟨Renaming.inverse p token, stamp index⟩ := by
  cases token with
  | unit => exact .unit _
  | restrict owner key => exact .restrict owner key _
  | operate owner key inverse => exact .operate owner key _ (respect owner key inverse rfl)
  | retire child => exact .retire child (p.toFun child) _

omit [Setoid Value] in
private theorem word_empty (trace : Trace program last) {time : Nat} (bound : time ≤ last) (name : Name)
    (absent : trace.state time name = none) : (trace.notes time).2 name = [] := by
  apply (List.map_eq_nil_iff (f := Capture.token)).mp
  rw [trace.projects time bound name]
  simp [PartialReplayRegistry.saved, absent]

omit [Setoid Value] in
private theorem ordinary_owner (trace : Trace program last) {time : Nat} (bound : time ≤ last)
    {actor : Name} {capture : C} (recorded : capture ∈ (trace.notes time).2 actor) :
    match capture.token with
    | .restrict owner _ | .operate owner _ _ => trace.state time owner ≠ none
    | _ => True := by
  have saved : capture.token ∈ PartialReplayRegistry.saved (trace.state time) actor := by
    rw [← trace.projects time bound actor]
    exact List.mem_map.mpr ⟨capture, recorded, rfl⟩
  cases found : trace.state time actor with
  | none => simp [PartialReplayRegistry.saved, found] at saved
  | some row =>
    have member : capture.token ∈ row.phase.accumulator := by
      simpa [PartialReplayRegistry.saved, found] using saved
    have routing := (trace.invariants time bound).2 actor row found _ member
    cases kind : capture.token with
    | unit | retire => trivial
    | restrict owner key =>
      have same : owner = actor := by simpa [kind, PartialReplayRouting.Scoped] using routing
      subst owner
      simp [found]
    | operate owner key inverse =>
      rw [kind] at routing
      rcases routing with rfl | ⟨view, chosen, needed, route⟩
      · simp [found]
      obtain ⟨_, provider, present, _, _⟩ :=
        trace.supported time bound actor owner key ⟨row, view, found, needed, chosen, route⟩
      simp [present]

/-- Updating the match on vacant names preserves every old actual saved
pair. Ordinary inverse owners are live by routing and support. Retirements
keep their historical stamps and can retain the old raw names. -/
theorem SavedMatch.rematch {left : Trace program last} {right : Trace otherProgram otherLast}
    {i j : Nat} (hi : i ≤ last) (hj : j ≤ otherLast) {p q : P} {stamp : Nat → Nat}
    (old : SavedMatch left right i j p stamp)
    (keeps : ∀ name, left.state i name ≠ none → q.toFun name = p.toFun name)
    (aligned : ∀ name, (right.notes j).1 (q.toFun name) = ((left.notes i).1 name).map stamp) :
    SavedMatch left right i j q stamp := by
  classical
  intro name
  by_cases present : left.state i name ≠ none
  · rw [keeps name present]
    have pairList {as bs : List C} (alignedWords : ListRelated (CapturePair p stamp) as bs)
        (members : ∀ part ∈ as, part ∈ (left.notes i).2 name) : ListRelated (CapturePair q stamp) as bs := by
      induction alignedWords with
      | nil => exact .nil
      | cons head tail ih =>
        have live := ordinary_owner left hi (members _ List.mem_cons_self)
        refine .cons ?_ (ih (fun part member => members part (List.mem_cons_of_mem _ member)))
        cases head with
        | unit => exact .unit _
        | retire => exact .retire _ _ _
        | restrict owner key index =>
          rw [← keeps owner live]
          exact .restrict owner key index
        | operate owner key index related =>
          rw [← keeps owner live]
          exact .operate owner key index related
    exact pairList (old name) (fun _ member => member)
  · have absent := Decidable.not_not.mp present
    have targetVacant : right.state j (q.toFun name) = none := by
      apply (right.births_agree j hj (q.toFun name)).mp
      rw [aligned, (left.births_agree i hi name).mpr absent]
      rfl
    rw [word_empty left hi name absent, word_empty right hj (q.toFun name) targetVacant]
    exact .nil

private theorem apply_pair (left : Trace program last) (right : Trace otherProgram otherLast)
    {i j : Nat} (hi : i ≤ last) (hj : j ≤ otherLast) {p : P} {stamp : Nat → Nat}
    (aligned : ∀ name, (right.notes j).1 (p.toFun name) = ((left.notes i).1 name).map stamp)
    (injective : ∀ ⦃a b⦄, stamp a = stamp b → a = b)
    {actor otherActor : Name} {a b : C}
    (lm : a ∈ (left.notes i).2 actor) (rm : b ∈ (right.notes j).2 otherActor)
    (paired : CapturePair p stamp a b) {Q : Code → Code → Prop} {r s : R}
    (states : StageSimulation.Related Q (Renaming.registry p r) s) :
    StageSimulation.Related Q (Renaming.registry p (a.apply (left.notes i).1 r))
      (b.apply (right.notes j).1 s) := by
  cases paired with
  | unit => exact states
  | restrict owner key =>
    simp only [Capture.apply, Renaming.undo_eq]
    exact StageSimulation.undo_related states (.restrict (p.toFun owner) key)
  | operate owner key birth related =>
    simp only [Capture.apply, Renaming.undo_eq]
    exact StageSimulation.undo_related states (.operate (p.toFun owner) key related)
  | retire child otherChild birth =>
    have agreement := retirement_match left right hi hj aligned injective lm rm rfl rfl rfl
    by_cases active : (left.notes i).1 child = some birth
    · have otherActive := agreement.1.mp active
      have same := agreement.2 active
      simpa only [Capture.apply, if_pos active, if_pos otherActive, Renaming.retire_eq, same]
        using StageSimulation.retire_related states otherChild
    · have otherInactive := fun found => active (agreement.1.mpr found)
      simpa only [Capture.apply, if_neg active, if_neg otherInactive] using states

private theorem replay_recorded (left : Trace program last) (right : Trace otherProgram otherLast)
    {i j : Nat} (hi : i ≤ last) (hj : j ≤ otherLast) {p : P} {stamp : Nat → Nat}
    (aligned : ∀ name, (right.notes j).1 (p.toFun name) = ((left.notes i).1 name).map stamp)
    (injective : ∀ ⦃a b⦄, stamp a = stamp b → a = b) {actor : Name}
    {as bs : List C} (paired : ListRelated (CapturePair p stamp) as bs)
    (fromLeft : ∀ a ∈ as, a ∈ (left.notes i).2 actor)
    (fromRight : ∀ b ∈ bs, b ∈ (right.notes j).2 (p.toFun actor)) {Q : Code → Code → Prop}
    (states : StageSimulation.Related Q
      (Renaming.registry p (project (left.state i))) (project (right.state j))) :
    StageSimulation.Related Q
      (Renaming.registry p (project (replay (left.notes i).1 as (left.state i))))
      (project (replay (right.notes j).1 bs (right.state j))) := by
  have replayRelated {as bs : List C} (pairs : ListRelated (CapturePair p stamp) as bs)
      (fromLeft : ∀ a ∈ as, a ∈ (left.notes i).2 actor)
      (fromRight : ∀ b ∈ bs, b ∈ (right.notes j).2 (p.toFun actor))
      {r s : R} (base : StageSimulation.Related Q (Renaming.registry p r) s) :
      StageSimulation.Related Q (Renaming.registry p (replay (left.notes i).1 as r))
        (replay (right.notes j).1 bs s) := by
    induction pairs generalizing r s with
    | nil => exact base
    | cons heads tails ih =>
      exact ih (fun a member => fromLeft a (List.mem_cons_of_mem _ member))
        (fun b member => fromRight b (List.mem_cons_of_mem _ member))
        (apply_pair left right hi hj aligned injective
          (fromLeft _ List.mem_cons_self) (fromRight _ List.mem_cons_self) heads base)
  rw [project_replay, project_replay]
  exact replayRelated paired fromLeft fromRight states

/-- At matched cuts, replay of the actual paired saved words preserves the
registry comparison, with the saved words compared by their own evidence. -/
theorem replay_actual_words (left : Trace program last) (right : Trace otherProgram otherLast)
    {i j : Nat} (hi : i ≤ last) (hj : j ≤ otherLast) {p : P} {stamp : Nat → Nat}
    (aligned : ∀ name, (right.notes j).1 (p.toFun name) = ((left.notes i).1 name).map stamp)
    (injective : ∀ ⦃a b⦄, stamp a = stamp b → a = b) (actor : Name)
    (paired : ListRelated (CapturePair p stamp) ((left.notes i).2 actor)
      ((right.notes j).2 (p.toFun actor))) {Q : Code → Code → Prop}
    (states : StageSimulation.Related Q
      (Renaming.registry p (project (left.state i))) (project (right.state j))) :
    StageSimulation.Related Q
      (Renaming.registry p (project (replay (left.notes i).1 ((left.notes i).2 actor) (left.state i))))
      (project (replay (right.notes j).1 ((right.notes j).2 (p.toFun actor)) (right.state j))) :=
  replay_recorded left right hi hj aligned injective (actor := actor) paired
    (fun _ member => member) (fun _ member => member) states

omit [DecidableEq Name] [DecidableEq Key] in
private theorem take_paired {p : P} {stamp : Nat → Nat} {as bs : List C}
    (paired : ListRelated (CapturePair p stamp) as bs) (count : Nat) :
    ListRelated (CapturePair p stamp) (as.take count) (bs.take count) := by
  induction paired generalizing count with
  | nil => simpa only [List.take_nil] using (ListRelated.nil (rel := CapturePair p stamp))
  | cons head _ ih =>
    cases count with
    | zero => exact .nil
    | succ n => exact .cons head (ih n)

/-- The same registry comparison holds after each number of LIFO
inverses, including before either actual word is discharged. -/
theorem replay_actual_prefixes (left : Trace program last) (right : Trace otherProgram otherLast)
    {i j : Nat} (hi : i ≤ last) (hj : j ≤ otherLast) {p : P} {stamp : Nat → Nat}
    (aligned : ∀ name, (right.notes j).1 (p.toFun name) = ((left.notes i).1 name).map stamp)
    (injective : ∀ ⦃a b⦄, stamp a = stamp b → a = b) (actor : Name)
    (paired : ListRelated (CapturePair p stamp) ((left.notes i).2 actor)
      ((right.notes j).2 (p.toFun actor))) {Q : Code → Code → Prop}
    (states : StageSimulation.Related Q
      (Renaming.registry p (project (left.state i))) (project (right.state j))) (count : Nat) :
    StageSimulation.Related Q
      (Renaming.registry p (project (replay (left.notes i).1 (((left.notes i).2 actor).take count) (left.state i))))
      (project (replay (right.notes j).1 (((right.notes j).2 (p.toFun actor)).take count) (right.state j))) :=
  replay_recorded left right hi hj aligned injective (actor := actor) (take_paired paired count)
    (fun _ member => List.mem_of_mem_take member) (fun _ member => List.mem_of_mem_take member) states

/-- Every corresponding replay cut comes from two defined partial
evaluations, with the observation holding at each intermediate registry. -/
theorem replay_prefixes_in_domain (left : Trace program last) (right : Trace otherProgram otherLast)
    (leftMeaning : PartialReplayRegistry.Coeffects program)
    (rightMeaning : PartialReplayRegistry.Coeffects otherProgram)
    {i j : Nat} (hi : i ≤ last) (hj : j ≤ otherLast) {p : P} {stamp : Nat → Nat}
    (aligned : ∀ name, (right.notes j).1 (p.toFun name) = ((left.notes i).1 name).map stamp)
    (injective : ∀ ⦃a b⦄, stamp a = stamp b → a = b) (actor : Name)
    (paired : ListRelated (CapturePair p stamp) ((left.notes i).2 actor)
      ((right.notes j).2 (p.toFun actor))) {Q : Code → Code → Prop}
    (states : StageSimulation.Related Q
      (Renaming.registry p (project (left.state i))) (project (right.state j))) :
    ReplayBindingDomains.WordDefined leftMeaning (left.notes i).1 ((left.notes i).2 actor) (left.state i) ∧
    ReplayBindingDomains.WordDefined rightMeaning (right.notes j).1
      ((right.notes j).2 (p.toFun actor)) (right.state j) ∧
    ∀ count, StageSimulation.Related Q
      (Renaming.registry p (project (replay (left.notes i).1 (((left.notes i).2 actor).take count) (left.state i))))
      (project (replay (right.notes j).1 (((right.notes j).2 (p.toFun actor)).take count) (right.state j))) := by
  exact ⟨ReplayBindingDomains.saved_word_defined left i hi leftMeaning actor,
    ReplayBindingDomains.saved_word_defined right j hj rightMeaning (p.toFun actor),
    replay_actual_prefixes left right hi hj aligned injective actor paired states⟩

/-- In two actual unloads, the final phase edit preserves the comparison
established by replay. The original labels and guards come from the traces. -/
theorem unload_endpoints (left : Trace program last) (right : Trace otherProgram otherLast)
    {i j : Nat} (hi : i < last) (hj : j < otherLast) {p : P} {stamp : Nat → Nat} (actor : Name)
    (first : left.event i = .lifecycle .unload actor)
    (second : right.event j = .lifecycle .unload (p.toFun actor))
    (aligned : ∀ name, (right.notes j).1 (p.toFun name) = ((left.notes i).1 name).map stamp)
    (injective : ∀ ⦃a b⦄, stamp a = stamp b → a = b)
    (paired : ListRelated (CapturePair p stamp) ((left.notes i).2 actor)
      ((right.notes j).2 (p.toFun actor)))
    {Q : Code → Code → Prop}
    (states : StageSimulation.Related Q
      (Renaming.registry p (project (left.state i))) (project (right.state j))) :
    StageSimulation.Related Q (Renaming.registry p (project (left.state (i + 1))))
      (project (right.state (j + 1))) := by
  have firstStep := (left.step i hi).1
  have secondStep := (right.step j hj).1
  rw [first] at firstStep
  rw [second] at secondStep
  obtain ⟨_, _, _, _, _, firstEnd⟩ := firstStep
  obtain ⟨_, _, _, _, _, secondEnd⟩ := secondStep
  have projectMark (state : R) (name : Name) :
      project (mark state name .inactive) = mark (project state) name .inactive :=
    project_modify _ _ _ (fun _ => rfl)
  rw [firstEnd, secondEnd, projectMark, projectMark, Renaming.mark_eq]
  exact StageSimulation.mark_related
    (replay_actual_words left right (Nat.le_of_lt hi) (Nat.le_of_lt hj) aligned injective actor paired states)
    (p.toFun actor) .inactive

end Cordis.Repairs.GuardedBirthReplay
