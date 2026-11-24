import Cordis.Repairs.GuardedRenaming
import Cordis.Repairs.FreshNameTransport
import Cordis.Repairs.GuardedOpenProvenance

/-! An actual guarded event creates at most one incarnation. Matching live
birth stamps therefore determines the live name correspondence at a cut. -/
namespace Cordis.Repairs.GuardedBirthMatching
open Calculus Stages GuardedHistory Incarnation IncarnationReplay LegalHistory
universe u
variable {Name Key Value Code Error : Type u} [DecidableEq Name] [DecidableEq Key]
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
local notation "P" => Renaming.Permutation Name
variable {program : Code → Instruction Name Key Value Code Error}

def AtMostOneBirth (before after : R) : Prop :=
  ∀ ⦃first second : Name⦄, before first = none → after first ≠ none →
    before second = none → after second ≠ none → first = second

omit [DecidableEq Name] [DecidableEq Key] in
private theorem no_birth {before after : R} (preserves : ∀ name, before name = none → after name = none) :
    AtMostOneBirth before after :=
  fun {_ _} vacant present _ _ => False.elim (present (preserves _ vacant))

omit [DecidableEq Key] in
private theorem put_birth (before : R) (name : Name) (row : F) : AtMostOneBirth before (put before name row) := by
  have atName {query : Name} (vacant : before query = none) (present : put before name row query ≠ none) :
      query = name := by
    by_cases same : query = name
    · exact same
    · exact False.elim (present (by simp [put, same, vacant]))
  intro first second vacant present vacant' present'
  exact (atName vacant present).trans (atName vacant' present').symm

private theorem land_birth {before after : R} {actor : Name} {code : Code} {token next}
    (landed : Land program actor code before after token next) : AtMostOneBirth before after := by
  cases landed with
  | unit => exact no_birth (fun _ missing => missing)
  | provide | operate =>
    apply no_birth
    intro name vacant
    simp [write, Calculus.modify, vacant]
  | instantiate => exact put_birth _ _ _

private theorem step_birth {before after : R} (step : Calculus.Step (Land program) Stages.undo before after) :
    AtMostOneBirth before after := by
  have marked {before after : R} (birth : AtMostOneBirth before after) (name : Name) (phase) :
      AtMostOneBirth before (mark after name phase) :=
    fun {_ _} vacant present vacant' present' =>
      birth vacant (fun missing => present ((Transposition.mark_presence _ _ _ _).mpr missing))
        vacant' (fun missing => present' ((Transposition.mark_presence _ _ _ _).mpr missing))
  cases step with
  | insert => exact put_birth _ _ _
  | retire | remove | begin | leave =>
    apply no_birth
    intro name vacant
    simp [Calculus.retire, erase, mark, Calculus.modify, vacant]
  | iter _ _ _ _ _ _ _ _ _ _ _ landed
  | finish _ _ _ _ _ _ _ _ _ _ landed =>
    exact marked (land_birth landed) _ _
  | divert _ _ _ _ _ _ _ _ _ _ alternative =>
    rcases alternative with ⟨rfl, rfl⟩ | ⟨_, _, landed, rfl⟩
    · exact marked (no_birth (fun _ missing => missing)) _ _
    · exact marked (land_birth landed) _ _
  | unload actor row word view present phase free =>
    apply marked
    apply no_birth
    intro name vacant
    cases found : discharge Stages.undo word before name with
    | none => rfl
    | some row =>
      obtain ⟨_, original, _⟩ := Frame.discharge_origins before word name row found
      rw [vacant] at original
      cases original

theorem transition_birth {before after : R} {event : Event Name Key Code}
    {notes : Vestigial.CutNotes Name Key Value}
    (step : GuardedSuffix.Transition program notes event before after) :
    AtMostOneBirth before after := by
  rcases transition_cases step with native | ⟨actor, unloadEvent, unload⟩
  · exact step_birth native.toCalculus
  · obtain ⟨_, _, _, _, _, rfl⟩ := unload
    apply no_birth
    intro name vacant
    exact (Transposition.mark_presence _ _ _ _).mpr ((replay_presence _ _ _ name).mpr vacant)

variable {last : Nat}

def BornAt (trace : Trace program last) (name : Name) (birth : Nat) : Prop :=
  0 < birth ∧ birth ≤ last ∧ trace.state (birth - 1) name = none ∧ trace.state birth name ≠ none

theorem born_unique (trace : Trace program last) {first second : Name} {birth : Nat}
    (left : BornAt trace first birth) (right : BornAt trace second birth) : first = second := by
  obtain ⟨positive, bounded, vacant, present⟩ := left
  have step := transition_birth (trace.step (birth - 1) (by omega)).1
  have same : birth - 1 + 1 = birth := by omega
  rw [same] at step
  exact step vacant present right.2.2.1 right.2.2.2

theorem recorded_birth (trace : Trace program last) {cut birth : Nat} {name : Name}
    (bounded : cut ≤ last) (recorded : (trace.notes cut).1 name = some birth) :
    BornAt trace name birth ∧ birth ≤ cut := by
  rw [trace.notes_eq cut bounded] at recorded
  have lives := resident_of_birthAt recorded
  have earlier := lives.ordered
  have positive : birth ≠ 0 := by
    intro zero
    have existsAtStart := lives.present 0 (by omega) (by omega)
    exact existsAtStart (congrFun trace.start name)
  exact ⟨⟨by omega, by omega, lives.boundary.resolve_left positive,
    lives.present birth (by omega) earlier⟩, earlier⟩

theorem live_stamp_unique (trace : Trace program last) {cut birth : Nat} {first second : Name}
    (bounded : cut ≤ last) (left : (trace.notes cut).1 first = some birth)
    (right : (trace.notes cut).1 second = some birth) : first = second :=
  born_unique trace (recorded_birth trace bounded left).1 (recorded_birth trace bounded right).1

theorem captured_birth (trace : Trace program last) {cut : Nat} {actor child : Name}
    {capture : Capture Name Key Value} (bounded : cut ≤ last) (member : capture ∈ (trace.notes cut).2 actor)
    (retired : capture.token = .retire child) : BornAt trace child capture.index := by
  obtain ⟨_, step, within, stamp, acting, middle, code, next, landed, saved, presence⟩ :=
    trace.capture_origin cut bounded actor capture member
  rw [retired] at landed
  cases landed with
  | instantiate _ _ _ component child _ ready =>
    rw [stamp]
    refine ⟨by omega, by omega, by simpa using ready.1, ?_⟩
    intro absent
    have impossible := (presence child).mp absent
    simp at impossible

structure LiveMatch (left right : Name → Option Nat) (stamp : Nat → Nat) : Prop where
  injective : ∀ ⦃a b⦄, stamp a = stamp b → a = b
  forward : ∀ ⦃source birth⦄, left source = some birth → ∃ target, right target = some (stamp birth)
  backward : ∀ ⦃target birth⦄, right target = some birth →
    ∃ source original, left source = some original ∧ stamp original = birth

omit [DecidableEq Key] in
/-- Extend a finite one-to-one relation by swapping the images at each new pair. -/
theorem extend_pairs (pairs : List (Name × Name))
    (functional : ∀ {a b c}, (a, b) ∈ pairs → (a, c) ∈ pairs → b = c)
    (injective : ∀ {a b c}, (a, c) ∈ pairs → (b, c) ∈ pairs → a = b) :
    ∃ p : P, ∀ {source target}, (source, target) ∈ pairs → p.toFun source = target := by
  induction pairs with
  | nil =>
    refine ⟨⟨id, id, fun _ => rfl, fun _ => rfl⟩, ?_⟩
    simp
  | cons head tail ih =>
    obtain ⟨p, agrees⟩ := ih
      (fun left right => functional (List.mem_cons_of_mem _ left) (List.mem_cons_of_mem _ right))
      (fun left right => injective (List.mem_cons_of_mem _ left) (List.mem_cons_of_mem _ right))
    let exchange := FreshNameTransport.swap (p.toFun head.1) head.2
    let extended : P :=
      ⟨exchange.toFun ∘ p.toFun, p.invFun ∘ exchange.invFun,
        fun n => by simp, fun n => by simp⟩
    have mapsHead : extended.toFun head.1 = head.2 :=
      FreshNameTransport.swap_first _ _
    refine ⟨extended, ?_⟩
    intro source target member
    have headMember : (head.1, head.2) ∈ head :: tail := List.mem_cons_self
    by_cases sameSource : source = head.1
    · subst source
      rw [mapsHead, functional headMember member]
    have tailMember : (source, target) ∈ tail := by
      rcases List.mem_cons.mp member with same | inside
      · exact False.elim (sameSource (congrArg Prod.fst same))
      · exact inside
    have differentTarget : target ≠ head.2 := by
      intro same
      subst target
      exact sameSource (injective member headMember)
    change exchange.toFun (p.toFun source) = target
    exact (FreshNameTransport.swap_other (fun h => sameSource (p.injective h))
      (fun h => differentTarget ((agrees tailMember).symm.trans h))).trans (agrees tailMember)

variable {otherProgram : Code → Instruction Name Key Value Code Error} {otherLast : Nat}

/-- The live correspondence extends to a permutation at this cut. A later cut
can use a different permutation after the name of an earlier birth is reused. -/
theorem cut_permutation (left : Trace program last) (right : Trace otherProgram otherLast)
    {i j : Nat} (hi : i ≤ last) (hj : j ≤ otherLast) {stamp : Nat → Nat}
    (paired : LiveMatch (left.notes i).1 (right.notes j).1 stamp) :
    ∃ p : P, ∀ name, (right.notes j).1 (p.toFun name) = ((left.notes i).1 name).map stamp := by
  classical
  let actual (birth : Nat) (pair : Name × Name) : Prop :=
    (left.notes i).1 pair.1 = some birth ∧ (right.notes j).1 pair.2 = some (stamp birth)
  let pick (birth : Nat) : Option (Name × Name) :=
    if found : ∃ pair, actual birth pair then some (Classical.choose found) else none
  let pairs := (List.range (i + 1)).filterMap pick
  have sound {pair} (member : pair ∈ pairs) : ∃ birth, actual birth pair := by
    obtain ⟨birth, _, hp⟩ := List.mem_filterMap.mp member
    unfold pick at hp
    split at hp
    · exact ⟨birth, Option.some.inj hp ▸ Classical.choose_spec ‹∃ p, actual birth p›⟩
    · cases hp
  have complete {pair birth} (found : actual birth pair) : pair ∈ pairs := by
    have bound := (recorded_birth left hi found.1).2
    have existsPair : ∃ pair, actual birth pair := ⟨pair, found⟩
    have chosen := Classical.choose_spec existsPair
    have same : Classical.choose existsPair = pair := Prod.ext
      (live_stamp_unique left hi chosen.1 found.1) (live_stamp_unique right hj chosen.2 found.2)
    exact List.mem_filterMap.mpr ⟨birth, List.mem_range.mpr (by omega), by
      change (if h : ∃ pair, actual birth pair then some (Classical.choose h) else none) = some pair
      rw [dif_pos existsPair, same]⟩
  obtain ⟨p, agrees⟩ := extend_pairs pairs
    (by
      intro a b c first second
      obtain ⟨s, ls, rs⟩ := sound first
      obtain ⟨t, lt, rt⟩ := sound second
      have same := Option.some.inj (ls.symm.trans lt)
      exact live_stamp_unique right hj rs (same ▸ rt))
    (by
      intro a b c first second
      obtain ⟨s, ls, rs⟩ := sound first
      obtain ⟨t, lt, rt⟩ := sound second
      have same := paired.injective (Option.some.inj (rs.symm.trans rt))
      exact live_stamp_unique left hi ls (same ▸ lt))
  refine ⟨p, fun name => ?_⟩
  cases found : (left.notes i).1 name with
  | some birth =>
    obtain ⟨target, live⟩ := paired.forward found
    rw [agrees (complete (pair := (name, target)) ⟨found, live⟩)]
    exact live
  | none =>
    cases live : (right.notes j).1 (p.toFun name) with
    | none => rfl
    | some birth =>
      obtain ⟨source, original, present, rfl⟩ := paired.backward live
      have same := p.injective (agrees (complete (pair := (source, p.toFun name)) ⟨present, live⟩))
      subst source
      rw [found] at present
      cases present

theorem name_of_birth_match (right : Trace otherProgram otherLast) {j : Nat} (hj : j ≤ otherLast)
    {leftLive : Name → Option Nat} {stamp : Nat → Nat} {p : P}
    (aligned : ∀ name, (right.notes j).1 (p.toFun name) = (leftLive name).map stamp)
    {source target : Name} {birth : Nat} (sourceLive : leftLive source = some birth)
    (targetLive : (right.notes j).1 target = some (stamp birth)) :
    p.toFun source = target :=
  live_stamp_unique right hj (by simpa [sourceLive] using aligned source) targetLive

omit [DecidableEq Key] in
/-- Choose the image of a vacant name without changing any existing live match. -/
theorem match_fresh_draw {leftLive rightLive : Name → Option Nat} {stamp : Nat → Nat} {p : P}
    (aligned : ∀ name, rightLive (p.toFun name) = (leftLive name).map stamp)
    {source target : Name} (sourceVacant : leftLive source = none)
    (targetVacant : rightLive target = none) :
    ∃ next : P, next.toFun source = target ∧
      (∀ name, rightLive (next.toFun name) = (leftLive name).map stamp) ∧
      ∀ name, leftLive name ≠ none → next.toFun name = p.toFun name := by
  let exchange := FreshNameTransport.swap (p.toFun source) target
  let next : P := ⟨exchange.toFun ∘ p.toFun, p.invFun ∘ exchange.invFun,
    fun _ => by simp, fun _ => by simp⟩
  have imageVacant : rightLive (p.toFun source) = none := by simpa [sourceVacant] using aligned source
  refine ⟨next, FreshNameTransport.swap_first _ _, ?_, ?_⟩
  · intro name
    change rightLive (exchange.toFun (p.toFun name)) = (leftLive name).map stamp
    rw [← aligned name]
    by_cases atSource : p.toFun name = p.toFun source
    · rw [atSource, show exchange.toFun (p.toFun source) = target from
        FreshNameTransport.swap_first _ _, imageVacant, targetVacant]
    by_cases atTarget : p.toFun name = target
    · rw [atTarget, targetVacant]
      by_cases same : p.toFun source = target
      · rw [← same, show exchange.toFun (p.toFun source) = target from
          FreshNameTransport.swap_first _ _, targetVacant]
      · simpa [exchange, FreshNameTransport.swap, Ne.symm same] using imageVacant
    rw [FreshNameTransport.swap_other atSource atTarget]
  · intro name present
    have active : rightLive (p.toFun name) ≠ none := by
      rw [aligned]
      cases found : leftLive name <;> simp_all
    exact FreshNameTransport.swap_other
      (fun same => active (same ▸ imageVacant)) (fun same => active (same ▸ targetVacant))

/-- A matched pair of successor domains carries every live match forward.
When the steps add rows, their step stamps record the new paired births. -/
theorem advance_cut (left : Trace program last) (right : Trace otherProgram otherLast)
    {i j : Nat} (hi : i < last) (hj : j < otherLast) {stamp : Nat → Nat} {p : P}
    (aligned : ∀ name, (right.notes j).1 (p.toFun name) = ((left.notes i).1 name).map stamp)
    (successor : ∀ name, right.state (j + 1) (p.toFun name) = none ↔ left.state (i + 1) name = none)
    (stepStamp : stamp (i + 1) = j + 1) :
    ∀ name, (right.notes (j + 1)).1 (p.toFun name) = ((left.notes (i + 1)).1 name).map stamp := by
  rw [(left.step i hi).2, (right.step j hj).2]
  intro name
  change (right.state (j + 1) (p.toFun name)).map (fun _ => ((right.notes j).1 (p.toFun name)).getD (j + 1)) =
    ((left.state (i + 1) name).map (fun _ => ((left.notes i).1 name).getD (i + 1))).map stamp
  rw [aligned]
  cases found : left.state (i + 1) name with
  | none => rw [(successor name).mpr found]; rfl
  | some row =>
    cases other : right.state (j + 1) (p.toFun name) with
    | none =>
      have missing := (successor name).mp other
      rw [found] at missing
      cases missing
    | some otherRow =>
      cases (left.notes i).1 name <;> simp [stepStamp]

/-- The images of the actual pre-command targets are determined by their
birth correspondence, for both retirements and removals. -/
theorem command_targets (left : Trace program last) (right : Trace otherProgram otherLast)
    {i j : Nat} (hi : i < last) (hj : j < otherLast) {stamp : Nat → Nat} {p : P}
    (aligned : ∀ name, (right.notes j).1 (p.toFun name) = ((left.notes i).1 name).map stamp)
    {source target : Name}
    (lc : left.event i = .command (.retire source) ∨ left.event i = .command (.remove source))
    (rc : right.event j = .command (.retire target) ∨ right.event j = .command (.remove target)) :
    ∃ lb rb, (left.notes i).1 source = some lb ∧ (right.notes j).1 target = some rb ∧
      (stamp lb = rb ↔ p.toFun source = target) := by
  obtain ⟨lb, _, _, _, _, sourceLive, _⟩ := left.retire_remove_birth hi lc
  obtain ⟨rb, _, _, _, _, targetLive, _⟩ := right.retire_remove_birth hj rc
  refine ⟨lb + 1, rb + 1, sourceLive, targetLive, ⟨?_, ?_⟩⟩
  · intro same
    exact name_of_birth_match right (Nat.le_of_lt hj) aligned sourceLive (same.symm ▸ targetLive)
  · intro names
    have image := aligned source
    rw [names, sourceLive, targetLive, Option.map_some] at image
    exact (Option.some.inj image).symm

/-- Two actual saved retirements at paired births either both miss their
original incarnation, or both find it at the corresponding current name. -/
theorem retirement_match (left : Trace program last) (right : Trace otherProgram otherLast)
    {i j : Nat} (hi : i ≤ last) (hj : j ≤ otherLast) {stamp : Nat → Nat} {p : P}
    (aligned : ∀ name, (right.notes j).1 (p.toFun name) = ((left.notes i).1 name).map stamp)
    (injective : ∀ ⦃a b⦄, stamp a = stamp b → a = b)
    {actor otherActor source target : Name} {a b : Capture Name Key Value}
    (lm : a ∈ (left.notes i).2 actor) (rm : b ∈ (right.notes j).2 otherActor)
    (la : a.token = .retire source) (rb : b.token = .retire target) (stamped : stamp a.index = b.index) :
    ((left.notes i).1 source = some a.index ↔ (right.notes j).1 target = some b.index) ∧
    ((left.notes i).1 source = some a.index → p.toFun source = target) := by
  have rightBorn := captured_birth right hj rm rb
  have currentName (found : (left.notes i).1 source = some a.index) : p.toFun source = target := by
    have moved : (right.notes j).1 (p.toFun source) = some b.index := by
      rw [aligned, found, Option.map_some, stamped]
    exact born_unique right (recorded_birth right hj moved).1 rightBorn
  refine ⟨⟨?_, ?_⟩, currentName⟩
  · intro found
    rw [← currentName found, aligned, found, Option.map_some, stamped]
  · intro found
    obtain ⟨name, image⟩ := p.surjective target
    have original := aligned name
    rw [image, found] at original
    cases live : (left.notes i).1 name with
    | none => simp [live] at original
    | some birth =>
      rw [live, Option.map_some] at original
      have index := injective (stamped.trans (Option.some.inj original))
      rw [← index] at live
      have names := born_unique left (recorded_birth left hi live).1 (captured_birth left hi lm la)
      exact names ▸ live

end Cordis.Repairs.GuardedBirthMatching
