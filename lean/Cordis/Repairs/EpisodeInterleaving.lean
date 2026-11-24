import Cordis.Repairs.GuardedNormalization
import Cordis.Repairs.GuardedOpenProvenance

/-! Provision reservations can force two surviving episodes to interleave,
even if child commands may be included in an episode's block. -/
namespace Cordis.Repairs.EpisodeInterleaving
open Calculus Stages LegalHistory GuardedHistory Incarnation
open Vestigial (cutNotes eventActor)
open OrchestrationSorting (Command)

inductive Code where
  | startP | endP | startQ | endQ | provideLow | provideHigh
  deriving DecidableEq

abbrev Values : Bool → Type := fun _ => Nat

def operations : PaperEffectEquations.CoeffectOperations Values where
  Name _ := Empty
  Argument _ name := nomatch name
  Outcome _ name := nomatch name
  operation _ name := nomatch name

abbrev R := TypedRegistry.RawRegistry Nat operations Code
abbrev F := TypedRegistry.RawFiber Nat operations Code
abbrev Ev := Event Nat Bool Code
abbrev V := TypedRegistry.Scalar operations

def rootP : Component Bool Code := ⟨fun _ => false, fun _ => false, .startP⟩
def rootQ : Component Bool Code := ⟨fun _ => false, (! ·), .startQ⟩
def low : Component Bool Code := ⟨fun _ => false, (! ·), .provideLow⟩
def high : Component Bool Code := ⟨fun _ => false, id, .provideHigh⟩

def entry : Code → TypedRegistry.Instruction Nat operations Code
  | .startP => ⟨.instantiate low, fun _ => some .endP⟩
  | .endP => ⟨.instantiate high, fun _ => none⟩
  | .startQ => ⟨.instantiate high, fun _ => some .endQ⟩
  | .endQ | .provideLow => ⟨.provide false 10, fun _ => none⟩
  | .provideHigh => ⟨.provide true 20, fun _ => none⟩

abbrev program := TypedRegistry.encodeProgram entry
abbrev Source (last : Nat) := Trace program last

def view : View Nat Bool := fun _ => 0
def valueLow : V := TypedCoeffectReplay.pack false 10
def valueHigh : V := TypedCoeffectReplay.pack true 20

def s0 : R := fun _ => none
def s1 : R := put s0 0 (fresh rootP none)
def s2 : R := mark s1 0 (.reloading .startP [] view)
def s3 : R := mark (put s2 2 (fresh low (some 0))) 0 (.reloading .endP [.retire 2] view)
def s4 : R := retire s3 2
def s5 : R := erase s4 2
def s6 : R := put s5 1 (fresh rootQ none)
def s7 : R := mark s6 1 (.reloading .startQ [] view)
def s8 : R := mark (put s7 3 (fresh high (some 1))) 1 (.reloading .endQ [.retire 3] view)
def s9 : R := retire s8 3
def s10 : R := erase s9 3
def s11 : R := mark (write s10 1 false (some valueLow)) 1 (.active [.restrict 1 false, .retire 3] view)
def s12 : R := mark (put s11 4 (fresh high (some 0))) 0 (.active [.retire 4, .retire 2] view)
def s13 : R := mark s12 4 (.reloading .provideHigh [] view)
def s14 : R := mark (write s13 4 true (some valueHigh)) 4 (.active [.restrict 4 true] view)

def states : Nat → R
  | 0 => s0 | 1 => s1 | 2 => s2 | 3 => s3 | 4 => s4 | 5 => s5 | 6 => s6 | 7 => s7
  | 8 => s8 | 9 => s9 | 10 => s10 | 11 => s11 | 12 => s12 | 13 => s13 | _ => s14

def events : Nat → Ev
  | 0 => .command (.insert 0 rootP)
  | 1 => .lifecycle .begin 0
  | 2 => .lifecycle .iter 0
  | 3 => .command (.retire 2)
  | 4 => .command (.remove 2)
  | 5 => .command (.insert 1 rootQ)
  | 6 => .lifecycle .begin 1
  | 7 => .lifecycle .iter 1
  | 8 => .command (.retire 3)
  | 9 => .command (.remove 3)
  | 10 => .lifecycle .finish 1
  | 11 => .lifecycle .finish 0
  | 12 => .lifecycle .begin 4
  | _ => .lifecycle .finish 4

private theorem birthLow : Insertable s2 2 low (some 0) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro name parent
    cases parent
    exact Option.noConfusion
  · intro name key
    by_cases owner : name = 0
    · subst name; simp [s2, s1, mark, Calculus.modify, put, fresh, rootP]
    · simp [s2, s1, s0, mark, Calculus.modify, put, owner]

private theorem removeLow : Removable s4 2 := by
  refine ⟨rfl, rfl, fun _ => rfl, ?_⟩
  intro name
  by_cases owner : name = 0
  · subst name; change (none : Option Nat) ≠ some 2; decide
  by_cases atChild : name = 2
  · subst name; change (some 0 : Option Nat) ≠ some 2; decide
  simp [s4, s3, s2, s1, s0, retire, mark, Calculus.modify, put, owner, atChild]

private theorem insertQ : Insertable s5 1 rootQ none := by
  refine ⟨rfl, by simp, ?_⟩
  intro name key
  by_cases owner : name = 0
  · subst name
    change rootQ.provides key = true → ¬ (rootP.provides key = true)
    simp [rootP]
  by_cases atChild : name = 2
  · subst name; exact True.intro
  simp [s5, s4, s3, s2, s1, s0, erase, retire, mark, Calculus.modify, put, owner, atChild]

private theorem birthQHigh : Insertable s7 3 high (some 1) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro name parent
    cases parent
    exact Option.noConfusion
  · intro name key
    by_cases owner : name = 0
    · subst name
      change high.provides key = true → ¬ (rootP.provides key = true)
      simp [rootP]
    by_cases atQ : name = 1
    · subst name
      change high.provides key = true → ¬ (rootQ.provides key = true)
      cases key <;> decide
    by_cases atChild : name = 2
    · subst name; exact True.intro
    simp [s7, s6, s5, s4, s3, s2, s1, s0, erase, retire, mark, Calculus.modify, put, owner, atQ, atChild]

private theorem removeHigh : Removable s9 3 := by
  refine ⟨rfl, rfl, fun _ => rfl, ?_⟩
  intro name
  by_cases owner : name = 0
  · subst name; change (none : Option Nat) ≠ some 3; decide
  by_cases atQ : name = 1
  · subst name; change (none : Option Nat) ≠ some 3; decide
  by_cases first : name = 2
  · subst name; exact True.intro
  by_cases second : name = 3
  · subst name; change (some 1 : Option Nat) ≠ some 3; decide
  simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, s0, erase, retire, mark, Calculus.modify, put, owner, atQ, first, second]

private theorem birthPHigh : Insertable s11 4 high (some 0) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro name parent
    cases parent
    exact Option.noConfusion
  · intro name key
    by_cases owner : name = 0
    · subst name
      change high.provides key = true → ¬ (rootP.provides key = true)
      simp [rootP]
    by_cases atQ : name = 1
    · subst name
      change high.provides key = true → ¬ (rootQ.provides key = true)
      cases key <;> decide
    by_cases first : name = 2
    · subst name; exact True.intro
    by_cases second : name = 3
    · subst name; exact True.intro
    simp [s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, s0, write, erase, retire, mark, Calculus.modify,
      put, owner, atQ, first, second]

private theorem target_none {state : R} {actor : Nat} {row : F} (present : state actor = some row)
    (live : row.retired = false) (requires : ∀ key, row.component.requires key = false) :
    Target state actor view := by
  simp only [Target, present]
  exact ⟨live, fun key required => Bool.noConfusion ((requires key).symm.trans required)⟩

def trace : Source 14 where
  state := states
  notes := cutNotes states (fun cut => eventActor (events cut))
  event := events
  start := rfl
  seed := rfl
  step cut valid := by
    have cuts : cut = 0 ∨ cut = 1 ∨ cut = 2 ∨ cut = 3 ∨ cut = 4 ∨ cut = 5 ∨ cut = 6 ∨
      cut = 7 ∨ cut = 8 ∨ cut = 9 ∨ cut = 10 ∨ cut = 11 ∨ cut = 12 ∨ cut = 13 := by omega
    rcases cuts with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨⟨⟨rfl, by simp, fun _ _ => trivial⟩, rfl⟩, rfl⟩
    · exact ⟨.begin s1 0 (fresh rootP none) view rfl rfl Option.noConfusion (target_none rfl rfl (fun _ => rfl)), rfl⟩
    · exact ⟨.iter s2 _ 0 { (fresh rootP none : F) with phase := .reloading .startP [] view }
        .startP [] view (.retire 2) .endP rfl rfl (target_none rfl rfl (fun _ => rfl))
        (.instantiate s2 0 .startP low 2 rfl birthLow), rfl⟩
    · exact ⟨⟨Option.noConfusion, rfl⟩, rfl⟩
    · exact ⟨⟨removeLow, rfl⟩, rfl⟩
    · exact ⟨⟨insertQ, rfl⟩, rfl⟩
    · exact ⟨.begin s6 1 (fresh rootQ none) view rfl rfl Option.noConfusion (target_none rfl rfl (fun _ => rfl)), rfl⟩
    · exact ⟨.iter s7 _ 1 { (fresh rootQ none : F) with phase := .reloading .startQ [] view }
        .startQ [] view (.retire 3) .endQ rfl rfl (target_none rfl rfl (fun _ => rfl))
        (.instantiate s7 1 .startQ high 3 rfl birthQHigh), rfl⟩
    · exact ⟨⟨Option.noConfusion, rfl⟩, rfl⟩
    · exact ⟨⟨removeHigh, rfl⟩, rfl⟩
    · exact ⟨.finish s10 _ 1 { (fresh rootQ none : F) with phase := .reloading .endQ [.retire 3] view }
        .endQ [.retire 3] view (.restrict 1 false) rfl rfl (target_none rfl rfl (fun _ => rfl))
        (.provide s10 1 .endQ _ false valueLow rfl rfl rfl rfl), rfl⟩
    · exact ⟨.finish s11 _ 0 { (fresh rootP none : F) with phase := .reloading .endP [.retire 2] view }
        .endP [.retire 2] view (.retire 4) rfl rfl (target_none rfl rfl (fun _ => rfl))
        (.instantiate s11 0 .endP high 4 rfl birthPHigh), rfl⟩
    · exact ⟨.begin s12 4 (fresh high (some 0)) view rfl rfl Option.noConfusion (target_none rfl rfl (fun _ => rfl)), rfl⟩
    · exact ⟨.finish s13 _ 4 { (fresh high (some 0) : F) with phase := .reloading .provideHigh [] view }
        .provideHigh [] view (.restrict 4 true) rfl rfl (target_none rfl rfl (fun _ => rfl))
        (.provide s13 4 .provideHigh _ true valueHigh rfl rfl rfl rfl), rfl⟩

theorem open_only : ¬ Nonempty (ClosedEpisode trace) := by
  rintro ⟨closed⟩
  obtain ⟨unload, _⟩ := unload_boundary trace closed.interval
  change events closed.closed = .lifecycle .unload closed.name at unload
  have bound := closed.interval.bounded
  have cuts : closed.closed = 0 ∨ closed.closed = 1 ∨ closed.closed = 2 ∨ closed.closed = 3 ∨
      closed.closed = 4 ∨ closed.closed = 5 ∨ closed.closed = 6 ∨ closed.closed = 7 ∨
      closed.closed = 8 ∨ closed.closed = 9 ∨ closed.closed = 10 ∨ closed.closed = 11 ∨
      closed.closed = 12 ∨ closed.closed = 13 := by omega
  rcases cuts with cut | cut | cut | cut | cut | cut | cut | cut | cut | cut | cut | cut | cut | cut <;>
    simp [events, cut] at unload

def finalP : F := { (fresh rootP none : F) with phase := .active [.retire 4, .retire 2] view }
def finalQ : F := { (fresh rootQ none : F) with
  table := fun key => if key = false then some valueLow else none
  phase := .active [.restrict 1 false, .retire 3] view }
def finalChild : F := { (fresh high (some 0) : F) with
  table := fun key => if key = true then some valueHigh else none
  phase := .active [.restrict 4 true] view }

theorem final_rows (name : Nat) : trace.state 14 name =
    if name = 0 then some finalP else if name = 1 then some finalQ else if name = 4 then some finalChild else none := by
  change s14 name = _
  by_cases owner : name = 0
  · subst name; rfl
  by_cases atQ : name = 1
  · subst name; rfl
  by_cases child : name = 4
  · subst name; rfl
  by_cases removedLow : name = 2
  · subst name; rfl
  by_cases removedHigh : name = 3
  · subst name; rfl
  simp [s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, s0, write, erase, retire,
    mark, Calculus.modify, put, owner, atQ, child, removedLow, removedHigh]

theorem quiet : Progress.Quiet (trace.state 14) := by
  intro name row present
  rw [final_rows] at present
  split at present
  · cases Option.some.inj present
    exact target_none (by rw [final_rows, if_pos ‹name = 0›]) rfl (fun _ => rfl)
  split at present
  · cases Option.some.inj present
    exact target_none (by rw [final_rows, if_neg ‹name ≠ 0›, if_pos ‹name = 1›]) rfl (fun _ => rfl)
  split at present
  · cases Option.some.inj present
    exact target_none (by rw [final_rows, if_neg ‹name ≠ 0›, if_neg ‹name ≠ 1›, if_pos ‹name = 4›]) rfl
      (fun _ => rfl)
  · cases present

theorem total : SupportAtQuiescence.TotalProvision (trace.state 14) := by
  intro name row present _ key
  rw [final_rows] at present
  split at present
  · cases Option.some.inj present
    simp [finalP, rootP, fresh]
  split at present
  · cases Option.some.inj present
    cases key <;> simp [finalQ, rootQ, fresh]
  split at present
  · cases Option.some.inj present
    cases key <;> simp [finalChild, high, fresh]
  · cases present

private theorem allocation_guard {state landed : R} {actor : Nat} {code : Code}
    {token : Inverse Nat Bool V} {next : Option Code} {component : Component Bool Code}
    (executed : Land program actor code state landed token next)
    (instruction : (program code).action = .instantiate component) :
    ∃ name, Insertable state name component (some actor) := by
  cases executed with
  | unit _ _ _ action => cases instruction.symm.trans action
  | provide _ _ _ _ _ _ action _ _ _ => cases instruction.symm.trans action
  | operate _ _ _ _ _ _ _ _ _ _ action _ _ => cases instruction.symm.trans action
  | instantiate _ _ _ payload name action ready =>
    have eq : component = payload := Stages.Action.instantiate.inj (instruction.symm.trans action)
    exact ⟨name, eq.symm ▸ ready⟩

/-- These endpoint rows force a P activation, a Q activation and another P
activation in that strict order. The names of both roots and of the retained
child are arbitrary, as are all fresh draws during the replay. -/
theorem forced_interleaving {last : Nat} (replay : Source last)
    (openOnly : ¬ Nonempty (ClosedEpisode replay)) (quiet : Progress.Quiet (replay.state last))
    {p q child : Nat} (different : p ≠ q) {pRow qRow childRow : F}
    (pFound : replay.state last p = some pRow) (pComponent : pRow.component = rootP)
    (pActive : pRow.phase.available) (qFound : replay.state last q = some qRow)
    (qComponent : qRow.component = rootQ) (qRoot : qRow.parent = none) (qActive : qRow.phase.available)
    (childFound : replay.state last child = some childRow) (childComponent : childRow.component = high)
    (parent : childRow.parent = some p) :
    ∃ pFirst qFirst pLater : Nat, pFirst < qFirst ∧ qFirst < pLater ∧ pLater < last ∧
      ∃ (firstKind betweenKind lastKind : Lifecycle),
        replay.event pFirst = .lifecycle firstKind p ∧ replay.event qFirst = .lifecycle betweenKind q ∧
        replay.event pLater = .lifecycle lastKind p := by
  obtain ⟨pFirst, pKind, pBound, firstEvent, pLanded, pToken, pNext, firstLand⟩ :=
    replay.active_entry_landing openOnly quiet (Nat.le_refl _) pFound pActive
  obtain ⟨qFirst, qKind, qBound, qEvent, qLanded, qToken, qNext, qLand⟩ :=
    replay.active_entry_landing openOnly quiet (Nat.le_refl _) qFound qActive
  obtain ⟨lowDraw, lowReady⟩ := allocation_guard firstLand (by rw [pComponent]; rfl)
  obtain ⟨highDraw, highReady⟩ := allocation_guard qLand (by rw [qComponent]; rfl)
  obtain ⟨qInsert, qInserted, qLives, insertEvent, newRoot⟩ :=
    replay.resident_root_insertion openOnly (Nat.le_refl _) qFound qRoot
  have lowOrder := replay.reservation_precedes_residency qLives (by omega) newRoot lowReady false
    (by rw [qComponent]; rfl) rfl
  have insertedBefore : qInsert < qFirst := by
    apply Nat.lt_of_not_ge
    intro tooSoon
    by_cases same : qFirst = qInsert
    · have impossible := qEvent.symm.trans (same.symm ▸ insertEvent)
      cases impossible
    · obtain ⟨active, step⟩ := replay.activation_at openOnly quiet qBound qEvent
      have view := activation_installs_view step active
      have persists := replay.installed_through openOnly q (show qFirst + 1 ≤ qInsert by omega) (by omega) view
      have insertion := (replay.step qInsert qInserted).1
      rw [insertEvent] at insertion
      have empty := insertion.1.1
      rw [show ControlFrame.viewAt (replay.state qInsert) q = none by simp [ControlFrame.viewAt, empty]] at persists
      exact view persists.symm
  obtain ⟨pLater, lastKind, lastBound, childLives, lastEvent, bornChild⟩ :=
    replay.resident_child_creation openOnly quiet (Nat.le_refl _) childFound parent
  have highOrder := replay.reservation_precedes_residency childLives (by omega) bornChild highReady true
    (by rw [childComponent]; rfl) rfl
  have unequal : qFirst ≠ pLater := by
    intro same
    exact different (Event.lifecycle.inj (lastEvent.symm.trans (same ▸ qEvent))).2
  exact ⟨pFirst, qFirst, pLater, by omega, by omega, lastBound, pKind, qKind, lastKind, firstEvent, qEvent, lastEvent⟩

/-- Even a block that contains its own required child commands must put
all its actor's lifecycle events on the same side of a different block. -/
def EpisodeBefore {last : Nat} (replay : Source last) (first second : Nat) : Prop :=
  ∀ {i j : Nat} {a b : Lifecycle}, i < last → j < last →
    replay.event i = .lifecycle a first → replay.event j = .lifecycle b second → i < j

/-- No quiet open replay preserving the required endpoint rows can put P
and Q in disjoint episode blocks, even with different fresh names and even
if the child commands are allowed inside either block. -/
theorem no_serial_replay {last : Nat} (replay : Source last)
    (openOnly : ¬ Nonempty (ClosedEpisode replay)) (quiet : Progress.Quiet (replay.state last))
    {p q child : Nat} (different : p ≠ q) {pRow qRow childRow : F}
    (pFound : replay.state last p = some pRow) (pComponent : pRow.component = rootP)
    (pActive : pRow.phase.available) (qFound : replay.state last q = some qRow)
    (qComponent : qRow.component = rootQ) (qRoot : qRow.parent = none) (qActive : qRow.phase.available)
    (childFound : replay.state last child = some childRow) (childComponent : childRow.component = high)
    (parent : childRow.parent = some p) :
    ¬ (EpisodeBefore replay p q ∨ EpisodeBefore replay q p) := by
  obtain ⟨pFirst, qFirst, pLater, early, later, bound, _, _, _, atP, atQ, atLater⟩ :=
    forced_interleaving replay openOnly quiet different pFound pComponent pActive qFound qComponent qRoot qActive
      childFound childComponent parent
  rintro (pBeforeQ | qBeforeP)
  · exact Nat.lt_asymm later (pBeforeQ bound (by omega) atLater atQ)
  · exact Nat.lt_asymm early (qBeforeP (by omega) (by omega) atQ atP)

theorem roots_in_order : originalRoots trace = [.insert 0 rootP, .insert 1 rootQ] := rfl

theorem neither_root_supports_the_other :
    ¬ SupportUniqueness.ActivePredecessor (trace.state 14) 0 1 ∧
    ¬ SupportUniqueness.ActivePredecessor (trace.state 14) 1 0 := by
  constructor
  · rintro ⟨_, _, actor, prior, atActor, atPrior, edge⟩
    rw [final_rows] at atActor atPrior
    have q : finalQ = actor := Option.some.inj atActor
    have p : finalP = prior := Option.some.inj atPrior
    subst actor
    subst prior
    rcases edge with parent | ⟨key, required, _⟩
    · cases parent
    · cases required
  · rintro ⟨_, _, actor, prior, atActor, atPrior, edge⟩
    rw [final_rows] at atActor atPrior
    have p : finalP = actor := Option.some.inj atActor
    have q : finalQ = prior := Option.some.inj atPrior
    subst actor
    subst prior
    rcases edge with parent | ⟨key, required, _⟩
    · cases parent
    · cases required

private theorem component_eq {left right : Component Bool Code}
    (fields : StageSimulation.ComponentRelated Eq left right) : left = right := by
  obtain ⟨a, b, c⟩ := left
  obtain ⟨_, _, _⟩ := right
  obtain ⟨requires, provides, entry⟩ := fields
  cases requires
  cases provides
  cases entry
  rfl

/-- Neither serialized order works even after permitted vestige erasure
and any endpoint renaming. No particular replay order of external child
commands or equality of fresh draws is assumed. -/
theorem no_serial_after_renaming_and_erasure [Setoid V] {last : Nat} (replay : Source last)
    (openOnly : ¬ Nonempty (ClosedEpisode replay)) (quiet : Progress.Quiet (replay.state last))
    (names : Renaming.Permutation Nat) {projected : R}
    (erased : VestigeErasures (trace.state 14) projected)
    (endpoint : StageSimulation.Related Eq (Renaming.registry names projected) (replay.state last)) :
    ¬ (EpisodeBefore replay (names.toFun 0) (names.toFun 1) ∨
      EpisodeBefore replay (names.toFun 1) (names.toFun 0)) := by
  have present {name : Nat} {row : F} (found : trace.state 14 name = some row)
      (active : row.phase.available) :
      Renaming.registry names projected (names.toFun name) = some (Renaming.fiber names row) := by
    rw [Renaming.registry_at, erased.active_row found active]
    rfl
  obtain ⟨pRow, atP, fieldsP⟩ := StageSimulation.present_related endpoint (names.toFun 0)
    (Renaming.fiber names finalP) (present (by rfl) (by trivial))
  obtain ⟨qRow, atQ, fieldsQ⟩ := StageSimulation.present_related endpoint (names.toFun 1)
    (Renaming.fiber names finalQ) (present (by rfl) (by trivial))
  obtain ⟨childRow, atChild, fieldsChild⟩ := StageSimulation.present_related endpoint (names.toFun 4)
    (Renaming.fiber names finalChild) (present (by rfl) (by trivial))
  have pActive := (GuardObservations.phase_available_iff fieldsP.phase.observed.1).mp (by trivial)
  have qActive := (GuardObservations.phase_available_iff fieldsQ.phase.observed.1).mp (by trivial)
  have qRoot : qRow.parent = none := fieldsQ.parent.symm
  have childParent : childRow.parent = some (names.toFun 0) := fieldsChild.parent.symm
  exact no_serial_replay replay openOnly quiet (fun same => Nat.noConfusion (names.injective same))
    atP (component_eq fieldsP.component).symm pActive atQ (component_eq fieldsQ.component).symm qRoot qActive
    atChild (component_eq fieldsChild.component).symm childParent

end Cordis.Repairs.EpisodeInterleaving
