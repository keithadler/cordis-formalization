import Cordis.Repairs.GuardedCausalOrder

/-! Identical orchestration commands can address different child births.
Both traces have contiguous episodes, use the same fresh draws in order,
and differ on the presence of an observable provision. -/
namespace Cordis.Repairs.ChildCommandConfluence
open Calculus Stages GuardedHistory LegalHistory
open Vestigial (cutNotes eventActor)
open OrchestrationSorting (Command)

inductive Code where
  | spawn (key : Bool)
  | provide (key : Bool)
  deriving DecidableEq

abbrev Values : Bool → Type := fun _ => Nat

def operations : PaperEffectEquations.CoeffectOperations Values where
  Name _ := Empty
  Argument _ name := nomatch name
  Outcome _ name := nomatch name
  operation _ name := nomatch name

abbrev R := TypedRegistry.RawRegistry Nat operations Code
abbrev F := TypedRegistry.RawFiber Nat operations Code
abbrev V := TypedRegistry.Scalar operations
abbrev Ev := Event Nat Bool Code

def root (key : Bool) : Component Bool Code := ⟨fun _ => false, fun _ => false, .spawn key⟩
def child (key : Bool) : Component Bool Code := ⟨fun _ => false, (· == key), .provide key⟩

def entry : Code → TypedRegistry.Instruction Nat operations Code
  | .spawn key => ⟨.instantiate (child key), fun _ => none⟩
  | .provide key => ⟨.provide key 1, fun _ => none⟩

abbrev program := TypedRegistry.encodeProgram entry
abbrev Source := Trace program 10

def rootName (key : Bool) : Nat := if key then 1 else 0
def view : View Nat Bool := fun _ => 0
def value (key : Bool) : V := TypedCoeffectReplay.pack key 1

def openedRoot (key : Bool) : F :=
  { (fresh (root key) none : F) with phase := .reloading (.spawn key) [] view }

def activeRoot (key : Bool) (draw : Nat) : F :=
  { (fresh (root key) none : F) with phase := .active [.retire draw] view }

def openedChild (key : Bool) : F :=
  { (fresh (child key) (some (rootName key)) : F) with phase := .reloading (.provide key) [] view }

def activeChild (key : Bool) : F :=
  { (fresh (child key) (some (rootName key)) : F) with
    phase := .active [.restrict 3 key] view
    table := fun k => if k = key then some (value key) else none }

def s0 : R := fun _ => none
def s1 : R := put s0 0 (fresh (root false) none)
def s2 : R := put s1 1 (fresh (root true) none)
def s3 (first : Bool) : R := mark s2 (rootName first) (openedRoot first).phase
def s4 (first : Bool) : R :=
  mark (put (s3 first) 2 (fresh (child first) (some (rootName first))))
    (rootName first) (activeRoot first 2).phase
def s5 (first : Bool) : R := retire (s4 first) 2
def s6 (first : Bool) : R := erase (s5 first) 2
def s7 (first : Bool) : R := mark (s6 first) (rootName (!first)) (openedRoot (!first)).phase
def s8 (first : Bool) : R :=
  mark (put (s7 first) 3 (fresh (child (!first)) (some (rootName (!first)))))
    (rootName (!first)) (activeRoot (!first) 3).phase
def s9 (first : Bool) : R := mark (s8 first) 3 (openedChild (!first)).phase
def s10 (first : Bool) : R :=
  mark (write (s9 first) 3 (!first) (some (value (!first)))) 3 (activeChild (!first)).phase

def states (first : Bool) : Nat → R
  | 0 => s0 | 1 => s1 | 2 => s2 | 3 => s3 first | 4 => s4 first
  | 5 => s5 first | 6 => s6 first | 7 => s7 first | 8 => s8 first | 9 => s9 first
  | _ => s10 first

def events (first : Bool) : Nat → Ev
  | 0 => .command (.insert 0 (root false))
  | 1 => .command (.insert 1 (root true))
  | 2 => .lifecycle .begin (rootName first)
  | 3 => .lifecycle .finish (rootName first)
  | 4 => .command (.retire 2)
  | 5 => .command (.remove 2)
  | 6 => .lifecycle .begin (rootName (!first))
  | 7 => .lifecycle .finish (rootName (!first))
  | 8 => .lifecycle .begin 3
  | _ => .lifecycle .finish 3

private theorem target {state : R} {name : Nat} {row : F}
    (found : state name = some row) (live : row.retired = false)
    (requires : ∀ key, row.component.requires key = false) : Target state name view := by
  simp only [Target, found]
  exact ⟨live, fun key needed => Bool.noConfusion ((requires key).symm.trans needed)⟩

private theorem second_root_insertion : Insertable s1 1 (root true) none := by
  refine ⟨rfl, by simp, fun other key => ?_⟩
  by_cases atRoot : other = 0
  · subst other
    simp [s1, put, root, fresh]
  · simp [s1, put, s0, atRoot]

private theorem first_birth (first : Bool) :
    Insertable (s3 first) 2 (child first) (some (rootName first)) := by
  refine ⟨by cases first <;> rfl, ?_, ?_⟩
  · intro p parent
    cases parent
    cases first <;> exact Option.noConfusion
  · intro name key
    by_cases a : name = 0
    · subst name
      cases first <;> simp [s3, s2, s1, put, mark, Calculus.modify, rootName, fresh, root]
    by_cases b : name = 1
    · subst name
      cases first <;> simp [s3, s2, put, mark, Calculus.modify, rootName, fresh, root]
    cases first <;> simp [s3, s2, s1, s0, put, mark, Calculus.modify, rootName, a, b]

private theorem first_removal (first : Bool) : Removable (s5 first) 2 := by
  have atChild : s5 first 2 = some { (fresh (child first) (some (rootName first)) : F) with retired := true } := by
    cases first <;> rfl
  rw [Removable, atChild]
  refine ⟨rfl, rfl, fun _ => rfl, fun name => ?_⟩
  by_cases a : name = 0
  · subst name
    cases first <;> exact Option.noConfusion
  by_cases b : name = 1
  · subst name
    cases first <;> exact Option.noConfusion
  by_cases c : name = 2
  · subst name
    rw [atChild]
    cases first <;> decide
  cases first <;>
    simp [s5, s4, s3, s2, s1, s0, retire, put, mark, Calculus.modify, rootName, a, b, c]

private theorem second_birth (first : Bool) :
    Insertable (s7 first) 3 (child (!first)) (some (rootName (!first))) := by
  refine ⟨by cases first <;> rfl, ?_, ?_⟩
  · intro p parent
    cases parent
    cases first <;> exact Option.noConfusion
  · intro name key
    by_cases a : name = 0
    · subst name
      cases first <;> simp [s7, s6, s5, s4, s3, s2, s1, put, erase, retire, mark,
        Calculus.modify, rootName, fresh, root]
    by_cases b : name = 1
    · subst name
      cases first <;> simp [s7, s6, s5, s4, s3, s2, put, erase, retire, mark,
        Calculus.modify, rootName, fresh, root]
    by_cases c : name = 2
    · subst name
      cases first <;> trivial
    cases first <;> simp [s7, s6, s5, s4, s3, s2, s1, s0, put, erase, retire, mark,
      Calculus.modify, rootName, a, b, c]

def trace (first : Bool) : Source where
  state := states first
  notes := cutNotes (states first) (fun cut => eventActor (events first cut))
  event := events first
  start := rfl
  seed := rfl
  step cut valid := by
    have cuts : cut = 0 ∨ cut = 1 ∨ cut = 2 ∨ cut = 3 ∨ cut = 4 ∨
        cut = 5 ∨ cut = 6 ∨ cut = 7 ∨ cut = 8 ∨ cut = 9 := by omega
    rcases cuts with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨⟨⟨rfl, by simp, fun _ _ => trivial⟩, rfl⟩, rfl⟩
    · exact ⟨⟨second_root_insertion, rfl⟩, rfl⟩
    · have found : s2 (rootName first) = some (fresh (root first) none) := by cases first <;> rfl
      exact ⟨.begin s2 _ _ view found rfl (by cases first <;> exact Option.noConfusion) (target found rfl (fun _ => rfl)), rfl⟩
    · have found : s3 first (rootName first) = some (openedRoot first) := by cases first <;> rfl
      exact ⟨.finish (s3 first) _ _ _ (.spawn first) [] view (.retire 2) found rfl
        (target found rfl (fun _ => rfl))
        (.instantiate (s3 first) _ _ (child first) 2 rfl (first_birth first)), rfl⟩
    · exact ⟨⟨by cases first <;> exact Option.noConfusion, rfl⟩, rfl⟩
    · exact ⟨⟨first_removal first, rfl⟩, rfl⟩
    · have found : s6 first (rootName (!first)) = some (fresh (root (!first)) none) := by cases first <;> rfl
      exact ⟨.begin (s6 first) _ _ view found rfl (by cases first <;> exact Option.noConfusion) (target found rfl (fun _ => rfl)), rfl⟩
    · have found : s7 first (rootName (!first)) = some (openedRoot (!first)) := by cases first <;> rfl
      exact ⟨.finish (s7 first) _ _ _ (.spawn (!first)) [] view (.retire 3) found rfl
        (target found rfl (fun _ => rfl))
        (.instantiate (s7 first) _ _ (child (!first)) 3 rfl (second_birth first)), rfl⟩
    · have found : s8 first 3 = some (fresh (child (!first)) (some (rootName (!first)))) := by cases first <;> rfl
      exact ⟨.begin (s8 first) 3 _ view found rfl (by cases first <;> exact Option.noConfusion) (target found rfl (fun _ => rfl)), rfl⟩
    · have found : s9 first 3 = some (openedChild (!first)) := by cases first <;> rfl
      exact ⟨.finish (s9 first) _ 3 _ (.provide (!first)) [] view (.restrict 3 (!first)) found rfl
        (target found rfl (fun _ => rfl))
        (.provide (s9 first) 3 _ _ (!first) (value (!first)) rfl found
          (by cases first <;> rfl) rfl), rfl⟩

theorem raw_commands (first : Bool) :
    (scheduledEvents (trace first)).filterMap (fun
      | .command cmd => some cmd
      | .lifecycle _ _ => none) =
      [.insert 0 (root false), .insert 1 (root true), .retire 2, .remove 2] := rfl

/-- The same names are drawn in the same order. The command at the next cut
addresses the first draw, whose parent changes with the lifecycle schedule. -/
theorem draws_and_command_target (first : Bool) :
    (trace first).state 3 2 = none ∧
    (trace first).state 4 2 = some (fresh (child first) (some (rootName first))) ∧
    (trace first).event 4 = .command (.retire 2) ∧
    (trace first).state 7 3 = none ∧
    (trace first).state 8 3 = some (fresh (child (!first)) (some (rootName (!first)))) := by
  cases first <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem endpoint_rows (first : Bool) (name : Nat) : (trace first).state 10 name =
    if name = rootName first then some (activeRoot first 2)
    else if name = rootName (!first) then some (activeRoot (!first) 3)
    else if name = 3 then some (activeChild (!first)) else none := by
  change s10 first name = _
  by_cases a : name = 0
  · subst name; cases first <;> rfl
  by_cases b : name = 1
  · subst name; cases first <;> rfl
  by_cases c : name = 2
  · subst name; cases first <;> rfl
  by_cases d : name = 3
  · subst name; cases first <;> rfl
  cases first <;> simp [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, s0, write, mark,
    Calculus.modify, retire, erase, put, rootName, a, b, c, d]

theorem quiet (first : Bool) : Progress.Quiet ((trace first).state 10) := by
  intro name row found
  rw [endpoint_rows] at found
  split at found
  · cases Option.some.inj found
    exact target (state := (trace first).state 10) (by rw [endpoint_rows, if_pos ‹name = rootName first›]) rfl (fun _ => rfl)
  split at found
  · cases Option.some.inj found
    exact target (state := (trace first).state 10) (by rw [endpoint_rows, if_neg ‹name ≠ rootName first›,
      if_pos ‹name = rootName (!first)›]) rfl (fun _ => rfl)
  split at found
  · cases Option.some.inj found
    exact target (state := (trace first).state 10) (by rw [endpoint_rows, if_neg ‹name ≠ rootName first›,
      if_neg ‹name ≠ rootName (!first)›, if_pos ‹name = 3›]) rfl (fun _ => rfl)
  · cases found

theorem total (first : Bool) : SupportAtQuiescence.TotalProvision ((trace first).state 10) := by
  intro name row found _ key
  rw [endpoint_rows] at found
  split at found
  · cases Option.some.inj found
    simp [activeRoot, fresh, root]
  split at found
  · cases Option.some.inj found
    simp [activeRoot, fresh, root]
  split at found
  · cases Option.some.inj found
    cases first <;> cases key <;> simp [activeChild, child, fresh]
  · cases found

private def supplies (state : R) (name : Nat) (key : Bool) : Bool :=
  match state name with
  | none => true
  | some row =>
    match row.phase with
    | .active .. => (row.table key).isSome == row.component.provides key
    | _ => true

theorem total_at_every_cut (first : Bool) {cut : Nat} (bounded : cut ≤ 10) :
    SupportAtQuiescence.TotalProvision ((trace first).state cut) := by
  rcases Nat.eq_or_lt_of_le bounded with rfl | before
  · exact total first
  intro name row found available key
  by_cases inRange : name < 4
  · have checks :
        (List.range 10).all (fun time =>
          (List.range 4).all (fun owner => supplies (states first time) owner key)) = true := by
      cases first <;> cases key <;> decide
    have atCut := List.all_eq_true.mp checks cut (List.mem_range.mpr before)
    have atOwner := List.all_eq_true.mp atCut name (List.mem_range.mpr inRange)
    change states first cut name = some row at found
    unfold supplies at atOwner
    rw [found] at atOwner
    cases h : row.phase <;> simp_all [Phase.available]
    cases slot : row.table key <;> cases provided : row.component.provides key <;> simp_all
  · have cuts : cut = 0 ∨ cut = 1 ∨ cut = 2 ∨ cut = 3 ∨ cut = 4 ∨
        cut = 5 ∨ cut = 6 ∨ cut = 7 ∨ cut = 8 ∨ cut = 9 := by omega
    have a : name ≠ 0 := by omega
    have b : name ≠ 1 := by omega
    have c : name ≠ 2 := by omega
    have d : name ≠ 3 := by omega
    change states first cut name = some row at found
    rcases cuts with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      cases first <;>
      simp [states, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, mark, Calculus.modify, erase,
        retire, put, rootName, a, b, c, d] at found

/-- All instructions ignore their outcome, including the two allocation heads. -/
theorem renamed_program (names : Renaming.Permutation Nat) : Renaming.program names program = program := by
  funext code
  cases code <;> apply congrArg (fun next => Stages.Instruction.mk _ next) <;>
    funext outcome <;> cases outcome <;> rfl

theorem open_only (first : Bool) : ¬ Nonempty (ClosedEpisode (trace first)) := by
  rintro ⟨closed⟩
  obtain ⟨unload, _⟩ := unload_boundary (trace first) closed.interval
  change events first closed.closed = .lifecycle .unload closed.name at unload
  have bound := closed.interval.bounded
  have cuts : closed.closed = 0 ∨ closed.closed = 1 ∨ closed.closed = 2 ∨
      closed.closed = 3 ∨ closed.closed = 4 ∨ closed.closed = 5 ∨ closed.closed = 6 ∨
      closed.closed = 7 ∨ closed.closed = 8 ∨ closed.closed = 9 := by omega
  rcases cuts with cut | cut | cut | cut | cut | cut | cut | cut | cut | cut <;>
    simp [events, cut] at unload

theorem opening_order (first : Bool) {provider actor : Nat}
    (edge : SupportUniqueness.ActivePredecessor ((trace first).state 10) provider actor) :
    openingRanks (trace first) 10 provider < openingRanks (trace first) 10 actor :=
  (trace first).opening_ranks_support (open_only first) (quiet first) (total first) edge

theorem root_commands (first : Bool) :
    originalRoots (trace first) = [.insert 0 (root false), .insert 1 (root true)] := by
  cases first <;> rfl

/-- Both examples are already normal for the stage-ordering repair.
In particular, stage normalization alone does not identify the endpoints. -/
theorem stage_normal (first : Bool) :
    StageOrderNormal (trace first) (openingRanks (trace first) 10) := by
  intro cut bounded move
  have cuts : cut = 0 ∨ cut = 1 ∨ cut = 2 ∨ cut = 3 ∨ cut = 4 ∨
      cut = 5 ∨ cut = 6 ∨ cut = 7 ∨ cut = 8 := by omega
  have label (time : Nat) : (trace first).event time = events first time := rfl
  have state (time : Nat) : (trace first).state time = states first time := rfl
  rcases cuts with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    cases move <;>
    simp only [label, state, Nat.reduceAdd, events, Event.command.injEq, Event.lifecycle.injEq, reduceCtorEq] at *
  all_goals
    simp_all [commandRoots, rootAt]
  all_goals
    subst_vars
  · contradiction
  · rename_i notChild
    exact notChild (by cases first <;> rfl)
  · rename_i notChild _
    exact notChild (by cases first <;> rfl)
  · rename_i earlier firstActor secondActor
    obtain ⟨_, rfl⟩ := firstActor
    obtain ⟨_, rfl⟩ := secondActor
    exact (show ¬ openingRanks (trace first) 10 3 < openingRanks (trace first) 10 (rootName (!first)) by
      cases first <;> decide) earlier

/-- The birth at the retirement cut denotes different children in the two
histories. Its stamp is the same, but the stamped creation has a different
parent and a different component payload. -/
theorem retirement_at_actual_birth (first : Bool) :
    ((trace first).notes 4).1 2 = some 4 ∧
    (trace first).event 3 = .lifecycle .finish (rootName first) ∧
    (trace first).event 4 = .command (.retire 2) ∧
    ((trace first).state 4 2).map (fun row => (row.parent, row.component)) =
      some (some (rootName first), child first) := by
  obtain ⟨vacant, entered, command, _⟩ := draws_and_command_target first
  refine ⟨?_, rfl, command, ?_⟩
  · rw [(trace first).notes_eq 4 (by decide)]
    apply Incarnation.birthAt_of_created vacant
    change (trace first).state 4 2 ≠ none
    rw [entered]
    exact Option.noConfusion
  · rw [entered]
    rfl

/-- A name bijection preserves component payloads. It cannot make the
two actual targets of the identical O-Retire command agree. -/
theorem different_retirement_targets (names : Renaming.Permutation Nat) :
    ((trace true).state 4 2).map (Renaming.fiber names) ≠ (trace false).state 4 2 := by
  intro same
  have declaration := congrArg (Option.map fun row : F => row.component.provides false) same
  change some false = some true at declaration
  cases declaration

private theorem false_present : StageRecovery.tableAt ((trace true).state 10) 3 false = some (value false) := rfl

private theorem false_absent (name : Nat) : StageRecovery.tableAt ((trace false).state 10) name false = none := by
  unfold StageRecovery.tableAt
  rw [endpoint_rows]
  split
  · rfl
  split
  · rfl
  split <;> rfl

private theorem renamed_table (names : Renaming.Permutation Nat) (state : R) (name : Nat) (key : Bool) :
    StageRecovery.tableAt (Renaming.registry names state) (names.toFun name) key =
      StageRecovery.tableAt state name key := by
  unfold StageRecovery.tableAt
  rw [Renaming.registry_at]
  cases state name <;> rfl

/-- The two endpoints disagree even on the paper's owner-free union-table
observation, for every value setoid and after arbitrary renamings and permitted
vestige erasures on either side. -/
theorem distinct_observations (observe : Bool → Setoid V) (leftNames rightNames : Renaming.Permutation Nat)
    {left right : R} (leftErased : VestigeErasures ((trace true).state 10) left)
    (rightErased : VestigeErasures ((trace false).state 10) right) :
    ¬ PaperStateObservation.TablesRelatedAt observe (fun _ => True)
      (Renaming.registry leftNames left) (Renaming.registry rightNames right) := by
  intro related
  have bound : StageRecovery.tableAt (Renaming.registry leftNames left) (leftNames.toFun 3) false =
      some (value false) := by
    rw [renamed_table, leftErased.table_at, false_present]
  obtain ⟨name, other, found, _⟩ := (related false trivial).1 _ _ bound
  obtain ⟨original, rfl⟩ := rightNames.surjective name
  rw [renamed_table, rightErased.table_at, false_absent] at found
  cases found

theorem distinct_paper_endpoints (sem : PaperStateObservation.Semantics Nat Bool V Code PUnit)
    (leftNames rightNames : Renaming.Permutation Nat)
    {left right : R} (leftErased : VestigeErasures ((trace true).state 10) left)
    (rightErased : VestigeErasures ((trace false).state 10) right) :
    ¬ PaperStateObservation.Related sem
      (Renaming.registry leftNames left) (Renaming.registry rightNames right) :=
  fun related => distinct_observations sem.keyObservation leftNames rightNames leftErased rightErased related.1

end Cordis.Repairs.ChildCommandConfluence
