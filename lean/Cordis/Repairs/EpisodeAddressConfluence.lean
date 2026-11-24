import Cordis.Repairs.GuardedConfluence

/-! The same historical child address can select an expendable child in an
obsolete parent episode and a child of the surviving episode in another
history. Both histories use the same declarations, program and commands. -/
namespace Cordis.Repairs.EpisodeAddressConfluence
open Calculus Stages LegalHistory GuardedHistory GuardedBirthAddresses
open IncarnationReplay (Capture)
open Vestigial (cutNotes eventActor)
open OrchestrationSorting (Command)

inductive Name where
  | parent | provider | child
  deriving DecidableEq
open Name (parent provider child)

inductive Code where
  | spawn | provision (key : Bool)
  deriving DecidableEq

abbrev Values : Bool → Type := fun _ => Nat

def operations : PaperEffectEquations.CoeffectOperations Values where
  Name _ := Empty
  Argument _ operation := nomatch operation
  Outcome _ operation := nomatch operation
  operation _ operation := nomatch operation

abbrev R := TypedRegistry.RawRegistry Name operations Code
abbrev F := TypedRegistry.RawFiber Name operations Code
abbrev V := TypedRegistry.Scalar operations
abbrev Ev := Event Name Bool Code
abbrev I := Inverse Name Bool V

def parentComponent : Component Bool Code := ⟨(! ·), fun _ => false, .spawn⟩
def providerComponent : Component Bool Code := ⟨fun _ => false, (! ·), .provision false⟩
def childComponent : Component Bool Code := ⟨fun _ => false, id, .provision true⟩

def component : Name → Component Bool Code
  | .parent => parentComponent
  | .provider => providerComponent
  | .child => childComponent

def entry : Code → TypedRegistry.Instruction Name operations Code
  | .spawn => ⟨.instantiate childComponent, fun _ => none⟩
  | .provision key => ⟨.provide key 7, fun _ => none⟩

abbrev program := TypedRegistry.encodeProgram entry
def view : View Name Bool := fun _ => provider
def value (key : Bool) : V := TypedCoeffectReplay.pack key 7

private def install (name : Name) : Ev := .command (.insert name (component name))
private def start (name : Name) : Ev := .lifecycle .begin name
private def finish (name : Name) : Ev := .lifecycle .finish name
private def leave (name : Name) : Ev := .lifecycle .leave name
private def unload (name : Name) : Ev := .lifecycle .unload name
private def retireEvent (name : Name) : Ev := .command (.retire name)
private def remove (name : Name) : Ev := .command (.remove name)

def schedule (early : Bool) : List Ev :=
  [install provider, install parent, start provider, finish provider] ++
  (if early then [start parent, finish parent] else []) ++
  [retireEvent provider, leave provider] ++ (if early then [leave parent, unload parent] else []) ++
  [unload provider, remove provider, install provider, start provider, finish provider] ++
  (if early then [] else [start parent, finish parent]) ++ [retireEvent child, remove child] ++
  (if early then [start parent, finish parent, start child, finish child] else [])

def events (early : Bool) (cut : Nat) : Ev := (schedule early)[cut]?.getD (finish parent)

private def token : Name → I
  | .parent => .retire child
  | .provider => .restrict provider false
  | .child => .restrict child true

private def applyEvent (r : R) : Ev → R
  | .command command => command.apply r
  | .lifecycle .begin name => mark r name (.reloading (component name).entry [] view)
  | .lifecycle .finish name =>
    let landed := match name with
      | .parent => put r child (fresh childComponent (some parent))
      | .provider => write r provider false (some (value false))
      | .child => write r child true (some (value true))
    mark landed name (.active [token name] view)
  | .lifecycle .leave name => mark r name (.unloading [token name] view)
  | .lifecycle .unload name => mark (Stages.undo (token name) r) name .inactive
  | _ => r

def states (early : Bool) : Nat → R
  | 0 => fun _ => none
  | cut + 1 => applyEvent (states early cut) (events early cut)

private def notes (early : Bool) := cutNotes (states early) (fun cut => eventActor (events early cut))

private abbrev Valid (early : Bool) (cut : Nat) : Prop :=
  GuardedSuffix.Transition program (notes early cut) (events early cut) (states early cut) (states early (cut + 1))

private theorem can_insert {r : R} {name : Name} {part : Component Bool Code} {above : Option Name}
    (vacant : r name = none) (parentPresent : ∀ name, above = some name → r name ≠ none)
    (disjoint : ∀ name key, match r name with
      | none => True
      | some row => part.provides key = true → row.component.provides key = false) :
    Insertable r name part above := by
  refine ⟨vacant, parentPresent, fun name key => ?_⟩
  have checked := disjoint name key
  cases found : r name with
  | none => trivial
  | some row =>
    rw [found] at checked
    exact fun h bad => Bool.noConfusion ((checked h).symm.trans bad)

private theorem insertion {early : Bool} {cut : Nat} {name : Name}
    (event : events early cut = install name)
    (ready : Insertable (states early cut) name (component name) none) : Valid early cut := by
  unfold Valid
  rw [states, event]
  exact ⟨ready, rfl⟩

private theorem removal {early : Bool} {cut : Nat} {name : Name}
    (event : events early cut = remove name) (ready : Removable (states early cut) name) : Valid early cut := by
  unfold Valid
  rw [states, event]
  exact ⟨ready, rfl⟩

private theorem retiring {early : Bool} {cut : Nat} {name : Name}
    (event : events early cut = retireEvent name) (present : states early cut name ≠ none) : Valid early cut := by
  unfold Valid
  rw [states, event]
  exact ⟨present, rfl⟩

private theorem starts {early : Bool} {cut : Nat} {name : Name} {row : F}
    (event : events early cut = start name) (found : states early cut name = some row) (inactive : row.phase = .inactive)
    (code : row.component.entry = (component name).entry) (ready : Target (states early cut) name view) : Valid early cut := by
  have endpoint : states early (cut + 1) = mark (states early cut) name (.reloading row.component.entry [] view) := by
    rw [states, event, code]
    rfl
  unfold Valid
  rw [event, endpoint]
  exact Labeled.Step.begin _ _ _ view found inactive (fun absent => Option.noConfusion (found.symm.trans absent)) ready

private theorem spawns {early : Bool} {cut : Nat} {row : F}
    (event : events early cut = finish parent) (found : states early cut parent = some row)
    (phase : row.phase = .reloading .spawn [] view) (target : Target (states early cut) parent view)
    (freshChild : Insertable (states early cut) child childComponent (some parent)) : Valid early cut := by
  unfold Valid
  rw [states, event]
  exact Labeled.Step.finish _ _ _ row .spawn [] view (.retire child) found phase target
    (.instantiate _ parent .spawn childComponent child rfl freshChild)

private theorem provides {early : Bool} {cut : Nat} {name : Name} {key : Bool} {row : F}
    (event : events early cut = finish name) (found : states early cut name = some row)
    (phase : row.phase = .reloading (.provision key) [] view) (target : Target (states early cut) name view)
    (declared : row.component.provides key = true) (vacant : row.table key = none)
    (edited : applyEvent (states early cut) (finish name) =
      mark (write (states early cut) name key (some (value key))) name (.active [.restrict name key] view)) : Valid early cut := by
  unfold Valid
  rw [states, event, edited]
  exact Labeled.Step.finish _ _ _ row (.provision key) [] view (.restrict name key) found phase target
    (.provide _ name (.provision key) row key (value key) rfl found declared vacant)

private theorem leaves {early : Bool} {cut : Nat} {name : Name} {row : F}
    (event : events early cut = leave name) (found : states early cut name = some row)
    (phase : row.phase = .active [token name] view) (stale : ¬ Target (states early cut) name view) : Valid early cut := by
  unfold Valid
  rw [states, event]
  exact Labeled.Step.leave _ _ row [token name] view found phase stale

private theorem unloads {early : Bool} {cut : Nat} {name : Name} {row : F} {stamp : Nat}
    (event : events early cut = unload name) (found : states early cut name = some row)
    (phase : row.phase = .unloading [token name] view) (free : ¬ Relied (states early cut) name)
    (saved : (notes early cut).2 name = [⟨token name, stamp⟩])
    (replay : IncarnationReplay.replay (notes early cut).1 [⟨token name, stamp⟩] (states early cut) =
      Stages.undo (token name) (states early cut)) : Valid early cut := by
  unfold Valid
  rw [states, event]
  refine ⟨row, view, found, ?_, free, ?_⟩
  · rw [saved]; exact phase
  · rw [saved, replay]; rfl


private theorem independent_target {r : R} {name : Name} {row : F}
    (found : r name = some row) (live : row.retired = false)
    (independent : ∀ key, row.component.requires key = false) : Target r name view := by
  rw [Target, found]
  exact ⟨live, fun key needed => False.elim (Bool.noConfusion ((independent key).symm.trans needed))⟩

private theorem parent_target {r : R} {row source : F}
    (found : r parent = some row) (live : row.retired = false) (declared : row.component = parentComponent)
    (providerAt : r provider = some source) (available : source.phase.available)
    (bound : source.table false ≠ none) : Target r parent view := by
  rw [Target, found]
  refine ⟨live, ?_⟩
  intro key needed
  rw [declared] at needed
  cases key
  · simpa only [view, providerAt] using And.intro available bound
  · cases needed

private theorem clear_demands {r : R} {supplied : Name}
    (clear : ∀ name, name ≠ supplied → match r name with
      | none => True
      | some row => match row.phase.committed with
        | none => True
        | some selected => ∀ key, row.component.requires key = false ∨ selected key ≠ supplied) :
    ¬ Relied r supplied := by
  rintro ⟨name, different, used⟩
  have ready := clear name different
  cases found : r name <;> simp only [found] at ready used
  rename_i row
  cases view : row.phase.committed <;> simp only [view] at ready used
  obtain ⟨key, required, equals⟩ := used
  rcases ready key with denied | other
  · exact Bool.noConfusion (required.symm.trans denied)
  · exact other equals

private theorem nonparent_ready {r : R} {name : Name} {row : F}
    (found : r name = some row) (live : row.retired = false)
    (declared : row.component = component name) (other : name ≠ parent) : Target r name view := by
  apply independent_target found live
  rw [declared]
  cases name <;> intro key
  · exact False.elim (other rfl)
  · rfl
  · rfl


set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
private theorem transition (early : Bool) (cut : Nat) (bounded : cut < (schedule early).length) : Valid early cut := by
  cases early with
  | false =>
    change cut < 15 at bounded
    have cuts : cut = 0 ∨ cut = 1 ∨ cut = 2 ∨ cut = 3 ∨ cut = 4 ∨ cut = 5 ∨ cut = 6 ∨
        cut = 7 ∨ cut = 8 ∨ cut = 9 ∨ cut = 10 ∨ cut = 11 ∨ cut = 12 ∨ cut = 13 ∨ cut = 14 := by omega
    rcases cuts with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact insertion (name := provider) rfl (can_insert rfl (by intro name absent; cases absent) (by
        intro name key
        cases name <;> cases key <;> first | trivial | (intro h; first | rfl | cases h)))
    · exact insertion (name := parent) rfl (can_insert rfl (by intro name absent; cases absent) (by
        intro name key
        cases name <;> cases key <;> first | trivial | (intro h; first | rfl | cases h)))
    · exact starts (name := provider) rfl rfl rfl rfl (nonparent_ready rfl rfl rfl (by decide))
    · exact provides (name := provider) (key := false) rfl rfl rfl (nonparent_ready rfl rfl rfl (by decide))
        rfl rfl rfl
    · exact retiring (name := provider) rfl (by intro absent; cases absent)
    · exact leaves (name := provider) rfl rfl rfl (fun unavailable => Bool.noConfusion unavailable.1)
    · refine unloads (name := provider) (stamp := 4) rfl rfl rfl (clear_demands ?_) rfl rfl
      intro name different
      cases name <;> first | exact False.elim (different rfl) | trivial | (intro key; exact Or.inl rfl)
    · refine removal (name := provider) rfl ⟨rfl, rfl, (by intro key; cases key <;> rfl), ?_⟩
      intro name
      cases name <;> first | trivial | (intro impossible; cases impossible)
    · exact insertion (name := provider) rfl (can_insert rfl (by intro name absent; cases absent) (by
        intro name key
        cases name <;> cases key <;> first | trivial | (intro h; first | rfl | cases h)))
    · exact starts (name := provider) rfl rfl rfl rfl (nonparent_ready rfl rfl rfl (by decide))
    · exact provides (name := provider) (key := false) rfl rfl rfl (nonparent_ready rfl rfl rfl (by decide))
        rfl rfl rfl
    · exact starts (name := parent) rfl rfl rfl rfl (parent_target rfl rfl rfl rfl trivial Option.noConfusion)
    · exact spawns rfl rfl rfl (parent_target rfl rfl rfl rfl trivial Option.noConfusion)
        (can_insert rfl (by intro name found; cases found; exact Option.noConfusion) (by
          intro name key
          cases name <;> cases key <;> first | trivial | (intro h; first | rfl | cases h)))
    · exact retiring (name := child) rfl (by intro absent; cases absent)
    · refine removal (name := child) rfl ⟨rfl, rfl, fun _ => rfl, ?_⟩
      intro name
      cases name <;> first | trivial | (intro impossible; cases impossible)
  | true =>
    change cut < 21 at bounded
    have cuts : cut = 0 ∨ cut = 1 ∨ cut = 2 ∨ cut = 3 ∨ cut = 4 ∨ cut = 5 ∨ cut = 6 ∨
        cut = 7 ∨ cut = 8 ∨ cut = 9 ∨ cut = 10 ∨ cut = 11 ∨ cut = 12 ∨ cut = 13 ∨
        cut = 14 ∨ cut = 15 ∨ cut = 16 ∨ cut = 17 ∨ cut = 18 ∨ cut = 19 ∨ cut = 20 := by omega
    rcases cuts with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact insertion (name := provider) rfl (can_insert rfl (by intro name absent; cases absent) (by
        intro name key
        cases name <;> cases key <;> first | trivial | (intro h; first | rfl | cases h)))
    · exact insertion (name := parent) rfl (can_insert rfl (by intro name absent; cases absent) (by
        intro name key
        cases name <;> cases key <;> first | trivial | (intro h; first | rfl | cases h)))
    · exact starts (name := provider) rfl rfl rfl rfl (nonparent_ready rfl rfl rfl (by decide))
    · exact provides (name := provider) (key := false) rfl rfl rfl (nonparent_ready rfl rfl rfl (by decide))
        rfl rfl rfl
    · exact starts (name := parent) rfl rfl rfl rfl (parent_target rfl rfl rfl rfl trivial Option.noConfusion)
    · exact spawns rfl rfl rfl (parent_target rfl rfl rfl rfl trivial Option.noConfusion)
        (can_insert rfl (by intro name found; cases found; exact Option.noConfusion) (by
          intro name key
          cases name <;> cases key <;> first | trivial | (intro h; first | rfl | cases h)))
    · exact retiring (name := provider) rfl (by intro absent; cases absent)
    · exact leaves (name := provider) rfl rfl rfl (fun unavailable => Bool.noConfusion unavailable.1)
    · exact leaves (name := parent) rfl rfl rfl (fun unavailable => (unavailable.2 false rfl).1)
    · refine unloads (name := parent) (stamp := 6) rfl rfl rfl (clear_demands ?_) rfl rfl
      intro name different
      cases name <;> first | exact False.elim (different rfl) | trivial | (intro key; exact Or.inl rfl)
    · refine unloads (name := provider) (stamp := 4) rfl rfl rfl (clear_demands ?_) rfl rfl
      intro name different
      cases name <;> first | exact False.elim (different rfl) | trivial | (intro key; exact Or.inl rfl)
    · refine removal (name := provider) rfl ⟨rfl, rfl, (by intro key; cases key <;> rfl), ?_⟩
      intro name
      cases name <;> first | trivial | (intro impossible; cases impossible)
    · exact insertion (name := provider) rfl (can_insert rfl (by intro name absent; cases absent) (by
        intro name key
        cases name <;> cases key <;> first | trivial | (intro h; first | rfl | cases h)))
    · exact starts (name := provider) rfl rfl rfl rfl (nonparent_ready rfl rfl rfl (by decide))
    · exact provides (name := provider) (key := false) rfl rfl rfl (nonparent_ready rfl rfl rfl (by decide))
        rfl rfl rfl
    · exact retiring (name := child) rfl (by intro absent; cases absent)
    · refine removal (name := child) rfl ⟨rfl, rfl, fun _ => rfl, ?_⟩
      intro name
      cases name <;> first | trivial | (intro impossible; cases impossible)
    · exact starts (name := parent) rfl rfl rfl rfl (parent_target rfl rfl rfl rfl trivial Option.noConfusion)
    · exact spawns rfl rfl rfl (parent_target rfl rfl rfl rfl trivial Option.noConfusion)
        (can_insert rfl (by intro name found; cases found; exact Option.noConfusion) (by
          intro name key
          cases name <;> cases key <;> first | trivial | (intro h; first | rfl | cases h)))
    · exact starts (name := child) rfl rfl rfl rfl (nonparent_ready rfl rfl rfl (by decide))
    · exact provides (name := child) (key := true) rfl rfl rfl (nonparent_ready rfl rfl rfl (by decide))
        rfl rfl rfl

def trace (early : Bool) : Trace program (schedule early).length where
  state := states early
  event := events early
  notes := notes early
  start := rfl
  seed := rfl
  step cut bounded := ⟨transition early cut bounded, rfl⟩


def observe (_ : Bool) : Setoid Nat := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩

theorem fixed_child_continuations : GuardedLandingMatching.ChildContinuations program := by
  intro code part action first second
  cases code <;> rfl

private theorem old_provider_address (early : Bool) : Addressed (trace early) 1 (.root 0) :=
  .root (time := 0) (by cases early <;> decide) rfl

private theorem parent_address (early : Bool) : Addressed (trace early) 2 (.root 1) :=
  .root (time := 1) (by cases early <;> decide) rfl

private theorem first_child_early : Addressed (trace true) 6 (.child (.root 1) 0) :=
  .child (time := 5) (name := child) (parentBirth := 2) (by decide) rfl rfl Option.noConfusion rfl (parent_address true)

private theorem first_child_late : Addressed (trace false) 13 (.child (.root 1) 0) :=
  .child (time := 12) (name := child) (parentBirth := 2) (by decide) rfl rfl Option.noConfusion rfl (parent_address false)

theorem second_child_early : Addressed (trace true) 19 (.child (.root 1) 1) :=
  .child (time := 18) (name := child) (parentBirth := 2) (by decide) rfl rfl Option.noConfusion rfl (parent_address true)

private theorem command_on_old_provider (early : Bool) :
    targetAt (trace early) (if early then 6 else 4) provider = some (.root 0, providerComponent) ∧
    targetAt (trace early) (if early then 11 else 7) provider = some (.root 0, providerComponent) := by
  cases early
  · exact ⟨(targetAt_eq_some _).mpr ⟨1, _, rfl, old_provider_address false, rfl, rfl⟩,
      (targetAt_eq_some _).mpr ⟨1, _, rfl, old_provider_address false, rfl, rfl⟩⟩
  · exact ⟨(targetAt_eq_some _).mpr ⟨1, _, rfl, old_provider_address true, rfl, rfl⟩,
      (targetAt_eq_some _).mpr ⟨1, _, rfl, old_provider_address true, rfl, rfl⟩⟩

private theorem command_on_first_child (early : Bool) :
    targetAt (trace early) (if early then 15 else 13) child = some (.child (.root 1) 0, childComponent) ∧
    targetAt (trace early) (if early then 16 else 14) child = some (.child (.root 1) 0, childComponent) := by
  cases early
  · exact ⟨(targetAt_eq_some _).mpr ⟨13, _, rfl, first_child_late, rfl, rfl⟩,
      (targetAt_eq_some _).mpr ⟨13, _, rfl, first_child_late, rfl, rfl⟩⟩
  · exact ⟨(targetAt_eq_some _).mpr ⟨6, _, rfl, first_child_early, rfl, rfl⟩,
      (targetAt_eq_some _).mpr ⟨6, _, rfl, first_child_early, rfl, rfl⟩⟩

def input : List (AddressedCommand Name Bool Code) :=
  [.insert provider providerComponent, .insert parent parentComponent, .retire (.root 0) providerComponent,
    .remove (.root 0) providerComponent, .insert provider providerComponent,
    .retire (.child (.root 1) 0) childComponent, .remove (.child (.root 1) 0) childComponent]

set_option maxRecDepth 2048 in
theorem full_addressed_input (early : Bool) : orchestrationInput (trace early) = input := by
  obtain ⟨retireProvider, removeProvider⟩ := command_on_old_provider early
  obtain ⟨retireChild, removeChild⟩ := command_on_first_child early
  have label (cut : Nat) : (trace early).event cut = events early cut := rfl
  unfold orchestrationInput
  cases early <;> simp only [Bool.false_eq_true, if_false, if_true] at retireProvider removeProvider retireChild removeChild
  · change ([0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] : List Nat).filterMap (commandAt (trace false)) = input
    simp [commandAt, label, events, schedule, install, start, leave, unload, finish, retireEvent, remove, component,
      retireProvider, removeProvider, retireChild, removeChild, input]
  · change ([0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20] : List Nat).filterMap (commandAt (trace true)) = input
    simp [commandAt, label, events, schedule, install, start, leave, unload, finish, retireEvent, remove, component,
      retireProvider, removeProvider, retireChild, removeChild, input]

/-- Equal parent-relative child addresses in the two executions use
different provider incarnations at the landing that creates the child. -/
theorem different_provider_origins :
    Addressed (trace true) 6 (.child (.root 1) 0) ∧ Addressed (trace false) 13 (.child (.root 1) 0) ∧
    ((trace true).notes 5).1 (view false) = some 1 ∧ ((trace false).notes 12).1 (view false) = some 9 ∧
    Addressed (trace true) 1 (.root 0) ∧ Addressed (trace false) 9 (.root 2) :=
  ⟨first_child_early, first_child_late, rfl, rfl, old_provider_address true, .root (time := 8) (by decide) rfl⟩

set_option maxRecDepth 2048 in
theorem quiet (early : Bool) : Progress.Quiet ((trace early).state (schedule early).length) := by
  intro name row present
  cases early <;> cases name
  · change some _ = some row at present
    cases Option.some.inj present
    exact parent_target rfl rfl rfl rfl trivial Option.noConfusion
  · change some _ = some row at present
    cases Option.some.inj present
    exact nonparent_ready rfl rfl rfl (by decide)
  · cases present
  · change some _ = some row at present
    cases Option.some.inj present
    exact parent_target rfl rfl rfl rfl trivial Option.noConfusion
  · change some _ = some row at present
    cases Option.some.inj present
    exact nonparent_ready rfl rfl rfl (by decide)
  · change some _ = some row at present
    cases Option.some.inj present
    exact nonparent_ready rfl rfl rfl (by decide)

/-- The late schedule retires the old provider while its inactive consumer
could start. A quiescent boundary before every command excludes that cut. -/
theorem late_retirement_cut_not_quiet : ¬ Progress.Quiet ((trace false).state 4) := by
  intro settled
  have parentReady : Target ((trace false).state 4) parent view :=
    parent_target rfl rfl rfl rfl trivial Option.noConfusion
  have dormant := settled parent (fresh parentComponent none) rfl
  exact dormant view parentReady

private def totalAt (state : R) (name : Name) (key : Bool) : Bool :=
  match state name with
  | none => true
  | some row =>
    match row.phase with
    | .active .. => (row.table key).isSome == row.component.provides key
    | _ => true

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
theorem total_at_every_cut (early : Bool) (cut : Nat) (bounded : cut ≤ (schedule early).length) :
    SupportAtQuiescence.TotalProvision ((trace early).state cut) := by
  intro name row present available key
  have certified : (List.range ((schedule early).length + 1)).all
      (fun i => ([parent, provider, child] : List Name).all (fun n => totalAt (states early i) n key)) = true := by
    cases early <;> cases key <;> decide
  have member : name ∈ ([parent, provider, child] : List Name) := by cases name <;> decide
  have verified := List.all_eq_true.mp (List.all_eq_true.mp certified cut (List.mem_range.mpr (by omega))) name member
  change states early cut name = some row at present
  unfold totalAt at verified
  rw [present] at verified
  cases kind : row.phase <;> simp_all [Phase.available]
  cases bound : row.table key <;> cases declared : row.component.provides key <;> simp_all

abbrev earlyEnd : R := (trace true).state (schedule true).length
abbrev lateEnd : R := (trace false).state (schedule false).length

theorem early_child_binding : StageRecovery.tableAt earlyEnd child true = some (value true) := rfl

theorem provider_binding (early : Bool) :
    StageRecovery.tableAt ((trace early).state (schedule early).length) provider false = some (value false) := by
  cases early <;> rfl

theorem no_late_binding (name : Name) : StageRecovery.tableAt lateEnd name true = none := by
  cases name <;> rfl

/-- The disagreement is already visible in the union of the coeffect
tables and is independent of the chosen value equivalence. -/
theorem different_tables (observation : Bool → Setoid V) :
    ¬ PaperStateObservation.TablesRelatedAt observation (fun _ => True) earlyEnd lateEnd := by
  intro aligned
  obtain ⟨name, _, found, _⟩ := (aligned true trivial).1 child (value true) early_child_binding
  rw [no_late_binding] at found
  cases found

/-- Matching raw commands and recursive child addresses can still leave
different observed endpoints, even with the same name-insensitive program
and the repaired allowance for renaming and vestige erasures. -/
theorem same_addressed_input_different_endpoints :
    orchestrationInput (trace true) = orchestrationInput (trace false) ∧
    GuardedLandingMatching.ChildContinuations program ∧
    (∀ early, Progress.Quiet ((trace early).state (schedule early).length)) ∧
    (∀ early cut, cut ≤ (schedule early).length → SupportAtQuiescence.TotalProvision ((trace early).state cut)) ∧
    (∀ observation : ∀ key, Setoid (Values key), ¬ GuardedConfluence.EndpointAgreement observation earlyEnd lateEnd) := by
  refine ⟨(full_addressed_input true).trans (full_addressed_input false).symm, fixed_child_continuations, quiet,
    total_at_every_cut, ?_⟩
  intro observation agreement
  exact different_tables _ (GuardedConfluence.EndpointAgreement.paper_tables observation agreement)

theorem same_raw_commands :
    (schedule true).filterMap (fun | .command command => some command | .lifecycle .. => none) =
      (schedule false).filterMap (fun | .command command => some command | .lifecycle .. => none) := rfl

/-- No choices of valid endpoint-preserving open reductions can produce a
shared addressed event order for these two inputs. -/
theorem no_common_addressed_reduction (observation : ∀ key, Setoid (Values key))
    {length : Nat} {left right : Trace program length} {leftPruned rightPruned : R}
    (leftErased : VestigeErasures earlyEnd leftPruned) (rightErased : VestigeErasures lateEnd rightPruned)
    (leftRelated : @StageSimulation.Related Name Bool V Code _ (TypedCoeffectReplay.setoid observation) Eq
      leftPruned (left.state length))
    (rightRelated : @StageSimulation.Related Name Bool V Code _ (TypedCoeffectReplay.setoid observation) Eq
      rightPruned (right.state length))
    (leftOpen : ¬ Nonempty (ClosedEpisode left)) (rightOpen : ¬ Nonempty (ClosedEpisode right))
    (leftQuiet : Progress.Quiet (left.state length)) (rightQuiet : Progress.Quiet (right.state length)) :
    ¬ ∀ cut, cut < length → GuardedAddressSchedule.addressedEventAt left cut = GuardedAddressSchedule.addressedEventAt right cut := by
  intro aligned
  have endpoint := GuardedConfluence.compare_normalized_endpoints_by_addresses observation left right
    leftErased rightErased leftRelated rightRelated fixed_child_continuations leftOpen rightOpen leftQuiet rightQuiet aligned
  exact different_tables _ (GuardedConfluence.EndpointAgreement.paper_tables observation endpoint)


private theorem unload_times {early : Bool} {cut : Nat} {name : Name} (bounded : cut < (schedule early).length)
    (event : events early cut = unload name) :
    if early then (cut = 9 ∧ name = parent) ∨ (cut = 10 ∧ name = provider)
    else cut = 6 ∧ name = provider := by
  have lengthBound : (schedule early).length ≤ 21 := by cases early <;> decide
  have finite : cut < 21 := Nat.lt_of_lt_of_le bounded lengthBound
  have cuts : cut = 0 ∨ cut = 1 ∨ cut = 2 ∨ cut = 3 ∨ cut = 4 ∨ cut = 5 ∨ cut = 6 ∨
      cut = 7 ∨ cut = 8 ∨ cut = 9 ∨ cut = 10 ∨ cut = 11 ∨ cut = 12 ∨ cut = 13 ∨
      cut = 14 ∨ cut = 15 ∨ cut = 16 ∨ cut = 17 ∨ cut = 18 ∨ cut = 19 ∨ cut = 20 := by omega
  cases early <;>
    rcases cuts with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [events, schedule, install, start, finish, leave, unload, retireEvent, remove] at event ⊢
  all_goals exact event.symm

private theorem literal_unload {early : Bool} {cut : Nat} {name : Name} (bounded : cut < (schedule early).length)
    (event : events early cut = unload name) :
    IncarnationReplay.replay (notes early cut).1 ((notes early cut).2 name) (states early cut) =
      discharge Stages.undo (((notes early cut).2 name).map Capture.token) (states early cut) := by
  have whereAt := unload_times bounded event
  cases early
  · obtain ⟨rfl, rfl⟩ := whereAt
    rfl
  · rcases whereAt with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

/-- At every unload in the example, the native inverse word has the same
effect as the incarnation-checked word. These are also native runs. -/
def nativeTrace (early : Bool) : Indexed.Trace program (fun _ => none) (schedule early).length where
  state := (trace early).state
  actor := (trace early).actor
  rule := (trace early).rule
  start := rfl
  step cut bounded := by
    rcases transition_cases ((trace early).step cut bounded).1 with native | ⟨name, event, guarded⟩
    · exact native
    · have literal := literal_unload bounded (show events early cut = unload name from event)
      obtain ⟨row, selected, found, phase, free, endpoint⟩ := guarded
      rw [Trace.rule, Trace.actor, event, eventRule, Lifecycle.rule, eventActor]
      rw [endpoint]
      change Labeled.Step program .unload name (states early cut)
        (mark (IncarnationReplay.replay (notes early cut).1 ((notes early cut).2 name) (states early cut)) name .inactive)
      rw [literal]
      exact .unload _ name row _ selected found phase free


def formerParentEpisode : ClosedEpisode (trace true) where
  name := parent
  opened := 5
  closed := 9
  interval := ⟨by decide, by decide, by decide, installed, rfl, rfl⟩
where
  installed cut (lower : 5 ≤ cut) (upper : cut ≤ 9) : ControlFrame.viewAt ((trace true).state cut) parent ≠ none := by
    have cuts : cut = 5 ∨ cut = 6 ∨ cut = 7 ∨ cut = 8 ∨ cut = 9 := by omega
    rcases cuts with rfl | rfl | rfl | rfl | rfl <;> exact Option.noConfusion

def formerProviderEpisode : ClosedEpisode (trace false) where
  name := provider
  opened := 3
  closed := 6
  interval := ⟨by decide, by decide, by decide, installed, rfl, rfl⟩
where
  installed cut (lower : 3 ≤ cut) (upper : cut ≤ 6) : ControlFrame.viewAt ((trace false).state cut) provider ≠ none := by
    have cuts : cut = 3 ∨ cut = 4 ∨ cut = 5 ∨ cut = 6 := by omega
    rcases cuts with rfl | rfl | rfl | rfl <;> exact Option.noConfusion

private theorem first_maximal (later : ClosedEpisode (trace true)) : ¬ EpisodeEdge formerParentEpisode later := by
  intro edge
  have earlier := episode_edge_earlier edge
  change 5 < later.opened at earlier
  have ordered := later.interval.ordered
  obtain ⟨lastEvent, _⟩ := unload_boundary (trace true) later.interval
  have closes := unload_times later.interval.bounded (show events true later.closed = unload later.name from lastEvent)
  have within : later.closed ≤ 10 := by
    rcases closes with ⟨position, _⟩ | ⟨position, _⟩ <;> omega
  obtain ⟨firstEvent, _⟩ := begin_boundary (trace true) later.interval
  change events true (later.opened - 1) = start later.name at firstEvent
  have cuts : later.opened - 1 = 5 ∨ later.opened - 1 = 6 ∨ later.opened - 1 = 7 ∨
      later.opened - 1 = 8 ∨ later.opened - 1 = 9 := by omega
  rcases cuts with cut | cut | cut | cut | cut <;> rw [cut] at firstEvent <;> cases firstEvent

private theorem second_maximal (later : ClosedEpisode (trace false)) : ¬ EpisodeEdge formerProviderEpisode later := by
  intro edge
  have earlier := episode_edge_earlier edge
  change 3 < later.opened at earlier
  have ordered := later.interval.ordered
  obtain ⟨lastEvent, _⟩ := unload_boundary (trace false) later.interval
  have ⟨closes, _⟩ := unload_times later.interval.bounded (show events false later.closed = unload later.name from lastEvent)
  obtain ⟨firstEvent, _⟩ := begin_boundary (trace false) later.interval
  change events false (later.opened - 1) = start later.name at firstEvent
  have cuts : later.opened - 1 = 3 ∨ later.opened - 1 = 4 ∨ later.opened - 1 = 5 := by omega
  rcases cuts with cut | cut | cut <;> rw [cut] at firstEvent <;> cases firstEvent

theorem early_episode_excision : EpisodeExcised (trace true) formerParentEpisode observe :=
  excise_closed_episode (trace true) formerParentEpisode first_maximal (quiet true) observe
    (fun _ action => nomatch action) (fun _ action => nomatch action) (fun _ action => nomatch action)

theorem late_episode_excision : EpisodeExcised (trace false) formerProviderEpisode observe :=
  excise_closed_episode (trace false) formerProviderEpisode second_maximal (quiet false) observe
    (fun _ action => nomatch action) (fun _ action => nomatch action) (fun _ action => nomatch action)

private def removesChild : Ev → Bool
  | .command (.remove .child) => true
  | _ => false

private def retiresChild : Ev → Bool
  | .command (.retire .child) => true
  | _ => false

/-- Legitimate deletion drops the child command in the early run and
retains it in the late run. Comparing commands that survive deletion
therefore distinguishes this pair of executions. -/
theorem excisions_distinguish_commands :
    ∃ (leftMask rightMask : List Name) (leftEnd rightEnd : R)
      (leftNotes rightNotes : Vestigial.CutNotes Name Bool V),
      GuardedSuffix.ExecWith program (trace true).sourceAt (excisedEvents (trace true) formerParentEpisode leftMask)
        (states true 0) (notes true 0) leftEnd leftNotes (originalRoots (trace true)) ∧
      GuardedSuffix.ExecWith program (trace false).sourceAt (excisedEvents (trace false) formerProviderEpisode rightMask)
        (states false 0) (notes false 0) rightEnd rightNotes (originalRoots (trace false)) ∧
      ((excisedEvents (trace true) formerParentEpisode leftMask).map Prod.snd).any retiresChild = false ∧
      ((excisedEvents (trace true) formerParentEpisode leftMask).map Prod.snd).any removesChild = false ∧
      ((excisedEvents (trace false) formerProviderEpisode rightMask).map Prod.snd).any retiresChild = true ∧
      ((excisedEvents (trace false) formerProviderEpisode rightMask).map Prod.snd).any removesChild = true := by
  obtain ⟨left, after, recorded, unique, leftMember, _, run, _⟩ := early_episode_excision
  obtain ⟨right, other, otherNotes, _, rightMember, _, runOther, _⟩ := late_episode_excision
  have onlyChild (name : Name) : name ∈ left ↔ name = child := by
    rw [leftMember]
    cases name <;> decide
  have noRight (name : Name) : name ∉ right := by
    rw [rightMember]
    cases name <;> decide
  have exactLeft : left = [child] := by
    cases left with
    | nil => exact False.elim (List.not_mem_nil ((onlyChild child).mpr rfl))
    | cons head tail =>
      have name := (onlyChild head).mp List.mem_cons_self
      subst head
      cases tail with
      | nil => rfl
      | cons first rest =>
        have same := (onlyChild first).mp (List.mem_cons_of_mem _ List.mem_cons_self)
        subst first
        exact False.elim ((List.nodup_cons.mp unique).1 List.mem_cons_self)
  have exactRight : right = [] := by
    cases right with
    | nil => rfl
    | cons head _ => exact False.elim (noRight head List.mem_cons_self)
  subst left
  subst right
  exact ⟨[child], [], after, other, recorded, otherNotes, run, runOther, rfl, rfl, rfl, rfl⟩

end Cordis.Repairs.EpisodeAddressConfluence
