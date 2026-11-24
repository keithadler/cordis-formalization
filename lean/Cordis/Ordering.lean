import Cordis.Stages

/-!
Retained-provider ordering for the full iterator calculus (Theorems 70–71).
The invariant includes captured-inverse provenance: only a fiber's own provision
inverse can remove a binding. Operations keep the binding and change its value.
-/
namespace Cordis.Ordering
open Calculus Stages
universe u
variable {Name Key Value Code Error : Type u}
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
variable [DecidableEq Name] [DecidableEq Key]
set_option linter.unusedSectionVars false

def Retained : Phase Name Key Code (Inverse Name Key Value) → Prop
  | .active _ _ | .unloading _ _ => True
  | _ => False

def Demand (r : R) (consumer provider : Name) (key : Key) : Prop :=
  ∃ fiber view, r consumer = some fiber ∧ fiber.component.requires key = true ∧
    fiber.phase.committed = some view ∧ view key = provider

def Supply (r : R) (provider : Name) (key : Key) : Prop :=
  ∃ fiber, r provider = some fiber ∧ Retained fiber.phase ∧ fiber.table key ≠ none

def Supported (r : R) : Prop :=
  ∀ consumer provider key, Demand r consumer provider key →
    consumer ≠ provider ∧ Supply r provider key

def OwnInverse (actor : Name) : Inverse Name Key Value → Prop
  | .restrict owner _ => owner = actor
  | _ => True

def LocalAccumulators (r : R) : Prop :=
  ∀ name fiber, r name = some fiber →
    ∀ inverse ∈ fiber.phase.accumulator, OwnInverse name inverse

theorem demand_relied (r : R) (consumer provider : Name) (key : Key)
    (demand : Demand r consumer provider key) (different : consumer ≠ provider) :
    Relied r provider := by
  obtain ⟨fiber, view, present, required, committed, names⟩ := demand
  exact ⟨consumer, different, by simp only [present, committed]; exact ⟨key, required, names⟩⟩

theorem supported_empty : Supported (fun _ => none : R) := by
  intro c p k ⟨f, v, impossible, _⟩
  contradiction

theorem local_empty : LocalAccumulators (fun _ => none : R) := by
  intro n f impossible
  contradiction

theorem supported_transfer {r s : R} (old : Supported r)
    (demands : ∀ c p k, Demand s c p k → Demand r c p k)
    (supplies : ∀ p k, Supply r p k → Supply s p k) : Supported s := by
  intro c p k h
  have ⟨hne, hs⟩ := old c p k (demands c p k h)
  exact ⟨hne, supplies p k hs⟩

/-- Table/flag changes that preserve declarations and phase preserve demands. -/
theorem demand_modify_iff (r : R) (actor consumer provider : Name) (key : Key)
    (change : F → F)
    (decl : ∀ f, (change f).component.requires = f.component.requires)
    (view : ∀ f, (change f).phase.committed = f.phase.committed) :
    Demand (Calculus.modify r actor change) consumer provider key ↔ Demand r consumer provider key := by
  by_cases eq : consumer = actor
  · subst consumer
    cases present : r actor <;> simp [Demand, Calculus.modify, present, decl, view]
  · simp [Demand, Calculus.modify, eq]

theorem supply_modify (r : R) (actor provider : Name) (key : Key) (change : F → F)
    (retained : ∀ f, Retained f.phase → Retained (change f).phase)
    (bound : ∀ f k, f.table k ≠ none → (change f).table k ≠ none)
    (supply : Supply r provider key) : Supply (Calculus.modify r actor change) provider key := by
  obtain ⟨fiber, present, phase, binding⟩ := supply
  by_cases eq : provider = actor
  · subst provider
    exact ⟨change fiber, by simp [Calculus.modify, present], retained fiber phase, bound fiber key binding⟩
  · exact ⟨fiber, by simp [Calculus.modify, eq, present], phase, binding⟩

theorem modify_supported (r : R) (actor : Name) (change : F → F) (old : Supported r)
    (decl : ∀ f, (change f).component.requires = f.component.requires)
    (view : ∀ f, (change f).phase.committed = f.phase.committed)
    (retained : ∀ f, Retained f.phase → Retained (change f).phase)
    (bound : ∀ f k, f.table k ≠ none → (change f).table k ≠ none) :
    Supported (Calculus.modify r actor change) :=
  supported_transfer old
    (fun c p k => (demand_modify_iff r actor c p k change decl view).mp)
    (fun p k => supply_modify r actor p k change retained bound)

theorem modify_local (r : R) (actor : Name) (change : F → F) (old : LocalAccumulators r)
    (acc : ∀ f, (change f).phase.accumulator = f.phase.accumulator) :
    LocalAccumulators (Calculus.modify r actor change) := by
  intro name fiber present inverse member
  by_cases eq : name = actor
  · subst name
    cases h : r actor with
    | none => simp [Calculus.modify, h] at present
    | some original =>
      have same : change original = fiber := by simpa [Calculus.modify, h] using present
      subst fiber
      exact old actor original h inverse (by simpa [acc] using member)
  · exact old name fiber (by simpa [Calculus.modify, eq] using present) inverse member

theorem write_demand_iff (r : R) (actor consumer provider : Name) (key changed : Key)
    (value : Option Value) :
    Demand (write r actor changed value) consumer provider key ↔ Demand r consumer provider key :=
  demand_modify_iff r actor consumer provider key _ (fun _ => rfl) (fun _ => rfl)

theorem write_some_supported (r : R) (actor : Name) (key : Key) (value : Value)
    (old : Supported r) : Supported (write r actor key (some value)) := by
  unfold write
  refine modify_supported r actor _ old (fun _ => rfl) (fun _ => rfl) (fun _ h => h) ?_
  intro f k bound
  by_cases eq : k = key <;> simp [eq, bound]

theorem write_local (r : R) (actor : Name) (key : Key) (value : Option Value)
    (old : LocalAccumulators r) : LocalAccumulators (write r actor key value) :=
  modify_local r actor _ old (fun _ => rfl)

theorem retire_supported (r : R) (actor : Name) (old : Supported r) :
    Supported (Calculus.retire r actor) :=
  modify_supported r actor _ old (fun _ => rfl) (fun _ => rfl) (fun _ h => h) (fun _ _ h => h)

theorem retire_local (r : R) (actor : Name) (old : LocalAccumulators r) :
    LocalAccumulators (Calculus.retire r actor) := modify_local r actor _ old (fun _ => rfl)

theorem insert_supported (r : R) (actor : Name) (component : Component Key Code)
    (parent : Option Name) (absent : r actor = none) (old : Supported r) :
    Supported (put r actor (fresh component parent)) := by
  intro c p k demand
  have cdiff : c ≠ actor := by
    intro eq
    subst c
    obtain ⟨f, v, present, _, committed, _⟩ := demand
    have same : fresh component parent = f := by simpa using present
    subst f
    cases committed
  have prior : Demand r c p k := by simpa [Demand, put, cdiff] using demand
  obtain ⟨distinct, provider, present, retained, bound⟩ := old c p k prior
  have pdiff : p ≠ actor := by
    intro eq
    subst p
    simp [absent] at present
  exact ⟨distinct, provider, by simp [put, pdiff, present], retained, bound⟩

theorem insert_local (r : R) (actor : Name) (component : Component Key Code)
    (parent : Option Name) (old : LocalAccumulators r) :
    LocalAccumulators (put r actor (fresh component parent)) := by
  intro name fiber present inverse member
  by_cases eq : name = actor
  · subst name
    have same : fresh component parent = fiber := by simpa using present
    subst fiber
    cases member
  · exact old name fiber (by simpa [put, eq] using present) inverse member

theorem land_supported (program : Code → Instruction Name Key Value Code Error)
    {actor : Name} {code : Code} {r s : R} {inverse : Inverse Name Key Value} {next : Option Code}
    (landing : Land program actor code r s inverse next) (old : Supported r) : Supported s := by
  cases landing with
  | unit => exact old
  | provide r name code fiber key value _ _ _ _ => exact write_some_supported r actor key value old
  | operate r name code key run owner before after inverse result _ _ _ =>
    exact write_some_supported r owner key after old
  | instantiate r name code component child _ allowed =>
    exact insert_supported r child component (some actor) allowed.1 old

theorem land_local (program : Code → Instruction Name Key Value Code Error)
    {actor : Name} {code : Code} {r s : R} {inverse : Inverse Name Key Value} {next : Option Code}
    (landing : Land program actor code r s inverse next) (old : LocalAccumulators r) :
    LocalAccumulators s ∧ OwnInverse actor inverse := by
  cases landing with
  | unit => exact ⟨old, trivial⟩
  | provide r name code fiber key value _ _ _ _ => exact ⟨write_local r actor key _ old, rfl⟩
  | operate r name code key run owner before after inverse result _ _ _ =>
    exact ⟨write_local r owner key _ old, trivial⟩
  | instantiate r name code component child _ _ => exact ⟨insert_local r child component _ old, trivial⟩

theorem supply_mark (r : R) (actor provider : Name) (fiber : F) (phase)
    (present : r actor = some fiber) (retained : Retained fiber.phase → Retained phase)
    (key : Key) (supply : Supply r provider key) : Supply (mark r actor phase) provider key := by
  obtain ⟨entry, hp, hr, hb⟩ := supply
  by_cases eq : provider = actor
  · subst provider
    have same : entry = fiber := Option.some.inj (hp.symm.trans present)
    subst entry
    exact ⟨{ fiber with phase := phase }, by simp [mark, Calculus.modify, present], retained hr, hb⟩
  · exact ⟨entry, by simp [mark, Calculus.modify, eq, hp], hr, hb⟩

theorem mark_with_supported_view (r : R) (actor : Name) (fiber : F) (phase)
    (present : r actor = some fiber) (old : Supported r)
    (good : ∀ view key, phase.committed = some view → fiber.component.requires key = true →
      actor ≠ view key ∧ Supply r (view key) key)
    (retained : Retained fiber.phase → Retained phase) : Supported (mark r actor phase) := by
  intro c p k ⟨entry, view, hp, required, committed, names⟩
  have before : c ≠ p ∧ Supply r p k := by
    by_cases eq : c = actor
    · subst c
      have same : { fiber with phase := phase } = entry := by
        simpa [mark, Calculus.modify, present] using hp
      subst entry
      simpa [names] using good view k committed required
    · exact old c p k ⟨entry, view, by simpa [mark, Calculus.modify, eq] using hp,
        required, committed, names⟩
  exact ⟨before.1, supply_mark r actor p fiber phase present retained k before.2⟩

theorem mark_same_view_supported (r : R) (actor : Name) (fiber : F) (phase)
    (present : r actor = some fiber) (old : Supported r)
    (committed : phase.committed = fiber.phase.committed)
    (retained : Retained fiber.phase → Retained phase) : Supported (mark r actor phase) := by
  apply mark_with_supported_view r actor fiber phase present old _ retained
  intro view key hp hr
  exact old actor (view key) key ⟨fiber, view, present, hr, committed.symm.trans hp, rfl⟩

theorem begin_supported (r : R) (actor : Name) (fiber : F) (view : View Name Key)
    (present : r actor = some fiber) (inactive : fiber.phase = .inactive)
    (old : Supported r) (target : Target r actor view) :
    Supported (mark r actor (.reloading fiber.component.entry [] view)) := by
  apply mark_with_supported_view r actor fiber _ present old
  · intro selected key hp required
    have eq : selected = view := Option.some.inj hp.symm
    subst selected
    have ht := target
    simp only [Target, present] at ht
    have available := ht.2 key required
    cases provider : r (view key) with
    | none => simp [provider] at available
    | some entry =>
      have facts : entry.phase.available ∧ entry.table key ≠ none := by simpa [provider] using available
      have different : actor ≠ view key := by
        intro same
        rw [← same] at provider
        have ep : entry = fiber := Option.some.inj (provider.symm.trans present)
        subst entry
        simp [inactive, Phase.available] at facts
      refine ⟨different, entry, provider, ?_, facts.2⟩
      cases h : entry.phase <;> simp [h, Phase.available, Retained] at facts ⊢
  · simp [inactive, Retained]

theorem mark_local (r : R) (actor : Name) (phase) (old : LocalAccumulators r)
    (own : ∀ inverse ∈ phase.accumulator, OwnInverse actor inverse) :
    LocalAccumulators (mark r actor phase) := by
  intro name fiber present inverse member
  by_cases eq : name = actor
  · subst name
    cases h : r actor with
    | none => simp [mark, Calculus.modify, h] at present
    | some original =>
      have same : { original with phase := phase } = fiber := by
        simpa [mark, Calculus.modify, h] using present
      subst fiber
      exact own inverse member
  · exact old name fiber (by simpa [mark, Calculus.modify, eq] using present) inverse member

/-- A stage preserves all already installed fibers' declarations and phase. -/
theorem land_existing_control (program : Code → Instruction Name Key Value Code Error)
    {actor : Name} {code : Code} {r s : R} {inverse : Inverse Name Key Value} {next : Option Code}
    (landing : Land program actor code r s inverse next) (name : Name) (fiber : F)
    (present : r name = some fiber) :
    ∃ entry, s name = some entry ∧ entry.component = fiber.component ∧ entry.phase = fiber.phase := by
  cases landing with
  | unit => exact ⟨fiber, present, rfl, rfl⟩
  | provide r n code f key value _ _ _ _ =>
    by_cases eq : name = actor
    · subst name
      exact ⟨{ fiber with table := fun other => if other = key then some value else fiber.table other },
        by simp [write, Calculus.modify, present], rfl, rfl⟩
    · exact ⟨fiber, by simp [write, Calculus.modify, eq, present], rfl, rfl⟩
  | operate r n code key run owner before after inverse result _ _ _ =>
    by_cases eq : name = owner
    · subst name
      exact ⟨{ fiber with table := fun other => if other = key then some after else fiber.table other },
        by simp [write, Calculus.modify, present], rfl, rfl⟩
    · exact ⟨fiber, by simp [write, Calculus.modify, eq, present], rfl, rfl⟩
  | instantiate r n code component child _ allowed =>
    have different : name ≠ child := by
      intro eq
      subst name
      simp [allowed.1] at present
    exact ⟨fiber, by simp [put, different, present], rfl, rfl⟩

theorem relied_iff_demand (r : R) (actor : Name) :
    Relied r actor ↔ ∃ consumer key, consumer ≠ actor ∧ Demand r consumer actor key := by
  constructor
  · rintro ⟨consumer, different, hr⟩
    cases present : r consumer with
    | none => simp [present] at hr
    | some fiber =>
      cases committed : fiber.phase.committed with
      | none => simp [present, committed] at hr
      | some view =>
        obtain ⟨key, required, names⟩ := (by simpa [present, committed] using hr :
          ∃ key, fiber.component.requires key ∧ view key = actor)
        exact ⟨consumer, key, different, fiber, view, present, required, committed, names⟩
  · rintro ⟨consumer, key, different, demand⟩
    exact demand_relied r consumer actor key demand different

theorem undo_demand_iff (r : R) (inverse : Inverse Name Key Value)
    (consumer provider : Name) (key : Key) :
    Demand (Stages.undo inverse r) consumer provider key ↔ Demand r consumer provider key := by
  cases inverse with
  | unit => rfl
  | restrict name changed => exact write_demand_iff r name consumer provider key changed none
  | operate name changed inverse =>
    exact demand_modify_iff r name consumer provider key _ (fun _ => rfl) (fun _ => rfl)
  | retire name => exact demand_modify_iff r name consumer provider key _ (fun _ => rfl) (fun _ => rfl)

theorem undo_not_relied (r : R) (inverse : Inverse Name Key Value) (actor : Name)
    (free : ¬ Relied r actor) : ¬ Relied (Stages.undo inverse r) actor := by
  intro relied
  obtain ⟨consumer, key, different, demand⟩ := (relied_iff_demand _ _).mp relied
  exact free (demand_relied r consumer actor key ((undo_demand_iff r inverse consumer actor key).mp demand) different)

theorem undo_local (r : R) (inverse : Inverse Name Key Value) (old : LocalAccumulators r) :
    LocalAccumulators (Stages.undo inverse r) := by
  cases inverse with
  | unit => exact old
  | restrict name key => exact write_local r name key none old
  | operate name key inverse => exact modify_local r name _ old (fun _ => rfl)
  | retire name => exact retire_local r name old

/-- Captured operation inverses preserve binding presence. A provision inverse
can remove only the actor's own binding, after all other consumers have left. -/
theorem undo_supported (r : R) (actor : Name) (inverse : Inverse Name Key Value)
    (own : OwnInverse actor inverse) (free : ¬ Relied r actor) (old : Supported r) :
    Supported (Stages.undo inverse r) := by
  cases inverse with
  | unit => exact old
  | restrict owner changed =>
    have eq : owner = actor := own
    subst owner
    intro consumer provider key demand
    have prior := (write_demand_iff r actor consumer provider key changed none).mp demand
    obtain ⟨different, entry, present, retained, bound⟩ := old consumer provider key prior
    have pdiff : provider ≠ actor := by
      intro eq
      subst provider
      exact free (demand_relied r consumer actor key prior different)
    exact ⟨different, entry, by simp [Stages.undo, write, Calculus.modify, pdiff, present], retained, bound⟩
  | operate owner changed inverse =>
    unfold Stages.undo
    refine modify_supported r owner _ old (fun _ => rfl) (fun _ => rfl) (fun _ h => h) ?_
    intro f k bound
    by_cases eq : k = changed
    · subst k
      cases h : f.table changed <;> simp [h] at bound ⊢
    · simpa [eq] using bound
  | retire child => exact retire_supported r child old

theorem discharge_invariants (r : R) (actor : Name) (accumulator : List (Inverse Name Key Value))
    (own : ∀ inverse ∈ accumulator, OwnInverse actor inverse)
    (free : ¬ Relied r actor) (supported : Supported r) (localAcc : LocalAccumulators r) :
    Supported (discharge Stages.undo accumulator r) ∧
    LocalAccumulators (discharge Stages.undo accumulator r) ∧
    ¬ Relied (discharge Stages.undo accumulator r) actor := by
  induction accumulator generalizing r with
  | nil => exact ⟨supported, localAcc, free⟩
  | cons inverse rest ih =>
    exact ih (Stages.undo inverse r) (fun inv mem => own inv (List.mem_cons_of_mem inverse mem))
      (undo_not_relied r inverse actor free)
      (undo_supported r actor inverse (own inverse (List.mem_cons_self)) free supported)
      (undo_local r inverse localAcc)

theorem mark_inactive_supported (r : R) (actor : Name)
    (free : ¬ Relied r actor) (old : Supported r) : Supported (mark r actor .inactive) := by
  intro consumer provider key ⟨fiber, view, present, required, committed, names⟩
  have cdiff : consumer ≠ actor := by
    intro eq
    subst consumer
    cases h : r actor with
    | none => simp [mark, Calculus.modify, h] at present
    | some entry =>
      have same : { entry with phase := .inactive } = fiber := by
        simpa [mark, Calculus.modify, h] using present
      subst fiber
      cases committed
  have prior : Demand r consumer provider key :=
    ⟨fiber, view, by simpa [mark, Calculus.modify, cdiff] using present, required, committed, names⟩
  obtain ⟨different, entry, installed, retained, bound⟩ := old consumer provider key prior
  have pdiff : provider ≠ actor := by
    intro eq
    rw [eq] at prior different
    exact free (demand_relied r consumer actor key prior different)
  exact ⟨different, entry, by simp [mark, Calculus.modify, pdiff, installed], retained, bound⟩

theorem erase_supported (r : R) (actor : Name) (fiber : F)
    (present : r actor = some fiber) (inactive : fiber.phase = .inactive)
    (old : Supported r) : Supported (erase r actor) := by
  intro consumer provider key ⟨entry, view, installed, required, committed, names⟩
  have cdiff : consumer ≠ actor := by intro eq; simp [erase, eq] at installed
  have prior : Demand r consumer provider key :=
    ⟨entry, view, by simpa [erase, cdiff] using installed, required, committed, names⟩
  obtain ⟨different, pentry, ppresent, retained, bound⟩ := old consumer provider key prior
  have pdiff : provider ≠ actor := by
    intro eq
    rw [eq] at ppresent
    have same : pentry = fiber := Option.some.inj (ppresent.symm.trans present)
    subst pentry
    simp [inactive, Retained] at retained
  exact ⟨different, pentry, by simp [erase, pdiff, ppresent], retained, bound⟩

theorem erase_local (r : R) (actor : Name) (old : LocalAccumulators r) :
    LocalAccumulators (erase r actor) := by
  intro name fiber present
  have different : name ≠ actor := by intro eq; simp [erase, eq] at present
  exact old name fiber (by simpa [erase, different] using present)

def Invariant (r : R) : Prop := Supported r ∧ LocalAccumulators r

theorem reloading_mark (r : R) (actor : Name) (fiber : F) (code)
    (accumulator : List (Inverse Name Key Value)) (view : View Name Key) (phase)
    (present : r actor = some fiber) (reloading : fiber.phase = .reloading code accumulator view)
    (old : Invariant r) (sameView : phase.committed = some view)
    (own : ∀ inverse ∈ phase.accumulator, OwnInverse actor inverse) :
    Invariant (mark r actor phase) := by
  constructor
  · apply mark_same_view_supported r actor fiber phase present old.1
    · simpa [reloading, Phase.committed] using sameView
    · simp [reloading, Retained]
  · exact mark_local r actor phase old.2 own

theorem landing_mark (program : Code → Instruction Name Key Value Code Error)
    {actor : Name} {code : Code} {r s : R} {inverse : Inverse Name Key Value} {next : Option Code}
    (landing : Land program actor code r s inverse next) (fiber : F)
    (accumulator : List (Inverse Name Key Value)) (view : View Name Key) (phase)
    (present : r actor = some fiber) (reloading : fiber.phase = .reloading code accumulator view)
    (old : Invariant r) (sameView : phase.committed = some view)
    (own : ∀ inv ∈ phase.accumulator, OwnInverse actor inv) : Invariant (mark s actor phase) := by
  obtain ⟨entry, installed, _, phaseSame⟩ := land_existing_control program landing actor fiber present
  exact reloading_mark s actor entry code accumulator view phase installed (phaseSame.trans reloading)
    ⟨land_supported program landing old.1, (land_local program landing old.2).1⟩ sameView own

theorem accumulator_of_phase (r : R) (actor : Name) (fiber : F) (phase)
    (present : r actor = some fiber) (same : fiber.phase = phase) (old : LocalAccumulators r) :
    ∀ inverse ∈ phase.accumulator, OwnInverse actor inverse := by
  intro inv member
  exact old actor fiber present inv (by simpa [same] using member)

/-- Every actual stage and all nine rules preserve provider lifetime. The proof
applies the captured inverses during L-Unload; it never replaces them by clearing
a table and does not assume an abstract transition already preserves support. -/
theorem step_invariant (program : Code → Instruction Name Key Value Code Error)
    {r s : R} (step : Step (Land program) Stages.undo r s) (old : Invariant r) : Invariant s := by
  cases step with
  | insert name component parent allowed =>
    exact ⟨insert_supported r name component parent allowed.1 old.1, insert_local r name component parent old.2⟩
  | retire name _ => exact ⟨retire_supported r name old.1, retire_local r name old.2⟩
  | remove name ready =>
    cases present : r name with
    | none => simp [Removable, present] at ready
    | some fiber =>
      have facts := ready
      simp only [Removable, present] at facts
      exact ⟨erase_supported r name fiber present facts.2.1 old.1, erase_local r name old.2⟩
  | begin name fiber view present inactive _ target =>
    exact ⟨begin_supported r name fiber view present inactive old.1 target,
      mark_local r name _ old.2 (by simp [Phase.accumulator])⟩
  | iter s name fiber code accumulator view inverse next present reloading _ landing =>
    apply landing_mark program landing fiber accumulator view _ present reloading old rfl
    intro inv member
    rcases List.mem_cons.mp member with same | prior
    · subst inv
      exact (land_local program landing old.2).2
    · exact accumulator_of_phase r name fiber _ present reloading old.2 inv prior
  | finish s name fiber code accumulator view inverse present reloading _ landing =>
    apply landing_mark program landing fiber accumulator view _ present reloading old rfl
    intro inv member
    rcases List.mem_cons.mp member with same | prior
    · subst inv
      exact (land_local program landing old.2).2
    · exact accumulator_of_phase r name fiber _ present reloading old.2 inv prior
  | divert s name fiber code accumulator view tail present reloading _ alternative =>
    rcases alternative with ⟨same, empty⟩ | ⟨inverse, next, landing, single⟩
    · subst s tail
      apply reloading_mark r name fiber code accumulator view _ present reloading old rfl
      simpa [Phase.accumulator] using accumulator_of_phase r name fiber (.reloading code accumulator view) present reloading old.2
    · subst tail
      apply landing_mark program landing fiber accumulator view _ present reloading old rfl
      intro inv member
      rcases List.mem_cons.mp member with same | prior
      · subst inv
        exact (land_local program landing old.2).2
      · exact accumulator_of_phase r name fiber _ present reloading old.2 inv prior
  | leave name fiber accumulator view present active _ =>
    constructor
    · apply mark_same_view_supported r name fiber _ present old.1
      · simp [active, Phase.committed]
      · simp [Retained]
    · apply mark_local r name _ old.2
      simpa [Phase.accumulator] using accumulator_of_phase r name fiber (.active accumulator view) present active old.2
  | unload name fiber accumulator view present unloading free =>
    have discharged := discharge_invariants r name accumulator
      (accumulator_of_phase r name fiber _ present unloading old.2) free old.1 old.2
    exact ⟨mark_inactive_supported _ name discharged.2.2 discharged.1,
      mark_local _ name _ discharged.2.1 (by simp [Phase.accumulator])⟩

/-- Theorem 70: a committed consumer, including an unloading consumer executing
its cleanup, retains every required provider and its binding. -/
theorem retained_provider (r : R) (consumer : Name) (fiber : F) (view : View Name Key)
    (key : Key) (supported : Supported r) (present : r consumer = some fiber)
    (committed : fiber.phase.committed = some view) (required : fiber.component.requires key = true) :
    consumer ≠ view key ∧ ∃ provider, r (view key) = some provider ∧
      Retained provider.phase ∧ provider.table key ≠ none :=
  supported consumer (view key) key ⟨fiber, view, present, required, committed, rfl⟩

def ViewStable (r s : R) : Prop :=
  ∀ name before after v w, r name = some before → s name = some after →
    before.phase.committed = some v → after.phase.committed = some w → v = w

def ExistingPhases (r s : R) : Prop :=
  ∀ name fiber, r name = some fiber →
    ∃ entry, s name = some entry ∧ entry.phase = fiber.phase

theorem existing_phases_stable {r s : R} (phases : ExistingPhases r s) : ViewStable r s := by
  intro n before after v w hp hq hv hw
  obtain ⟨entry, he, samePhase⟩ := phases n before hp
  have eq : entry = after := Option.some.inj (he.symm.trans hq)
  subst entry
  rw [samePhase, hv] at hw
  exact Option.some.inj hw

theorem existing_phases_trans {r s t : R} (first : ExistingPhases r s) (second : ExistingPhases s t) :
    ExistingPhases r t := by
  intro n f hp
  obtain ⟨g, hg, hgf⟩ := first n f hp
  obtain ⟨h, hh, hhg⟩ := second n g hg
  exact ⟨h, hh, hhg.trans hgf⟩

theorem existing_then_stable {r s t : R} (first : ExistingPhases r s) (second : ViewStable s t) :
    ViewStable r t := by
  intro n before after v w hp hq hv hw
  obtain ⟨entry, he, samePhase⟩ := first n before hp
  exact second n entry after v w he hq (by simpa [samePhase] using hv) hw

theorem modify_existing_phases (r : R) (actor : Name) (change : F → F)
    (phase : ∀ fiber, (change fiber).phase = fiber.phase) : ExistingPhases r (Calculus.modify r actor change) := by
  intro n f hp
  by_cases eq : n = actor
  · subst n
    exact ⟨change f, by simp [Calculus.modify, hp], phase f⟩
  · exact ⟨f, by simp [Calculus.modify, eq, hp], rfl⟩

theorem land_existing_phases (program : Code → Instruction Name Key Value Code Error)
    {actor : Name} {code : Code} {r s : R} {inverse : Inverse Name Key Value} {next : Option Code}
    (landing : Land program actor code r s inverse next) : ExistingPhases r s := by
  intro name fiber present
  obtain ⟨entry, installed, _, phase⟩ := land_existing_control program landing name fiber present
  exact ⟨entry, installed, phase⟩

theorem undo_existing_phases (r : R) (inverse : Inverse Name Key Value) :
    ExistingPhases r (Stages.undo inverse r) := by
  cases inverse with
  | unit => exact fun _ f hp => ⟨f, hp, rfl⟩
  | restrict name key => exact modify_existing_phases r name _ (fun _ => rfl)
  | operate name key inverse => exact modify_existing_phases r name _ (fun _ => rfl)
  | retire name => exact modify_existing_phases r name _ (fun _ => rfl)

theorem discharge_existing_phases (r : R) (accumulator : List (Inverse Name Key Value)) :
    ExistingPhases r (discharge Stages.undo accumulator r) := by
  induction accumulator generalizing r with
  | nil => exact fun _ f hp => ⟨f, hp, rfl⟩
  | cons inverse rest ih => exact existing_phases_trans (undo_existing_phases r inverse) (ih _)

theorem mark_views_stable (r : R) (actor : Name) (fiber : F) (phase)
    (present : r actor = some fiber)
    (compatible : fiber.phase.committed = none ∨ phase.committed = none ∨
      phase.committed = fiber.phase.committed) : ViewStable r (mark r actor phase) := by
  intro name before after v w hp hq hv hw
  by_cases eq : name = actor
  · subst name
    have same : before = fiber := Option.some.inj (hp.symm.trans present)
    subst before
    have sameAfter : { fiber with phase := phase } = after := by
      simpa [mark, Calculus.modify, present] using hq
    subst after
    rcases compatible with empty | empty | same
    · simp [empty] at hv
    · simp [empty] at hw
    · rw [same, hv] at hw
      exact Option.some.inj hw
  · have same : before = after := by
      have ha : r name = some after := by simpa [mark, Calculus.modify, eq] using hq
      exact Option.some.inj (hp.symm.trans ha)
    subst after
    exact Option.some.inj (hv.symm.trans hw)

theorem mark_inactive_views_stable (r : R) (actor : Name) : ViewStable r (mark r actor .inactive) := by
  intro name before after v w hp hq hv hw
  by_cases eq : name = actor
  · subst name
    have same : { before with phase := .inactive } = after := by simpa [mark, Calculus.modify, hp] using hq
    subst after
    cases hw
  · have same : before = after := by
      have ha : r name = some after := by simpa [mark, Calculus.modify, eq] using hq
      exact Option.some.inj (hp.symm.trans ha)
    subst after
    exact Option.some.inj (hv.symm.trans hw)

/-- No lifecycle step retargets an already installed committed view. -/
theorem step_views_stable (program : Code → Instruction Name Key Value Code Error)
    {r s : R} (step : Step (Land program) Stages.undo r s) : ViewStable r s := by
  cases step with
  | insert name component parent allowed =>
    intro n before after v w hp hq hv hw
    have different : n ≠ name := by intro eq; subst n; simp [allowed.1] at hp
    have same : before = after := Option.some.inj (hp.symm.trans (by simpa [put, different] using hq))
    subst after
    exact Option.some.inj (hv.symm.trans hw)
  | retire name _ => exact existing_phases_stable (modify_existing_phases r name _ (fun _ => rfl))
  | remove name _ =>
    intro n before after v w hp hq hv hw
    have different : n ≠ name := by intro eq; simp [erase, eq] at hq
    have same : before = after := Option.some.inj (hp.symm.trans (by simpa [erase, different] using hq))
    subst after
    exact Option.some.inj (hv.symm.trans hw)
  | begin name fiber view present inactive _ _ =>
    exact mark_views_stable r name fiber _ present (Or.inl (by simp [inactive, Phase.committed]))
  | iter s name fiber code accumulator view inverse next present reloading _ landing =>
    apply existing_then_stable (land_existing_phases program landing)
    obtain ⟨entry, installed, _, phase⟩ := land_existing_control program landing name fiber present
    apply mark_views_stable s name entry _ installed
    exact Or.inr (Or.inr (by simp [phase, reloading, Phase.committed]))
  | finish s name fiber code accumulator view inverse present reloading _ landing =>
    apply existing_then_stable (land_existing_phases program landing)
    obtain ⟨entry, installed, _, phase⟩ := land_existing_control program landing name fiber present
    apply mark_views_stable s name entry _ installed
    exact Or.inr (Or.inr (by simp [phase, reloading, Phase.committed]))
  | divert s name fiber code accumulator view tail present reloading _ alternative =>
    rcases alternative with ⟨same, _⟩ | ⟨inverse, next, landing, _⟩
    · subst s
      exact mark_views_stable r name fiber _ present (Or.inr (Or.inr (by simp [reloading, Phase.committed])))
    · apply existing_then_stable (land_existing_phases program landing)
      obtain ⟨entry, installed, _, phase⟩ := land_existing_control program landing name fiber present
      apply mark_views_stable s name entry _ installed
      exact Or.inr (Or.inr (by simp [phase, reloading, Phase.committed]))
  | leave name fiber accumulator view present active _ =>
    exact mark_views_stable r name fiber _ present (Or.inr (Or.inr (by simp [active, Phase.committed])))
  | unload name fiber accumulator view _ _ _ =>
    exact existing_then_stable (discharge_existing_phases r accumulator) (mark_inactive_views_stable _ name)

end Cordis.Ordering
