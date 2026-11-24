import Cordis.Repairs.GuardedBirthMatching

/-! The registry data used by a landing at a guarded cut. Retain phase and
code, and keep the provider selected for each declared requirement. Saved
words have their own birth-indexed correspondence. -/
namespace Cordis.Repairs.GuardedCutState
open Calculus Stages GuardedHistory

universe u
variable {Name Key Value Code Error : Type u}
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
local notation "S" => Phase Name Key Code (Inverse Name Key Value)
local notation "P" => Renaming.Permutation Name

def requiredView (actor : Name) (required : Key → Bool) (view : View Name Key) : View Name Key :=
  fun key => if required key then view key else actor

def projectPhase (actor : Name) (required : Key → Bool) : S → S
  | .inactive => .inactive
  | .reloading code _ view => .reloading code [] (requiredView actor required view)
  | .active _ view => .active [] (requiredView actor required view)
  | .unloading _ view => .unloading [] (requiredView actor required view)

def projectFiber (actor : Name) (row : F) : F :=
  { row with phase := projectPhase actor row.component.requires row.phase }

def project (state : R) : R :=
  fun name => (state name).map (projectFiber name)

theorem project_present (state : R) (name : Name) : project state name = none ↔ state name = none := by
  simp [project]

theorem project_insertable (state : R) (name : Name) (component : Component Key Code) (parent : Option Name) :
    Insertable (project state) name component parent ↔ Insertable state name component parent := by
  constructor <;> rintro ⟨vacant, parents, others⟩
  · refine ⟨(project_present state name).mp vacant, fun p tag missing => parents p tag ((project_present state p).mpr missing), ?_⟩
    intro other key
    have valid := others other key
    cases row : state other <;> simp [project, projectFiber, row] at valid ⊢ <;> exact valid
  · refine ⟨(project_present state name).mpr vacant, fun p tag missing => parents p tag ((project_present state p).mp missing), ?_⟩
    intro other key
    have valid := others other key
    cases row : state other <;> simp [project, projectFiber, row] at valid ⊢ <;> exact valid

theorem project_removable (state : R) (name : Name) :
    Removable (project state) name ↔ Removable state name := by
  cases found : state name with
  | none => simp [Removable, project, found]
  | some row =>
    have projected : project state name = some (projectFiber name row) := by simp [project, found]
    rw [Removable, Removable, projected, found]
    dsimp only
    have phase : (projectFiber name row).phase = .inactive ↔ row.phase = .inactive := by
      cases kind : row.phase <;> simp [projectFiber, projectPhase, kind]
    constructor <;> rintro ⟨retired, inactive, empty, children⟩
    · refine ⟨retired, phase.mp inactive, empty, ?_⟩
      intro child
      have leaf := children child
      cases present : state child <;> simp [project, projectFiber, present] at leaf ⊢ <;> exact leaf
    · refine ⟨retired, phase.mpr inactive, empty, ?_⟩
      intro child
      have leaf := children child
      cases present : state child <;> simp [project, projectFiber, present] at leaf ⊢ <;> exact leaf

theorem project_modify [DecidableEq Name] (state : R) (name : Name) (edit : F → F)
    (commutes : ∀ row, projectFiber name (edit row) = edit (projectFiber name row)) :
    project (Calculus.modify state name edit) = Calculus.modify (project state) name edit := by
  funext query
  by_cases same : query = name
  · subst query
    simp [project, Calculus.modify, Option.map_map, Function.comp_def, commutes]
  · simp [project, Calculus.modify, same]

theorem project_put [DecidableEq Name] (state : R) (name : Name) (row : F) :
    project (put state name row) = put (project state) name (projectFiber name row) := by
  funext query
  by_cases same : query = name
  · subst query; simp [project, put]
  · simp [project, put, same]

theorem project_erase [DecidableEq Name] (state : R) (name : Name) :
    project (erase state name) = erase (project state) name := by
  funext query
  by_cases same : query = name <;> simp [project, erase, same]

theorem project_mark [DecidableEq Name] (state : R) (name : Name) {row : F}
    (present : state name = some row) (phase : S) :
    project (mark state name phase) =
      mark (project state) name (projectPhase name row.component.requires phase) := by
  funext query
  by_cases same : query = name
  · subst query; simp [project, mark, Calculus.modify, present, projectFiber]
  · simp [project, mark, Calculus.modify, same]

theorem project_retire [DecidableEq Name] (state : R) (name : Name) :
    project (retire state name) = retire (project state) name :=
  project_modify _ _ _ (fun _ => rfl)

theorem project_write [DecidableEq Name] [DecidableEq Key] (state : R) (name : Name) (key : Key)
    (value : Option Value) :
    project (write state name key value) = write (project state) name key value :=
  project_modify _ _ _ (fun _ => rfl)

private theorem chosen_view (p : P) (actor : Name) (required : Key → Bool) (view : View Name Key) :
    Renaming.view p (requiredView actor required view) =
      requiredView (p.toFun actor) required (Renaming.view p view) := by
  funext key
  by_cases demand : required key = true <;> simp [requiredView, Renaming.view, demand]

theorem project_rename (p : P) (state : R) :
    project (Renaming.registry p state) = Renaming.registry p (project state) := by
  funext query
  obtain ⟨name, rfl⟩ := p.surjective query
  rw [project, Renaming.registry_at, Renaming.registry_at]
  cases found : state name with
  | none => simp [project, found]
  | some row =>
    have commute : projectFiber (p.toFun name) (Renaming.fiber p row) = Renaming.fiber p (projectFiber name row) := by
      cases phase : row.phase <;>
        simp [projectFiber, Renaming.fiber, phase, projectPhase, Renaming.phase, chosen_view]
    simpa [project, found] using commute

theorem project_location (state : R) (actor : Name) (key : Key) :
    location (project state) actor key = location state actor key := by
  have tables (name : Name) : ((project state name).bind fun row => row.table key) =
      ((state name).bind fun row => row.table key) := by cases found : state name <;> simp [project, found, projectFiber]
  have route : bindingOwner (project state) actor key = bindingOwner state actor key := by
    cases found : state actor with
    | none => simp [project, bindingOwner, found]
    | some row =>
      by_cases demand : row.component.requires key = true
      · cases phase : row.phase <;>
          simp [project, bindingOwner, found, projectFiber, phase, projectPhase, Phase.committed, requiredView, demand]
      · simp [project, bindingOwner, found, projectFiber, demand]
  simp only [location, route]
  cases bindingOwner state actor key with
  | none => rfl
  | some owner => simp only [Option.bind_some, tables]

theorem project_target (state : R) (actor : Name) (view : View Name Key) :
    Target (project state) actor view ↔ Target state actor view := by
  cases found : state actor with
  | none => simp [project, Target, found]
  | some row =>
    simp only [project, Target, found, Option.map_some, projectFiber]
    constructor <;> intro valid <;> refine ⟨valid.1, fun key needed => ?_⟩ <;>
      have binding := valid.2 key needed <;> cases foundProvider : state (view key) with
    | none => simp [foundProvider] at binding
    | some provider =>
      cases phase : provider.phase <;>
        simp [foundProvider, phase, projectFiber, projectPhase, Phase.available] at binding ⊢ <;>
        exact binding

theorem project_quiet_iff [DecidableEq Name] [DecidableEq Key] (state : R) :
    Progress.Quiet (project state) ↔ Progress.Quiet state := by
  have atRow (name : Name) (row : F) (found : state name = some row) :
      (match (projectFiber name row).phase with
      | .inactive => ∀ view, ¬ Target (project state) name view
      | .active _ view => Target (project state) name view
      | _ => False) ↔
      (match row.phase with
      | .inactive => ∀ view, ¬ Target state name view
      | .active _ view => Target state name view
      | _ => False) := by
    cases phase : row.phase with
    | inactive =>
      simp only [projectFiber, phase, projectPhase]
      exact ⟨fun quiet view target => quiet view ((project_target state name view).mpr target),
        fun quiet view target => quiet view ((project_target state name view).mp target)⟩
    | active word view =>
      simp only [projectFiber, phase, projectPhase]
      let selected := requiredView name row.component.requires view
      have same : TargetView.mask row.component.requires selected = TargetView.mask row.component.requires view := by
        funext key
        by_cases needed : row.component.requires key = true <;> simp [selected, TargetView.mask, requiredView, needed]
      exact (project_target state name selected).trans
        ⟨TargetView.target_of_mask_eq state name row found selected view same,
          TargetView.target_of_mask_eq state name row found view selected same.symm⟩
    | reloading | unloading => simp only [projectFiber, phase, projectPhase]
  constructor
  · intro quiet name row found
    exact (atRow name row found).mp (quiet name (projectFiber name row) (by simp [project, found]))
  · intro quiet name row found
    cases source : state name with
    | none => simp [project, source] at found
    | some old =>
      have same : projectFiber name old = row := Option.some.inj (by simpa only [project, source, Option.map_some] using found)
      subst row
      exact (atRow name old source).mpr (quiet name old source)

theorem quiet_of_related [DecidableEq Name] [DecidableEq Key] [Setoid Value] {before after : R}
    (aligned : StageSimulation.Related Eq before after)
    (quiet : Progress.Quiet before) : Progress.Quiet after := by
  intro name row found
  obtain ⟨old, oldAt, fields⟩ := StageSimulation.present_related (aligned.symm (fun _ _ same => same.symm)) name row found
  have prior := quiet name old oldAt
  have phases := fields.phase
  cases first : old.phase <;> cases second : row.phase <;> simp only [first, second] at phases prior ⊢ <;> cases phases
  all_goals first
    | exact False.elim prior
    | exact (GuardObservations.target_iff aligned.observed name _).mp prior
    | exact fun view target => prior view ((GuardObservations.target_iff aligned.observed name view).mpr target)

theorem project_owned (state : R) (owned : Safety.Owned state) : Safety.Owned (project state) := by
  intro name row key found bound
  cases prior : state name with
  | none => simp [project, prior] at found
  | some old =>
    have same : projectFiber name old = row := Option.some.inj (by simpa [project, prior] using found)
    subst row
    exact owned name old key prior bound

theorem project_disjoint [DecidableEq Name] [DecidableEq Key] (state : R) (disjoint : WellFormed.Disjoint state) :
    WellFormed.Disjoint (project state) := by
  apply WellFormed.disjoint_of_origins ?_ disjoint
  intro name row found
  cases prior : state name with
  | none => simp [project, prior] at found
  | some old =>
    have same : projectFiber name old = row := Option.some.inj (by simpa [project, prior] using found)
    have component := congrArg Fiber.component same
    exact ⟨old, rfl, component⟩

theorem project_self_related [Setoid Value] (state : R) :
    StageSimulation.Related Eq (project state) (project state) := by
  intro name
  cases found : state name with
  | none => simp [project, found, Iterators.OptionRel]
  | some row =>
    rw [show project state name = some (projectFiber name row) by simp [project, found]]
    refine ⟨⟨rfl, rfl, rfl⟩, rfl, rfl, ?_, fun key => ?_⟩
    · cases phase : row.phase <;> simp only [projectFiber, phase, projectPhase]
      · exact .inactive
      · exact .reloading _ rfl .nil
      · exact .active _ .nil
      · exact .unloading _ .nil
    · change Iterators.OptionRel _ (row.table key) (row.table key)
      cases row.table key with
      | none => trivial
      | some value => exact Setoid.refl value

theorem project_related [Setoid Value] {Q : Code → Code → Prop} {left right : R}
    (related : StageSimulation.Related Q left right) : StageSimulation.Related Q (project left) (project right) := by
  intro name
  have row := related name
  cases lp : left name <;> cases rp : right name <;>
    simp only [project, lp, rp, Option.map_none, Option.map_some, Iterators.OptionRel] at row ⊢
  rename_i a b
  refine ⟨row.component, row.parent, row.retired, ?_, row.table⟩
  have phase := row.phase
  change StageSimulation.PhaseRelated Q (projectPhase name a.component.requires a.phase)
    (projectPhase name b.component.requires b.phase)
  rw [row.component.requires]
  generalize a.phase = leftPhase at phase ⊢
  generalize b.phase = rightPhase at phase ⊢
  cases phase with
  | inactive => exact .inactive
  | reloading view code _ => exact .reloading (requiredView _ _ view) code .nil
  | active view _ => exact .active (requiredView _ _ view) .nil
  | unloading view _ => exact .unloading (requiredView _ _ view) .nil

theorem rename_related [Setoid Value] {Q : Code → Code → Prop} {left right : R}
    (p : P) (related : StageSimulation.Related Q left right) :
    StageSimulation.Related Q (Renaming.registry p left) (Renaming.registry p right) := by
  have renameStack {a b : List (Inverse Name Key Value)} (stack : StageSimulation.StackRelated a b) :
      StageSimulation.StackRelated (a.map (Renaming.inverse p)) (b.map (Renaming.inverse p)) := by
    induction stack with
    | nil => exact .nil
    | cons top _ ih =>
      apply StageSimulation.StackRelated.cons _ ih
      cases top with
      | unit => exact .unit
      | restrict owner key => exact .restrict (p.toFun owner) key
      | operate owner key related => exact .operate (p.toFun owner) key related
      | retire child => exact .retire (p.toFun child)
  intro name
  obtain ⟨old, rfl⟩ := p.surjective name
  have row := related old
  rw [Renaming.registry_at, Renaming.registry_at]
  cases lp : left old <;> cases rp : right old <;>
    simp only [lp, rp, Option.map_none, Option.map_some, Iterators.OptionRel] at row ⊢
  rename_i a b
  refine ⟨row.component, congrArg (Option.map p.toFun) row.parent, row.retired, ?_, row.table⟩
  have phase := row.phase
  change StageSimulation.PhaseRelated Q (Renaming.phase p a.phase) (Renaming.phase p b.phase)
  generalize a.phase = leftPhase at phase ⊢
  generalize b.phase = rightPhase at phase ⊢
  cases phase with
  | inactive => exact .inactive
  | reloading view code stack => exact .reloading (Renaming.view p view) code (renameStack stack)
  | active view stack => exact .active (Renaming.view p view) (renameStack stack)
  | unloading view stack => exact .unloading (Renaming.view p view) (renameStack stack)

/-- Agreement of retained controls and observed tables up to renaming. -/
def ProjectedAgreement [Setoid Value] (left right : R) : Prop :=
  ∃ p : P, StageSimulation.Related Eq (Renaming.registry p (project left)) (project right)

theorem ProjectedAgreement.of_related [Setoid Value] {left right : R}
    (related : StageSimulation.Related Eq left right) : ProjectedAgreement left right :=
  ⟨Renaming.Permutation.identity, by simpa only [Renaming.registry_identity] using project_related related⟩

theorem ProjectedAgreement.of_rename_eq [Setoid Value] {left right : R} {p : P}
    (equal : Renaming.registry p (project left) = project right) : ProjectedAgreement left right :=
  ⟨p, by rw [equal]; exact project_self_related right⟩

theorem ProjectedAgreement.refl [Setoid Value] (state : R) : ProjectedAgreement state state :=
  .of_rename_eq (p := Renaming.Permutation.identity) (Renaming.registry_identity _)

theorem ProjectedAgreement.symm [Setoid Value] {left right : R}
    (related : ProjectedAgreement left right) : ProjectedAgreement right left := by
  classical
  obtain ⟨p, compared⟩ := related
  have back := rename_related p.symm (compared.symm (fun _ _ equal => equal.symm))
  exact ⟨p.symm, by simpa only [Renaming.registry_symm] using back⟩

theorem ProjectedAgreement.trans [Setoid Value] {left middle right : R}
    (first : ProjectedAgreement left middle) (second : ProjectedAgreement middle right) : ProjectedAgreement left right := by
  classical
  obtain ⟨p, earlier⟩ := first
  obtain ⟨q, later⟩ := second
  have moved := rename_related q earlier
  rw [Renaming.registry_trans] at moved
  exact ⟨p.trans q, StageSimulation.Related.trans (Q := Eq) (fun a b => a.trans b) moved later⟩

variable [DecidableEq Name] [DecidableEq Key]

/-- Changing a permutation on vacant names leaves the renamed cut projection
unchanged. Parent closure and support ensure all retained references are live. -/
theorem rename_on_live {program : Code → Instruction Name Key Value Code Error} {last time : Nat}
    (trace : Trace program last) (bounded : time ≤ last) {p q : P}
    (same : ∀ name, trace.state time name ≠ none → p.toFun name = q.toFun name) :
    Renaming.registry p (project (trace.state time)) = Renaming.registry q (project (trace.state time)) := by
  let state := trace.state time
  have parents := trace.parent_closed time bounded
  have supported := trace.supported time bounded
  have agrees {name : Name} {row : F} (found : state name = some row) :
      Renaming.fiber p (projectFiber name row) = Renaming.fiber q (projectFiber name row) := by
    have parent : row.parent.map p.toFun = row.parent.map q.toFun := by
      cases declared : row.parent with
      | none => rfl
      | some owner => exact congrArg some (same owner (parents name row owner found declared))
    have views (view : View Name Key) (committed : row.phase.committed = some view) :
        Renaming.view p (requiredView name row.component.requires view) =
          Renaming.view q (requiredView name row.component.requires view) := by
      funext key
      by_cases needed : row.component.requires key = true
      · obtain ⟨_, provider, present, _, _⟩ := Ordering.retained_provider state name row view key supported found committed needed
        simpa [Renaming.view, requiredView, needed] using same (view key) (by change state (view key) ≠ none; simp [present])
      · simpa [Renaming.view, requiredView, needed] using same name (by change state name ≠ none; simp [found])
    cases phase : row.phase <;>
      simp [projectFiber, Renaming.fiber, projectPhase, Renaming.phase, phase, parent] <;>
      exact views _ (by rw [phase]; rfl)
  funext image
  obtain ⟨name, rfl⟩ := p.surjective image
  rw [Renaming.registry_at]
  cases found : state name with
  | some row =>
    rw [same name (by change state name ≠ none; simp [found]), Renaming.registry_at]
    change ((state name).map (projectFiber name)).map (Renaming.fiber p) =
      ((state name).map (projectFiber name)).map (Renaming.fiber q)
    simp [found, agrees found]
  | none =>
    rw [show project (trace.state time) name = none from (project_present _ _).mpr found]
    obtain ⟨other, h⟩ := q.surjective (p.toFun name)
    rw [← h, Renaming.registry_at]
    have vacant : state other = none := by
      cases otherFound : state other with
      | none => rfl
      | some value =>
        have eq := p.injective ((same other (by change state other ≠ none; simp [otherFound])).trans h)
        rw [eq, found] at otherFound
        cases otherFound
    rw [(project_present _ _).mpr vacant]
    rfl

end Cordis.Repairs.GuardedCutState
