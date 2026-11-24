import Cordis.TranspositionPhases
import Cordis.TargetView

/-! The first-Begin subcase of Lemma78(1). It needs no primitive independence:
Begin has identity state application, and the foreign activation's actual table
domain frame preserves the target. Both exchanged transitions are constructed. -/
namespace Cordis.Transposition
open Calculus Stages Labeled
universe u
variable {Name Key Value Code Error : Type u}
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
variable [DecidableEq Name] [DecidableEq Key]
set_option linter.unusedSectionVars false

theorem activation_source (program : Code → Instruction Name Key Value Code Error)
    {rule : Rule} {actor : Name} {r s : R} (step : Labeled.Step program rule actor r s)
    (active : Activation rule) :
    ∃ fiber view, r actor = some fiber ∧ ¬ fiber.phase.available ∧ Target r actor view := by
  cases step with
  | begin _ _ fiber view found phase free target =>
    exact ⟨fiber, view, found, by simp [phase, Phase.available], target⟩
  | iter _ middle _ fiber code acc view inverse next found phase target land =>
    exact ⟨fiber, view, found, by simp [phase, Phase.available], target⟩
  | finish _ middle _ fiber code acc view inverse found phase target land =>
    exact ⟨fiber, view, found, by simp [phase, Phase.available], target⟩
  | _ => simp [Activation] at active

theorem land_existing_table (program : Code → Instruction Name Key Value Code Error)
    {actor : Name} {code : Code} {r s : R} {inverse next}
    (land : Land program actor code r s inverse next)
    (name : Name) (fiber : F) (present : r name = some fiber) :
    ∃ table, s name = some {fiber with table := table} := by
  cases land with
  | unit => exact ⟨fiber.table, present⟩
  | provide _ _ _ entry key value action found declared absent =>
    by_cases same : name = actor
    · subst name
      exact ⟨fun other => if other = key then some value else fiber.table other,
        by simp [write, Calculus.modify, present]⟩
    · exact ⟨fiber.table, by simp [write, Calculus.modify, same, present]⟩
  | operate _ _ _ key run owner before after inv result action located called =>
    by_cases same : name = owner
    · subst name
      exact ⟨fun other => if other = key then some after else fiber.table other,
        by simp [write, Calculus.modify, present]⟩
    · exact ⟨fiber.table, by simp [write, Calculus.modify, same, present]⟩
  | instantiate _ _ _ component child action ready =>
    have different : name ≠ child := by
      intro same
      have absent : r name = none := same ▸ ready.1
      simp [present] at absent
    exact ⟨fiber.table, by simp [put, different, present]⟩

theorem activation_other_table_domains (program : Code → Instruction Name Key Value Code Error)
    {rule : Rule} {actor : Name} {r s : R} (step : Labeled.Step program rule actor r s)
    (active : Activation rule) (name : Name) (fiber : F) (different : name ≠ actor)
    (present : r name = some fiber) :
    ∃ table, s name = some {fiber with table := table} ∧
      ∀ key, table key = none ↔ fiber.table key = none := by
  cases step with
  | begin => exact ⟨fiber.table, (mark_other _ _ _ _ different).trans present, fun _ => Iff.rfl⟩
  | iter _ middle _ entry code acc view inverse next found phase target land
  | finish _ middle _ entry code acc view inverse found phase target land =>
    obtain ⟨table, existsEntry⟩ := land_existing_table program land name fiber present
    exact ⟨table, (mark_other _ _ _ _ different).trans existsEntry, fun key =>
      ((TableFrame.land_frame program land entry found name fiber _ present existsEntry different key).1).symm⟩
  | _ => simp [Activation] at active

theorem activation_other_table (program : Code → Instruction Name Key Value Code Error)
    {rule : Rule} {actor : Name} {r s : R} (step : Labeled.Step program rule actor r s)
    (active : Activation rule) (name : Name) (fiber : F) (different : name ≠ actor)
    (present : r name = some fiber) : ∃ table, s name = some {fiber with table := table} := by
  obtain ⟨table, kept, _⟩ := activation_other_table_domains program step active name fiber different present
  exact ⟨table, kept⟩

theorem landing_mark_target (program : Code → Instruction Name Key Value Code Error)
    {actor : Name} {code : Code} {r s : R} {inverse next}
    (land : Land program actor code r s inverse next)
    (actorFiber : F) (actorFound : r actor = some actorFiber)
    (unavailable : ¬ actorFiber.phase.available) (phase)
    (name : Name) (view : View Name Key) (different : name ≠ actor)
    (target : Target r name view) : Target (mark s actor phase) name view := by
  cases found : r name with
  | none => simp [Target, found] at target
  | some fiber =>
    obtain ⟨table, present⟩ := land_existing_table program land name fiber found
    simp only [Target, found] at target
    simp only [Target, mark_other s name actor phase different, present]
    refine ⟨target.1, ?_⟩
    intro key required
    have ready := target.2 key required
    cases providerFound : r (view key) with
    | none => simp [providerFound] at ready
    | some provider =>
      simp only [providerFound] at ready
      have foreign : view key ≠ actor := by
        intro equal
        have same : provider = actorFiber := Option.some.inj (by simpa [equal, actorFound] using providerFound.symm)
        exact unavailable (same ▸ ready.1)
      obtain ⟨newTable, providerPresent⟩ := land_existing_table program land (view key) provider providerFound
      simp only [mark_other s (view key) actor phase foreign, providerPresent]
      refine ⟨ready.1, ?_⟩
      have frame := TableFrame.land_frame program land actorFiber actorFound (view key) provider
        {provider with table := newTable} providerFound providerPresent foreign
      intro absent
      exact ready.2 ((frame key).1.mpr absent)

/-- An activation cannot invalidate an already satisfied target of another
actor: it only adds its own bindings and preserves every foreign binding domain.
The acting fiber is not an available provider at an activation source. -/
theorem activation_target_forward (program : Code → Instruction Name Key Value Code Error)
    {rule : Rule} {actor : Name} {r s : R} (step : Labeled.Step program rule actor r s)
    (active : Activation rule) (name : Name) (view : View Name Key) (different : name ≠ actor)
    (target : Target r name view) : Target s name view := by
  cases step with
  | begin _ _ fiber selected found inactive free ownTarget =>
    exact (mark_target r actor fiber _ found (by simp [inactive, Phase.available]) name view).mpr target
  | iter _ middle _ fiber code acc selected inverse next found reloading ownTarget land =>
    exact landing_mark_target program land fiber found (by simp [reloading, Phase.available]) _ name view different target
  | finish _ middle _ fiber code acc selected inverse found reloading ownTarget land =>
    exact landing_mark_target program land fiber found (by simp [reloading, Phase.available]) _ name view different target
  | _ => simp [Activation] at active

theorem mark_twice (r : R) (name : Name) (first second) :
    mark (mark r name first) name second = mark r name second := by
  funext other
  by_cases same : other = name <;>
    simp [mark, Calculus.modify, same, Option.map_map, Function.comp_def]

theorem mark_existing (r : R) (name : Name) (fiber : F) (found : r name = some fiber) :
    mark r name fiber.phase = r := by
  funext other
  by_cases same : other = name
  · subst other; simp [mark, Calculus.modify, found]
  · simp [mark, Calculus.modify, same]

/-- Lemma78(1) when its first activation is Begin. The result is stronger than
the stated subcase: applicability of the second step at the earlier state is
derived, and the two orders have literally equal endpoints. -/
theorem begin_activation_diamond (program : Code → Instruction Name Key Value Code Error)
    {rule : Rule} {first second : Name} {r s t : R}
    (opening : Labeled.Step program .begin first r s)
    (activation : Labeled.Step program rule second s t) (active : Activation rule)
    (different : first ≠ second) :
    ∃ middle, Labeled.Step program rule second r middle ∧
      Labeled.Step program .begin first middle t := by
  cases opening with
  | begin _ _ fiber view found inactive free target =>
    let started : F := {fiber with phase := .reloading fiber.component.entry [] view}
    have startedFound : mark r first (.reloading fiber.component.entry [] view) first = some started :=
      mark_self r first fiber _ found
    have restored : mark (mark r first (.reloading fiber.component.entry [] view)) first .inactive = r := by
      rw [mark_twice, ← inactive]
      exact mark_existing r first fiber found
    have swapped := activation_after_phase program activation active first started .inactive
      (Ne.symm different) startedFound (Iff.refl False)
    rw [restored] at swapped
    obtain ⟨table, finalFound⟩ := activation_other_table program activation active first started different startedFound
    have firstTarget : Target (mark r first (.reloading fiber.component.entry [] view)) first view :=
      (mark_target r first fiber _ found (by simp [inactive, Phase.available]) first view).mpr target
    have finalTarget := activation_target_forward program activation active first view different firstTarget
    let current : F := {started with table := table}
    have currentFound : t first = some current := finalFound
    have currentPhase : current.phase = .reloading fiber.component.entry [] view := rfl
    have earlierFound : mark t first .inactive first = some {current with phase := .inactive} :=
      mark_self t first current .inactive currentFound
    have closed : mark (mark t first .inactive) first (.reloading fiber.component.entry [] view) = t := by
      rw [mark_twice, ← currentPhase]
      exact mark_existing t first current currentFound
    refine ⟨mark t first .inactive, swapped, ?_⟩
    have beginning : Labeled.Step program .begin first (mark t first .inactive)
        (mark (mark t first .inactive) first (.reloading fiber.component.entry [] view)) := by
      apply Labeled.Step.begin (mark t first .inactive) first {current with phase := .inactive} view earlierFound rfl
      · simp [ErrorFree, earlierFound]
      · exact (mark_target t first current .inactive currentFound (Iff.refl False) first view).mpr finalTarget
    simpa only [closed] using beginning

/-- The second-Begin subcase, retaining its actual chosen view explicitly.
`earlierTarget` is precisely the nontrivial earlier-applicability premise in
Lemma78(1); the earlier fiber, inactive phase and error-free guard are derived.
The other displayed guards constitute the actual second Begin rule. -/
theorem activation_begin_diamond (program : Code → Instruction Name Key Value Code Error)
    {rule : Rule} {actor : Name} {r s : R}
    (activation : Labeled.Step program rule actor r s) (active : Activation rule)
    (name : Name) (fiber : F) (view : View Name Key) (different : name ≠ actor)
    (found : s name = some fiber) (inactive : fiber.phase = .inactive)
    (_free : ErrorFree s name) (_target : Target s name view) (earlierTarget : Target r name view) :
    ∃ middle, Labeled.Step program .begin name r middle ∧
      Labeled.Step program rule actor middle (mark s name (.reloading fiber.component.entry [] view)) := by
  cases originalFound : r name with
  | none => simp [Target, originalFound] at earlierTarget
  | some original =>
    obtain ⟨table, currentFound⟩ := activation_other_table program activation active name original different originalFound
    have currentEq : {original with table := table} = fiber := Option.some.inj (currentFound.symm.trans found)
    have phaseEq : original.phase = .inactive := (congrArg Fiber.phase currentEq).trans inactive
    have componentEq : original.component = fiber.component := by
      have equality := congrArg Fiber.component currentEq
      exact equality
    have earlierFree : ErrorFree r name := by simp [ErrorFree, originalFound]
    refine ⟨mark r name (.reloading original.component.entry [] view),
      .begin r name original view originalFound phaseEq earlierFree earlierTarget, ?_⟩
    have swapped := activation_after_phase program activation active name original
      (.reloading original.component.entry [] view) (Ne.symm different) originalFound
      (by simp [phaseEq, Phase.available])
    simpa only [componentEq] using swapped

/-- Earlier applicability can choose a different total view at irrelevant
coordinates. Actual ownership plus disjoint reservations force equality at all
declared coordinates; hence the view chosen by the later Begin also works
before the activation. No literal equality of total views is assumed. -/
theorem earlier_target_for_selected_view (program : Code → Instruction Name Key Value Code Error)
    {rule : Rule} {actor : Name} {r s : R}
    (activation : Labeled.Step program rule actor r s) (active : Activation rule)
    (owned : Safety.Owned r) (disjoint : WellFormed.Disjoint r)
    (name : Name) (fiber : F) (view : View Name Key) (different : name ≠ actor)
    (found : s name = some fiber) (target : Target s name view)
    (earlier : ∃ selected, Target r name selected) : Target r name view := by
  obtain ⟨selected, earlierTarget⟩ := earlier
  cases originalFound : r name with
  | none => simp [Target, originalFound] at earlierTarget
  | some original =>
    obtain ⟨table, currentFound⟩ := activation_other_table program activation active name original different originalFound
    have currentEq : {original with table := table} = fiber := Option.some.inj (currentFound.symm.trans found)
    have componentEq : original.component = fiber.component := by
      have equality := congrArg Fiber.component currentEq
      exact equality
    have laterTarget := activation_target_forward program activation active name selected different earlierTarget
    have masks := TargetView.masked_targets_equal s name fiber found
      (Safety.step_owned program activation.toCalculus owned)
      (WellFormed.step_disjoint program activation.toCalculus disjoint) selected view laterTarget target
    exact TargetView.target_of_mask_eq r name original originalFound selected view
      (by simpa only [componentEq] using masks) earlierTarget

/-- An already selected target is available before a foreign activation
exactly when the consumer was already present and no required key takes
its provider from that activation's actor. A freshly born child cannot
already be an active provider. -/
theorem selected_target_before_activation_iff (program : Code → Instruction Name Key Value Code Error)
    {rule : Rule} {actor name : Name} {r s : R}
    (activation : Labeled.Step program rule actor r s) (active : Activation rule)
    (different : name ≠ actor) {fiber : F} {view : View Name Key}
    (found : s name = some fiber) (target : Target s name view) :
    Target r name view ↔
      r name ≠ none ∧ ∀ key, fiber.component.requires key = true → view key ≠ actor := by
  obtain ⟨acting, _, actingFound, unavailable, _⟩ := activation_source program activation active
  constructor
  · intro earlier
    cases originalFound : r name with
    | none => simp [Target, originalFound] at earlier
    | some original =>
      obtain ⟨table, kept⟩ := activation_other_table program activation active name original different originalFound
      have same := Option.some.inj (kept.symm.trans found)
      refine ⟨by simp, ?_⟩
      intro key required equal
      have oldRequired : original.component.requires key = true := by
        simpa [← same] using required
      simp only [Target, originalFound] at earlier
      have needs := earlier.2 key oldRequired
      rw [equal, actingFound] at needs
      exact unavailable needs.1
  · rintro ⟨present, avoids⟩
    cases originalFound : r name with
    | none => exact False.elim (present originalFound)
    | some original =>
      obtain ⟨table, kept⟩ := activation_other_table program activation active name original different originalFound
      have same := Option.some.inj (kept.symm.trans found)
      simp only [Target, found] at target
      simp only [Target, originalFound]
      refine ⟨(congrArg Fiber.retired same).trans target.1, ?_⟩
      intro key required
      have newRequired : fiber.component.requires key = true := by
        simpa [← same] using required
      have foreign := avoids key newRequired
      have ready := target.2 key newRequired
      cases laterProvider : s (view key) with
      | none => simp [laterProvider] at ready
      | some provider =>
        simp only [laterProvider] at ready
        cases priorProvider : r (view key) with
        | none =>
          have created := (activation_creates_iff program activation active (view key) (Ne.symm foreign)).mpr
            ⟨priorProvider, by simp [laterProvider]⟩
          obtain ⟨_, component, phase, _, _, endpoint⟩ := created
          rw [endpoint, mark_other _ _ _ phase foreign, put_self] at laterProvider
          cases Option.some.inj laterProvider
          exact False.elim (by simpa [fresh, Phase.available] using ready.1)
        | some oldProvider =>
          obtain ⟨otherTable, other, domain⟩ := activation_other_table_domains program activation active
            (view key) oldProvider foreign priorProvider
          have compare := Option.some.inj (other.symm.trans laterProvider)
          subst provider
          exact ⟨ready.1, fun absent => ready.2 ((domain key).mpr absent)⟩

/-- Lemma78(1)'s second-Begin case with its original existential applicability
premise. `Owned` is Definition48's binding/declaration invariant; disjointness is
Definition63(2). The selected-view bridge above eliminates the representation's
arbitrary total-view coordinates before constructing the actual swapped steps. -/
theorem activation_begin_diamond_of_applicable (program : Code → Instruction Name Key Value Code Error)
    {rule : Rule} {actor name : Name} {r s t : R}
    (activation : Labeled.Step program rule actor r s) (active : Activation rule)
    (opening : Labeled.Step program .begin name s t) (different : name ≠ actor)
    (owned : Safety.Owned r) (disjoint : WellFormed.Disjoint r)
    (earlier : ∃ middle, Labeled.Step program .begin name r middle) :
    ∃ middle, Labeled.Step program .begin name r middle ∧
      Labeled.Step program rule actor middle t := by
  have earlierTarget : ∃ selected, Target r name selected := by
    obtain ⟨middle, begins⟩ := earlier
    cases begins with
    | begin _ _ entry selected present phase free target => exact ⟨selected, target⟩
  cases opening with
  | begin _ _ fiber view found inactive free target =>
    exact activation_begin_diamond program activation active name fiber view different found inactive free target
      (earlier_target_for_selected_view program activation active owned disjoint name fiber view different
        found target earlierTarget)

end Cordis.Transposition
