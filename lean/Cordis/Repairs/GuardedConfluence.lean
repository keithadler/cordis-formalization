import Cordis.Repairs.GuardedCausalOrder
import Cordis.Repairs.GuardedScheduleMatching
import Cordis.Repairs.GuardedAddressSchedule
import Cordis.Repairs.GuardedActivationAlignment
import Cordis.Repairs.GuardedCompleteAlignment
import Cordis.Repairs.GuardedNameExtension

/-! Compare original endpoints once their open reductions have matching
ordered events. Only removable nonroot vestiges may be erased. -/
namespace Cordis.Repairs.GuardedConfluence
open Calculus Stages GuardedHistory GuardedCutState GuardedLandingMatching GuardedScheduleMatching
open GuardedBirthAddresses (orchestrationInput)
open GuardedAddressSchedule (addressedEventAt open_events_of_ordered_addresses)
open Iterators (OptionRel)
open PaperEffectEquations (CoeffectOperations ValueOperationWitness)
open PaperObservationEquations (OperationRespects)
open PartialCoeffectIndependenceContracts (tableSetoid)
open StageRecovery (tableAt)
open TypedRegistry (RawRegistry Scalar encodeProgram)

universe u
variable {Name Key Code : Type u} {V : Key → Type u} {ops : CoeffectOperations V}
variable [DecidableEq Name] [DecidableEq Key]
variable {program : Code → TypedRegistry.Instruction Name ops Code}
local notation "R" => RawRegistry Name ops Code
local notation "A" => Scalar ops

/-- Compare retained control fields and observed table values under a
permutation after justified erasures. Saved words and unused view
coordinates have their own cut comparisons. -/
def EndpointAgreement (observe : ∀ key, Setoid (V key)) (left right : R) : Prop :=
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  ∃ (p : Renaming.Permutation Name) (leftPruned rightPruned : R),
    VestigeErasures left leftPruned ∧ VestigeErasures right rightPruned ∧
    StageSimulation.Related Eq (Renaming.registry p (project leftPruned)) (project rightPruned)

omit [DecidableEq Key] in
theorem EndpointAgreement.refl (observe : ∀ key, Setoid (V key)) (state : R) :
    EndpointAgreement observe state state := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  obtain ⟨names, compared⟩ := ProjectedAgreement.refl state
  exact ⟨names, state, state, .refl _, .refl _, compared⟩

omit [DecidableEq Key] in
theorem EndpointAgreement.symm (observe : ∀ key, Setoid (V key)) {left right : R}
    (agreement : EndpointAgreement observe left right) : EndpointAgreement observe right left := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  obtain ⟨names, leftPruned, rightPruned, leftErased, rightErased, compared⟩ := agreement
  obtain ⟨inverse, back⟩ := ProjectedAgreement.symm
    (left := leftPruned) (right := rightPruned) ⟨names, compared⟩
  exact ⟨inverse, rightPruned, leftPruned, rightErased, leftErased, back⟩

private theorem projected_erasure_transport [Setoid A] {source reduced target : R}
    (erased : VestigeErasures source reduced) (agreement : ProjectedAgreement source target) :
    ∃ targetReduced, VestigeErasures target targetReduced ∧ ProjectedAgreement reduced targetReduced := by
  induction erased generalizing target with
  | refl => exact ⟨target, .refl _, agreement⟩
  | @remove before after name ready child remaining ih =>
    obtain ⟨names, compared⟩ := agreement
    let renamed := names.toFun name
    have readyProjected := Renaming.removable_map names (project before) name ((project_removable before name).mpr ready)
    have readyTarget : Removable target renamed :=
      (project_removable target renamed).mp ((GuardObservations.removable_iff compared.observed renamed).mp readyProjected)
    have childTarget : LegalHistory.rootAt target renamed = false := by
      have row := compared.observed renamed
      change OptionRel _ (Renaming.registry names (project before) (names.toFun name)) (project target renamed) at row
      rw [Renaming.registry_at] at row
      cases original : before name <;> cases renamedRow : target renamed <;>
        simp [project, projectFiber, Renaming.fiber, original, renamedRow, OptionRel, LegalHistory.rootAt] at row child ⊢
      rw [← row.parent]
      simpa using child
    have next : ProjectedAgreement (erase before name) (erase target renamed) := by
      refine ⟨names, ?_⟩
      rw [project_erase, project_erase, Renaming.erase_eq]
      exact StageSimulation.erase_related compared renamed
    obtain ⟨targetReduced, path, result⟩ := ih next
    exact ⟨targetReduced, .remove renamed readyTarget childTarget path, result⟩

/-- Endpoint agreement is transitive. Two erasure choices for the middle
registry can be joined, and the extra erasures transfer to either side. -/
theorem EndpointAgreement.trans (observe : ∀ key, Setoid (V key)) {left middle right : R}
    (first : EndpointAgreement observe left middle) (second : EndpointAgreement observe middle right) :
    EndpointAgreement observe left right := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  obtain ⟨firstNames, leftPruned, firstMiddle, leftErased, middleFirst, firstCompared⟩ := first
  obtain ⟨secondNames, secondMiddle, rightPruned, middleSecond, rightErased, secondCompared⟩ := second
  obtain ⟨joined, joinFirst, joinSecond⟩ := middleFirst.join middleSecond
  have leftAgreement : ProjectedAgreement firstMiddle leftPruned :=
    ProjectedAgreement.symm (left := leftPruned) ⟨firstNames, firstCompared⟩
  have rightAgreement : ProjectedAgreement secondMiddle rightPruned := ⟨secondNames, secondCompared⟩
  obtain ⟨leftFinal, leftExtra, joinedLeft⟩ := projected_erasure_transport joinFirst leftAgreement
  obtain ⟨rightFinal, rightExtra, joinedRight⟩ := projected_erasure_transport joinSecond rightAgreement
  obtain ⟨names, compared⟩ := joinedLeft.symm.trans joinedRight
  exact ⟨names, leftFinal, rightFinal, leftErased.append leftExtra, rightErased.append rightExtra, compared⟩

/-- Endpoint agreement can be checked after pruning both registries
as far as the vestige guards allow. -/
theorem endpointAgreement_iff_normal (observe : ∀ key, Setoid (V key)) {left right leftNormal rightNormal : R}
    (leftPath : VestigeErasures left leftNormal) (rightPath : VestigeErasures right rightNormal)
    (leftDone : VestigeNormal leftNormal) (rightDone : VestigeNormal rightNormal) :
    letI : Setoid A := TypedCoeffectReplay.setoid observe
    EndpointAgreement observe left right ↔ ProjectedAgreement leftNormal rightNormal := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  constructor
  · rintro ⟨names, leftPruned, rightPruned, leftErased, rightErased, compared⟩
    obtain ⟨leftJoin, leftMore, leftEnd⟩ := leftErased.join leftPath
    have leftSame := leftEnd.eq_of_normal leftDone
    subst leftJoin
    obtain ⟨intermediate, rightMore, agreement⟩ :=
      projected_erasure_transport leftMore (target := rightPruned) ⟨names, compared⟩
    obtain ⟨rightJoin, rightFinish, rightEnd⟩ := (rightErased.append rightMore).join rightPath
    have rightSame := rightEnd.eq_of_normal rightDone
    subst rightJoin
    obtain ⟨leftFinal, leftFinish, result⟩ := projected_erasure_transport rightFinish agreement.symm
    have same := leftFinish.eq_of_normal leftDone
    subst leftFinal
    exact result.symm
  · rintro ⟨names, compared⟩
    exact ⟨names, leftNormal, rightNormal, leftPath, rightPath, compared⟩

private theorem compare_at_cut (observe : ∀ key, Setoid (V key))
    {left right leftPruned rightPruned : R} {firstLength secondLength cut : Nat}
    (first : Trace (encodeProgram program) firstLength) (second : Trace (encodeProgram program) secondLength)
    (leftErased : VestigeErasures left leftPruned) (rightErased : VestigeErasures right rightPruned)
    (leftRelated : @StageSimulation.Related Name Key A Code _ (TypedCoeffectReplay.setoid observe) Eq
      leftPruned (first.state cut))
    (rightRelated : @StageSimulation.Related Name Key A Code _ (TypedCoeffectReplay.setoid observe) Eq
      rightPruned (second.state cut))
    (matchesAtCut : CutAgreement first second cut) : EndpointAgreement observe left right := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  obtain ⟨names, mid, _, _⟩ := matchesAtCut
  have earlier := rename_related names (project_related leftRelated)
  rw [mid] at earlier
  exact ⟨names, leftPruned, rightPruned, leftErased, rightErased,
    StageSimulation.Related.trans (Q := Eq) (fun a b => a.trans b) earlier
      ((project_related rightRelated).symm (fun _ _ equal => equal.symm))⟩

omit [DecidableEq Key] in
private theorem compare_projected_endpoints (observe : ∀ key, Setoid (V key))
    {left right leftPruned rightPruned first second : R}
    (leftErased : VestigeErasures left leftPruned) (rightErased : VestigeErasures right rightPruned)
    (leftRelated : @StageSimulation.Related Name Key A Code _ (TypedCoeffectReplay.setoid observe) Eq
      leftPruned first)
    (rightRelated : @StageSimulation.Related Name Key A Code _ (TypedCoeffectReplay.setoid observe) Eq
      rightPruned second)
    (between : @ProjectedAgreement Name Key A Code _ (TypedCoeffectReplay.setoid observe) first second) :
    EndpointAgreement observe left right := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  obtain ⟨names, compared⟩ :=
    (ProjectedAgreement.of_related leftRelated).trans (between.trans (ProjectedAgreement.of_related rightRelated).symm)
  exact ⟨names, leftPruned, rightPruned, leftErased, rightErased, compared⟩

/-- A certified exchange path between the reductions suffices to
compare the original endpoints after the permitted vestige erasures. -/
theorem compare_endpoints_of_schedule_path (observe : ∀ key, Setoid (V key))
    {left right leftPruned rightPruned : R} {length : Nat}
    {first second : Trace (encodeProgram program) length}
    (leftErased : VestigeErasures left leftPruned) (rightErased : VestigeErasures right rightPruned)
    (leftRelated : @StageSimulation.Related Name Key A Code _ (TypedCoeffectReplay.setoid observe) Eq
      leftPruned (first.state length))
    (rightRelated : @StageSimulation.Related Name Key A Code _ (TypedCoeffectReplay.setoid observe) Eq
      rightPruned (second.state length))
    (path : @GuardedCompleteAlignment.ScheduleAlignmentPath Name Key Code _ _ V ops program
      (TypedCoeffectReplay.setoid observe) length first second) :
    EndpointAgreement observe left right := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  exact compare_projected_endpoints observe leftErased rightErased leftRelated rightRelated path.preserves.1

/-- The endpoint inference of the confluence proof. The schedule premise
is exactly the alignment still needed between independent reductions. -/
theorem compare_normalized_endpoints (observe : ∀ key, Setoid (V key))
    {left right leftPruned rightPruned : R} {length : Nat}
    (first second : Trace (encodeProgram program) length)
    (leftErased : VestigeErasures left leftPruned) (rightErased : VestigeErasures right rightPruned)
    (leftRelated : @StageSimulation.Related Name Key A Code _ (TypedCoeffectReplay.setoid observe) Eq
      leftPruned (first.state length))
    (rightRelated : @StageSimulation.Related Name Key A Code _ (TypedCoeffectReplay.setoid observe) Eq
      rightPruned (second.state length))
    (stable : ChildContinuations (encodeProgram program))
    (aligned : ∀ cut, cut < length → OpenEventsAgree first second cut) : EndpointAgreement observe left right :=
  compare_at_cut observe first second leftErased rightErased leftRelated rightRelated
    (match_open_prefix first second stable length (Nat.le_refl _) (Nat.le_refl _) aligned)

/-- The confluence inference can be stated purely using the addressed
event order of the open reductions. Their birth stamps are derived. -/
theorem compare_normalized_endpoints_by_addresses (observe : ∀ key, Setoid (V key))
    {left right leftPruned rightPruned : R} {length : Nat}
    (first second : Trace (encodeProgram program) length)
    (leftErased : VestigeErasures left leftPruned) (rightErased : VestigeErasures right rightPruned)
    (leftRelated : @StageSimulation.Related Name Key A Code _ (TypedCoeffectReplay.setoid observe) Eq
      leftPruned (first.state length))
    (rightRelated : @StageSimulation.Related Name Key A Code _ (TypedCoeffectReplay.setoid observe) Eq
      rightPruned (second.state length))
    (stable : ChildContinuations (encodeProgram program))
    (firstOpen : ¬ Nonempty (ClosedEpisode first)) (secondOpen : ¬ Nonempty (ClosedEpisode second))
    (firstQuiet : Progress.Quiet (first.state length)) (secondQuiet : Progress.Quiet (second.state length))
    (ordered : ∀ cut, cut < length → addressedEventAt first cut = addressedEventAt second cut) :
    EndpointAgreement observe left right :=
  compare_normalized_endpoints observe first second leftErased rightErased leftRelated rightRelated stable
    (open_events_of_ordered_addresses first second firstOpen secondOpen firstQuiet secondQuiet ordered)

/-- Confluence for equal surviving addressed inputs when one reduction
can execute all its commands before activating. The other reduction can
start with any legal schedule. Endpoint agreement includes the permitted
vestige erasures of the two original histories. -/
theorem compare_command_first_endpoints (observe : ∀ key, Setoid (V key))
    {left right leftPruned rightPruned : R} {firstLength secondLength split : Nat}
    (first : Trace (encodeProgram program) firstLength) (second : Trace (encodeProgram program) secondLength)
    (bounded : split ≤ firstLength)
    (leftErased : VestigeErasures left leftPruned) (rightErased : VestigeErasures right rightPruned)
    (leftRelated : @StageSimulation.Related Name Key A Code _ (TypedCoeffectReplay.setoid observe) Eq
      leftPruned (first.state firstLength))
    (rightRelated : @StageSimulation.Related Name Key A Code _ (TypedCoeffectReplay.setoid observe) Eq
      rightPruned (second.state secondLength))
    (stable : ChildContinuations (encodeProgram program))
    (firstOpen : ¬ Nonempty (ClosedEpisode first)) (secondOpen : ¬ Nonempty (ClosedEpisode second))
    (firstQuiet : Progress.Quiet (first.state firstLength)) (secondQuiet : Progress.Quiet (second.state secondLength))
    (input : orchestrationInput first = orchestrationInput second)
    (prefixCommands : ∀ cut, cut < split → ∃ cmd, first.event cut = .command cmd)
    (suffixActivations : ∀ cut, split ≤ cut → cut < firstLength → ∃ kind name, first.event cut = .lifecycle kind name)
    (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r) : EndpointAgreement observe left right := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  obtain ⟨moved, _, sameLength, _, _, matchesAtEnd, _, movedRelated, _, _, _⟩ :=
    GuardedActivationAlignment.align_commands_first first second bounded firstOpen firstQuiet secondOpen secondQuiet
      stable input prefixCommands suffixActivations observe recovery commutative respect
  have alignedRight := StageSimulation.Related.trans (Q := Eq) (fun a b => a.trans b) rightRelated movedRelated
  exact compare_at_cut observe first moved leftErased rightErased leftRelated (sameLength.symm ▸ alignedRight) matchesAtEnd

/-- Confluence for arbitrary surviving schedules with equal addressed
commands, under a sufficient supply of fresh names. Both original quiet
endpoints may first be pruned by the justified vestige erasures. -/
theorem compare_surviving_endpoints_with_spare_names (observe : ∀ key, Setoid (V key))
    {left right leftPruned rightPruned : R} {firstLength secondLength : Nat}
    (first : Trace (encodeProgram program) firstLength) (second : Trace (encodeProgram program) secondLength)
    (leftErased : VestigeErasures left leftPruned) (rightErased : VestigeErasures right rightPruned)
    (leftRelated : @StageSimulation.Related Name Key A Code _ (TypedCoeffectReplay.setoid observe) Eq
      leftPruned (first.state firstLength))
    (rightRelated : @StageSimulation.Related Name Key A Code _ (TypedCoeffectReplay.setoid observe) Eq
      rightPruned (second.state secondLength))
    (stable : ChildContinuations (encodeProgram program))
    (firstOpen : ¬ Nonempty (ClosedEpisode first)) (secondOpen : ¬ Nonempty (ClosedEpisode second))
    (firstQuiet : Progress.Quiet (first.state firstLength)) (secondQuiet : Progress.Quiet (second.state secondLength))
    (input : orchestrationInput first = orchestrationInput second)
    (supply : ∀ used : List Name, ∃ spare, spare ∉ used)
    (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r) : EndpointAgreement observe left right := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  obtain ⟨moved, sameLength, ⟨_, registry, _, _⟩, _, _, endpoint, _, _, _, _⟩ :=
    GuardedCompleteAlignment.align_surviving_schedules_with_spare_names first second firstOpen firstQuiet secondOpen
      secondQuiet stable input supply observe recovery commutative respect
  have matched : ProjectedAgreement (first.state firstLength) (moved.state secondLength) := by
    rw [← congrArg moved.state sameLength]
    exact .of_rename_eq registry
  have before : ProjectedAgreement leftPruned (moved.state secondLength) :=
    (ProjectedAgreement.of_related leftRelated).trans matched
  have after : ProjectedAgreement rightPruned (moved.state secondLength) :=
    (ProjectedAgreement.of_related rightRelated).trans endpoint
  obtain ⟨names, compared⟩ := before.trans after.symm
  exact ⟨names, leftPruned, rightPruned, leftErased, rightErased, compared⟩

/-- Endpoint confluence for equal addressed commands on the two surviving
histories. The original name set is arbitrary, and the permitted vestige
erasures are taken on the original endpoints. -/
theorem compare_surviving_endpoints (observe : ∀ key, Setoid (V key))
    {left right leftPruned rightPruned : R} {firstLength secondLength : Nat}
    (first : Trace (encodeProgram program) firstLength) (second : Trace (encodeProgram program) secondLength)
    (leftErased : VestigeErasures left leftPruned) (rightErased : VestigeErasures right rightPruned)
    (leftRelated : @StageSimulation.Related Name Key A Code _ (TypedCoeffectReplay.setoid observe) Eq
      leftPruned (first.state firstLength))
    (rightRelated : @StageSimulation.Related Name Key A Code _ (TypedCoeffectReplay.setoid observe) Eq
      rightPruned (second.state secondLength))
    (stable : ChildContinuations (encodeProgram program))
    (firstOpen : ¬ Nonempty (ClosedEpisode first)) (secondOpen : ¬ Nonempty (ClosedEpisode second))
    (firstQuiet : Progress.Quiet (first.state firstLength)) (secondQuiet : Progress.Quiet (second.state secondLength))
    (input : orchestrationInput first = orchestrationInput second)
    (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r) : EndpointAgreement observe left right ∧
      (GuardedAddressSchedule.addressedEvents first).Perm (GuardedAddressSchedule.addressedEvents second) := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  obtain ⟨leftMoved, rightMoved, sameLength, order, _, leftPath, rightPath⟩ :=
    GuardedNameExtension.align_open_histories_in_original_names first second firstOpen firstQuiet secondOpen secondQuiet
      stable input observe recovery commutative respect
  subst secondLength
  obtain ⟨leftOpen, leftQuiet⟩ := leftPath.open_quiet firstOpen firstQuiet
  obtain ⟨rightOpen, rightQuiet⟩ := rightPath.open_quiet secondOpen secondQuiet
  have redraw := GuardedCompleteAlignment.path_of_same_addressed_schedule leftMoved rightMoved
    leftOpen leftQuiet rightOpen rightQuiet stable
    (leftPath.input_eq.trans (input.trans rightPath.input_eq.symm)) order
  obtain ⟨endpoints, permuted⟩ := (leftPath.trans (redraw.trans rightPath.reverse)).preserves
  exact ⟨compare_projected_endpoints observe leftErased rightErased leftRelated rightRelated endpoints, permuted.symm⟩

omit [DecidableEq Name] [DecidableEq Key] in
private theorem table_project_rename (p : Renaming.Permutation Name) (state : R) (name : Name) (key : Key) :
    tableAt (Renaming.registry p (project state)) (p.toFun name) key = tableAt state name key := by
  unfold tableAt
  rw [Renaming.registry_at]
  cases found : state name <;> simp [project, projectFiber, Renaming.fiber, found]

/-- The table observation on the original endpoints follows with the
same permutation. Justified erasures preserve every binding. -/
theorem EndpointAgreement.tables (observe : ∀ key, Setoid (V key)) {left right : R}
    (agrees : EndpointAgreement observe left right) :
    ∃ p : Renaming.Permutation Name, ∀ name key,
      OptionRel (TypedCoeffectReplay.setoid observe).r (tableAt left name key) (tableAt right (p.toFun name) key) := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  obtain ⟨names, leftPruned, rightPruned, leftErased, rightErased, compared⟩ := agrees
  refine ⟨names, fun name key => ?_⟩
  have rows := compared (names.toFun name)
  have table : OptionRel (TypedCoeffectReplay.setoid observe).r
      (tableAt (Renaming.registry names (project leftPruned)) (names.toFun name) key)
      (tableAt (project rightPruned) (names.toFun name) key) := by
    cases l : Renaming.registry names (project leftPruned) (names.toFun name) <;>
      cases r : project rightPruned (names.toFun name) <;>
      simp only [tableAt, l, r, Option.bind_none, Option.bind_some, OptionRel] at rows ⊢
    exact rows.table key
  have rightTable : tableAt (project rightPruned) (names.toFun name) key = tableAt rightPruned (names.toFun name) key := by
    unfold tableAt
    cases found : rightPruned (names.toFun name) <;> simp [project, projectFiber, found]
  rwa [table_project_rename, rightTable, leftErased.table_at, rightErased.table_at] at table

theorem EndpointAgreement.paper_tables (observe : ∀ key, Setoid (V key)) {left right : R}
    (agrees : EndpointAgreement observe left right) :
    PaperStateObservation.TablesRelatedAt (fun _ => TypedCoeffectReplay.setoid observe) (fun _ => True) left right := by
  obtain ⟨names, matched⟩ := agrees.tables observe
  intro key _
  constructor
  · intro name value present
    have related := matched name key
    rw [present] at related
    cases found : tableAt right (names.toFun name) key with
    | none => simp [found, OptionRel] at related
    | some other => exact ⟨names.toFun name, other, found, by simpa only [found, OptionRel] using related⟩
  · intro name value present
    obtain ⟨old, rfl⟩ := names.surjective name
    have related := matched old key
    rw [present] at related
    cases found : tableAt left old key with
    | none => simp [found, OptionRel] at related
    | some other => exact ⟨old, other, found, by simpa only [found, OptionRel] using related⟩

end Cordis.Repairs.GuardedConfluence
