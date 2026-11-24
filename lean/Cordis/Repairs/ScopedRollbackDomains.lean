import Cordis.Repairs.ScopedEffects

/-! Domains retained throughout one iterator calculation. Landings can
add a fresh child. Their saved inverses can retire children. Both kinds
of map preserve the component, parent, and phase of every existing row. -/
namespace Cordis.Repairs.ScopedRollback
open TypedRegistry ScopedEffects
open PaperEffectEquations (CoeffectOperations)
universe u
variable {Name Key Code : Type u} {V : Key → Type u}
variable [DecidableEq Name] [DecidableEq Key] {ops : CoeffectOperations V}
local notation "R" => Registry Name V Code
local notation "F" => Fiber Name V Code
local notation "I" => Inverse Name V

structure Keeps (ops : CoeffectOperations V) (before after : R) : Prop where
  allowed : CompatibleProvision.Allowed ops before → CompatibleProvision.Allowed ops after
  row : ∀ name old, before name = some old →
    ∃ current, after name = some current ∧ current.component = old.component ∧
      current.parent = old.parent ∧ current.phase.committed = old.phase.committed

structure Stable (ops : CoeffectOperations V) (domain : R → Prop) : Prop where
  land : ∀ {program : Code → Instruction Name ops Code} {actor code before after token next},
    Land program actor code before after token next → domain before → domain after
  undo : ∀ token state, domain state → domain (TypedRegistry.undo token state)

namespace Keeps

omit [DecidableEq Name] in
theorem refl (ops : CoeffectOperations V) (state : R) : Keeps ops state state :=
  ⟨fun old => old, fun _ row atRow => ⟨row, atRow, rfl, rfl, rfl⟩⟩

omit [DecidableEq Name] in
theorem trans {before middle after : R} (first : Keeps ops before middle) (second : Keeps ops middle after) :
    Keeps ops before after := by
  refine ⟨fun old => second.allowed (first.allowed old), ?_⟩
  intro name row found
  obtain ⟨mid, atMid, comp, par, phase⟩ := first.row name row found
  obtain ⟨last, atLast, comp', par', phase'⟩ := second.row name mid atMid
  exact ⟨last, atLast, comp'.trans comp, par'.trans par, phase'.trans phase⟩

omit [DecidableEq Key] in
private theorem modify_rows (state : R) (owner : Name) (change : F → F)
    (component : ∀ fiber, (change fiber).component = fiber.component)
    (parent : ∀ fiber, (change fiber).parent = fiber.parent)
    (committed : ∀ fiber, (change fiber).phase.committed = fiber.phase.committed) :
    ∀ name old, state name = some old →
      ∃ current, modify state owner change name = some current ∧ current.component = old.component ∧
        current.parent = old.parent ∧ current.phase.committed = old.phase.committed := by
  intro name old found
  by_cases same : name = owner
  · subst owner
    exact ⟨change old, by simp [TypedRegistry.modify, found], component old, parent old, committed old⟩
  · exact ⟨old, by simpa only [TypedRegistry.modify, if_neg same] using found, rfl, rfl, rfl⟩

theorem land {program : Code → Instruction Name ops Code}
    {actor : Name} {code : Code} {before after : R} {token : I} {next : Option Code}
    (step : Land program actor code before after token next) : Keeps ops before after := by
  refine ⟨MediatedRegistry.landing_allowed _ (land_encode ops step), ?_⟩
  cases step with
  | unit => exact fun name old found => ⟨old, found, rfl, rfl, rfl⟩
  | provide => exact modify_rows _ _ _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  | operate => exact modify_rows _ _ _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  | instantiate state actor code component child _ ready =>
    intro name old found
    have different : name ≠ child := by
      intro equal
      subst name
      rw [ready.1] at found
      cases found
    exact ⟨old, by simpa only [put, if_neg different] using found, rfl, rfl, rfl⟩

theorem undo (ops : CoeffectOperations V) (token : I) (state : R) :
    Keeps ops state (TypedRegistry.undo token state) := by
  refine ⟨?_, ?_⟩
  · intro allowed
    change MediatedRegistry.Allowed (encodeRegistry ops (TypedRegistry.undo token state))
    rw [encode_undo]
    exact MediatedRegistry.inverse_allowed _ allowed
  · cases token with
    | unit => exact fun name old found => ⟨old, found, rfl, rfl, rfl⟩
    | restrict | operate | retire =>
      exact modify_rows _ _ _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

omit [DecidableEq Name] in
theorem bindingOwner {before after : R} (kept : Keeps ops before after)
    {actor : Name} {row : F} (found : before actor = some row) (key : Key) :
    TypedRegistry.bindingOwner after actor key = TypedRegistry.bindingOwner before actor key := by
  obtain ⟨current, present, component, _, phase⟩ := kept.row actor row found
  simp [TypedRegistry.bindingOwner, found, present, component, phase]

omit [DecidableEq Name] in
theorem compatible {before after : R} (kept : Keeps ops before after)
    {actor : Name} {component : Calculus.Component Key Code}
    (old : CompatibleProvision.Compatible ops actor component before) :
    CompatibleProvision.Compatible ops actor component after := by
  obtain ⟨row, found, fields⟩ := old.2
  obtain ⟨current, present, component, _, _⟩ := kept.row actor row found
  exact ⟨kept.allowed old.1, current, present, component.trans fields⟩

omit [DecidableEq Name] in
theorem bound {before after : R} (kept : Keeps ops before after)
    {actor owner : Name} {acting providing : Calculus.Component Key Code} {key : Key}
    (old : BoundOperation.Compatible ops actor acting owner providing key before) :
    BoundOperation.Compatible ops actor acting owner providing key after := by
  obtain ⟨row, found, _⟩ := old.1.2
  exact ⟨kept.compatible old.1, kept.compatible old.2.1, (kept.bindingOwner found key).trans old.2.2⟩

omit [DecidableEq Name] in
theorem allocated {before after : R} (kept : Keeps ops before after)
    {actor child : Name} {acting payload : Calculus.Component Key Code}
    (old : CompatibleProvision.Compatible ops actor acting before ∧
      ∃ row, before child = some row ∧ row.component = payload ∧ row.parent = some actor) :
    CompatibleProvision.Compatible ops actor acting after ∧
      ∃ row, after child = some row ∧ row.component = payload ∧ row.parent = some actor := by
  obtain ⟨row, found, component, parent⟩ := old.2
  obtain ⟨current, present, sameComponent, sameParent, _⟩ := kept.row child row found
  exact ⟨kept.compatible old.1, current, present, sameComponent.trans component, sameParent.trans parent⟩

end Keeps

namespace Stable

private theorem ofKeeps {domain : Registry Name V Code → Prop}
    (keeps : ∀ ⦃before after : R⦄, Keeps ops before after → domain before → domain after) :
    Stable ops domain :=
  ⟨fun landed => keeps (Keeps.land landed), fun token state => keeps (Keeps.undo ops token state)⟩

theorem true (ops : CoeffectOperations V) : Stable ops (fun _ : R => True) :=
  ⟨fun _ old => old, fun _ _ old => old⟩

theorem and {first second : R → Prop} (left : Stable ops first) (right : Stable ops second) :
    Stable ops (fun state => first state ∧ second state) :=
  ⟨fun landed old => ⟨left.land landed old.1, right.land landed old.2⟩,
    fun token state old => ⟨left.undo token state old.1, right.undo token state old.2⟩⟩

theorem provision (ops : CoeffectOperations V) (actor : Name) (component : Calculus.Component Key Code) :
    Stable ops (CompatibleProvision.Compatible ops actor component) :=
  ofKeeps (fun _ _ kept old => kept.compatible old)

theorem operate (ops : CoeffectOperations V) (actor owner : Name)
    (acting providing : Calculus.Component Key Code) (key : Key) :
    Stable ops (BoundOperation.Compatible ops actor acting owner providing key) :=
  ofKeeps (fun _ _ kept old => kept.bound old)

theorem allocate (ops : CoeffectOperations V) (actor child : Name) (acting payload : Calculus.Component Key Code) :
    Stable ops (fun state : R => CompatibleProvision.Compatible ops actor acting state ∧
      ∃ row, state child = some row ∧ row.component = payload ∧ row.parent = some actor) :=
  ofKeeps (fun _ _ kept old => kept.allocated old)

end Stable
end Cordis.Repairs.ScopedRollback
