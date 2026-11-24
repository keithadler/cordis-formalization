import Cordis.TranspositionBirth

/-! Primitive table rows for Lemma78(1). Undeclared-key separation is a local
component property derived by `simultaneous_separation`; no whole-registry
commuting map or swapped landing is assumed. -/
namespace Cordis.Transposition
open Calculus Stages Labeled
universe u
variable {Name Key Value Code Error : Type u}
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
variable [DecidableEq Name] [DecidableEq Key]
set_option linter.unusedSectionVars false

theorem write_routing (r : R) (owner actor : Name) (key query : Key) (value : Option Value) :
    GuardedApplications.routing (write r owner key value) actor query =
      GuardedApplications.routing r actor query := by
  by_cases same : actor = owner
  · subst actor
    cases found : r owner <;> simp [Stages.bindingOwner, write, Calculus.modify, found]
  · simp [Stages.bindingOwner, write, Calculus.modify, same]

theorem tableAt_write_away (r : R) (owner actor : Name) (key query : Key) (value : Option Value)
    (different : actor ≠ owner ∨ query ≠ key) :
    StageRecovery.tableAt (write r owner key value) actor query = StageRecovery.tableAt r actor query := by
  rcases different with different | different
  · simp [StageRecovery.tableAt, write, Calculus.modify, different]
  · by_cases same : actor = owner
    · subst actor
      cases found : r owner <;> simp [StageRecovery.tableAt, write, Calculus.modify, found, different]
    · simp [StageRecovery.tableAt, write, Calculus.modify, same]

theorem location_write_other_key (r : R) (owner actor : Name) (key query : Key) (value : Option Value)
    (different : query ≠ key) : location (write r owner key value) actor query = location r actor query := by
  rw [GuardedApplications.location_routing, GuardedApplications.location_routing, write_routing]
  congr 1
  funext selected
  rw [tableAt_write_away r owner selected key query value (.inr different)]

theorem writes_commute (r : R) (first second : Name) (key query : Key) (left right : Option Value)
    (different : first ≠ second ∨ key ≠ query) :
    write (write r first key left) second query right = write (write r second query right) first key left := by
  funext owner
  by_cases atFirst : owner = first <;> by_cases atSecond : owner = second
  · subst owner
    have keys : key ≠ query := different.resolve_left (fun unequal => unequal atSecond)
    subst second
    cases found : r first with
    | none => simp [write, Calculus.modify, found]
    | some fiber =>
      have tables : (fun k => if k = query then right else if k = key then left else fiber.table k) =
          (fun k => if k = key then left else if k = query then right else fiber.table k) := by
        funext k
        by_cases one : k = key <;> by_cases two : k = query <;> simp_all
      simpa [write, Calculus.modify, found] using
        congrArg (fun table => some ({fiber with table := table} : F)) tables
  · simp_all [write, Calculus.modify]
  · simp_all [write, Calculus.modify]
  · simp_all [write, Calculus.modify]

theorem write_insertable (r : R) (owner child : Name) (key : Key) (value : Option Value)
    (component : Component Key Code) (parent : Option Name) :
    Insertable (write r owner key value) child component parent ↔ Insertable r child component parent := by
  have presence : ∀ n, write r owner key value n = none ↔ r n = none := by
    intro n
    by_cases same : n = owner <;> simp [write, Calculus.modify, same]
  unfold Insertable
  apply and_congr (presence child)
  apply and_congr
  · apply forall_congr'; intro p
    exact imp_congr_right (fun _ => not_congr (presence p))
  · apply forall_congr'; intro other
    apply forall_congr'; intro query
    by_cases same : other = owner
    · subst other
      cases found : r owner <;> simp [write, Calculus.modify, found]
    · simp [write, Calculus.modify, same]

theorem undeclared_location (r : R) (actor : Name) (fiber : F) (found : r actor = some fiber)
    (key : Key) (unprovided : fiber.component.provides key = false) (unrequired : fiber.component.requires key = false) :
    location r actor key = none := by
  simp [location, Stages.bindingOwner, found, unprovided, unrequired]

/-- All successful operations resolve a declared key; an undeclared coordinate
cannot secretly supply a callback merely because a binding exists there. -/
theorem operation_key_different (r : R) (actor owner : Name) (fiber : F) (found : r actor = some fiber)
    (key query : Key) (unprovided : fiber.component.provides key = false)
    (unrequired : fiber.component.requires key = false) (before : Value)
    (located : location r actor query = some (owner, before)) : query ≠ key := by
  intro same
  subst query
  rw [undeclared_location r actor fiber found key unprovided unrequired] at located
  cases located

/-- A foreign primitive preserves every table's coordinate at a key the
acting component neither provides nor requires. Birth creates an empty table
and therefore satisfies the same literal coordinate equality. -/
theorem land_undeclared_table (program : Code → Instruction Name Key Value Code Error)
    {actor : Name} {code : Code} {r s : R} {inverse next}
    (land : Land program actor code r s inverse next)
    (fiber : F) (found : r actor = some fiber) (key : Key)
    (unprovided : fiber.component.provides key = false) (unrequired : fiber.component.requires key = false)
    (owner : Name) : StageRecovery.tableAt s owner key = StageRecovery.tableAt r owner key := by
  cases land with
  | unit => rfl
  | provide _ _ _ entry query value action present declared absent =>
    have same : entry = fiber := Option.some.inj (present.symm.trans found)
    subst entry
    have different : key ≠ query := by intro same; subst query; simp [unprovided] at declared
    exact tableAt_write_away r actor owner query key (some value) (.inr different)
  | operate _ _ _ query run selected before after inv result action located called =>
    have different := operation_key_different r actor selected fiber found key query unprovided unrequired before located
    exact tableAt_write_away r selected owner query key (some after) (.inr (Ne.symm different))
  | instantiate _ _ _ component child action ready =>
    exact fresh_put_tables r child component (some actor) ready.1 owner key

/-- A write at an undeclared key can be moved through the complete selected
primitive. Presence of the written owner excludes creation of that same name;
successful callbacks and both kinds of outcomes are retained literally. -/
theorem land_write_undeclared (program : Code → Instruction Name Key Value Code Error)
    {actor : Name} {code : Code} {r s : R} {inverse next}
    (land : Land program actor code r s inverse next)
    (fiber : F) (found : r actor = some fiber) (owner : Name) (different : actor ≠ owner)
    (ownerPresent : r owner ≠ none) (key : Key) (value : Option Value)
    (unprovided : fiber.component.provides key = false) (unrequired : fiber.component.requires key = false) :
    Land program actor code (write r owner key value) (write s owner key value) inverse next := by
  cases land with
  | unit _ _ _ action => exact .unit _ _ _ action
  | provide _ _ _ entry query offered action present declared absent =>
    rw [writes_commute r actor owner query key (some offered) value (.inl different)]
    exact .provide _ _ _ entry query offered action
      (by simpa [write, Calculus.modify, different] using present) declared absent
  | operate _ _ _ query run selected before after inv result action located called =>
    have keys := operation_key_different r actor selected fiber found key query unprovided unrequired before located
    rw [writes_commute r selected owner query key (some after) value (.inr keys)]
    exact .operate _ _ _ query run selected before after inv result action
      ((location_write_other_key r owner actor key query value keys).trans located) called
  | instantiate _ _ _ component child action ready =>
    have freshName : owner ≠ child := by intro same; exact ownerPresent (same ▸ ready.1)
    rw [write_put r owner child _ key value freshName]
    exact .instantiate _ _ _ component child action ((write_insertable r owner child key value component (some actor)).mpr ready)

theorem write_twice (r : R) (owner : Name) (key : Key) (first second : Option Value) :
    write (write r owner key first) owner key second = write r owner key second := by
  funext name
  by_cases same : name = owner
  · subst name
    cases found : r owner with
    | none => simp [write, Calculus.modify, found]
    | some fiber =>
      simp [write, Calculus.modify, found]
      funext k
      by_cases same : k = key <;> simp [same]
  · simp [write, Calculus.modify, same]

theorem write_existing (r : R) (owner : Name) (fiber : F) (found : r owner = some fiber) (key : Key) :
    write r owner key (fiber.table key) = r := by
  funext name
  by_cases same : name = owner
  · subst name
    have tableSame : (fun k => if k = key then fiber.table key else fiber.table k) = fiber.table := by
      funext k
      by_cases equal : k = key <;> simp_all
    simp [write, Calculus.modify, found, tableSame]
  · simp [write, Calculus.modify, same]

/-- Provision followed by any foreign primitive at a component which does not
declare that provision key. Swapped applicability is reconstructed by deleting
the just-added binding, then reinstalling it at the end. This uses the exact
actual returned inverse and continuation, including a child-name branch. -/
theorem provision_landing_diamond (program : Code → Instruction Name Key Value Code Error)
    (r : R) (provider actor : Name) (providerFiber actorFiber : F)
    (providerFound : r provider = some providerFiber) (actorFound : r actor = some actorFiber)
    (different : actor ≠ provider) (key : Key) (value : Value) (firstCode secondCode : Code)
    (action : (program firstCode).action = .provide key value)
    (declared : providerFiber.component.provides key = true) (absent : providerFiber.table key = none)
    (unprovided : actorFiber.component.provides key = false) (unrequired : actorFiber.component.requires key = false)
    {s : R} {inverse next}
    (landing : Land program actor secondCode (write r provider key (some value)) s inverse next) :
    ∃ middle, Land program actor secondCode r middle inverse next ∧
      Land program provider firstCode middle s (.restrict provider key) ((program firstCode).next (.value value)) := by
  let offered : F := {providerFiber with table := fun k => if k = key then some value else providerFiber.table k}
  have offeredFound : write r provider key (some value) provider = some offered := by
    simp [write, Calculus.modify, providerFound, offered]
  have actorRetained : write r provider key (some value) actor = some actorFiber := by
    simpa [write, Calculus.modify, different] using actorFound
  have restored : write (write r provider key (some value)) provider key none = r := by
    rw [write_twice, ← absent]
    exact write_existing r provider providerFiber providerFound key
  have swapped := land_write_undeclared program landing actorFiber actorRetained provider different
    (by simp [offeredFound]) key none unprovided unrequired
  rw [restored] at swapped
  obtain ⟨table, currentFound⟩ := land_existing_table program landing provider offered offeredFound
  have retainedKey := land_undeclared_table program landing actorFiber actorRetained key unprovided unrequired provider
  have keyPresent : table key = some value := by
    simpa [StageRecovery.tableAt, currentFound, offeredFound, offered] using retainedKey
  let current : F := {offered with table := table}
  let cleared : F := {current with table := fun k => if k = key then none else current.table k}
  have clearFound : write s provider key none provider = some cleared := by
    simp [write, Calculus.modify, currentFound, cleared, current]
  have reinstated : write (write s provider key none) provider key (some value) = s := by
    rw [write_twice, ← keyPresent]
    exact write_existing s provider current currentFound key
  refine ⟨write s provider key none, swapped, ?_⟩
  have provided : Land program provider firstCode (write s provider key none)
      (write (write s provider key none) provider key (some value))
      (.restrict provider key) ((program firstCode).next (.value value)) :=
    .provide _ provider firstCode cleared key value action clearFound declared (by simp [cleared])
  simpa only [reinstated] using provided

/-- The opposite provision order. The later empty-slot guard is transported
backwards by the proved undeclared-coordinate frame, and the forward swapped
primitive is constructed by `land_write_undeclared`. -/
theorem landing_provision_diamond (program : Code → Instruction Name Key Value Code Error)
    {actor : Name} {firstCode : Code} {r s : R} {inverse next}
    (landing : Land program actor firstCode r s inverse next)
    (provider : Name) (actorFiber providerFiber current : F)
    (actorFound : r actor = some actorFiber) (providerFound : r provider = some providerFiber)
    (currentFound : s provider = some current) (different : actor ≠ provider)
    (key : Key) (value : Value) (secondCode : Code)
    (action : (program secondCode).action = .provide key value)
    (declared : current.component.provides key = true) (absent : current.table key = none)
    (unprovided : actorFiber.component.provides key = false) (unrequired : actorFiber.component.requires key = false) :
    ∃ middle, Land program provider secondCode r middle (.restrict provider key) ((program secondCode).next (.value value)) ∧
      Land program actor firstCode middle (write s provider key (some value)) inverse next := by
  obtain ⟨table, retained⟩ := land_existing_table program landing provider providerFiber providerFound
  have same : {providerFiber with table := table} = current := Option.some.inj (retained.symm.trans currentFound)
  have originalDeclared : providerFiber.component.provides key = true := by
    have componentEq := congrArg Fiber.component same
    simpa only [← componentEq] using declared
  have preserved := land_undeclared_table program landing actorFiber actorFound key unprovided unrequired provider
  have originalAbsent : providerFiber.table key = none := by
    simpa [StageRecovery.tableAt, currentFound, providerFound, absent] using preserved.symm
  exact ⟨write r provider key (some value),
    .provide r provider secondCode providerFiber key value action providerFound originalDeclared originalAbsent,
    land_write_undeclared program landing actorFiber actorFound provider different
      (by simp [providerFound]) key (some value) unprovided unrequired⟩

end Cordis.Transposition
