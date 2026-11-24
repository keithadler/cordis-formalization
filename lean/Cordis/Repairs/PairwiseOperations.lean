import Cordis.DependentCoeffectExchange
import Cordis.Repairs.BoundOperation

/-! The ordinary coeffect case of Definition 65. Actual typed forward calls
and defined saved inverse applications can change the binding read by a
second actor. Definition 44 and Equation (41) determine what it still yields. -/
namespace Cordis.Repairs.PairwiseOperations
open TypedRegistry
open PaperEffectEquations (CoeffectOperations)
open PartialCoeffectLifting (PartialMap forward)
open PartialCoeffectIndependenceContracts (OperationGenerator tableSetoid)
open PartialInverseObservation (MapRelated)
open PartialMapClosure (Generated)
open Iterators (OptionRel)

universe u
variable {Name Key Code : Type u} {V : Key → Type u} [DecidableEq Name] [DecidableEq Key]
variable {ops : CoeffectOperations V}
local notation "R" => Registry Name V Code
local notation "I" => Inverse Name V

omit [DecidableEq Name] [DecidableEq Key] in
theorem table_and_route {state : R} {actor owner : Name} {key : Key} {value : V key}
    (located : location state actor key = some (owner, value)) :
    bindingOwner state actor key = some owner ∧ tableAt state owner key = some value := by
  obtain ⟨selected, route, binding⟩ := Option.bind_eq_some_iff.mp located
  obtain ⟨loaded, bound, pair⟩ := Option.map_eq_some_iff.mp binding
  cases pair
  exact ⟨route, bound⟩

theorem location_write_here {state : R} {actor owner : Name} {key : Key} {value : V key}
    (located : location state actor key = some (owner, value)) (changed : V key) :
    location (write state owner key (some changed)) actor key = some (owner, changed) := by
  obtain ⟨route, bound⟩ := table_and_route located
  have changedBound : tableAt (write state owner key (some changed)) owner key = some changed := by
    cases found : state owner with
    | none => simp [tableAt, found] at bound
    | some row => simp [tableAt, write, TypedRegistry.modify, found]
  unfold location
  rw [BoundOperation.write_bindingOwner, route]
  simp [changedBound]

private theorem location_write_away {state : R} {actor owner editor : Name} {key changed : Key}
    {value : V key} (located : location state actor key = some (owner, value))
    (away : owner ≠ editor ∨ key ≠ changed) (written : Option (V changed)) :
    location (write state editor changed written) actor key = some (owner, value) := by
  obtain ⟨route, bound⟩ := table_and_route located
  have kept : tableAt (write state editor changed written) owner key = some value := by
    rcases away with other | otherKey
    · simpa [tableAt, write, TypedRegistry.modify, other] using bound
    · by_cases same : owner = editor
      · subst editor
        cases found : state owner with
        | none => simp [tableAt, found] at bound
        | some row => simpa [tableAt, write, TypedRegistry.modify, found, Ne.symm otherKey] using bound
      · simpa [tableAt, write, TypedRegistry.modify, same] using bound
  simp [location, BoundOperation.write_bindingOwner, route, kept]

omit [DecidableEq Key] in
private theorem location_after_insert {state : R} {actor owner child : Name} {key : Key} {value : V key}
    (located : location state actor key = some (owner, value)) (absent : state child = none)
    (row : Fiber Name V Code) : location (put state child row) actor key = some (owner, value) := by
  obtain ⟨route, bound⟩ := table_and_route located
  have distinctActor : actor ≠ child := by
    intro same
    subst child
    simp [bindingOwner, absent] at route
  have distinctOwner : owner ≠ child := by
    intro same
    subst child
    simp [tableAt, absent] at bound
  have keptRoute : bindingOwner (put state child row) actor key = some owner := by
    simpa [bindingOwner, put, distinctActor] using route
  have keptBound : tableAt (put state child row) owner key = some value := by
    simpa [tableAt, put, distinctOwner] using bound
  simp [location, keptRoute, keptBound]

omit [DecidableEq Name] [DecidableEq Key] in
theorem declared_route {state : R} {actor owner : Name} {key : Key}
    {row : Fiber Name V Code} (found : state actor = some row)
    (route : bindingOwner state actor key = some owner) :
    row.component.provides key = true ∨ row.component.requires key = true := by
  by_cases provided : row.component.provides key = true
  · exact .inl provided
  · by_cases required : row.component.requires key = true
    · exact .inr required
    · simp [bindingOwner, found, provided, required] at route

omit [DecidableEq Name] [DecidableEq Key] in
theorem declared_key {state : R} {actor owner : Name} {key : Key} {value : V key}
    {row : Fiber Name V Code} (found : state actor = some row)
    (located : location state actor key = some (owner, value)) :
    row.component.provides key = true ∨ row.component.requires key = true :=
  declared_route found (table_and_route located).1

theorem undo_operate_eq_write {state : R} {owner : Name} {key : Key}
    {value changed : V key} {inverse : PartialMap (V key)}
    (bound : tableAt state owner key = some value) (called : inverse value = some changed) :
    undo (.operate owner key inverse) state = write state owner key (some changed) := by
  cases found : state owner with
  | none => simp [tableAt, found] at bound
  | some row =>
    have table : row.table key = some value := by simpa [tableAt, found] using bound
    funext query
    by_cases same : query = owner
    · subst query
      simp [undo, write, TypedRegistry.modify, found, table, called]
    · simp [undo, write, TypedRegistry.modify, same]

/-- A finite successful word at a retained binding leaves the local
instruction's typed outcome and partial inverse observation intact. -/
theorem rerun_after_routed_word (observe : ∀ key, Setoid (V key)) (program : Code → Instruction Name ops Code)
    {state : R} {actor owner : Name} {key : Key} {code : Code} {name : ops.Name key}
    {arg : ops.Argument key name} {before output changed : V key} {inverse : PartialMap (V key)}
    {outcome : ops.Outcome key name} {move : PartialMap (V key)}
    (action : (program code).action = .operate key name arg)
    (located : location state actor key = some (owner, changed))
    (returned : (ops.operation key name arg).run before = some (output, inverse, outcome))
    (laws : PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (generated : Generated (fun map => ∃ foreignName foreignArg,
      OperationGenerator (ops.operation key foreignName foreignArg) map) move)
    (moved : move before = some changed) :
    ∃ after, ∃ newInverse : PartialMap (V key),
      Land program actor code state after (.operate owner key newInverse)
        ((program code).next (.operation key name outcome)) ∧
      MapRelated (observe key).r newInverse inverse := by
  have yield := DependentCoeffectExchange.yield_after_generated_at_key ops observe key name arg laws generated moved
  rw [returned] at yield
  cases called : (ops.operation key name arg).run changed with
  | none => simp [called, OptionRel] at yield
  | some result =>
    obtain ⟨newValue, newInverse, newOutcome⟩ := result
    rw [called] at yield
    have same : newOutcome = outcome := yield.2
    subst newOutcome
    exact ⟨_, newInverse, .operate _ _ _ _ _ _ _ _ _ _ _ action located called, yield.1⟩

/-- Project a real foreign primitive to the location of the local operation.
An actual binding remains at the same route. Only a foreign operation on
that very slot contributes a nonidentity coeffect generator. For a foreign
provision the actors' separated interfaces rule out sharing the slot. -/
theorem foreign_landing_at_location {program : Code → Instruction Name ops Code}
    {before after : R} {actor owner foreignActor : Name} {foreignCode : Code} {key : Key} {value : V key}
    {reader provider : Fiber Name V Code} {token : I} {next : Option Code}
    (readerFound : before actor = some reader) (providerFound : before foreignActor = some provider)
    (separated : Transposition.Separated reader.component provider.component)
    (located : location before actor key = some (owner, value))
    (foreign : Land program foreignActor foreignCode before after token next) :
    ∃ changed, location after actor key = some (owner, changed) ∧
      ∃ move : PartialMap (V key), Generated (fun map => ∃ foreignName foreignArg,
        OperationGenerator (ops.operation key foreignName foreignArg) map) move ∧ move value = some changed := by
  cases foreign with
  | unit => exact ⟨value, located, some, .identity, rfl⟩
  | instantiate _ _ _ component child _ ready =>
    exact ⟨value, location_after_insert located ready.1 (fresh component (some foreignActor)), some, .identity, rfl⟩
  | provide _ _ _ row written writtenValue _ found provides _ =>
    have rowSame := Option.some.inj (found.symm.trans providerFound)
    subst row
    have away : key ≠ written := by
      intro same
      subst written
      rcases declared_key readerFound located with localProvides | localRequires
      · rw [separated.provisions key localProvides] at provides
        contradiction
      · rw [separated.right_provision key provides] at localRequires
        contradiction
    exact ⟨value, location_write_away located (.inr away) _, some, .identity, rfl⟩
  | operate _ _ _ operated foreignName foreignArg writer input output inverse result _ foreignLocated returned =>
    by_cases sameOwner : owner = writer
    · subst writer
      by_cases sameKey : key = operated
      · subst operated
        have sameInput := Option.some.inj ((table_and_route foreignLocated).2.symm.trans (table_and_route located).2)
        subst input
        exact ⟨output, location_write_here located output, forward (ops.operation key foreignName foreignArg),
          .generator ⟨foreignName, foreignArg, .forward⟩, by simp [forward, returned]⟩
      · exact ⟨value, location_write_away located (.inr sameKey) _, some, .identity, rfl⟩
    · exact ⟨value, location_write_away located (.inl sameOwner) _, some, .identity, rfl⟩

/-- The local operation head's actual partial yield, with its routed owner.
An unavailable binding or an unsuccessful typed call gives no yield. -/
def operationYield (state : R) (actor : Name) (key : Key) (name : ops.Name key)
    (arg : ops.Argument key name) : Option (Name × (PartialMap (V key) × ops.Outcome key name)) :=
  (location state actor key).bind fun (owner, input) =>
    ((ops.operation key name arg).run input).map fun (_, inverse, outcome) => (owner, inverse, outcome)

/-- While the local binding is in scope, the native foreign primitive
preserves both defined and undefined yields of the local operation. -/
theorem operation_yield_after_foreign_landing (observe : ∀ key, Setoid (V key))
    {program : Code → Instruction Name ops Code} {before after : R} {actor owner foreignActor : Name}
    {foreignCode : Code} {key : Key} {name : ops.Name key} {arg : ops.Argument key name} {input : V key}
    {reader provider : Fiber Name V Code} {token : I} {next : Option Code}
    (readerFound : before actor = some reader) (providerFound : before foreignActor = some provider)
    (separated : Transposition.Separated reader.component provider.component)
    (located : location before actor key = some (owner, input))
    (foreign : Land program foreignActor foreignCode before after token next)
    (laws : PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key) :
    OptionRel (fun new old => new.1 = old.1 ∧ MapRelated (observe key).r new.2.1 old.2.1 ∧ new.2.2 = old.2.2)
      (operationYield after actor key name arg) (operationYield before actor key name arg) := by
  obtain ⟨changed, current, move, generated, moved⟩ :=
    foreign_landing_at_location readerFound providerFound separated located foreign
  have yields := DependentCoeffectExchange.yield_after_generated_at_key ops observe key name arg laws generated moved
  unfold operationYield
  rw [current, located]
  cases new : (ops.operation key name arg).run changed <;> cases old : (ops.operation key name arg).run input
  all_goals simp only [new, old, Option.bind_some, Option.map_none, Option.map_some, OptionRel] at yields ⊢
  exact ⟨True.intro, yields⟩

/-- Reevaluate a successful local operation after any successful foreign
primitive at a separated actor. The same typed result selects the same
continuation, and the returned inverse agrees as a partial function. -/
theorem rerun_after_foreign_landing (observe : ∀ key, Setoid (V key))
    (program : Code → Instruction Name ops Code) {before middle : R} {actor owner foreignActor : Name}
    {code foreignCode : Code} {key : Key} {name : ops.Name key} {arg : ops.Argument key name}
    {input output : V key} {inverse : PartialMap (V key)} {outcome : ops.Outcome key name}
    {reader provider : Fiber Name V Code} {token : I} {next : Option Code}
    (readerFound : before actor = some reader) (providerFound : before foreignActor = some provider)
    (separated : Transposition.Separated reader.component provider.component)
    (action : (program code).action = .operate key name arg)
    (located : location before actor key = some (owner, input))
    (returned : (ops.operation key name arg).run input = some (output, inverse, outcome))
    (foreign : Land program foreignActor foreignCode before middle token next)
    (laws : PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key) :
    ∃ after, ∃ newInverse : PartialMap (V key),
      Land program actor code middle after (.operate owner key newInverse)
        ((program code).next (.operation key name outcome)) ∧
      MapRelated (observe key).r newInverse inverse := by
  obtain ⟨changed, current, move, generated, moved⟩ :=
    foreign_landing_at_location readerFound providerFound separated located foreign
  exact rerun_after_routed_word observe program action current returned laws generated moved

private theorem provision_guard_after_other_write {state : R} {actor writer : Name} {key stored : Key}
    {row : Fiber Name V Code} (found : state actor = some row) (missing : row.table key = none)
    (away : actor ≠ writer ∨ key ≠ stored) (value : Option (V stored)) :
    ∃ after, write state writer stored value actor = some after ∧ after.component = row.component ∧
      after.table key = none := by
  by_cases same : actor = writer
  · subst writer
    have otherKey : stored ≠ key := Ne.symm (away.resolve_left (fun different => different rfl))
    let after : Fiber Name V Code := { row with table := fun query =>
      if eq : stored = query then eq ▸ value else row.table query }
    exact ⟨after, by simp [write, TypedRegistry.modify, found, after], rfl, by simp [after, otherKey, missing]⟩
  · exact ⟨row, by simpa [write, TypedRegistry.modify, same] using found, rfl, missing⟩

/-- A provision that's ready before the other actor's landing is ready after
it. A foreign provision writes the other actor's row. An operation cannot
change the empty slot because it needs a binding of its own on that slot. -/
theorem rerun_provision_after_foreign_landing (program : Code → Instruction Name ops Code)
    {before middle : R} {actor foreignActor : Name} {code foreignCode : Code} {key : Key} {value : V key}
    {row : Fiber Name V Code} {token : I} {next : Option Code}
    (different : actor ≠ foreignActor) (action : (program code).action = .provide key value)
    (found : before actor = some row) (declared : row.component.provides key = true) (missing : row.table key = none)
    (foreign : Land program foreignActor foreignCode before middle token next) :
    Land program actor code middle (write middle actor key (some value)) (.restrict actor key)
      ((program code).next (.provision key value)) := by
  have applyProvision {state : R} (ready : ∃ current, state actor = some current ∧
      current.component = row.component ∧ current.table key = none) :
      Land program actor code state (write state actor key (some value)) (.restrict actor key)
        ((program code).next (.provision key value)) := by
    obtain ⟨current, present, same, empty⟩ := ready
    exact .provide state actor code current key value action present (by simpa [same] using declared) empty
  apply applyProvision
  cases foreign with
  | unit => exact ⟨row, found, rfl, missing⟩
  | provide _ _ _ _ _ _ _ _ _ _ => exact provision_guard_after_other_write found missing (.inl different) _
  | instantiate _ _ _ component child _ ready =>
    have distinct : actor ≠ child := by
      intro same
      subst child
      have absent := ready.1
      rw [found] at absent
      exact Option.noConfusion absent
    exact ⟨row, by simpa [put, distinct] using found, rfl, missing⟩
  | operate _ _ _ operated _ _ writer _ _ _ _ _ located _ =>
    have away : actor ≠ writer ∨ key ≠ operated := by
      by_cases owner : actor = writer
      · subst writer
        right
        intro same
        subst operated
        have bound := (table_and_route located).2
        simp [tableAt, found, missing] at bound
      · exact .inl owner
    exact provision_guard_after_other_write found missing away _

/-- A real successful operation landing at the first actor is a generated
foreign move for the second actor reading the same binding. -/
theorem rerun_after_shared_forward (observe : ∀ key, Setoid (V key)) (program : Code → Instruction Name ops Code)
    {state : R} {actor owner foreignActor : Name} {key : Key} {code foreignCode : Code}
    {name foreignName : ops.Name key} {arg : ops.Argument key name} {foreignArg : ops.Argument key foreignName}
    {before output changed : V key} {inverse foreignInverse : PartialMap (V key)}
    {outcome : ops.Outcome key name} {foreignOutcome : ops.Outcome key foreignName}
    (action : (program code).action = .operate key name arg)
    (located : location state actor key = some (owner, before))
    (returned : (ops.operation key name arg).run before = some (output, inverse, outcome))
    (foreignAction : (program foreignCode).action = .operate key foreignName foreignArg)
    (foreignLocated : location state foreignActor key = some (owner, before))
    (foreignReturned : (ops.operation key foreignName foreignArg).run before = some (changed, foreignInverse, foreignOutcome))
    (laws : PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key) :
    ∃ middle after, ∃ newInverse : PartialMap (V key),
      Land program foreignActor foreignCode state middle (.operate owner key foreignInverse)
        ((program foreignCode).next (.operation key foreignName foreignOutcome)) ∧
      Land program actor code middle after (.operate owner key newInverse)
        ((program code).next (.operation key name outcome)) ∧
      MapRelated (observe key).r newInverse inverse := by
  have generator : Generated (fun map => ∃ selected args, OperationGenerator (ops.operation key selected args) map)
      (forward (ops.operation key foreignName foreignArg)) := .generator ⟨foreignName, foreignArg, .forward⟩
  have moved : forward (ops.operation key foreignName foreignArg) before = some changed := by
    simp [forward, foreignReturned]
  obtain ⟨after, newInverse, next, saved⟩ :=
    rerun_after_routed_word observe program action (location_write_here located changed) returned laws generator moved
  exact ⟨_, after, newInverse,
    .operate _ _ _ _ _ _ _ _ _ _ _ foreignAction foreignLocated foreignReturned, next, saved⟩

/-- The foreign move may instead be an actual saved inverse. Its successful
partial application at the later reader's binding determines the registry
update. The original foreign call establishes that this is a generator. -/
theorem rerun_after_shared_inverse (observe : ∀ key, Setoid (V key)) (program : Code → Instruction Name ops Code)
    {state : R} {actor owner : Name} {key : Key} {code : Code} {name foreignName : ops.Name key}
    {arg : ops.Argument key name} {foreignArg : ops.Argument key foreignName}
    {before output changed capturedAt capturedAfter : V key} {inverse foreignInverse : PartialMap (V key)}
    {outcome : ops.Outcome key name} {foreignOutcome : ops.Outcome key foreignName}
    (action : (program code).action = .operate key name arg)
    (located : location state actor key = some (owner, before))
    (returned : (ops.operation key name arg).run before = some (output, inverse, outcome))
    (origin : (ops.operation key foreignName foreignArg).run capturedAt = some (capturedAfter, foreignInverse, foreignOutcome))
    (moved : foreignInverse before = some changed)
    (laws : PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key) :
    ∃ after, ∃ newInverse : PartialMap (V key),
      Land program actor code (undo (.operate owner key foreignInverse) state) after (.operate owner key newInverse)
        ((program code).next (.operation key name outcome)) ∧
      MapRelated (observe key).r newInverse inverse := by
  have generator : Generated (fun map => ∃ selected args, OperationGenerator (ops.operation key selected args) map)
      foreignInverse := .generator ⟨foreignName, foreignArg, .inverse capturedAt capturedAfter _ foreignOutcome origin⟩
  rw [undo_operate_eq_write (table_and_route located).2 moved]
  exact rerun_after_routed_word observe program action (location_write_here located changed) returned laws generator moved

/-- Read the coeffect origin of the saved inverse off a prior native landing.
The capture's owner and typed key are the same as the local route at replay. -/
theorem rerun_after_captured_operation (observe : ∀ key, Setoid (V key))
    (program : Code → Instruction Name ops Code) {state origin captured : R}
    {actor owner foreignActor : Name} {key : Key} {code foreignCode : Code} {name : ops.Name key}
    {arg : ops.Argument key name} {before output changed : V key}
    {inverse foreignInverse : PartialMap (V key)} {outcome : ops.Outcome key name} {foreignNext : Option Code}
    (action : (program code).action = .operate key name arg)
    (located : location state actor key = some (owner, before))
    (returned : (ops.operation key name arg).run before = some (output, inverse, outcome))
    (originLanding : Land program foreignActor foreignCode origin captured (.operate owner key foreignInverse) foreignNext)
    (moved : foreignInverse before = some changed)
    (laws : PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key) :
    ∃ after, ∃ newInverse : PartialMap (V key),
      Land program actor code (undo (.operate owner key foreignInverse) state) after (.operate owner key newInverse)
        ((program code).next (.operation key name outcome)) ∧
      MapRelated (observe key).r newInverse inverse := by
  cases originLanding with
  | operate _ _ _ _ foreignName foreignArg _ capturedAt capturedAfter _ foreignOutcome _ _ foreignReturned =>
    exact rerun_after_shared_inverse observe program action located returned foreignReturned moved laws

end Cordis.Repairs.PairwiseOperations
