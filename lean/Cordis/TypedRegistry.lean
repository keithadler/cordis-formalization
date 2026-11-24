import Cordis.TypedProgram

/-! The registry of Definitions 49–56 with dependent coeffect tables.
Encoding preserves metadata, table presence, and captured inverse order. -/
namespace Cordis.TypedRegistry
open Calculus (Component Phase View)
open PaperEffectEquations (CoeffectOperations)
open TypedCoeffectReplay (pack unpack encodeMap)
universe u
variable {Name Key Code : Type u} {V : Key → Type u}

inductive Inverse (Name : Type u) {Key : Type u} (V : Key → Type u) where
  | unit
  | restrict (owner : Name) (key : Key)
  | operate (owner : Name) (key : Key) (inverse : V key → Option (V key))
  | retire (child : Name)

structure Fiber (Name : Type u) {Key : Type u} (V : Key → Type u) (Code : Type u) where
  component : Component Key Code
  parent : Option Name
  table : (key : Key) → Option (V key)
  retired : Bool
  phase : Phase Name Key Code (Inverse Name V)

abbrev Registry (Name : Type u) {Key : Type u} (V : Key → Type u) (Code : Type u) :=
  Name → Option (Fiber Name V Code)

abbrev RawFiber (Name : Type u) (ops : CoeffectOperations V) (Code : Type u) :=
  Calculus.Fiber Name Key (Scalar ops) Code (Stages.Inverse Name Key (Scalar ops)) (PUnit.{u + 1})

abbrev RawRegistry (Name : Type u) (ops : CoeffectOperations V) (Code : Type u) :=
  Name → Option (RawFiber Name ops Code)

local notation "R" => Registry Name V Code
local notation "F" => Fiber Name V Code
local notation "I" => Inverse Name V

def Target (r : R) (actor : Name) (view : View Name Key) : Prop :=
  match r actor with
  | none => False
  | some fiber => fiber.retired = false ∧
    ∀ key, fiber.component.requires key → match r (view key) with
      | none => False
      | some provider => provider.phase.available ∧ provider.table key ≠ none

def Relied (r : R) (name : Name) : Prop :=
  ∃ consumer, consumer ≠ name ∧ match r consumer with
    | none => False
    | some fiber => match fiber.phase.committed with
      | none => False
      | some view => ∃ key, fiber.component.requires key ∧ view key = name

def Insertable (r : R) (name : Name) (component : Component Key Code) (parent : Option Name) : Prop :=
  r name = none ∧ (∀ p, parent = some p → r p ≠ none) ∧
    ∀ other key, match r other with
      | none => True
      | some fiber => component.provides key → ¬ fiber.component.provides key

def Removable (r : R) (name : Name) : Prop :=
  match r name with
  | none => False
  | some fiber => fiber.retired = true ∧ fiber.phase = .inactive ∧
    (∀ key, fiber.table key = none) ∧
    ∀ child, match r child with
      | none => True
      | some entry => entry.parent ≠ some name

def fresh (component : Component Key Code) (parent : Option Name) : F :=
  ⟨component, parent, fun _ => none, false, .inactive⟩

def tableAt (r : R) (owner : Name) (key : Key) : Option (V key) :=
  (r owner).bind (fun entry => entry.table key)

def bindingOwner (r : R) (name : Name) (key : Key) : Option Name := do
  let fiber ← r name
  if fiber.component.provides key then some name
  else if fiber.component.requires key then fiber.phase.committed.map (fun view => view key)
  else none

def location (r : R) (name : Name) (key : Key) : Option (Name × V key) :=
  (bindingOwner r name key).bind fun owner => (tableAt r owner key).map (fun value => (owner, value))

variable [DecidableEq Name]

def put (r : R) (name : Name) (fiber : F) : R :=
  fun other => if other = name then some fiber else r other

def erase (r : R) (name : Name) : R :=
  fun other => if other = name then none else r other

def modify (r : R) (name : Name) (change : F → F) : R :=
  fun other => if other = name then (r other).map change else r other

def mark (r : R) (name : Name) (phase : Phase Name Key Code I) : R :=
  modify r name (fun fiber => {fiber with phase := phase})

def retire (r : R) (name : Name) : R :=
  modify r name (fun fiber => {fiber with retired := true})

variable [DecidableEq Key]

def write (r : R) (owner : Name) (key : Key) (value : Option (V key)) : R :=
  modify r owner (fun fiber => {fiber with table := fun other =>
    if same : key = other then same ▸ value else fiber.table other})

/-- The state map completes undefined probes by identity. Definedness of
actual inverse replay is a separate property of the trace. -/
def undo : I → R → R
  | .unit, r => r
  | .restrict owner key, r => write r owner key none
  | .operate owner key inverse, r =>
      modify r owner (fun fiber => {fiber with table := (fun other =>
        if same : key = other then same ▸ ((fiber.table key).map fun v => (inverse v).getD v)
        else fiber.table other)})
  | .retire child, r => retire r child

/-- Definedness of the native partial token, separately from the state map
`undo`. Retirement's incarnation check selects its effect, including identity. -/
def InverseDefined (state : R) : I → Prop
  | .unit | .retire _ => True
  | .restrict owner key => tableAt state owner key ≠ none
  | .operate owner key inverse =>
    ∃ input output, tableAt state owner key = some input ∧ inverse input = some output

def capturedChild : I → Option Name
  | .retire child => some child
  | _ => none

def discharge : List I → R → R
  | [], r => r
  | token :: rest, r => discharge rest (undo token r)

variable {ops : CoeffectOperations V}

/-- The actual partial inverse and the operation's own typed outcome. -/
inductive Land (program : Code → Instruction Name ops Code) :
    Name → Code → R → R → I → Option Code → Prop where
  | unit (r actor code) : (program code).action = .unit →
      Land program actor code r r .unit ((program code).next .unit)
  | provide (r actor code fiber key value) :
      (program code).action = .provide key value → r actor = some fiber →
      fiber.component.provides key = true → fiber.table key = none →
      Land program actor code r (write r actor key (some value)) (.restrict actor key)
        ((program code).next (.provision key value))
  | operate (r actor code key operation argument owner before after inverse result) :
      (program code).action = .operate key operation argument →
      location r actor key = some (owner, before) →
      (ops.operation key operation argument).run before = some (after, inverse, result) →
      Land program actor code r (write r owner key (some after)) (.operate owner key inverse)
        ((program code).next (.operation key operation result))
  | instantiate (r actor code component child) :
      (program code).action = .instantiate component → Insertable r child component (some actor) →
      Land program actor code r (put r child (fresh component (some actor))) (.retire child)
        ((program code).next (.child child))

/-- The typed outcome read by a successful landing. The draw may be
absent for an ordinary instruction. Legality of the landing is separate. -/
def replyAt (program : Code → Instruction Name ops Code) (actor : Name) (draw : Option Name)
    (code : Code) (state : R) : Option (Outcome Name ops) :=
  match (program code).action with
  | .unit => some .unit
  | .provide key value => some (.provision key value)
  | .operate key name argument => do
      let (_, value) ← location state actor key
      let (_, _, result) ← (ops.operation key name argument).run value
      return .operation key name result
  | .instantiate _ => draw.map Outcome.child

theorem Land.reply {program : Code → Instruction Name ops Code} {actor : Name}
    {code : Code} {before after : R} {token : I} {next : Option Code}
    (landed : Land program actor code before after token next) :
    ∃ outcome, replyAt program actor (capturedChild token) code before = some outcome ∧
      (program code).next outcome = next := by
  cases landed with
  | unit _ _ _ action => exact ⟨_, by simp [replyAt, action], rfl⟩
  | provide _ _ _ _ _ _ action _ _ _ => exact ⟨_, by simp [replyAt, action], rfl⟩
  | operate _ _ _ _ _ _ _ _ _ _ _ action located called =>
    exact ⟨_, by simp [replyAt, action, located, called], rfl⟩
  | instantiate _ _ _ _ _ action _ => exact ⟨_, by simp [replyAt, action, capturedChild], rfl⟩

variable (ops)

def encodeInverse : I → Stages.Inverse Name Key (Scalar ops)
  | .unit => .unit
  | .restrict owner key => .restrict owner key
  | .operate owner key inverse => .operate owner key (encodeMap key inverse)
  | .retire child => .retire child

def encodePhase : Phase Name Key Code I → Phase Name Key Code (Stages.Inverse Name Key (Scalar ops))
  | .inactive => .inactive
  | .reloading code saved view => .reloading code (saved.map (encodeInverse ops)) view
  | .active saved view => .active (saved.map (encodeInverse ops)) view
  | .unloading saved view => .unloading (saved.map (encodeInverse ops)) view

def encodeFiber (fiber : F) : RawFiber Name ops Code :=
  ⟨fiber.component, fiber.parent, fun key => (fiber.table key).map (pack key),
    fiber.retired, encodePhase ops fiber.phase⟩

def encodeRegistry (r : R) : RawRegistry Name ops Code :=
  fun name => (r name).map (encodeFiber ops)

omit [DecidableEq Name] in
@[simp] theorem encode_empty :
    encodeRegistry ops (fun _ => none : R) = (fun _ => none) := rfl

omit [DecidableEq Name] in
@[simp] theorem encode_fresh (component : Component Key Code) (parent : Option Name) :
    encodeFiber ops (fresh component parent : F) = Calculus.fresh component parent := rfl

@[simp] theorem encode_put (r : R) (name : Name) (fiber : F) :
    encodeRegistry ops (put r name fiber) = Calculus.put (encodeRegistry ops r) name (encodeFiber ops fiber) := by
  funext other
  by_cases same : other = name <;> simp [put, Calculus.put, same, encodeRegistry]

@[simp] theorem encode_erase (r : R) (name : Name) :
    encodeRegistry ops (erase r name) = Calculus.erase (encodeRegistry ops r) name := by
  funext other
  by_cases same : other = name <;> simp [erase, Calculus.erase, same, encodeRegistry]

private theorem encode_modify (r : R) (name : Name) (change : F → F)
    (raw : RawFiber Name ops Code → RawFiber Name ops Code)
    (commutes : ∀ fiber, encodeFiber ops (change fiber) = raw (encodeFiber ops fiber)) :
    encodeRegistry ops (modify r name change) = Calculus.modify (encodeRegistry ops r) name raw := by
  funext other
  by_cases same : other = name
  · subst other
    cases found : r name <;> simp [modify, Calculus.modify, found, encodeRegistry, commutes]
  · simp [modify, Calculus.modify, same, encodeRegistry]

@[simp] theorem encode_mark (r : R) (name : Name) (phase : Phase Name Key Code I) :
    encodeRegistry ops (mark r name phase) = Calculus.mark (encodeRegistry ops r) name (encodePhase ops phase) :=
  encode_modify ops r name _ _ fun _ => rfl

@[simp] theorem encode_retire (r : R) (name : Name) :
    encodeRegistry ops (retire r name) = Calculus.retire (encodeRegistry ops r) name :=
  encode_modify ops r name _ _ fun _ => rfl

@[simp] theorem encode_write (r : R) (owner : Name) (key : Key) (value : Option (V key)) :
    encodeRegistry ops (write r owner key value) = Stages.write (encodeRegistry ops r) owner key (value.map (pack key)) := by
  apply encode_modify
  intro entry
  simp only [encodeFiber]
  congr 1
  funext other
  by_cases same : key = other
  · subst other
    simp
  · simp [same, Ne.symm same]

@[simp] theorem encode_undo (token : I) (r : R) :
    encodeRegistry ops (undo token r) = Stages.undo (encodeInverse ops token) (encodeRegistry ops r) := by
  cases token with
  | unit => rfl
  | restrict => exact encode_write ops _ _ _ _
  | retire => exact encode_retire ops _ _
  | operate owner key inverse =>
    apply encode_modify
    intro entry
    simp only [encodeFiber]
    congr 1
    funext other
    by_cases same : key = other
    · subst other
      cases value : entry.table key <;> simp
    · simp [same, Ne.symm same]

@[simp] theorem encode_discharge (tokens : List I) (r : R) :
    encodeRegistry ops (discharge tokens r) =
      Calculus.discharge Stages.undo (tokens.map (encodeInverse ops)) (encodeRegistry ops r) := by
  induction tokens generalizing r with
  | nil => rfl
  | cons token rest ih =>
    simp only [discharge, List.map_cons, Calculus.discharge, ih, encode_undo]


omit [DecidableEq Name] in
theorem encodeInverse_injective : Function.Injective (encodeInverse (Name := Name) ops) := by
  intro left right same
  cases left <;> cases right <;> simp [encodeInverse] at same ⊢
  all_goals try exact same
  rename_i owner key inv other otherKey inverse
  obtain ⟨rfl, rfl, functions⟩ := same
  have equal := TypedCoeffectReplay.encodeMap_injective key functions
  cases equal
  simp

private theorem list_map_injective {A B : Type u} {f : A → B} (inj : Function.Injective f) :
    Function.Injective (List.map f) := by
  intro left
  induction left with
  | nil =>
    intro right equal
    cases right <;> simp_all
  | cons value tail ih =>
    intro right equal
    cases right with
    | nil => simp at equal
    | cons other rest =>
      obtain ⟨first, second⟩ : f value = f other ∧ tail.map f = rest.map f := by simpa using equal
      rw [inj first, ih second]

private theorem option_map_injective {A B : Type u} {f : A → B} (inj : Function.Injective f) :
    Function.Injective (Option.map f) := by
  intro left right equal
  cases left <;> cases right <;> simp_all
  exact inj equal

omit [DecidableEq Name] in
theorem encodePhase_injective : Function.Injective (encodePhase (Name := Name) (Code := Code) ops) := by
  intro left right same
  have words := list_map_injective (encodeInverse_injective (Name := Name) ops)
  cases left <;> cases right <;> simp [encodePhase] at same ⊢
  · exact ⟨same.1, words same.2.1, same.2.2⟩
  · exact ⟨words same.1, same.2⟩
  · exact ⟨words same.1, same.2⟩

omit [DecidableEq Name] in
theorem encodeFiber_injective : Function.Injective (encodeFiber (Name := Name) (Code := Code) ops) := by
  intro left right same
  cases left with
  | mk component parent table retired phase =>
    cases right with
    | mk nextComponent nextParent nextTable nextRetired nextPhase =>
      obtain ⟨rfl, rfl, tables, rfl, phases⟩ := Calculus.Fiber.mk.inj same
      have typedTables : table = nextTable := by
        funext key
        exact option_map_injective (TypedCoeffectReplay.pack_injective key) (congrFun tables key)
      have typedPhase := encodePhase_injective ops phases
      cases typedTables
      cases typedPhase
      rfl

omit [DecidableEq Name] in
theorem encodeRegistry_injective : Function.Injective (encodeRegistry (Name := Name) (Code := Code) ops) := by
  intro left right same
  funext name
  exact option_map_injective (encodeFiber_injective ops) (congrFun same name)

omit [DecidableEq Name] in
@[simp] theorem encodeRegistry_none (r : R) (name : Name) :
    encodeRegistry ops r name = none ↔ r name = none :=
  Option.map_eq_none_iff

omit [DecidableEq Name] in
theorem encodeRegistry_some {r : R} {name : Name} {entry : RawFiber Name ops Code}
    (present : encodeRegistry ops r name = some entry) :
    ∃ fiber, r name = some fiber ∧ encodeFiber ops fiber = entry :=
  Option.map_eq_some_iff.mp present


omit [DecidableEq Name] in
@[simp] theorem encodePhase_committed (phase : Phase Name Key Code I) :
    (encodePhase ops phase).committed = phase.committed := by
  cases phase <;> rfl

omit [DecidableEq Name] in
@[simp] theorem encodePhase_available (phase : Phase Name Key Code I) :
    (encodePhase ops phase).available ↔ phase.available := by
  cases phase <;> exact Iff.rfl

omit [DecidableEq Name] in
@[simp] theorem encodePhase_inactive (phase : Phase Name Key Code I) :
    encodePhase ops phase = .inactive ↔ phase = .inactive := by
  cases phase <;> simp [encodePhase]

omit [DecidableEq Name] in
@[simp] theorem insertable_encode_iff (r : R) (name : Name) (component : Component Key Code)
    (parent : Option Name) :
    Calculus.Insertable (encodeRegistry ops r) name component parent ↔ Insertable r name component parent := by
  simp only [Calculus.Insertable, Insertable, encodeRegistry_none]
  constructor
  · rintro ⟨empty, rooted, reserved⟩
    refine ⟨empty, fun p eq present => rooted p eq ((encodeRegistry_none ops r p).mpr present), ?_⟩
    intro other key
    cases seen : r other with
    | none => trivial
    | some fiber => simpa [encodeRegistry, seen, encodeFiber] using reserved other key
  · rintro ⟨empty, rooted, reserved⟩
    refine ⟨empty, fun p eq present => rooted p eq ((encodeRegistry_none ops r p).mp present), ?_⟩
    intro other key
    cases seen : r other with
    | none => simp [encodeRegistry, seen]
    | some fiber => simpa [encodeRegistry, seen, encodeFiber] using reserved other key

omit [DecidableEq Name] in
@[simp] theorem removable_encode_iff (r : R) (name : Name) :
    Calculus.Removable (encodeRegistry ops r) name ↔ Removable r name := by
  cases found : r name with
  | none => simp [Calculus.Removable, Removable, encodeRegistry, found]
  | some entry =>
    simp only [Calculus.Removable, Removable, encodeRegistry, found, Option.map_some, encodeFiber,
      encodePhase_inactive, Option.map_eq_none_iff]
    apply and_congr_right
    intro _
    apply and_congr_right
    intro _
    apply and_congr_right
    intro _
    apply forall_congr'
    intro child
    cases r child <;> simp [encodeFiber]

omit [DecidableEq Name] in
@[simp] theorem target_encode_iff (r : R) (name : Name) (view : View Name Key) :
    Calculus.Target (encodeRegistry ops r) name view ↔ Target r name view := by
  cases found : r name with
  | none => simp [Calculus.Target, Target, encodeRegistry, found]
  | some entry =>
    simp only [Calculus.Target, Target, encodeRegistry, found, Option.map_some, encodeFiber]
    apply and_congr_right
    intro _
    apply forall_congr'
    intro key
    cases r (view key) <;> simp [encodeFiber]

omit [DecidableEq Name] in
@[simp] theorem relied_encode_iff (r : R) (name : Name) :
    Calculus.Relied (encodeRegistry ops r) name ↔ Relied r name := by
  unfold Calculus.Relied Relied
  apply exists_congr
  intro consumer
  apply and_congr_right
  intro _
  cases found : r consumer <;>
    simp only [encodeRegistry, found, Option.map_none, Option.map_some, encodeFiber, encodePhase_committed] <;> rfl

omit [DecidableEq Name] in
@[simp] theorem encode_bindingOwner (r : R) (name : Name) (key : Key) :
    Stages.bindingOwner (encodeRegistry ops r) name key = bindingOwner r name key := by
  cases found : r name <;> simp [Stages.bindingOwner, bindingOwner, encodeRegistry, encodeFiber, found]

omit [DecidableEq Name] in
theorem encode_location (r : R) (name : Name) (key : Key) :
    Stages.location (encodeRegistry ops r) name key =
      (location r name key).map (fun (owner, value) => (owner, pack key value)) := by
  unfold Stages.location location
  rw [encode_bindingOwner]
  cases bindingOwner r name key with
  | none => rfl
  | some owner =>
    cases found : r owner with
    | none => simp [encodeRegistry, tableAt, found]
    | some entry =>
      cases binding : entry.table key <;> simp [encodeRegistry, encodeFiber, tableAt, found, binding]


theorem land_encode {program : Code → Instruction Name ops Code}
    {actor : Name} {code : Code} {before after : R} {inverse : I} {next : Option Code}
    (land : Land program actor code before after inverse next) :
    Stages.Land (encodeProgram program) actor code (encodeRegistry ops before)
      (encodeRegistry ops after) (encodeInverse ops inverse) next := by
  cases land with
  | unit r name entry action =>
    exact .unit _ _ _ (by simp [encodeProgram, encodeInstruction, action, encodeAction])
  | provide r name entry fiber key value action present declared empty =>
    rw [encode_write]
    exact .provide _ _ _ (encodeFiber ops fiber) key (pack key value)
      (by simp [encodeProgram, encodeInstruction, action, encodeAction])
      (by simp [encodeRegistry, present]) declared (by simp [encodeFiber, empty])
  | operate r name entry key operation argument owner input output inverse outcome action located called =>
    rw [encode_write]
    exact .operate _ _ _ key (encodeOperation ops key operation argument) owner (pack key input)
      (pack key output) (encodeMap key inverse) (packOutcome ops key operation outcome)
      (by simp [encodeProgram, encodeInstruction, action, encodeAction])
      (by simp [encode_location, located]) (by simp [encodeOperation, called])
  | instantiate r name entry component child action ready =>
    rw [encode_put, encode_fresh]
    exact .instantiate _ _ _ component child (by simp [encodeProgram, encodeInstruction, action, encodeAction])
      ((insertable_encode_iff ops _ _ _ _).mpr ready)


/-- Every raw landing from an encoded state comes from a typed landing,
including the returned inverse and continuation. -/
theorem land_decode {program : Code → Instruction Name ops Code}
    {actor : Name} {code : Code} {before : R} {after : RawRegistry Name ops Code}
    {inverse : Stages.Inverse Name Key (Scalar ops)} {next : Option Code}
    (land : Stages.Land (encodeProgram program) actor code (encodeRegistry ops before) after inverse next) :
    ∃ typed token, Land program actor code before typed token next ∧
      encodeRegistry ops typed = after ∧ encodeInverse ops token = inverse := by
  generalize source : encodeRegistry ops before = raw at land
  cases land with
  | unit raw actor code action =>
    cases native : (program code).action <;> simp [encodeProgram, encodeInstruction, native, encodeAction] at action
    exact ⟨_, _, .unit _ _ _ native, source, rfl⟩
  | provide raw actor code entry key value action present declared empty =>
    subst raw
    cases native : (program code).action <;> simp [encodeProgram, encodeInstruction, native, encodeAction] at action
    rename_i k typedValue
    obtain ⟨rfl, rfl⟩ := action
    obtain ⟨fiber, found, rfl⟩ := encodeRegistry_some ops present
    have absent : fiber.table k = none := Option.map_eq_none_iff.mp empty
    exact ⟨_, _, .provide _ _ _ fiber k typedValue native found declared absent, by simp, rfl⟩
  | operate raw actor code key run owner input output saved result action located called =>
    subst raw
    cases native : (program code).action <;> simp [encodeProgram, encodeInstruction, native, encodeAction] at action
    rename_i k operation argument
    obtain ⟨rfl, rfl⟩ := action
    rw [encode_location] at located
    obtain ⟨⟨actualOwner, value⟩, typedAt, encodedAt⟩ := Option.map_eq_some_iff.mp located
    cases encodedAt
    cases completed : (ops.operation k operation argument).run value with
    | none => simp [encodeOperation, completed] at called
    | some triple =>
      rcases triple with ⟨changed, inverse, outcome⟩
      simp [encodeOperation, completed] at called
      obtain ⟨rfl, rfl, rfl⟩ := called
      exact ⟨_, _, .operate _ _ _ k operation argument _ value changed inverse outcome native typedAt completed,
        by simp, rfl⟩
  | instantiate raw actor code component child action ready =>
    subst raw
    cases native : (program code).action <;> simp [encodeProgram, encodeInstruction, native, encodeAction] at action
    cases action
    exact ⟨_, _, .instantiate _ _ _ _ _ native ((insertable_encode_iff ops _ _ _ _).mp ready), by simp, rfl⟩

end Cordis.TypedRegistry
