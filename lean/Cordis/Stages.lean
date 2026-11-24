import Cordis.Calculus

/-!
Context-mediated stages (Definitions 30 and 56, pp. 22 and 38). A coeffect
operation receives exactly one declared value and returns its actual inverse.
A provision's inverse removes that binding; child creation yields retirement,
not immediate erasure. Outcome-dependent continuations are explicit functions.
-/
namespace Cordis.Stages
open Calculus
universe u
variable {Name Key Value Code Error : Type u}

inductive Inverse (Name Key Value : Type u) where
  | unit
  | restrict (owner : Name) (key : Key)
  | operate (owner : Name) (key : Key) (undo : Value → Value)
  | retire (child : Name)

inductive Outcome (Name Value : Type u) where
  | unit
  | value (value : Value)
  | child (name : Name)

inductive Action (Name Key Value Code Error : Type u) where
  | unit
  | provide (key : Key) (value : Value)
  | operate (key : Key) (run : Value → Except Error (Value × (Value → Value) × Value))
  | instantiate (component : Component Key Code)

structure Instruction (Name Key Value Code Error : Type u) where
  action : Action Name Key Value Code Error
  next : Outcome Name Value → Option Code

local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
variable [DecidableEq Name] [DecidableEq Key]

def write (r : R) (owner : Name) (key : Key) (value : Option Value) : R :=
  Calculus.modify r owner (fun fiber => { fiber with table :=
    fun other => if other = key then value else fiber.table other })

/-- Select the owner from the actor's own provisions or its committed view. -/
def bindingOwner (r : R) (name : Name) (key : Key) : Option Name := do
  let fiber ← r name
  if fiber.component.provides key then some name
  else if fiber.component.requires key then fiber.phase.committed.map (fun view => view key)
  else none

/-- A resolved owner must still hold the binding in its retained table. -/
def location (r : R) (name : Name) (key : Key) : Option (Name × Value) :=
  (bindingOwner r name key).bind fun owner =>
    ((r owner).bind fun fiber => fiber.table key).map fun value => (owner, value)

omit [DecidableEq Name] [DecidableEq Key] in
theorem location_owner {r : R} {actor owner : Name} {key : Key} {value : Value}
    (located : location r actor key = some (owner, value)) :
    bindingOwner r actor key = some owner := by
  obtain ⟨selected, route, result⟩ := Option.bind_eq_some_iff.mp located
  obtain ⟨_, _, pair⟩ := Option.map_eq_some_iff.mp result
  cases pair
  exact route

omit [DecidableEq Name] [DecidableEq Key] in
theorem location_scope {r : R} {actor owner : Name} {f : F} {key : Key} {value : Value}
    (present : r actor = some f) (located : location r actor key = some (owner, value)) :
    (owner = actor ∧ f.component.provides key = true) ∨
      ∃ view, f.phase.committed = some view ∧ f.component.requires key = true ∧ view key = owner := by
  have route := location_owner located
  by_cases own : f.component.provides key = true
  · exact .inl ⟨by simpa [bindingOwner, present, own] using route.symm, own⟩
  · by_cases required : f.component.requires key = true
    · cases committed : f.phase.committed with
      | none => simp [bindingOwner, present, own, required, committed] at route
      | some view => exact .inr ⟨view, rfl, required,
          by simpa [bindingOwner, present, own, required, committed] using route⟩
    · simp [bindingOwner, present, own, required] at route

/-- Captured inverses act on the current value. The inverse of an
instantiation is O-Retire at the captured name, as in Definition 52. -/
def undo : Inverse Name Key Value → R → R
  | .unit, r => r
  | .restrict owner key, r => write r owner key none
  | .operate owner key inverse, r =>
      Calculus.modify r owner (fun fiber => { fiber with table := fun other =>
        if other = key then (Option.map inverse (fiber.table key)) else fiber.table other })
  | .retire child, r => Calculus.retire r child

/-- Definition 56's primitives. The last index can retain the primitive's
outcome or project it through the continuation. -/
inductive Execution (program : Code → Instruction Name Key Value Code Error)
    {Result : Type u} (result : Code → Outcome Name Value → Result) :
    Name → Code → R → R → Inverse Name Key Value → Result → Prop
  | unit (r name code) : (program code).action = .unit →
      Execution program result name code r r .unit (result code .unit)
  | provide (r name code fiber key value) :
      (program code).action = .provide key value → r name = some fiber →
      fiber.component.provides key = true → fiber.table key = none →
      Execution program result name code r (write r name key (some value)) (.restrict name key)
        (result code (.value value))
  | operate (r name code key run owner before after inverse value) :
      (program code).action = .operate key run → location r name key = some (owner, before) →
      run before = .ok (after, inverse, value) →
      Execution program result name code r (write r owner key (some after)) (.operate owner key inverse)
        (result code (.value value))
  | instantiate (r name code component child) :
      (program code).action = .instantiate component → Insertable r child component (some name) →
      Execution program result name code r (put r child (fresh component (some name))) (.retire child)
        (result code (.child child))

/-- The paper's total continuation projects a successful primitive's outcome. -/
abbrev Land (program : Code → Instruction Name Key Value Code Error) :=
  Execution program fun code => (program code).next

/-- Primitive completion retains its outcome before the continuation runs. -/
abbrev Performed (program : Code → Instruction Name Key Value Code Error) :=
  Execution program fun _ outcome => outcome

theorem Performed.toLand (program : Code → Instruction Name Key Value Code Error)
    {name : Name} {code : Code} {r s : R} {inverse : Inverse Name Key Value}
    {outcome : Outcome Name Value} (performed : Performed program name code r s inverse outcome) :
    Land program name code r s inverse ((program code).next outcome) := by
  cases performed <;> constructor <;> assumption

end Cordis.Stages
