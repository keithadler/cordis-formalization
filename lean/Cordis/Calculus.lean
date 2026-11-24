import Cordis.Effects

/-!
Shi–Zhang–Cui, arXiv:2608.25512v1, §§4.1–4.2, pp. 31–38. This model retains
iterators, the actual captured inverses, and all nine rules. Program counters may
select their successor from an iteration's outcome. `Stages` supplies the
context-mediated iterations.
-/
namespace Cordis.Calculus

universe u v w x y z
variable {Name : Type u} {Key : Type v} {Value : Type w}
variable {Code : Type x} {Undo : Type y} {Error : Type z}

abbrev View (Name : Type u) (Key : Type v) := Key → Name

inductive Phase (Name : Type u) (Key : Type v) (Code : Type x) (Undo : Type y) where
  | inactive
  | reloading (iterator : Code) (accumulator : List Undo) (committed : View Name Key)
  | active (accumulator : List Undo) (committed : View Name Key)
  | unloading (accumulator : List Undo) (committed : View Name Key)

def Phase.committed : Phase Name Key Code Undo → Option (View Name Key)
  | .inactive => none
  | .reloading _ _ view | .active _ view | .unloading _ view => some view

def Phase.accumulator : Phase Name Key Code Undo → List Undo
  | .inactive => []
  | .reloading _ undo _ | .active undo _ | .unloading undo _ => undo

def Phase.available : Phase Name Key Code Undo → Prop
  | .active _ _ => True
  | _ => False

structure Component (Key : Type v) (Code : Type x) where
  requires : Key → Bool
  provides : Key → Bool
  entry : Code

structure Fiber (Name : Type u) (Key : Type v) (Value : Type w)
    (Code : Type x) (Undo : Type y) (Error : Type z) where
  component : Component Key Code
  parent : Option Name
  table : Key → Option Value
  retired : Bool
  phase : Phase Name Key Code Undo

abbrev Registry (Name : Type u) (Key : Type v) (Value : Type w)
    (Code : Type x) (Undo : Type y) (Error : Type z) :=
  Name → Option (Fiber Name Key Value Code Undo Error)

local notation "R" => Registry Name Key Value Code Undo Error
local notation "F" => Fiber Name Key Value Code Undo Error

/-- Definition 53. Declarations reserve keys, but only actual ACTIVE bindings
satisfy requirements. No parent-liveness condition is present. -/
def Target (r : R) (name : Name) (view : View Name Key) : Prop :=
  match r name with
  | none => False
  | some fiber => fiber.retired = false ∧
    ∀ key, fiber.component.requires key →
      match r (view key) with
      | none => False
      | some provider => provider.phase.available ∧ provider.table key ≠ none

/-- Entry presence at the source of an L-Begin rule. -/
abbrev ErrorFree (r : R) (name : Name) : Prop := r name ≠ none

/-- Definition 54 includes reloading and unloading consumers. -/
def Relied (r : R) (name : Name) : Prop :=
  ∃ consumer, consumer ≠ name ∧ match r consumer with
    | none => False
    | some fiber => match fiber.phase.committed with
      | none => False
      | some view => ∃ key, fiber.component.requires key ∧ view key = name

variable [DecidableEq Name]

def put (r : R) (name : Name) (fiber : F) : R :=
  fun other => if other = name then some fiber else r other

def erase (r : R) (name : Name) : R :=
  fun other => if other = name then none else r other

def modify (r : R) (name : Name) (change : F → F) : R :=
  fun other => if other = name then (r other).map change else r other

def mark (r : R) (name : Name) (phase : Phase Name Key Code Undo) : R :=
  modify r name (fun fiber => { fiber with phase := phase })

def retire (r : R) (name : Name) : R :=
  modify r name (fun fiber => { fiber with retired := true })

def fresh (component : Component Key Code) (parent : Option Name) : F :=
  ⟨component, parent, fun _ => none, false, .inactive⟩

/-- O-Insert reserves declarations even while their fibers are inactive. -/
def Insertable (r : R) (name : Name) (component : Component Key Code)
    (parent : Option Name) : Prop :=
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

/-- Newest inverse is stored first. L-Iter/L-Finish accumulate g ∘ h (p. 36). -/
def discharge (undo : Undo → R → R) : List Undo → R → R
  | [], r => r
  | head :: rest, r => discharge undo rest (undo head r)

/-- Actual returned state, inverse, and outcome-selected continuation. -/
abbrev Landing := Name → Code → R → R → Undo → Option Code → Prop

/-- The paper's nine rules. No rule clears a table in lieu of applying inverses. -/
inductive Step (land : Landing (Name := Name) (Key := Key) (Value := Value)
    (Code := Code) (Undo := Undo) (Error := Error)) (undo : Undo → R → R) : R → R → Prop
  | insert (r name component parent) : Insertable r name component parent →
      Step land undo r (put r name (fresh component parent))
  | retire (r name) : r name ≠ none → Step land undo r (retire r name)
  | remove (r name) : Removable r name → Step land undo r (erase r name)
  | begin (r name fiber view) : r name = some fiber → fiber.phase = .inactive →
      ErrorFree r name → Target r name view →
      Step land undo r (mark r name (.reloading fiber.component.entry [] view))
  | iter (r s name fiber code accumulator view inverse next) :
      r name = some fiber → fiber.phase = .reloading code accumulator view →
      Target r name view → land name code r s inverse (some next) →
      Step land undo r (mark s name (.reloading next (inverse :: accumulator) view))
  | finish (r s name fiber code accumulator view inverse) :
      r name = some fiber → fiber.phase = .reloading code accumulator view →
      Target r name view → land name code r s inverse none →
      Step land undo r (mark s name (.active (inverse :: accumulator) view))
  | divert (r s name fiber code accumulator view tail) :
      r name = some fiber → fiber.phase = .reloading code accumulator view →
      ¬ Target r name view →
      ((s = r ∧ tail = []) ∨ ∃ inverse next, land name code r s inverse next ∧ tail = [inverse]) →
      Step land undo r (mark s name (.unloading (tail ++ accumulator) view))
  | leave (r name fiber accumulator view) :
      r name = some fiber → fiber.phase = .active accumulator view → ¬ Target r name view →
      Step land undo r (mark r name (.unloading accumulator view))
  | unload (r name fiber accumulator view) :
      r name = some fiber → fiber.phase = .unloading accumulator view → ¬ Relied r name →
      Step land undo r (mark (discharge undo accumulator r) name .inactive)

@[simp] theorem put_self (r : R) (name : Name) (fiber : F) :
    put r name fiber name = some fiber := by simp [put]

@[simp] theorem modify_self (r : R) (name : Name) (change : F → F) :
    modify r name change name = (r name).map change := by simp [modify]

theorem mark_self (r : R) (name : Name) (fiber : F) (phase)
    (present : r name = some fiber) :
    mark r name phase name = some { fiber with phase := phase } := by
  simp [mark, present]

theorem retire_preserves_tables (r : R) (name other : Name) (key : Key) :
    ((retire r name) other).bind (fun f => f.table key) =
      (r other).bind (fun f => f.table key) := by
  by_cases same : other = name
  · subst other; cases h : r name <;> simp [retire, modify, h]
  · simp [retire, modify, same]

theorem retirement_has_no_target (r : R) (name : Name) (view : View Name Key) :
    ¬ Target (retire r name) name view := by
  cases h : r name <;> simp [Target, retire, modify, h]

/- Exact captured inverse order, not merely reversal of a list of declarations. -/

omit [DecidableEq Name] in
theorem child_prevents_removal (r : R) (parent child : Name) (fiber : F)
    (present : r child = some fiber) (parentOf : fiber.parent = some parent) :
    ¬ Removable r parent := by
  intro ready
  cases h : r parent with
  | none => simp [Removable, h] at ready
  | some entry =>
    simp only [Removable, h] at ready
    have noChild := (show entry.retired = true ∧ entry.phase = .inactive ∧
      (∀ key, entry.table key = none) ∧ _ from ready).2.2.2 child
    simp [present, parentOf] at noChild

end Cordis.Calculus
