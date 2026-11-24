import Cordis.Labeled
import Cordis.PaperEffectEquations
import Cordis.TypedCoeffectReplay

/-! Definitions 29, 30 and 56 with a distinct value type at each key and a
distinct outcome type at each operation. The encoding feeds the same program
to the existing registry proofs. -/
namespace Cordis.TypedRegistry
open Calculus
open PaperEffectEquations (CoeffectOperations)
open TypedCoeffectReplay (Encoded pack unpack encodeMap)
universe u
variable {Name Key Code : Type u} {V : Key → Type u}

abbrev Yield (ops : CoeffectOperations V) :=
  (key : Key) × (name : ops.Name key) × ops.Outcome key name

abbrev Scalar (ops : CoeffectOperations V) := Encoded V (Yield ops)

inductive Outcome (Name : Type u) (ops : CoeffectOperations V) where
  | unit
  | provision (key : Key) (value : V key)
  | operation (key : Key) (name : ops.Name key) (outcome : ops.Outcome key name)
  | child (name : Name)

inductive Action (Name : Type u) (ops : CoeffectOperations V) (Code : Type u) where
  | unit
  | provide (key : Key) (value : V key)
  | operate (key : Key) (name : ops.Name key) (argument : ops.Argument key name)
  | instantiate (component : Component Key Code)

structure Instruction (Name : Type u) (ops : CoeffectOperations V) (Code : Type u) where
  action : Action Name ops Code
  next : Outcome Name ops → Option Code

def packOutcome (ops : CoeffectOperations V) (key : Key) (name : ops.Name key)
    (value : ops.Outcome key name) : Scalar ops :=
  .inr (.inr ⟨key, name, value⟩)

def encodeOutcome (ops : CoeffectOperations V) : Outcome Name ops → Stages.Outcome Name (Scalar ops)
  | .unit => .unit
  | .provision key value => .value (pack key value)
  | .operation key name value => .value (packOutcome ops key name value)
  | .child name => .child name

def decodeOutcome (ops : CoeffectOperations V) : Stages.Outcome Name (Scalar ops) → Option (Outcome Name ops)
  | .unit => some .unit
  | .child name => some (.child name)
  | .value (.inl (some ⟨key, value⟩)) => some (.provision key value)
  | .value (.inr (.inr ⟨key, name, value⟩)) => some (.operation key name value)
  | .value (.inl none) | .value (.inr (.inl _)) => none

@[simp] theorem decode_encodeOutcome (ops : CoeffectOperations V) (outcome : Outcome Name ops) :
    decodeOutcome ops (encodeOutcome ops outcome) = some outcome := by
  cases outcome <;> rfl

variable [DecidableEq Key]

/-- A successful call retains the key, the actual partial inverse, and the
operation's own outcome type. Incorrectly tagged input cannot call it. -/
def encodeOperation (ops : CoeffectOperations V) (key : Key) (name : ops.Name key)
    (argument : ops.Argument key name) (input : Scalar ops) :
    Except (PUnit.{u + 1}) (Scalar ops × (Scalar ops → Scalar ops) × Scalar ops) :=
  match unpack key input with
  | none => .error .unit
  | some value =>
    match (ops.operation key name argument).run value with
    | none => .error .unit
    | some (out, inverse, outcome) => .ok (pack key out, encodeMap key inverse, packOutcome ops key name outcome)

def encodeAction (ops : CoeffectOperations V) : Action Name ops Code → Stages.Action Name Key (Scalar ops) Code (PUnit.{u + 1})
  | .unit => .unit
  | .provide key value => .provide key (pack key value)
  | .operate key name argument => .operate key (encodeOperation ops key name argument)
  | .instantiate component => .instantiate component

def encodeInstruction {ops : CoeffectOperations V} (instruction : Instruction Name ops Code) :
    Stages.Instruction Name Key (Scalar ops) Code (PUnit.{u + 1}) :=
  ⟨encodeAction ops instruction.action, fun outcome => (decodeOutcome ops outcome).bind instruction.next⟩

abbrev encodeProgram {ops : CoeffectOperations V} (program : Code → Instruction Name ops Code) :
    Code → Stages.Instruction Name Key (Scalar ops) Code (PUnit.{u + 1}) :=
  encodeInstruction ∘ program

@[simp] theorem encodeInstruction_next {ops : CoeffectOperations V} (instruction : Instruction Name ops Code)
    (outcome : Outcome Name ops) :
    (encodeInstruction instruction).next (encodeOutcome ops outcome) = instruction.next outcome := by
  simp [encodeInstruction]

end Cordis.TypedRegistry
