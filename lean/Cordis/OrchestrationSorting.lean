import Cordis.TranspositionOrchestration

/-! External command payloads for transposition and deletion. An insertion
records the exact component, and retirement and removal record the actor. -/
namespace Cordis.OrchestrationSorting
open Calculus Stages Labeled Transposition
universe u
variable {Name Key Value Code Error : Type u}
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
variable [DecidableEq Name] [DecidableEq Key]
set_option linter.unusedSectionVars false

inductive Command (Name Key Code : Type u) where
  | insert (name : Name) (component : Component Key Code)
  | retire (name : Name)
  | remove (name : Name)

def Command.actor : Command Name Key Code → Name
  | .insert name _ | .retire name | .remove name => name

def Command.apply (command : Command Name Key Code) (r : R) : R :=
  match command with
  | .insert name component => put r name (fresh component none)
  | .retire name => Calculus.retire r name
  | .remove name => erase r name

def Command.Enabled (command : Command Name Key Code) (r : R) : Prop :=
  match command with
  | .insert name component => Insertable r name component none
  | .retire name => r name ≠ none
  | .remove name => Removable r name

def Command.Step (command : Command Name Key Code) (r s : R) : Prop :=
  command.Enabled r ∧ s = command.apply r

private theorem insertable_of_insert (program : Code → Instruction Name Key Value Code Error)
    (source : R) (name : Name) (component : Component Key Code)
    (inserted : Labeled.Step program .insert name source (put source name (fresh component none))) :
    Insertable source name component none := by
  generalize endpoint : put source name (fresh component none) = after at inserted
  cases inserted
  rename_i selected parent ready
  have entries := congrFun endpoint name
  simp only [put_self] at entries
  have fields := Option.some.inj entries
  have componentEq := congrArg Fiber.component fields
  have parentEq := congrArg Fiber.parent fields
  change component = selected at componentEq
  change none = parent at parentEq
  subst selected
  subst parent
  exact ready

/-- Exchange a lifecycle activation with a named external command while
preserving the command's full payload, including the inserted component. -/
theorem activation_command_diamond (program : Code → Instruction Name Key Value Code Error)
    {rule : Rule} {actor : Name} {before middle : R} (command : Command Name Key Code)
    (activation : Labeled.Step program rule actor before middle)
    (active : Activation rule) (enabled : command.Enabled middle)
    (different : actor ≠ command.actor)
    (notCreated : before command.actor = none → middle command.actor = none) :
    command.Enabled before ∧
      Labeled.Step program rule actor (command.apply before) (command.apply middle) := by
  cases command with
  | insert name component =>
    obtain ⟨earlier, swapped⟩ := activation_insert_diamond program activation active name component different enabled
    exact ⟨insertable_of_insert program before name component earlier, swapped⟩
  | retire name =>
    have earlier : before name ≠ none := fun absent => enabled (notCreated absent)
    exact ⟨earlier, activation_after_retirement program activation active name different earlier⟩
  | remove name =>
    obtain ⟨earlier, swapped⟩ := activation_remove_diamond program activation active name different enabled
    generalize endpoint : erase before name = after at earlier
    cases earlier
    exact ⟨by assumption, swapped⟩

end Cordis.OrchestrationSorting
