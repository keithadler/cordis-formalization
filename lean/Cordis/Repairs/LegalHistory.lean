import Cordis.Repairs.CausalCommands

/-! The proposed Theorem 80 repair preserves the root-command subsequence
and uses legal exchanges. These finite histories retain full orchestration
payloads, not merely their rule/actor labels. Every step is a native rule.
The local exchange theorems lift inside an arbitrary front and suffix,
with exactly the same initial and final registries. -/
namespace Cordis.Repairs.LegalHistory
open Calculus Stages OrchestrationSorting CausalCommands
universe u
variable {Name Key Value Code Error : Type u} [DecidableEq Name] [DecidableEq Key]
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "Cmd" => Command Name Key Code

inductive Lifecycle where
  | begin | iter | finish | divert | leave | unload
  deriving DecidableEq

def Lifecycle.rule : Lifecycle → Labeled.Rule
  | .begin => .begin | .iter => .iter | .finish => .finish
  | .divert => .divert | .leave => .leave | .unload => .unload

inductive Event (Name Key Code : Type u) where
  | command (command : Command Name Key Code)
  | lifecycle (kind : Lifecycle) (actor : Name)

def Event.Step (program : Code → Instruction Name Key Value Code Error) :
    Event Name Key Code → R → R → Prop
  | .command cmd => cmd.Step
  | .lifecycle kind actor => Labeled.Step program kind.rule actor

def Event.rootCommand (roots : Name → Bool) : Event Name Key Code → Option Cmd
  | .command cmd => if roots cmd.actor then some cmd else none
  | .lifecycle _ _ => none

def rootCommands (roots : Name → Bool) (events : List (Event Name Key Code)) : List Cmd :=
  events.filterMap (Event.rootCommand roots)

inductive Exec (program : Code → Instruction Name Key Value Code Error) :
    List (Event Name Key Code) → R → R → Prop
  | nil (state) : Exec program [] state state
  | cons {event events before middle after} : Event.Step program event before middle →
      Exec program events middle after → Exec program (event :: events) before after

variable {program : Code → Instruction Name Key Value Code Error}

theorem Event.Step.toCalculus {event : Event Name Key Code} {before after : R}
    (step : event.Step program before after) :
    Calculus.Step (Land program) Stages.undo before after := by
  cases event with
  | lifecycle kind actor => exact Labeled.Step.toCalculus step
  | command command =>
    obtain ⟨enabled, rfl⟩ := step
    cases command with
    | insert name component => exact .insert before name component none enabled
    | retire name => exact .retire before name enabled
    | remove name => exact .remove before name enabled

theorem Exec.extendRun {events : List (Event Name Key Code)} {initial before after : R}
    (execution : Exec program events before after) (earlier : WellFormed.Run program initial before) :
    WellFormed.Run program initial after := by
  induction execution with
  | nil => exact earlier
  | cons step _ ih => exact ih (.step earlier step.toCalculus)

theorem Exec.toRun {events : List (Event Name Key Code)} {before after : R}
    (execution : Exec program events before after) : WellFormed.Run program before after :=
  execution.extendRun (.refl before)

theorem Exec.append {first second : List (Event Name Key Code)} {before middle after : R}
    (front : Exec program first before middle) (suffix : Exec program second middle after) :
    Exec program (first ++ second) before after := by
  induction front with
  | nil => exact suffix
  | cons step _ ih => exact .cons step (ih suffix)

theorem Exec.split {first second : List (Event Name Key Code)} {before after : R}
    (execution : Exec program (first ++ second) before after) :
    ∃ middle, Exec program first before middle ∧ Exec program second middle after := by
  induction first generalizing before with
  | nil => exact ⟨before, .nil before, execution⟩
  | cons event rest ih =>
    cases execution with
    | cons step tail =>
      obtain ⟨middle, front, suffix⟩ := ih tail
      exact ⟨middle, .cons step front, suffix⟩

omit [DecidableEq Name] [DecidableEq Key] in
theorem rootCommands_swap (roots : Name → Bool) (first second : Cmd)
    (oneChild : roots first.actor = false ∨ roots second.actor = false)
    (front suffix : List (Event Name Key Code)) :
    rootCommands roots (front ++ .command first :: .command second :: suffix) =
      rootCommands roots (front ++ .command second :: .command first :: suffix) := by
  cases a : roots first.actor <;> cases b : roots second.actor <;>
    simp_all [rootCommands, Event.rootCommand, List.filterMap_append]

omit [DecidableEq Name] [DecidableEq Key] in
theorem rootCommands_activation_swap (roots : Name → Bool) (kind : Lifecycle)
    (actor : Name) (command : Cmd) (front suffix : List (Event Name Key Code)) :
    rootCommands roots (front ++ .lifecycle kind actor :: .command command :: suffix) =
      rootCommands roots (front ++ .command command :: .lifecycle kind actor :: suffix) := by
  cases h : roots command.actor <;>
    simp [rootCommands, Event.rootCommand, h, List.filterMap_append]

/-- A legal command exchange inside any finite history. Neither root command
order nor applicability is replaced by an unrestricted permutation assumption. -/
theorem exchange_commands (roots : Name → Bool) (first second : Cmd)
    {front suffix : List (Event Name Key Code)} {initial before middle after final : R}
    (prefixRun : Exec program front initial before)
    (a : first.Step before middle) (b : second.Step middle after)
    (suffixRun : Exec program suffix after final)
    (different : first.actor ≠ second.actor) (earlier : second.Enabled before)
    (oneChild : roots first.actor = false ∨ roots second.actor = false) :
    Exec program (front ++ .command second :: .command first :: suffix) initial final ∧
      rootCommands roots (front ++ .command first :: .command second :: suffix) =
        rootCommands roots (front ++ .command second :: .command first :: suffix) := by
  obtain ⟨swapped, firstStep, secondStep⟩ := command_diamond first second a b different earlier
  exact ⟨prefixRun.append (.cons firstStep (.cons secondStep suffixRun)),
    rootCommands_swap roots first second oneChild front suffix⟩

/-- The birth exception is explicit: a command cannot be moved before the
activation that created its actor. All other applicability facts follow from
the native activation-command diamond, with the exact command payload. -/
theorem exchange_activation (roots : Name → Bool) (kind : Lifecycle) (actor : Name) (command : Cmd)
    {front suffix : List (Event Name Key Code)} {initial before middle after final : R}
    (prefixRun : Exec program front initial before)
    (activation : Labeled.Step program kind.rule actor before middle)
    (active : Transposition.Activation kind.rule) (external : command.Step middle after)
    (suffixRun : Exec program suffix after final) (different : actor ≠ command.actor)
    (notCreated : before command.actor = none → middle command.actor = none) :
    Exec program (front ++ .command command :: .lifecycle kind actor :: suffix) initial final ∧
      rootCommands roots (front ++ .lifecycle kind actor :: .command command :: suffix) =
        rootCommands roots (front ++ .command command :: .lifecycle kind actor :: suffix) := by
  obtain ⟨enabled, rfl⟩ := external
  obtain ⟨earlier, swapped⟩ := activation_command_diamond program command activation active enabled different notCreated
  exact ⟨prefixRun.append (.cons ⟨earlier, rfl⟩ (.cons swapped suffixRun)),
    rootCommands_activation_swap roots kind actor command front suffix⟩

end Cordis.Repairs.LegalHistory
