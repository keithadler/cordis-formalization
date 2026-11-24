import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-! Axiom audit policy for the formalization. The traversal checks
definitions and private helpers as well as theorems, including their dependencies.
Module ownership also covers generated declarations outside the user namespace. -/

namespace Cordis.AxiomAudit

open Lean Elab Command

def check (root : Name) (extraModules : Array Name := #[]) : CommandElabM Unit := do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut declarations := 0
  let mut theorems := 0
  -- Shared dependencies need only one traversal across all selected roots.
  let mut traversal : CollectAxioms.State := {}
  for (name, info) in env.constants.toList do
    let origin := match env.getModuleIdxFor? name with
      | some index => env.header.moduleNames[index.toNat]!
      | none => env.mainModule
    if root.isPrefixOf (privateToUserName name) || root.isPrefixOf origin ||
        extraModules.contains origin then
      declarations := declarations + 1
      if let .thmInfo _ := info then
        theorems := theorems + 1
      traversal := ((CollectAxioms.collect name).run env).run traversal |>.2
      for ax in traversal.axioms do
        unless allowed.contains ax do
          throwError "Unapproved axiom {ax} in {name}"
  logInfo m!"{root} axiom audit passed: {declarations} declarations, {theorems} theorem declarations; only standard Lean axioms."

end Cordis.AxiomAudit
