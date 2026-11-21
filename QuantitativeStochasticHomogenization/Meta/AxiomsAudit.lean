import Lean.Elab.Command
import QuantitativeStochasticHomogenization

/-!
# Axiom audit

Every declaration of the library, that is, every declaration of a module whose name starts with
`QuantitativeStochasticHomogenization`, is checked to depend on no axiom other than `propext`,
`Classical.choice` and `Quot.sound`. The check runs when this module is compiled; the module is
built with the library and is not imported by the root.
-/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let root : Name := `QuantitativeStochasticHomogenization
  let mut checked : Nat := 0
  for (name, _) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless root.isPrefixOf env.header.moduleNames[idx.toNat]! do continue
    checked := checked + 1
    for ax in ← liftCoreM (collectAxioms name) do
      unless allowed.contains ax do
        throwError "{name} depends on the axiom {ax}"
  logInfo m!"axiom audit: {checked} declarations checked"
