import Kobon
import Lean.Util.CollectAxioms

/-! Every theorem in the active project is checked for unapproved axioms.
Native evaluation is permitted and reported separately; sorryAx is not. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := env.constants.fold (init := #[]) fun names name info =>
    if name.toString.startsWith "Kobon" && info.isTheorem then names.push name else names
  for name in names do
    let axioms ← Lean.collectAxioms name
    let mut native := false
    for ax in axioms do
      if ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound then
        pure ()
      else if (ax.toString.splitOn "native_decide.ax_").length > 1 then
        native := true
      else
        throwError "Unapproved axiom {ax} in {name}"
    logInfo m!"AUDIT {name}: {if native then "native-evaluation" else "kernel"}; axioms={axioms}"
  logInfo m!"AUDIT_TOTAL {names.size}"
