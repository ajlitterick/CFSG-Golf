import Comparator.Solution
open Lean in
run_cmd do
  let ci ← getConstInfo ``CFSGComparator.classification
  let expected : Expr := .const ``TauCeti.ClassificationStatement [.param `u]
  unless ci.type == expected do
    throwError "statement changed: {ci.type}"
  unless ci.levelParams == [`u] do
    throwError "level params changed: {ci.levelParams}"
  logInfo "statement OK: CFSGComparator.classification : TauCeti.ClassificationStatement.{u}"
