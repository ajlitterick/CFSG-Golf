module

public import Certificates.Kernel.Co2.Join
public import CFSG.Certificates.Kernel.Th.S.BigS
public import CFSG.Certificates.Kernel.Th.S.DceS
public import CFSG.Certificates.Kernel.Th.S.OutS
public import CFSG.Certificates.Kernel.Th.S.TsS
public meta import Lean

public section

namespace CertificateChecks.KernelTh

open CFSG.KC CFSG.KC.Loop CertificateChecks.KernelCo2

theorem andB_true {a b : Bool} (ha : a = true) (hb : b = true) : CFSG.KC.Th.andB a b = true := by
  subst ha
  exact hb


open CFSG.KC.Th


end CertificateChecks.KernelTh

namespace CertificateChecks.KernelTh.Thm

open Lean Elab Command Term Meta

elab "kernel_exact " v:term : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let g ← Lean.Elab.Tactic.getMainGoal
    let e ← Lean.Elab.Tactic.elabTerm v none
    let e ← instantiateMVars e
    if e.hasMVar then throwError "kernel_exact: the term has metavariables{indentExpr e}"
    g.assign e
    Lean.Elab.Tactic.replaceMainGoal []

elab "#th_list_of " nm:ident thm:ident : command => do
  let name := (← getCurrNamespace) ++ nm.getId
  let t ← liftCoreM <| realizeGlobalConstNoOverload thm
  let some ci := (← getEnv).find? t | throwError "unknown theorem {t}"
  let some (_, l, _, _) := CertificateChecks.KernelCo2.Join.parts ci.type
    | throwError "{t}: not a slice check"
  let ty := mkApp (mkConst ``List [0]) (mkConst ``Nat)
  let d : DefinitionVal := { name, levelParams := [], type := ty, value := l, hints := .regular 0, safety := .safe }
  liftCoreM <| withOptions (Elab.async.set · false) <| addDecl (.defnDecl d)

end CertificateChecks.KernelTh.Thm
