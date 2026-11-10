module

public import Certificates.Kernel.SporSch.Th.PlaneText
public import Certificates.Kernel.SporSch.Th.Plane2320K
public import Certificates.Data.Kernel.SporSch.Sep2318
public import CFSG.Sporadic.ThSchreier.PlaneSepArithInputs
meta import CFSG.Sporadic.ThSchreier.PlaneSepArithInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_strof CertificateChecks.KernelSporSch.Th2318STc CFSG.Sporadic.ThSchreier.sepTree
#kss_natlist CertificateChecks.KernelSporSch.Th2318SF CFSG.Sporadic.ThSchreier.sepFNats
#kss_natlist CertificateChecks.KernelSporSch.Th2318SR CFSG.Sporadic.ThSchreier.sepRowNats
#kss_natlist CertificateChecks.KernelSporSch.Th2318ST CFSG.Sporadic.ThSchreier.sepTree

namespace CertificateChecks.KernelSporSch.Th2318

open CFSG.Sporadic.Th.Native CFSG.Sporadic.ThSchreier

meta def fiArr : Array V4 := invRows sepFRows
meta def ciArr : Array V4 := invRows sepCRows
meta def afArr : Array V4 := mulRows CFSG.Sporadic.Th.Max3.rowsA sepFRows
meta def atArr : Array V4 := transposeRows CFSG.Sporadic.Th.Max3.rowsA
meta def bfArr : Array V4 := mulRows CFSG.Sporadic.Th.Max3.rowsB sepFRows
meta def btArr : Array V4 := transposeRows CFSG.Sporadic.Th.Max3.rowsB
meta def cfArr : Array V4 := mulRows sepCRows sepFRows
meta def ctArr : Array V4 := transposeRows sepCRows

end CertificateChecks.KernelSporSch.Th2318

#kss_v4rows CertificateChecks.KernelSporSch.Th2318FI CertificateChecks.KernelSporSch.Th2318.fiArr
#kss_v4rows CertificateChecks.KernelSporSch.Th2318CI CertificateChecks.KernelSporSch.Th2318.ciArr
#kss_v4rows CertificateChecks.KernelSporSch.Th2318AF CertificateChecks.KernelSporSch.Th2318.afArr
#kss_v4rows CertificateChecks.KernelSporSch.Th2318AT CertificateChecks.KernelSporSch.Th2318.atArr
#kss_v4rows CertificateChecks.KernelSporSch.Th2318BF CertificateChecks.KernelSporSch.Th2318.bfArr
#kss_v4rows CertificateChecks.KernelSporSch.Th2318BT CertificateChecks.KernelSporSch.Th2318.btArr
#kss_v4rows CertificateChecks.KernelSporSch.Th2318CF CertificateChecks.KernelSporSch.Th2318.cfArr
#kss_v4rows CertificateChecks.KernelSporSch.Th2318CT CertificateChecks.KernelSporSch.Th2318.ctArr
#kss_v4rows CertificateChecks.KernelSporSch.Th2318G CFSG.Sporadic.ThSchreier.sepGramRows

namespace CertificateChecks.KernelSporSch.Th2318

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch CFSG.Sporadic.Th.Native CFSG.Sporadic.ThSchreier
open CertificateChecks.KernelSporSch

@[expose] noncomputable def fFI (i : Nat) : Bool := Nat.beq (vmT Th2318FI (Th2318SF i)) (Nat.shiftLeft 1 i)
@[expose] noncomputable def fIF (i : Nat) : Bool := Nat.beq (vmT Th2318SF (Th2318FI i)) (Nat.shiftLeft 1 i)
@[expose] noncomputable def fCI (i : Nat) : Bool := Nat.beq (vmT Th2318CI (Th2318SR i)) (Nat.shiftLeft 1 i)
@[expose] noncomputable def fIC (i : Nat) : Bool := Nat.beq (vmT Th2318SR (Th2318CI i)) (Nat.shiftLeft 1 i)
@[expose] noncomputable def fAF (i : Nat) : Bool := Nat.beq (vmT Th2318SF (ThA i)) (Th2318AF i)
@[expose] noncomputable def fAFA (i : Nat) : Bool := Nat.beq (vmT Th2318AT (Th2318AF i)) (Th2318SF i)
@[expose] noncomputable def fBF (i : Nat) : Bool := Nat.beq (vmT Th2318SF (ThB i)) (Th2318BF i)
@[expose] noncomputable def fBFB (i : Nat) : Bool := Nat.beq (vmT Th2318BT (Th2318BF i)) (Th2318SF i)
@[expose] noncomputable def fCF (i : Nat) : Bool := Nat.beq (vmT Th2318SF (Th2318SR i)) (Th2318CF i)
@[expose] noncomputable def fG (i : Nat) : Bool := Nat.beq (vmT Th2318CT (Th2318CF i)) (Th2318G i)

@[expose] noncomputable def sFI (q : Nat) : Bool := allBlk (Nat.mul 31 q) fFI 31
@[expose] noncomputable def sIF (q : Nat) : Bool := allBlk (Nat.mul 31 q) fIF 31
@[expose] noncomputable def sCI (q : Nat) : Bool := allBlk (Nat.mul 31 q) fCI 31
@[expose] noncomputable def sIC (q : Nat) : Bool := allBlk (Nat.mul 31 q) fIC 31
@[expose] noncomputable def sAF (q : Nat) : Bool := allBlk (Nat.mul 31 q) fAF 31
@[expose] noncomputable def sAFA (q : Nat) : Bool := allBlk (Nat.mul 31 q) fAFA 31
@[expose] noncomputable def sBF (q : Nat) : Bool := allBlk (Nat.mul 31 q) fBF 31
@[expose] noncomputable def sBFB (q : Nat) : Bool := allBlk (Nat.mul 31 q) fBFB 31
@[expose] noncomputable def sCF (q : Nat) : Bool := allBlk (Nat.mul 31 q) fCF 31
@[expose] noncomputable def sG (q : Nat) : Bool := allBlk (Nat.mul 31 q) fG 31

@[expose] noncomputable def tF (q : Nat) : Bool := allBlk (Nat.mul 31 q) (sepTrK Th2318SF Th2318SF) 31
@[expose] noncomputable def tA (q : Nat) : Bool := allBlk (Nat.mul 31 q) (sepTrK ThA Th2318AT) 31
@[expose] noncomputable def tB (q : Nat) : Bool := allBlk (Nat.mul 31 q) (sepTrK ThB Th2318BT) 31
@[expose] noncomputable def tC (q : Nat) : Bool := allBlk (Nat.mul 31 q) (sepTrK Th2318SR Th2318CT) 31

end CertificateChecks.KernelSporSch.Th2318

#kc_slices CertificateChecks.KernelSporSch.Th2318.FIs CertificateChecks.KernelSporSch.Th2318.sFI 8
#kc_slices CertificateChecks.KernelSporSch.Th2318.IFs CertificateChecks.KernelSporSch.Th2318.sIF 8
#kc_slices CertificateChecks.KernelSporSch.Th2318.CIs CertificateChecks.KernelSporSch.Th2318.sCI 8
#kc_slices CertificateChecks.KernelSporSch.Th2318.ICs CertificateChecks.KernelSporSch.Th2318.sIC 8
#kc_slices CertificateChecks.KernelSporSch.Th2318.AFs CertificateChecks.KernelSporSch.Th2318.sAF 8
#kc_slices CertificateChecks.KernelSporSch.Th2318.AFAs CertificateChecks.KernelSporSch.Th2318.sAFA 8
#kc_slices CertificateChecks.KernelSporSch.Th2318.BFs CertificateChecks.KernelSporSch.Th2318.sBF 8
#kc_slices CertificateChecks.KernelSporSch.Th2318.BFBs CertificateChecks.KernelSporSch.Th2318.sBFB 8
#kc_slices CertificateChecks.KernelSporSch.Th2318.CFs CertificateChecks.KernelSporSch.Th2318.sCF 8
#kc_slices CertificateChecks.KernelSporSch.Th2318.Gs CertificateChecks.KernelSporSch.Th2318.sG 8
#kc_slices CertificateChecks.KernelSporSch.Th2318.TFs CertificateChecks.KernelSporSch.Th2318.tF 8
#kc_slices CertificateChecks.KernelSporSch.Th2318.TAs CertificateChecks.KernelSporSch.Th2318.tA 8
#kc_slices CertificateChecks.KernelSporSch.Th2318.TBs CertificateChecks.KernelSporSch.Th2318.tB 8
#kc_slices CertificateChecks.KernelSporSch.Th2318.TCs CertificateChecks.KernelSporSch.Th2318.tC 8

namespace CertificateChecks.KernelSporSch.Th2318

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch CFSG.Sporadic.Th.Native CFSG.Sporadic.ThSchreier
open CFSG.Sporadic.Th CFSG.Sporadic.Th.FormBase
open CertificateChecks.KernelSporSch


theorem symm : ((List.range 124).all fun i => (List.range 124).all fun j =>
    invCode (sepCodeK Th2318G i j) == invCode (sepCodeK Th2318G j i)) = true := by quickRfl


end CertificateChecks.KernelSporSch.Th2318

end
