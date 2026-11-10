module

public import Certificates.Data.Kernel.SporSch.MathieuOC2
import CFSG.Certificates.Kernel.SporSch.ChainKRepsL
public import CFSG.Certificates.Kernel.SporSch.MOCChain
public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses
public import Certificates.Data.Kernel.Spor.MCount

public section

namespace CFSG.KS.SporSch.MOC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MEnum
open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.Th.Native CFSG.Monster.B.Mathieu

@[expose] def Counts2 (LR : Nat → Nat) (CS : List (List Nat)) (f : Nat → Nat → Nat) : Prop :=
  CS.length = rcnt (LR 0) ∧ ∀ k₀ < rcnt (LR 0), (CS.getD k₀ []).length = rcnt (LR 1) ∧
    ∀ k₁ < rcnt (LR 1), f k₀ k₁ = (CS.getD k₀ []).getD k₁ 0

variable {n w : Nat} {gens : List (Equiv.Perm (Fin n))} {words : List (List Int)} {k : Nat}
  {bv : Vector (Fin n) k} {PS PSI LR TR TRI : Nat → Nat} {kS BP NS CH : Nat}

theorem chainK_commCount (hn : 1 ≤ n) (hbs : bv.toList.Nodup)
    (hQ : ChainK n w gens words bv PS PSI LR TR TRI kS BP NS CH) {g₀ gA gB : Equiv.Perm (Fin n)}
    {G₀ A B : Nat} (hg₀ : imageList g₀ = (unpack n w G₀).toList)
    (_hG₀ : canonK n w (mask w) (n * w) G₀ = true)
    (hA : imageList gA = (unpack n w A).toList) (_hcA : canonK n w (mask w) (n * w) A = true)
    (hB : imageList gB = (unpack n w B).toList) (_hcB : canonK n w (mask w) (n * w) B = true)
    (hk : 2 ≤ k) {CS : List (List Nat)}
    (hc : Counts2 LR CS (cntCommK n w (mask w) (n * w) LR TR k G₀ A B)) :
    countProducts n (commAll n [toTable gA, toTable gB])
      (levelTables (certificate hn gens words bv hbs)) (toTable g₀) = (CS.map List.sum).sum :=
  chainK_commCount' hQ hn hbs hg₀ hA hB hk hc

theorem chainK_cosetCount2 (hn : 1 ≤ n) (hbs : bv.toList.Nodup)
    (hQ : ChainK n w gens words bv PS PSI LR TR TRI kS BP NS CH) {g₀ : Equiv.Perm (Fin n)}
    {G₀ e : Nat} (hg₀ : imageList g₀ = (unpack n w G₀).toList)
    (_hG₀ : canonK n w (mask w) (n * w) G₀ = true) (he : 0 < e) (hk : 2 ≤ k)
    {CS : List (List Nat)}
    (hc : Counts2 LR CS (cntOrd2K n w (mask w) (n * w) (pidn n w) LR TR k G₀ e)) :
    (cosetOrderTables (certificate hn gens words bv hbs) g₀ e).length = (CS.map List.sum).sum :=
  chainK_cosetCount2' hQ hn hbs hg₀ he hk hc


theorem mulK_rep {g h : Equiv.Perm (Fin n)} {G H : Nat} (hsz : szOK n w = true)
    (hg : imageList g = (unpack n w G).toList) (hh : imageList h = (unpack n w H).toList) :
    imageList (g * h) = (unpack n w (pcomp n w (mask w) G H)).toList :=
  mulK_rep' hsz hg hh

theorem invK_rep {g : Equiv.Perm (Fin n)} {G Gi : Nat}
    (hg : imageList g = (unpack n w G).toList) (h : permOK n w (mask w) (n * w) G Gi = true) :
    imageList g⁻¹ = (unpack n w Gi).toList :=
  invK_rep' hg h

end CFSG.KS.SporSch.MOC

end
