module

public import CFSG.Certificates.Kernel.ListBridge.PackSound
public import Certificates.Data.Kernel.ListBridgeRoot
public import CFSG.ClassicalInvolution.SmallCases.NobqLists
import CFSG.Certificates.Kernel.BfsPinSetSound

public section

namespace CFSG.ClassicalInvolution.ListBridge

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KC.BfsPin
open CFSG.KC.ListBridge

section Group

variable {M : Type*} [Group M]


end Group

variable {n w : Nat}

theorem eq_of_prep_shr {P Q : Nat} {g h : Equiv.Perm (Fin n)} (hw : 0 < w)
    (hP : P >>> (n * w) = 0) (hQ : Q >>> (n * w) = 0) (gP : PRep n w P g) (hQr : PRep n w Q h)
    (e : g = h) : P = Q :=
  CFSG.KS.PF.eq_of_fields hw hP hQ fun i hi => by rw [gP ⟨i, hi⟩, hQr ⟨i, hi⟩, e]

theorem rootsK_sound {ng N : Nat} {G T E S WI : Nat → Nat} {gens : List (Equiv.Perm (Fin n))}
    {R : Nat} {r : Equiv.Perm (Fin n)} (hk : bfsK n w ng G N T E S = true)
    (hl : gens.length = ng) (hG : ∀ k < ng, PRep n w (G k) (gens.getD k 1))
    (hR : PRep n w R r) (h : rootsK n w R N T WI = true) :
    ∀ c ∈ Subgroup.closure {s | s ∈ gens}, c * c = r →
      ∃ g ∈ Subgroup.closure {s | s ∈ gens}, (c * (g * c * g⁻¹)) * (c * (g * c * g⁻¹)) = 1 ∧
        c * (g * c * g⁻¹) ≠ 1 ∧ c * (g * c * g⁻¹) ≠ r := by
  obtain ⟨hn, hw⟩ := bfsK_sz hk
  have hn32 : n < 2 ^ 32 := by omega
  have hnw : n < 2 ^ w := by omega
  have hw0 : 0 < w := CFSG.KS.PF.w_pos hw
  set H := Subgroup.closure {s | s ∈ gens} with hH
  obtain ⟨hmem, -⟩ := enum_closure hk hl hG
  have hQ := (bfsK_points (fun y => ∃ g ∈ H, PRep n w y g)
    ⟨1, H.one_mem, prep_pidn hn hw⟩ (fun y ⟨g, hg, hy⟩ k hk1 =>
      ⟨gens.getD k 1 * g, H.mul_mem (Subgroup.subset_closure (getD_mem (hl ▸ hk1))) hg,
        prep_pcomp hn32 (hG k hk1) hy⟩) hk).2.2.1
  unfold rootsK at h
  rw [Orb.strictB_eq] at h
  obtain ⟨hRc, hall⟩ := (bAnd_iff _ _).1 h
  have hRs := (CFSG.KS.PF.canon_facts hRc).2.2.1
  have hIs := CFSG.KS.PF.pidn_shr hn hw
  intro c hc hcc
  obtain ⟨i, hi, hci⟩ := (hmem c).1 hc
  have hi' := allN_spec hall i hi
  rw [Orb.strictB_eq] at hi'
  have hb : Nat.beq (pcomp n w (mask w) (T i) (T i)) R = true := by
    rw [eq_of_prep_shr hw0 (CFSG.KS.PF.pcomp_shr _ _ hn32 hw0) hRs (prep_pcomp hn32 hci hci) hR
      hcc]
    exact Nat.beq_refl _
  rw [hb] at hi'
  have hi2 : strictB (WI i) (fun j => bAnd(Nat.blt j N, rootWitK n w R (T i) (T j))) = true :=
    hi'
  rw [Orb.strictB_eq] at hi2
  obtain ⟨hj, hwit⟩ := (bAnd_iff _ _).1 hi2
  obtain ⟨g, hgH, hgT⟩ := hQ _ (Nat.blt_eq.mp hj)
  refine ⟨g, hgH, ?_⟩
  unfold rootWitK at hwit
  rw [Orb.strictB_eq] at hwit
  obtain ⟨hx2, hrest⟩ := (bAnd_iff _ _).1 hwit
  have hX := prep_pcomp hn32 hci (prep_pcomp hn32 (prep_pcomp hn32 hgT hci)
    (CFSG.KS.SporSch.MOC.prep_pinvS hnw hgT).1)
  have hXs := CFSG.KS.PF.pcomp_shr (T i) (pcomp n w (mask w) (pcomp n w (mask w) (T (WI i)) (T i))
    (pinvS n w (mask w) (T (WI i)))) hn32 hw0
  refine ⟨?_, fun e => ?_, fun e => ?_⟩
  · have h2 := prep_pcomp hn32 hX hX
    rw [Nat.eq_of_beq_eq_true hx2] at h2
    exact prep_unique h2 (prep_pidn hn hw)
  · rw [eq_of_prep_shr hw0 hXs hIs hX (prep_pidn hn hw) e, Nat.beq_refl] at hrest
    exact Bool.false_ne_true hrest
  · have e1 : Nat.beq (pcomp n w (mask w) (T i) (pcomp n w (mask w)
        (pcomp n w (mask w) (T (WI i)) (T i)) (pinvS n w (mask w) (T (WI i))))) (pidn n w) =
        false := by
      cases hb1 : Nat.beq (pcomp n w (mask w) (T i) (pcomp n w (mask w)
        (pcomp n w (mask w) (T (WI i)) (T i)) (pinvS n w (mask w) (T (WI i))))) (pidn n w)
      · rfl
      · rw [hb1] at hrest
        exact absurd hrest Bool.false_ne_true
    rw [e1, eq_of_prep_shr hw0 hXs hRs hX hR e, Nat.beq_refl] at hrest
    exact Bool.false_ne_true hrest

end CFSG.ClassicalInvolution.ListBridge

end
