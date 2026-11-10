module

public import CFSG.Monster.B.CTIB.Rep4371Spin

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.CTIB

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Griess CFSG.Monster.Visible
  CFSG.Monster.SpinLattice CFSG.Monster.Spin CFSG.Monster.ScalarKernel CFSG.Monster.B
  CFSG.Monster.B.Short CFSG.Monster.B.TwoA CFSG.Monster.B.Rep4371 Matrix
open CFSG.Monster.B.Co2 (v0)

@[expose] def ehatS (e : Ehat) : Shat := ⟨e, Ehat_le_Shat' e.2⟩


theorem ehatS_mul (e f : Ehat) : ehatS (e * f) = ehatS e * ehatS f := rfl

theorem ehatS_one : ehatS 1 = 1 := rfl

theorem psiW_eq_zero_iff_coordOf {q : Q} (hq : q ∈ Subgroup.centralizer {rStar}) {e : Ehat}
    (hqe : iotaD (kappa ⟨rhoEquiv q, rhoEquiv_mem_Cgen hq⟩) = e) :
    psiW e = 0 ↔ coordOf q = 0 ∨ coordOf q = coordOf rStar := by
  have he : iotaD (kappa ⟨rhoEquiv q, rhoEquiv_mem_Cgen hq⟩) ∈ Ehat := by rw [hqe]; exact e.2
  have e1 : e = ⟨_, he⟩ := Subtype.ext hqe.symm
  rw [e1, psiW_iotaD_rho hq he, LinearEquiv.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero]
  show phi0 (coordOf q) ∈ vLineL (phi0 (coordOf rStar)) ↔ _
  exact mem_vLineL.trans (or_congr (phi0_injective.eq_iff' (map_zero phi0)) phi0_injective.eq_iff)

theorem trace_blkM_Ehat_eq_zero
    {e : Ehat} (he : psiW e ≠ 0) :
    Matrix.trace (blkM (ehatS e)) = 0 := by
  obtain ⟨q, hq, hqe⟩ := exists_of_mem_Ehat e.2
  have e1 : ehatS e = shatQ q hq := Subtype.ext hqe.symm
  rw [e1]
  have h := mt (psiW_eq_zero_iff_coordOf hq hqe).2 he
  rw [not_or] at h
  exact trace_blkM_shatQ_eq_zero hq h.1 h.2

theorem blkM_xhat :
    blkM (ehatS xhatE) = -1 := by
  have e1 : ehatS xhatE = shatQ zQ zQ_mem_centralizer_rStar := Subtype.ext rfl
  ext s t
  rw [e1, blkM_shatQ, Rq, coe_zQ, coe_zU, zmat, Matrix.neg_apply, Matrix.neg_apply,
    Matrix.one_apply, Matrix.one_apply]
  by_cases h : s = t
  · rw [ite_eq_left (congrArg spinIdx h.symm), ite_eq_left h]
  · rw [ite_eq_right (fun h' => h (spinIdx_injective h').symm), ite_eq_right h]


theorem card_Wv
    [Fintype (Wv v0)] : Fintype.card (Wv v0) = 2 ^ 22 := by
  rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card, Co2.finrank_W]


@[expose] noncomputable def spinCrd
    (v : Vst) : Fin 2048 → ℚ := fun s => Rbasis.repr v (tIdx s)

theorem spinCrd_rhoV
    (h : Shat) {v : Vst} (hv : v ∈ V2048) :
    spinCrd (rhoV h v) = blkM h *ᵥ spinCrd v := by
  funext s
  rw [spinCrd, repr_rhoV_blk h hv s]
  rfl

theorem repr_eq_zero_of_mem_span {v : Vst}
    (hv : v ∈ Submodule.span ℚ (Set.range fun t => Rbasis (tIdx t))) {k : Fin 4371}
    (hk : ∀ t, tIdx t ≠ k) : Rbasis.repr v k = 0 := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, rfl⟩ := hx
    rw [Module.Basis.repr_self, Finsupp.single_apply, ite_eq_right (hk t)]
  | zero => exact repr_zero' k
  | add x y _ _ hx hy => rw [repr_add, hx, hy, add_zero]
  | smul c x _ hx => rw [repr_smul, hx, mul_zero]

theorem eq_of_spinCrd {v w : Vst} (hv : v ∈ V2048) (hw : w ∈ V2048)
    (h : spinCrd v = spinCrd w) : v = w := by
  apply Rbasis.ext_elem
  intro k
  by_cases hk : ∃ t, tIdx t = k
  · obtain ⟨t, rfl⟩ := hk
    exact congrFun h t
  · push Not at hk
    rw [repr_eq_zero_of_mem_span (Tplus_span_Vst hv) hk,
      repr_eq_zero_of_mem_span (Tplus_span_Vst hw) hk]


theorem spinCrd_smul
    (c : ℚ) (x : Vst) : spinCrd (c • x) = c • spinCrd x :=
  funext fun _ => repr_smul c x _


theorem rhoV_xhat_V2048
    {v : Vst} (hv : v ∈ V2048) : rhoV (ehatS xhatE) v = (-1 : ℚ) • v := by
  have hmem : rhoV (ehatS xhatE) v ∈ V2048 :=
    (Jhat_preserves (Ehat_le_Jhat xhatE.2)).2.2 v hv
  refine eq_of_spinCrd hmem (V2048.smul_mem _ hv) ?_
  rw [spinCrd_rhoV _ hv, blkM_xhat, spinCrd_smul, Matrix.neg_mulVec, Matrix.one_mulVec,
    neg_one_smul]

theorem linearIndependent_RbT :
    LinearIndependent ℚ fun t : Fin 2048 => Rbasis (tIdx t) :=
  Rbasis.linearIndependent.comp _ tIdx_injective

theorem V2048_eq_span :
    V2048 = Submodule.span ℚ (Set.range fun t : Fin 2048 => Rbasis (tIdx t)) :=
  le_antisymm (fun _ hv => Tplus_span_Vst hv)
    (Submodule.span_le.2 (by rintro _ ⟨t, rfl⟩; exact Rbasis_tIdx_mem t))

end CFSG.Monster.B.CTIB
