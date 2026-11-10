module

public import CFSG.ClassicalInvolution.AschTight.S1911P3h
public import CFSG.ClassicalInvolution.AschTight.S1911SecG
public import CFSG.ClassicalInvolution.AschTight.S1911P3e
public import CFSG.ClassicalInvolution.AschTight.S1916FusStmt

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1911

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {K : Subgroup G} {z : G} {S : Sylow 2 G} {W : Subgroup G}

theorem secAct_eq_conj_of_residual {Y₀ : Type} [Group Y₀] {Y₁ : Subgroup Y₀} [Y₁.Normal]
    {s y : Y₀} (hy : y ∈ Y₁) (h : ∀ x ∈ Y₁, (s * y⁻¹) * x * (s * y⁻¹)⁻¹ * x⁻¹ ∈ oddCoreOf Y₁) :
    secAct Y₁ s = MulAut.conj (QuotientGroup.mk ⟨y, hy⟩) := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H x =>
    rw [secAct_mk, MulAut.conj_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv,
      ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have hx' : y * (x : Y₀) * y⁻¹ ∈ Y₁ := Y₁.mul_mem (Y₁.mul_mem hy x.2) (Y₁.inv_mem hy)
    obtain ⟨hwY, hwO⟩ := mem_oddCoreOf_iff.mp (h _ hx')
    have hN : (classicalInvolutionOddCore ↥Y₁).Normal := inferInstance
    have := (classicalInvolutionOddCore ↥Y₁).inv_mem
      (hN.conj_mem _ hwO (⟨y * (x : Y₀) * y⁻¹, hx'⟩)⁻¹)
    convert this using 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply]
    group


end CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
