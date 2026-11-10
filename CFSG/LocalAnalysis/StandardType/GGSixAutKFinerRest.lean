module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerBasic

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section HypParts

@[expose] def GGHypRestII (W : Type) [Group W] [Finite W] : Prop :=
  IsSimpleGroup ↥(CFSG.generalizedFitting W) ∧
    (∃ a b : ↥(CFSG.generalizedFitting W), a * b ≠ b * a) ∧
    InCatalog ↥(CFSG.generalizedFitting W)


@[expose] def GGHypRestIVComponentwise {W : Type} [Group W] [Finite W] (p : ℕ) (E : Subgroup W) : Prop :=
  (∀ x ∈ E, x ≠ 1 → ∀ C : Subgroup W, LargeEvenPComponent p (Subgroup.centralizer {x}) C →
    CFSG.Assembly.IsQuasisimple ↥C ∧ LargeEvenMarking ↥C (fun _ _ _ _ _ _ => True))


end HypParts

section Quotient

variable {G : Type} [Group G]

@[expose] noncomputable def ggAutKV (D K M : Subgroup G) (m : G) : Subgroup G :=
  ggAutKH D K M m ⊓ Subgroup.centralizer (K : Set G)

theorem ggAutKV_normal {D K M : Subgroup G} {m : G}
    (hEK : D.map (MulAut.conj m⁻¹).toMonoidHom ≤ Subgroup.normalizer (K : Set G)) :
    ((ggAutKV D K M m).subgroupOf (ggAutKW D K m)).Normal := by
  set E₀ := D.map (MulAut.conj m⁻¹).toMonoidHom with hE₀
  have hVW : ggAutKV D K M m ≤ ggAutKW D K m := fun v hv =>
    (sup_le_sup_left inf_le_left E₀ : E₀ ⊔ (K ⊓ M) ≤ E₀ ⊔ K) (Subgroup.mem_inf.mp hv).1
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hVW]
  have fwdE : ∀ e ∈ E₀, ∀ v ∈ ggAutKV D K M m, e * v * e⁻¹ ∈ ggAutKV D K M m := by
    intro e he v hv
    obtain ⟨hvH, hvC⟩ := Subgroup.mem_inf.mp hv
    have heH : e ∈ ggAutKH D K M m := (le_sup_left : E₀ ≤ E₀ ⊔ (K ⊓ M)) he
    refine Subgroup.mem_inf.mpr ⟨(ggAutKH D K M m).mul_mem
      ((ggAutKH D K M m).mul_mem heH hvH) ((ggAutKH D K M m).inv_mem heH), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hk' : e⁻¹ * k * e ∈ K := by
      have h0 := (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (K : Set G)).inv_mem (hEK he)) k).mp hk
      simpa using h0
    have h := Subgroup.mem_centralizer_iff.mp hvC (e⁻¹ * k * e) hk'
    calc k * (e * v * e⁻¹) = e * ((e⁻¹ * k * e) * v) * e⁻¹ := by group
      _ = e * (v * (e⁻¹ * k * e)) * e⁻¹ := by rw [h]
      _ = e * v * e⁻¹ * k := by group
  have fwdK : ∀ k ∈ K, ∀ v ∈ ggAutKV D K M m, k * v * k⁻¹ ∈ ggAutKV D K M m := by
    intro k hk v hv
    have h := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hv).2 k hk
    rw [h, mul_inv_cancel_right]
    exact hv
  have hnorm : ∀ X : Subgroup G,
      (∀ g ∈ X, ∀ v ∈ ggAutKV D K M m, g * v * g⁻¹ ∈ ggAutKV D K M m) →
      X ≤ Subgroup.normalizer (ggAutKV D K M m : Set G) := by
    intro X hX g hg
    rw [Subgroup.mem_normalizer_iff]
    intro v
    refine ⟨hX g hg v, fun hv => ?_⟩
    have h0 := hX g⁻¹ (X.inv_mem hg) _ hv
    simpa [mul_assoc] using h0
  exact sup_le (hnorm E₀ fwdE) (hnorm K fwdK)

@[expose] noncomputable def ggAutKPi (D K M : Subgroup G) (m : G)
    [((ggAutKV D K M m).subgroupOf (ggAutKW D K m)).Normal] :
    ↥(ggAutKW D K m) →* ↥(ggAutKW D K m) ⧸ (ggAutKV D K M m).subgroupOf (ggAutKW D K m) :=
  QuotientGroup.mk' _

@[expose] def GGAutKConjConfig [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (b : G) (L₁ K : Subgroup G) (m : G) : Prop :=
  b ∈ Bs ∧ b ≠ 1 ∧ IsComponentOf L₁ (ggG0 p B x L D J ⊓ Subgroup.centralizer {b}) ∧
    IsComponentOf K (Subgroup.centralizer {b}) ∧ L₁ ≤ K ∧ ¬ K ≤ ggM p B x L D J ∧
    m ∈ ggM p B x L D J ∧ D.map (MulAut.conj m⁻¹).toMonoidHom ≤ Subgroup.centralizer {b}

end Quotient

section Inputs

@[expose] def GGAutKCanonIIInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
      ∀ (b : G) (L₁ K : Subgroup G) (m : G), GGAutKConjConfig p B Bs x L D J b L₁ K m →
      ∀ [((ggAutKV D K (ggM p B x L D J) m).subgroupOf (ggAutKW D K m)).Normal],
        GGHypRestII
          (↥(ggAutKW D K m) ⧸ (ggAutKV D K (ggM p B x L D J) m).subgroupOf (ggAutKW D K m))


end Inputs

end CFSG.StandardType
