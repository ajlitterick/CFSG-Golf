module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveRest
public import CFSG.LocalAnalysis.StandardType.GGTypeAEndNodeLift

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.RankThree.PartTwo.Sec21 Matrix SpecialLinear

section Config

variable {G : Type} [Group G] [Finite G]

@[expose] def GGTypeANbrCfg (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) (n f : ℕ)
    (y : G) (K : Subgroup G) : Prop :=
  GGConfig p B Bs x L D J ∧ GGOpAutTrivial p Bs ∧ GGInnerDiagAll p B Bs x L D J ∧
    GGNoTransvection p Bs ∧ GGTypeANbr p B Bs x L D J n f y K

theorem GGTypeASplitNbr.toNbrCfg {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {n f : ℕ} {y : G} {K : Subgroup G} (h : GGTypeASplitNbr p B Bs x L D J n f y K) :
    GGTypeANbrCfg p B Bs x L D J n f y K := by
  obtain ⟨hcfg, hOp, hInn, hNoTr, hmod, hpq, hn, -, hsc, hnbr, hmodK, hW⟩ := h
  exact ⟨hcfg, hOp, hInn, hNoTr, hmod, hpq, hn, hsc, hnbr, hmodK, hW⟩

end Config

@[expose] def GGTypeAEndBlockLExGenInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (y : G) (K : Subgroup G), GGTypeANbrCfg p B Bs x L D J n f y K →
    ∃ φ : Matrix.SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f) →* G, φ.range = L ∧
      φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f)) ∧
      (φ.comp (slLowerBlockHom n (GaloisField 2 f))).range = J

@[expose] def GGTypeAEndBlockKGenInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (y : G) (K : Subgroup G), GGTypeANbrCfg p B Bs x L D J n f y K →
    ∃ φ₂ : SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f) →* G, φ₂.range = K ∧
      φ₂.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f)) ∧
      (φ₂.comp (slUpperBlockHom n (GaloisField 2 f))).range = J

@[expose] def GGTypeAFarCommuteGenInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (y : G) (K : Subgroup G), GGTypeANbrCfg p B Bs x L D J n f y K →
    ∀ φ₁ φ₂ : SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f) →* G, φ₁.range = L →
      φ₁.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f)) →
      φ₂.range = K →
      φ₂.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f)) →
      (φ₁.comp (slLowerBlockHom n (GaloisField 2 f))).range = J →
      φ₁.comp (slLowerBlockHom n (GaloisField 2 f)) =
        φ₂.comp (slUpperBlockHom n (GaloisField 2 f)) →
      ∀ i j : Fin n, i.val = 0 → j.val + 1 = n →
        Commute (φ₂ (weylRep n (GaloisField 2 f) j)) (φ₁ (weylRep n (GaloisField 2 f) i))


theorem exists_conj_lowerBlock_of_lift {G : Type} [Group G] {L J : Subgroup G} {n f : ℕ}
    (hn : 2 ≤ n) {φ φ₁ : Matrix.SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f) →* G}
    (hφL : φ.range = L)
    (hφker : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f)))
    (hJ : (φ.comp (slLowerBlockHom n (GaloisField 2 f))).range = J) (hφ₁L : φ₁.range = L)
    (hker : φ₁.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f))) :
    ∃ l ∈ L, (φ₁.comp (slLowerBlockHom n (GaloisField 2 f))).range.map
      (MulAut.conj l).toMonoidHom = J := by
  obtain ⟨α, hα⟩ := exists_mulAut_of_slLift (by omega : 3 ≤ n + 1) (hφL.trans hφ₁L.symm) hφker hker
  obtain ⟨s, hs⟩ := exists_conj_of_mulAut_slLowerBlockHom hn α⁻¹
  have hsL : φ₁ s ∈ L := by
    rw [← hφ₁L]
    exact ⟨s, rfl⟩
  refine ⟨φ₁ s, hsL, ?_⟩
  have e1 : (MulAut.conj (φ₁ s)).toMonoidHom.comp φ₁ = φ₁.comp (MulAut.conj s).toMonoidHom := by
    ext g
    simp [MulAut.conj_apply]
  have e2 : φ = φ₁.comp (α⁻¹).toMonoidHom := by
    rw [hα]
    ext g
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    exact congrArg φ (MulEquiv.apply_symm_apply α g).symm
  rw [← hJ, MonoidHom.range_comp, MonoidHom.range_comp, Subgroup.map_map, e1,
    ← Subgroup.map_map, ← hs, Subgroup.map_map, ← e2]

theorem ggTypeAJoinEndNodeInput_of_blocks (hA : GGTypeAEndBlockLExGenInput)
    (hB : GGTypeAEndBlockKGenInput) (hC : GGTypeAFarCommuteGenInput) :
    GGTypeAJoinEndNodeInput := by
  intro G _ _ p B Bs x L D J n f y K hcfg hOp hInn hNoTr hN φ₁ hφL hker
  have hNC : GGTypeANbrCfg p B Bs x L D J n f y K := ⟨hcfg, hOp, hInn, hNoTr, hN⟩
  obtain ⟨hmod, -, hn, -, -, -⟩ := hN
  have hf : 1 ≤ f := hmod.1.2.1
  have h2 : (2 : GaloisField 2 f) = 0 :=
    two_eq_zero_of_card (GaloisField.card 2 f (by omega)) hf
  obtain ⟨φ, hφL', hφker, hJ⟩ := hA G p B Bs x L D J n f y K hNC
  obtain ⟨l, hlL, hJl⟩ := exists_conj_lowerBlock_of_lift (by omega) hφL' hφker hJ hφL hker
  set ψ₁ := (MulAut.conj l).toMonoidHom.comp φ₁ with hψ₁
  have hψL : ψ₁.range = L := range_mulAutConj_comp hlL hφL
  have hψker : ψ₁.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f)) := by
    rw [hψ₁, ker_mulAutConj_comp]
    exact hker
  have hψJ : (ψ₁.comp (slLowerBlockHom n (GaloisField 2 f))).range = J := by
    rw [hψ₁, MonoidHom.comp_assoc, MonoidHom.range_comp, hJl]
  obtain ⟨φ₂₀, hφ₂K, hker₂, hJ₂⟩ := hB G p B Bs x L D J n f y K hNC
  obtain ⟨φ₂, hφ₂K', hker₂', hcomp⟩ := exists_slCompat_lift hn hψker hker₂ (hψJ.trans hJ₂.symm)
  rw [hφ₂K] at hφ₂K'
  have hfar := hC G p B Bs x L D J n f y K hNC ψ₁ φ₂ hψL hψker hφ₂K' hker₂' hψJ hcomp
    ⟨0, by omega⟩ ⟨n - 1, by omega⟩ rfl (by simp only; omega)
  have hT := ggTypeAEndNode_of_compat h2 hn hcomp hfar
  have hKle := slCompat_range_le h2 (by omega) hcomp
  rw [hψL, hφ₂K'] at hKle
  set T' := φ₂ (weylRep n (GaloisField 2 f) ⟨n - 1, by omega⟩) with hT'
  have hT'K : T' ∈ K := by
    rw [← hφ₂K']
    exact ⟨_, rfl⟩
  refine ⟨l⁻¹ * T' * l, ?_, GGTypeAEndNode.of_conj hT, ?_⟩
  · exact mul_mem (mul_mem (Subgroup.mem_sup_left (inv_mem hlL)) (Subgroup.mem_sup_right hT'K))
      (Subgroup.mem_sup_left hlL)
  · refine hKle.trans (sup_le le_sup_left ?_)
    intro z hz
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hz
    have e : (MulAut.conj T').toMonoidHom g =
        l * ((l⁻¹ * T' * l) * (l⁻¹ * g * l) * (l⁻¹ * T' * l)⁻¹) * l⁻¹ := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [e]
    have hm : (l⁻¹ * T' * l) * (l⁻¹ * g * l) * (l⁻¹ * T' * l)⁻¹ ∈
        L.map (MulAut.conj (l⁻¹ * T' * l)).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨l⁻¹ * g * l, L.mul_mem (L.mul_mem (L.inv_mem hlL) hg) hlL,
        by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hlL)
      (Subgroup.mem_sup_right hm)) (Subgroup.mem_sup_left (L.inv_mem hlL))

@[expose] def GGTypeAThirdNbrInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (y : G) (K : Subgroup G), GGTypeANbrCfg p B Bs x L D J n f y K → p ∣ n + 3 →
    (∃ (y' : G) (K' : Subgroup G), GGNbr p B x D J y' K' ∧ ¬ K' ≤ L ⊔ K) →
    ∃ (y₃ : G) (K₃ : Subgroup G), GGTypeANbr p B Bs x L D J n f y₃ K₃ ∧ ¬ K₃ ≤ L ⊔ K

@[expose] def GGTypeACrossInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (y : G) (K : Subgroup G) (y₃ : G) (K₃ : Subgroup G),
    GGTypeANbrCfg p B Bs x L D J n f y K → GGTypeANbr p B Bs x L D J n f y₃ K₃ → p ∣ n + 3 →
    ¬ K₃ ≤ L ⊔ K →
    ∀ φ₁ : SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f) →* G, φ₁.range = L →
      φ₁.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f)) →
      ∀ T₁ : G, T₁ ∈ L ⊔ K → GGTypeAEndNode φ₁ T₁ →
        K ≤ L ⊔ L.map (MulAut.conj T₁).toMonoidHom →
      ∀ T₃ : G, T₃ ∈ L ⊔ K₃ → GGTypeAEndNode φ₁ T₃ →
        K₃ ≤ L ⊔ L.map (MulAut.conj T₃).toMonoidHom →
        (T₃ * T₁) ^ 3 = 1 ∧ ∀ g, T₁ * T₃ * T₁ * φ₁ g = φ₁ g * (T₁ * T₃ * T₁)

@[expose] def GGTypeAJoinThreeInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (y : G) (K : Subgroup G) (y₃ : G) (K₃ : Subgroup G),
    GGTypeANbrCfg p B Bs x L D J n f y K → GGTypeANbr p B Bs x L D J n f y₃ K₃ → p ∣ n + 3 →
    ¬ K₃ ≤ L ⊔ K → ∀ (y' : G) (K' : Subgroup G), GGNbr p B x D J y' K' → K' ≤ L ⊔ K ⊔ K₃


section Assembly


end Assembly

end CFSG.StandardType
