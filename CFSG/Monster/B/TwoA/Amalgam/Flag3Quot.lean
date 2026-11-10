module

public import CFSG.Monster.B.TwoA.Amalgam.Kernels
public import CFSG.Monster.B.TwoA.Sp8.SubgeomFive

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8 MulAction

open scoped IsMulCommutative

attribute [local instance] k3SetAction subspaceAction parAction

abbrev Five : Type := orbit K3 subgeom

@[expose] def fiveC :
    Five := ⟨subgeom, mem_orbit_self subgeom⟩

theorem fiveC_coe :
    (fiveC : Set ParGeom) = subgeom := rfl

@[expose] def rho5 :
    K3 →* Equiv.Perm Five := toPermHom K3 Five

theorem coe_rho5
    (k : K3) (C' : Five) :
    ((rho5 k C' : Five) : Set ParGeom) = k • (C' : Set ParGeom) := by
  rw [rho5, toPermHom_apply, toPerm_apply, orbit.coe_smul]

theorem rho5_surjective :
    Function.Surjective rho5 := surjective_toPermHom_fiveConj

theorem ker_sigma3_le_ker_rho5 :
    sigma3.ker ≤ rho5.ker := fun n hn => by
  rw [MonoidHom.mem_ker]
  refine Equiv.ext fun ω => ?_
  exact fixes_of_normal_of_coprime Nat.prime_five natCard_orbit_subgeom sigma3.ker
    (by rw [natCard_ker_sigma3]; norm_num) ⟨n, hn⟩ ω

theorem natCard_perm_Five :
    Nat.card (Equiv.Perm Five) = 120 := by
  rw [Nat.card_perm, natCard_orbit_subgeom]
  rfl

theorem natCard_perm_fin_five : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
  rw [Nat.card_perm, Nat.card_fin]
  rfl

theorem ker_rho5 :
    rho5.ker = sigma3.ker := by
  refine (Subgroup.eq_of_le_of_card_ge ker_sigma3_le_ker_rho5 ?_).symm
  have h1 := Subgroup.card_mul_index rho5.ker
  have h2 := Subgroup.card_mul_index sigma3.ker
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 rho5_surjective, Subgroup.card_top,
    natCard_perm_Five] at h1
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 sigma3_surjective, Subgroup.card_top,
    natCard_perm_fin_five] at h2
  omega

@[expose] def psiK3 :
    K3 →* (Additive E3 ≃ₗ[ZMod 2] Additive E3) × Equiv.Perm Five :=
  (linConj E3).prod rho5

theorem psiK3_apply
    (k : K3) : psiK3 k = (linConj E3 k, rho5 k) := by
  rw [psiK3, MonoidHom.prod_apply]

@[expose] def glE3Equiv :
    (Additive E3 ≃ₗ[ZMod 2] Additive E3) ≃* GL (Fin 3) (ZMod 2) :=
  (mulAutEquivLinear E3).symm.trans (mulAutEquivGL natCard_E3_pow)

theorem glE3Equiv_linConj
    (k : K3) : glE3Equiv (linConj E3 k) = actE3 k := by
  change mulAutEquivGL natCard_E3_pow ((mulAutEquivLinear E3).symm
    (mulAutEquivLinear E3 (conjE E3 k))) = mulAutEquivGL natCard_E3_pow (conjE E3 k)
  rw [MulEquiv.symm_apply_apply]

theorem linConj_eq_one_iff
    (k : K3) : linConj E3 k = 1 ↔ actE3 k = 1 := by
  rw [← glE3Equiv_linConj, MulEquiv.map_eq_one_iff]

theorem ker_psiK3 :
    psiK3.ker = R3.subgroupOf K3 := by
  obtain ⟨e, he⟩ := exists_k3QuotProd
  ext k
  rw [MonoidHom.mem_ker, psiK3_apply, Prod.mk_eq_one, linConj_eq_one_iff,
    ← MonoidHom.mem_ker (f := rho5), ker_rho5, MonoidHom.mem_ker,
    ← QuotientGroup.eq_one_iff (N := R3.subgroupOf K3), ← e.map_eq_one_iff, he, Prod.mk_eq_one]

theorem psiK3_surjective :
    Function.Surjective psiK3 := by
  obtain ⟨e, he⟩ := exists_k3QuotProd
  intro y
  obtain ⟨k₁, hk₁⟩ := rho5_surjective y.2
  obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective (e.symm (glE3Equiv y.1, sigma3 k₁))
  have h := he k
  rw [hk, MulEquiv.apply_symm_apply, Prod.mk.injEq] at h
  have hσ : k₁⁻¹ * k ∈ sigma3.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, ← h.2, inv_mul_cancel]
  rw [← ker_rho5, MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at hσ
  refine ⟨k, ?_⟩
  have e1 : linConj E3 k = y.1 := glE3Equiv.injective ((glE3Equiv_linConj k).trans h.1.symm)
  have e2 : rho5 k = y.2 := hσ.symm.trans hk₁
  exact (psiK3_apply k).trans (Prod.ext e1 e2)

theorem Pc2_le_K3 : Pc 2 ≤ K3 := by
  rw [Pc_two]
  exact inf_le_left

theorem mem_centralizer_of_Pc2
    (g : Pc 2) : (g : Dfull) ∈ Subgroup.centralizer {cQ} :=
  Pc_le_centralizer 2 g.2

@[expose] def phiP3 :
    Pc 2 →* (Additive E3 ≃ₗ[ZMod 2] Additive E3) × Equiv.Perm Five :=
  psiK3.comp (Subgroup.inclusion Pc2_le_K3)

theorem phiP3_apply
    (g : Pc 2) : phiP3 g = psiK3 (Subgroup.inclusion Pc2_le_K3 g) := by
  rw [phiP3, MonoidHom.comp_apply]

theorem phiP3_fst
    (g : Pc 2) : (phiP3 g).1 = linConj E3 (Subgroup.inclusion Pc2_le_K3 g) := by
  rw [phiP3_apply, psiK3_apply]

theorem phiP3_snd
    (g : Pc 2) : (phiP3 g).2 = rho5 (Subgroup.inclusion Pc2_le_K3 g) := by
  rw [phiP3_apply, psiK3_apply]


theorem exists_Pc2_of_K3
    (k : K3) :
    ∃ (p : Pc 2) (r : K3), (r : Dfull) ∈ R3 ∧ Subgroup.inclusion Pc2_le_K3 p = r * k := by
  obtain ⟨r, hr, hrc⟩ := Par3.cE3_R3_transitive (Par3.conj_cQ_mem_cE3 k.2) Par3.cQ_mem_cE3
  have hm : r * (k : Dfull) ∈ Pc 2 := by
    rw [Pc_two]
    refine ⟨K3.mul_mem (Par3.R3_le_K3 hr) k.2, (Par3.stabilizer_iff _).1 ?_⟩
    calc r * (k : Dfull) * cQ * (r * k)⁻¹ = r * ((k : Dfull) * cQ * (k : Dfull)⁻¹) * r⁻¹ := by
          group
      _ = cQ := hrc
  exact ⟨⟨_, hm⟩, ⟨r, Par3.R3_le_K3 hr⟩, hr, Subtype.ext rfl⟩

theorem phiP3_surjective :
    Function.Surjective phiP3 := by
  intro y
  obtain ⟨k, rfl⟩ := psiK3_surjective y
  obtain ⟨p, r, hr, hp⟩ := exists_Pc2_of_K3 k
  have hrK : r ∈ psiK3.ker := by
    rw [ker_psiK3]
    exact Subgroup.mem_subgroupOf.2 hr
  refine ⟨p, ?_⟩
  calc phiP3 p = psiK3 (Subgroup.inclusion Pc2_le_K3 p) := phiP3_apply p
    _ = psiK3 r * psiK3 k := (congrArg psiK3 hp).trans (map_mul psiK3 r k)
    _ = psiK3 k := (congrArg (· * psiK3 k) (MonoidHom.mem_ker.1 hrK)).trans (one_mul _)


theorem zpowers_xhat_le_E3 : Subgroup.zpowers xhat ≤ E3 := Subgroup.zpowers_le.2 xhat_mem_E3

@[expose] def ptE1 : SubspaceDim (ZMod 2) (Additive E3) 1 :=
  ⟨subOf E3 (Subgroup.zpowers xhat), finrank_subOf E3 zpowers_xhat_le_E3 natCard_zpowers_xhat⟩

@[expose] def lnE2 : SubspaceDim (ZMod 2) (Additive E3) 2 :=
  ⟨subOf E3 Vhat, finrank_subOf E3 Vhat_le_E3 natCard_Vhat_pow⟩

theorem ptE1_coe : ptE1.1 = subOf E3 (Subgroup.zpowers xhat) := rfl

theorem lnE2_coe : lnE2.1 = subOf E3 Vhat := rfl

theorem ptE1_le_lnE2 : ptE1.1 ≤ lnE2.1 := fun _ hx =>
  (mem_subOf E3).2 (Subgroup.zpowers_le.2 xhat_mem_Vhat ((mem_subOf E3).1 hx))

theorem subspace_smul_coe {j : ℕ} (A : Additive E3 ≃ₗ[ZMod 2] Additive E3)
    (S : SubspaceDim (ZMod 2) (Additive E3) j) :
    (A • S).1 = S.1.map (A : Additive E3 →ₗ[ZMod 2] Additive E3) := rfl

theorem mem_Pc0_iff
    (g : Pc 2) : (g : Dfull) ∈ Pc 0 ↔ (phiP3 g).1 • ptE1 = ptE1 := by
  rw [← Subtype.coe_inj, subspace_smul_coe, phiP3_fst, ptE1_coe,
    map_linConj_eq_iff E3 zpowers_xhat_le_E3, Subgroup.coe_inclusion, normalizer_zpowers_xhat,
    Pc_zero, Subgroup.mem_inf]
  exact ⟨fun h => h.1, fun h => ⟨h, mem_centralizer_of_Pc2 g⟩⟩

theorem mem_Pc1_iff
    (g : Pc 2) : (g : Dfull) ∈ Pc 1 ↔ (phiP3 g).1 • lnE2 = lnE2 := by
  rw [← Subtype.coe_inj, subspace_smul_coe, phiP3_fst, lnE2_coe,
    map_linConj_eq_iff E3 Vhat_le_E3, Subgroup.coe_inclusion, Pc_one, Subgroup.mem_inf]
  exact ⟨fun h => h.1, fun h => ⟨h, mem_centralizer_of_Pc2 g⟩⟩

theorem mem_Pc3_iff
    (g : Pc 2) : (g : Dfull) ∈ Pc 3 ↔ (phiP3 g).2 fiveC = fiveC := by
  rw [← Subtype.coe_inj, phiP3_snd, coe_rho5, fiveC_coe, k3_smul_subgeom_eq_iff,
    Subgroup.coe_inclusion, Pc_three, Subgroup.mem_inf]
  exact ⟨fun h => h.1, fun h => ⟨h, mem_centralizer_of_Pc2 g⟩⟩


end CFSG.Monster.B.TwoA.Amalgam
