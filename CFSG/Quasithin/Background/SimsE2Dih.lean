module

public import CFSG.Quasithin.Background.SimsE2DihMod
public import CFSG.Quasithin.Background.SimsE213Four

public section

namespace CFSG.Quasithin.SimsE2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

namespace Dih

variable {Γ : Type*} [Group Γ]

theorem map_normalizerMonoidHom_subgroupOf {P Z : Subgroup Γ}
    (x : Subgroup.normalizer (P : Set Γ)) (hx : (x : Γ) ∈ Subgroup.normalizer (Z : Set Γ)) :
    (Z.subgroupOf P).map (P.normalizerMonoidHom x : ↥P →* ↥P) = Z.subgroupOf P := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    replace hz : (z : Γ) ∈ Z := hz
    change ((P.normalizerMonoidHom x z : P) : Γ) ∈ Z
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    exact (Subgroup.mem_normalizer_iff.mp hx z).mp hz
  · intro hy
    rw [Subgroup.mem_subgroupOf] at hy
    refine ⟨(P.normalizerMonoidHom x)⁻¹ y, ?_, ?_⟩
    · change (((P.normalizerMonoidHom x)⁻¹ y : P) : Γ) ∈ Z
      rw [← map_inv, Subgroup.normalizerMonoidHom_apply_apply_coe]
      exact (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (Z : Set Γ)).inv_mem hx) y).mp hy
    · change P.normalizerMonoidHom x ((P.normalizerMonoidHom x)⁻¹ y) = y
      rw [MulAut.apply_inv_self]

@[expose] noncomputable def conjSecAut (P Z K : Subgroup Γ) [(Z.subgroupOf P).Normal]
    (hKP : K ≤ Subgroup.normalizer (P : Set Γ)) (hKZ : K ≤ Subgroup.normalizer (Z : Set Γ)) :
    ↥K →* MulAut (↥P ⧸ Z.subgroupOf P) where
  toFun k := QuotientGroup.congr (Z.subgroupOf P) (Z.subgroupOf P)
    (P.normalizerMonoidHom ⟨k, hKP k.2⟩) (map_normalizerMonoidHom_subgroupOf _ (hKZ k.2))
  map_one' := by
    ext q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    rw [QuotientGroup.congr_mk, MulAut.one_apply]
    congr 1
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    simp
  map_mul' k k' := by
    ext q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    rw [MulAut.mul_apply, QuotientGroup.congr_mk, QuotientGroup.congr_mk, QuotientGroup.congr_mk]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_mul, mul_inv_rev]
    group


end Dih

open Dih


end CFSG.Quasithin.SimsE2
