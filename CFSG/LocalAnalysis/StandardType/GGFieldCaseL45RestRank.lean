module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45RestOmega
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45RestCore
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldCyclic

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section General

variable {G : Type} [Group G]

theorem exists_pow_prime_pow_not_mem {p : ℕ} {U₁ : Subgroup G} {w : G}
    (hw : ∃ n : ℕ, w ^ p ^ n = 1) (hwU₁ : w ∉ U₁) :
    ∃ k : ℕ, w ^ p ^ k ∉ U₁ ∧ (w ^ p ^ k) ^ p ∈ U₁ := by
  classical
  have hex : ∃ n : ℕ, w ^ p ^ n ∈ U₁ := by
    obtain ⟨n, hn⟩ := hw
    exact ⟨n, hn ▸ one_mem _⟩
  have hn0 : Nat.find hex ≠ 0 := by
    intro h0
    have := Nat.find_spec hex
    rw [h0, pow_zero, pow_one] at this
    exact hwU₁ this
  refine ⟨Nat.find hex - 1, Nat.find_min hex (by omega), ?_⟩
  rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn0)]
  exact Nat.find_spec hex


end General


section Rank

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J X B₂ : Subgroup G} {d y : G} {K U U₁ : Subgroup G}

theorem GGL45Config.exists_conj_eq_mul (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁) {g₀ : G} (hg₀ : g₀ ∈ U)
    (hcyc : U ≤ Subgroup.zpowers g₀ ⊔ U₁) {n : G} (hn : n ∈ Subgroup.normalizer (U : Set G))
    {v : G} (hv : v ∈ U ⊓ Subgroup.centralizer (K : Set G)) (hw : n * v * n⁻¹ ∉ U₁) :
    ∃ v'' ∈ U ⊓ Subgroup.centralizer (K : Set G), ∃ b ∈ U₁, n * v'' * n⁻¹ = x * b := by
  have : Fact p.Prime := ⟨hcfg.prime⟩
  obtain ⟨-, hxU₁, -⟩ := ggL4546_basic hraw hiso hcfg
  have hxU : x ∈ U := hcfg.bs_le hcfg.x_mem
  have hwU : n * v * n⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hn v).mp hv.1
  obtain ⟨m, hm⟩ := hcfg.isPGroup ⟨_, hwU⟩
  have hwm : (n * v * n⁻¹) ^ p ^ m = 1 := by simpa using congrArg Subtype.val hm
  obtain ⟨k, hk1, hk2⟩ := exists_pow_prime_pow_not_mem ⟨m, hwm⟩ hw
  rw [conj_pow] at hk1 hk2
  have hw'U : n * v ^ p ^ k * n⁻¹ ∈ U :=
    (Subgroup.mem_normalizer_iff.mp hn _).mp (U.pow_mem hv.1 _)
  obtain ⟨t, b, hb, hxe⟩ := exists_pow_mul_of_cyclic hcfg.le_normalizer_part hg₀ hcyc hw'U hk1
    hk2 hxU (by rw [hcfg.x_pow]; exact one_mem _)
  refine ⟨(v ^ p ^ k) ^ t, Subgroup.pow_mem _ (Subgroup.pow_mem _ hv _) _, b⁻¹, U₁.inv_mem hb, ?_⟩
  rw [← conj_pow, hxe]
  group


end Rank


end CFSG.StandardType

end
