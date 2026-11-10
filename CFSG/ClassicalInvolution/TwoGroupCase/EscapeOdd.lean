module

public import CFSG.ClassicalInvolution.TwoGroupCase.AmbientEscape
public import CFSG.ClassicalInvolution.QuaternionStructure.OddCoreSubgroup

public section

namespace CFSG.ClassicalInvolution

open CFSG CFSG.Open
open scoped Pointwise

universe u

variable {G : Type u} [Group G]


namespace OddByQuat

variable {R S : Subgroup G} {t : G}

theorem conj [Finite G] (d : OddByQuat R S t) (g : G) :
    OddByQuat (conjSubgroup g R) (conjSubgroup g S) (g * t * g⁻¹) where
  sylow := d.sylow.conj g
  t_mem := mem_conjSubgroup_of_mem d.t_mem
  t_ord := d.orderOf_t₁ g
  unique := d.unique_S₁ g
  le_C := by
    rw [← conjSubgroup_centralizer]
    exact conjSubgroup_mono d.le_C
  normal := by
    intro y hy
    rw [← conjSubgroup_centralizer] at hy
    have hy' : g⁻¹ * y * g ∈ Subgroup.centralizer ({t} : Set G) := mem_conjSubgroup_iff.mp hy
    have hN := d.normal hy'
    rw [← conjSubgroup_eq_self_iff] at hN ⊢
    have h1 : conjSubgroup y (conjSubgroup g R) =
        conjSubgroup g (conjSubgroup (g⁻¹ * y * g) R) := by
      rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup]
      congr 1
      group
    rw [h1, hN]
  two := by
    let φ : R ≃* conjSubgroup g R := (MulAut.conj g).subgroupMap R
    have hφ : (oddCore R).map φ.toMonoidHom = oddCore (conjSubgroup g R) :=
      QuaternionStructure.oddCore_map_mulEquiv φ
    exact d.two.of_equiv (QuotientGroup.congr _ _ φ hφ)

end OddByQuat


namespace OddByQuat

variable [Finite G] {R S : Subgroup G} {t : G}


end OddByQuat


namespace OddByQuat

variable [Finite G] {R S : Subgroup G} {t : G}


end OddByQuat

theorem mem_normalizer_inf_centralizer {X : Subgroup G} {y c : G}
    (hy : y ∈ Subgroup.normalizer (X : Set G)) (hyc : y * c = c * y) :
    y ∈ Subgroup.normalizer ((X ⊓ Subgroup.centralizer ({c} : Set G) : Subgroup G) : Set G) := by
  rw [← conjSubgroup_eq_self_iff, conjSubgroup_inf, conjSubgroup_eq_self_iff.mpr hy,
    conjSubgroup_centralizer]
  have : y * c * y⁻¹ = c := by rw [hyc]; group
  rw [this]


theorem exists_escape [Finite G] {T U : Subgroup G} (hnot : ¬ IsSylow2Of T ⊤)
    (hU : IsSylow2Of U ⊤) (hTU : T ≤ U) : ∃ x : G, Escape T U x := by
  have hne : T ≠ U := fun h => hnot (h ▸ hU)
  obtain ⟨x, hxU, hxN, hxT, hxx⟩ := exists_mem_normalizer_not_mem_sq_mem hU.2.1 hTU hne
  exact ⟨x, ⟨hU.2.1, hTU, hxU, hxN, hxT, hxx⟩⟩

namespace OddByQuat

section Escape

variable [Finite G] {R S T U : Subgroup G} {t x : G}


theorem two_mul_card_le (d : OddByQuat R S t) (hT : IsSylow2Of T (Subgroup.normalizer (S : Set G)))
    (e : Escape T U x) :
    2 * Nat.card T ≤
      2 ^ (Nat.card (Subgroup.centralizer ({t * (x * t * x⁻¹)} : Set G))).factorization 2 := by
  have h := card_le_of_isPGroup_le (W_two e) (d.c_central hT e)
  rwa [card_W e] at h


end Escape

end OddByQuat

end CFSG.ClassicalInvolution
