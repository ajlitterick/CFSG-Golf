module

public import CFSG.LocalAnalysis.StandardType.GGNbrTransvectionDichotomy
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenOver

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

variable {G : Type} [Group G] [Finite G]

theorem eq_one_of_ggOverGamma_one {p : ℕ} (hp : p.Prime) {Bs K : Subgroup G}
    (hBs : IsElemAbelian p Bs) (hNoTr : GGNoTransvection p Bs)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hZ : Nat.card ↥(Bs ⊓ K ⊓ Subgroup.centralizer (K : Set G)) ≤ p)
    {κ : MulAut ↥Bs} (hκ : κ ∈ ggAutomizer K Bs) (hover : GGOverGamma hN κ 1) : κ = 1 := by
  classical
  obtain ⟨g, hgK, hg, hκg⟩ := mem_ggAutomizer_iff.mp hκ
  let N : Subgroup ↥Bs := (Bs ⊓ K ⊓ Subgroup.centralizer (K : Set G)).subgroupOf Bs
  have hVc : ∀ a b : ↥Bs, a * b = b * a := fun a b => hBs.1.is_comm.comm a b
  have hVp : ∀ v : ↥Bs, v ^ p = 1 := fun v => Subtype.ext (by simpa using hBs.2 v v.2)
  have hleBs : Bs ⊓ K ⊓ Subgroup.centralizer (K : Set G) ≤ Bs := by
    intro x hx
    exact (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hx).1).1
  have hNcard : Nat.card N ≤ p := by
    change Nat.card ↥((Bs ⊓ K ⊓ Subgroup.centralizer (K : Set G)).subgroupOf Bs) ≤ p
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hleBs).toEquiv]
    exact hZ
  have hκN : ∀ v : ↥Bs, v⁻¹ * κ v ∈ N := by
    intro v
    have hw : ((v⁻¹ * κ v : ↥Bs) : G) = (v : G)⁻¹ * g * (v : G) * g⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hκg v]
      group
    have hwK : ((v⁻¹ * κ v : ↥Bs) : G) ∈ K := by
      rw [hw]
      exact K.mul_mem ((Subgroup.mem_normalizer_iff''.mp (hN v.2) g).mp hgK)
        (K.inv_mem hgK)
    have hwC : ((v⁻¹ * κ v : ↥Bs) : G) ∈ Subgroup.centralizer (K : Set G) := by
      rw [← ggGamma_eq_one_iff K hN (v⁻¹ * κ v)]
      have hgamma : ggGamma K hN (κ v) = ggGamma K hN v := by
        have hv := hover v
        simp only [MulAut.one_apply] at hv
        simpa only [MonoidHom.coe_rangeRestrict] using Subtype.ext_iff.mp hv
      rw [map_mul, map_inv, hgamma, inv_mul_cancel]
    change ((v⁻¹ * κ v : ↥Bs) : G) ∈ Bs ⊓ K ⊓ Subgroup.centralizer (K : Set G)
    exact ⟨⟨(v⁻¹ * κ v).2, hwK⟩, hwC⟩
  have hfix : ∀ n ∈ N, κ n = n := by
    intro n hn
    have hn' : (n : G) ∈ Bs ⊓ K ⊓ Subgroup.centralizer (K : Set G) := hn
    have hnK : (n : G) ∈ K := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hn').1).2
    have hnC : (n : G) ∈ Subgroup.centralizer (K : Set G) := (Subgroup.mem_inf.mp hn').2
    have hgn : g * (n : G) = (n : G) * g := (Subgroup.mem_centralizer_iff.mp hnC) g hgK
    apply Subtype.ext
    rw [hκg n, hgn]
    group
  have hmem : κ ∈ ggInduced ⊤ Bs := ⟨g, Subgroup.mem_top g, hg, hκg⟩
  rcases mulAut_eq_one_or_transvection hp hVc hVp N hNcard κ hκN hfix with h1 | h2
  · exact h1
  · exact absurd h2 (hNoTr κ hmem)


end CFSG.StandardType

end
