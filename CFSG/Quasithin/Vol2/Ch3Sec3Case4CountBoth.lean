module

public import CFSG.Quasithin.Vol2.Ch3Sec3Case4CountGen
public import CFSG.Quasithin.Background.C134Case4Kappa

public section

namespace CFSG.Quasithin.H13.Case4Count

open CFSG.Open (pCoreOf quasithinOmegaOneCenter)
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.Quasithin.H13.L3316 (liftPre liftCore liftCore_le liftCore_eq)
open CFSG.Quasithin.H13.L3321 (RData SL4)
open CFSG.Quasithin.CubicCount CFSG.Quasithin.SevenL4Model
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Data

variable {T L R : Subgroup G} {α : ↥L →* SL4}


theorem exists_modO2_one (hR : Data G T L R α) :
    ∃ α₂ : ↥(liftCore α (FLc.QI 4 {1})) →* ↥(StatedSL 3 (ZMod 2)),
      IsModO2Surj (liftCore α (FLc.QI 4 {1})) α₂ := by
  obtain ⟨ψ, hψs, hψk, -⟩ := hR.exists_levi_one
  exact ⟨_, L3321.isModO2Surj_comp hψs hψk⟩

theorem exists_modO2_three (hR : Data G T L R α) :
    ∃ α₂ : ↥(liftCore α (FLc.QI 4 {3})) →* ↥(StatedSL 3 (ZMod 2)),
      IsModO2Surj (liftCore α (FLc.QI 4 {3})) α₂ := by
  have hno : ∀ c ∈ ({3} : Set ℕ), ¬ (0 < c ∧ c < 0 + 3) := by
    intro c hc
    rw [Set.mem_singleton_iff] at hc
    omega
  have hk2 : IsPGroup 2 ↥α.ker := by
    rw [hR.ker]
    exact CFSG.pCore_isPGroup
  obtain ⟨ψ, hψs, hψk, -⟩ := L3318.exists_levi (Nat.card_zmod 2) (by norm_num) hR.surj hk2
    (I := {3}) (a := 0) (m := 3) (by norm_num) le_rfl (Or.inl rfl) (Or.inr rfl) hno
  exact ⟨_, L3321.isModO2Surj_comp hψs
    (Ln2.ker_eq_pCore_of_hom (Nat.card_zmod 2) le_rfl hψs hψk)⟩


end Data

end CFSG.Quasithin.H13.Case4Count

namespace CFSG.Quasithin.H13.L3321

open CFSG.Open (pCoreOf quasithinOmegaOneCenter)
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Quasithin.H13.L3316 (liftPre liftCore liftCore_le)
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T M L D : Subgroup G} {α : ↥L →* SL4}

theorem FData.exists_mul (hD : FData G T M L D α) {t : G} (ht : t ∈ T) :
    ∃ l ∈ L, ∃ c ∈ qL L T, t = l * c := by
  obtain ⟨y, -, hy⟩ := hD.exists_conj ht
  refine ⟨y, y.2, (y : G)⁻¹ * t, ?_, by group⟩
  refine Case4Count.mem_qL_of_central hD.TL hD.hyp.sylow.1 hD.surj hD.ker
    ((L ⊔ T).mul_mem (Subgroup.mem_sup_left (L.inv_mem y.2)) (Subgroup.mem_sup_right ht))
    fun x hx => ?_
  have htx : t * x * t⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hD.TL ht) x).mp hx
  have hmem : (y : G)⁻¹ * t * x * ((y : G)⁻¹ * t)⁻¹ * x⁻¹ ∈ L := by
    have e : (y : G)⁻¹ * t * x * ((y : G)⁻¹ * t)⁻¹ * x⁻¹ =
        (y : G)⁻¹ * (t * x * t⁻¹) * y * x⁻¹ := by
      group
    rw [e]
    exact L.mul_mem (L.mul_mem (L.mul_mem (L.inv_mem y.2) htx) y.2) (L.inv_mem hx)
  have h1 : α ⟨_, hmem⟩ = 1 := by
    have e : (⟨_, hmem⟩ : ↥L) = y⁻¹ * ⟨t * x * t⁻¹, htx⟩ * y * (⟨x, hx⟩ : ↥L)⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hy ⟨x, hx⟩ htx]
    group
  have h2 : (⟨_, hmem⟩ : ↥L) ∈ α.ker := h1
  rw [hD.ker, Lem3328.mem_pCore_iff] at h2
  exact h2

theorem FData.toCountData (hD : FData G T M L D α) : Case4Count.Data G T L T α where
  TL := hD.TL
  T2 := hD.hyp.sylow.1
  surj := hD.surj
  ker := hD.ker
  RT := le_rfl
  QR := EscapingLocal.pCoreOf_le_of_isSylowTwoOf hD.hyp.toSetup331.isSylowTwoOf
  mul := fun _ ht => hD.exists_mul ht
  RQ1 := fun l hl => FLc.Ut_le_QI 4 {1} (hD.mem_Ut l hl)
  RQ3 := fun l hl => FLc.Ut_le_QI 4 {3} (hD.mem_Ut l hl)
  RY1 := hD.le_normalizer_Y {1}
  RY3 := hD.le_normalizer_Y {3}

end CFSG.Quasithin.H13.L3321
