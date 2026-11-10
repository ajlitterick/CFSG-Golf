module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermLinDefs
public import CFSG.LocalAnalysis.StandardType.GGSelectedPSUBlock
public import CFSG.ClassicalInvolution.WeakCT.UnitaryEightCharts
import CFSG.ClassicalInvolution.WeakCT.UnitaryEightWeakCT
import CFSG.LocalAnalysis.StandardType.GGSecFivePresTagUnitary
public import CFSG.RankThree.PartOne.CTP.SpNode
public import CFSG.RankThree.PartOne.CTP.SpPos

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType CFSG.LieType.Universal
  CFSG.LieType.BorelTits
open CFSG.ClassicalInvolution.WeakCT (blockSL blockSL2 weakCT_unitary_eight_of_charts
  weakCT_unitary_eight_even_of_charts)
open CFSG.Blueprint
open CFSG.LieType.Universal.Unitary (SU)
open CFSG.StandardType.SelectedRoot CFSG.StandardType.SelectedRoot.SelPSU
open CFSG.LieType.Steinberg (fixedSubfield mem_fixedSubfield)
open CFSG.ClassicalInvolution.WeakCT (hom_ext_sl2)
open CFSG.Timmesfeld (tv)
open CFSG.Timmesfeld.LevisExtras (tv01_eq_sl2Upper tv10_eq_sl2Lower)
open scoped MatrixGroups


theorem exists_selectedModel_PSU_rL
    {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) :
    ∃ model : SelectedSL2Model (Unitary.rootDatum hF 6) (fixedSubfield F 2 f)
        (InnerDiagSU.twoWtRoot 6 (2 : Fin 6)),
      model.phi = CFSG.RankThree.PartTwo.CTU6.rL F f := by
  classical
  have hi : (2 : Fin 6) ≠ Fin.rev 2 := by decide
  obtain ⟨model, -, hmat⟩ := exists_selectedModel_PSU_chart_rootPair_at hF (2 : Fin 6) hi
  let σ := unitaryInvolution F 2 f
  let k := fixedSubfield F 2 f
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hk : ∀ c ∈ k, σ c = c := fun c hc => mem_fixedSubfield.mp hc
  have hphi : ∀ A, model.phi A = chart σ k (pairCoord_injective hi) (pairCoord_rev 2) h2 hk A := by
    intro A
    apply Subtype.ext
    apply Units.ext
    exact hmat A
  refine ⟨model, ?_⟩
  apply hom_ext_sl2
  · intro c
    rw [CFSG.RankThree.PartTwo.CTU6.rL_tv01, hphi, tv01_eq_sl2Upper,
      chart_upper σ k hi h2 hk]
    rfl
  · intro c
    rw [CFSG.RankThree.PartTwo.CTU6.rL_tv10, hphi, tv10_eq_sl2Lower,
      chart_lower σ k hi h2 hk]
    rfl


theorem ggCompatPresented_of_unitary_long_node
    {f : ℕ} (hf : 1 ≤ f) {G : Type} [Group G]
    (Ψ : SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) 8 →* G)
    (hΨ : Ψ.ker ≤ Subgroup.center (SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) 8))
    (κ : SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) 6 →* G)
    (hκ : κ.ker ≤ Subgroup.center (SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) 6))
    (hnode : (CFSG.LieType.CurtisTits.rankOne
      (Unitary.rootDatum (card_galoisField_two_mul 2 f hf) 8).rootGroup
      (⟨3, by change 3 < 4; decide⟩ :
        Fin (Unitary.rootDatum (card_galoisField_two_mul 2 f hf) 8).rank)).map Ψ =
      (κ.comp (CFSG.RankThree.PartTwo.CTU6.rL (GaloisField 2 (2 * f)) f)).range) :
    GGCompatPresented (Unitary.rootDatum (card_galoisField_two_mul 2 f hf) 8) Ψ κ.range := by
  classical
  have hF := card_galoisField_two_mul 2 f hf
  obtain ⟨model, hm, -⟩ :=
    exists_selectedModel_PSU_chart_rootPair_at hF (3 : Fin 8) (by decide)
  obtain ⟨model', hm'⟩ := exists_selectedModel_PSU_rL hF
  have hγ : InnerDiagSU.twoWtRoot 8 (3 : Fin 8) =
      Pi.single (⟨3, by change 3 < 4; decide⟩ : Fin (Unitary.rootDatum hF 8).rank) 1 := by
    change (InnerDiagSU.twoWtRoot 8 (3 : Fin 8) : Fin 4 → ℤ) = Pi.single (3 : Fin 4) 1
    funext j
    fin_cases j <;> decide +kernel
  have hr : (Ψ.comp model.phi).range = (κ.comp model'.phi).range := by
    calc (Ψ.comp model.phi).range = model.phi.range.map Ψ := by rw [MonoidHom.range_comp]
      _ = (CFSG.LieType.CurtisTits.rankOne (Unitary.rootDatum hF 8).rootGroup
          (⟨3, by change 3 < 4; decide⟩ : Fin (Unitary.rootDatum hF 8).rank)).map Ψ := by
        rw [hm, hγ]
        rfl
      _ = (κ.comp (CFSG.RankThree.PartTwo.CTU6.rL (GaloisField 2 (2 * f)) f)).range := hnode
      _ = (κ.comp model'.phi).range := by rw [hm']
  have hconj : (MulAut.conj (1 : SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) 8)).toMonoidHom =
      MonoidHom.id _ := by
    ext x
    simp
  obtain ⟨u, hmatch⟩ := SelectedRoot.selectedRootMatch_of_map_eq model model' Ψ κ hΨ hκ 1
    (by simpa only [hconj, MonoidHom.comp_id] using hr)
  have hadm : StatedLieAdmissible .PSU 6 2 f :=
    ⟨Nat.prime_two, hf, by norm_num, by simp⟩
  have hM6 : ggU .PSU 6 f =
      (⟨SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) 6,
        Unitary.rootDatum hF 6⟩ : LieUniversal) := by
    simp only [ggU, lieUniversal, hf, ↓reduceDIte]
  unfold GGCompatPresented
  refine ⟨.PSU, 6, f, ?_⟩
  rw [hM6]
  refine ⟨κ, hadm, ?_, hκ, rfl, InnerDiagSU.twoWtRoot 6 (2 : Fin 6), model'.root_mem,
    InnerDiagSU.twoWtRoot 8 (3 : Fin 8), model.root_mem, u, hmatch⟩
  change 2 ≤ 6 / 2
  norm_num


theorem ggSU8_even_presents_compat_of_charts {a : ℕ} (ha : 2 ≤ a) {G : Type} [Group G]
    (φ : SL(4, GaloisField 2 (2 * a)) →* G)
    (hφ : φ.ker ≤ Subgroup.center SL(4, GaloisField 2 (2 * a)))
    (κ : Unitary.SU (unitaryInvolution (GaloisField 2 (2 * a)) 2 a) 6 →* G)
    (hκ : κ.ker ≤ Subgroup.center (Unitary.SU (unitaryInvolution (GaloisField 2 (2 * a)) 2 a) 6))
    (h1 : (φ.comp (blockSL2 (GaloisField 2 (2 * a)) 3 1)).range =
      (κ.comp (CFSG.RankThree.PartTwo.CTU6.rS0 _
        (unitaryInvolution_involutive (card_galoisField_two_mul 2 a (by omega))))).range)
    (h2 : (φ.comp (blockSL2 (GaloisField 2 (2 * a)) 3 2)).range =
      (κ.comp (CFSG.RankThree.PartTwo.CTU6.rS1 _
        (unitaryInvolution_involutive (card_galoisField_two_mul 2 a (by omega))))).range)
    (hcross : ∀ y ∈ (φ.comp (blockSL2 (GaloisField 2 (2 * a)) 3 0)).range,
      ∀ z ∈ (κ.comp (CFSG.RankThree.PartTwo.CTU6.rL (GaloisField 2 (2 * a)) a)).range,
        y * z = z * y) :
    ∃ Ψ : (ggU .PSU 8 a).K →* G,
      Ψ.ker ≤ Subgroup.center (ggU .PSU 8 a).K ∧ Ψ.range = φ.range ⊔ κ.range ∧
      GGPresentsG0 Ψ.range (ggU .PSU 8 a).D .PSU 8 a Ψ ∧
      GGCompatPresented (ggU .PSU 8 a).D Ψ κ.range := by
  have hF := card_galoisField_two_mul 2 a (by omega)
  obtain ⟨Ψ, hker, hrange, hnode⟩ :=
    CFSG.ClassicalInvolution.WeakCT.weakCT_unitary_eight_even_of_charts_with_long_root
      hF ha φ hφ κ hκ h1 h2 hcross
  have hcomp := ggCompatPresented_of_unitary_long_node (by omega : 1 ≤ a) Ψ hker κ hκ hnode
  have hpres := ggPresentsG0_of_unitary_hom hF (by omega : 1 ≤ a) (by norm_num : 4 ≤ 8) Ψ hker
  have ha1 : 1 ≤ a := by omega
  have e : ggU .PSU 8 a =
      (⟨SU (unitaryInvolution (GaloisField 2 (2 * a)) 2 a) 8,
        Unitary.rootDatum hF 8⟩ : LieUniversal) := by
    simp only [ggU, lieUniversal, ha1, ↓reduceDIte]
  rw [e]
  exact ⟨Ψ, hker, hrange, hpres, hcomp⟩

theorem ggSU8_even_of_charts {a : ℕ} (ha : 2 ≤ a) {G : Type} [Group G]
    (φ : SL(4, GaloisField 2 (2 * a)) →* G)
    (hφ : φ.ker ≤ Subgroup.center SL(4, GaloisField 2 (2 * a)))
    (κ : Unitary.SU (unitaryInvolution (GaloisField 2 (2 * a)) 2 a) 6 →* G)
    (hκ : κ.ker ≤ Subgroup.center (Unitary.SU (unitaryInvolution (GaloisField 2 (2 * a)) 2 a) 6))
    (h1 : (φ.comp (blockSL2 (GaloisField 2 (2 * a)) 3 1)).range =
      (κ.comp (CFSG.RankThree.PartTwo.CTU6.rS0 _
        (unitaryInvolution_involutive (card_galoisField_two_mul 2 a (by omega))))).range)
    (h2 : (φ.comp (blockSL2 (GaloisField 2 (2 * a)) 3 2)).range =
      (κ.comp (CFSG.RankThree.PartTwo.CTU6.rS1 _
        (unitaryInvolution_involutive (card_galoisField_two_mul 2 a (by omega))))).range)
    (hcross : ∀ y ∈ (φ.comp (blockSL2 (GaloisField 2 (2 * a)) 3 0)).range,
      ∀ z ∈ (κ.comp (CFSG.RankThree.PartTwo.CTU6.rL (GaloisField 2 (2 * a)) a)).range,
        y * z = z * y) :
    ∃ Ψ : (ggU .PSU 8 a).K →* G,
      Ψ.ker ≤ Subgroup.center (ggU .PSU 8 a).K ∧ Ψ.range = φ.range ⊔ κ.range := by
  obtain ⟨Ψ, hker, hrange, -, -⟩ :=
    ggSU8_even_presents_compat_of_charts ha φ hφ κ hκ h1 h2 hcross
  exact ⟨Ψ, hker, hrange⟩


theorem GGSecFiveRouteCfg.compat_of_suRanges
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J K : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hK : K ∈ 𝒦)
    {a : ℕ} (ha : 2 ≤ a) (φ : SL(4, GaloisField 2 (2 * a)) →* G)
    (hφ : φ.ker ≤ Subgroup.center SL(4, GaloisField 2 (2 * a)))
    (κ : SU (unitaryInvolution (GaloisField 2 (2 * a)) 2 a) 6 →* G)
    (hκ : κ.ker ≤ Subgroup.center (SU (unitaryInvolution (GaloisField 2 (2 * a)) 2 a) 6))
    (hκrange : κ.range = K)
    (h1 : (φ.comp (blockSL2 (GaloisField 2 (2 * a)) 3 1)).range =
      (κ.comp (CFSG.RankThree.PartTwo.CTU6.rS0 _
        (unitaryInvolution_involutive (card_galoisField_two_mul 2 a (by omega))))).range)
    (h2 : (φ.comp (blockSL2 (GaloisField 2 (2 * a)) 3 2)).range =
      (κ.comp (CFSG.RankThree.PartTwo.CTU6.rS1 _
        (unitaryInvolution_involutive (card_galoisField_two_mul 2 a (by omega))))).range)
    (hcross : ∀ y ∈ (φ.comp (blockSL2 (GaloisField 2 (2 * a)) 3 0)).range,
      ∀ z ∈ (κ.comp (CFSG.RankThree.PartTwo.CTU6.rL (GaloisField 2 (2 * a)) a)).range,
        y * z = z * y)
    (hG0 : ggG0 p B x L D J = φ.range ⊔ κ.range) :
    GGSecFiveCompat p B x L D J := by
  obtain ⟨Ψ, -, hrange, hpres, hcomp⟩ :=
    ggSU8_even_presents_compat_of_charts ha φ hφ κ hκ h1 h2 hcross
  have hpres0 : GGPresentsG0 (ggG0 p B x L D J) (ggU .PSU 8 a).D .PSU 8 a Ψ := by
    rw [← hrange.trans hG0.symm]
    exact hpres
  obtain ⟨y, hy⟩ := hcfg.2.2.2.1.2 K hK
  exact ⟨.PSU, 8, a, Ψ, hpres0, κ.range,
    Or.inr ⟨y, by simpa only [hκrange] using hy⟩, hcomp⟩

end CFSG.StandardType

end
