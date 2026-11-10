module

public import CFSG.LocalAnalysis.StandardType.GGD5LabelGlue
import CFSG.LocalAnalysis.StandardType.GGResF4ExactTwo

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module

theorem lup10e_not_symp
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J) (hxL : x ∉ L) {y : G}
    {H : Subgroup G} (M : GGQTwoAmbModel 3 Bs x y L H) (e : Fin 5 ≃ M.ι)
    (hecart : ∀ i j, M.cartan (e i) (e j) = CartanMatrix.D 5 i j) (he0 : M.a = e 0)
    (hbas : M.toLin.Basis) :
    ¬ GGInnerDiagOnLabel (fun _ lab =>
        (lab.tag = .B ∨ lab.tag = .C ∨ lab.tag = .F4) ∧ lab.n = 1) 3 Bs L := by
  intro h
  have hsplit : GGInnerDiagOnLabel
      (fun _ lab => (lab.tag = .B ∧ lab.n = 1) ∨ (lab.tag = .C ∧ lab.n = 1) ∨
        (lab.tag = .F4 ∧ lab.n = 1)) 3 Bs L := by
    refine GGInnerDiagOnLabel.mono_label ?_ h
    rintro lab ⟨hbc | hf4, hn⟩
    · exact Or.inl ⟨hbc, hn⟩
    · rcases hf4 with hc | hf4
      · exact Or.inr (Or.inl ⟨hc, hn⟩)
      · exact Or.inr (Or.inr ⟨hf4, hn⟩)
  rcases GGInnerDiagOnLabel.elim_or hsplit with hB | hCF4
  ·
    obtain ⟨_, lab, hlab, hraw⟩ := hB
    have hraw_copy := hraw
    obtain ⟨_, _, _, _, hQ0⟩ := largeEvenRawDatum_exists hraw_copy
    obtain ⟨-, -, _, hP0⟩ := hQ0
    obtain ⟨ht, hn⟩ := hP0.1
    rcases lab with ⟨t, rank, n⟩
    subst ht
    subst hn
    obtain ⟨K, hKfield, hKfin, hKcard, hQ⟩ := hraw
    let R := LargeEvenProj (LargeEvenSpGroup K rank)
    let I : Set (MulAut R) :=
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K rank)) (LargeEvenGSpSet K rank)
    let F : Set (MulAut R) :=
      LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSpGroup K rank))
    obtain ⟨-, -, θ, hP⟩ := hQ
    obtain ⟨-, hBsN, hBs3⟩ := hP
    have hr : 3 ≤ rank := by
      have h := hlab.2
      simp only at h
      omega
    have : CharP K 2 := charP_two_of_card hKcard
    have hSC : GGTorusAutCardSC 3 R I rank (2 ^ rank * rank.factorial) :=
      KGA.kga_sp (K := K) (p := 3) (N := rank) hr Nat.prime_three (by norm_num)
        (by rw [hKcard]; norm_num)
    have hI : I ⊆ LargeEvenInnSet R := TableBSymp.sp_I_subset_inn
    have hcard := lup10c_card_automizer M e hecart he0 hbas
    have hSC' := lup10c_torusAutCard hS hxL M e hbas θ hBsN hBs3 hSC
    rcases hSC' with ⟨_, hN⟩
    have hN' := hN hI
    have hN192 : 2 ^ rank * rank.factorial = 192 := by
      rw [← hcard, hN']
    rcases (show rank = 3 ∨ rank = 4 ∨ 5 ≤ rank by omega) with h3 | h4 | h5
    · subst h3; norm_num at hN192
    · subst h4; norm_num at hN192
    · omega
  rcases GGInnerDiagOnLabel.elim_or hCF4 with hC | hF4
  ·
    obtain ⟨_, lab, hlab, hraw⟩ := hC
    have hraw_copy := hraw
    obtain ⟨_, _, _, _, hQ0⟩ := largeEvenRawDatum_exists hraw_copy
    obtain ⟨-, -, _, hP0⟩ := hQ0
    obtain ⟨ht, hn⟩ := hP0.1
    rcases lab with ⟨t, rank, n⟩
    subst ht
    subst hn
    obtain ⟨K, hKfield, hKfin, hKcard, hQ⟩ := hraw
    let R := LargeEvenProj (LargeEvenSpGroup K rank)
    let I : Set (MulAut R) :=
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K rank)) (LargeEvenGSpSet K rank)
    let F : Set (MulAut R) :=
      LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSpGroup K rank))
    obtain ⟨-, -, θ, hP⟩ := hQ
    obtain ⟨-, hBsN, hBs3⟩ := hP
    have hr : 3 ≤ rank := by
      have h := hlab.2
      simp only at h
      omega
    have : CharP K 2 := charP_two_of_card hKcard
    have hSC : GGTorusAutCardSC 3 R I rank (2 ^ rank * rank.factorial) :=
      KGA.kga_sp (K := K) (p := 3) (N := rank) hr Nat.prime_three (by norm_num)
        (by rw [hKcard]; norm_num)
    have hI : I ⊆ LargeEvenInnSet R := TableBSymp.sp_I_subset_inn
    have hcard := lup10c_card_automizer M e hecart he0 hbas
    have hSC' := lup10c_torusAutCard hS hxL M e hbas θ hBsN hBs3 hSC
    rcases hSC' with ⟨_, hN⟩
    have hN' := hN hI
    have hN192 : 2 ^ rank * rank.factorial = 192 := by
      rw [← hcard, hN']
    rcases (show rank = 3 ∨ rank = 4 ∨ 5 ≤ rank by omega) with h3 | h4 | h5
    · subst h3; norm_num at hN192
    · subst h4; norm_num at hN192
    · omega
  ·
    have hF4' : GGInnerDiagOnLabel (fun p lab => p = 3 ∧ lab.tag = .F4 ∧ lab.n = 1) 3 Bs L := by
      refine GGInnerDiagOnLabel.mono_label
        (T := fun p lab => p = 3 ∧ lab.tag = .F4 ∧ lab.n = 1) ?_ hF4
      intro lab hs
      exact ⟨rfl, hs⟩
    have hCfg : GGConfig 3 B Bs x L D J := hS.1.1
    have hLperf : commutator ↥L = ⊤ := hF4'.1
    have hCard : Nat.card Bs = 3 ^ 5 := lup10c_card_Bs M e hbas
    have hZL : ∀ g ∈ Subgroup.center ↥L, Nat.Coprime 3 (orderOf g) :=
      lup10c_center_coprime hS hxL M
    have hInnL := ggResF4_innerOnL hF4' hLperf
    have h1152 := ggResF4_automizerL_card_eq_1152 hCfg hCard hF4' hLperf hZL hInnL
    have h192 := lup10c_card_automizer M e hecart he0 hbas
    rw [h1152] at h192
    norm_num at h192

end CFSG.StandardType

end
