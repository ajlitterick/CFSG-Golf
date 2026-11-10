module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBLabelDefs
public import CFSG.LocalAnalysis.StandardType.GGF4ThreeNbrRankDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBLabelCore
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpKCent
import CFSG.LocalAnalysis.StandardType.GGResNonsingF4Three
import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitE6Two
import CFSG.LocalAnalysis.StandardType.GGAutomizerGammaCard
import CFSG.LocalAnalysis.StandardType.GGResCentBoundNbrHolds

public import CFSG.LocalAnalysis.StandardType.GGTBXPlumb
import CFSG.LocalAnalysis.StandardType.GGTBJLabelJ
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordDExclReal
import CFSG.LocalAnalysis.StandardType.GGF4QGeFourEnds
public import CFSG.Certificates.CentralKernel
public import CFSG.Certificates.CosetTableCompactPresented
public import CFSG.Certificates.CosetTableWalkC
public import CFSG.Certificates.LiftedSchreierData
public import CFSG.Monster.AxisCount.HSIdentBaby
public import CFSG.Monster.AxisCount.HSIdentRec0
public import CFSG.Monster.AxisCount.HSIdentRec1
public import CFSG.Monster.AxisCount.HSIdentRec2
public import CFSG.Monster.AxisCount.HSIdentRec3
public import CFSG.Monster.AxisCount.HSIdentRec4
public import CFSG.Monster.AxisCount.HSIdentRec5
public import CFSG.Monster.AxisCount.HSIdentRec6
public import CFSG.Monster.AxisCount.HSIdentRec7
public import CFSG.Monster.AxisCount.HSIdentSmall
public import CFSG.Sporadic.Bridge.BOrder
public import CFSG.Sporadic.Bridge.BSurjInputs
public import CFSG.Sporadic.Bridge.Fi24Data
public import CFSG.Sporadic.Bridge.J4SurjInputs
public import CFSG.Sporadic.Bridge.McLSurj
public import CFSG.Sporadic.Presentation.Co1
public import CFSG.Sporadic.Presentation.Co2FusionInputs
public import CFSG.Sporadic.Presentation.Co3
public import CFSG.Sporadic.Presentation.Fi22Exact
public import CFSG.Sporadic.Presentation.Fi22ExactCover
public import CFSG.Sporadic.Presentation.Fi22ExactTop
public import CFSG.Sporadic.Presentation.Fi24PrimeExact
public import CFSG.Sporadic.Presentation.HeExact
public import CFSG.Sporadic.Presentation.J4
public import CFSG.Sporadic.Presentation.M23
public import CFSG.Sporadic.Presentation.M24Exact
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs
public import CFSG.Sporadic.Presentation.ONan
public import CFSG.Sporadic.Presentation.ThBase
public import CFSG.Sporadic.Schreier.M23
public import CFSG.Sporadic.Th
public import CFSG.Sporadic.Th.CertificateBase

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem two_pow_mul_factorial_ne_1152 (k : ℕ) : 2 ^ k * k.factorial ≠ 1152 :=
  two_pow_mul_factorial_ne_of_between (a := 4) (by norm_num [Nat.factorial])
    (by norm_num [Nat.factorial])

theorem two_pow_mul_factorial_ne_51840 (k : ℕ) : 2 ^ k * k.factorial ≠ 51840 :=
  two_pow_mul_factorial_ne_of_between (a := 6) (by norm_num [Nat.factorial])
    (by norm_num [Nat.factorial])

theorem two_pow_mul_factorial_ne_720 (k : ℕ) : 2 ^ k * k.factorial ≠ 720 :=
  two_pow_mul_factorial_ne_of_between (a := 4) (by norm_num [Nat.factorial])
    (by norm_num [Nat.factorial])

theorem ggSecFiveBCoordBRes_typeA {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig 3 B Bs x L D J) {n : ℕ} (hBs : Nat.card Bs = 3 ^ n)
    (hL : GGInnerDiagOnLabel (fun _ lab => lab.tag = .A ∧ 6 ≤ lab.rank ∧ lab.n = 1) 3 Bs L) :
    GGInnerDiagOnLabel (fun p lab => GGSecFiveBCoordBLabel n p lab) 3 Bs L := by
  obtain ⟨hperf, lab, hlab, hraw⟩ := hL
  obtain ⟨R, _, I, F, hQraw⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨hsimple, hnonab, θ, hS, hBN, hact⟩ := hQraw
  obtain ⟨htag, hrank6, hn1⟩ := hS
  obtain ⟨tag, rank, n_lab⟩ := lab
  have htag' : tag = .A := htag
  have hn' : n_lab = 1 := hn1
  subst htag'
  subst hn'
  have hHas : GGHasLabel ⟨.A, rank, 1⟩ (↥L ⧸ Subgroup.center ↥L) := by
    unfold GGHasLabel
    refine largeEvenRawDatum_mono ?_ hraw
    rintro R _ I F ⟨-, -, θ, -⟩
    exact ⟨θ⟩
  have hmodelLZ : CFSG.Open.StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL (rank + 1) 2 1 :=
    statedClassicalModel_of_hasLabel_typeA hlab hHas
  have hrank6' : 6 ≤ rank := hrank6
  have hm : (rank - 2) + 1 + 1 + 1 = rank + 1 := by omega
  obtain ⟨φ, hφr, hφi⟩ := GGHalf.exists_slLift_two (m := rank - 2) (by omega) hperf
    (by simpa [hm] using hmodelLZ)
  obtain ⟨A, hframe⟩ := ggHalf_torusFrame (X := L) (p := 3) rfl hcfg.2.1
    (N := rank - 2 + 1 + 1) (by omega) hBN φ hφr hφi
  have hBs' : Bs = Subgroup.zpowers x ⊔
      (GGHalf.halfTorus (rank - 2 + 1 + 1)).map
        (φ.comp (MulAut.conj A).toMonoidHom) :=
    ggQ2Lin_bstar_eq_sup hcfg hframe
  have hcard : Nat.card Bs = 3 * 3 ^ ((rank - 2 + 1 + 1 + 1) / 2) :=
    ggQ2Lin_card_bstar hcfg hframe hBs'
  have hcard' : Nat.card Bs = 3 * 3 ^ ((rank + 1) / 2) := by
    simpa [hm] using hcard
  have hpow : 3 ^ n = 3 ^ (1 + (rank + 1) / 2) := by
    rw [← hBs, hcard', Nat.pow_add, Nat.pow_one]
  have hn_eq : n = 1 + (rank + 1) / 2 :=
    Nat.pow_right_injective (by norm_num : 2 ≤ 3) hpow
  have hrank_rel : rank = 2 * n - 3 ∨ rank = 2 * n - 2 := by
    omega
  have hQ : GGSecFiveBCoordBLabel n 3 ⟨.A, rank, 1⟩ := by
    right; right; right
    exact ⟨rfl, hrank_rel, rfl, rfl⟩
  exact ⟨hperf, ⟨.A, rank, 1⟩, hlab, largeEvenRawDatum_mono (fun R _ I F hP => by
    obtain ⟨hs, hna, θ, hcont⟩ := hP
    exact ⟨hs, hna, θ, ⟨hQ, hcont.2⟩⟩) ((largeEvenRawDatum_legacy _ _).mpr hraw)⟩

section E6Two

private theorem largeEvenLabelAll_e6Two_facts :
    LargeEvenLabelAll ⟨.E6, 0, 1⟩ (fun R _ I _ =>
      (GGCenterPrime 3 R ∧ GGOutdiagPrime 3 R I ∧
        ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
          ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
          ∀ A : Subgroup (MulAut L'), IsElemAbelian 3 A →
            (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
            3 ^ 4 ≤ Nat.card A → GGTorusSelfCent 3 A →
            Nat.card (ggAutomizer (MulAut.conj : L' →* MulAut L').range A) = 1152) ∧
      (GGTorusReflGenW 3 4 R I ∧ GGTorusLift 3 4 R)) :=
  largeEvenLabelAll_and
    (ggPumpTwExcKnown_holds 1 (by norm_num) ⟨.E6, 0, 1⟩ (Or.inl ⟨rfl, by norm_num⟩))
    (largeEvenLabelAll_and
      (by
        intro Q hQ
        dsimp only [LargeEvenRawDatum, LargeEvenRecipeChevalley] at hQ
        obtain ⟨K, hField, hFinite, hK, hQ'⟩ := hQ
        have hK2 : Nat.card K = 2 := by simpa using hK
        exact ⟨K, hField, hFinite, hK, hQ', ggTorusReflGenW_E6Two_three (K := K) hK2⟩)
      (largeEvenLabelAll_torusLift_E6_two ⟨rfl, rfl⟩))

private theorem largeEvenMarking_e6Two_facts {G : Type} [Group G] {Bs X : Subgroup G}
    (hX : GGInnerDiagOnLabel (fun _ lab => lab.tag = .E6 ∧ lab.n = 1) 3 Bs X) :
    LargeEvenMarking X (fun lab R _ I _ θ =>
      ((lab.tag = .E6 ∧ lab.n = 1) ∧ Bs ≤ Subgroup.normalizer (X : Set G) ∧
        ∀ b ∈ Bs, ∃ φ ∈ I,
          LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) ∧
      ((GGCenterPrime 3 R ∧ GGOutdiagPrime 3 R I ∧
        ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
          ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
          ∀ A : Subgroup (MulAut L'), IsElemAbelian 3 A →
            (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
            3 ^ 4 ≤ Nat.card A → GGTorusSelfCent 3 A →
            Nat.card (ggAutomizer (MulAut.conj : L' →* MulAut L').range A) = 1152) ∧
      (GGTorusReflGenW 3 4 R I ∧ GGTorusLift 3 4 R))) := by
  refine largeEvenMarking_and_labelAll (S := fun lab => lab.tag = .E6 ∧ lab.n = 1)
    (P' := fun R _ I _ =>
      (GGCenterPrime 3 R ∧ GGOutdiagPrime 3 R I ∧
        ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
          ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
          ∀ A : Subgroup (MulAut L'), IsElemAbelian 3 A →
            (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
            3 ^ 4 ≤ Nat.card A → GGTorusSelfCent 3 A →
            Nat.card (ggAutomizer (MulAut.conj : L' →* MulAut L').range A) = 1152) ∧
      (GGTorusReflGenW 3 4 R I ∧ GGTorusLift 3 4 R)) ?_ ?_ hX
  · intro lab hlab hs
    have hlabE6 : lab = ⟨.E6, 0, 1⟩ := by
      obtain ⟨t, l, n⟩ := lab
      obtain ⟨ht, hn⟩ := hs
      dsimp only at ht hn hlab
      subst ht
      subst hn
      have hl0 : l = 0 := by simpa using hlab.2
      subst hl0
      rfl
    exact hlabE6 ▸ largeEvenLabelAll_e6Two_facts
  · intro lab R _ I F θ hP
    exact hP.1

theorem card_ggAutomizer_of_e6Two_of_rank {G : Type} [Group G] [Finite G] {B Bs : Subgroup G}
    {x : G} {L D J X : Subgroup G} (hcfg : GGConfig 3 B Bs x L D J)
    (hNoTr : GGNoTransvection 3 Bs)
    (hX : GGInnerDiagOnLabel (fun _ lab => lab.tag = .E6 ∧ lab.n = 1) 3 Bs X)
    (hrk : ∀ {R : Type} [Group R], (X ⧸ Subgroup.center X ≃* R) →
      ∀ hN : Bs ≤ Subgroup.normalizer (X : Set G), commutator X = ⊤ → GGTorusLift 3 4 R →
        3 ^ 4 ≤ Nat.card (ggGamma X hN).range)
    (hZ : Nat.card ↥(Bs ⊓ X ⊓ Subgroup.centralizer (X : Set G)) ≤ 3) :
    Nat.card ↥(ggAutomizer X Bs) = 1152 := by
  obtain ⟨hperf, _, _, hraw⟩ := largeEvenMarking_e6Two_facts hX
  obtain ⟨R, hR, I, F, _, _, θ, hP, hE6facts⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨⟨_, _⟩, hBsN, hBs3⟩ := hP
  obtain ⟨⟨_, _, horder⟩, hrefl, hlift⟩ := hE6facts
  have hBs : IsElemAbelian 3 Bs := hcfg.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs :=
    hcfg.2.1.2.2.2
  have h4 : 3 ^ 4 ≤ Nat.card (ggGamma X hBsN).range := hrk θ hBsN hperf hlift
  have hTB : GGTorusTBGroup 3 4 R I X (ggQuotHom θ) (ggGamma X hBsN).range :=
    ggTorusTBGroup_of_marking (r := 4) Nat.prime_three hBs hSC hperf θ hBsN
      (fun b hb => ggLAut_mem_of_induces X θ hBsN hBs3 hb) h4 (le_trans (by norm_num) h4)
  have hInner : Nat.card (ggAutomizer (MulAut.conj : ↥X →* MulAut ↥X).range
      (ggGamma X hBsN).range) = 1152 :=
    horder X (ggQuotHom θ) (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hperf
      (ggGamma X hBsN).range hTB.2.2.2.1 hTB.2.2.2.2.1 h4 hTB.2.2.2.2.2.2.2
  have hWrefl : ggAutomizer (MulAut.conj : ↥X →* MulAut ↥X).range
      (ggGamma X hBsN).range ≤
        Subgroup.closure (ggTorusReflSet 3 (ggGamma X hBsN).range) :=
    hrefl X (ggQuotHom θ) (ggGamma X hBsN).range hTB
  rw [card_ggAutomizer_eq_gamma_of_weylReflSet (p := 3) Nat.prime_three (by norm_num) (X := X)
    hBs hSC hNoTr hBsN hZ hWrefl]
  exact hInner

theorem card_ggAutomizer_of_e6Two {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig 3 B Bs x L D J) (hNoTr : GGNoTransvection 3 Bs)
    (hL : GGInnerDiagOnLabel (fun _ lab => lab.tag = .E6 ∧ lab.n = 1) 3 Bs L) :
    Nat.card ↥(ggAutomizer L Bs) = 1152 := by
  refine card_ggAutomizer_of_e6Two_of_rank hcfg hNoTr hL
    (fun θ hN hperf hlift => (card_range_ggGamma_bstar_ge hcfg hperf θ hN hlift).1) ?_
  have hle : Bs ⊓ L ⊓ Subgroup.centralizer (L : Set G) ≤
      Bs ⊓ Subgroup.centralizer (L : Set G) := by
    intro z hz
    exact ⟨hz.1.1, hz.2⟩
  have h := Subgroup.card_le_of_le hle
  rwa [GGConfig.card_bstar_inf_centralizer_L hcfg] at h

end E6Two

theorem card_ggAutomizer_of_twA5Three
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig 3 B Bs x L D J)
    (hL : GGInnerDiagOnLabel (fun _ lab => lab.tag = .twA ∧ lab.rank = 5 ∧ 3 ∣ 2 ^ lab.n + 1)
      3 Bs L) :
    Nat.card ↥(ggAutomizer L Bs) = 720 := by
  have hMark : GGInnerDiagOnLabel (fun _ lab => lab.tag = .twA ∧ lab.rank = 5 ∧
      3 ∣ ggTorM lab) 3 Bs L := by
    refine largeEvenMarking_mono (fun lab R _ I F θ hP => ?_) hL
    obtain ⟨⟨htw, hr5, hdvd⟩, hN', hBsI⟩ := hP
    exact ⟨⟨htw, hr5, by simpa [ggTorM, htw] using hdvd⟩, hN', hBsI⟩
  have hM : GGInnerDiagOnLab GGUnitDvd63Label 3 Bs L := by
    refine largeEvenMarking_mono (fun lab R _ I F θ hP => ?_) hL
    obtain ⟨⟨htw, hr5, hdvd⟩, hN', hBsI⟩ := hP
    exact ⟨⟨⟨htw, by omega, hdvd, by omega⟩, hr5, rfl⟩,
      Or.inr (Or.inl ⟨by simp [LargeEvenUntwisted, htw], by simp [htw], hdvd⟩), hN', hBsI⟩
  have hr : ∀ hN : Bs ≤ Subgroup.normalizer (L : Set G),
      3 ^ 4 ≤ Nat.card (ggGamma L hN).range := by
    intro hN
    have hcard := Line63.H5.ggUnitDvd63BstarRankInput_holds G 3 B Bs x L D J hcfg hM
    obtain ⟨hp, hBs, hxBs, hLx, -⟩ := hcfg.tableB_facts
    have hS : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
    have hmul := card_range_ggGamma_mul_of hp hBs hxBs hS.2.2.1 hLx hS.2.2.2.2 hN
    rw [← hmul, pow_succ] at hcard
    exact Nat.le_of_mul_le_mul_right hcard hp.pos
  obtain ⟨f, hf, hpq, -, hN, hTor⟩ := ggTwA5Three_torData hcfg hMark hr
  have hodd : Odd (2 ^ f + 1) := by
    obtain ⟨g, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : f ≠ 0)
    rw [pow_succ]
    exact ⟨2 ^ g, by omega⟩
  have hW := NSJoin.weylOfType_of_torData (p := 3) (by norm_num : (3 : ℕ) ≠ 2) hodd hpq
    (ggIntCartan_A 5) hcfg.2.1.2.1 hcfg.2.1.2.2.2 hN hTor
  obtain ⟨e, -⟩ := hW
  rw [← Nat.card_congr e.toEquiv, l05nK3a_card_coxeterA 5]
  norm_num [Nat.factorial]

private theorem false_of_ggAutomizer_card_eq {G : Type} [Group G] {Bs L : Subgroup G} {n m : ℕ}
    (hcard : Nat.card ↥(ggAutomizer L Bs) = 2 ^ (n - 1) * (n - 1).factorial)
    (h : Nat.card ↥(ggAutomizer L Bs) = m) (hm : ∀ k, 2 ^ k * k.factorial ≠ m) : False :=
  hm (n - 1) (hcard.symm.trans h)

section Res

theorem ggSecFiveBCoordBResInput_holds : GGSecFiveBCoordBResInput := by
  intro G _ _ p B Bs x L D J 𝒦 hR n hn eta i0 hAut hL
  have hcfg : GGConfig p B Bs x L D J := hR.1.1
  have hNoTr : GGNoTransvection p Bs := hR.1.2.2.2.1
  obtain ⟨hp, -, -, -, -⟩ := hcfg.tableB_facts
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hcardA : Nat.card ↥(ggAutomizer L Bs) = 2 ^ (n - 1) * (n - 1).factorial :=
    card_ggAutomizer_of_bCoordinateBlock hp hp2 eta i0 hAut
  have hmarkL := hL
  obtain ⟨-, lab, -, hraw⟩ := hmarkL
  obtain ⟨-, -, -, -, -, -, -, hres, -, -⟩ := largeEvenRawDatum_exists hraw
  have hp3 : p = 3 := by
    have h := hres
    simp only [GGSecFiveBCoordBResLabel] at h
    exact h.1
  subst hp3
  have hBs3 : Nat.card Bs = 3 ^ n := by
    rw [Nat.card_congr eta.toEquiv, Nat.card_fun, Nat.card_congr Multiplicative.toAdd,
      Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hsplit : GGInnerDiagOnLabel (fun _ lab =>
      (lab.tag = .A ∧ 6 ≤ lab.rank ∧ lab.n = 1) ∨
        (lab.tag = .E6 ∧ lab.n = 1) ∨ (lab.tag = .F4 ∧ lab.n = 1) ∨
        (lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1) ∨
        (lab.tag = .twA ∧ lab.rank = 5 ∧ 3 ∣ 2 ^ lab.n + 1)) 3 Bs L := by
    refine GGInnerDiagOnLabel.mono_label (S := fun p lab => GGSecFiveBCoordBResLabel p lab) ?_ hL
    intro lab h
    simpa [GGSecFiveBCoordBResLabel] using h
  have hZ : Nat.card ↥(Bs ⊓ L ⊓ Subgroup.centralizer (L : Set G)) ≤ 3 := by
    have hle : Bs ⊓ L ⊓ Subgroup.centralizer (L : Set G) ≤
        Bs ⊓ Subgroup.centralizer (L : Set G) := by
      intro z hz
      exact ⟨hz.1.1, hz.2⟩
    have h := Subgroup.card_le_of_le hle
    rwa [GGConfig.card_bstar_inf_centralizer_L hcfg] at h
  rcases GGInnerDiagOnLabel.elim_or hsplit with hA | hRest1
  · exact ggSecFiveBCoordBRes_typeA hcfg hBs3 hA
  rcases GGInnerDiagOnLabel.elim_or hRest1 with hE6 | hRest2
  · exfalso
    exact false_of_ggAutomizer_card_eq hcardA (card_ggAutomizer_of_e6Two hcfg hNoTr hE6)
      two_pow_mul_factorial_ne_1152
  rcases GGInnerDiagOnLabel.elim_or hRest2 with hF4 | hRest3
  · have hF4' : GGInnerDiagOnLabel GGF4ThreeLabel 3 Bs L := by
      refine GGInnerDiagOnLabel.mono_label
        (S := fun _ lab => lab.tag = .F4 ∧ lab.n = 1) ?_ hF4
      intro lab h
      obtain ⟨ht, hn⟩ := h
      dsimp only [GGF4ThreeLabel]
      exact ⟨ht, rfl, by rw [hn]; norm_num⟩
    exfalso
    exact false_of_ggAutomizer_card_eq hcardA
      (card_ggAutomizer_of_f4Three hcfg hNoTr hF4' hZ) two_pow_mul_factorial_ne_1152
  rcases GGInnerDiagOnLabel.elim_or hRest3 with hTwE6 | hTwA
  · have hTwE6' : GGInnerDiagOnLabel GGTwE6BadLabel 3 Bs L := by
      refine GGInnerDiagOnLabel.mono_label
        (S := fun _ lab => lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1) ?_ hTwE6
      intro lab h
      obtain ⟨ht, hd⟩ := h
      dsimp only [GGTwE6BadLabel]
      exact ⟨ht, rfl, hd⟩
    have hcardE6 : Nat.card ↥(ggAutomizer L Bs) = 51840 := by
      obtain ⟨e, -⟩ := ggTwE6Bad_weylOfType hR.1 hTwE6'
      rw [← Nat.card_congr e.toEquiv, card_coxeterE6_group]
    exfalso
    exact false_of_ggAutomizer_card_eq hcardA hcardE6 two_pow_mul_factorial_ne_51840
  · exfalso
    exact false_of_ggAutomizer_card_eq hcardA
      (card_ggAutomizer_of_twA5Three hcfg hTwA) two_pow_mul_factorial_ne_720

end Res

end CFSG.StandardType

end
