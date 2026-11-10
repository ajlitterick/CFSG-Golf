module

public import CFSG.LocalAnalysis.StandardType.GGK2E6E6OriginalSpanTwo

public import CFSG.LocalAnalysis.StandardType.GGIntCartanDet

public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepMove

public import CFSG.LocalAnalysis.StandardType.GGResIBasic
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcReflLinear
public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3BridgeA
public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3Bridge
public import CFSG.LocalAnalysis.StandardType.GGPZCartanRank
public import CFSG.LocalAnalysis.StandardType.GGFrameRouteNbrFix
public import CFSG.LocalAnalysis.StandardType.GGTBTorCor
public import CFSG.LocalAnalysis.StandardType.GGTBE6
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1E6Three
public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeLinear
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallTypeA

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open

@[expose] def ggTypLADvd (p : ℕ) {Λ Λ' : Type} (ML : CoxeterMatrix Λ)
    (_ : CoxeterMatrix Λ') : Prop :=
  GGIsTypeA ML ∧ p ∣ Nat.card Λ + 1

theorem ggTypLADvd_or_E6_of_cartan_singular
    {p : ℕ} {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {M : CoxeterMatrix Λ} {C : Matrix Λ Λ ℤ} (hC : GGIntCartan M C)
    (h : (∃ (n : ℕ) (e : Fin n ≃ Λ), 1 ≤ n ∧ p ∣ n + 1 ∧
        ∀ i j, C (e i) (e j) = CartanMatrix.A n i j) ∨
      (p = 3 ∧ ∃ e : Fin 6 ≃ Λ,
        ∀ i j, C (e i) (e j) = CartanMatrix.E 6 i j)) :
    (GGIsTypeA M ∧ p ∣ Nat.card Λ + 1) ∨ (p = 3 ∧ GGIsTypeE6 M) := by
  rcases h with ⟨n, e, hn, hpd, he⟩ | ⟨hp3, e, he⟩
  · left
    have hCeq : C = fun i j => CartanMatrix.A n (e.symm i) (e.symm j) := by
      ext i j
      simpa using he (e.symm i) (e.symm j)
    have hAint : GGIntCartan ((CoxeterMatrix.A n).reindex e) C := by
      rw [hCeq]
      exact l05nBL_intCartan_reindex (ggIntCartan_A n) e.symm
    have hMeq : M = (CoxeterMatrix.A n).reindex e := ggIntCartan_coxeter_eq hC hAint
    refine ⟨⟨n, e, hn, hMeq⟩, ?_⟩
    have hcard : Fintype.card Λ = n := by
      simpa using Fintype.card_congr e.symm
    simpa [hcard] using hpd
  · right
    refine ⟨hp3, ?_⟩
    exact ⟨e, ggIntCartan_E6_coxeter_reindex hC e he⟩

theorem ggFixedSubmodule_pi_ker {p : ℕ} [Fact p.Prime] {Λ : Type} [Fintype Λ]
    [DecidableEq Λ] {S : Finset Λ} {E : Type} [Group E] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (ι : Additive E ≃+ V)
    (φ : {i : Λ // i ∉ S} → MulAut E) (h : {i : Λ // i ∉ S} → V)
    (α : {i : Λ // i ∉ S} → Module.Dual (ZMod p) V)
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hdiag : ∀ i, α i (h i) = 2) (hp2 : p ≠ 2)
    (N : Subgroup (MulAut E)) (hgen : N = Subgroup.closure (Set.range φ)) :
    (LinearMap.pi α).ker = ggFixedSubmodule (p := p) ι N := by
  classical
  have h2 : (2 : ZMod p) ≠ 0 := zmod_two_ne_zero hp2
  have hh : ∀ i, h i ≠ 0 := by
    intro i hi
    apply h2
    rw [← hdiag i, hi, map_zero]
  ext v
  constructor
  · intro hv
    rw [LinearMap.mem_ker] at hv
    have hvα : ∀ i, α i v = 0 := by
      intro i
      have := congrFun hv i
      simpa using this
    rw [mem_ggFixedSubmodule_iff]
    intro ψ hψ
    rw [hgen] at hψ
    refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hψ
    · rintro _ ⟨i, rfl⟩
      rw [hlin, hvα i, zero_smul, sub_zero]
    · simp
    · intro x y _ _ hx hy
      rw [map_mul]
      change ggLin (p := p) ι x (ggLin (p := p) ι y v) = v
      rw [hy, hx]
    · intro x _ hx
      calc
        ggLin (p := p) ι x⁻¹ v =
            ggLin (p := p) ι x⁻¹ (ggLin (p := p) ι x v) := by rw [hx]
        _ = (ggLin (p := p) ι x⁻¹ * ggLin (p := p) ι x) v := rfl
        _ = ggLin (p := p) ι (x⁻¹ * x) v := by rw [map_mul]
        _ = ggLin (p := p) ι 1 v := by rw [inv_mul_cancel]
        _ = v := by simp
  · intro hv
    rw [mem_ggFixedSubmodule_iff] at hv
    rw [LinearMap.mem_ker]
    funext i
    have hfix : ggLin (p := p) ι (φ i) v = v := by
      apply hv
      rw [hgen]
      exact Subgroup.subset_closure ⟨i, rfl⟩
    have hzero : α i v • h i = 0 := by
      have h' : v - α i v • h i = v := by
        rw [← hlin i v, hfix]
      exact sub_eq_self.mp h'
    exact (smul_eq_zero.mp hzero).resolve_right (hh i)

theorem e6_exact_two_survivor_det_ne_zero {S : Finset (Fin 6)}
    (hS : S.card = 2) (hc : GGDeletedConnectedS CoxeterMatrix.E₆ S) :
    (Matrix.of fun i j : {i : Fin 6 // i ∉ S} =>
      (CartanMatrix.E 6 i.val j.val : ZMod 3)).det ≠ 0 := by
  rcases ggDeletedConnectedS_E6_exact_two hS hc with rfl | rfl | rfl | rfl | rfl <;>
    decide +kernel

section E6DeletedExtension

open Module

set_option maxHeartbeats 800000


end E6DeletedExtension


theorem ggIntCartan_E6_entries_of_type
    {Λ : Type} {M : CoxeterMatrix Λ} {C : Matrix Λ Λ ℤ}
    (hC : GGIntCartan M C) (e : Fin 6 ≃ Λ) (hM : M = CoxeterMatrix.E₆.reindex e) :
    ∀ i j, C (e i) (e j) = CartanMatrix.E 6 i j := by
  have hstd : GGIntCartan M (fun i j => CartanMatrix.E 6 (e.symm i) (e.symm j)) := by
    rw [hM]
    exact l05nBL_intCartan_reindex ggIntCartan_E₆ e.symm
  have hthree : ∀ i j, i ≠ j → M i j ≤ 3 := by
    intro i j hij
    rw [hM]
    change CoxeterMatrix.E₆ (e.symm i) (e.symm j) ≤ 3
    have he6 : ∀ a b : Fin 6, CoxeterMatrix.E₆ a b ≤ 3 := by
      intro a b
      fin_cases a <;> fin_cases b <;> decide +kernel
    exact he6 _ _
  have heq : C = (fun i j => CartanMatrix.E 6 (e.symm i) (e.symm j)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      exact (hC.1 i).trans (hstd.1 i).symm
    · exact ((hC.pair hstd hij).2 (hthree i j hij)).1
  intro i j
  rw [heq]
  simp


theorem finrank_le_card_add_finrank_ker_pi {p : ℕ} [Fact p.Prime] {Λ : Type} [Fintype Λ]
    [DecidableEq Λ] {S : Finset Λ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    [Finite V] (α : {i : Λ // i ∉ S} → Module.Dual (ZMod p) V) :
    Module.finrank (ZMod p) V ≤
      Fintype.card {i : Λ // i ∉ S} +
        Module.finrank (ZMod p) (LinearMap.pi α).ker := by
  let : Module.Finite (ZMod p) V := Module.Finite.of_finite
  let hMod : Module (ZMod p) ({i : Λ // i ∉ S} → ZMod p) :=
    Pi.module ({i : Λ // i ∉ S}) (fun _ => ZMod p) (ZMod p)
  let := hMod
  let π : V →ₗ[ZMod p] ({i : Λ // i ∉ S} → ZMod p) := LinearMap.pi α
  have h := @LinearMap.finrank_range_add_finrank_ker (ZMod p) V _ _ _
    ({i : Λ // i ∉ S} → ZMod p)
    (inferInstance : AddCommGroup ({i : Λ // i ∉ S} → ZMod p)) hMod _ π
  have hcod : Module.finrank (ZMod p) ({i : Λ // i ∉ S} → ZMod p) =
      Fintype.card {i : Λ // i ∉ S} := by
    simp
  have hrange : Module.finrank (ZMod p) π.range ≤ Fintype.card {i : Λ // i ∉ S} := by
    rw [← hcod]
    exact Submodule.finrank_le _
  change Module.finrank (ZMod p) V ≤
    Fintype.card {i : Λ // i ∉ S} + Module.finrank (ZMod p) π.ker
  rw [← h]
  exact Nat.add_le_add_right hrange _

theorem fix_mem_centralizer_of_pointwise_noFix {G : Type} [Group G] [Finite G]
    {p : ℕ} (hp : p.Prime) {Bs X : Subgroup G}
    (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    {R : Type} [Group R]
    (θ : X ⧸ Subgroup.center X ≃* R)
    {I : Set (MulAut R)} (hBsN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hBs3 : ∀ b ∈ Bs, ∃ φ ∈ I,
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hT : ∀ a ∈ (ggGamma X hBsN).range,
      (∀ n : X, GGTorusWeylElt p (ggGamma X hBsN).range n →
        MulAut.conj n * a * (MulAut.conj n)⁻¹ = a) → a = 1) :
    ∀ b : Bs, (∀ φ ∈ ggAutomizer X Bs, φ b = b) →
      (b : G) ∈ Subgroup.centralizer (X : Set G) := by
  classical
  have := Fact.mk hp
  intro b hb
  set γ := ggGamma X hBsN with hγ
  have hBp : ∀ b : Bs, b ^ p = 1 := fun b => Subtype.ext (by simpa using hBs.2 b b.2)
  have hBc : ∀ a b : Bs, a * b = b * a := fun a b =>
    Subtype.ext (IsElemAbelian.comm hBs a.2 b.2)
  have hA : IsElemAbelian p γ.range := isElemAbelian_range hBc hBp γ
  have hAI : ∀ a ∈ γ.range, ∃ φ ∈ I, ∀ l : X, φ (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    rintro _ ⟨b, rfl⟩
    exact ⟨ggBeta X θ hBsN b, ggBeta_mem X θ hBsN hBs3 b,
      fun l => ggBeta_ggQuotHom X hBsN θ b l⟩
  rw [← ggGamma_eq_one_iff X hBsN]
  refine hT (γ b) ⟨b, rfl⟩ ?_
  intro n hn
  have hWB : ∀ b ∈ Bs, (n : G) * b * (n : G)⁻¹ ∈ Bs := by
    intro b hb
    obtain ⟨htp, htA⟩ := hn (γ ⟨b, hb⟩) ⟨⟨b, hb⟩, rfl⟩
    have htG : ((n * (γ ⟨b, hb⟩ n)⁻¹ : X) : G) = n * b * (n : G)⁻¹ * b⁻¹ := by
      push_cast
      rw [hγ, ggGamma_coe]
      group
    have htC : ((n * (γ ⟨b, hb⟩ n)⁻¹ : X) : G) ∈ Subgroup.centralizer (Bs : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b' hb'
      have h1 := congrArg Subtype.val (htA (γ ⟨b', hb'⟩) ⟨⟨b', hb'⟩, rfl⟩)
      rw [hγ, ggGamma_coe] at h1
      calc b' * ((n * (γ ⟨b, hb⟩ n)⁻¹ : X) : G)
          = b' * ((n * (γ ⟨b, hb⟩ n)⁻¹ : X) : G) * b'⁻¹ * b' := by group
        _ = ((n * (γ ⟨b, hb⟩ n)⁻¹ : X) : G) * b' := by rw [h1]
    have htp' : ((n * (γ ⟨b, hb⟩ n)⁻¹ : X) : G) ^ p = 1 := by
      have := congrArg Subtype.val htp
      simpa using this
    have htB := hSC _ htC htp'
    have e : (n : G) * b * (n : G)⁻¹ =
        ((n * (γ ⟨b, hb⟩ n)⁻¹ : X) : G) * b := by
      rw [htG]
      group
    rw [e]
    exact Bs.mul_mem htB hb
  have hnN : (n : G) ∈ Subgroup.normalizer (Bs : Set G) := by
    have h := mem_normalizer_of_forall_conj_mem (W := Bs) (g := (n : G)⁻¹) (fun w hw => by
      simpa using hWB w hw)
    simpa using Subgroup.inv_mem _ h
  have hφ : Bs.normalizerMonoidHom ⟨n, hnN⟩ ∈ ggAutomizer X Bs :=
    Subgroup.subset_closure ⟨(n : G), n.2, hnN, fun _ => rfl⟩
  have hnb : (n : G) * b * (n : G)⁻¹ = b := congrArg Subtype.val (hb _ hφ)
  have hc := ggGamma_conj X hBsN n b (hWB b b.2)
  rw [← hγ] at hc
  rw [← hc]
  congr 1
  exact Subtype.ext hnb


theorem finrank_fixedSubmodule_eq_two_of_fix_eq_D
    {p : ℕ} [Fact p.Prime] {E : Type} [Group E] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] [Finite V]
    (ι : Additive E ≃+ V) (A : Subgroup (MulAut E)) (D : Subgroup E)
    (hfix : ∀ b : E, (∀ φ ∈ A, φ b = b) ↔ b ∈ D)
    (hDcard : Nat.card D = p ^ 2) :
    Module.finrank (ZMod p) (ggFixedSubmodule (p := p) ι A) = 2 := by
  classical
  let f : D → ↥(ggFixedSubmodule (p := p) ι A) := fun d =>
    ⟨ι (Additive.ofMul (d : E)), by
      rw [mem_ggFixedSubmodule_iff]
      intro φ hφ
      rw [ggLin_apply_ofMul]
      rw [((hfix (d : E)).mpr d.2) φ hφ]⟩
  have hf_inj : Function.Injective f := by
    intro d1 d2 h
    apply Subtype.ext
    apply Additive.ofMul.injective
    apply ι.injective
    exact congrArg Subtype.val h
  have hf_surj : Function.Surjective f := by
    intro v
    let b : E := Additive.toMul (ι.symm v.1)
    have hbD : b ∈ D := by
      apply (hfix b).mp
      intro φ hφ
      have hv := (mem_ggFixedSubmodule_iff.mp v.2) φ hφ
      have hv_eq : v.1 = ι (Additive.ofMul b) := by simp [b]
      rw [hv_eq, ggLin_apply_ofMul] at hv
      exact Additive.ofMul.injective (ι.injective hv)
    refine ⟨⟨b, hbD⟩, ?_⟩
    apply Subtype.ext
    simp [f, b]
  let e := Equiv.ofBijective f ⟨hf_inj, hf_surj⟩
  have hcard : Nat.card ↥(ggFixedSubmodule (p := p) ι A) = Nat.card D :=
    (Nat.card_congr e).symm
  have hfixedpow : Nat.card ↥(ggFixedSubmodule (p := p) ι A) =
      p ^ Module.finrank (ZMod p) ↥(ggFixedSubmodule (p := p) ι A) := by
    let : Module.Finite (ZMod p) ↥(ggFixedSubmodule (p := p) ι A) := Module.Finite.of_finite
    have h := Module.natCard_eq_pow_finrank (K := ZMod p)
      (V := ↥(ggFixedSubmodule (p := p) ι A))
    simpa using h
  have hEq : p ^ Module.finrank (ZMod p) ↥(ggFixedSubmodule (p := p) ι A) = p ^ 2 := by
    calc
      p ^ Module.finrank (ZMod p) ↥(ggFixedSubmodule (p := p) ι A) =
          Nat.card ↥(ggFixedSubmodule (p := p) ι A) := hfixedpow.symm
      _ = Nat.card D := hcard
      _ = p ^ 2 := hDcard
  exact Nat.pow_right_injective (Fact.out : p.Prime).two_le hEq


theorem ggResExact2_finrank_le_card
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs J : Subgroup G} (hp2 : p ≠ 2)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {S : Finset Λ}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ι : Additive ↥Bs ≃+ V)
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ} (hCL : GGIntCartan ML CL)
    (φL : Λ → MulAut ↥Bs) (hL : Λ → V) (αL : Λ → Module.Dual (ZMod p) V)
    (hlinL : ∀ i w, ggLin (p := p) ι (φL i) w = w - αL i w • hL i)
    (hpairL : ∀ i j, αL i (hL j) = (CL i j : ZMod p))
    (hS : S.card = 2)
    (hgenJ : ggAutomizer J Bs =
      Subgroup.closure (Set.range (fun i : {i : Λ // i ∉ S} => φL i)))
    (hfix : Module.finrank (ZMod p) (ggFixedSubmodule (p := p) ι (ggAutomizer J Bs)) = 2) :
    Module.finrank (ZMod p) V ≤ Fintype.card Λ := by
  classical
  have hdiagJ : ∀ i : {i : Λ // i ∉ S}, αL i (hL i) = 2 := by
    intro i
    rw [hpairL i i, hCL.1 i]
    norm_num
  have hker := ggFixedSubmodule_pi_ker (p := p) (Λ := Λ) (S := S) (E := ↥Bs) (V := V)
    ι (fun i : {i : Λ // i ∉ S} => φL i) (fun i => hL i) (fun i => αL i)
    (fun i w => hlinL i w) hdiagJ hp2 (ggAutomizer J Bs) hgenJ
  have hle := finrank_le_card_add_finrank_ker_pi (p := p) (Λ := Λ) (S := S) (V := V)
    (fun i : {i : Λ // i ∉ S} => αL i)
  rw [hker] at hle
  rw [hfix] at hle
  have hsub : Fintype.card {i : Λ // i ∈ S} = S.card := by
    rw [Fintype.card_subtype]
    simp
  have hcomp : Fintype.card {i : Λ // i ∉ S} = Fintype.card Λ - S.card := by
    rw [Fintype.card_subtype_compl (fun i : Λ => i ∈ S), hsub]
  have hSle : S.card ≤ Fintype.card Λ := S.card_le_univ
  have hcard : Fintype.card {i : Λ // i ∉ S} + 2 = Fintype.card Λ := by
    rw [hcomp, hS]
    omega
  calc
    Module.finrank (ZMod p) V ≤ Fintype.card {i : Λ // i ∉ S} + 2 := hle
    _ = Fintype.card Λ := hcard

theorem ggResExact2_cartan_singular
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {S : Finset Λ}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ι : Additive ↥Bs ≃+ V)
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    (hML : GGIsWeylMatrix ML) (hCL : GGIntCartan ML CL)
    (φL : Λ → MulAut ↥Bs) (hL : Λ → V) (αL : Λ → Module.Dual (ZMod p) V)
    (hlinL : ∀ i w, ggLin (p := p) ι (φL i) w = w - αL i w • hL i)
    (hpairL : ∀ i j, αL i (hL j) = (CL i j : ZMod p))
    (hgenL : ggAutomizer L Bs = Subgroup.closure (Set.range φL))
    (hS : S.card = 2)
    (hgenJ : ggAutomizer J Bs =
      Subgroup.closure (Set.range (fun i : {i : Λ // i ∉ S} => φL i)))
    (hfix : Module.finrank (ZMod p) (ggFixedSubmodule (p := p) ι (ggAutomizer J Bs)) = 2) :
    (∃ (n : ℕ) (e : Fin n ≃ Λ), 1 ≤ n ∧ p ∣ n + 1 ∧
      ∀ i j, CL (e i) (e j) = CartanMatrix.A n i j) ∨
    (p = 3 ∧ ∃ e : Fin 6 ≃ Λ, ∀ i j, CL (e i) (e j) = CartanMatrix.E 6 i j) := by
  classical
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have haxis := ggResL_rank_core_add_one hH hlinL hpairL hCL.1 hgenL
  have hdimΛ : Module.finrank (ZMod p) V ≤ Fintype.card Λ :=
    ggResExact2_finrank_le_card hp2 ι hCL φL hL αL hlinL hpairL hS hgenJ hfix
  have hrank : Matrix.rank (CL.map (Int.castRingHom (ZMod p))) < Fintype.card Λ := by
    omega
  exact ggIntCartan_A_or_E6_of_rank_lt hML hCL hp2 hrank


theorem ggResExact2_fix_eq_two_of_fix_centralizer
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hI1 : Bs ⊓ Subgroup.centralizer (J : Set G) = D)
    (hfixJ : ∀ b : ↥Bs,
      (∀ φ ∈ ggAutomizer J Bs, φ b = b) ↔
        (b : G) ∈ Subgroup.centralizer (J : Set G))
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ι : Additive ↥Bs ≃+ V) :
    Module.finrank (ZMod p) (ggFixedSubmodule (p := p) ι (ggAutomizer J Bs)) = 2 := by
  have hDle : D ≤ Bs := hH.1.2.2.1.1.trans hH.1.2.1.1
  have hfixD : ∀ b : ↥Bs,
      (∀ φ ∈ ggAutomizer J Bs, φ b = b) ↔ b ∈ D.subgroupOf Bs := by
    intro b
    rw [Subgroup.mem_subgroupOf]
    rw [hfixJ b, ← hI1]
    exact ⟨fun h => ⟨b.2, h⟩, fun h => h.2⟩
  have hDcard : Nat.card D = p ^ 2 := hH.1.2.2.1.2.2.1
  have hDcard' : Nat.card (D.subgroupOf Bs) = p ^ 2 := by
    rw [← hDcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDle).toEquiv
  exact finrank_fixedSubmodule_eq_two_of_fix_eq_D ι (ggAutomizer J Bs)
    (D.subgroupOf Bs) hfixD hDcard'


theorem ggResExact2_typed_dichotomy_L_of_fixed
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hI1 : Bs ⊓ Subgroup.centralizer (J : Set G) = D)
    (hfixJ : ∀ b : ↥Bs,
      (∀ φ ∈ ggAutomizer J Bs, φ b = b) ↔
        (b : G) ∈ Subgroup.centralizer (J : Set G))
    (hD : GGResLeviDatumCard 2 p Bs L J K ggSelAny ggTypAny) :
    GGResLeviDatumCard 2 p Bs L J K ggSelAny (ggTypLADvd p) ∨
    (p = 3 ∧ GGResLeviDatumCard 2 p Bs L J K ggSelAny ggTypLE6) := by
  classical
  rcases hD with ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    hS, hΛa1, hΛa3, hML, hCL, hMK, hCK, htyp, hlin, hrefl, hpair, hpairK, hsel,
    ⟨fL, hfL⟩, ⟨fK, hfK⟩, hclosL, hclosK, hconn, hclosJ⟩
  let := i1
  let := i2
  let := i3
  let := i4
  let := i5
  let := i6
  let : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  have hfix := ggResExact2_fix_eq_two_of_fix_centralizer hH hI1 hfixJ ι
  let pack : ∀ (typ : ∀ {Λ Λ' : Type},
      CoxeterMatrix Λ → CoxeterMatrix Λ' → Prop),
      typ ML MK → GGResLeviDatumCard 2 p Bs L J K ggSelAny typ :=
    fun typ htyp => ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
      hS, hΛa1, hΛa3, hML, hCL, hMK, hCK, htyp, hlin, hrefl, hpair, hpairK, hsel,
      ⟨fL, hfL⟩, ⟨fK, hfK⟩, hclosL, hclosK, hconn, hclosJ⟩
  have hsing := ggResExact2_cartan_singular (hH := hH) (Λ := Λ) (S := S) (V := V) (ι := ι)
    (hML := hML) (hCL := hCL) (φL := fun i => φ (Sum.inl i))
    (hL := fun i => h (Sum.inl i)) (αL := fun i => α (Sum.inl i))
    (hlinL := fun i w => hlin (Sum.inl i) w) (hpairL := hpair)
    (hgenL := hclosL) (hS := hS) (hgenJ := hclosJ) (hfix := hfix)
  rcases ggTypLADvd_or_E6_of_cartan_singular hCL hsing with ⟨hA, hpdiv⟩ | ⟨hp3, hE6⟩
  · exact Or.inl (pack (ggTypLADvd p) ⟨hA, hpdiv⟩)
  · exact Or.inr ⟨hp3, pack ggTypLE6 hE6⟩


section E6


end E6

theorem card_fixedSubmodule_eq_card_of_fix_eq {p : ℕ} [Fact p.Prime]
    {E : Type} [Group E] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive E ≃+ V) (A : Subgroup (MulAut E)) (D : Subgroup E)
    (hfix : ∀ b : E, (∀ φ ∈ A, φ b = b) ↔ b ∈ D) :
    Nat.card ↥(ggFixedSubmodule (p := p) ι A) = Nat.card D := by
  classical
  let f : D → ↥(ggFixedSubmodule (p := p) ι A) := fun d =>
    ⟨ι (Additive.ofMul (d : E)), by
      rw [mem_ggFixedSubmodule_iff]
      intro φ hφ
      rw [ggLin_apply_ofMul]
      rw [((hfix (d : E)).mpr d.2) φ hφ]⟩
  have hf_inj : Function.Injective f := by
    intro d1 d2 h
    apply Subtype.ext
    apply Additive.ofMul.injective
    apply ι.injective
    exact congrArg Subtype.val h
  have hf_surj : Function.Surjective f := by
    intro v
    let b : E := Additive.toMul (ι.symm v.1)
    have hbD : b ∈ D := by
      apply (hfix b).mp
      intro φ hφ
      have hv := (mem_ggFixedSubmodule_iff.mp v.2) φ hφ
      have hv_eq : v.1 = ι (Additive.ofMul b) := by simp [b]
      rw [hv_eq, ggLin_apply_ofMul] at hv
      exact Additive.ofMul.injective (ι.injective hv)
    refine ⟨⟨b, hbD⟩, ?_⟩
    apply Subtype.ext
    simp [f, b]
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩)).symm

theorem finrank_fixedSubmodule_le_three_of_fix_eq_of_card_le {p : ℕ} [Fact p.Prime]
    {E : Type} [Group E] [Finite E] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive E ≃+ V) (A : Subgroup (MulAut E)) (D : Subgroup E)
    (hfix : ∀ b : E, (∀ φ ∈ A, φ b = b) ↔ b ∈ D)
    (hcard : Nat.card D ≤ p ^ 3) :
    Module.finrank (ZMod p) (ggFixedSubmodule (p := p) ι A) ≤ 3 := by
  classical
  let W := ggFixedSubmodule (p := p) ι A
  let : Finite V := Finite.of_equiv (Additive E) ι.toEquiv
  have hcardW : Nat.card ↥W = Nat.card D :=
    card_fixedSubmodule_eq_card_of_fix_eq ι A D hfix
  have hpow : Nat.card ↥W = p ^ Module.finrank (ZMod p) ↥W := by
    let : Module.Finite (ZMod p) ↥W := Module.Finite.of_finite
    simpa using (Module.natCard_eq_pow_finrank (K := ZMod p) (V := ↥W))
  have hle : p ^ Module.finrank (ZMod p) ↥W ≤ p ^ 3 := by
    rw [← hpow, hcardW]
    exact hcard
  exact (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp hle


theorem ggResExact2_fix_le_three {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hfixJ : ∀ b : ↥Bs,
      (∀ φ ∈ ggAutomizer J Bs, φ b = b) ↔
        (b : G) ∈ Subgroup.centralizer (J : Set G))
    {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) :
    Module.finrank (ZMod p) (ggFixedSubmodule (p := p) ι (ggAutomizer J Bs)) ≤ 3 := by
  classical
  let C : Subgroup G := Bs ⊓ Subgroup.centralizer (J : Set G)
  let D' : Subgroup ↥Bs := C.subgroupOf Bs
  have hfixC : ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer J Bs, φ b = b) ↔ b ∈ D' := by
    intro b
    rw [hfixJ b, Subgroup.mem_subgroupOf]
    exact ⟨fun h => ⟨b.2, h⟩, fun h => h.2⟩
  have hcardC : Nat.card C ≤ p ^ 3 :=
    GGConfig.card_bstar_inf_centralizer_J_le hH.1
  have hcardD' : Nat.card D' ≤ p ^ 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
    exact hcardC
  exact finrank_fixedSubmodule_le_three_of_fix_eq_of_card_le ι (ggAutomizer J Bs) D' hfixC hcardD'

theorem ggResExact2_finrank_le_card_add_one {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {Bs J : Subgroup G} (hp2 : p ≠ 2)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {S : Finset Λ}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ι : Additive ↥Bs ≃+ V)
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ} (hCL : GGIntCartan ML CL)
    (φL : Λ → MulAut ↥Bs) (hL : Λ → V) (αL : Λ → Module.Dual (ZMod p) V)
    (hlinL : ∀ i w, ggLin (p := p) ι (φL i) w = w - αL i w • hL i)
    (hpairL : ∀ i j, αL i (hL j) = (CL i j : ZMod p))
    (hS : S.card = 2)
    (hgenJ : ggAutomizer J Bs =
      Subgroup.closure (Set.range (fun i : {i : Λ // i ∉ S} => φL i)))
    (hfix : Module.finrank (ZMod p) (ggFixedSubmodule (p := p) ι (ggAutomizer J Bs)) ≤ 3) :
    Module.finrank (ZMod p) V ≤ Fintype.card Λ + 1 := by
  classical
  have hdiagJ : ∀ i : {i : Λ // i ∉ S}, αL i (hL i) = 2 := by
    intro i
    rw [hpairL i i, hCL.1 i]
    norm_num
  have hker := ggFixedSubmodule_pi_ker (p := p) (Λ := Λ) (S := S) (E := ↥Bs) (V := V)
    ι (fun i : {i : Λ // i ∉ S} => φL i) (fun i => hL i) (fun i => αL i)
    (fun i w => hlinL i w) hdiagJ hp2 (ggAutomizer J Bs) hgenJ
  have hle := finrank_le_card_add_finrank_ker_pi (p := p) (Λ := Λ) (S := S) (V := V)
    (fun i : {i : Λ // i ∉ S} => αL i)
  rw [hker] at hle
  have hle' : Module.finrank (ZMod p) V ≤ Fintype.card {i : Λ // i ∉ S} + 3 :=
    hle.trans (Nat.add_le_add_left hfix _)
  have hsub : Fintype.card {i : Λ // i ∈ S} = S.card := by
    rw [Fintype.card_subtype]
    simp
  have hcomp : Fintype.card {i : Λ // i ∉ S} = Fintype.card Λ - S.card := by
    rw [Fintype.card_subtype_compl (fun i : Λ => i ∈ S), hsub]
  have hSle : S.card ≤ Fintype.card Λ := S.card_le_univ
  calc
    Module.finrank (ZMod p) V ≤ Fintype.card {i : Λ // i ∉ S} + 3 := hle'
    _ = (Fintype.card Λ - S.card) + 3 := by rw [hcomp]
    _ = Fintype.card Λ + 1 := by rw [hS]; omega

theorem ggResExact2_fix_eq_three_of_finrank_eq_card_add_one {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {Bs J : Subgroup G} (hp2 : p ≠ 2)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {S : Finset Λ}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ι : Additive ↥Bs ≃+ V)
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ} (hCL : GGIntCartan ML CL)
    (φL : Λ → MulAut ↥Bs) (hL : Λ → V) (αL : Λ → Module.Dual (ZMod p) V)
    (hlinL : ∀ i w, ggLin (p := p) ι (φL i) w = w - αL i w • hL i)
    (hpairL : ∀ i j, αL i (hL j) = (CL i j : ZMod p))
    (hS : S.card = 2)
    (hgenJ : ggAutomizer J Bs =
      Subgroup.closure (Set.range (fun i : {i : Λ // i ∉ S} => φL i)))
    (hdim : Module.finrank (ZMod p) V = Fintype.card Λ + 1)
    (hfixle : Module.finrank (ZMod p) (ggFixedSubmodule (p := p) ι (ggAutomizer J Bs)) ≤ 3) :
    Module.finrank (ZMod p) (ggFixedSubmodule (p := p) ι (ggAutomizer J Bs)) = 3 := by
  classical
  have hdiagJ : ∀ i : {i : Λ // i ∉ S}, αL i (hL i) = 2 := by
    intro i
    rw [hpairL i i, hCL.1 i]
    norm_num
  have hker := ggFixedSubmodule_pi_ker (p := p) (Λ := Λ) (S := S) (E := ↥Bs) (V := V)
    ι (fun i : {i : Λ // i ∉ S} => φL i) (fun i => hL i) (fun i => αL i)
    (fun i w => hlinL i w) hdiagJ hp2 (ggAutomizer J Bs) hgenJ
  have hle := finrank_le_card_add_finrank_ker_pi (p := p) (Λ := Λ) (S := S) (V := V)
    (fun i : {i : Λ // i ∉ S} => αL i)
  rw [hker] at hle
  have hsub : Fintype.card {i : Λ // i ∈ S} = S.card := by
    rw [Fintype.card_subtype]
    simp
  have hcomp : Fintype.card {i : Λ // i ∉ S} = Fintype.card Λ - S.card := by
    rw [Fintype.card_subtype_compl (fun i : Λ => i ∈ S), hsub]
  have hSle : S.card ≤ Fintype.card Λ := S.card_le_univ
  rw [hcomp, hS] at hle
  omega

theorem ggResExact2_finrank_eq_card_add_one_of_L {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {S : Finset Λ}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ι : Additive ↥Bs ≃+ V)
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ} (hCL : GGIntCartan ML CL)
    (φL : Λ → MulAut ↥Bs) (hL : Λ → V) (αL : Λ → Module.Dual (ZMod p) V)
    (hlinL : ∀ i w, ggLin (p := p) ι (φL i) w = w - αL i w • hL i)
    (hpairL : ∀ i j, αL i (hL j) = (CL i j : ZMod p))
    (hgenL : ggAutomizer L Bs = Subgroup.closure (Set.range φL))
    (hS : S.card = 2)
    (hgenJ : ggAutomizer J Bs =
      Subgroup.closure (Set.range (fun i : {i : Λ // i ∉ S} => φL i)))
    (hfixJ : ∀ b : ↥Bs,
      (∀ φ ∈ ggAutomizer J Bs, φ b = b) ↔
        (b : G) ∈ Subgroup.centralizer (J : Set G))
    (hrank : Matrix.rank (CL.map (Int.castRingHom (ZMod p))) = Fintype.card Λ) :
    Module.finrank (ZMod p) V = Fintype.card Λ + 1 := by
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hfixle := ggResExact2_fix_le_three hH hfixJ ι
  have hdimle := ggResExact2_finrank_le_card_add_one hp2 ι hCL φL hL αL hlinL hpairL
    hS hgenJ hfixle
  have haxis := ggResL_rank_core_add_one hH hlinL hpairL hCL.1 hgenL
  rw [hrank] at haxis
  omega

theorem ggResExact2_finrank_eq_card_add_one_of_K_base {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {S : Finset Λ}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ι : Additive ↥Bs ≃+ V)
    {MK : CoxeterMatrix Λ} {CK : Matrix Λ Λ ℤ} (hCK : GGIntCartan MK CK)
    (φK : Λ → MulAut ↥Bs) (hK : Λ → V) (αK : Λ → Module.Dual (ZMod p) V)
    (hlinK : ∀ i w, ggLin (p := p) ι (φK i) w = w - αK i w • hK i)
    (hpairK : ∀ i j, αK i (hK j) = (CK i j : ZMod p))
    (hgenK : ggAutomizer K Bs = Subgroup.closure (Set.range φK))
    (hS : S.card = 2)
    (hgenJ : ggAutomizer J Bs =
      Subgroup.closure (Set.range (fun i : {i : Λ // i ∉ S} => φK i)))
    (hfixJ : ∀ b : ↥Bs,
      (∀ φ ∈ ggAutomizer J Bs, φ b = b) ↔
        (b : G) ∈ Subgroup.centralizer (J : Set G))
    (hrank : Matrix.rank (CK.map (Int.castRingHom (ZMod p))) = Fintype.card Λ) :
    Module.finrank (ZMod p) V = Fintype.card Λ + 1 := by
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hfixle := ggResExact2_fix_le_three hH hfixJ ι
  have hdimle := ggResExact2_finrank_le_card_add_one hp2 ι hCK φK hK αK hlinK hpairK
    hS hgenJ hfixle
  have haxis := ggResK_rank_core_add_one hH hlinK hpairK hCK.1 hgenK
  rw [hrank] at haxis
  omega

theorem ggResExact2_fix_eq_three_of_L {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {S : Finset Λ}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ι : Additive ↥Bs ≃+ V)
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ} (hCL : GGIntCartan ML CL)
    (φL : Λ → MulAut ↥Bs) (hL : Λ → V) (αL : Λ → Module.Dual (ZMod p) V)
    (hlinL : ∀ i w, ggLin (p := p) ι (φL i) w = w - αL i w • hL i)
    (hpairL : ∀ i j, αL i (hL j) = (CL i j : ZMod p))
    (hgenL : ggAutomizer L Bs = Subgroup.closure (Set.range φL))
    (hS : S.card = 2)
    (hgenJ : ggAutomizer J Bs =
      Subgroup.closure (Set.range (fun i : {i : Λ // i ∉ S} => φL i)))
    (hfixJ : ∀ b : ↥Bs,
      (∀ φ ∈ ggAutomizer J Bs, φ b = b) ↔
        (b : G) ∈ Subgroup.centralizer (J : Set G))
    (hrank : Matrix.rank (CL.map (Int.castRingHom (ZMod p))) = Fintype.card Λ) :
    Module.finrank (ZMod p) (ggFixedSubmodule (p := p) ι (ggAutomizer J Bs)) = 3 := by
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hdim := ggResExact2_finrank_eq_card_add_one_of_L hH ι hCL φL hL αL hlinL hpairL
    hgenL hS hgenJ hfixJ hrank
  exact ggResExact2_fix_eq_three_of_finrank_eq_card_add_one hp2 ι hCL φL hL αL hlinL hpairL
    hS hgenJ hdim (ggResExact2_fix_le_three hH hfixJ ι)

theorem ggResExact2_fix_eq_three_of_K_base {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {S : Finset Λ}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ι : Additive ↥Bs ≃+ V)
    {MK : CoxeterMatrix Λ} {CK : Matrix Λ Λ ℤ} (hCK : GGIntCartan MK CK)
    (φK : Λ → MulAut ↥Bs) (hK : Λ → V) (αK : Λ → Module.Dual (ZMod p) V)
    (hlinK : ∀ i w, ggLin (p := p) ι (φK i) w = w - αK i w • hK i)
    (hpairK : ∀ i j, αK i (hK j) = (CK i j : ZMod p))
    (hgenK : ggAutomizer K Bs = Subgroup.closure (Set.range φK))
    (hS : S.card = 2)
    (hgenJ : ggAutomizer J Bs =
      Subgroup.closure (Set.range (fun i : {i : Λ // i ∉ S} => φK i)))
    (hfixJ : ∀ b : ↥Bs,
      (∀ φ ∈ ggAutomizer J Bs, φ b = b) ↔
        (b : G) ∈ Subgroup.centralizer (J : Set G))
    (hrank : Matrix.rank (CK.map (Int.castRingHom (ZMod p))) = Fintype.card Λ) :
    Module.finrank (ZMod p) (ggFixedSubmodule (p := p) ι (ggAutomizer J Bs)) = 3 := by
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hdim := ggResExact2_finrank_eq_card_add_one_of_K_base hH ι hCK φK hK αK hlinK hpairK
    hgenK hS hgenJ hfixJ hrank
  exact ggResExact2_fix_eq_three_of_finrank_eq_card_add_one hp2 ι hCK φK hK αK hlinK hpairK
    hS hgenJ hdim (ggResExact2_fix_le_three hH hfixJ ι)

theorem ggResExact2_centralizer_J_card_eq_pow_three_of_fix_eq_three {G : Type} [Group G]
    [Finite G] {p : ℕ} [Fact p.Prime] {Bs J : Subgroup G}
    (hfixJ : ∀ b : ↥Bs,
      (∀ φ ∈ ggAutomizer J Bs, φ b = b) ↔
        (b : G) ∈ Subgroup.centralizer (J : Set G))
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ι : Additive ↥Bs ≃+ V)
    (hfix3 : Module.finrank (ZMod p) (ggFixedSubmodule (p := p) ι (ggAutomizer J Bs)) = 3) :
    Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) = p ^ 3 := by
  classical
  let C : Subgroup G := Bs ⊓ Subgroup.centralizer (J : Set G)
  let D' : Subgroup ↥Bs := C.subgroupOf Bs
  have hfixC : ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer J Bs, φ b = b) ↔ b ∈ D' := by
    intro b
    rw [hfixJ b, Subgroup.mem_subgroupOf]
    exact ⟨fun h => ⟨b.2, h⟩, fun h => h.2⟩
  have hcardW : Nat.card ↥(ggFixedSubmodule (p := p) ι (ggAutomizer J Bs)) = Nat.card D' :=
    card_fixedSubmodule_eq_card_of_fix_eq ι (ggAutomizer J Bs) D' hfixC
  have hpow : Nat.card ↥(ggFixedSubmodule (p := p) ι (ggAutomizer J Bs)) =
      p ^ Module.finrank (ZMod p) (ggFixedSubmodule (p := p) ι (ggAutomizer J Bs)) := by
    let : Module.Finite (ZMod p) ↥(ggFixedSubmodule (p := p) ι (ggAutomizer J Bs)) :=
      Module.Finite.of_finite
    simpa using (Module.natCard_eq_pow_finrank (K := ZMod p)
      (V := ↥(ggFixedSubmodule (p := p) ι (ggAutomizer J Bs))))
  have hcardD' : Nat.card D' = p ^ 3 := by
    rw [← hcardW, hpow, hfix3]
  have hcardC : Nat.card C = Nat.card D' :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv).symm
  rw [hcardC, hcardD']

theorem ggResExact2_D_lt_centralizer_J_of_card_eq_pow_three {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hcardC : Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) = p ^ 3) :
    D < Bs ⊓ Subgroup.centralizer (J : Set G) := by
  let C : Subgroup G := Bs ⊓ Subgroup.centralizer (J : Set G)
  have hD : D = B ⊓ Subgroup.centralizer (J : Set G) := hH.1.2.2.1.2.2.2.2.2.2
  have hBBs : B ≤ Bs := hH.1.2.1.1
  have hle : D ≤ C := by
    rw [hD]
    exact inf_le_inf hBBs le_rfl
  have hcardD : Nat.card D = p ^ 2 := hH.1.2.2.1.2.2.1
  have hlt : Nat.card D < Nat.card C := by
    rw [hcardD, hcardC]
    exact Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt (by norm_num)
  exact lt_of_le_of_ne hle
    (fun h => (ne_of_lt hlt) (congrArg (fun H : Subgroup G => Nat.card ↥H) h))


theorem rank_map_eq_card_of_det_ne_zero {p : ℕ} [Fact p.Prime] {Λ : Type} [Fintype Λ]
    [DecidableEq Λ] {C : Matrix Λ Λ ℤ} (hdet : (C.det : ZMod p) ≠ 0) :
    Matrix.rank (C.map (Int.castRingHom (ZMod p))) = Fintype.card Λ := by
  apply Matrix.rank_of_det_ne_zero
  simpa [Int.cast_det] using hdet

theorem ggResExact2_finrank_eq_card_add_one_of_L_of_det {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {S : Finset Λ}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ι : Additive ↥Bs ≃+ V)
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ} (hCL : GGIntCartan ML CL)
    (φL : Λ → MulAut ↥Bs) (hL : Λ → V) (αL : Λ → Module.Dual (ZMod p) V)
    (hlinL : ∀ i w, ggLin (p := p) ι (φL i) w = w - αL i w • hL i)
    (hpairL : ∀ i j, αL i (hL j) = (CL i j : ZMod p))
    (hgenL : ggAutomizer L Bs = Subgroup.closure (Set.range φL))
    (hS : S.card = 2)
    (hgenJ : ggAutomizer J Bs =
      Subgroup.closure (Set.range (fun i : {i : Λ // i ∉ S} => φL i)))
    (hfixJ : ∀ b : ↥Bs,
      (∀ φ ∈ ggAutomizer J Bs, φ b = b) ↔
        (b : G) ∈ Subgroup.centralizer (J : Set G))
    (hdet : (CL.det : ZMod p) ≠ 0) :
    Module.finrank (ZMod p) V = Fintype.card Λ + 1 :=
  ggResExact2_finrank_eq_card_add_one_of_L hH ι hCL φL hL αL hlinL hpairL hgenL hS hgenJ
    hfixJ (rank_map_eq_card_of_det_ne_zero hdet)

theorem ggResExact2_finrank_eq_card_add_one_of_K_base_of_det {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {S : Finset Λ}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ι : Additive ↥Bs ≃+ V)
    {MK : CoxeterMatrix Λ} {CK : Matrix Λ Λ ℤ} (hCK : GGIntCartan MK CK)
    (φK : Λ → MulAut ↥Bs) (hK : Λ → V) (αK : Λ → Module.Dual (ZMod p) V)
    (hlinK : ∀ i w, ggLin (p := p) ι (φK i) w = w - αK i w • hK i)
    (hpairK : ∀ i j, αK i (hK j) = (CK i j : ZMod p))
    (hgenK : ggAutomizer K Bs = Subgroup.closure (Set.range φK))
    (hS : S.card = 2)
    (hgenJ : ggAutomizer J Bs =
      Subgroup.closure (Set.range (fun i : {i : Λ // i ∉ S} => φK i)))
    (hfixJ : ∀ b : ↥Bs,
      (∀ φ ∈ ggAutomizer J Bs, φ b = b) ↔
        (b : G) ∈ Subgroup.centralizer (J : Set G))
    (hdet : (CK.det : ZMod p) ≠ 0) :
    Module.finrank (ZMod p) V = Fintype.card Λ + 1 :=
  ggResExact2_finrank_eq_card_add_one_of_K_base hH ι hCK φK hK αK hlinK hpairK hgenK hS hgenJ
    hfixJ (rank_map_eq_card_of_det_ne_zero hdet)

theorem ggResExact2_nonI1_L_of_det {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {S : Finset Λ}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ι : Additive ↥Bs ≃+ V)
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ} (hCL : GGIntCartan ML CL)
    (φL : Λ → MulAut ↥Bs) (hL : Λ → V) (αL : Λ → Module.Dual (ZMod p) V)
    (hlinL : ∀ i w, ggLin (p := p) ι (φL i) w = w - αL i w • hL i)
    (hpairL : ∀ i j, αL i (hL j) = (CL i j : ZMod p))
    (hgenL : ggAutomizer L Bs = Subgroup.closure (Set.range φL))
    (hS : S.card = 2)
    (hgenJ : ggAutomizer J Bs =
      Subgroup.closure (Set.range (fun i : {i : Λ // i ∉ S} => φL i)))
    (hfixJ : ∀ b : ↥Bs,
      (∀ φ ∈ ggAutomizer J Bs, φ b = b) ↔
        (b : G) ∈ Subgroup.centralizer (J : Set G))
    (hdet : (CL.det : ZMod p) ≠ 0) :
    Module.finrank (ZMod p) V = Fintype.card Λ + 1 ∧
      Module.finrank (ZMod p) (ggFixedSubmodule (p := p) ι (ggAutomizer J Bs)) = 3 ∧
      Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) = p ^ 3 ∧
      D < Bs ⊓ Subgroup.centralizer (J : Set G) := by
  have hdim := ggResExact2_finrank_eq_card_add_one_of_L_of_det hH ι hCL φL hL αL hlinL hpairL
    hgenL hS hgenJ hfixJ hdet
  have hfix3 := ggResExact2_fix_eq_three_of_L hH ι hCL φL hL αL hlinL hpairL hgenL hS hgenJ
    hfixJ (rank_map_eq_card_of_det_ne_zero hdet)
  have hcard := ggResExact2_centralizer_J_card_eq_pow_three_of_fix_eq_three hfixJ ι hfix3
  exact ⟨hdim, hfix3, hcard,
    ggResExact2_D_lt_centralizer_J_of_card_eq_pow_three hH hcard⟩

theorem ggResExact2_nonI1_K_base_of_det {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {S : Finset Λ}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ι : Additive ↥Bs ≃+ V)
    {MK : CoxeterMatrix Λ} {CK : Matrix Λ Λ ℤ} (hCK : GGIntCartan MK CK)
    (φK : Λ → MulAut ↥Bs) (hK : Λ → V) (αK : Λ → Module.Dual (ZMod p) V)
    (hlinK : ∀ i w, ggLin (p := p) ι (φK i) w = w - αK i w • hK i)
    (hpairK : ∀ i j, αK i (hK j) = (CK i j : ZMod p))
    (hgenK : ggAutomizer K Bs = Subgroup.closure (Set.range φK))
    (hS : S.card = 2)
    (hgenJ : ggAutomizer J Bs =
      Subgroup.closure (Set.range (fun i : {i : Λ // i ∉ S} => φK i)))
    (hfixJ : ∀ b : ↥Bs,
      (∀ φ ∈ ggAutomizer J Bs, φ b = b) ↔
        (b : G) ∈ Subgroup.centralizer (J : Set G))
    (hdet : (CK.det : ZMod p) ≠ 0) :
    Module.finrank (ZMod p) V = Fintype.card Λ + 1 ∧
      Module.finrank (ZMod p) (ggFixedSubmodule (p := p) ι (ggAutomizer J Bs)) = 3 ∧
      Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) = p ^ 3 ∧
      D < Bs ⊓ Subgroup.centralizer (J : Set G) := by
  have hdim := ggResExact2_finrank_eq_card_add_one_of_K_base_of_det hH ι hCK φK hK αK hlinK
    hpairK hgenK hS hgenJ hfixJ hdet
  have hfix3 := ggResExact2_fix_eq_three_of_K_base hH ι hCK φK hK αK hlinK hpairK hgenK hS
    hgenJ hfixJ (rank_map_eq_card_of_det_ne_zero hdet)
  have hcard := ggResExact2_centralizer_J_card_eq_pow_three_of_fix_eq_three hfixJ ι hfix3
  exact ⟨hdim, hfix3, hcard,
    ggResExact2_D_lt_centralizer_J_of_card_eq_pow_three hH hcard⟩


theorem ggResExact3_typed_dichotomy_L_of_fixed
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hfwd : ∀ b : ↥Bs, (∀ a ∈ ggAutomizer J Bs, a b = b) →
      (b : G) ∈ Subgroup.centralizer (J : Set G))
    (hD : GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny) :
    (GGResLeviDatumExact3 p Bs L J K ggSelAny (ggTypLADvd p) ∨
      (p = 3 ∧ GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypLE6)) ∧
      Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) = p ^ 3 := by
  classical
  obtain ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    hS3, hA1, hA3, hWML, hCLL, hWMK, hCKK, htyp, hlin, hrefl, hpairL, hpairK, hsel,
    ⟨fL, hfL⟩, ⟨fK, hfK⟩, hclosL, hclosK, hdel, hclosJ⟩ := hD
  let := i1
  let := i2
  let := i3
  let := i4
  let := i5
  let := i6
  have haxis := ggResL_rank_core_add_one hH
    (fun i w => hlin (Sum.inl i) w) hpairL hCLL.1 hclosL
  obtain ⟨-, -, -, hsing, hcent, -⟩ := ggRes_exactThree_singular_chart_of_axis_bound hH.1 ι
    (fun i => φ (Sum.inl i)) (fun i => h (Sum.inl i)) (fun i => α (Sum.inl i))
    hWML hCLL (fun i w => hlin (Sum.inl i) w) (fun i => hrefl (Sum.inl i)) hpairL
    haxis S hS3 hclosJ hfwd
  refine ⟨?_, hcent⟩
  let pack : ∀ (typ : ∀ {Λ Λ' : Type},
      CoxeterMatrix Λ → CoxeterMatrix Λ' → Prop),
      typ ML MK → GGResLeviDatumExact3 p Bs L J K ggSelAny typ :=
    fun typ htyp => ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
      hS3, hA1, hA3, hWML, hCLL, hWMK, hCKK, htyp, hlin, hrefl, hpairL, hpairK, hsel,
      ⟨fL, hfL⟩, ⟨fK, hfK⟩, hclosL, hclosK, hdel, hclosJ⟩
  rcases hsing with ⟨hA, hpd⟩ | ⟨hp3, hE6⟩
  · exact Or.inl (pack (ggTypLADvd p)
      ⟨hA, by simpa [Nat.card_eq_fintype_card] using hpd⟩)
  · exact Or.inr ⟨hp3, pack ggTypLE6 hE6⟩

theorem ggResExact3_typed_dichotomy_K_base_of_fixed
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hfwd : ∀ b : ↥Bs, (∀ a ∈ ggAutomizer J Bs, a b = b) →
      (b : G) ∈ Subgroup.centralizer (J : Set G))
    (hD : GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny) :
    (GGResLeviDatumExact3 p Bs K J L ggSelAny (ggTypLADvd p) ∨
      (p = 3 ∧ GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypLE6)) ∧
      Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) = p ^ 3 := by
  classical
  obtain ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    hS3, hA1, hA3, hWML, hCLL, hWMK, hCKK, htyp, hlin, hrefl, hpairL, hpairK, hsel,
    ⟨fL, hfL⟩, ⟨fK, hfK⟩, hclosL, hclosK, hdel, hclosJ⟩ := hD
  let := i1
  let := i2
  let := i3
  let := i4
  let := i5
  let := i6
  have haxis := ggResK_rank_core_add_one hH
    (fun i w => hlin (Sum.inl i) w) hpairL hCLL.1 hclosL
  obtain ⟨-, -, -, hsing, hcent, -⟩ := ggRes_exactThree_singular_chart_of_axis_bound hH.1 ι
    (fun i => φ (Sum.inl i)) (fun i => h (Sum.inl i)) (fun i => α (Sum.inl i))
    hWML hCLL (fun i w => hlin (Sum.inl i) w) (fun i => hrefl (Sum.inl i)) hpairL
    haxis S hS3 hclosJ hfwd
  refine ⟨?_, hcent⟩
  let pack : ∀ (typ : ∀ {Λ Λ' : Type},
      CoxeterMatrix Λ → CoxeterMatrix Λ' → Prop),
      typ ML MK → GGResLeviDatumExact3 p Bs K J L ggSelAny typ :=
    fun typ htyp => ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
      hS3, hA1, hA3, hWML, hCLL, hWMK, hCKK, htyp, hlin, hrefl, hpairL, hpairK, hsel,
      ⟨fL, hfL⟩, ⟨fK, hfK⟩, hclosL, hclosK, hdel, hclosJ⟩
  rcases hsing with ⟨hA, hpd⟩ | ⟨hp3, hE6⟩
  · exact Or.inl (pack (ggTypLADvd p)
      ⟨hA, by simpa [Nat.card_eq_fintype_card] using hpd⟩)
  · exact Or.inr ⟨hp3, pack ggTypLE6 hE6⟩


theorem GGConfig.centralizer_inter_eq_D_of_typeA_marking
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J)
    (hL : GGInnerDiagOnLabel (fun p lab => lab.tag = .A ∧ p ∣ 2 ^ lab.n - 1) p Bs L) :
    Bs ⊓ Subgroup.centralizer (J : Set G) = D := by
  obtain ⟨hperf, lab, hlab, hraw⟩ := hL
  have hBle : B ≤ Bs := hcfg.2.1.1
  have hmark : LargeEvenMarking L (fun lab R _ I F θ =>
      GGTypeASplitLabel p lab ∧ LargeEvenSplit p lab ∧
        B ≤ Subgroup.normalizer (L : Set G) ∧
        ∀ b ∈ B, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' : ↥L => (l' : G) = b⁻¹ * l * b) φ) := by
    refine ⟨hperf, lab, hlab, ?_⟩
    apply largeEvenRawDatum_mono (Q' := fun R _ I F =>
      IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
        ∃ θ : ↥L ⧸ Subgroup.center ↥L ≃* R,
          GGTypeASplitLabel p lab ∧ LargeEvenSplit p lab ∧
            B ≤ Subgroup.normalizer (L : Set G) ∧
            ∀ b ∈ B, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' : ↥L => (l' : G) = b⁻¹ * l * b) φ) ?_ hraw
    rintro R _ I F hq
    obtain ⟨hsimple, hnab, θ, hP⟩ := hq
    obtain ⟨hA, hN, hact⟩ := hP
    obtain ⟨htag, hpn⟩ := hA
    have hsplit : LargeEvenSplit p lab := by
      refine Or.inl ⟨?_, hpn⟩
      rw [htag]
      trivial
    have htype : GGTypeASplitLabel p lab := by
      by_cases hdvd : p ∣ lab.rank + 1
      · exact Or.inr ⟨htag, hpn, hdvd⟩
      · exact Or.inl (Or.inl ⟨htag, hpn, hdvd⟩)
    refine ⟨hsimple, hnab, θ, ?_⟩
    refine ⟨htype, hsplit, hBle.trans hN, ?_⟩
    intro b hb
    exact hact b (hBle hb)
  exact (GGStdSubFixedJOn_typeA_split G p B Bs x L D J hcfg hmark).1

theorem GGResHyp.fix_mem_centralizer_J_of_typeA_split_marking
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hL : GGInnerDiagOnLabel (fun p lab => lab.tag = .A ∧ p ∣ 2 ^ lab.n - 1) p Bs L) :
    ∀ b : Bs, (∀ a ∈ ggAutomizer J Bs, a b = b) →
      (b : G) ∈ Subgroup.centralizer (J : Set G) := by
  obtain ⟨hperf, lab, hlab, hraw⟩ := hL
  obtain ⟨R, _, I, F, _, _, θ, hpred, _, _⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨htag, hpq⟩ := hpred
  have hlabeq : lab = ⟨.A, lab.rank, lab.n⟩ := by
    cases lab
    simp_all
  have hmark : GGInnerDiagOnLabel
      (fun _ lab' => lab' = ⟨.A, lab.rank, lab.n⟩) p Bs L := by
    refine ⟨hperf, lab, hlab, ?_⟩
    exact largeEvenRawDatum_mono (fun R _ I F hq => by
      obtain ⟨hs, hn, θ, _, hN, hact⟩ := hq
      exact ⟨hs, hn, θ, hlabeq, hN, hact⟩) hraw
  exact hH.fix_mem_centralizer_J_of_typeA_marking hpq hmark

theorem ggResExactThree_absurd_of_typeA_split_L_marking
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hL : GGInnerDiagOnLabel (fun p lab => lab.tag = .A ∧ p ∣ 2 ^ lab.n - 1) p Bs L)
    (hD : GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny ∨
      GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny) : False := by
  have hfwd := hH.fix_mem_centralizer_J_of_typeA_split_marking hL
  have hcent : Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) = p ^ 3 := by
    rcases hD with hD | hD
    · exact (ggResExact3_typed_dichotomy_L_of_fixed hH hfwd hD).2
    · exact (ggResExact3_typed_dichotomy_K_base_of_fixed hH hfwd hD).2
  have hEq := hH.1.centralizer_inter_eq_D_of_typeA_marking hL
  have hDcard : Nat.card ↥D = p ^ 2 := hH.1.2.2.1.2.2.1
  rw [hEq, hDcard] at hcent
  have hlt : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt (by norm_num)
  omega


end CFSG.StandardType

end
