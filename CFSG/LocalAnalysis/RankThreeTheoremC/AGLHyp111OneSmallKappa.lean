module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111B3
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111StarAt
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseOne3AConfig

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.PreuniquenessRankFour.Helpers

section AutTwo

variable {K : Type} [Group K] [Finite K]

omit [Finite K] in
theorem mul_conj_mul_inv (f : MulAut K) (x : K) :
    f * MulAut.conj x * f⁻¹ = MulAut.conj (f x) := by
  ext y
  simp [MulAut.conj_apply]

omit [Finite K] in
theorem aut_twoGroup_eq_bot (hZ : Subgroup.center K = ⊥) {T : Subgroup K}
    (hNo2 : ∀ U : Subgroup K, IsPGroup 2 U → T ≤ Subgroup.normalizer (U : Set K) → U = ⊥)
    (hCent : ∀ V : Subgroup (MulAut K), IsPGroup 2 V → (∀ v ∈ V, ∀ t ∈ T, v t = t) → V = ⊥)
    (V : Subgroup (MulAut K)) (hV : IsPGroup 2 V)
    (hTV : ∀ t ∈ T, MulAut.conj t ∈ Subgroup.normalizer (V : Set (MulAut K))) : V = ⊥ := by
  have hinj : Function.Injective (MulAut.conj : K →* MulAut K) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxZ : x ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h := congrArg (fun f : MulAut K => f g) hx
      simp only [MulAut.conj_apply, MulAut.one_apply] at h
      calc g * x = (x * g * x⁻¹) * x := by rw [h]
        _ = x * g := by group
    rw [hZ, Subgroup.mem_bot] at hxZ
    exact hxZ
  set U : Subgroup K := V.comap (MulAut.conj : K →* MulAut K) with hUdef
  have hU2 : IsPGroup 2 U := hV.comap_of_injective _ hinj
  have hTU : T ≤ Subgroup.normalizer (U : Set K) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro u
    simp only [hUdef, Subgroup.mem_comap, map_mul, map_inv]
    exact Subgroup.mem_normalizer_iff.mp (hTV t ht) (MulAut.conj u)
  have hU := hNo2 U hU2 hTU
  refine hCent V hV fun v hv t ht => ?_
  have hc : v * MulAut.conj t * v⁻¹ * (MulAut.conj t)⁻¹ ∈ V := by
    have h1 : MulAut.conj t * v⁻¹ * (MulAut.conj t)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hTV t ht) v⁻¹).mp (V.inv_mem hv)
    have e : v * MulAut.conj t * v⁻¹ * (MulAut.conj t)⁻¹ =
        v * (MulAut.conj t * v⁻¹ * (MulAut.conj t)⁻¹) := by group
    rw [e]
    exact V.mul_mem hv h1
  have e2 : v * MulAut.conj t * v⁻¹ * (MulAut.conj t)⁻¹ = MulAut.conj (v t * t⁻¹) := by
    rw [map_mul, map_inv, mul_conj_mul_inv]
  rw [e2] at hc
  have hmem : v t * t⁻¹ ∈ U := hc
  rw [hU, Subgroup.mem_bot] at hmem
  exact mul_inv_eq_one.mp hmem

end AutTwo


variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}


@[expose] noncomputable def d1KBar (p : ℕ) (M H : Subgroup G) :
    Subgroup (H ⧸ primeComplementCore (G := H) p) :=
  ⨆ (L : Subgroup (H ⧸ primeComplementCore (G := H) p))
    (_ : IsComponentOf L ⊤ ∧ ¬ L ≤ d1X0 p M H), L

@[expose] noncomputable def d1Kappa (p : ℕ) (M H : Subgroup G) : ℕ := Nat.card (d1KBar p M H)

omit [Finite G] in
theorem le_d1KBar {L : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hL : IsComponentOf L ⊤)
    (hLX : ¬ L ≤ d1X0 p M H) : L ≤ d1KBar p M H :=
  le_iSup₂_of_le L ⟨hL, hLX⟩ le_rfl

omit [Finite G] in
theorem d1KBar_eq_of_unique {L₁ : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (h₁ : IsComponentOf L₁ ⊤) (hL₁ : ¬ L₁ ≤ d1X0 p M H)
    (huniq : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ →
      ¬ L ≤ d1X0 p M H → L = L₁) : d1KBar p M H = L₁ :=
  le_antisymm (iSup₂_le fun L hL => (huniq L hL.1 hL.2).le) (le_d1KBar h₁ hL₁)


end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
