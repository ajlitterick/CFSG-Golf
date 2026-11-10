module

public import CFSG.Quasithin.Background.D36GluedL24
public import CFSG.Quasithin.Background.RealizesFaithful

public section

namespace CFSG.Quasithin

open Matrix CFSG.Open

section LinAlg

variable {K : Type} [Field K]


end LinAlg

section Coords

variable {V : Type} [CommGroup V] {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
  {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)} {H : Subgroup (MulAut V)} {U Z : Subgroup V}

theorem natural_section_coords {π : ↥Γ →* ↥H} (h : (FFModel.nat Γ).RealizesVia H U Z π) :
    ∃ φ : ↥U →* Multiplicative (ι → K), Function.Surjective φ ∧
      (∀ u : ↥U, φ u = 1 ↔ (u : V) ∈ Z) ∧
      ∀ (γ : ↥Γ) (u : ↥U) (hu : ((π γ : ↥H) : MulAut V) (u : V) ∈ U),
        φ ⟨((π γ : ↥H) : MulAut V) (u : V), hu⟩ =
          Multiplicative.ofAdd (((γ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) *ᵥ
            Multiplicative.toAdd (φ u)) := by
  obtain ⟨hs, hZU, hker, hHU, hHZ, hsec, hkerinv, β, hβs, hβk, hβe⟩ := h
  let N := ((FFModel.nat Γ).ker).subgroupOf ((FFModel.nat Γ).sec)
  let e : (↥(FFModel.nat Γ).sec ⧸ N) →* Multiplicative (ι → K) :=
    QuotientGroup.lift N (Subgroup.subtype _) (by
      intro x hx
      have := Subgroup.mem_subgroupOf.mp hx
      exact Subgroup.mem_bot.mp this)
  have he : ∀ m : ↥(FFModel.nat Γ).sec,
      e (QuotientGroup.mk m) = ((m : (FFModel.nat Γ).Amb) : Multiplicative (ι → K)) :=
    fun m => rfl
  have heinj : ∀ q q' : (↥(FFModel.nat Γ).sec ⧸ N), e q = e q' → q = q' := by
    intro q q' hqq'
    induction q using QuotientGroup.induction_on with | H m => ?_
    induction q' using QuotientGroup.induction_on with | H m' => ?_
    rw [he, he] at hqq'
    have : m = m' := Subtype.ext hqq'
    rw [this]
  refine ⟨e.comp β, ?_, ?_, ?_⟩
  · intro a
    obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk ⟨a, trivial⟩)
    exact ⟨u, by simp [MonoidHom.comp_apply, hu, he]⟩
  · intro u
    constructor
    · intro hu
      have : β u = 1 := heinj _ _ (by simpa using hu)
      exact (hβk u).mp this
    · intro hu
      have := (hβk u).mpr hu
      simp [MonoidHom.comp_apply, this]
  · intro γ u hu
    have hm : (FFModel.nat Γ).act γ ((e (β u) : Multiplicative (ι → K))) ∈ (FFModel.nat Γ).sec :=
      trivial
    have hβu : β u = QuotientGroup.mk ⟨e (β u), trivial⟩ := by
      apply heinj
      rw [he]
    have h' := hβe γ u ⟨e (β u), trivial⟩ hu hm hβu
    exact (congrArg e h').trans (he _)

end Coords

theorem charTwo_of_card_four (K : Type) [Field K] [Finite K] (h : Nat.card K = 4) :
    CharP K 2 := by
  haveI := Fintype.ofFinite K
  obtain ⟨p, hp⟩ := CharP.exists K
  haveI := hp
  obtain ⟨n, hpp, hn⟩ := FiniteField.card K p
  have h4 : p ^ (n : ℕ) = 4 := by
    rw [← hn]
    simpa [Nat.card_eq_fintype_card] using h
  have hdvd : p ∣ 2 ^ 2 := by
    have : p ∣ p ^ (n : ℕ) := dvd_pow_self p n.ne_zero
    rw [h4] at this
    simpa using this
  have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp (hpp.dvd_of_dvd_pow hdvd)
  rw [hp2] at hp
  exact hp

section Data

variable {V : Type} [CommGroup V]

structure Nat24 (H : Subgroup (MulAut V)) (U Z : Subgroup V) (K : Type) [Field K] where
  M : ↥H → Matrix (Fin 2) (Fin 2) K
  φ : ↥U →* Multiplicative (Fin 2 → K)
  M_mul : ∀ a b, M (a * b) = M a * M b
  M_one : M 1 = 1
  M_inj : ∀ a b, M a = M b → a = b
  φ_surj : Function.Surjective φ
  φ_ker : ∀ u : ↥U, φ u = 1 ↔ (u : V) ∈ Z
  φ_act : ∀ (a : ↥H) (u : ↥U) (hu : (a : MulAut V) (u : V) ∈ U),
    φ ⟨(a : MulAut V) (u : V), hu⟩ =
      Multiplicative.ofAdd (M a *ᵥ Multiplicative.toAdd (φ u))
  H_U : ∀ a : ↥H, ∀ u ∈ U, (a : MulAut V) u ∈ U

variable {H : Subgroup (MulAut V)} {U Z : Subgroup V}

theorem natural24_data (h : BinaryNaturalSL H U Z 2 2) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 4 ∧ Z ≤ U ∧
      Nonempty (Nat24 H U Z K) := by
  obtain ⟨K, hK, hKfin, hcard, π₀, hπ₀⟩ := h
  obtain ⟨π, hπ⟩ : ∃ π : ↥(StatedSL 2 K) →* ↥H,
      (FFModel.nat (StatedSL 2 K)).RealizesVia H U Z π := ⟨π₀, hπ₀⟩
  have hcard4 : Nat.card K = 4 := by rw [hcard]; norm_num
  have hπinj : Function.Injective π :=
    FFModel.RealizesVia.injective_of_faithful_on (FFModel.nat_faithful _) hπ
  have hπsurj : Function.Surjective π := hπ.1
  have hHU : ∀ a : ↥H, ∀ u ∈ U, (a : MulAut V) u ∈ U := hπ.2.2.2.1
  obtain ⟨φ, hφs, hφk, hφe⟩ := natural_section_coords hπ
  refine ⟨K, hK, hKfin, charTwo_of_card_four K hcard4, hcard4, hπ.2.1, ⟨?_⟩⟩
  refine ⟨fun a => (((Function.surjInv hπsurj a : ↥(StatedSL 2 K)) :
      Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K), φ, ?_, ?_, ?_, hφs, hφk,
    ?_, hHU⟩
  · intro a b
    have h1 : Function.surjInv hπsurj (a * b) =
        Function.surjInv hπsurj a * Function.surjInv hπsurj b := by
      apply hπinj
      rw [map_mul, Function.surjInv_eq hπsurj, Function.surjInv_eq hπsurj,
        Function.surjInv_eq hπsurj]
    simp only [h1]
    rfl
  · have h1 : Function.surjInv hπsurj (1 : ↥H) = 1 := by
      apply hπinj
      rw [map_one, Function.surjInv_eq hπsurj]
    simp only [h1]
    rfl
  · intro a b hab
    have : Function.surjInv hπsurj a = Function.surjInv hπsurj b := by
      apply Subtype.ext
      apply Units.ext
      exact hab
    have h2 := congrArg π this
    rwa [Function.surjInv_eq hπsurj, Function.surjInv_eq hπsurj] at h2
  · intro a u hu
    have hπa : π (Function.surjInv hπsurj a) = a := Function.surjInv_eq hπsurj a
    have hu' : ((π (Function.surjInv hπsurj a) : ↥H) : MulAut V) (u : V) ∈ U := by
      rw [hπa]; exact hu
    have h1 := hφe (Function.surjInv hπsurj a) u hu'
    have h2 : (⟨((π (Function.surjInv hπsurj a) : ↥H) : MulAut V) (u : V), hu'⟩ : ↥U) =
        ⟨(a : MulAut V) (u : V), hu⟩ :=
      Subtype.ext (show ((π (Function.surjInv hπsurj a) : ↥H) : MulAut V) (u : V) =
        (a : MulAut V) (u : V) by rw [hπa])
    rw [h2] at h1
    exact h1

end Data

section Counting

variable {K : Type} [Field K] [Finite K]


end Counting

namespace Nat24

variable {V : Type} [CommGroup V] {H : Subgroup (MulAut V)} {U Z : Subgroup V} {K : Type}
  [Field K] (D : Nat24 H U Z K)

noncomputable def N (a : ↥H) : Matrix (Fin 2) (Fin 2) K := D.M a - 1


theorem key (a : ↥H) (u : ↥U) :
    (a : MulAut V) (u : V) * (u : V)⁻¹ ∈ Z ↔
      D.N a *ᵥ Multiplicative.toAdd (D.φ u) = 0 := by
  have hau : (a : MulAut V) (u : V) ∈ U := D.H_U a u u.2
  have h2 := D.φ_ker ⟨(a : MulAut V) (u : V) * (u : V)⁻¹, U.mul_mem hau (U.inv_mem u.2)⟩
  have h1 : (⟨(a : MulAut V) (u : V) * (u : V)⁻¹, U.mul_mem hau (U.inv_mem u.2)⟩ : ↥U) =
      ⟨(a : MulAut V) (u : V), hau⟩ * u⁻¹ := rfl
  rw [← h2, h1, map_mul, map_inv, D.φ_act a u hau, mul_inv_eq_one]
  unfold N
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero]
  constructor
  · intro h
    exact Multiplicative.ofAdd.injective h
  · intro h
    rw [h]
    rfl

end Nat24

namespace Nat24


end Nat24


end CFSG.Quasithin
