module

public import CFSG.ClassicalInvolution.Asc77.AscT7AStep12
public import CFSG.ClassicalInvolution.Asc77.AscT7ASetup
public import CFSG.ClassicalInvolution.Asc77.AscT7AEStand
public import CFSG.ClassicalInvolution.Asc77.AscP1ThompsonTwelve

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson

namespace T7A

section Finite

open Equiv

def swaps4 : Finset (Perm (Fin 4)) :=
  {swap 0 1, swap 0 2, swap 0 3, swap 1 2, swap 1 3, swap 2 3}

def swaps3 : Finset (Perm (Fin 3)) := {swap 0 1, swap 0 2, swap 1 2}

theorem odd_inv_mem4 : ∀ d : Perm (Fin 4), d * d = 1 → d ≠ 1 → Perm.sign d = -1 → d ∈ swaps4 := by
  decide

theorem even_inv_not_comm4 : ∀ d : Perm (Fin 4), d * d = 1 → d ≠ 1 → Perm.sign d = 1 →
    ∃ s ∈ swaps4, s * d ≠ d * s ∧ (s * d) ^ 3 ≠ 1 := by
  decide

theorem swaps_conj4 : ∀ s ∈ swaps4, ∀ s' ∈ swaps4, ∃ g : Perm (Fin 4), g * s * g⁻¹ = s' := by
  decide

theorem no_three_swaps4 : ∀ a ∈ swaps4, ∀ b ∈ swaps4, ∀ c ∈ swaps4, a ≠ b → a ≠ c → b ≠ c →
    a * b = b * a → a * c = c * a → b * c = c * b → False := by
  decide

theorem inv_mem3 : ∀ d : Perm (Fin 3), d * d = 1 → d ≠ 1 → d ∈ swaps3 := by decide

theorem no_two_comm3 : ∀ a ∈ swaps3, ∀ b ∈ swaps3, a ≠ b → a * b ≠ b * a := by decide

theorem no_three_commuting_perm4 {Δ : Set (Perm (Fin 4))} (h : Star3T.IsTT Δ) :
    ∀ a ∈ Δ, ∀ b ∈ Δ, ∀ c ∈ Δ, a ≠ b → a ≠ c → b ≠ c → a * b = b * a → a * c = c * a →
      b * c = c * b → False := by
  have hsw : ∀ d ∈ Δ, Perm.sign d = -1 → d ∈ swaps4 := fun d hd hs =>
    odd_inv_mem4 d (h.mul_self d hd) (h.ne_one d hd) hs
  have hodd : ∃ d ∈ Δ, Perm.sign d = -1 := by
    by_contra hno
    push Not at hno
    have hle : Subgroup.closure Δ ≤ (Perm.sign : Perm (Fin 4) →* ℤˣ).ker := by
      rw [Subgroup.closure_le]
      intro d hd
      rw [SetLike.mem_coe, MonoidHom.mem_ker]
      rcases Int.units_eq_one_or (Perm.sign d) with h1 | h1
      · exact h1
      · exact absurd h1 (hno d hd)
    rw [h.closure_eq_top] at hle
    have := hle (Subgroup.mem_top (swap (0 : Fin 4) 1))
    rw [MonoidHom.mem_ker, Perm.sign_swap (by decide)] at this
    exact absurd this (by decide)
  obtain ⟨d₀, hd₀, hd₀s⟩ := hodd
  have hall : ∀ s ∈ swaps4, s ∈ Δ := fun s hs => by
    obtain ⟨g, hg⟩ := swaps_conj4 d₀ (hsw d₀ hd₀ hd₀s) s hs
    rw [← hg]
    exact h.conj_mem d₀ hd₀ g
  have hΔ : ∀ x ∈ Δ, x ∈ swaps4 := fun x hx => by
    rcases Int.units_eq_one_or (Perm.sign x) with h1 | h1
    · exfalso
      obtain ⟨s, hs, hsne, hs3⟩ := even_inv_not_comm4 x (h.mul_self x hx) (h.ne_one x hx) h1
      rcases h.comm_or_cube s (hall s hs) x hx with h2 | h2
      · exact hsne h2
      · exact hs3 h2
    · exact hsw x hx h1
  intro a ha b hb c hc hab hac hbc h1 h2 h3
  exact no_three_swaps4 a (hΔ a ha) b (hΔ b hb) c (hΔ c hc) hab hac hbc h1 h2 h3

theorem no_two_commuting_perm3 {Δ : Set (Perm (Fin 3))} (h : Star3T.IsTT Δ) :
    ∀ a ∈ Δ, ∀ b ∈ Δ, a ≠ b → a * b ≠ b * a := fun a ha b hb hab =>
  no_two_comm3 a (inv_mem3 a (h.mul_self a ha) (h.ne_one a ha)) b
    (inv_mem3 b (h.mul_self b hb) (h.ne_one b hb)) hab

end Finite

theorem isTT_map_equiv {Q Q' : Type*} [Group Q] [Group Q'] {Δ : Set Q} (h : Star3T.IsTT Δ)
    (e : Q ≃* Q') : Star3T.IsTT (e '' Δ) where
  mul_self := by
    rintro _ ⟨d, hd, rfl⟩
    rw [← map_mul, h.mul_self d hd, map_one]
  ne_one := by
    rintro _ ⟨d, hd, rfl⟩ h1
    exact h.ne_one d hd (e.injective (by rw [h1, map_one]))
  conj_mem := by
    rintro _ ⟨d, hd, rfl⟩ g
    refine ⟨e.symm g * d * (e.symm g)⁻¹, h.conj_mem d hd _, ?_⟩
    simp
  closure_eq_top := by
    have h1 : Subgroup.closure (e '' Δ) = (Subgroup.closure Δ).map e.toMonoidHom :=
      (MonoidHom.map_closure e.toMonoidHom Δ).symm
    rw [h1, h.closure_eq_top]
    exact Subgroup.map_top_of_surjective _ e.surjective
  comm_or_cube := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rcases h.comm_or_cube a ha b hb with h1 | h1
    · left
      rw [← map_mul, ← map_mul, h1]
    · right
      rw [← map_mul, ← map_pow, h1, map_one]

end T7A

section Members

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

omit [Finite G] in
theorem exists_muDelta_eq_piG {W R : Subgroup G} (hR : R ∈ DSet Ω W) {r : G} (hr : r ∈ R)
    (hrW : r ∉ W) : ∃ a ∈ muDelta Ω W, (a : NQuot (W ⊔ OCW W)) = piG W r :=
  ⟨⟨piG W r, piG_mem_muGroup (Subgroup.mem_sup_left (le_MGrp_of_mem_D hR hr))⟩,
    ⟨R, hR, r, hr, hrW, rfl⟩, rfl⟩

omit [Finite G] in
theorem muGroup_comm_of_comm {W R T : Subgroup G} (hR : R ∈ DSet Ω W) (hT : T ∈ DSet Ω W)
    {r t : G} (hr : r ∈ R) (ht : t ∈ T) (hrt : r * t = t * r) {a b : ↥(muGroup Ω W)}
    (ha : (a : NQuot (W ⊔ OCW W)) = piG W r) (hb : (b : NQuot (W ⊔ OCW W)) = piG W t) :
    a * b = b * a := by
  apply Subtype.ext
  show (a : NQuot (W ⊔ OCW W)) * b = b * a
  rw [ha, hb]
  refine (piG_comm_iff (hR.2 hr) (hT.2 ht)).mpr ?_
  have : r * t * r⁻¹ * t⁻¹ = 1 := by rw [hrt]; group
  rw [this]
  exact one_mem _

theorem piG_ne_of_ne_members (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {W : Subgroup G} (hW : W ∈ WSet Ω) {R T K J : Subgroup G} (hR : R ∈ DSet Ω W)
    (hT : T ∈ DSet Ω W) (hK : K ∈ Ω) (hJ : J ∈ Ω) (hRK : IsSylow2In R K) (hTJ : IsSylow2In T J)
    (hKJ : K ≠ J) {r t : G} (hr : r ∈ R) (ht : t ∈ T) (htW : t ∉ W) :
    piG W r ≠ piG W t := by
  intro heq
  have hTR : T ≤ R ⊔ W ⊔ OCW W :=
    le_sup_of_piG_eq hr hR.2 hT.2 fun x hx hxW =>
      (D_piG_eq hp hq hΩ hW hT hx ht hxW htW).trans heq.symm
  obtain ⟨M, hM, hRM, hTM⟩ := exists_member_of_D_same hp hq hΩ hW hR hT hTR
  have h8R := hΩ.eight_le_of_mem_RSet hp hR.1
  have h8T := hΩ.eight_le_of_mem_RSet hp hT.1
  have h1 : K = M := hΩ.eq_of_le_of_le hK hM hRK.2.1 (by omega) hRK.1 hRM
  have h2 : J = M := hΩ.eq_of_le_of_le hJ hM hTJ.2.1 (by omega) hTJ.1 hTM
  exact hKJ (h1.trans h2.symm)

end Members

section Exclude


end Exclude

end CFSG.ClassicalInvolution.Asc77
