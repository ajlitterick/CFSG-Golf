module

public import CFSG.Quasithin.EmptyFaithful.Der6AGen
public import CFSG.Quasithin.EmptyFaithful.S143Aux
public import CFSG.Quasithin.EmptyFaithful.S151Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace Der6A

variable {G : Type} [Group G]

theorem exists_mul_of_mem_sup_of_commute {U C : Subgroup G} (h : ∀ u ∈ U, ∀ c ∈ C, u * c = c * u)
    {x : G} (hx : x ∈ U ⊔ C) : ∃ u ∈ U, ∃ c ∈ C, u * c = x := by
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨x, hx, 1, C.one_mem, mul_one x⟩
    · exact ⟨1, U.one_mem, x, hx, one_mul x⟩
  | one => exact ⟨1, U.one_mem, 1, C.one_mem, mul_one 1⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨u₁, hu₁, c₁, hc₁, rfl⟩ := ihx
    obtain ⟨u₂, hu₂, c₂, hc₂, rfl⟩ := ihy
    refine ⟨u₁ * u₂, U.mul_mem hu₁ hu₂, c₁ * c₂, C.mul_mem hc₁ hc₂, ?_⟩
    have := h u₂ hu₂ c₁ hc₁
    calc u₁ * u₂ * (c₁ * c₂) = u₁ * (u₂ * c₁) * c₂ := by group
      _ = u₁ * (c₁ * u₂) * c₂ := by rw [this]
      _ = u₁ * c₁ * (u₂ * c₂) := by group
  | inv x _ ih =>
    obtain ⟨u, hu, c, hc, rfl⟩ := ih
    refine ⟨u⁻¹, U.inv_mem hu, c⁻¹, C.inv_mem hc, ?_⟩
    have := h u hu c hc
    calc u⁻¹ * c⁻¹ = (c * u)⁻¹ := by group
      _ = (u * c)⁻¹ := by rw [this]

theorem arith_A0 {a b u c f n : ℕ} (hb : 0 < b) (hu : 0 < u) (hf : 0 < f)
    (c1 : a ^ 2 * f = b ^ 2 * u) (c2 : u * c ^ 2 = b ^ 2 * f) (h0 : n * f = u * c) : n = a := by
  have h3 : (a * c) ^ 2 * (f * u) = (b ^ 2) ^ 2 * (f * u) := by
    have : a ^ 2 * f * (u * c ^ 2) = b ^ 2 * u * (b ^ 2 * f) := by rw [c1, c2]
    calc (a * c) ^ 2 * (f * u) = a ^ 2 * f * (u * c ^ 2) := by ring
      _ = b ^ 2 * u * (b ^ 2 * f) := this
      _ = (b ^ 2) ^ 2 * (f * u) := by ring
  have h4 : (a * c) ^ 2 = (b ^ 2) ^ 2 :=
    Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hf hu) h3
  have h5 : a * c = b ^ 2 := Nat.pow_left_injective (by norm_num : 2 ≠ 0) h4
  have h6 : n * (b ^ 2 * u) = a * (b ^ 2 * u) := by
    calc n * (b ^ 2 * u) = n * (a ^ 2 * f) := by rw [c1]
      _ = (n * f) * a ^ 2 := by ring
      _ = u * c * a ^ 2 := by rw [h0]
      _ = u * (a * c) * a := by ring
      _ = a * (b ^ 2 * u) := by rw [h5]; ring
  exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos (pow_pos hb 2) hu) h6

section Finite

variable [Finite G]

theorem inf_centralizer_eq_inf {T A W : Subgroup G} (hA : IsMaxElemAbelian T A) (hWT : W ≤ T)
    (hW : IsElemAbelian 2 W) :
    W ⊓ Subgroup.centralizer (A : Set G) = W ⊓ A := by
  apply le_antisymm
  · rintro w ⟨hwW, hwC⟩
    refine ⟨hwW, ?_⟩
    rw [eq_omegaOneOf_centralizer hA]
    exact Subgroup.subset_closure ⟨⟨hWT hwW, hwC⟩, hW.2 w hwW⟩
  · rintro w ⟨hwW, hwA⟩
    exact ⟨hwW, Subgroup.mem_centralizer_iff.mpr fun a ha => B2F.isElemAbelian_comm hA.2.1 ha hwA⟩

theorem exists_A0 {T A U P : Subgroup G} (hA : IsMaxElemAbelian T A) (hUP : U ≤ P) (hPT : P ≤ T)
    (hU : IsElemAbelian 2 U)
    (c1 : Nat.card A ^ 2 * Nat.card ↥(U ⊓ Subgroup.centralizer (A : Set G)) =
      Nat.card ↥(A ⊓ P) ^ 2 * Nat.card U)
    (c2 : Nat.card U * Nat.card ↥(A ⊓ P ⊓ Subgroup.centralizer (U : Set G)) ^ 2 =
      Nat.card ↥(A ⊓ P) ^ 2 * Nat.card ↥(U ⊓ Subgroup.centralizer (A : Set G))) :
    IsElemAbelian 2 (U ⊔ (A ⊓ P ⊓ Subgroup.centralizer (U : Set G))) ∧
      Nat.card ↥(U ⊔ (A ⊓ P ⊓ Subgroup.centralizer (U : Set G))) = Nat.card A := by
  set CB := A ⊓ P ⊓ Subgroup.centralizer (U : Set G) with hCB
  have hUA : U ⊓ Subgroup.centralizer (A : Set G) = U ⊓ A :=
    inf_centralizer_eq_inf hA (hUP.trans hPT) hU
  have hcomm : ∀ u ∈ U, ∀ c ∈ CB, u * c = c * u := fun u hu c hc =>
    Subgroup.mem_centralizer_iff.mp hc.2 u hu
  have hCBe : IsElemAbelian 2 CB := B2F.isElemAbelian_mono (inf_le_left.trans inf_le_left) hA.2.1
  refine ⟨B2F.isElemAbelian_sup_of_commute hU hCBe hcomm, ?_⟩
  have hprod := B2F.card_sup_mul_card_inf_of_commute hcomm
  have hinf : U ⊓ CB = U ⊓ A := by
    apply le_antisymm
    · rintro x ⟨hxU, hxC⟩
      exact ⟨hxU, hxC.1.1⟩
    · rintro x ⟨hxU, hxA⟩
      exact ⟨hxU, ⟨hxA, hUP hxU⟩, Subgroup.mem_centralizer_iff.mpr fun u hu =>
        B2F.isElemAbelian_comm hU hu hxU⟩
  rw [hinf] at hprod
  rw [hUA] at c1 c2
  exact arith_A0 Nat.card_pos Nat.card_pos Nat.card_pos c1 c2 hprod

theorem omegaOneCenter_J1_le_of_isMax {S A₀ : Subgroup G} (hS : 1 < CFSG.Open.pRank 2 S)
    (hA₀ : IsMaxElemAbelian S A₀) : omegaOneCenterOf (thompsonJi S 1) ≤ A₀ := by
  have h1 := (omegaOneCenterOf_thompsonJi_le (S := S) (i := 0) (j := 1) (Nat.zero_le 1) hS).1
  have h2 := omegaOne_centralizer_thompsonJ S
  rw [← thompsonJ_eq_thompsonJi_zero] at h1
  refine h1.trans ?_
  rw [h2.1, h2.2]
  exact iInf₂_le A₀ hA₀

theorem normalizer_le_normalizer_omegaOneCenter_J1 (S : Subgroup G) :
    Subgroup.normalizer (S : Set G) ≤
      Subgroup.normalizer (omegaOneCenterOf (thompsonJi S 1) : Set G) :=
  normalizer_le_normalizer_of_map_mulEquiv (F := fun Y => omegaOneCenterOf (thompsonJi Y 1))
    (fun φ Y => by rw [omegaOneCenterOf_map_mulEquiv, thompsonJi_map_mulEquiv151]) S

omit [Finite G] in
theorem normalizer_le_normalizer_centralizer (E : Subgroup G) :
    Subgroup.normalizer (E : Set G) ≤
      Subgroup.normalizer ((Subgroup.centralizer (E : Set G) : Subgroup G) : Set G) :=
  normalizer_le_normalizer_of_map_mulEquiv (F := fun Y => Subgroup.centralizer (Y : Set G))
    (fun φ Y => centralizer_map_mulEquiv φ Y) E

theorem oTwoUpper_le_centralizer_of_sup {H W T E : Subgroup G} (hH : H = W ⊔ T)
    (hT2 : IsPGroup 2 T) (hWC : W ≤ Subgroup.centralizer (E : Set G))
    (hTE : T ≤ Subgroup.normalizer (E : Set G)) :
    oTwoUpper H ≤ Subgroup.centralizer (E : Set G) := by
  have hHE : H ≤ Subgroup.normalizer (E : Set G) := by
    rw [hH]
    exact sup_le (hWC.trans (Subgroup.centralizer_le_normalizer _)) hTE
  have hHK := hHE.trans (normalizer_le_normalizer_centralizer E)
  have hWH : W ≤ H := hH ▸ le_sup_left
  have hTH : T ≤ H := hH ▸ le_sup_right
  have h := oTwoUpper_le_of_normal_sup (H := H) (N := H ⊓ Subgroup.centralizer (E : Set G))
    (S := T) inf_le_left
    ⟨fun x hx g => by
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact ⟨H.mul_mem (H.mul_mem g.2 hx.1) (H.inv_mem g.2),
        (Subgroup.mem_normalizer_iff.mp (hHK g.2) x).mp hx.2⟩⟩
    hT2 hTH (hH.le.trans (sup_le_sup (le_inf hWH hWC) le_rfl))
  exact h.trans inf_le_right

omit [Finite G] in
theorem omegaOneCenterOf_le_centralizer (Y : Subgroup G) :
    omegaOneCenterOf Y ≤ Subgroup.centralizer (Y : Set G) :=
  (Subgroup.closure_le _).mpr fun _ hx => hx.1.2

theorem omegaOneCenter_J1_le_J1 {S Q A₀ : Subgroup G} (hQS : Q ≤ S) (hrQ : CFSG.Open.pRank 2 Q = CFSG.Open.pRank 2 S)
    (hrQ1 : 1 < CFSG.Open.pRank 2 Q) (hEA₀ : omegaOneCenterOf (thompsonJi S 1) ≤ A₀)
    (hA₀Q : A₀ ≤ Q) :
    omegaOneCenterOf (thompsonJi S 1) ≤ omegaOneCenterOf (thompsonJi Q 1) := by
  have hJQS : thompsonJi Q 1 ≤ thompsonJi S 1 := by
    refine iSup₂_le fun B hB => ?_
    obtain ⟨hBQ, hBe, hBc⟩ := hB
    exact le_iSup₂_of_le (f := fun (B : Subgroup G) (_ : IsElemAbelianCorank S 1 B) => B) B
      ⟨hBQ.trans hQS, hBe, by rw [hBc, hrQ]⟩ le_rfl
  have hD' : omegaOneOf (Q ⊓ Subgroup.centralizer (thompsonJi Q 1 : Set G)) =
      omegaOneCenterOf (thompsonJi Q 1) :=
    (omegaOneCenterOf_thompsonJi_le (le_refl 1) hrQ1).2
  rw [← hD']
  refine (Subgroup.closure_le _).mpr fun x hx => ?_
  exact Subgroup.subset_closure ⟨⟨hA₀Q (hEA₀ (Subgroup.subset_closure hx)),
    Subgroup.centralizer_le hJQS hx.1.2⟩, hx.2⟩

omit [Finite G] in
theorem conj_mem_inf_centralizer {X D : Subgroup G} (hXD : X ≤ Subgroup.normalizer (D : Set G))
    {g n : G} (hg : g ∈ X) (hn : n ∈ X ⊓ Subgroup.centralizer (D : Set G)) :
    g * n * g⁻¹ ∈ X ⊓ Subgroup.centralizer (D : Set G) := by
  refine ⟨X.mul_mem (X.mul_mem hg hn.1) (X.inv_mem hg), Subgroup.mem_centralizer_iff.mpr ?_⟩
  intro d hd
  have hd' : g⁻¹ * d * g ∈ D := by
    have := (Subgroup.mem_normalizer_iff.mp (hXD (X.inv_mem hg)) d).mp hd
    simpa using this
  have h1 : g⁻¹ * d * g * n = n * (g⁻¹ * d * g) := Subgroup.mem_centralizer_iff.mp hn.2 _ hd'
  calc d * (g * n * g⁻¹) = g * (g⁻¹ * d * g * n) * g⁻¹ := by group
    _ = g * (n * (g⁻¹ * d * g)) * g⁻¹ := by rw [h1]
    _ = g * n * g⁻¹ * d := by group


end Finite

end Der6A

end CFSG.Quasithin
