module

public import CFSG.RankThree.PartOne.S12.Sec1511Y2Quot
public import CFSG.RankThree.PartOne.S12.Sec1511SPEFStar

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.ABGLocalTools StrongP

namespace Sec1511


@[expose] def KFL225 : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (S : Subgroup H), S.Normal →
    Subgroup.centralizer (S : Set H) = ⊥ →
    (∃ q : TauCeti.PrimePower, q.p = 5 ∧ q.exponent = 2 ∧ Census3.IsoLie ↥S (.A 1 q)) →
    ∀ Y₀ : Subgroup H, IsStronglyPEmbedded 5 Y₀ →
      ∀ P : Subgroup H, IsSylowOf 5 P ⊤ → IsElementaryAbelian 5 (omegaOne 5 P) →
        Nat.card (omegaOne 5 P) = 25 →
        Nat.card ↥P = 25 ∧
        (∀ V : Subgroup H, IsPGroup 2 ↥V →
          omegaOne 5 P ≤ Subgroup.normalizer (V : Set H) → V = ⊥) ∧
        Group.IsSolvable ↥Y₀ ∧
        ∃ g ∈ Subgroup.normalizer ((omegaOne 5 P : Subgroup H) : Set H), OrderModC (omegaOne 5 P) g 3

section Tools

@[expose] def HasNonabSimpleSection (q : ℕ) (X : Type) [Group X] : Prop :=
  ∃ (A : Subgroup X) (S : Type) (_ : Group S) (φ : ↥A →* S), Function.Surjective φ ∧ IsSimpleGroup S ∧
    (∃ a b : S, a * b ≠ b * a) ∧ q ∣ Nat.card S

theorem HasNonabSimpleSection.of_surjective {X Y : Type} [Group X] [Group Y] {q : ℕ} (π : X →* Y)
    (hπ : Function.Surjective π) (h : HasNonabSimpleSection q Y) : HasNonabSimpleSection q X := by
  obtain ⟨A, S, hSg, φ, hφ, hs, hn, hq⟩ := h
  let A' : Subgroup X := A.comap π
  let ψ : ↥A' →* ↥A := (π.comp A'.subtype).codRestrict A fun x => x.2
  have hψ : Function.Surjective ψ := fun y => by
    obtain ⟨x, hx⟩ := hπ (y : Y)
    exact ⟨⟨x, by simp [A', Subgroup.mem_comap, hx]⟩, Subtype.ext hx⟩
  exact ⟨A', S, hSg, φ.comp ψ, hφ.comp hψ, hs, hn, hq⟩

theorem HasNonabSimpleSection.of_injective {X Y : Type} [Group X] [Group Y] {q : ℕ} (ι : X →* Y)
    (hι : Function.Injective ι) (h : HasNonabSimpleSection q X) : HasNonabSimpleSection q Y := by
  obtain ⟨A, S, hSg, φ, hφ, hs, hn, hq⟩ := h
  let e : ↥A ≃* ↥(A.map ι) := A.equivMapOfInjective ι hι
  exact ⟨A.map ι, S, hSg, φ.comp e.symm.toMonoidHom, hφ.comp e.symm.surjective, hs, hn, hq⟩

theorem not_hasNonabSimpleSection {X Q : Type} [Group X] [Finite X] [Group Q] {q : ℕ} (f : X →* Q)
    (hQ : Group.IsSolvable Q) (hk : ¬ q ∣ Nat.card f.ker) : ¬ HasNonabSimpleSection q X := by
  rintro ⟨A, S, hSg, φ, hφ, hsimple, ⟨a, b, hab⟩, hq⟩
  classical
  let ψ : ↥A →* Q := f.comp A.subtype
  have hNn : ψ.ker.Normal := ψ.normal_ker
  have hmapN : (ψ.ker.map φ).Normal := Subgroup.Normal.map hNn φ hφ
  rcases hsimple.eq_bot_or_eq_top_of_normal (ψ.ker.map φ) with hbot | htop
  · have hle : ψ.ker ≤ φ.ker := (Subgroup.map_eq_bot_iff _).1 hbot
    let ρ : ↥A ⧸ ψ.ker →* S := QuotientGroup.lift ψ.ker φ hle
    have hρ : Function.Surjective ρ := fun y => by
      obtain ⟨x, rfl⟩ := hφ y
      exact ⟨(x : ↥A ⧸ ψ.ker), rfl⟩
    have hrange : Group.IsSolvable ↥ψ.range :=
      Group.isSolvable_of_isSolvable_injective (f := ψ.range.subtype) ψ.range.subtype_injective
    have h1 : Group.IsSolvable (↥A ⧸ ψ.ker) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (QuotientGroup.quotientKerEquivRange ψ).toMonoidHom)
        (QuotientGroup.quotientKerEquivRange ψ).injective
    have h2 : Group.IsSolvable S := Group.isSolvable_of_surjective hρ
    exact hab (IsSimpleGroup.comm_iff_isSolvable.2 h2 a b)
  · have hsurj : Function.Surjective (φ.comp ψ.ker.subtype) := fun y => by
      have hy : y ∈ ψ.ker.map φ := htop ▸ Subgroup.mem_top y
      obtain ⟨x, hx, rfl⟩ := hy
      exact ⟨⟨x, hx⟩, rfl⟩
    have h1 : Nat.card S ∣ Nat.card ψ.ker := Subgroup.card_dvd_of_surjective hsurj
    have hle2 : ψ.ker.map A.subtype ≤ f.ker := by
      rintro _ ⟨x, hx, rfl⟩
      exact hx
    have h2 : Nat.card ψ.ker ∣ Nat.card f.ker := by
      have := Subgroup.card_dvd_of_le hle2
      rwa [Subgroup.card_map_of_injective A.subtype_injective] at this
    exact hk (hq.trans (h1.trans h2))

theorem isKGroup_subgroup_quotient {A : Type} [Group A] (hA : CFSG.IsKGroup A) (O : Subgroup A)
    [O.Normal] (S : Subgroup (A ⧸ O)) : CFSG.IsKGroup ↥S :=
  (hA.quotient O).subgroup S

theorem map_mem_normalizer {G H : Type*} [Group G] [Group H] (f : G →* H) {A : Subgroup G} {n : G}
    (hn : n ∈ Subgroup.normalizer (A : Set G)) :
    f n ∈ Subgroup.normalizer ((A.map f : Subgroup H) : Set H) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨n * a * n⁻¹, (Subgroup.mem_normalizer_iff.1 hn a).1 ha, by simp⟩
  · rintro ⟨a, ha, hay⟩
    refine ⟨n⁻¹ * a * n, ?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer (A : Set G)).inv_mem hn) a).1 ha
      simpa using this
    · have h1 : f a = f n * y * (f n)⁻¹ := hay
      rw [map_mul, map_mul, map_inv, h1]
      group

end Tools

section Arith

theorem arith_l2sq {p m : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hm1 : 1 ≤ m) (hm4 : m ≤ 4)
    (h : (p ^ 2 - 1) / 2 ∣ Nat.lcm (p - 1) m) : p = 5 := by
  have hlcm : Nat.lcm (p - 1) m ≤ (p - 1) * m :=
    Nat.le_of_dvd (Nat.mul_pos (by omega) (by omega)) (Nat.lcm_dvd_mul _ _)
  have hlpos : 0 < Nat.lcm (p - 1) m := Nat.lcm_pos (by omega) (by omega)
  have hle : (p ^ 2 - 1) / 2 ≤ (p - 1) * m := (Nat.le_of_dvd hlpos h).trans hlcm
  have hp7 : p ≤ 7 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨a, rfl⟩ : ∃ a, p = a + 8 := ⟨p - 8, by omega⟩
    have h1 : (a + 8) ^ 2 - 1 = a ^ 2 + 16 * a + 63 := by
      have : (a + 8) ^ 2 = a ^ 2 + 16 * a + 64 := by ring
      omega
    have h2 : (a + 8 - 1) * m ≤ (a + 7) * 4 := by
      have : a + 8 - 1 = a + 7 := by omega
      rw [this]
      exact Nat.mul_le_mul_left _ hm4
    have h3 : (a ^ 2 + 16 * a + 63) / 2 ≤ (a + 7) * 4 := by
      rw [h1] at hle
      exact hle.trans h2
    omega
  interval_cases p
  · rfl
  · exact absurd hp (by norm_num)
  · exfalso
    interval_cases m <;> simp [Nat.lcm] at h

theorem arith_l2cube {p m : ℕ} (hp5 : 5 ≤ p) (hm1 : 1 ≤ m) (hm6 : m ≤ 6)
    (h : (p ^ 3 - 1) / 2 ∣ Nat.lcm (p - 1) m) : False := by
  have hlcm : Nat.lcm (p - 1) m ≤ (p - 1) * m :=
    Nat.le_of_dvd (Nat.mul_pos (by omega) (by omega)) (Nat.lcm_dvd_mul _ _)
  have hlpos : 0 < Nat.lcm (p - 1) m := Nat.lcm_pos (by omega) (by omega)
  have hle : (p ^ 3 - 1) / 2 ≤ (p - 1) * m := (Nat.le_of_dvd hlpos h).trans hlcm
  obtain ⟨a, rfl⟩ : ∃ a, p = a + 5 := ⟨p - 5, by omega⟩
  have h1 : (a + 5) ^ 3 - 1 = a ^ 3 + 15 * a ^ 2 + 75 * a + 124 := by
    have : (a + 5) ^ 3 = a ^ 3 + 15 * a ^ 2 + 75 * a + 125 := by ring
    omega
  have h2 : (a + 5 - 1) * m ≤ (a + 4) * 6 := by
    have : a + 5 - 1 = a + 4 := by omega
    rw [this]
    exact Nat.mul_le_mul_left _ hm6
  have h3 : (a ^ 3 + 15 * a ^ 2 + 75 * a + 124) / 2 ≤ (a + 4) * 6 := by
    rw [h1] at hle
    exact hle.trans h2
  omega

theorem arith_eight {m : ℕ} (hm1 : 1 ≤ m) (hm6 : m ≤ 6) (h : 8 ∣ Nat.lcm (5 - 1) m) : False := by
  interval_cases m <;> simp [Nat.lcm] at h

theorem arith_five {m : ℕ} (hm1 : 1 ≤ m) (hm4 : m ≤ 4) (h : 5 ∣ Nat.lcm (5 - 1) m) : False := by
  interval_cases m <;> simp [Nat.lcm] at h

end Arith

section Main

variable {M : Type} [Group M] [Finite M] {p : ℕ}

structure Y2Cfg (p : ℕ) (M₀ P B : Subgroup M) : Prop where
  prime : p.Prime
  p5 : 5 ≤ p
  syl : IsSylowOf p P ⊤
  omega : omegaOne p P = B
  Bel : IsElementaryAbelian p ↥B
  card : Nat.card ↥B = p ^ 2 ∨ Nat.card ↥B = p ^ 3
  spe : IsStronglyPEmbedded p M₀
  coprime : ∀ V : Subgroup M, V.Normal → ¬ p ∣ Nat.card ↥V → V ≤ M₀

structure Y2Aut (p : ℕ) (B : Subgroup M) : Prop where
  ord6 : ∀ n ∈ Subgroup.normalizer (B : Set M), ∃ m : ℕ, 1 ≤ m ∧ m ≤ 6 ∧
    n ^ Nat.lcm (p - 1) m ∈ Subgroup.centralizer (B : Set M)
  ord4 : Nat.card ↥B = p ^ 2 → ∀ n ∈ Subgroup.normalizer (B : Set M), ∃ m : ℕ, 1 ≤ m ∧ m ≤ 4 ∧
    n ^ Nat.lcm (p - 1) m ∈ Subgroup.centralizer (B : Set M)
  count : Nat.card ↥B = 25 → ∀ F : Finset M, (∀ x ∈ F, x ∈ Subgroup.normalizer (B : Set M)) →
    (∀ x ∈ F, ∀ y ∈ F, x ≠ y → x⁻¹ * y ∉ Subgroup.centralizer (B : Set M)) → F.card ≤ 32

structure L225Out (p : ℕ) (M₀ P B O : Subgroup M) : Prop where
  p5 : p = 5
  card : Nat.card ↥B = 25
  PB : P = B
  two : ∀ V : Subgroup M, IsPGroup 2 ↥V → B ≤ Subgroup.normalizer (V : Set M) → V ≤ O
  simple5 : ∃ (Q : Type) (_ : Group Q) (f : ↥M₀ →* Q), Group.IsSolvable Q ∧ ¬ 5 ∣ Nat.card f.ker
  three : ∃ n ∈ Subgroup.normalizer (B : Set M), OrderModC B n 3

theorem exists_dvd_lcm_of_orderModC [Fact p.Prime] {O : Subgroup M} [O.Normal] {B : Subgroup M}
    (hBp : IsPGroup p ↥B) (hO : ¬ p ∣ Nat.card O) {g : M ⧸ O}
    (hg : g ∈ Subgroup.normalizer ((B.map (QuotientGroup.mk' O) : Subgroup (M ⧸ O)) : Set (M ⧸ O)))
    {r : ℕ} (hr : OrderModC (B.map (QuotientGroup.mk' O)) g r) {M₁ : ℕ}
    (hn : ∀ n ∈ Subgroup.normalizer (B : Set M), ∃ m : ℕ, 1 ≤ m ∧ m ≤ M₁ ∧
      n ^ Nat.lcm (p - 1) m ∈ Subgroup.centralizer (B : Set M)) :
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ M₁ ∧ r ∣ Nat.lcm (p - 1) m := by
  obtain ⟨n, hnN, rfl⟩ := exists_lift_normalizer hBp hO hg
  obtain ⟨m, hm1, hm2, hnm⟩ := hn n hnN
  exact ⟨m, hm1, hm2, orderModC_dvd hr ((pow_mem_centralizer_iff hBp hO hnN _).1 hnm)⟩


end Main

end Sec1511

end CFSG.RankThree.PartOne
