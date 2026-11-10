module

public import CFSG.ClassicalInvolution.ModelFacts.ChevAutMain
public import CFSG.ClassicalInvolution.ModelFacts.ChevAutTorusDiag
public import CFSG.ClassicalInvolution.RouteD.LocalTwinWeyl

public section

namespace CFSG.ClassicalInvolution.ModelFacts.ChevAut

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.CentralExt
  CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.RootSystem CFSG.LieType.CurtisTits

section Instances

variable (F : Type) [Field F]


theorem torusSetup_E7 : TorusSetup (e7Datum F) (e7Data_valid.xm F) (e7Data_valid.nm F)
    (e7Data_valid.torus F) := by
  obtain ⟨O⟩ := nonempty_commOrder_ofCartan (e7Datum F).isFiniteType
    (Dv := (e7Datum F).divisible) rfl
  exact ⟨⟨_, O, e7_chevalleyExtras F O _
      (e7Data_valid.commutatorFormula_commC F posDef_cartan_E7 _
        (roots_eq isFiniteType_cartan_E7) O)⟩,
    e7Datum_isCTGroupDatum F, e7Datum_steinbergExtras F, e7Datum_bruhatExtras F,
    fun _ => rfl, fun _ _ => ⟨fun ⟨s, hs⟩ => ⟨s, hs.symm⟩, fun ⟨s, hs⟩ => ⟨s, hs.symm⟩⟩,
    fun i s s' => e7Data_valid.hm_mul F i s s', rfl⟩


end Instances

section Sign

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {F : Type} [Field F]

open Classical in
theorem diagChar_eq_one_iff (h2 : (2 : F) ≠ 0) {b : Fin D.rank → Fˣ}
    (hb : ∀ i, b i = 1 ∨ b i = -1) (γ : Fin D.rank → ℤ) :
    diagChar b γ = 1 ↔ ∑ i, (γ i : ZMod 2) * (if b i = 1 then 0 else 1) = 0 := by
  have hne : (-1 : Fˣ) ≠ 1 := by
    intro h
    apply h2
    have := congrArg (fun u : Fˣ => (u : F)) h
    simp only [Units.val_neg, Units.val_one] at this
    linear_combination -this
  have h1 : diagChar b γ = (-1 : Fˣ) ^ (∑ i, γ i * (if b i = 1 then (0 : ℤ) else 1)) := by
    rw [diagChar, ← Finset.prod_zpow_eq_zpow_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rcases hb i with h | h
    · rw [h]
      simp
    · rw [h]
      simp [hne]
  have h4 : ∀ M : ℤ, (-1 : Fˣ) ^ M = 1 ↔ Even M := by
    intro M
    rw [neg_one_zpow_eq_ite]
    by_cases he : Even M
    · simp [he]
    · simp [he, hne]
  rw [h1, h4]
  have h3 : ((∑ i, γ i * (if b i = 1 then (0 : ℤ) else 1) : ℤ) : ZMod 2) =
      ∑ i, (γ i : ZMod 2) * (if b i = 1 then 0 else 1) := by
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  rw [← h3, ZMod.intCast_eq_zero_iff_even]

end Sign

section Fixed

variable {K : Type} [Group K] {D : UniversalRootDatum K} {F : Type} [Field F]
  {x : (Fin D.rank → ℤ) → F → K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}

theorem eq_of_map_eq {p : ℕ} [Fact p.Prime] [CharP F p] (hS : TorusSetup D x n H)
    {X : Type} [Group X] (θ : K →* X) (hker : θ.ker ≤ Subgroup.center K)
    (hC : ¬ p ∣ Nat.card θ.ker) {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) {c c' : F}
    (h : θ (x γ c) = θ (x γ c')) : c = c' := by
  obtain ⟨C, O, hE⟩ := hS.chev
  exact (hE.param γ hγ).2.2 (CFSG.LieType.CentralExt.eq_of_pElement (π := θ) hker hC h
    (exists_orderOf_param hE.param hγ c) (exists_orderOf_param hE.param hγ c'))

theorem fixes_iff_charOf {p : ℕ} [Fact p.Prime] [CharP F p] (hS : TorusSetup D x n H)
    (hp2 : p ≠ 2) {X : Type} [Group X] (θ : K →* X) (hker : θ.ker ≤ Subgroup.center K)
    (hC : ¬ p ∣ Nat.card θ.ker) (σ : X ≃* X) (hσ2 : ∀ y, σ (σ y) = y) (α : K →* K)
    (hαθ : ∀ y, θ (α y) = σ (θ y)) (b : Fin D.rank → Fˣ)
    (hb : ∀ γ ∈ D.roots, ∀ c, α (x γ c) = x γ ((diagChar b γ : F) * c)) :
    ∃ v : Fin D.rank → ZMod 2, ∀ γ ∈ D.roots,
      ((∀ y ∈ (D.rootGroup γ ⊔ D.rootGroup (-γ)).map θ, σ y = y) ↔
        ∑ i, (γ i : ZMod 2) * v i = 0) := by
  classical
  obtain ⟨C, O, hE⟩ := hS.chev
  have h2 : (2 : F) ≠ 0 := by
    intro h0
    have := (CharP.cast_eq_zero_iff F p 2).1 (by exact_mod_cast h0)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 this)
  have hroot : ∀ i, (Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots := fun i =>
    (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i
  have hneg : ∀ γ ∈ D.roots, -γ ∈ D.roots := fun γ hγ =>
    CFSG.LieType.Steinberg.OfCartan.neg_mem_roots D.isFiniteType hγ
  have hbpm : ∀ i, b i = 1 ∨ b i = -1 := by
    intro i
    have h1 := hb (Pi.single i 1) (hroot i) 1
    rw [diagChar_single] at h1
    have h2' := hb (Pi.single i 1) (hroot i) ((b i : F) * 1)
    rw [diagChar_single] at h2'
    have h3 : θ (x (Pi.single i 1) ((b i : F) * ((b i : F) * 1))) = θ (x (Pi.single i 1) 1) :=
      calc θ (x (Pi.single i 1) ((b i : F) * ((b i : F) * 1)))
          = θ (α (α (x (Pi.single i 1) 1))) := by rw [h1, h2']
        _ = σ (θ (α (x (Pi.single i 1) 1))) := hαθ _
        _ = σ (σ (θ (x (Pi.single i 1) 1))) := by rw [hαθ]
        _ = θ (x (Pi.single i 1) 1) := hσ2 _
    have h4 := eq_of_map_eq hS θ hker hC (hroot i) h3
    have h5 : (b i : F) * (b i : F) = 1 := by simpa using h4
    rcases mul_self_eq_one_iff.1 h5 with h | h
    · exact Or.inl (Units.ext (by simpa using h))
    · exact Or.inr (Units.ext (by simpa using h))
  refine ⟨fun i => if b i = 1 then 0 else 1, fun γ hγ => ?_⟩
  rw [← diagChar_eq_one_iff h2 hbpm γ]
  constructor
  · intro hall
    have hmem : θ (x γ 1) ∈ (D.rootGroup γ ⊔ D.rootGroup (-γ)).map θ :=
      ⟨x γ 1, Subgroup.mem_sup_left (((hE.param γ hγ).1 _).2 ⟨1, rfl⟩), rfl⟩
    have h1 := hall _ hmem
    rw [← hαθ, hb γ hγ 1] at h1
    have h3 := eq_of_map_eq hS θ hker hC hγ h1
    exact Units.ext (by simpa using h3)
  · intro hd y hy
    obtain ⟨k, hk, rfl⟩ := hy
    have hα1 : ∀ c, α (x γ c) = x γ c := fun c => by
      rw [hb γ hγ c, hd]
      simp
    have hα2 : ∀ c, α (x (-γ) c) = x (-γ) c := fun c => by
      rw [hb (-γ) (hneg γ hγ) c, diagChar_neg, hd]
      simp
    have hle : (D.rootGroup γ ⊔ D.rootGroup (-γ)) ≤ MonoidHom.eqLocus α (MonoidHom.id K) := by
      refine sup_le (fun g hg => ?_) (fun g hg => ?_)
      · obtain ⟨c, rfl⟩ := ((hE.param γ hγ).1 g).1 hg
        exact hα1 c
      · obtain ⟨c, rfl⟩ := ((hE.param (-γ) (hneg γ hγ)).1 g).1 hg
        exact hα2 c
    have hk' : α k = k := hle hk
    calc σ (θ k) = θ (α k) := (hαθ k).symm
      _ = θ k := by rw [hk']

end Fixed

section Lift

variable {K : Type} [Group K] (D : UniversalRootDatum K) {F : Type} [Field F]


end Lift

section Toral

variable {K : Type} [Group K] {D : UniversalRootDatum K} {F : Type} [Field F]
  {x : (Fin D.rank → ℤ) → F → K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}

theorem mul_inv_mem_center_of_fix {X : Type} [Group X] (θ : K →* X)
    (hker : θ.ker ≤ Subgroup.center K) (σ : X ≃* X) (α : K →* K)
    (hαθ : ∀ y, θ (α y) = σ (θ y)) {t : K} (ht : σ (θ t) = θ t) :
    α t * t⁻¹ ∈ Subgroup.center K := by
  apply hker
  rw [MonoidHom.mem_ker, map_mul, map_inv, hαθ, ht, mul_inv_cancel]


end Toral

section Ambient

variable {K : Type} [Group K] {D : UniversalRootDatum K} {F : Type} [Field F] [Finite F]
  {p : ℕ} [Fact p.Prime] [CharP F p] {x : (Fin D.rank → ℤ) → F → K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}


end Ambient

section Families

open CFSG.ClassicalInvolution.RouteD (charOf)
open CFSG.ClassicalInvolution.Generic (conjSub)

theorem cartanE6_nb : ∀ k : Fin 6, ∃ j : Fin 6, Tag.cartan .E6 j k = -1 := by decide
theorem cartanE7_nb : ∀ k : Fin 7, ∃ j : Fin 7, Tag.cartan .E7 j k = -1 := by decide
theorem cartanE8_nb : ∀ k : Fin 8, ∃ j : Fin 8, Tag.cartan .E8 j k = -1 := by decide


theorem cartanE7_offDiag :
    ∀ i j : Fin 7, i ≠ j → Tag.cartan .E7 i j = 0 ∨ Tag.cartan .E7 i j = -1 := by
  intro i j hij
  have h : i = j ∨ Tag.cartan .E7 i j = 0 ∨ Tag.cartan .E7 i j = -1 := by
    fin_cases i <;> fin_cases j <;> decide
  exact h.resolve_left hij


variable (F : Type) [Field F] [Finite F]


theorem hC_E7 {p : ℕ} [Fact p.Prime] [CharP F p] :
    ∀ N : Subgroup ↥(e7Data_valid.minGroup F), N ≤ Subgroup.center _ → ¬ p ∣ Nat.card N := by
  intro N hN
  have := finite_minGroup e7Data_valid F
  exact not_dvd_card_of_forall_pow_card_sub_one (F := F) fun z hz =>
    center_pow_eq_one (e7Datum_isCTGroupDatum F) (e7Datum_steinbergExtras F)
      (e7Datum_bruhatExtras F) (fun i h hh => torus_pow_card_sub_one e7Data_valid F i hh) z
      (hN hz)


end Families

end CFSG.ClassicalInvolution.ModelFacts.ChevAut
