module

public import CFSG.Quasithin.H13.A5F91

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model

@[expose] def wt (x : W5) : ℕ :=
  (Finset.univ.filter fun i : Fin 5 => ((Multiplicative.toAdd x : ↥Ev) : Fin 5 → ZMod 2) i ≠ 0).card

@[expose] def IsSing (x : W5) : Prop := wt x % 4 = 0

instance : DecidablePred IsSing := fun x => inferInstanceAs (Decidable (wt x % 4 = 0))


@[expose] def AltReach (x y : W5) : Prop := ∃ σ : Equiv.Perm (Fin 5), σ.sign = 1 ∧ pact σ x = y

instance : DecidableRel AltReach := fun x y =>
  inferInstanceAs (Decidable (∃ σ : Equiv.Perm (Fin 5), σ.sign = 1 ∧ pact σ x = y))

@[expose] def AltTrans (x y : W5) : Prop :=
  x ≠ 1 → y ≠ 1 → (IsSing x ↔ IsSing y) → AltReach x y

instance : DecidableRel AltTrans := fun x y =>
  inferInstanceAs (Decidable (x ≠ 1 → y ≠ 1 → (IsSing x ↔ IsSing y) → AltReach x y))

theorem altTrans : ∀ x y : W5, AltTrans x y := by
  decide +kernel

theorem exists_alt_pact (x y : W5) (hx : x ≠ 1) (hy : y ≠ 1) (h : IsSing x ↔ IsSing y) :
    AltReach x y :=
  altTrans x y hx hy h

theorem isSing_W4 : IsSing W4 := by decide +kernel

@[expose] def Input1326Two : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting G T L V) (g : G)
    (v w : ↥V), g * v * g⁻¹ = w → (IsSing (S.frame.ψ v) ↔ IsSing (S.frame.ψ w))

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)
include S

omit [Finite G] S in
theorem mem_normalizer_conjSub_iff {X : Subgroup G} {g x : G} :
    x ∈ Subgroup.normalizer (conjSub g⁻¹ X : Set G) ↔
      g * x * g⁻¹ ∈ Subgroup.normalizer (X : Set G) := by
  rw [conjSub_normalizer, mem_conjSub, inv_inv]


theorem exists_centralizer_conj (h1326 : Input1326Two) {v g : G} (hv : v ∈ V) (hv1 : v ≠ 1)
    (hvg : v ∈ conjSub g⁻¹ V) :
    ∃ c ∈ Subgroup.centralizer ({v} : Set G), conjSub g⁻¹ V = conjSub c⁻¹ V := by
  rw [mem_conjSub, inv_inv] at hvg
  have hsing := h1326 G T L V S g ⟨v, hv⟩ ⟨g * v * g⁻¹, hvg⟩ rfl
  have hw1 : S.frame.ψ ⟨g * v * g⁻¹, hvg⟩ ≠ 1 := by
    intro h
    apply hv1
    have : (⟨g * v * g⁻¹, hvg⟩ : ↥V) = 1 := S.frame.ψ.injective (by rw [h, map_one])
    have := congrArg Subtype.val this
    simp only [OneMemClass.coe_one] at this
    have e : v = g⁻¹ * (g * v * g⁻¹) * g := by group
    rw [e, this]; group
  have hv1' : S.frame.ψ ⟨v, hv⟩ ≠ 1 := by
    intro h
    apply hv1
    have : (⟨v, hv⟩ : ↥V) = 1 := S.frame.ψ.injective (by rw [h, map_one])
    exact congrArg Subtype.val this
  obtain ⟨σ, hσ, hσx⟩ := exists_alt_pact _ _ hw1 hv1' hsing.symm
  obtain ⟨l, hlL, hlσ⟩ := (S.frame.image_L σ).2 hσ
  refine ⟨l * g, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    have := (S.psi_conj l ⟨g * v * g⁻¹, hvg⟩)
    rw [hlσ, hσx] at this
    have hlv : (l : G) * (g * v * g⁻¹) * (l : G)⁻¹ = v := by
      have := congrArg Subtype.val (S.frame.ψ.injective this)
      simpa using this
    calc l * g * v = (l : G) * (g * v * g⁻¹) * (l : G)⁻¹ * (l * g) := by group
      _ = v * (l * g) := by rw [hlv]
  · rw [mul_inv_rev, conjSub_mul, conjSub_self_of_mem (Subgroup.inv_mem _ l.2)]

end Setting

end CFSG.Quasithin.H13.A5
