module

public import CFSG.Quasithin.Background.MS09.LLemma
public import CFSG.Quasithin.Background.MS09.Module45

public section

namespace CFSG.Quasithin.MS09

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.B6 CFSG.Quasithin.MS09.Mod

variable {P : Type} [Group P] {V : Type} [CommGroup V] {ρ : P →* MulAut V}

namespace Th46

theorem exists_fix_ne_one [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {N : Subgroup P}
    (hN : IsPGroup 2 N) (hV1 : (⊤ : Subgroup V) ≠ ⊥) : fixIn ρ N ⊤ ≠ ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : MulAction ↥N V := MulAction.compHom V (ρ.comp N.subtype)
  have hcong := hN.card_modEq_card_fixedPoints V
  have hV2 : IsPGroup 2 V := fun v => ⟨1, by simpa using hV v⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hV2
  have hn0 : n ≠ 0 := by
    rintro rfl
    apply hV1
    rw [pow_zero] at hn
    have : Subsingleton V := (Nat.card_eq_one_iff_unique.mp hn).1
    exact Subsingleton.elim _ _
  have heven : 2 ∣ Nat.card (MulAction.fixedPoints ↥N V) := by
    have h2 : 2 ∣ Nat.card V := by rw [hn]; exact dvd_pow_self 2 hn0
    exact (Nat.modEq_zero_iff_dvd.mp (hcong.symm.trans (Nat.modEq_zero_iff_dvd.mpr h2)))
  have hfix : ∀ v : V, v ∈ MulAction.fixedPoints ↥N V ↔ v ∈ fixIn ρ N ⊤ := fun v => by
    rw [MulAction.mem_fixedPoints]
    constructor
    · intro h
      exact ⟨Subgroup.mem_top v, fun g hg => h ⟨g, hg⟩⟩
    · intro h n
      exact h.2 n n.2
  intro hbot
  have hsub : MulAction.fixedPoints ↥N V = {1} := by
    ext v
    rw [hfix, hbot, Subgroup.mem_bot, Set.mem_singleton_iff]
  rw [hsub, Nat.card_unique] at heven
  exact absurd heven (by decide)


section MinPar

variable [Finite P] [Finite V] {S M : Subgroup P} (hmp : MinParabolic (⊤ : Subgroup P) S M)
  (hV : ∀ v : V, v ^ 2 = 1)
  (hirr : ∀ W : Subgroup V, (⊤ : Subgroup P) ≤ stabIn ρ W → W = ⊥ ∨ W = ⊤)
  (hnt : ¬ (⊤ : Subgroup P) ≤ cenIn ρ ⊤)

include hnt in
theorem top_ne_bot : (⊤ : Subgroup V) ≠ ⊥ := by
  intro h
  apply hnt
  intro g _ v hv
  have : v ∈ (⊥ : Subgroup V) := h ▸ hv
  rw [Subgroup.mem_bot] at this
  rw [this, map_one]


end MinPar

end Th46

end CFSG.Quasithin.MS09

end
