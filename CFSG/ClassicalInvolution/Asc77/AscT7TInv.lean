module

public import CFSG.ClassicalInvolution.Asc77.AscT7TC5
public import CFSG.ClassicalInvolution.Asc77.AscT7TStar2
public import CFSG.ClassicalInvolution.Asc77.AscP1Strong
public import CFSG.ClassicalInvolution.Asc77.AscT7TOdd

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace T7T

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ : G}

theorem perm_R_of_hyp (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂) {s : G}
    (hs : s ∈ (S : Subgroup G)) {X : Subgroup G} (hX : X = R ∨ X = R') :
    conjSub s X = R ∨ conjSub s X = R' := by
  have hΩ : HypOmegaMod p f Ω := hyp.std.setting.stand.hyp
  have hXmem : X ∈ RSet Ω := by rcases hX with rfl | rfl; exacts [hyp.hR.1, hyp.hR'.1]
  have hXS : X ≤ (S : Subgroup G) := by rcases hX with rfl | rfl; exacts [hyp.hR.2.2, hyp.hR'.2.2]
  have hmem : conjSub s X ∈ RSet Ω := RSet.conj hΩ.conjInvariant hXmem s
  have hle : conjSub s X ≤ (S : Subgroup G) := by
    intro x hx
    rw [mem_conjSub_iff] at hx
    have h1 : s * (s⁻¹ * x * s) * s⁻¹ ∈ (S : Subgroup G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hs (hXS hx)) (Subgroup.inv_mem _ hs)
    simpa [mul_assoc] using h1
  exact hyp.hRS _ hmem hle


theorem conjSub_sup_of_hyp (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂) {s : G}
    (hs : s ∈ (S : Subgroup G)) : conjSub s (R ⊔ R') = R ⊔ R' := by
  have hne : R ≠ R' := T7ER.ne_of_hyp25 hyp
  rw [T7F2.conjSub_sup']
  rcases perm_R_of_hyp hyp hs (Or.inl rfl : R = R ∨ R = R') with h | h
  · have h' : conjSub s R' = R' := by
      rcases perm_R_of_hyp hyp hs (Or.inr rfl : R' = R ∨ R' = R') with h' | h'
      · exact absurd (conjSub_injective s (h.trans h'.symm)) hne
      · exact h'
    rw [h, h']
  · have h' : conjSub s R' = R := by
      rcases perm_R_of_hyp hyp hs (Or.inr rfl : R' = R ∨ R' = R') with h' | h'
      · exact h'
      · exact absurd (conjSub_injective s (h.trans h'.symm)) hne
    rw [h, h', sup_comm]

theorem conjSub_centralizer_of_hyp (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂) {s : G}
    (hs : s ∈ (S : Subgroup G)) :
    conjSub s ((S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G)) =
      (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) := by
  rw [T7F2.conjSub_inf_centralizer, conjSub_eq_self_of_mem hs, conjSub_sup_of_hyp hyp hs]

theorem z_mem_centralizer_of_hyp (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂) :
    z ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) := by
  have hs : Hyp23Setting p f Ω K K' z := hyp.std.setting
  have hp : p ≠ 2 := hs.stand.odd
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hK' : K' ∈ Ω := hs.hK'.1
  have hz : IsUniqueInvolution K z := hs.hz
  have hz' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hs.hK'
  have hRsyl : IsSylow2In R K := T7C.isSylow2In_of_mem_RSet_of_le hp hΩ hK hyp.hR.1 hyp.hR.2.1
  have hR'syl : IsSylow2In R' K' :=
    T7C.isSylow2In_of_mem_RSet_of_le hp hΩ hK' hyp.hR'.1 hyp.hR'.2.1
  have h8 := (hΩ.isQuatSub_of_mem_RSet hp hyp.hR.1).eight_le
  have h8' := (hΩ.isQuatSub_of_mem_RSet hp hyp.hR'.1).eight_le
  have hzR : z ∈ R := mem_of_isUniqueInvolution_of_isPGroup hz hyp.hR.2.1 hRsyl.2.1 (by omega)
  have hzR' : z ∈ R' := mem_of_isUniqueInvolution_of_isPGroup hz' hyp.hR'.2.1 hR'syl.2.1 (by omega)
  have hle : R ⊔ R' ≤ Subgroup.centralizer ({z} : Set G) :=
    sup_le (hyp.hR.2.1.trans (AscP1Nine3.le_centralizer_of_uniqueInvolution hz))
      (hyp.hR'.2.1.trans (AscP1Nine3.le_centralizer_of_uniqueInvolution hz'))
  refine ⟨hyp.hR.2.2 hzR, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
  have := Subgroup.mem_centralizer_singleton_iff.mp (hle hx)
  exact this


end T7T

end CFSG.ClassicalInvolution.Asc77
