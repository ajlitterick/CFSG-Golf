module

public import CFSG.ClassicalInvolution.Q3.Q3TLT3Fusion
public import CFSG.ClassicalInvolution.Q3.Q3TLTInnerAb
public import CFSG.ClassicalInvolution.Q3.TL3Split

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution
open scoped commutatorElement

section Datum

variable {G : Type*} [Group G] [Finite G] {R : Subgroup G} {S : Sylow 2 R} {t : G}

namespace TightDatum

theorem mem_ker_act_iff (d : TightDatum R S t) (y : Subgroup.centralizer ({t} : Set G)) :
    y ∈ d.act.ker ↔ ∀ r ∈ R, ⁅(y : G), r⁆ ∈ oddCoreImg R :=
  d.act_eq_one_iff y.2

theorem nonempty_equiv_q8 (d : TightDatum R S t) {x : Subgroup.centralizer ({t} : Set G)}
    {k : ℕ} (hx : x ^ 3 ^ k = 1) (hx1 : d.act x ≠ 1) :
    Nonempty ((R ⧸ oddCore R) ≃* QuaternionGroup 2) := by
  obtain ⟨e1⟩ := QuaternionStructure.nonempty_mulEquiv_sylow_of_isPGroup_oddCore_quotient
    d.twoGroup S
  have hx3 : (x : G) ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hx
  have hxR : ∃ r ∈ R, ⁅(x : G), r⁆ ∉ oddCoreImg R := by
    by_contra hcon
    push Not at hcon
    exact hx1 ((d.mem_ker_act_iff x).mpr hcon)
  obtain ⟨e2⟩ := tl3_nonempty_mulEquiv_q8 S d.quat d.twoGroup d.le_normalizer x.2 hx3 hxR
  exact ⟨e1.trans e2⟩

theorem act_pow_three_eq_one (d : TightDatum R S t)
    (e : (R ⧸ oddCore R) ≃* QuaternionGroup 2) {x : Subgroup.centralizer ({t} : Set G)}
    {k : ℕ} (hx : x ^ 3 ^ k = 1) : d.act x ^ 3 = 1 :=
  tl3_aut_pow_three_of_pow_three_pow e (by rw [← map_pow, hx, map_one])


end TightDatum

end Datum

section Statements


end Statements

section Main

variable {G : Type*} [Group G] [Finite G] {R : Subgroup G} {S : Sylow 2 R} {t : G}

namespace TightDatum

@[expose] def DiagFree (_d : TightDatum R S t) : Prop :=
  ∀ (x : G) (k : ℕ), x ∈ Subgroup.centralizer ({t} : Set G) → x ^ 3 ^ k = 1 →
    (∃ r ∈ R, ⁅x, r⁆ ∉ oddCoreImg R) →
    ∃ (x' : G) (k' : ℕ), x' ∈ Subgroup.centralizer ({t} : Set G) ∧ x' ^ 3 ^ k' = 1 ∧
      (∃ r ∈ R, ⁅x', r⁆ ∉ oddCoreImg R) ∧
      ∀ y ∈ Subgroup.centralizer ({t} : Set G), (∀ r ∈ R, ⁅y, r⁆ ∈ oddCoreImg R) →
        ⁅x', y⁆ ∈ oddCoreImg (Subgroup.centralizer ({t} : Set G))


omit [Finite G] in
theorem commutator_mem_oddCore_iff (x y : Subgroup.centralizer ({t} : Set G)) :
    ⁅x, y⁆ ∈ oddCore (Subgroup.centralizer ({t} : Set G)) ↔
      ⁅(x : G), (y : G)⁆ ∈ oddCoreImg (Subgroup.centralizer ({t} : Set G)) := by
  rw [mem_oddCore_iff_coe_mem_oddCoreImg]
  rfl


theorem diagFree_iff_c (d : TightDatum R S t) : d.DiagFree ↔
    ∀ (x : Subgroup.centralizer ({t} : Set G)) (k : ℕ), x ^ 3 ^ k = 1 → d.act x ≠ 1 →
      ∃ (x' : Subgroup.centralizer ({t} : Set G)) (k' : ℕ), x' ^ 3 ^ k' = 1 ∧ d.act x' ≠ 1 ∧
        x' ∈ centModO d.act (oddCore (Subgroup.centralizer ({t} : Set G))) := by
  constructor
  · intro h x k hx hx1
    have hx3 : (x : G) ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hx
    have hxR : ∃ r ∈ R, ⁅(x : G), r⁆ ∉ oddCoreImg R := by
      by_contra hcon
      push Not at hcon
      exact hx1 ((d.mem_ker_act_iff x).mpr hcon)
    obtain ⟨x', k', hx'C, hx'3, hx'R, hW⟩ := h (x : G) k x.2 hx3 hxR
    refine ⟨⟨x', hx'C⟩, k', Subtype.ext (by simpa using hx'3), ?_, ?_⟩
    · intro h1
      obtain ⟨r, hr, hnr⟩ := hx'R
      exact hnr ((d.act_eq_one_iff hx'C).mp h1 r hr)
    · intro y hy
      exact (commutator_mem_oddCore_iff _ _).mpr (hW (y : G) y.2 ((d.mem_ker_act_iff y).mp hy))
  · intro h x k hxC hx3 hxR
    have hx1 : d.act ⟨x, hxC⟩ ≠ 1 := fun h1 => by
      obtain ⟨r, hr, hnr⟩ := hxR
      exact hnr ((d.act_eq_one_iff hxC).mp h1 r hr)
    obtain ⟨x', k', hx', hx'1, hW⟩ := h ⟨x, hxC⟩ k (Subtype.ext (by simpa using hx3)) hx1
    refine ⟨(x' : G), k', x'.2, by simpa using congrArg Subtype.val hx', ?_, ?_⟩
    · by_contra hcon
      push Not at hcon
      exact hx'1 ((d.mem_ker_act_iff x').mpr hcon)
    · intro y hyC hy
      exact (commutator_mem_oddCore_iff x' ⟨y, hyC⟩).mp (hW ⟨y, hyC⟩
        ((d.mem_ker_act_iff ⟨y, hyC⟩).mpr hy))


end TightDatum

end Main


end CFSG.ClassicalInvolution.Q3
