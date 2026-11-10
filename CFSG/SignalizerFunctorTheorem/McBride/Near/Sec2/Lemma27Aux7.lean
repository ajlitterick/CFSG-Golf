module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Lemma27Aux4
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.PrimeTwo

public section

open CFSG.Open
open scoped Pointwise
open CFSG.SignalizerFunctorTheorem.Nonsolvable (simpleComponents IsASimple)
open CFSG.SignalizerFunctorTheorem.McBride
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Lemma27

variable {Γ : Type*} [Group Γ] [Finite Γ]

omit [Finite Γ] in
theorem isDirectProduct_of_subset {S T : Set (Subgroup Γ)} {K : Subgroup Γ}
    (hK : IsDirectProduct S K) (hTS : T ⊆ S) : IsDirectProduct T (sSup T) where
  commute J hJ L hL hne x hx y hy := hK.commute J (hTS hJ) L (hTS hL) hne x hx y hy
  indep J hJ := by
    have h1 := hK.indep (hTS hJ)
    exact h1.mono_right (sSup_le_sSup (Set.sdiff_subset_sdiff_left hTS))
  sSup_eq := rfl

omit [Finite Γ] in
theorem simple_of_mem_lcal {K J : Subgroup Γ} (hJ : J ∈ lcal K) :
    IsSimpleGroup J ∧ ∃ x ∈ J, ∃ y ∈ J, x * y ≠ y * x := by
  obtain ⟨-, -, hJs, hnc⟩ := mem_lcal_iff.mp hJ
  refine ⟨hJs, ?_⟩
  by_contra hcon
  push Not at hcon
  exact hnc (isMulCommutative_iff.mpr fun x y => Subtype.ext (hcon x x.2 y y.2))


theorem diagSetting_orbitClosure {p : ℕ} {A R J : Subgroup Γ} (hp : p.Prime)
    (hA : IsElemAbelian p A) (hAR : A ≤ Subgroup.normalizer (R : Set Γ)) (hJ : J ∈ lcal R) :
    DiagSetting p A (orbitClosure J A) ∧ lcal (orbitClosure J A) = L514.conjOrbit A J := by
  have hL := L514.isDirectProduct_conjOrbit hAR hJ
  have hsub := L514.conjOrbit_subset_lcal hAR hJ
  have hlcal : lcal (orbitClosure J A) = L514.conjOrbit A J :=
    lcal_eq_of_isDirectProduct hL fun D hD => simple_of_mem_lcal (hsub hD)
  refine ⟨⟨hp, hA, fun a ha => L514.mem_normalizer_orbitClosure ha, hlcal ▸ hL,
    hlcal ▸ ⟨J, L514.self_mem_conjOrbit A J⟩, ?_⟩, hlcal⟩
  rw [hlcal]
  exact fun J₁ h₁ J₂ h₂ => L514.exists_conj_of_mem_conjOrbit h₁ h₂


end CFSG.SignalizerFunctorTheorem.McBride.Near.Lemma27
