module

public import CFSG.Quasithin.AppendixH.H9.GLBasics
public import CFSG.Quasithin.AppendixH.H9.GLAutomorphisms
public import CFSG.Quasithin.AppendixH.H9.AutPair.StabilizerElements

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH.AutPair

open CFSG.Quasithin CFSG.Open

variable (m : ℕ)

@[expose] noncomputable def Mv : Subgroup (MulAut (PairN (m + 1))) :=
  Mg (m + 1) ⊓ centSub (Subgroup.zpowers (pairVec (ez m) 0 * pairVec 0 (ez m)))

variable {m}

theorem mem_Mv {g : MulAut (PairN (m + 1))} :
    g ∈ Mv m ↔ (∃ B : GL (Fin m) (ZMod 2), g = pairActN (m + 1) (levi m B)) ∨
      ∃ B : GL (Fin m) (ZMod 2), g = pairActN (m + 1) (levi m B) * swapN (m + 1) :=
  mem_Mv_iff

variable (m)

@[expose] noncomputable def kappa : GL (Fin m) (ZMod 2) →* Mv m :=
  ((pairActN (m + 1)).comp (levi m)).codRestrict (Mv m) fun B => mem_Mv.2 (Or.inl ⟨B, rfl⟩)

@[expose] noncomputable def swapElt : Mv m :=
  ⟨swapN (m + 1), mem_Mv.2 (Or.inr ⟨1, by simp⟩)⟩

variable {m}


theorem exists_eq_kappa_or (g : Mv m) :
    (∃ B : GL (Fin m) (ZMod 2), g = kappa m B) ∨
      ∃ B : GL (Fin m) (ZMod 2), g = kappa m B * swapElt m := by
  obtain ⟨g, hg⟩ := g
  rcases mem_Mv.1 hg with ⟨B, rfl⟩ | ⟨B, rfl⟩
  · exact Or.inl ⟨B, rfl⟩
  · exact Or.inr ⟨B, rfl⟩

theorem swapElt_mul_kappa_mul_inv (X : GL (Fin m) (ZMod 2)) :
    swapElt m * kappa m X * (swapElt m)⁻¹ = kappa m (dualGLn m X) := by
  apply Subtype.ext
  show swapN (m + 1) * pairActN (m + 1) (levi m X) * (swapN (m + 1))⁻¹ =
    pairActN (m + 1) (levi m (dualGLn m X))
  rw [swapN_mul_pairActN_levi, mul_assoc, mul_inv_cancel, mul_one]

instance kappa_range_normal : (kappa m).range.Normal where
  conj_mem := by
    rintro _ ⟨X, rfl⟩ g
    rcases exists_eq_kappa_or g with ⟨B, rfl⟩ | ⟨B, rfl⟩
    · exact ⟨B * X * B⁻¹, by simp only [map_mul, map_inv]⟩
    · refine ⟨B * dualGLn m X * B⁻¹, ?_⟩
      rw [map_mul, map_mul, map_inv, ← swapElt_mul_kappa_mul_inv]
      group


end CFSG.ASVolI.ChH.AutPair
