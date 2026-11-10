module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMismatchTablesTransport
public import CFSG.LieType.Universal.SymplecticRoots

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup
open CFSG.Quasithin (perfectCore)

section Tori

variable (F : Type) [Field F]

@[expose] noncomputable def sp6ParamA : Fˣ →* (Fin 3 → Fˣ) :=
  MonoidHom.mulSingle (fun _ : Fin 3 => Fˣ) 0

@[expose] noncomputable def sp6ParamM2 : Fˣ × Fˣ →* (Fin 3 → Fˣ) :=
  (MonoidHom.mulSingle (fun _ : Fin 3 => Fˣ) 0).comp (MonoidHom.fst Fˣ Fˣ) *
    (MonoidHom.mulSingle (fun _ : Fin 3 => Fˣ) 1).comp (MonoidHom.snd Fˣ Fˣ)

@[expose] noncomputable def sp6ParamM3 : Fˣ × Fˣ →* (Fin 3 → Fˣ) :=
  (MonoidHom.mulSingle (fun _ : Fin 3 => Fˣ) 0).comp (MonoidHom.fst Fˣ Fˣ) *
    ((MonoidHom.mulSingle (fun _ : Fin 3 => Fˣ) 1) * (MonoidHom.mulSingle (fun _ : Fin 3 => Fˣ) 2)).comp
      (MonoidHom.snd Fˣ Fˣ)

@[expose] noncomputable def sp6Diag :
    (Fin 3 → Fˣ) →* CFSG.Assembly.LowTwoRank.StatedSp 3 F :=
  (CFSG.LieType.Universal.Symplectic.equivStatedSp 3 F).toMonoidHom.comp
    TauCeti.GLSymplecticFin.diagonal

variable {F}

@[expose] noncomputable def sp6TorusA (A : Subgroup Fˣ) :
    Subgroup (CFSG.Assembly.LowTwoRank.StatedSp 3 F) :=
  A.map ((sp6Diag F).comp (sp6ParamA F))

@[expose] noncomputable def sp6TorusM2 (A : Subgroup Fˣ) :
    Subgroup (CFSG.Assembly.LowTwoRank.StatedSp 3 F) :=
  (A.prod A).map ((sp6Diag F).comp (sp6ParamM2 F))

@[expose] noncomputable def sp6TorusM3 (A : Subgroup Fˣ) :
    Subgroup (CFSG.Assembly.LowTwoRank.StatedSp 3 F) :=
  (A.prod A).map ((sp6Diag F).comp (sp6ParamM3 F))

end Tori

theorem mul_diagonal_eq_diagonal_mul_iff {ι F : Type*} [Fintype ι] [DecidableEq ι] [Field F]
    (g : Matrix ι ι F) (d : ι → F) :
    g * Matrix.diagonal d = Matrix.diagonal d * g ↔ ∀ i j, d i ≠ d j → g i j = 0 := by
  constructor
  · intro h i j hij
    have h' := congrFun (congrFun h i) j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h'
    have h'' : (d j - d i) * g i j = 0 := by
      rw [sub_mul, mul_comm (d j), h', sub_self]
    rcases mul_eq_zero.mp h'' with h0 | h0
    · exact absurd (sub_eq_zero.mp h0).symm hij
    · exact h0
  · intro h
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hij : d i = d j
    · rw [hij, mul_comm]
    · rw [h i j hij, zero_mul, mul_zero]


section Kinds

variable {G : Type*} [Group G] [Finite G] {E T₁₂ T₁ T₂ : Subgroup G}

private theorem exists_unit_sq_ne_one {F : Type} [Field F] [Finite F] (hF : 4 ≤ Nat.card F) :
    ∃ a : Fˣ, a ^ 2 ≠ 1 := by
  classical
  have := Fintype.ofFinite F
  obtain ⟨x, -, hx⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({0, 1, -1} : Finset F)) (t := Finset.univ) (by
      calc ({0, 1, -1} : Finset F).card ≤ 3 := Finset.card_le_three
        _ < Finset.univ.card := by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
  obtain ⟨h0, h1, hm1⟩ := hx
  refine ⟨Units.mk0 x h0, fun h => ?_⟩
  have h2 : x ^ 2 = 1 := by
    have := congrArg (fun u : Fˣ => (u : F)) h
    simpa using this
  rcases sq_eq_one_iff.mp h2 with h3 | h3
  · exact h1 h3
  · exact hm1 h3


end Kinds

end CFSG.SeitzReduction.F4Pilot
