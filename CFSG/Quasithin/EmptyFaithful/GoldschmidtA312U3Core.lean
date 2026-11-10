module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3Red
public import CFSG.RepresentationTheory.UniqueVectorOrbitTwisting

public section

namespace CFSG.Quasithin.A312U3

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Assembly.LowTwoRank CFSG.Quasithin CFSG.RepresentationTheory

@[expose] def IsIrrIn {K : Type} [Field K] (A : Subgroup (GL (Fin 3) K)) (M : Subgroup ↥A) :
    Prop :=
  IsIrreducibleMatrixRep ((M.map A.subtype).subtype)

@[expose] def CoreC (p : ℕ) {K : Type} [Field K] (M : Subgroup ↥(StatedSU 3 (p ^ 1) K)) : Prop :=
  Group.IsSolvable ↥M ∨ IsSL2 p ↥(perfectCore M) ∨
    (p = 5 ∧ IsHat ↥(perfectCore M) (alternatingGroup (Fin 6)) ∧
      ∀ z ∈ Subgroup.center ↥(perfectCore M),
        (((z : ↥(perfectCore M)) : ↥(StatedSU 3 (p ^ 1) K)) : GL (Fin 3) K) ∈
          StatedScalars (Fin 3) K)

@[expose] def SU3OddIrr : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (K : Type) [Field K] [Finite K], Nat.card K = p ^ 2 →
    ∀ M : Subgroup ↥(StatedSU 3 (p ^ 1) K), Odd M.index → IsIrrIn (StatedSU 3 (p ^ 1) K) M →
      M = ⊤ ∨ Group.IsSolvable ↥M ∨
        (p = 5 ∧ IsHat ↥(perfectCore M) (alternatingGroup (Fin 6)) ∧
          ∀ z ∈ Subgroup.center ↥(perfectCore M),
            (((z : ↥(perfectCore M)) : ↥(StatedSU 3 (p ^ 1) K)) : GL (Fin 3) K) ∈
              StatedScalars (Fin 3) K)

variable {p : ℕ} {F : Type} [Field F]

theorem exists_invariant_of_not_irr {M : Subgroup ↥(unitarySU p 1 F 3)}
    (h : ¬ IsIrrIn (unitarySU p 1 F 3) M) :
    ∃ W : Submodule F (Fin 3 → F),
      (∀ g ∈ M, ∀ w ∈ W, ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w ∈ W) ∧
        W ≠ ⊥ ∧ W ≠ ⊤ := by
  unfold IsIrrIn IsIrreducibleMatrixRep at h
  push Not at h
  obtain ⟨W, hW, hbot, htop⟩ := h
  refine ⟨W, fun g hg w hw => ?_, hbot, htop⟩
  exact hW ⟨(g : GL (Fin 3) F), g, hg, rfl⟩ w hw

variable [Finite F]

theorem CoreC.of_map_conj (g : ↥(unitarySU p 1 F 3)) {M : Subgroup ↥(unitarySU p 1 F 3)}
    (h : CoreC p (M.map (MulAut.conj g).toMonoidHom)) : CoreC p M := by
  classical
  set c : ↥(unitarySU p 1 F 3) ≃* ↥(unitarySU p 1 F 3) := MulAut.conj g with hc
  set M₁ : Subgroup ↥(unitarySU p 1 F 3) := M.map c.toMonoidHom with hM₁
  let ε : ↥(perfectCore M) ≃* ↥(perfectCore M₁) :=
    ((perfectCore M).equivMapOfInjective c.toMonoidHom c.injective).trans
      (MulEquiv.subgroupCongr (map_perfectCore c.toMonoidHom M))
  rcases h with hs | hSL | ⟨hp5, hHat, hz⟩
  · left
    exact Group.isSolvable_of_isSolvable_injective
      (f := (M.equivMapOfInjective c.toMonoidHom c.injective).toMonoidHom)
      (MulEquiv.injective _)
  · right
    left
    obtain ⟨e⟩ := hSL
    exact ⟨ε.trans e⟩
  · right
    right
    refine ⟨hp5, IsHat.of_mulEquiv ε.symm hHat, fun z hzc => ?_⟩
    have hεz : ε z ∈ Subgroup.center ↥(perfectCore M₁) := by
      rw [Subgroup.mem_center_iff]
      intro w'
      obtain ⟨w, rfl⟩ := ε.surjective w'
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hzc w]
    have h1 := hz (ε z) hεz
    have h2 : (((ε z : ↥(perfectCore M₁)) : ↥(unitarySU p 1 F 3)) : GL (Fin 3) F) =
        (g : GL (Fin 3) F) * (((z : ↥(perfectCore M)) : ↥(unitarySU p 1 F 3)) : GL (Fin 3) F) *
          (g : GL (Fin 3) F)⁻¹ := rfl
    rw [h2] at h1
    have hcen : Subgroup.center (GL (Fin 3) F) = StatedScalars (Fin 3) F :=
      Matrix.GeneralLinearGroup.center_eq_range_scalar
    rw [← hcen] at h1 ⊢
    set z' : GL (Fin 3) F := (((z : ↥(perfectCore M)) : ↥(unitarySU p 1 F 3)) : GL (Fin 3) F)
      with hz'
    have hzz : (g : GL (Fin 3) F) * z' * (g : GL (Fin 3) F)⁻¹ = z' := by
      have := (Subgroup.mem_center_iff.mp h1) (g : GL (Fin 3) F)
      calc (g : GL (Fin 3) F) * z' * (g : GL (Fin 3) F)⁻¹
          = (g : GL (Fin 3) F)⁻¹ * ((g : GL (Fin 3) F) * ((g : GL (Fin 3) F) * z' *
              (g : GL (Fin 3) F)⁻¹)) := by group
        _ = (g : GL (Fin 3) F)⁻¹ * (((g : GL (Fin 3) F) * z' * (g : GL (Fin 3) F)⁻¹) *
              (g : GL (Fin 3) F)) := by rw [this]
        _ = z' := by group
    rw [hzz] at h1
    exact h1


end CFSG.Quasithin.A312U3
