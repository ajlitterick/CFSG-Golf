module

public import CFSG.Milestones.ASVolI.A3L3.Glue
public import CFSG.Milestones.ASVolI.A3L3.Sylow

public section

namespace CFSG.ASVolI

open Matrix CFSG.RankThree.SubgroupLists CFSG.GH74.GLS.IVK.Proofs2.Lemma41aL3
open scoped Pointwise

@[expose] noncomputable def burnsideA315y_equivMap {G Y : Type} [Group G] [Group Y] (f : G →* Y)
    (H : Subgroup G) (hker : ∀ h ∈ H, f h = 1 → h = 1) : ↥H ≃* ↥(H.map f) :=
  (MonoidHom.ofInjective (f := f.comp H.subtype) (by
    rw [injective_iff_map_eq_one]
    intro h hh
    exact Subtype.ext (hker h h.2 hh))).trans
    (MulEquiv.subgroupCongr (by rw [← MonoidHom.map_range, Subgroup.range_subtype]))

theorem burnsideA315y_card_map_of_ker {G Y : Type} [Group G] [Group Y] (f : G →* Y)
    (H : Subgroup G) (hker : ∀ h ∈ H, f h = 1 → h = 1) : Nat.card ↥(H.map f) = Nat.card ↥H :=
  (Nat.card_congr (burnsideA315y_equivMap f H hker).toEquiv).symm


namespace burnsideA315y_Model

variable {F : Type} [Field F] {X : Type} [Group X] (M : burnsideA315y_Model F X)


theorem C₁_comm {g : ↥M.Γ} (hg : g ∈ M.C₁) :
    (g : GL (Fin 3) F) * negDiag3 F = negDiag3 F * g := by
  have h1 : ((g * M.zh : ↥M.Γ) : GL (Fin 3) F) = ((M.zh * g : ↥M.Γ) : GL (Fin 3) F) :=
    congrArg Subtype.val hg.2
  rwa [Subgroup.coe_mul, Subgroup.coe_mul, M.zh_val] at h1

theorem C₁_block {g : ↥M.Γ} (hg : g ∈ M.C₁) :
    ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 2 = 0 ∧
    ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 1 2 = 0 ∧
    ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 ∧
    ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 := by
  have hm : ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * diagonal ![-1, -1, 1] =
      diagonal ![-1, -1, 1] * ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    rw [← coe_negDiag3, ← Units.val_mul, M.C₁_comm hg, Units.val_mul]
  exact block_eq_zero_of_commute_negDiag M.two_ne hm

theorem C₁_22_ne {g : ↥M.Γ} (hg : g ∈ M.C₁) :
    ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 2 ≠ 0 := by
  intro h0
  obtain ⟨h02, h12, h20, h21⟩ := M.C₁_block hg
  have hd := hg.1
  rw [Matrix.det_fin_three, h02, h12, h20, h21, h0] at hd
  simp at hd

@[expose] noncomputable def e22 : ↥M.C₁ →* Fˣ where
  toFun g := Units.mk0 ((((g : ↥M.Γ) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 2)
    (M.C₁_22_ne g.2)
  map_one' := by
    apply Units.ext
    simp
  map_mul' a b := by
    apply Units.ext
    obtain ⟨-, -, a20, a21⟩ := M.C₁_block a.2
    obtain ⟨b02, b12, -, -⟩ := M.C₁_block b.2
    simp only [Subgroup.coe_mul, Units.val_mul, Units.val_mk0, Matrix.mul_apply, Fin.sum_univ_three,
      a20, a21, b02, b12, zero_mul, mul_zero, zero_add]


theorem c_K₀_ker {k : ↥M.Γ} (hk : k ∈ M.K₀) (h1 : M.c k = 1) : k = 1 := by
  obtain ⟨μ, hμ⟩ := M.exists_scalar_of_c_eq_one h1
  have h22 : ((k : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 2 = 1 := hk.2.2.2.2.2
  rw [hμ] at h22
  have hμ1 : μ = 1 := Units.ext (by simpa [Matrix.GeneralLinearGroup.coe_scalar] using h22)
  apply Subtype.ext
  rw [hμ, hμ1, map_one, Subgroup.coe_one]


theorem card_K : Nat.card ↥M.K = Nat.card ↥M.K₀ :=
  burnsideA315y_card_map_of_ker M.c M.K₀ (fun _ hk h1 => M.c_K₀_ker hk h1)


end burnsideA315y_Model


end CFSG.ASVolI
