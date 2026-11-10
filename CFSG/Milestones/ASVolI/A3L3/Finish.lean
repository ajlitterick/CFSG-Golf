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
