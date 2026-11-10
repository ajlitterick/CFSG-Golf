module

public import CFSG.Quasithin.Background.F7Basic
public import CFSG.Quasithin.Background.E1Inherit

public section

namespace CFSG.Quasithin.RonanF713

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7

variable {G : Type*} [Group G]


theorem isSylowTwoOf_pCoreOf_le_loc {T H : Subgroup G} (h : IsSylowTwoOf T H) :
    pCoreOf 2 H ≤ T := by
  obtain ⟨S, hS⟩ := F7.isSylowTwoOf_exists_sylow h
  have : (CFSG.pCore 2 ↥H).Normal := CFSG.pCore_normal (p := 2) (G := ↥H)
  have hle : CFSG.pCore 2 ↥H ≤ (S : Subgroup ↥H) :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥H)).le_sylow_of_normal S
  rintro _ ⟨y, hy, rfl⟩
  have := hle hy
  rw [hS] at this
  simpa [Subgroup.mem_subgroupOf] using this

theorem isSylowTwoOf_exists_conj_le_loc {T H : Subgroup G} [Finite ↥H] (h : IsSylowTwoOf T H)
    {P : Subgroup G} (hPH : P ≤ H) (hP : IsPGroup 2 P) : ∃ x ∈ H, P ≤ conjSub x T := by
  obtain ⟨S, hS⟩ := F7.isSylowTwoOf_exists_sylow h
  have hP' : IsPGroup 2 (P.subgroupOf H) :=
    hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPH).symm
  obtain ⟨Q, hQ⟩ := hP'.exists_le_sylow
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq H S Q
  refine ⟨x, x.2, fun y hy => ?_⟩
  have h1 : (⟨y, hPH hy⟩ : H) ∈ Q := hQ (by simpa [Subgroup.mem_subgroupOf] using hy)
  rw [← hx] at h1
  have h2 : (⟨y, hPH hy⟩ : H) ∈ ((x • S : Sylow 2 H) : Subgroup H) := h1
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h2
  have h3 : (MulAut.conj x)⁻¹ • (⟨y, hPH hy⟩ : H) ∈ (S : Subgroup H) := h2
  rw [hS] at h3
  rw [mem_conjSub]
  simpa [Subgroup.mem_subgroupOf, MulAut.conj_inv_apply, mul_assoc] using h3


end CFSG.Quasithin.RonanF713
