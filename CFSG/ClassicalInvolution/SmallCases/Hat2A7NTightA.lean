module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7NDefs

public section

namespace CFSG.ClassicalInvolution.Hat2A7N

open CFSG.Open CFSG.ClassicalInvolution.Hat2A7

section Clique

variable {F : Type} [Group F] [Finite F] {K : Subgroup F} {z : F}

omit [Finite F] in
theorem TightSettingN.centralizer_ne_top (S : TightSettingN F K z) {x : F} (hx : x ≠ 1) :
    Subgroup.centralizer ({x} : Set F) ≠ ⊤ := by
  intro h
  apply hx
  apply S.center_trivial
  intro y
  have : y ∈ Subgroup.centralizer ({x} : Set F) := h ▸ Subgroup.mem_top y
  exact Subgroup.mem_centralizer_iff.mp this x rfl

omit [Finite F] in
theorem TightSettingN.mem_memb (S : TightSettingN F K z) {u : F} (hu : u ∈ classOf z) :
    u ∈ memb K z u :=
  (S.tight.memb hu).classical.mem

omit [Finite F] in
theorem TightSettingN.ne_one (S : TightSettingN F K z) {u : F} (hu : u ∈ classOf z) : u ≠ 1 := by
  intro h
  have := orderOf_eq_two_of_mem_classOf S.tight hu
  rw [h, orderOf_one] at this
  omega

omit [Finite F] in
theorem TightSettingN.isConjSubgroup_memb (S : TightSettingN F K z) {u : F} (hu : u ∈ classOf z) :
    IsConjSubgroup K (memb K z u) := by
  obtain ⟨g, hg⟩ := hu
  rw [memb_eq S.tight hg]
  exact isConjSubgroup_map_conj K g

omit [Finite F] in
theorem TightSettingN.commOrEq_of_le_centralizer (S : TightSettingN F K z) {x : F}
    (hx : orderOf x = 2) (hxE : IsCommProd z x) {u v : F} (hu : u ∈ classOf z)
    (hv : v ∈ classOf z) (hux : memb K z u ≤ Subgroup.centralizer ({x} : Set F))
    (hvx : memb K z v ≤ Subgroup.centralizer ({x} : Set F)) :
    CommOrEq (memb K z u) (memb K z v) :=
  S.IH x hx hxE _ _ u v (Or.inl (S.isConjSubgroup_memb hu)) (S.isConjSubgroup_memb hv)
    ((S.tight.memb hu).classical.mono hux le_top) ((S.tight.memb hv).classical.mono hvx le_top)

omit [Finite F] in
theorem TightSettingN.mem_centralizer_of_commOrEq (S : TightSettingN F K z) {u v : F}
    (hv : v ∈ classOf z) (h : CommOrEq (memb K z u) (memb K z v)) {k : F} (hk : k ∈ memb K z u) :
    k * v = v * k := by
  rcases h with h | h
  · rw [h] at hk
    exact (S.tight.memb hv).classical.mul_comm_of_mem hk
  · exact h k hk v (S.mem_memb hv)

omit [Finite F] in
theorem TightSettingN.commOrEq_trans (S : TightSettingN F K z) {u v w : F} (hu : u ∈ classOf z)
    (hv : v ∈ classOf z) (hw : w ∈ classOf z) (h1 : CommOrEq (memb K z u) (memb K z v))
    (h2 : CommOrEq (memb K z v) (memb K z w)) : CommOrEq (memb K z u) (memb K z w) := by
  have hc : ∀ {a : F}, a ∈ classOf z → CommOrEq (memb K z a) (memb K z v) →
      memb K z a ≤ Subgroup.centralizer ({v} : Set F) := fun {a} _ h k hk =>
    Subgroup.mem_centralizer_iff.mpr (fun x hx => by
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact (S.mem_centralizer_of_commOrEq hv h hk).symm)
  exact S.commOrEq_of_le_centralizer (orderOf_eq_two_of_mem_classOf S.tight hv)
    (isCommProd_of_mem_classOf hv) hu hw (hc hu h1) (hc hw h2.symm)

omit [Finite F] in
theorem TightSettingN.self_mem_Zset (S : TightSettingN F K z) : z ∈ Zset K z :=
  ⟨mem_classOf_self z, by rw [memb_self S.tight]; exact CommOrEq.refl K⟩

omit [Finite F] in
theorem TightSettingN.commOrEq_of_mem_Zset (S : TightSettingN F K z) {u v : F}
    (hu : u ∈ Zset K z) (hv : v ∈ Zset K z) : CommOrEq (memb K z u) (memb K z v) := by
  refine S.commOrEq_trans hu.1 (mem_classOf_self z) hv.1 ?_ ?_
  · rw [memb_self S.tight]; exact hu.2.symm
  · rw [memb_self S.tight]; exact hv.2

omit [Finite F] in
theorem TightSettingN.mem_centralizer_memb_of_mem_Zset (S : TightSettingN F K z) {u v : F}
    (hu : u ∈ Zset K z) (hv : v ∈ Zset K z) :
    u ∈ Subgroup.centralizer ((memb K z v : Subgroup F) : Set F) := by
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  exact S.mem_centralizer_of_commOrEq hu.1 (S.commOrEq_of_mem_Zset hv hu) hk


omit [Finite F] in
theorem TightSettingN.Zset_commute (S : TightSettingN F K z) {u v : F} (hu : u ∈ Zset K z)
    (hv : v ∈ Zset K z) : u * v = v * u :=
  (Subgroup.mem_centralizer_iff.mp (S.mem_centralizer_memb_of_mem_Zset hu hv) v
    (S.mem_memb hv.1)).symm


omit [Finite F] in
theorem TightSettingN.E_centralizes (S : TightSettingN F K z) {x w : F}
    (hx : x ∈ Subgroup.closure (Zset K z)) (hw : w ∈ Zset K z) : x * w = w * x := by
  have : Subgroup.closure (Zset K z) ≤ Subgroup.centralizer ({w} : Set F) := by
    rw [Subgroup.closure_le]
    intro u hu
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact (S.Zset_commute hu hw).symm
  exact (Subgroup.mem_centralizer_iff.mp (this hx) w rfl).symm

omit [Finite F] in
theorem TightSettingN.E_comm (S : TightSettingN F K z) {x y : F}
    (hx : x ∈ Subgroup.closure (Zset K z)) (hy : y ∈ Subgroup.closure (Zset K z)) :
    x * y = y * x := by
  have : Subgroup.closure (Zset K z) ≤ Subgroup.centralizer ({x} : Set F) := by
    rw [Subgroup.closure_le]
    intro w hw
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact S.E_centralizes hx hw
  exact Subgroup.mem_centralizer_iff.mp (this hy) x rfl

omit [Finite F] in
theorem TightSettingN.E_sq (S : TightSettingN F K z) {x : F}
    (hx : x ∈ Subgroup.closure (Zset K z)) : x * x = 1 := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    have := orderOf_eq_two_of_mem_classOf S.tight hx.1
    have h2 := pow_orderOf_eq_one x
    rwa [this, pow_two] at h2
  | one => simp
  | mul x y hx hy ihx ihy =>
    have hc := S.E_comm hx hy
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [← hc]
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [ihx, ihy]; group
  | inv x hx ih =>
    calc x⁻¹ * x⁻¹ = (x * x)⁻¹ := by group
      _ = 1 := by rw [ih]; simp


end Clique

end CFSG.ClassicalInvolution.Hat2A7N
