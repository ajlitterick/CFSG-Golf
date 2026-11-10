module

public import CFSG.Quasithin.H13.A5S136l

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model

theorem W4_mul_pact_c234 : W4 * pact c234 W4 * pact c234⁻¹ W4 = E12 := by decide +kernel

theorem W4_mul_pact_c234_inv : W4 * pact c234⁻¹ W4 * pact c234 W4 = E12 := by decide +kernel

theorem coe_conjAct_apply' {G : Type} [Group G] {U : Subgroup G}
    (g : ↥(Subgroup.normalizer (U : Set G))) (u : ↥U) :
    ((conjAct U g u : ↥U) : G) = (g : G) * u * (g : G)⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe U _ u

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)

theorem Gv_le_normalizer_Uv :
    Subgroup.centralizer ({S.v12} : Set G) ≤ Subgroup.normalizer (S.Uv : Set G) :=
  le_normalizer_conjClosure _ _

theorem Lv_le_Gv : S.Lv ≤ Subgroup.centralizer ({S.v12} : Set G) := by
  rw [Lv, oTwoRes_eq_oTwoUpper]
  exact (oTwoUpper_le _).trans inf_le_right

theorem v12_mem_Uv : S.v12 ∈ S.Uv :=
  S.Vv_le_Uv (S.mem_Vv.2 ⟨S.v12_mem_V, by rw [S.psi_v12]; decide +kernel⟩)

@[expose] noncomputable def vU : ↥S.Uv := ⟨S.v12, S.v12_mem_Uv⟩

theorem apply_vU {a : MulAut ↥S.Uv}
    (ha : a ∈ autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv) : a S.vU = S.vU := by
  obtain ⟨g, hg, rfl⟩ := ha
  have hgv : (g : G) ∈ Subgroup.centralizer ({S.v12} : Set G) := Subgroup.mem_subgroupOf.mp hg
  apply Subtype.ext
  rw [coe_conjAct_apply']
  have h := Subgroup.mem_centralizer_singleton_iff.mp hgv
  show (g : G) * S.v12 * (g : G)⁻¹ = S.v12
  rw [h, mul_inv_cancel_right]

theorem exists_apply_ne_zU_of_normal {X : Subgroup (MulAut ↥S.Uv)}
    (hXG : autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv ≤
      Subgroup.normalizer (X : Set (MulAut ↥S.Uv))) (hX : X ≠ ⊥) :
    ∃ x ∈ X, x S.zU ≠ S.zU := by
  by_contra hcon
  push Not at hcon
  apply hX
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  set E : Subgroup G :=
    (MonoidHom.eqLocus (x : ↥S.Uv ≃* ↥S.Uv).toMonoidHom (MonoidHom.id _)).map S.Uv.subtype
    with hE
  have hUE : S.Uv ≤ E := by
    refine conjClosure_le fun g hg w hw => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    have hgN := S.Gv_le_normalizer_Uv hg
    set c : MulAut ↥S.Uv := conjAct S.Uv ⟨g, hgN⟩ with hcdef
    have hc : c ∈ autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv :=
      ⟨⟨g, hgN⟩, Subgroup.mem_subgroupOf.mpr hg, rfl⟩
    have hcx : c⁻¹ * x * c ∈ X := by
      have := (Subgroup.mem_normalizer_iff.mp (hXG (Subgroup.inv_mem _ hc)) x).mp hx
      simpa using this
    have h1 : (c⁻¹ * x * c) S.zU = S.zU := hcon _ hcx
    have h2 : x (c S.zU) = c S.zU := by
      have h3 := congrArg c h1
      simpa [MulAut.mul_apply] using h3
    have h3 : ((c S.zU : ↥S.Uv) : G) = g * S.z * g⁻¹ := coe_conjAct_apply' _ _
    refine ⟨(c S.zU) ^ k, ?_, ?_⟩
    · show (x : ↥S.Uv ≃* ↥S.Uv).toMonoidHom ((c S.zU) ^ k) = (c S.zU) ^ k
      rw [map_zpow]
      exact congrArg (· ^ k) h2
    · show (((c S.zU) ^ k : ↥S.Uv) : G) = g * S.z ^ k * g⁻¹
      rw [Subgroup.coe_zpow, h3, conj_zpow]
  ext u
  obtain ⟨u', hu', hu'eq⟩ := hUE u.2
  have hu'u : u' = u := Subtype.ext hu'eq
  rw [← hu'u, MulAut.one_apply]
  exact congrArg Subtype.val (show x u' = u' from hu')

theorem v12_eq_mul (l : ↥(Subgroup.normalizer (V : Set G)))
    (hl : S.frame.ρ l = c234 ∨ S.frame.ρ l = c234⁻¹) :
    S.v12 = S.z * ((l : G) * S.z * (l : G)⁻¹) * ((l : G)⁻¹ * S.z * (l : G)) := by
  have hm1 : (l : G) * S.z * (l : G)⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.mp l.2 _).mp S.z_mem_V
  have hm2 : (l : G)⁻¹ * S.z * (l : G) ∈ V := by
    have := (Subgroup.mem_normalizer_iff.mp (l⁻¹).2 S.z).mp S.z_mem_V
    simpa using this
  have h1 : S.frame.ψ ⟨(l : G) * S.z * (l : G)⁻¹, hm1⟩ = pact (S.frame.ρ l) W4 := by
    rw [← S.psi_z]
    exact S.psi_conj l ⟨S.z, S.z_mem_V⟩
  have h2 : S.frame.ψ ⟨(l : G)⁻¹ * S.z * (l : G), hm2⟩ = pact (S.frame.ρ l)⁻¹ W4 := by
    rw [← S.psi_z, ← map_inv]
    have := S.psi_conj l⁻¹ ⟨S.z, S.z_mem_V⟩
    convert this using 3
    simp
  have hmem : S.z * ((l : G) * S.z * (l : G)⁻¹) * ((l : G)⁻¹ * S.z * (l : G)) ∈ V :=
    V.mul_mem (V.mul_mem S.z_mem_V hm1) hm2
  have key : S.frame.ψ ⟨S.v12, S.v12_mem_V⟩ = S.frame.ψ ⟨_, hmem⟩ := by
    have e : (⟨_, hmem⟩ : ↥V) = ⟨S.z, S.z_mem_V⟩ * ⟨_, hm1⟩ * ⟨_, hm2⟩ := rfl
    rw [e, map_mul, map_mul, h1, h2, S.psi_z, S.psi_v12]
    rcases hl with hl | hl
    · rw [hl, W4_mul_pact_c234]
    · rw [hl, inv_inv, W4_mul_pact_c234_inv]
  exact congrArg Subtype.val (S.frame.ψ.injective key)

theorem vU_eq_mul_conjAct (l₀ : ↥(Subgroup.normalizer (V : Set G)))
    (hl₀σ : S.frame.ρ l₀ = c234 ∨ S.frame.ρ l₀ = c234⁻¹)
    (hl₀N : (l₀ : G) ∈ Subgroup.normalizer (S.Uv : Set G)) :
    S.vU = S.zU * conjAct S.Uv ⟨l₀, hl₀N⟩ S.zU * (conjAct S.Uv ⟨l₀, hl₀N⟩)⁻¹ S.zU := by
  apply Subtype.ext
  have h1 : ((conjAct S.Uv ⟨l₀, hl₀N⟩ S.zU : ↥S.Uv) : G) = (l₀ : G) * S.z * (l₀ : G)⁻¹ :=
    coe_conjAct_apply' _ _
  have h2 : (((conjAct S.Uv ⟨l₀, hl₀N⟩)⁻¹ S.zU : ↥S.Uv) : G) =
      (l₀ : G)⁻¹ * S.z * (l₀ : G) := by
    rw [← map_inv, coe_conjAct_apply']
    show (l₀ : G)⁻¹ * S.z * ((l₀ : G)⁻¹)⁻¹ = _
    rw [inv_inv]
  show S.v12 = S.z * ((conjAct S.Uv ⟨l₀, hl₀N⟩ S.zU : ↥S.Uv) : G) *
    (((conjAct S.Uv ⟨l₀, hl₀N⟩)⁻¹ S.zU : ↥S.Uv) : G)
  rw [h1, h2]
  exact S.v12_eq_mul l₀ hl₀σ


end Setting

end CFSG.Quasithin.H13.A5
