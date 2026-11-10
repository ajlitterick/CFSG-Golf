module

public import CFSG.Quasithin.H13.A5Producer
public import CFSG.Quasithin.Background.B2FactorizationBridge
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.GH74.QTGen4.U42

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.A5Model CFSG.Blueprint
open CFSG.Quasithin.H13 CFSG.Quasithin.H13.A5

@[expose] def paE : Equiv.Perm (Fin 5) := Equiv.swap 0 1 * Equiv.swap 2 3

@[expose] def t3 : Equiv.Perm (Fin 5) := Equiv.swap 1 4 * Equiv.swap 1 2

theorem paE_eq : paE = pa := rfl

theorem t3_cube : t3 * t3 * t3 = 1 := by decide

theorem pa_sq : pa * pa = 1 := by decide

theorem pa_t3_pow_five : (pa * t3) ^ 5 = 1 := by decide


theorem sq_W5 (x : W5) : x * x = 1 := by
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  funext i
  have h : ∀ a : ZMod 2, a + a = 0 := by decide
  simpa using h _

theorem pact_mul_apply (σ τ : Equiv.Perm (Fin 5)) (x : W5) :
    pact (σ * τ) x = pact σ (pact τ x) := by
  rw [map_mul]
  rfl

theorem pact_one_apply (x : W5) : pact 1 x = x := by
  rw [map_one]
  rfl

theorem delta_mul (v : W5) (σ τ : Equiv.Perm (Fin 5)) :
    v * pact (σ * τ) v = (v * pact σ v) * pact σ (v * pact τ v) := by
  have e1 : pact σ (v * pact τ v) = pact σ v * pact (σ * τ) v := by
    rw [map_mul (pact σ) v (pact τ v), pact_mul_apply]
  rw [e1, pact_mul_apply]
  have h := sq_W5 (pact σ v)
  simp only [mul_assoc]
  rw [← mul_assoc (pact σ v) (pact σ v), h, one_mul]

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
theorem H1_t3 : ∀ x y : W5,
    x * pact pa x = 1 →
    y * pact t3 y * pact (t3 * t3) y = 1 →
    (x * pact pa y) * pact (pa * t3) (x * pact pa y) *
      pact ((pa * t3) * (pa * t3)) (x * pact pa y) *
      pact ((pa * t3) * (pa * t3) * (pa * t3)) (x * pact pa y) *
      pact ((pa * t3) * (pa * t3) * (pa * t3) * (pa * t3)) (x * pact pa y) = 1 →
    ∃ v : W5, x = v * pact pa v ∧ y = v * pact t3 v := by
  decide +kernel

def genE (x y : Equiv.Perm (Fin 5)) : ℕ → Finset (Equiv.Perm (Fin 5))
  | 0 => {1}
  | n + 1 =>
    let X := genE x y n
    X ∪ X.image (· * x) ∪ X.image (· * y)

theorem genE_mem (x y : Equiv.Perm (Fin 5)) : ∀ n : ℕ, ∀ z ∈ genE x y n,
    z ∈ Subgroup.closure ({x, y} : Set (Equiv.Perm (Fin 5)))
  | 0, z, hz => by
    simp only [genE, Finset.mem_singleton] at hz
    subst hz
    exact Subgroup.one_mem _
  | n + 1, z, hz => by
    simp only [genE, Finset.mem_union, Finset.mem_image] at hz
    rcases hz with (hz | ⟨w, hw, rfl⟩) | ⟨w, hw, rfl⟩
    · exact genE_mem x y n z hz
    · exact Subgroup.mul_mem _ (genE_mem x y n w hw) (Subgroup.subset_closure (by simp))
    · exact Subgroup.mul_mem _ (genE_mem x y n w hw) (Subgroup.subset_closure (by simp))

theorem mem_genE_of_sign : ∀ σ : Equiv.Perm (Fin 5), σ.sign = 1 → σ ∈ genE paE t3 12 := by
  decide +kernel

theorem alt_gen_pt : ∀ σ : Equiv.Perm (Fin 5), σ.sign = 1 →
    σ ∈ Subgroup.closure ({pa, t3} : Set (Equiv.Perm (Fin 5))) := by
  intro σ hσ
  have h := genE_mem paE t3 12 σ (mem_genE_of_sign σ hσ)
  rw [paE_eq] at h
  exact h

theorem sup_decomp_V {G : Type} [Group G] {V K : Subgroup G}
    (hN : ∀ q : G, q ∈ V ⊔ K → ∀ v ∈ V, q * v * q⁻¹ ∈ V) {q : G} (hq : q ∈ V ⊔ K) :
    ∃ a ∈ K, ∃ v ∈ V, a * v = q := by
  let P : Subgroup G :=
    { carrier := {g | ∃ a ∈ K, ∃ v ∈ V, a * v = g}
      one_mem' := ⟨1, K.one_mem, 1, V.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨a1, ha1, v1, hv1, rfl⟩ ⟨a2, ha2, v2, hv2, rfl⟩
        have hc : a2⁻¹ * v1 * a2⁻¹⁻¹ ∈ V :=
          hN a2⁻¹ (Subgroup.mem_sup_right (K.inv_mem ha2)) v1 hv1
        refine ⟨a1 * a2, K.mul_mem ha1 ha2, a2⁻¹ * v1 * a2⁻¹⁻¹ * v2,
          V.mul_mem hc hv2, by group⟩
      inv_mem' := by
        rintro _ ⟨a, ha, v, hv, rfl⟩
        refine ⟨a⁻¹, K.inv_mem ha, a * v⁻¹ * a⁻¹, hN a (Subgroup.mem_sup_right ha) v⁻¹
          (V.inv_mem hv), by group⟩ }
  have hP : V ⊔ K ≤ P :=
    sup_le (fun v hv => ⟨1, K.one_mem, v, hv, by simp⟩)
      (fun a ha => ⟨a, ha, 1, V.one_mem, by simp⟩)
  obtain ⟨a, ha, v, hv, h⟩ : ∃ a ∈ K, ∃ v ∈ V, a * v = q := hP hq
  exact ⟨a, ha, v, hv, h⟩

theorem pa_sign_one : pa.sign = 1 := by
  rw [← paE_eq]
  show Equiv.Perm.sign (Equiv.swap (0 : Fin 5) 1 * Equiv.swap (2 : Fin 5) 3) = 1
  rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (show (0 : Fin 5) ≠ 1 by decide),
    Equiv.Perm.sign_swap (show (2 : Fin 5) ≠ 3 by decide)]
  rfl

theorem t3_sign_one : t3.sign = 1 := by
  show Equiv.Perm.sign (Equiv.swap (1 : Fin 5) 4 * Equiv.swap (1 : Fin 5) 2) = 1
  rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (show (1 : Fin 5) ≠ 4 by decide),
    Equiv.Perm.sign_swap (show (1 : Fin 5) ≠ 2 by decide)]
  rfl

theorem pa_t3_sign_one : (pa * t3).sign = 1 := by
  rw [Equiv.Perm.sign_mul, pa_sign_one, t3_sign_one, mul_one]

theorem cocycle_pow_five_alt (c : Equiv.Perm (Fin 5) → W5)
    (hcm : ∀ σ τ : Equiv.Perm (Fin 5), σ.sign = 1 → τ.sign = 1 →
      c (σ * τ) = c σ * pact σ (c τ))
    (w : Equiv.Perm (Fin 5)) (hw : w.sign = 1) :
    c (w ^ 5) = c w * pact w (c w) * pact (w * w) (c w) * pact (w * w * w) (c w) *
      pact (w * w * w * w) (c w) := by
  have s2 : (w * w).sign = 1 := by rw [Equiv.Perm.sign_mul, hw, mul_one]
  have s3 : (w * (w * w)).sign = 1 := by rw [Equiv.Perm.sign_mul, s2, hw, mul_one]
  have s4 : (w * (w * (w * w))).sign = 1 := by rw [Equiv.Perm.sign_mul, s3, hw, mul_one]
  rw [show w ^ 5 = w * (w * (w * (w * w))) by simp only [pow_succ, pow_zero, one_mul, mul_assoc],
    hcm w (w * (w * (w * w))) hw s4, hcm w (w * (w * w)) hw s3, hcm w (w * w) hw s2,
    hcm w w hw hw]
  simp only [map_mul, MulAut.mul_apply, mul_assoc]

theorem cocycle_coboundary_alt (c : Equiv.Perm (Fin 5) → W5) (hc1 : c 1 = 1)
    (hcm : ∀ σ τ : Equiv.Perm (Fin 5), σ.sign = 1 → τ.sign = 1 →
      c (σ * τ) = c σ * pact σ (c τ)) :
    ∃ v : W5, ∀ σ : Equiv.Perm (Fin 5), σ.sign = 1 → c σ = v * pact σ v := by
  have hx : c pa * pact pa (c pa) = 1 := by
    have h := hcm pa pa pa_sign_one pa_sign_one
    rw [pa_sq, hc1] at h
    exact h.symm
  have hy : c t3 * pact t3 (c t3) * pact (t3 * t3) (c t3) = 1 := by
    have h := hcm (t3 * t3) t3 (by rw [Equiv.Perm.sign_mul, t3_sign_one, mul_one]) t3_sign_one
    rw [t3_cube, hc1, hcm t3 t3 t3_sign_one t3_sign_one] at h
    exact h.symm
  have hw : c pa * pact pa (c t3) * pact (pa * t3) (c pa * pact pa (c t3)) *
      pact (pa * t3 * (pa * t3)) (c pa * pact pa (c t3)) *
      pact (pa * t3 * (pa * t3) * (pa * t3)) (c pa * pact pa (c t3)) *
      pact (pa * t3 * (pa * t3) * (pa * t3) * (pa * t3)) (c pa * pact pa (c t3)) = 1 := by
    have h := cocycle_pow_five_alt c hcm (pa * t3) pa_t3_sign_one
    rw [pa_t3_pow_five, hc1, hcm pa t3 pa_sign_one t3_sign_one] at h
    exact h.symm
  obtain ⟨v, hv1, hv2⟩ := H1_t3 (c pa) (c t3) hx hy hw
  have hcl : ∀ σ ∈ Subgroup.closure ({pa, t3} : Set (Equiv.Perm (Fin 5))), σ.sign = 1 := by
    have hle : Subgroup.closure ({pa, t3} : Set (Equiv.Perm (Fin 5))) ≤
        Equiv.Perm.sign.ker := by
      rw [Subgroup.closure_le]
      intro x hx'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx'
      rcases hx' with rfl | rfl
      · exact MonoidHom.mem_ker.mpr pa_sign_one
      · exact MonoidHom.mem_ker.mpr t3_sign_one
    intro σ hσ
    exact MonoidHom.mem_ker.mp (hle hσ)
  have hP : ∀ σ ∈ Subgroup.closure ({pa, t3} : Set (Equiv.Perm (Fin 5))),
      c σ = v * pact σ v := by
    intro σ hσ
    induction hσ using Subgroup.closure_induction with
    | mem x hx' =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx'
      rcases hx' with rfl | rfl
      · exact hv1
      · exact hv2
    | one => rw [hc1, pact_one_apply, sq_W5]
    | mul x y hx0 hy0 hx' hy' =>
      rw [hcm x y (hcl x hx0) (hcl y hy0), hx', hy']
      exact (delta_mul v x y).symm
    | inv x hx0 hx' =>
      have hinv : x⁻¹.sign = 1 := by rw [Equiv.Perm.sign_inv, hcl x hx0]
      have h := hcm x x⁻¹ (hcl x hx0) hinv
      rw [mul_inv_cancel, hc1] at h
      have e : pact x (c x⁻¹) = c x := by
        calc pact x (c x⁻¹) = (c x * c x) * pact x (c x⁻¹) := by rw [sq_W5, one_mul]
          _ = c x * (c x * pact x (c x⁻¹)) := by rw [mul_assoc]
          _ = c x := by rw [← h, mul_one]
      have e2 : c x⁻¹ = pact x⁻¹ (c x) := by
        rw [← e, ← pact_mul_apply, inv_mul_cancel, pact_one_apply]
      rw [e2, hx', map_mul (pact x⁻¹) v (pact x v), ← pact_mul_apply, inv_mul_cancel,
        pact_one_apply, mul_comm]
  exact ⟨v, fun σ hσ => hP σ (alt_gen_pt σ hσ)⟩

section Complement

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : A5.Setting G T L V)
include S

open Classical in
noncomputable def rgL (g : G) : Equiv.Perm (Fin 5) :=
  if hg : g ∈ L then S.frame.ρ ⟨g, S.frame.L_le hg⟩ else 1

theorem rgL_of_mem {g : G} (hg : g ∈ L) : rgL S g = S.frame.ρ ⟨g, S.frame.L_le hg⟩ := by
  unfold rgL
  simp [hg]

theorem rgL_mul {g h : G} (hg : g ∈ L) (hh : h ∈ L) :
    rgL S (g * h) = rgL S g * rgL S h := by
  rw [rgL_of_mem S hg, rgL_of_mem S hh, rgL_of_mem S (L.mul_mem hg hh), ← map_mul]
  rfl

theorem rgL_inv {g : G} (hg : g ∈ L) : rgL S g⁻¹ = (rgL S g)⁻¹ := by
  rw [rgL_of_mem S hg, rgL_of_mem S (L.inv_mem hg), ← map_inv]
  rfl

theorem rgL_V (hVL : V ≤ L) {v : G} (hv : v ∈ V) : rgL S v = 1 := by
  rw [rgL_of_mem S (hVL hv)]
  refine S.frame.rho_eq_one_of_mem _ ?_
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  exact B2F.isElemAbelian_comm S.elemAbelian_V hw hv


theorem mem_V_of_rgL_eq_one (hO : pCoreOf 2 (L ⊔ T) = V) {g : G} (hg : g ∈ L)
    (h1 : rgL S g = 1) : g ∈ V := by
  rw [rgL_of_mem S hg] at h1
  have hc : g ∈ Subgroup.centralizer (V : Set G) :=
    S.frame.mem_centralizer_of_rho ⟨g, S.frame.L_le hg⟩ h1
  have hmem : g ∈ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) := ⟨Subgroup.mem_sup_left hg, hc⟩
  rw [S.cLT, hO] at hmem
  exact hmem


theorem exists_rgL_eq {K : Subgroup G} (hVL : V ≤ L) (hK : K ≤ L) (hKL : V ⊔ K = L)
    {σ : Equiv.Perm (Fin 5)} (hσ : σ.sign = 1) : ∃ a ∈ K, rgL S a = σ := by
  obtain ⟨g, hgL, hg⟩ := (S.frame.image_L σ).2 hσ
  have hq : (g : G) ∈ V ⊔ K := by rw [hKL]; exact hgL
  have hN : ∀ q : G, q ∈ V ⊔ K → ∀ v ∈ V, q * v * q⁻¹ ∈ V := by
    intro q hq' v hv
    have hqL : q ∈ L := by rw [← hKL]; exact hq'
    exact (Subgroup.mem_normalizer_iff.mp (S.frame.L_le hqL) v).mp hv
  obtain ⟨a, ha, v, hv, hav⟩ := sup_decomp_V hN hq
  have hsplit : rgL S (g : G) = rgL S a * rgL S v := by
    rw [← hav, rgL_mul S (hK ha) (hVL hv)]
  rw [rgL_V S hVL hv, mul_one, rgL_of_mem S hgL] at hsplit
  exact ⟨a, ha, by rw [← hsplit]; exact hg⟩

open Classical in
noncomputable def pickE (K : Subgroup G) (σ : Equiv.Perm (Fin 5)) : G :=
  Classical.epsilon (fun a : G => a ∈ K ∧ rgL S a = σ)

theorem pickE_spec {K : Subgroup G} (hVL : V ≤ L) (hK : K ≤ L) (hKL : V ⊔ K = L)
    {σ : Equiv.Perm (Fin 5)} (hσ : σ.sign = 1) :
    pickE S K σ ∈ K ∧ rgL S (pickE S K σ) = σ := by
  obtain ⟨a, ha, h⟩ := exists_rgL_eq S hVL hK hKL hσ
  exact Classical.epsilon_spec (p := fun b : G => b ∈ K ∧ rgL S b = σ) ⟨a, ha, h⟩

theorem u_mem (hO : pCoreOf 2 (L ⊔ T) = V) (hVL : V ≤ L) {A B : Subgroup G}
    (hA : A ≤ L) (hAL : V ⊔ A = L) (hB : B ≤ L) (hBL : V ⊔ B = L)
    {σ : Equiv.Perm (Fin 5)} (hσ : σ.sign = 1) :
    pickE S B σ * (pickE S A σ)⁻¹ ∈ V := by
  obtain ⟨hbB, hbρ⟩ := pickE_spec S hVL hB hBL hσ
  obtain ⟨haA, haρ⟩ := pickE_spec S hVL hA hAL hσ
  apply mem_V_of_rgL_eq_one S hO (L.mul_mem (hB hbB) (L.inv_mem (hA haA)))
  rw [rgL_mul S (hB hbB) (L.inv_mem (hA haA)), rgL_inv S (hA haA), hbρ, haρ, mul_inv_cancel]


end Complement

end CFSG.GH74.QTGen4.U42

end
