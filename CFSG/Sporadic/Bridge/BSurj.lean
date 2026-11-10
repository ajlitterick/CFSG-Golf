module

public meta import CFSG.Sporadic.Bridge.BData
public import CFSG.Sporadic.Bridge.BOrder
public import CFSG.Sporadic.Bridge.BGlue9201
public import Certificates.Certificate9201
public meta import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Points

public section

namespace CFSG.Sporadic.Bridge.B

open CFSG.Blueprint CFSG.Monster.B CFSG.Monster.B.Pinned CFSG.Monster.B.Bin
  CFSG.Monster.B.Primes.Native TauCeti
open scoped Matrix

private theorem presentation_eq : SporadicName.B.presentation = pres := rfl


@[expose] def Wd.eval {G : Type*} [Monoid G] (g : ℕ → G) : Wd → G
  | .gen i => g i
  | .mul u v => u.eval g * v.eval g
  | .pow u e => u.eval g ^ e

theorem wA_eval {G : Type*} [Monoid G] (g : ℕ → G) :
    (wA : Wd).eval g = CFSG.KC.BM.B9201.apT g := by
  simp only [wA, wR, wS, Wd.chain, List.foldl_cons, List.foldl_nil, Wd.eval, CFSG.KC.BM.B9201.apT,
    CFSG.KC.BM.B9201.rT, CFSG.KC.BM.B9201.sT, CFSG.KC.BM.B9201.lp, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, mul_assoc]

theorem wB_eval {G : Type*} [Group G] {g : ℕ → G} (i : ∀ k < 11, (g k)⁻¹ = g k) :
    (wB : Wd).eval g = (CFSG.KC.BM.B9201.hT g)⁻¹ * (g 0 * g 1) * CFSG.KC.BM.B9201.hT g := by
  simp only [wB, wR, wS, wRi, wSi, Wd.chain, List.foldl_cons, List.foldl_nil, Wd.eval,
    CFSG.KC.BM.B9201.hT, CFSG.KC.BM.B9201.rT, CFSG.KC.BM.B9201.sT, CFSG.KC.BM.B9201.lp,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, ← inv_pow, mul_inv_rev,
    i 0 (by norm_num), i 1 (by norm_num), i 2 (by norm_num), i 3 (by norm_num), i 4 (by norm_num),
    i 5 (by norm_num), i 6 (by norm_num), i 7 (by norm_num), i 8 (by norm_num), i 9 (by norm_num),
    i 10 (by norm_num), mul_assoc]


theorem wordProd_flatten_replicate {G : Type*} [Group G] (g : ℕ → G) (base : List (ℕ × Bool))
    (k : ℕ) : wordProd g (List.replicate k base).flatten = wordProd g base ^ k := by
  induction k with
  | zero => simp [wordProd]
  | succ k ih =>
    rw [List.replicate_succ, List.flatten_cons]
    simp only [wordProd, List.map_append, List.prod_append] at ih ⊢
    rw [ih, pow_succ']


theorem conj_facts {A B a b : Mat} (ha : a.size ≤ 4370) (hb : b.size ≤ 4370)
    (h : conjChecks A B a b = true) :
    ∃ G Gi : Matrix (Fin 4370) (Fin 4370) (ZMod 2), cmat 4370 A * G = G * cmat 4370 a ∧
      cmat 4370 B * G = G * cmat 4370 b ∧ G * Gi = 1 := by
  unfold conjChecks at h
  dsimp only at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  set Gm := mulP 4370 (invM 4370 (spinMat 4370 (unitRow 4370 0) A B (treeOfText treeText)))
    (spinMat 4370 (rowOfText rowText) a b (treeOfText treeText)) with hGm
  set Gi := mulP 4370 (invM 4370 (spinMat 4370 (rowOfText rowText) a b (treeOfText treeText)))
    (spinMat 4370 (unitRow 4370 0) A B (treeOfText treeText)) with hGi
  have hGms : Gm.size ≤ 4370 := by
    rw [hGm, mulP_size, invM_size]
  have hGis : Gi.size ≤ 4370 := by
    rw [hGi, mulP_size, invM_size]
  refine ⟨cmat 4370 Gm, cmat 4370 Gi, ?_, ?_, ?_⟩
  · rw [← cmat_mulP 4370 A Gm hGms, ← cmat_mulP 4370 Gm a ha]
    exact cmat_eq_of_beq h1
  · rw [← cmat_mulP 4370 B Gm hGms, ← cmat_mulP 4370 Gm b hb]
    exact cmat_eq_of_beq h2
  · rw [← cmat_mulP 4370 Gm Gi hGis, cmat_eq_of_beq h3, cmat_idMat]

@[expose] noncomputable def tB
    (k : ℕ) : NativeSporadic.B := runG bProg bA₁ bA₂ (bTreg k)

structure BridgeFacts (rels : List (List (ℕ × Bool))) : Prop where
  inv : ∀ i < 11, tB i * tB i = 1
  rels : ∀ v ∈ rels, wordProd tB v = 1
  conj : ∃ Gu : GL (Fin 4370) (ZMod 2), glA₁ * Gu = Gu * bGL ((wA : Wd).eval tB) ∧
    glA₂ * Gu = Gu * bGL ((wB : Wd).eval tB)


theorem conj_words {T : ℕ → NativeSporadic.B}
    (hinv : ∀ i < 11, T i * T i = 1) {Gu : GL (Fin 4370) (ZMod 2)}
    (hA : glA₁ * Gu = Gu * bGL (CFSG.KC.BM.B9201.apT T))
    (hB : glA₂ * Gu =
      Gu * bGL ((CFSG.KC.BM.B9201.hT T)⁻¹ * (T 0 * T 1) * CFSG.KC.BM.B9201.hT T)) :
    glA₁ * Gu = Gu * bGL ((wA : Wd).eval T) ∧ glA₂ * Gu = Gu * bGL ((wB : Wd).eval T) := by
  have i : ∀ k < 11, (T k)⁻¹ = T k := fun k hk => inv_eq_of_mul_eq_one_right (hinv k hk)
  have eA : (wA : Wd).eval T = CFSG.KC.BM.B9201.apT T := wA_eval T
  have eB : (wB : Wd).eval T =
      (CFSG.KC.BM.B9201.hT T)⁻¹ * (T 0 * T 1) * CFSG.KC.BM.B9201.hT T := wB_eval i
  rw [eA, eB]
  exact ⟨hA, hB⟩

theorem bridgeFacts :
    BridgeFacts pres.relatorLetters := by
  obtain ⟨hinv, hrels, Gu, hA, hB⟩ :=
    R9201.bridge_gen (T := tB) (fun k _ => R9201.bMat_runG k) Certificates.certificate9201
  exact ⟨hinv, hrels, Gu, conj_words hinv hA hB⟩

noncomputable def φ :
    pres.Group →* NativeSporadic.B := presHom pres tB bridgeFacts.rels

theorem generatorCount_eq : pres.generatorCount = 11 := rfl

theorem tB_mem_range
    (k : ℕ) (hk : k < 11) : tB k ∈ φ.range :=
  ⟨presGen pres k, presHom_presGen pres tB bridgeFacts.rels (by rw [generatorCount_eq]; exact hk)⟩

theorem eval_mem_range :
    ∀ w : Wd, w.gensLt 11 = true → w.eval tB ∈ φ.range
  | .gen i, h => by
    simp only [Wd.gensLt, decide_eq_true_eq] at h
    exact tB_mem_range i h
  | .mul u v, h => by
    simp only [Wd.gensLt, Bool.and_eq_true] at h
    exact mul_mem (eval_mem_range u h.1) (eval_mem_range v h.2)
  | .pow u e, h => by
    simp only [Wd.gensLt] at h
    exact pow_mem (eval_mem_range u h) e

theorem wA_lt : wA.gensLt 11 = true := by decide +kernel

theorem wB_lt : wB.gensLt 11 = true := by decide +kernel

theorem bGL_injective : Function.Injective bGL := by
  intro x y h
  apply bMat_injective
  have := congrArg (fun g : GL (Fin 4370) (ZMod 2) => (g : Matrix (Fin 4370) (Fin 4370) (ZMod 2))) h
  simpa [coe_bGL] using this

theorem range_bGL :
    bGL.range = Subgroup.closure ({glA₁, glA₂} : Set (GL (Fin 4370) (ZMod 2))) := by
  rw [MonoidHom.range_eq_map, ← closure_bA_eq_top, MonoidHom.map_closure, Set.image_pair,
    bGL_bA₁, bGL_bA₂]

theorem range_eq_top :
    φ.range = ⊤ := by
  obtain ⟨Gu, hA, hB⟩ := bridgeFacts.conj
  let c : GL (Fin 4370) (ZMod 2) →* GL (Fin 4370) (ZMod 2) := (MulAut.conj Gu⁻¹).toMonoidHom
  have hc : ∀ g, c g = Gu⁻¹ * g * Gu := fun g => by simp [c]
  have hmap : bGL.range.map c ≤ φ.range.map bGL := by
    rw [range_bGL, MonoidHom.map_closure, Set.image_pair, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · refine ⟨_, eval_mem_range wA wA_lt, ?_⟩
      rw [hc, mul_assoc, hA, ← mul_assoc, inv_mul_cancel, one_mul]
    · refine ⟨_, eval_mem_range wB wB_lt, ?_⟩
      rw [hc, mul_assoc, hB, ← mul_assoc, inv_mul_cancel, one_mul]
  have hle : φ.range.map bGL ≤ bGL.range := by
    rintro _ ⟨x, -, rfl⟩
    exact ⟨x, rfl⟩
  have hinj : Function.Injective c := (MulAut.conj Gu⁻¹).injective
  have heq : φ.range.map bGL = bGL.range := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [← Subgroup.card_map_of_injective hinj]
    exact Subgroup.card_le_of_le hmap
  rw [eq_top_iff]
  intro x _
  have hx : bGL x ∈ φ.range.map bGL := by
    rw [heq]
    exact ⟨x, rfl⟩
  obtain ⟨y, hy, hyx⟩ := hx
  rwa [← bGL_injective hyx]

theorem φ_surjective :
    Function.Surjective φ := MonoidHom.range_eq_top.1 range_eq_top

theorem nonempty_mulEquiv_of_card_le
    (hfin : Finite TauCeti.SporadicName.B.Group)
    (hcard : Nat.card TauCeti.SporadicName.B.Group ≤ 4154781481226426191177580544000000) :
    Nonempty (CFSG.Blueprint.NativeSporadic.B ≃* TauCeti.SporadicName.B.Group) := by
  revert hfin hcard
  show Finite SporadicName.B.presentation.Group →
    Nat.card SporadicName.B.presentation.Group ≤ 4154781481226426191177580544000000 →
    Nonempty (Blueprint.NativeSporadic.B ≃* SporadicName.B.presentation.Group)
  rw [presentation_eq]
  intro hfin hcard
  exact @nonempty_mulEquiv_of_surjective pres.Group NativeSporadic.B _ _ hfin φ φ_surjective _
    hcard card_le_card_B

end CFSG.Sporadic.Bridge.B
