module

public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem3_1
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.pStability
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem5_1

namespace CFSG
end CFSG
open CFSG

/-!
# Glauberman, "A Characteristic Subgroup of a p-Stable Group" — §3, Theorem 3.2 and companions

Statements and proofs of Lemma 3.5, Theorem 3.2, Lemma 3.7, and Corollaries 3.4/3.5 of
George Glauberman, *A Characteristic Subgroup of a p-Stable Group*, Canadian Journal of
Mathematics 20 (1968), 1101–1135 — reference [6] of the dihedral-Sylow project — following
the validated transcription in `refs/glauberman-p-stable.tex`:

* Lemma 3.5 (tex L571–L593): for `S ∈ Syl_p G`, (a) `A ∈ A(S)`, `A ≤ P ≤ S` ⟹
  `Z(J(S)) ≤ A` and `Z(J(S)) ≤ Z(J(P))`; (b) `P` a `p`-subgroup of `G` with `J(S) ≤ P`
  ⟹ `J(S) = J(P)`.
* Theorem 3.2 (tex L606–L695): `p` odd, `S ∈ Syl_p G`, `B ⊴ G` an Abelian `p`-subgroup,
  `G` `p`-stable ⟹ `Z(J(S)) ∩ B ⊴ G`.  The proof follows the paper: `L` is the normal core
  of `N_G(C)` (`C = Z(J(S)) ∩ B`); the Frattini argument gives `G = L·N(L∩S) = L·N(X)`
  with `X = Z(J(L∩S))`; `(3.5)` (an `A ∈ A(S)` with `[C₁,A,A] = 1` for a normal `p`-subgroup
  `C₁ ⊇ C` lies in `L`) is derived from the `p`-stability hypothesis via the local plumbing
  `pStableLocal_apply_of_normal_pSubgroup` (the paper's `(3.4)` containment
  `O_p(G/C(C₁)) ⊆ L/C(C₁)`); the normal closure `V = ⟨C^G⟩` satisfies `V ⊆ X` ("(3.8)")
  because every conjugate of `C` by `g = ln` (`l ∈ L`, `n ∈ N(X)`) collapses to a conjugate
  by `n` (`L ≤ N(C)`); the Thompson Replacement Theorem applied to `(V, A)` for `A ∈ A(S)`
  with `A ⊄ L` and `A ∩ V` maximal yields the contradiction `[V,A,A] ≠ 1` vs.
  `[V,A,A] ⊆ [X,A,A] ⊆ [A*,A,A] = 1`.
* Lemma 3.7 (tex L699–L733): `H ≤ Z(J(S))` ⟹ `N(H) = C(H)(N(J(S)) ∩ N(H))`.
* Corollary 3.4 (tex L697–L709): (a) `Z(J(S)) ⊴ G` iff `Z(J(S))` is contained in a normal
  Abelian subgroup of `G`; (b) if `O_p(G)` contains an element of `A(S)`, then `Z(J(S)) ⊴ G`.
* Corollary 3.5 (tex L735–L745): `G` `p`-stable, `C(O_p(G)) ⊆ O_p(G)` ⟹
  `G = C(Z(S))·N(J(S))`.

The infrastructure lemmas of `FeitThompson/Gorenstein/Chapter8_2.lean` and
`Glauberman/Theorem5_1.lean` that are used here (`thompsonSubgroup_le`,
`thompsonCenter_isMulCommutative`, `exists_mem_thompsonAbelianSubgroups`, the
conjugation-invariance of `A(P)`) are `module`-private there; they are reproduced locally
at the top of this file.  The `p`-stability plumbing
`pStableLocal_apply_of_core_normal` of `Glauberman/pStability.lean` is generalized here
to arbitrary normal `p`-subgroups `P` (`pStableLocal_apply_of_normal_pSubgroup`), which is
exactly the paper's use of `p`-stability in `(3.5)`.

No `axiom`/`opaque`/unregistered `sorry` is used.
-/

open scoped Pointwise commutatorElement

namespace CFSG.Glauberman

variable {G : Type*} [Group G]

/-! ## Local infrastructure (module-private copies of Chapter8_2 / Theorem5_1 helpers) -/

/-- `J(P) ≤ P`. -/
private lemma thompsonSubgroup_le (P : Subgroup G) :
    thompsonSubgroup (G := G) P ≤ P := by
  refine sSup_le ?_
  intro A hA
  exact hA.1

/-- `Z(J(P)) ≤ P`. -/
private lemma thompsonCenter_le (P : Subgroup G) :
    thompsonCenter (G := G) P ≤ P := by
  calc
    thompsonCenter (G := G) P ≤ thompsonSubgroup (G := G) P := by
      exact inf_le_left
    _ ≤ P := thompsonSubgroup_le (G := G) P

/-- `Z(J(P))` is Abelian. -/
private lemma thompsonCenter_isMulCommutative (P : Subgroup G) :
    IsMulCommutative (thompsonCenter (G := G) P) := by
  refine (Subgroup.le_centralizer_iff_isMulCommutative (K := thompsonCenter (G := G) P)).1 ?_
  have hle_left : thompsonCenter (G := G) P ≤ thompsonSubgroup (G := G) P := by
    exact inf_le_left
  have hle_right :
      thompsonCenter (G := G) P ≤
        Subgroup.centralizer (thompsonSubgroup (G := G) P : Set G) := by
    exact inf_le_right
  exact hle_right.trans <|
    Subgroup.centralizer_le
      (show (thompsonCenter (G := G) P : Set G) ⊆ (thompsonSubgroup (G := G) P : Set G) from
        hle_left)

/-- The Abelian subgroups of `S` of maximal order form a non-empty set (finite `S`). -/
private theorem exists_mem_thompsonAbelianSubgroups (S : Subgroup G) [Finite ↥S] :
    ∃ A : Subgroup G, A ∈ thompsonAbelianSubgroups (G := G) S := by
  classical
  let s : Set (Subgroup G) := {A | A ≤ S ∧ IsMulCommutative A}
  have hsfin : s.Finite := by
    have hinj :
        Function.Injective (fun A : ↥s => ((A : Subgroup G).subgroupOf S : Subgroup ↥S)) := by
      intro A B h
      apply Subtype.ext
      have h' := congrArg (fun X : Subgroup ↥S => X.map S.subtype) h
      calc
        A.1 = (A.1.subgroupOf S).map S.subtype := by
          exact (Subgroup.map_subgroupOf_eq_of_le (H := A.1) (K := S) A.2.1).symm
        _ = (B.1.subgroupOf S).map S.subtype := h'
        _ = B.1 := by
          exact Subgroup.map_subgroupOf_eq_of_le (H := B.1) (K := S) B.2.1
    have : Finite ↥s := Finite.of_injective _ hinj
    exact Set.finite_coe_iff.mp inferInstance
  have hsne : s.Nonempty := by
    refine ⟨⊥, ?_⟩
    refine ⟨bot_le, ?_⟩
    exact (Subgroup.le_centralizer_iff_isMulCommutative (K := ⊥)).1 bot_le
  obtain ⟨A, hA, hAmax⟩ :=
    Set.exists_max_image s (fun C : Subgroup G => Nat.card C) hsfin hsne
  exact ⟨A, hA.1, hA.2, fun B hB_le hB_comm => hAmax B ⟨hB_le, hB_comm⟩⟩

/-- Conjugation by a normalizer element preserves `A(P)`: if `g ∈ N_G(P)`, then the map
`A ↦ A^g` is a bijection of `A(P)` onto itself.  This is the content of the first half of
the proof of `thompsonCenter_normal_subgroupOf_sylow` in `Chapter8_2.lean`, generalised
from `g ∈ S` to `g ∈ N_G(P)`; it is exactly "J is characteristic in P". -/
private lemma thompsonSubgroup_map_conj_of_normalizer (P : Subgroup G) {g : G}
    (hg : g ∈ Subgroup.normalizer (P : Set G)) :
    (thompsonSubgroup (G := G) P).map (MulAut.conj g).toMonoidHom =
      thompsonSubgroup (G := G) P := by
  classical
  let e : G ≃* G := MulAut.conj g
  let e' : G ≃* G := MulAut.conj (g⁻¹ : G)
  have hg' : (P : Subgroup G).map e.toMonoidHom = P :=
    (Subgroup.mem_normalizer_iff_map_conj_eq).1 hg
  have hg'inv : g⁻¹ ∈ Subgroup.normalizer (P : Set G) :=
    (Subgroup.normalizer (P : Set G)).inv_mem hg
  have hg'inv' : (P : Subgroup G).map e'.toMonoidHom = P :=
    (Subgroup.mem_normalizer_iff_map_conj_eq).1 hg'inv
  have himage :
      (MulEquiv.mapSubgroup e) '' thompsonAbelianSubgroups (G := G) P =
        thompsonAbelianSubgroups (G := G) P := by
    ext B
    constructor
    · rintro ⟨A, hA, rfl⟩
      refine ⟨?_, ?_, ?_⟩
      · change A.map e.toMonoidHom ≤ P
        exact (Subgroup.map_mono hA.1).trans hg'.le
      · let : IsMulCommutative A := hA.2.1
        exact Subgroup.map_isMulCommutative (H := A) e.toMonoidHom
      · intro C hC hCcomm
        have hCpre_le : C.map e'.toMonoidHom ≤ P :=
          (Subgroup.map_mono hC).trans hg'inv'.le
        have hCpre_comm : IsMulCommutative (C.map e'.toMonoidHom) := by
          infer_instance
        have hAmax := hA.2.2 (C.map e'.toMonoidHom) hCpre_le hCpre_comm
        calc
          Nat.card C = Nat.card (C.map e'.toMonoidHom) := by
            symm
            exact Subgroup.card_map_of_injective (K := C) e'.injective
          _ ≤ Nat.card A := hAmax
          _ = Nat.card (A.map e.toMonoidHom) := by
            symm
            exact Subgroup.card_map_of_injective (K := A) e.injective
    · intro hB
      refine ⟨B.map e'.toMonoidHom, ?_, ?_⟩
      · refine ⟨?_, ?_, ?_⟩
        · exact (Subgroup.map_mono hB.1).trans hg'inv'.le
        · let : IsMulCommutative B := hB.2.1
          exact Subgroup.map_isMulCommutative (H := B) e'.toMonoidHom
        · intro C hC hCcomm
          have hCpre_le : C.map e.toMonoidHom ≤ P :=
            (Subgroup.map_mono hC).trans hg'.le
          have hCpre_comm : IsMulCommutative (C.map e.toMonoidHom) := by
            infer_instance
          have hBmax := hB.2.2 (C.map e.toMonoidHom) hCpre_le hCpre_comm
          calc
            Nat.card C = Nat.card (C.map e.toMonoidHom) := by
              symm
              exact Subgroup.card_map_of_injective (K := C) e.injective
            _ ≤ Nat.card B := hBmax
            _ = Nat.card (B.map e'.toMonoidHom) := by
              symm
              exact Subgroup.card_map_of_injective (K := B) e'.injective
      · ext x
        simp [e, e', mul_assoc]
  calc
    (thompsonSubgroup (G := G) P).map (MulAut.conj g).toMonoidHom
        = (MulEquiv.mapSubgroup e) (sSup (thompsonAbelianSubgroups (G := G) P)) := rfl
    _ = sSup ((MulEquiv.mapSubgroup e) '' thompsonAbelianSubgroups (G := G) P) := by
      simp
    _ = thompsonSubgroup (G := G) P := by
      simpa [thompsonSubgroup] using congrArg sSup himage

/-- If `P` is a subgroup of `G`, then `N_G(P) ≤ N_G(J(P))`: `J(P)` is characteristic in `P`. -/
private lemma normalizer_le_normalizer_of_thompsonSubgroup (P : Subgroup G) :
    Subgroup.normalizer (P : Set G) ≤
      Subgroup.normalizer ((thompsonSubgroup (G := G) P : Subgroup G) : Set G) := by
  intro g hg
  exact (Subgroup.mem_normalizer_iff_map_conj_eq).2 (thompsonSubgroup_map_conj_of_normalizer P hg)

/-- If `P` is a subgroup of `G`, then `N_G(J(P)) ≤ N_G(Z(J(P)))`: `Z(J(P))` is
characteristic in `J(P)`. -/
private lemma normalizer_le_normalizer_of_thompsonCenter (P : Subgroup G) :
    Subgroup.normalizer ((thompsonSubgroup (G := G) P : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((thompsonCenter (G := G) P : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hJ : (thompsonSubgroup (G := G) P).map (MulAut.conj g).toMonoidHom =
      thompsonSubgroup (G := G) P :=
    (Subgroup.mem_normalizer_iff_map_conj_eq).1 hg
  have hcen : (Subgroup.centralizer (thompsonSubgroup (G := G) P : Set G)).map
      (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer (thompsonSubgroup (G := G) P : Set G) := by
    rw [map_centralizer_eq_of_equiv (G := G) (G' := G) (e := MulAut.conj g)
      (P := thompsonSubgroup (G := G) P), hJ]
  calc
    (thompsonCenter (G := G) P).map (MulAut.conj g).toMonoidHom
        = ((thompsonSubgroup (G := G) P ⊓
            Subgroup.centralizer (thompsonSubgroup (G := G) P : Set G)) : Subgroup G).map
            (MulAut.conj g).toMonoidHom := rfl
    _ = (thompsonSubgroup (G := G) P).map (MulAut.conj g).toMonoidHom ⊓
        (Subgroup.centralizer (thompsonSubgroup (G := G) P : Set G)).map
          (MulAut.conj g).toMonoidHom := by
          exact Subgroup.map_inf (thompsonSubgroup (G := G) P)
            (Subgroup.centralizer (thompsonSubgroup (G := G) P : Set G))
            (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
    _ = thompsonCenter (G := G) P := by
      rw [hJ, hcen]
      rfl

/-- The centralizer of `H` is contained in the normalizer of `H`. -/
private lemma centralizer_le_normalizer (H : Subgroup G) :
    Subgroup.centralizer (H : Set G) ≤ Subgroup.normalizer (H : Set G) :=
  Subgroup.centralizer_le_normalizer (H : Set G)

/-! ## The `pStableLocal` application for arbitrary normal `p`-subgroups -/

/-- The `pStable` application shape for an arbitrary normal `p`-subgroup: if `G` is
`p`-stable and `O_p(G) ≠ ⊥` (so that `⊤ ∈ M_p(G)`), then for every normal `p`-subgroup
`P` of `G` and every `x ∈ G` with `[P,x,x] = 1`, the coset of `x` modulo `C_G(P)` lies in
`O_p(G/C_G(P))`.  This generalises `pStableLocal_apply_of_core_normal`
(`Glauberman/pStability.lean`, the case `P = O_p(G)`) to arbitrary normal `p`-subgroups,
which is exactly how the `p`-stability hypothesis is used in the proof of `(3.5)` of
Theorem 3.2 (`refs/glauberman-p-stable.tex` L683–L689): there `P := C₁` is any normal
`p`-subgroup of `G` containing `C`, and the conclusion is fed into the containment
`O_p(G/C(C₁)) ⊆ L/C(C₁)` ("(3.4)"). -/
public theorem pStableLocal_apply_of_normal_pSubgroup {G : Type*} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (hstab : pStable p G) (hPne : pCore p G ≠ ⊥)
    {P : Subgroup G} (hPp : IsPGroup p P) (hPnorm : P.Normal) :
    ∀ x : G, ⁅⁅P, Subgroup.zpowers x⁆, Subgroup.zpowers x⁆ = ⊥ →
      QuotientGroup.mk' (Subgroup.centralizer (P : Set G)) x ∈
        pCore p (G ⧸ Subgroup.centralizer (P : Set G)) := by
  classical
  intro x hcomm
  -- `⊤ ∈ M_p(G)` because `O_p(⊤) ≅ O_p(G) ≠ ⊥`
  have hMtop : (⊤ : Subgroup G) ∈ MpSet p G := by
    change pCore p (↥(⊤ : Subgroup G)) ≠ ⊥ ∧
      ∀ K : Subgroup G, pCore p (↥K) ≠ ⊥ → (⊤ : Subgroup G) ≤ K → K = (⊤ : Subgroup G)
    constructor
    · intro hbot
      apply hPne
      have hmap := pCore_map_iso (G := ↥(⊤ : Subgroup G)) (G' := G) (p := p)
        (f := (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G))
      simpa [hbot] using hmap.symm
    · intro K hKne htople
      exact le_antisymm le_top htople
  have hstabTop : pStableLocal p (G := ↥(⊤ : Subgroup G)) := hstab (⊤ : Subgroup G) hMtop
  -- work in the isomorphic copy `T := ↥(⊤ : Subgroup G)` of `G`
  let T := ↥(⊤ : Subgroup G)
  let e : T ≃* G := Subgroup.topEquiv
  have hP0p : IsPGroup p (P.map e.symm.toMonoidHom) :=
    IsPGroup.map hPp e.symm.toMonoidHom
  have hP0_normal : (P.map e.symm.toMonoidHom).Normal :=
    Subgroup.Normal.map hPnorm e.symm.toMonoidHom e.symm.surjective
  have hP0n : (pPrimeCore p T ⊔ P.map e.symm.toMonoidHom).Normal := by
    have hp' : pPrimeCore p T = (pPrimeCore p G).map e.symm.toMonoidHom := by
      exact (pPrimeCore_map_iso (G := G) (G' := T) (p := p) (f := e.symm)).symm
    rw [hp']
    dsimp
    rw [← Subgroup.map_sup (pPrimeCore p G) P (e.symm : G →* T)]
    exact Subgroup.Normal.map (Subgroup.sup_normal (pPrimeCore p G) P) e.symm.toMonoidHom
      e.symm.surjective
  let x0 : T := ⟨x, by simp⟩
  have hx0 : x0 ∈ Subgroup.normalizer ((P.map e.symm.toMonoidHom) : Set T) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hP0_normal]
    trivial
  -- the commutator hypothesis in `G` transports to `T`
  have hP0_map : (P.map e.symm.toMonoidHom).map e.toMonoidHom = P := by
    dsimp
    have hcomp : (e : T →* G).comp (e.symm : G →* T) = MonoidHom.id G := by
      ext g
      simp
    rw [Subgroup.map_map, hcomp, Subgroup.map_id]
  have hZ0_map : (Subgroup.zpowers x0).map e.toMonoidHom = Subgroup.zpowers x := by
    rw [MonoidHom.map_zpowers]
    congr 1
  have hcomm0 : ⁅⁅P.map e.symm.toMonoidHom, Subgroup.zpowers x0⁆, Subgroup.zpowers x0⁆ = ⊥ := by
    apply (Subgroup.map_injective (f := e.toMonoidHom) e.injective)
    rw [Subgroup.map_commutator, Subgroup.map_commutator, hP0_map, hZ0_map, hcomm,
      Subgroup.map_bot]
  -- the `pStableLocal` conclusion, with `N = N_T(P₀) = ⊤` and `C = C_T(P₀)`
  let N0 : Subgroup T := Subgroup.normalizer ((P.map e.symm.toMonoidHom) : Set T)
  let C0 : Subgroup T := Subgroup.centralizer ((P.map e.symm.toMonoidHom) : Set T)
  have hN0 : N0 = ⊤ := by simpa [N0] using (Subgroup.normalizer_eq_top_iff.mpr hP0_normal)
  have hC0_normal : C0.Normal := Subgroup.normal_centralizer (H := P.map e.symm.toMonoidHom)
  have : (C0.subgroupOf N0).Normal := Subgroup.Normal.subgroupOf hC0_normal N0
  have : (C0.subgroupOf (⊤ : Subgroup T)).Normal :=
    Subgroup.Normal.subgroupOf hC0_normal (⊤ : Subgroup T)
  have hconcl0 : QuotientGroup.mk' (C0.subgroupOf N0) ⟨x0, hx0⟩ ∈ pCore p (N0 ⧸ C0.subgroupOf N0) := by
    simpa [N0, C0] using (hstabTop (P.map e.symm.toMonoidHom) hP0p hP0n x0 hx0 hcomm0)
  -- step 1: transport `N0 ⧸ C0.subgroupOf N0` to `⊤ ⧸ C0.subgroupOf ⊤` (ambient `↥⊤`)
  let eN0 : ↥N0 ≃* ↥(⊤ : Subgroup T) :=
    { toEquiv := Equiv.subtypeEquivRight (fun y : T => by rw [hN0])
      map_mul' := by intro a b; rfl }
  have heN0 : (C0.subgroupOf N0).map (eN0 : ↥N0 →* ↥(⊤ : Subgroup T)) =
      C0.subgroupOf (⊤ : Subgroup T) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hz)
    · intro hy
      refine ⟨⟨y, by simp [hN0]⟩, ?_, ?_⟩
      · exact Subgroup.mem_subgroupOf.mpr (by simpa using (Subgroup.mem_subgroupOf.mp hy))
      · apply Subtype.ext
        rfl
  let Φ₀ : ↥N0 ⧸ C0.subgroupOf N0 ≃* ↥(⊤ : Subgroup T) ⧸ C0.subgroupOf (⊤ : Subgroup T) :=
    QuotientGroup.congr (G := ↥N0) (H := ↥(⊤ : Subgroup T))
      (G' := C0.subgroupOf N0) (H' := C0.subgroupOf (⊤ : Subgroup T)) eN0 heN0
  have hcore₀ : (pCore p (↥N0 ⧸ C0.subgroupOf N0)).map Φ₀.toMonoidHom =
      pCore p (↥(⊤ : Subgroup T) ⧸ C0.subgroupOf (⊤ : Subgroup T)) :=
    pCore_map_iso (G := ↥N0 ⧸ C0.subgroupOf N0) (G' := ↥(⊤ : Subgroup T) ⧸ C0.subgroupOf (⊤ : Subgroup T))
      (p := p) (f := Φ₀)
  have hmem₀ : Φ₀ (QuotientGroup.mk' (C0.subgroupOf N0) ⟨x0, hx0⟩) ∈
      pCore p (↥(⊤ : Subgroup T) ⧸ C0.subgroupOf (⊤ : Subgroup T)) := by
    rw [← hcore₀]
    exact Subgroup.mem_map.mpr ⟨QuotientGroup.mk' (C0.subgroupOf N0) ⟨x0, hx0⟩, hconcl0, rfl⟩
  have happly₀ : Φ₀ (QuotientGroup.mk' (C0.subgroupOf N0) ⟨x0, hx0⟩) =
      QuotientGroup.mk' (C0.subgroupOf (⊤ : Subgroup T)) ⟨x0, (by simp : x0 ∈ (⊤ : Subgroup T))⟩ := by
    dsimp [Φ₀]
    rfl
  have hconcl1 : QuotientGroup.mk' (C0.subgroupOf (⊤ : Subgroup T))
      ⟨x0, (by simp : x0 ∈ (⊤ : Subgroup T))⟩ ∈
      pCore p (↥(⊤ : Subgroup T) ⧸ C0.subgroupOf (⊤ : Subgroup T)) := by
    rw [happly₀] at hmem₀
    exact hmem₀
  -- step 2: transport `⊤ ⧸ C0.subgroupOf ⊤` to `G ⧸ C` along `e : T ≃* G`
  have : (Subgroup.centralizer (P : Set G)).Normal := Subgroup.normal_centralizer (H := P)
  let C : Subgroup G := Subgroup.centralizer (P : Set G)
  let eT : ↥(⊤ : Subgroup T) ≃* T := Subgroup.topEquiv
  let eTot : ↥(⊤ : Subgroup T) ≃* G := eT.trans e
  have he_subgroupOf : (C0.subgroupOf (⊤ : Subgroup T)).map eT.toMonoidHom = C0 := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa [eT] using (Subgroup.mem_subgroupOf.mp hz)
    · intro hy
      refine ⟨⟨y, by simp⟩, ?_, ?_⟩
      · exact Subgroup.mem_subgroupOf.mpr (by simpa using hy)
      · rfl
  have he_centralizer : C0.map e.toMonoidHom = C := by
    calc
      C0.map e.toMonoidHom =
          Subgroup.centralizer (((P.map e.symm.toMonoidHom).map e.toMonoidHom : Subgroup G) : Set G) := by
        exact map_centralizer_eq_of_equiv (e := e) (P := P.map e.symm.toMonoidHom)
      _ = C := by
        rw [hP0_map]
  have hcomp₁ : eTot.toMonoidHom = e.toMonoidHom.comp eT.toMonoidHom := by
    dsimp [eTot]
  have heTot : (C0.subgroupOf (⊤ : Subgroup T)).map eTot.toMonoidHom = C := by
    rw [hcomp₁, ← Subgroup.map_map, he_subgroupOf, he_centralizer]
  let Φ₁ : ↥(⊤ : Subgroup T) ⧸ C0.subgroupOf (⊤ : Subgroup T) ≃* G ⧸ C :=
    QuotientGroup.congr (G := ↥(⊤ : Subgroup T)) (H := G)
      (G' := C0.subgroupOf (⊤ : Subgroup T)) (H' := C) eTot heTot
  have hcore₁ : (pCore p (↥(⊤ : Subgroup T) ⧸ C0.subgroupOf (⊤ : Subgroup T))).map Φ₁.toMonoidHom =
      pCore p (G ⧸ C) :=
    pCore_map_iso (G := ↥(⊤ : Subgroup T) ⧸ C0.subgroupOf (⊤ : Subgroup T)) (G' := G ⧸ C)
      (p := p) (f := Φ₁)
  have hmem₁ : Φ₁ (QuotientGroup.mk' (C0.subgroupOf (⊤ : Subgroup T))
      ⟨x0, (by simp : x0 ∈ (⊤ : Subgroup T))⟩) ∈ pCore p (G ⧸ C) := by
    rw [← hcore₁]
    exact Subgroup.mem_map.mpr ⟨QuotientGroup.mk' (C0.subgroupOf (⊤ : Subgroup T))
      ⟨x0, (by simp : x0 ∈ (⊤ : Subgroup T))⟩, hconcl1, rfl⟩
  have happly₁ : Φ₁ (QuotientGroup.mk' (C0.subgroupOf (⊤ : Subgroup T))
      ⟨x0, (by simp : x0 ∈ (⊤ : Subgroup T))⟩) = QuotientGroup.mk' C x := by
    dsimp [Φ₁]
    rfl
  have hconcl : QuotientGroup.mk' C x ∈ pCore p (G ⧸ C) := by
    rw [happly₁] at hmem₁
    exact hmem₁
  simpa [C] using hconcl

/-! ## Lemma 3.5 (tex L571–L593) -/

/-- If `A ∈ A(P)` then `Z(J(P)) ≤ A`: `Z(J(P))·A` is Abelian (the centre of `J(P)`
commutes with `A ⊆ J(P)`) and contained in `P`, so maximality of `|A|` forces
`Z(J(P)) ⊆ A`.  This is the first conclusion of Lemma 3.5(a), stated for an arbitrary
subgroup `P` (no Sylow hypothesis needed). -/
private lemma lemma3_5a [Finite G] {P A : Subgroup G}
    (hA : A ∈ thompsonAbelianSubgroups (G := G) P) :
    thompsonCenter (G := G) P ≤ A := by
  classical
  let Z := thompsonCenter (G := G) P
  have hZ_le_P : Z ≤ P := thompsonCenter_le (G := G) P
  have hZ_cent_J : Z ≤ Subgroup.centralizer (thompsonSubgroup (G := G) P : Set G) := by
    exact inf_le_right
  have hA_le_J : A ≤ thompsonSubgroup (G := G) P := by
    exact le_sSup hA
  have hZA_comm : IsMulCommutative ((Z ⊔ A : Subgroup G)) := by
    rw [Subgroup.sup_eq_closure]
    let : IsMulCommutative Z := thompsonCenter_isMulCommutative (G := G) P
    let : IsMulCommutative A := hA.2.1
    refine Subgroup.isMulCommutative_closure (k := ((Z : Subgroup G) : Set G) ∪ ((A : Subgroup G) : Set G)) (Set.Pairwise.of_forall₂ ?_)
    intro y hy z hz
    show y * z = z * y
    rcases hy with hyZ | hyA
    · rcases hz with hzZ | hzA
      · exact setLike_mul_comm (s := Z) hyZ hzZ
      · exact (Subgroup.mem_centralizer_iff.mp (hZ_cent_J hyZ) z (hA_le_J hzA)).symm
    · rcases hz with hzZ | hzA
      · exact Subgroup.mem_centralizer_iff.mp (hZ_cent_J hzZ) y (hA_le_J hyA)
      · exact setLike_mul_comm (s := A) hyA hzA
  have hZA_le_P : Z ⊔ A ≤ P := sup_le hZ_le_P hA.1
  have hcard : Nat.card (Z ⊔ A : Subgroup G) ≤ Nat.card A :=
    hA.2.2 (Z ⊔ A : Subgroup G) hZA_le_P hZA_comm
  have hA_le_ZA : A ≤ Z ⊔ A := le_sup_right
  have hZA_eq_A : A = Z ⊔ A := Subgroup.eq_of_le_of_card_ge hA_le_ZA hcard
  exact hZA_eq_A ▸ le_sup_left

/-- Within a Sylow `p`-subgroup `T`, if `J(T) ≤ P ≤ T` then `J(P) = J(T)`: every
`A ∈ A(T)` is an element of `A(P)` (it lies in `J(T) ≤ P`), and every `A ∈ A(P)` has
order `d(T)` hence lies in `A(T)`, so `J(P)` and `J(T)` are generated by the same set. -/
private lemma j_eq_of_sylow_le {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    (T : Sylow p G) {P : Subgroup G}
    (hJ_le_P : thompsonSubgroup (T : Subgroup G) ≤ P) (hP_le_T : P ≤ (T : Subgroup G)) :
    thompsonSubgroup (G := G) P = thompsonSubgroup (T : Subgroup G) := by
  classical
  obtain ⟨A0, hA0⟩ := exists_mem_thompsonAbelianSubgroups (S := (T : Subgroup G))
  have hA0_le_J : A0 ≤ thompsonSubgroup (T : Subgroup G) := le_sSup hA0
  have hA0_le_P : A0 ≤ P := hA0_le_J.trans hJ_le_P
  have hA0_in_AP : A0 ∈ thompsonAbelianSubgroups (G := G) P := by
    refine ⟨hA0_le_P, hA0.2.1, ?_⟩
    intro B hB hBcomm
    exact hA0.2.2 B (hB.trans hP_le_T) hBcomm
  have hAP_card : ∀ A : Subgroup G, A ∈ thompsonAbelianSubgroups (G := G) P →
      Nat.card A = Nat.card A0 := by
    intro A hA
    have hle1 : Nat.card A ≤ Nat.card A0 := hA0.2.2 A (hA.1.trans hP_le_T) hA.2.1
    have hle2 : Nat.card A0 ≤ Nat.card A := hA.2.2 A0 hA0_le_P hA0.2.1
    exact le_antisymm hle1 hle2
  have hJTeP : thompsonSubgroup (T : Subgroup G) ≤ thompsonSubgroup (G := G) P := by
    refine sSup_le ?_
    intro A hA
    have hA_le_P : A ≤ P := (le_sSup hA).trans hJ_le_P
    have hA_in_AP : A ∈ thompsonAbelianSubgroups (G := G) P := by
      refine ⟨hA_le_P, hA.2.1, ?_⟩
      intro B hB hBcomm
      exact hA.2.2 B (hB.trans hP_le_T) hBcomm
    exact le_sSup hA_in_AP
  have hJPeT : thompsonSubgroup (G := G) P ≤ thompsonSubgroup (T : Subgroup G) := by
    refine sSup_le ?_
    intro A hA
    have hA_in_AT : A ∈ thompsonAbelianSubgroups (G := G) (T : Subgroup G) := by
      refine ⟨hA.1.trans hP_le_T, hA.2.1, ?_⟩
      intro B hB hBcomm
      have hcard : Nat.card B ≤ Nat.card A0 := hA0.2.2 B hB hBcomm
      rw [← hAP_card A hA] at hcard
      exact hcard
    exact le_sSup hA_in_AT
  exact le_antisymm hJPeT hJTeP

/-- Lemma 3.5 ([6], §3, p. 1108; `refs/glauberman-p-stable.tex` L571–L593): let `S` be a
Sylow `p`-subgroup of a finite group `G`.  Then:

(a) if `A ∈ A(S)` and `A ≤ P ≤ S`, then `Z(J(S)) ≤ A` and `Z(J(S)) ≤ Z(J(P))`;
(b) if `P` is a `p`-subgroup of `G` that contains `J(S)`, then `J(S) = J(P)`.

Route of the paper: (a) `Z(J(S))·A` is Abelian and `|A| = d(S)`, so maximality of `|A|`
gives `Z(J(S)) ⊆ A`; then `d(P) = |A| = d(S)` and `Z(J(S)) ⊆ A ⊆ J(P) ⊆ J(S)` give
`Z(J(S)) ⊆ Z(J(P))`.  (b) extend `P` to a Sylow `p`-subgroup `T` of `G`; then
`J(S) = J(T)` by the Sylow version (`thompsonSubgroup_eq_of_sylow_le`), and
`J(T) = J(P)` by the argument of (a) inside `T`. -/
public lemma lemma3_5 {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    (S : Sylow p G) :
    (∀ {A P : Subgroup G}, A ∈ thompsonAbelianSubgroups (G := G) (S : Subgroup G) →
      A ≤ P → P ≤ (S : Subgroup G) → thompsonCenter (G := G) (S : Subgroup G) ≤ A) ∧
    (∀ {A P : Subgroup G}, A ∈ thompsonAbelianSubgroups (G := G) (S : Subgroup G) →
      A ≤ P → P ≤ (S : Subgroup G) → thompsonCenter (G := G) (S : Subgroup G) ≤
        thompsonCenter (G := G) P) ∧
    (∀ {P : Subgroup G}, IsPGroup p P → thompsonSubgroup (G := G) (S : Subgroup G) ≤ P →
      thompsonSubgroup (G := G) (S : Subgroup G) = thompsonSubgroup (G := G) P) := by
  classical
  constructor
  · intro A P hA hAP hPS
    exact lemma3_5a hA
  constructor
  · intro A P hA hAP hPS
    have hA_in_AP : A ∈ thompsonAbelianSubgroups (G := G) P := by
      refine ⟨hAP, hA.2.1, ?_⟩
      intro B hB hBcomm
      exact hA.2.2 B (hB.trans hPS) hBcomm
    have hA_le_JP : A ≤ thompsonSubgroup (G := G) P := le_sSup hA_in_AP
    have hJP_le_JS : thompsonSubgroup (G := G) P ≤ thompsonSubgroup (G := G) (S : Subgroup G) := by
      refine sSup_le ?_
      intro A' hA'
      have hA'_in_AS : A' ∈ thompsonAbelianSubgroups (G := G) (S : Subgroup G) := by
        refine ⟨hA'.1.trans hPS, hA'.2.1, ?_⟩
        intro B hB hBcomm
        have hle1 : Nat.card B ≤ Nat.card A := hA.2.2 B hB hBcomm
        have hcardA' : Nat.card A' = Nat.card A := by
          have hle2 : Nat.card A' ≤ Nat.card A := hA.2.2 A' (hA'.1.trans hPS) hA'.2.1
          have hle3 : Nat.card A ≤ Nat.card A' := hA'.2.2 A hAP hA.2.1
          exact le_antisymm hle2 hle3
        rw [← hcardA'] at hle1
        exact hle1
      exact le_sSup hA'_in_AS
    intro z hz
    refine ⟨?_, ?_⟩
    · exact hA_le_JP (lemma3_5a hA hz)
    · exact Subgroup.mem_centralizer_iff.mpr (fun y hy =>
        (Subgroup.mem_centralizer_iff.mp hz.2) y (hJP_le_JS hy))
  · intro P hPp hJS_le_P
    obtain ⟨T, hP_le_T⟩ := IsPGroup.exists_le_sylow hPp
    have hJS_le_T : thompsonSubgroup (G := G) (S : Subgroup G) ≤ (T : Subgroup G) :=
      hJS_le_P.trans hP_le_T
    have hJS_eq_JS : thompsonSubgroup (G := G) (S : Subgroup G) =
        thompsonSubgroup (G := G) (T : Subgroup G) :=
      thompsonSubgroup_eq_of_sylow_le T S hJS_le_T
    have hJT_le_P : thompsonSubgroup (G := G) (T : Subgroup G) ≤ P := by
      simpa [hJS_eq_JS] using hJS_le_P
    have hJT_eq_JP : thompsonSubgroup (G := G) P = thompsonSubgroup (G := G) (T : Subgroup G) :=
      j_eq_of_sylow_le T hJT_le_P hP_le_T
    exact hJS_eq_JS.trans hJT_eq_JP.symm

/-! ## Sylow subgroups of normal subgroups and the Frattini argument -/

/-- If `N ⊴ G` and `S ∈ Syl_p G`, then `S ∩ N` (viewed as a subgroup of `N`) is a Sylow
`p`-subgroup of `N`: it is a `p`-group (as a subgroup of `S`), and it is maximal among the
`p`-subgroups of `N` because every `p`-subgroup `Q` of `N` is conjugate in `G` to a
subgroup of `S`, hence (conjugating back into the normal subgroup `N`) to a subgroup of
`S ∩ N`, so `|Q| ≤ |S ∩ N|`.  This is the standard "Sylow ∩ normal = Sylow of normal". -/
private lemma sylow_subgroupOf_normal {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    (S : Sylow p G) (N : Subgroup G) [N.Normal] :
    ∃ P : Sylow p (↥N), (P : Subgroup (↥N)).map N.subtype = (S : Subgroup G) ⊓ N := by
  classical
  let T : Subgroup (↥N) := (S : Subgroup G).subgroupOf N
  have hT_map : T.map N.subtype = (S : Subgroup G) ⊓ N := by
    simp [T, Subgroup.subgroupOf_map_subtype]
  have hT_p : IsPGroup p T := by
    intro x
    let xs : ↥(S : Subgroup G) := ⟨x.1.1, x.2⟩
    rcases (S.isPGroup' xs) with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    simpa [Subgroup.coe_pow] using congrArg Subtype.val hn
  have hT_max : ∀ {Q : Subgroup (↥N)}, IsPGroup p Q → T ≤ Q → Q = T := by
    intro Q hQ hTQ
    let QG : Subgroup G := Q.map N.subtype
    have hQG_p : IsPGroup p QG := IsPGroup.map hQ N.subtype
    obtain ⟨T', hQ_le_T'⟩ := IsPGroup.exists_le_sylow hQG_p
    obtain ⟨x, hx⟩ : ∃ x : G, x • S = T' := MulAction.exists_smul_eq G S T'
    have hQG_le_xS : QG ≤ ((x • S : Sylow p G) : Subgroup G) := by
      simpa [hx] using hQ_le_T'
    have hQGx_le_S : QG.map (MulAut.conj (x⁻¹ : G)).toMonoidHom ≤ (S : Subgroup G) := by
      calc
        QG.map (MulAut.conj (x⁻¹ : G)).toMonoidHom
            ≤ ((x • S : Sylow p G) : Subgroup G).map (MulAut.conj (x⁻¹ : G)).toMonoidHom :=
              Subgroup.map_mono hQG_le_xS
        _ = (S : Subgroup G) := by
          rw [sylow_smul_subgroup_eq_map_conj x S]
          calc
            ((S : Subgroup G).map (MulAut.conj (x : G)).toMonoidHom).map
                (MulAut.conj (x⁻¹ : G)).toMonoidHom
                = (S : Subgroup G).map
                    ((MulAut.conj (x⁻¹ : G)).toMonoidHom.comp (MulAut.conj (x : G)).toMonoidHom) := by
                      rw [Subgroup.map_map]
            _ = (S : Subgroup G) := by
              ext g
              simp [MulAut.conj_apply, mul_assoc]
    have hQGx_le_N : QG.map (MulAut.conj (x⁻¹ : G)).toMonoidHom ≤ N := by
      have hNinv : N.map (MulAut.conj (x⁻¹ : G)).toMonoidHom = N := by
        have hxN : x⁻¹ ∈ Subgroup.normalizer (N : Set G) :=
          (Subgroup.normalizer_eq_top_iff.mpr (inferInstance : N.Normal)) ▸ trivial
        exact (Subgroup.mem_normalizer_iff_map_conj_eq).1 hxN
      calc
        QG.map (MulAut.conj (x⁻¹ : G)).toMonoidHom
            ≤ N.map (MulAut.conj (x⁻¹ : G)).toMonoidHom := by
              exact Subgroup.map_mono (by
                intro y hy
                rcases Subgroup.mem_map.mp hy with ⟨n, hn, rfl⟩
                exact n.2)
        _ = N := hNinv
    have hQGx_le_T : QG.map (MulAut.conj (x⁻¹ : G)).toMonoidHom ≤ T.map N.subtype := by
      rw [hT_map]
      exact le_inf hQGx_le_S hQGx_le_N
    have hcard_Q_le_T : Nat.card Q ≤ Nat.card T := by
      calc
        Nat.card Q = Nat.card QG := by
          symm
          exact Subgroup.card_map_of_injective (K := Q) (f := N.subtype) N.subtype_injective
        _ = Nat.card (QG.map (MulAut.conj (x⁻¹ : G)).toMonoidHom) := by
          symm
          exact Subgroup.card_map_of_injective (K := QG) (f := (MulAut.conj (x⁻¹ : G)).toMonoidHom)
            (MulAut.conj (x⁻¹ : G)).injective
        _ ≤ Nat.card (T.map N.subtype) := Subgroup.card_le_of_le hQGx_le_T
        _ = Nat.card T := by
          exact Subgroup.card_map_of_injective (K := T) (f := N.subtype) N.subtype_injective
    have hTQ_map_le : T.map N.subtype ≤ QG := Subgroup.map_mono hTQ
    have hcard_QT : Nat.card QG ≤ Nat.card (T.map N.subtype) := by
      calc
        Nat.card QG = Nat.card Q := by
          exact Subgroup.card_map_of_injective (K := Q) (f := N.subtype) N.subtype_injective
        _ ≤ Nat.card T := hcard_Q_le_T
        _ = Nat.card (T.map N.subtype) := by
          symm
          exact Subgroup.card_map_of_injective (K := T) (f := N.subtype) N.subtype_injective
    have hTQ_map_eq : T.map N.subtype = QG := Subgroup.eq_of_le_of_card_ge hTQ_map_le hcard_QT
    apply (Subgroup.map_injective (f := N.subtype) N.subtype_injective)
    simpa [QG] using hTQ_map_eq.symm
  refine ⟨⟨T, hT_p, hT_max⟩, hT_map⟩

/-- The Frattini argument: if `L ⊴ G` and `S ∈ Syl_p G`, then `G = L·N_G(L ∩ S)`; here
`L ∩ S` is the Sylow `p`-subgroup of `L` supplied by `sylow_subgroupOf_normal`.  This is
Lemma 3.6 of the paper (`refs/glauberman-p-stable.tex` L595–L604), stated in the ambient
group `G`. -/
private lemma frattini_sup_eq_top {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    (S : Sylow p G) (L : Subgroup G) [L.Normal] :
    Subgroup.normalizer (((S : Subgroup G) ⊓ L : Subgroup G) : Set G) ⊔ L = ⊤ := by
  classical
  obtain ⟨P, hP_map⟩ := sylow_subgroupOf_normal S L
  have hfr := Sylow.normalizer_sup_eq_top (N := L) (P := P)
  simpa [hP_map] using hfr

/-! ## Theorem 3.2 (tex L606–L695) -/


/-! ## Lemma 3.7 (tex L699–L733) -/

/-- Lemma 3.7 ([6], §3, Lemma 3.7, p. 1110; `refs/glauberman-p-stable.tex` L699–L733):
let `S` be a Sylow `p`-subgroup of a finite group `G` and let `H` be a subgroup of
`Z(J(S))`.  Then
`N(H) = C(H)(N(J(S)) ∩ N(H))`.

Proof of the paper: `C(H)` is normal in `N(H)`; let `T` be a Sylow `p`-subgroup of
`C(H)` containing `J(S)` (possible since `H ≤ Z(J(S)) ⊆ C(J(S))`, so `J(S) ≤ C(H)`).
The Frattini argument gives `N(H) = C(H)(N(T) ∩ N(H))`; by Lemma 3.5(b), `J(S) = J(T)`,
and `J(S)` is characteristic in `T`, so `N(T) ⊆ N(J(S))`.  The statement is given in the
equivalent sup form (the product is a subgroup because `C(H) ⊴ N(H)`). -/
public lemma lemma3_7 {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    (S : Sylow p G) {H : Subgroup G} (hH : H ≤ ZJ (G := G) (S : Subgroup G)) :
    Subgroup.normalizer (H : Set G) =
      Subgroup.centralizer (H : Set G) ⊔
        (Subgroup.normalizer ((thompsonSubgroup (G := G) (S : Subgroup G) : Subgroup G) : Set G) ⊓
          Subgroup.normalizer (H : Set G)) := by
  classical
  let C : Subgroup G := Subgroup.centralizer (H : Set G)
  -- `J(S) ≤ C(H)`: `H ⊆ Z(J(S)) ⊆ C(J(S))`
  have hJS_le_C : thompsonSubgroup (G := G) (S : Subgroup G) ≤ C := by
    intro j hj
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hz : h ∈ ZJ (G := G) (S : Subgroup G) := hH hh
    exact (Subgroup.mem_centralizer_iff.mp hz.2 j hj).symm
  -- a Sylow `p`-subgroup `T₀` of `C(H)` containing `J(S)`
  have hJSsub_p : IsPGroup p ((thompsonSubgroup (G := G) (S : Subgroup G)).subgroupOf C) := by
    have hJS_p : IsPGroup p (thompsonSubgroup (G := G) (S : Subgroup G)) :=
      IsPGroup.to_le S.isPGroup' (thompsonSubgroup_le (G := G) (S : Subgroup G))
    exact hJS_p.of_equiv (Subgroup.subgroupOfEquivOfLe hJS_le_C).symm
  obtain ⟨T0, hJT0⟩ := IsPGroup.exists_le_sylow hJSsub_p
  -- `T = T₀` viewed in `G`
  let T : Subgroup G := (T0 : Subgroup (↥C)).map C.subtype
  have hJS_le_T : thompsonSubgroup (G := G) (S : Subgroup G) ≤ T := by
    intro j hj
    have hjC : j ∈ C := hJS_le_C hj
    have hjT0 : (⟨j, hjC⟩ : ↥C) ∈ (T0 : Subgroup (↥C)) := by
      exact hJT0 (Subgroup.mem_subgroupOf.mpr hj)
    exact Subgroup.mem_map.mpr ⟨⟨j, hjC⟩, hjT0, rfl⟩
  -- `N_G(T) ≤ N_G(J(S))`: `J(T) = J(S)` (Lemma 3.5(b)) and `J(T)` characteristic in `T`
  have hJT_eq_JS : thompsonSubgroup (G := G) T = thompsonSubgroup (G := G) (S : Subgroup G) := by
    have hT_p : IsPGroup p T := IsPGroup.map T0.isPGroup' C.subtype
    exact ((lemma3_5 S).2.2 hT_p hJS_le_T).symm
  have hNT_le_NJ : Subgroup.normalizer (T : Set G) ≤
      Subgroup.normalizer ((thompsonSubgroup (G := G) (S : Subgroup G) : Subgroup G) : Set G) := by
    calc
      Subgroup.normalizer (T : Set G)
          ≤ Subgroup.normalizer ((thompsonSubgroup (G := G) T : Subgroup G) : Set G) :=
            normalizer_le_normalizer_of_thompsonSubgroup T
      _ = Subgroup.normalizer ((thompsonSubgroup (G := G) (S : Subgroup G) : Subgroup G) : Set G) := by
            rw [hJT_eq_JS]
  -- `N(H) ≤ N(C(H))` (for the Sylow transport below)
  have hN_le_NC : Subgroup.normalizer (H : Set G) ≤ Subgroup.normalizer (C : Set G) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    calc
      C.map (MulAut.conj n).toMonoidHom
          = Subgroup.centralizer ((H : Subgroup G).map (MulAut.conj n).toMonoidHom : Set G) := by
            exact map_centralizer_eq_of_equiv (e := MulAut.conj n) (P := H)
      _ = C := by
        have hH' : (H : Subgroup G).map (MulAut.conj n).toMonoidHom = H :=
          (Subgroup.mem_normalizer_iff_map_conj_eq.mp hn)
        rw [hH']
  refine le_antisymm ?_ ?_
  · -- `N(H) ⊆ C(H) ⊔ (N(J(S)) ∩ N(H))`
    intro n hn
    -- the automorphism of `C(H)` induced by `n`
    let e : ↥C ≃* ↥C :=
      { toFun := fun c => ⟨n * (c : G) * n⁻¹, (Subgroup.mem_normalizer_iff.mp (hN_le_NC hn) (c : G)).1 c.2⟩
        invFun := fun c => ⟨n⁻¹ * (c : G) * n, (Subgroup.mem_normalizer_iff''.mp (hN_le_NC hn) (c : G)).1 c.2⟩
        left_inv := by
          intro c
          apply Subtype.ext
          group
        right_inv := by
          intro c
          apply Subtype.ext
          group
        map_mul' := by
          intro c d
          apply Subtype.ext
          simp [mul_assoc] }
    -- `T' = n•T` as a Sylow `p`-subgroup of `C(H)`
    let T' : Sylow p (↥C) := T0.mapSurjective (f := e.toMonoidHom) e.surjective
    have hT'_map : (T' : Subgroup (↥C)).map C.subtype = T.map (MulAut.conj n).toMonoidHom := by
      -- `T' = T₀·e`, and `subtype ∘ e = (conj n) ∘ subtype`
      have hT' : (T' : Subgroup (↥C)) = (T0 : Subgroup (↥C)).map e.toMonoidHom := rfl
      have hsub_comp : C.subtype.comp e.toMonoidHom = (MulAut.conj n).toMonoidHom.comp C.subtype := by
        ext x
        simp [e, MulAut.conj_apply, mul_assoc]
      calc
        (T' : Subgroup (↥C)).map C.subtype
            = ((T0 : Subgroup (↥C)).map e.toMonoidHom).map C.subtype := by rw [hT']
        _ = (T0 : Subgroup (↥C)).map (C.subtype.comp e.toMonoidHom) := by rw [Subgroup.map_map]
        _ = (T0 : Subgroup (↥C)).map ((MulAut.conj n).toMonoidHom.comp C.subtype) := by rw [hsub_comp]
        _ = ((T0 : Subgroup (↥C)).map C.subtype).map (MulAut.conj n).toMonoidHom := by rw [Subgroup.map_map]
        _ = T.map (MulAut.conj n).toMonoidHom := rfl
    -- Sylow conjugacy in `C(H)`: `∃ c ∈ C(H)`, `c • T' = T₀`
    obtain ⟨c, hcT'⟩ : ∃ c : ↥C, c • T' = T0 := MulAction.exists_smul_eq (↥C) T' T0
    -- `c•(n•T) = T` in `G`
    have hcT : (T.map (MulAut.conj n).toMonoidHom).map (MulAut.conj (c : G)).toMonoidHom = T := by
      have hmap_smul : ((c • T' : Sylow p (↥C)) : Subgroup (↥C)).map C.subtype = T := by
        rw [hcT']
      have hcomp : ((c • T' : Sylow p (↥C)) : Subgroup (↥C)).map C.subtype =
          ((T' : Subgroup (↥C)).map C.subtype).map (MulAut.conj (c : G)).toMonoidHom := by
        rw [sylow_smul_subgroup_eq_map_conj c T']
        ext x
        constructor
        · intro hx
          rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
          rcases Subgroup.mem_map.mp hy with ⟨z, hz, rfl⟩
          refine Subgroup.mem_map.mpr ⟨C.subtype z, Subgroup.mem_map.mpr ⟨z, hz, rfl⟩, ?_⟩
          simp [MulAut.conj_apply, mul_assoc]
        · intro hx
          rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
          rcases Subgroup.mem_map.mp hy with ⟨z, hz, rfl⟩
          refine Subgroup.mem_map.mpr ⟨(MulAut.conj (c : ↥C)).toMonoidHom z,
            Subgroup.mem_map.mpr ⟨z, hz, rfl⟩, ?_⟩
          simp [MulAut.conj_apply, mul_assoc]
      have h1 : ((T' : Subgroup (↥C)).map C.subtype).map (MulAut.conj (c : G)).toMonoidHom = T := by
        rw [← hcomp]
        exact hmap_smul
      rw [← hT'_map]
      exact h1
    -- `c·n ∈ N(T)`
    have hcn_mem : (c : G) * n ∈ Subgroup.normalizer (T : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      calc
        T.map (MulAut.conj ((c : G) * n)).toMonoidHom
            = (T.map (MulAut.conj n).toMonoidHom).map (MulAut.conj (c : G)).toMonoidHom := by
              ext x
              constructor
              · intro hx
                rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
                refine Subgroup.mem_map.mpr ⟨(MulAut.conj n).toMonoidHom y,
                  Subgroup.mem_map.mpr ⟨y, hy, rfl⟩, ?_⟩
                simp [MulAut.conj_apply, mul_assoc]
              · intro hx
                rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
                rcases Subgroup.mem_map.mp hy with ⟨z, hz, rfl⟩
                refine Subgroup.mem_map.mpr ⟨z, hz, ?_⟩
                simp [MulAut.conj_apply, mul_assoc]
        _ = T := hcT
    -- `n = c⁻¹·(c·n) ∈ C(H)·(N(J(S)) ∩ N(H))`
    have hc_inv_mem : (c : G)⁻¹ ∈ C := C.inv_mem c.2
    have hcn_NH : (c : G) * n ∈ Subgroup.normalizer (H : Set G) :=
      (Subgroup.normalizer (H : Set G)).mul_mem (centralizer_le_normalizer H c.2) hn
    have hcn_NJ : (c : G) * n ∈ Subgroup.normalizer ((thompsonSubgroup (G := G) (S : Subgroup G) : Subgroup G) : Set G) :=
      hNT_le_NJ hcn_mem
    let K : Subgroup G :=
      Subgroup.normalizer ((thompsonSubgroup (G := G) (S : Subgroup G) : Subgroup G) : Set G) ⊓
        Subgroup.normalizer (H : Set G)
    have hc_inv_mem' : (c : G)⁻¹ ∈ C ⊔ K := (le_sup_left : C ≤ C ⊔ K) hc_inv_mem
    have hcn_mem' : (c : G) * n ∈ C ⊔ K := (le_sup_right : K ≤ C ⊔ K) ⟨hcn_NJ, hcn_NH⟩
    rw [show n = (c : G)⁻¹ * ((c : G) * n) by group]
    exact (C ⊔ K).mul_mem hc_inv_mem' hcn_mem'
  · -- `C(H) ⊔ (N(J(S)) ∩ N(H)) ≤ N(H)`
    refine sup_le ?_ ?_
    · exact centralizer_le_normalizer H
    · intro x hx
      exact hx.2

/-! ## Corollaries 3.4 and 3.5 (tex L697–L745) -/

