module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCheck

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Cert

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoSporadic CFSG.ABGLocalTools
open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer

structure ExcRef where
  node : ℕ
  w : Array ℕ
deriving Inhabited

@[expose] def childrenOK (n : ℕ) (cS : ArrCert) (nodes : Array Node) (cN : Array ArrCert)
    (i : ℕ) : Bool :=
  allLt cS.pts.size fun p =>
    !(eqA n (compA n cS.pts[p]! cS.pts[p]!) (idA n)) ||
      !(allLt nodes[i]!.basis.size fun k => commA n cS.pts[p]! nodes[i]!.basis[k]!) ||
      memA n cN[i]! cS.pts[p]! || childOK n nodes cN i cS.pts[p]! nodes[i]!.children[p]!

@[expose] def excOK (n : ℕ) (ps : List ℕ) (fuel : ℕ) (inW : Array ℕ → Bool)
    (e0 : Array (Array ℕ)) (cN : Array ArrCert) (excs : List ExcRef) (i : ℕ) : Bool :=
  let c0 := enumBfs n e0 ps fuel
  enumOK n e0 ps c0 && excs.any fun r => r.node == i && validA n r.w && inW r.w &&
    (allLt e0.size fun j => memA n cN[i]! (conjA n r.w e0[j]!)) &&
      c0.pts.size == cN[i]!.pts.size

@[expose] def censusExcOK (n : ℕ) (ps : List ℕ) (fuel : ℕ) (inX outX inW : Array ℕ → Bool)
    (allowPW allowInX allowU : Bool) (sGens : Array (Array ℕ)) (roots : Array ℕ)
    (nodes : Array Node) (e0 : Array (Array ℕ)) (excs : List ExcRef) : Bool :=
  let cS := enumBfs n sGens ps fuel
  let cN := nodes.map fun nd => enumBfs n nd.basis ps fuel
  enumOK n sGens ps cS && (allLt cS.pts.size fun p => rootOK n nodes cN cS.pts[p]! roots[p]!) &&
    allLt nodes.size fun i => nodeOK n ps fuel inX outX allowPW allowInX allowU cS nodes cN i ||
      (enumOK n nodes[i]!.basis ps cN[i]! && excOK n ps fuel inW e0 cN excs i &&
        childrenOK n cS nodes cN i)

section Soundness

variable {n : ℕ} {X : Subgroup (Equiv.Perm (Fin n))} {inX outX : Array ℕ → Bool}

theorem monoW_of_le {W : Type*} [Group W] {X E₀ E : Subgroup W} {allowPW : Bool}
    (h : MonoW X allowPW E₀) (hle : E₀ ≤ E) : MonoW X allowPW E := by
  rcases h with ⟨w, hw, h4⟩ | ⟨hPW, hP⟩
  · exact Or.inl ⟨w, nE_mono X hle hw, h4⟩
  · exact Or.inr ⟨hPW, pWitness_of_le hle hP⟩


end Soundness


section Pair

@[expose] def ExcClass {n : ℕ} (R E₀ : Subgroup (Equiv.Perm (Fin n))) (E : Subgroup ↥R) : Prop :=
  ∃ w ∈ R, E.map R.subtype = E₀.map (MulAut.conj w).toMonoidHom

variable {n : ℕ} {P R E₀ : Subgroup (Equiv.Perm (Fin n))}

theorem excClass_of_map_conj {E : Subgroup ↥R} {w : ↥R}
    (h : ExcClass R E₀ (E.map (MulAut.conj w).toMonoidHom)) : ExcClass R E₀ E := by
  obtain ⟨v, hvR, hv⟩ := h
  refine ⟨(w : Equiv.Perm (Fin n))⁻¹ * v, R.mul_mem (R.inv_mem w.2) hvR, ?_⟩
  have key : (E.map (MulAut.conj w).toMonoidHom).map R.subtype =
      (E.map R.subtype).map (MulAut.conj (w : Equiv.Perm (Fin n))).toMonoidHom := by
    rw [map_map, map_map]
    congr 1
  rw [key] at hv
  calc E.map R.subtype
      = ((E.map R.subtype).map (MulAut.conj (w : Equiv.Perm (Fin n))).toMonoidHom).map
          (MulAut.conj (w : Equiv.Perm (Fin n))⁻¹).toMonoidHom := by
        rw [map_map]
        conv_lhs => rw [← map_id (E.map R.subtype)]
        congr 1
        ext x
        simp [MulAut.conj_apply, mul_assoc]
    _ = (E₀.map (MulAut.conj v).toMonoidHom).map
          (MulAut.conj (w : Equiv.Perm (Fin n))⁻¹).toMonoidHom := by rw [hv]
    _ = E₀.map (MulAut.conj ((w : Equiv.Perm (Fin n))⁻¹ * v)).toMonoidHom := by
        rw [map_map]
        congr 1


end Pair

end CFSG.ComponentClassification.RankTwoSporadic.Cert
