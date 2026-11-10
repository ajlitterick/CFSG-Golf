module

public import CFSG.RankThree.PartTwo.Census.Sporadic.RankFourCert

public section

namespace CFSG.RankThree.PartTwo.Census

open CFSG.Assembly CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native
open scoped Matrix

structure NC2Data where
  base : Data
  inv : ℕ
  conj : ℕ
  conjInv : ℕ
  odd : ℕ
  oddExp : ℕ
  genExp : ℕ
  par : Array ℕ
  lab : Array ℕ
  edges : Array (Array ℕ)
  extra : List (ℕ × ℕ) := []

namespace NC2Data

variable {M V : Type} (O : Ops M V)

@[expose] def regs [Inhabited M] (D : NC2Data) : Array M :=
  O.run D.base.prog (O.initRegs (O.decode D.base.seedA) (O.decode D.base.seedB) D.base.nregs)

@[expose] def gensOf [Inhabited M] (D : NC2Data) (R : Array M) : Array M :=
  (D.base.outs.map fun r => R[r]!).toArray

@[expose] def buildPts [Inhabited M] (gens : Array M) (par lab : Array ℕ) (n : ℕ) : Array M :=
  (List.range n).foldl
    (fun acc i => acc.push (if i = 0 then O.one else O.mul acc[par[i]!]! gens[lab[i]!]!)) #[]

@[expose] def movesOK (tests : List ℕ) (X : M) : Bool :=
  tests.any fun k => O.vne (O.vmul (O.unit k) X) (O.unit k)

@[expose] def conjVec (G P Gi : M) (k : ℕ) : V := O.vmul (O.vmul (O.vmul (O.unit k) G) P) Gi

@[expose] def sig (tests : List ℕ) (X : M) : List V := tests.map fun k => O.vmul (O.unit k) X

@[expose] def vecsNe : List V → List V → Bool
  | u :: us, w :: ws => O.vne u w || vecsNe us ws
  | _, _ => false

@[expose] def progOK (D : NC2Data) : Bool :=
  decide (2 ≤ D.base.nregs) && D.base.prog.all (Op.lt D.base.nregs) &&
    D.base.outs.all (decide <| · < D.base.nregs) && decide (D.inv < D.base.nregs) &&
    decide (D.conj < D.base.nregs) && decide (D.conjInv < D.base.nregs) &&
    decide (D.odd < D.base.nregs)

@[expose] def relOK [Inhabited M] (D : NC2Data) (R : Array M) : Bool :=
  O.eq (O.mul R[D.inv]! R[D.inv]!) O.one && movesOK O D.base.tests R[D.inv]! &&
    D.base.outs.all (fun r => O.commOK R[r]! R[D.inv]!) && O.commOK R[D.conj]! R[D.inv]! &&
    O.commOK R[D.odd]! R[D.inv]! && decide (0 < D.genExp) &&
    D.base.outs.all (fun r => O.eq (O.pow R[r]! D.genExp) O.one) &&
    O.eq (O.mul R[D.conj]! R[D.conjInv]!) O.one && O.eq (O.pow R[D.odd]! D.oddExp) O.one &&
    decide (D.oddExp % 2 = 1) && movesOK O D.base.tests R[D.odd]!

@[expose] def extraOK [Inhabited M] (D : NC2Data) (R : Array M) : Bool :=
  D.extra.all fun rq => decide (rq.1 < D.base.nregs) && decide rq.2.Prime &&
    O.commOK R[rq.1]! R[D.inv]! && O.eq (O.pow R[rq.1]! rq.2) O.one &&
    movesOK O D.base.tests R[rq.1]!

@[expose] def treeOK (D : NC2Data) (ngens : ℕ) : Bool :=
  decide (0 < D.par.size) && decide (D.lab.size = D.par.size) &&
    decide (D.edges.size = D.par.size) &&
    (List.range D.par.size).all (fun i => decide (i = 0) ||
      (decide (D.par[i]! < i) && decide (D.lab[i]! < ngens)))

@[expose] def closedOK [Inhabited M] (gens pts : Array M) (edges : Array (Array ℕ)) (n : ℕ) :
    Bool :=
  (List.range n).all fun i => (List.range gens.size).all fun k =>
    decide ((edges[i]!)[k]! < n) && O.eq (O.mul pts[i]! gens[k]!) pts[(edges[i]!)[k]!]!

@[expose] def distinctOK (sigs : Array (List V)) (n : ℕ) : Bool :=
  (List.range n).all fun j => (List.range j).all fun i => vecsNe O sigs[i]! sigs[j]!

@[expose] def interOK [Inhabited M] (tests : List ℕ) (G Gi X : M) (pts : Array M)
    (sigs : Array (List V)) (n : ℕ) : Bool :=
  (List.range n).all fun i =>
    (let cv := tests.map (conjVec O G pts[i]! Gi)
     (List.range n).all fun j => vecsNe O cv sigs[j]!) ||
    O.commOK X (O.mul (O.mul G pts[i]!) Gi)

@[expose] def check [Inhabited M] (D : NC2Data) : Bool :=
  let R := regs O D
  let gens := gensOf D R
  let pts := buildPts O gens D.par D.lab D.par.size
  let sigs := pts.map (sig O D.base.tests)
  progOK D && relOK O D R && extraOK O D R && treeOK D gens.size &&
    closedOK O gens pts D.edges D.par.size &&
    distinctOK O sigs D.par.size &&
    interOK O D.base.tests R[D.conj]! R[D.conjInv]! R[D.odd]! pts sigs D.par.size


end NC2Data


namespace OpsSpec

variable {M V : Type} {O : Ops M V} {p d : ℕ} (Sp : OpsSpec O p d)
include Sp


theorem toVec_unit_vmul {X : M} (hX : Sp.WF X) (k : ℕ) :
    Sp.toVec (O.vmul (O.unit k) X) = Sp.toVec (O.unit k) ᵥ* Sp.toMat X :=
  Sp.toVec_vmul (Sp.unit_wf k) hX


theorem toMat_ne_one_of_movesOK {tests : List ℕ} {X : M} (hX : Sp.WF X)
    (h : NC2Data.movesOK O tests X = true) : Sp.toMat X ≠ 1 := by
  intro e
  obtain ⟨k, -, hk⟩ := List.any_eq_true.1 h
  apply Sp.toVec_ne hk
  rw [toVec_unit_vmul Sp hX, e, Matrix.vecMul_one]


omit Sp in
theorem normalizer_zpowers_eq_centralizer {U : Type*} [Group U] {t : U} (ht : orderOf t = 2) :
    Subgroup.normalizer ((Subgroup.zpowers t : Subgroup U) : Set U) =
      Subgroup.centralizer ({t} : Set U) := by
  apply le_antisymm
  · intro g hg
    have hmem := (Subgroup.mem_normalizer_iff.mp hg t).mp (Subgroup.mem_zpowers t)
    obtain ⟨k, e⟩ := Subgroup.mem_zpowers_iff.mp hmem
    rw [← zpow_mod_orderOf, ht] at e
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hk : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 := by omega
    rcases hk with hk | hk
    · exfalso
      rw [hk, zpow_zero, eq_comm, conj_eq_one_iff] at e
      rw [e, orderOf_one] at ht
      omega
    · rw [hk, zpow_one] at e
      calc g * t = g * t * g⁻¹ * g := by group
        _ = t * g := by rw [← e]
  · intro g hg
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
    rintro _ ⟨m, rfl⟩
    exact (Commute.zpow_left (Subgroup.mem_centralizer_singleton_iff.1 hg).symm m).eq


end OpsSpec

theorem factorization_two_of_eq {n a m : ℕ} (h : n = 2 ^ a * m) (hm : m % 2 = 1) :
    n.factorization 2 = a := by
  have hm0 : m ≠ 0 := by omega
  rw [h, Nat.factorization_mul (by positivity) hm0, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by omega), add_zero]

theorem excluded433_sporadic_of_not_isCharTwoType {s : TauCeti.SporadicName} {T : Type}
    [Group T] (e : IsSimpleGroup s.Group → Nonempty (s.Group ≃* T)) (hT : ¬ IsCharTwoType T) :
    Excluded433 (.sporadic s) :=
  excluded433_sporadic_of_equiv e fun _ _ _ hG eT => hG.false_of_not_isCharTwoType eT hT

end CFSG.RankThree.PartTwo.Census
