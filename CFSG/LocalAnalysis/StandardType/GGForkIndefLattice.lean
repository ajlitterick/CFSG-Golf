module

public import CFSG.LocalAnalysis.StandardType.GGFixedRealizedConfig
public import CFSG.LocalAnalysis.StandardType.GGReflClosedIndep

public section

namespace CFSG.StandardType


open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Lattice

@[expose] def ggSRefl {N : Type} [Fintype N] [DecidableEq N] (X : Matrix N N ℤ) (j : N)
    (m : N → ℤ) : N → ℤ :=
  m - (∑ i, X j i * m i) • Pi.single j 1

@[expose] def ggSReflR {N : Type} [Fintype N] [DecidableEq N] (X : Matrix N N ℤ) (j : N)
    (c : N → ℤ) : N → ℤ :=
  c - (∑ i, c i * X i j) • Pi.single j 1

@[expose] def ggSWord {N : Type} [Fintype N] [DecidableEq N] (X : Matrix N N ℤ) :
    List N → (N → ℤ) → (N → ℤ)
  | [], m => m
  | j :: ψ, m => ggSRefl X j (ggSWord X ψ m)

@[expose] def ggSWordR {N : Type} [Fintype N] [DecidableEq N] (X : Matrix N N ℤ) :
    List N → (N → ℤ) → (N → ℤ)
  | [], c => c
  | j :: ψ, c => ggSReflR X j (ggSWordR X ψ c)

end Lattice

section Datum

structure GGExtDatum {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G} {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {N : Type} (ι : Additive ↥Bs ≃+ V) (X : Matrix N N ℤ)
    (φ' : N → MulAut ↥Bs) (h' : N → V) (α' : N → Module.Dual (ZMod p) V) : Prop where
  mem : ∀ o, φ' o ∈ ggInduced ⊤ Bs
  lin : ∀ o w, ggLin (p := p) ι (φ' o) w = w - α' o w • h' o
  pair : ∀ i j, α' i (h' j) = (X i j : ZMod p)
  indep : LinearIndependent (ZMod p) h'
  diag : ∀ j, X j j = 2

private theorem latw_single_cast {p : ℕ} {N : Type} [DecidableEq N] (k i : N) :
    (((Pi.single k (1 : ℤ) : N → ℤ) i : ℤ) : ZMod p) =
      (Pi.single k (1 : ZMod p) : N → ZMod p) i := by
  rw [Pi.single_apply, Pi.single_apply]
  by_cases h : i = k
  · rw [if_pos h, if_pos h]; exact Int.cast_one
  · rw [if_neg h, if_neg h]; exact Int.cast_zero

private theorem latw_single_smul_sum {p : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {N : Type} [Fintype N] [DecidableEq N] (k : N) (v : N → V) :
    ∑ i, ((Pi.single k (1 : ZMod p) : N → ZMod p) i) • v i = v k := by
  refine (Fintype.sum_eq_single k ?_).trans ?_
  · intro i hi
    rw [Pi.single_apply, if_neg hi, zero_smul]
  · rw [Pi.single_apply, if_pos rfl, one_smul]

private theorem latw_single_mul_sum {p : ℕ} {N : Type} [Fintype N] [DecidableEq N]
    (k : N) (f : N → ZMod p) :
    ∑ i, ((Pi.single k (1 : ZMod p) : N → ZMod p) i) * f i = f k := by
  refine (Fintype.sum_eq_single k ?_).trans ?_
  · intro i hi
    rw [Pi.single_apply, if_neg hi, zero_mul]
  · rw [Pi.single_apply, if_pos rfl, one_mul]

private theorem latw_reflect_involutive {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V] {N : Type}
    {ι : Additive ↥Bs ≃+ V} {X : Matrix N N ℤ} {φ' : N → MulAut ↥Bs} {h' : N → V}
    {α' : N → Module.Dual (ZMod p) V} (hD : GGExtDatum ι X φ' h' α') (o : N) (w : V) :
    ggLin (p := p) ι (φ' o) (ggLin (p := p) ι (φ' o) w) = w := by
  rw [hD.lin o, hD.lin o]
  have hα : α' o (w - α' o w • h' o) = -(α' o w) := by
    rw [map_sub, map_smul, smul_eq_mul, hD.pair o o, hD.diag o]
    ring
  rw [hα, neg_smul]
  abel

private theorem latw_inv_reflection {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V] {N : Type}
    {ι : Additive ↥Bs ≃+ V} {X : Matrix N N ℤ} {φ' : N → MulAut ↥Bs} {h' : N → V}
    {α' : N → Module.Dual (ZMod p) V} (hD : GGExtDatum ι X φ' h' α') (o : N) :
    (ggLin (p := p) ι (φ' o))⁻¹ = ggLin (p := p) ι (φ' o) := by
  have hmul : ggLin (p := p) ι (φ' o) * ggLin (p := p) ι (φ' o) = 1 := by
    refine LinearEquiv.ext (fun w => ?_)
    rw [LinearEquiv.mul_apply, latw_reflect_involutive hD o w]
    rfl
  exact inv_eq_of_mul_eq_one_right hmul

private theorem latw_lin_comb {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V] {N : Type}
    [Fintype N] [DecidableEq N]
    {ι : Additive ↥Bs ≃+ V} {X : Matrix N N ℤ} {φ' : N → MulAut ↥Bs} {h' : N → V}
    {α' : N → Module.Dual (ZMod p) V} (hD : GGExtDatum ι X φ' h' α') (j : N) (m : N → ℤ) :
    ggLin (p := p) ι (φ' j) (∑ i, ((m i : ℤ) : ZMod p) • h' i)
      = ∑ i, ((ggSRefl X j m i : ℤ) : ZMod p) • h' i := by
  set C : ZMod p := ∑ i, ((X j i : ℤ) : ZMod p) * ((m i : ℤ) : ZMod p) with hC
  have hα : α' j (∑ i, ((m i : ℤ) : ZMod p) • h' i) = C := by
    rw [hC, map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul, smul_eq_mul, hD.pair j i]
    exact mul_comm _ _
  have hstep : (∑ i, (((m i : ℤ) : ZMod p) - C * ((Pi.single j (1 : ZMod p) : N → ZMod p) i)) •
      h' i) = (∑ i, ((m i : ℤ) : ZMod p) • h' i) - C • h' j := by
    have h1 : ∀ i, (((m i : ℤ) : ZMod p) - C * ((Pi.single j (1 : ZMod p) : N → ZMod p) i)) • h' i
        = ((m i : ℤ) : ZMod p) • h' i - (C * ((Pi.single j (1 : ZMod p) : N → ZMod p) i)) • h' i :=
      fun i => sub_smul _ _ _
    simp only [h1]
    rw [Finset.sum_sub_distrib]
    congr 1
    calc ∑ i, (C * ((Pi.single j (1 : ZMod p) : N → ZMod p) i)) • h' i
        = ∑ i, C • (((Pi.single j (1 : ZMod p) : N → ZMod p) i) • h' i) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [mul_smul]
      _ = C • ∑ i, ((Pi.single j (1 : ZMod p) : N → ZMod p) i) • h' i := (Finset.smul_sum).symm
      _ = C • h' j := by rw [latw_single_smul_sum]
  have hcoef : ∀ i, (((m i : ℤ) : ZMod p) - C * ((Pi.single j (1 : ZMod p) : N → ZMod p) i))
      = ((ggSRefl X j m i : ℤ) : ZMod p) := by
    intro i
    have hgg : ggSRefl X j m i = m i - (∑ k, X j k * m k) * ((Pi.single j (1 : ℤ) : N → ℤ) i) := by
      simp [ggSRefl]
    have hsingle : (((Pi.single j (1 : ℤ) : N → ℤ) i : ℤ) : ZMod p) =
        (Pi.single j (1 : ZMod p) : N → ZMod p) i :=
      latw_single_cast j i
    have hsum : ((∑ k, X j k * m k : ℤ) : ZMod p) = C := by
      rw [hC, Int.cast_sum]
      exact Finset.sum_congr rfl (fun k _ => Int.cast_mul (X j k) (m k))
    rw [hgg, Int.cast_sub, Int.cast_mul, hsingle, hsum]
  calc ggLin (p := p) ι (φ' j) (∑ i, ((m i : ℤ) : ZMod p) • h' i)
      = (∑ i, ((m i : ℤ) : ZMod p) • h' i) - C • h' j := by rw [hD.lin j, hα]
    _ = ∑ i, (((m i : ℤ) : ZMod p) - C * ((Pi.single j (1 : ZMod p) : N → ZMod p) i)) •
          h' i := hstep.symm
    _ = ∑ i, ((ggSRefl X j m i : ℤ) : ZMod p) • h' i := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [hcoef i]

private theorem latw_word_coroot {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V] {N : Type}
    [Fintype N] [DecidableEq N]
    {ι : Additive ↥Bs ≃+ V} {X : Matrix N N ℤ} {φ' : N → MulAut ↥Bs} {h' : N → V}
    {α' : N → Module.Dual (ZMod p) V} (hD : GGExtDatum ι X φ' h' α') (ψ : List N) (k : N) :
    ggLin (p := p) ι ((ψ.map φ').prod) (h' k)
      = ∑ i, ((ggSWord X ψ (Pi.single k 1) i : ℤ) : ZMod p) • h' i := by
  induction ψ with
  | nil =>
      show ggLin (p := p) ι (1 : MulAut ↥Bs) (h' k)
        = ∑ i, (((Pi.single k (1 : ℤ) : N → ℤ) i : ℤ) : ZMod p) • h' i
      rw [map_one]
      rw [show (1 : V ≃ₗ[ZMod p] V) (h' k) = h' k from rfl]
      calc h' k = ∑ i, ((Pi.single k (1 : ZMod p) : N → ZMod p) i) • h' i :=
            (latw_single_smul_sum k h').symm
        _ = ∑ i, (((Pi.single k (1 : ℤ) : N → ℤ) i : ℤ) : ZMod p) • h' i := by
              refine Finset.sum_congr rfl (fun i _ => ?_)
              rw [latw_single_cast]
  | cons j ψ ih =>
      rw [List.map_cons, List.prod_cons, map_mul, LinearEquiv.mul_apply]
      rw [ih]
      rw [latw_lin_comb hD j]
      rfl

private theorem latw_root_reflect {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V] {N : Type}
    {ι : Additive ↥Bs ≃+ V} {X : Matrix N N ℤ} {φ' : N → MulAut ↥Bs} {h' : N → V}
    {α' : N → Module.Dual (ZMod p) V} (hD : GGExtDatum ι X φ' h' α') (i j : N) (v : V) :
    α' i (ggLin (p := p) ι (φ' j) v) = α' i v - ((X i j : ℤ) : ZMod p) * α' j v := by
  rw [hD.lin j, map_sub, map_smul, smul_eq_mul, hD.pair i j]
  ring

private theorem latw_root_split {p : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {N : Type} [Fintype N] [DecidableEq N]
    {X : Matrix N N ℤ} {α' : N → Module.Dual (ZMod p) V} (j : N) (c : N → ℤ) (v : V) :
    ∑ i, ((ggSReflR X j c i : ℤ) : ZMod p) * α' i v
      = ∑ i, ((c i : ℤ) : ZMod p) * α' i v
        - (∑ i, ((c i : ℤ) : ZMod p) * ((X i j : ℤ) : ZMod p)) * α' j v := by
  set S : ZMod p := ∑ i, ((c i : ℤ) : ZMod p) * ((X i j : ℤ) : ZMod p) with hS
  have hgg : ∀ i, ggSReflR X j c i =
      c i - (∑ k, c k * X k j) * ((Pi.single j (1 : ℤ) : N → ℤ) i) := by
    intro i
    simp [ggSReflR]
  have hSc : ∀ i, ((ggSReflR X j c i : ℤ) : ZMod p)
      = ((c i : ℤ) : ZMod p) - S * ((Pi.single j (1 : ZMod p) : N → ZMod p) i) := by
    intro i
    have hsum : ((∑ k, c k * X k j : ℤ) : ZMod p) = S := by
      rw [hS, Int.cast_sum]
      exact Finset.sum_congr rfl (fun k _ => Int.cast_mul (c k) (X k j))
    rw [hgg i, Int.cast_sub, Int.cast_mul, latw_single_cast j i, hsum]
  calc ∑ i, ((ggSReflR X j c i : ℤ) : ZMod p) * α' i v
      = ∑ i, (((c i : ℤ) : ZMod p) - S * ((Pi.single j (1 : ZMod p) : N → ZMod p) i)) * α' i v := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [hSc i]
    _ = ∑ i, (((c i : ℤ) : ZMod p) * α' i v
          - (S * ((Pi.single j (1 : ZMod p) : N → ZMod p) i)) * α' i v) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          ring
    _ = ∑ i, ((c i : ℤ) : ZMod p) * α' i v
          - ∑ i, (S * ((Pi.single j (1 : ZMod p) : N → ZMod p) i)) * α' i v :=
          Finset.sum_sub_distrib _ _
    _ = ∑ i, ((c i : ℤ) : ZMod p) * α' i v - S * α' j v := by
          congr 1
          calc ∑ i, (S * ((Pi.single j (1 : ZMod p) : N → ZMod p) i)) * α' i v
              = S * ∑ i, ((Pi.single j (1 : ZMod p) : N → ZMod p) i) * α' i v := by
                  rw [Finset.mul_sum]
                  refine Finset.sum_congr rfl (fun i _ => ?_)
                  ring
            _ = S * α' j v := by rw [latw_single_mul_sum]
    _ = ∑ i, ((c i : ℤ) : ZMod p) * α' i v
          - (∑ i, ((c i : ℤ) : ZMod p) * ((X i j : ℤ) : ZMod p)) * α' j v := by
          rw [hS]

private theorem latw_root_apply_sum {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V] {N : Type}
    [Fintype N] [DecidableEq N]
    {ι : Additive ↥Bs ≃+ V} {X : Matrix N N ℤ} {φ' : N → MulAut ↥Bs} {h' : N → V}
    {α' : N → Module.Dual (ZMod p) V} (hD : GGExtDatum ι X φ' h' α') (j : N) (c : N → ℤ) (v : V) :
    ∑ i, ((c i : ℤ) : ZMod p) * α' i (ggLin (p := p) ι (φ' j) v)
      = ∑ i, ((ggSReflR X j c i : ℤ) : ZMod p) * α' i v := by
  calc ∑ i, ((c i : ℤ) : ZMod p) * α' i (ggLin (p := p) ι (φ' j) v)
      = ∑ i, ((c i : ℤ) : ZMod p)
          * (α' i v - ((X i j : ℤ) : ZMod p) * α' j v) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [latw_root_reflect hD i j v]
    _ = ∑ i, (((c i : ℤ) : ZMod p) * α' i v
          - (((c i : ℤ) : ZMod p) * ((X i j : ℤ) : ZMod p)) * α' j v) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          ring
    _ = ∑ i, ((c i : ℤ) : ZMod p) * α' i v
          - ∑ i, (((c i : ℤ) : ZMod p) * ((X i j : ℤ) : ZMod p)) * α' j v :=
          Finset.sum_sub_distrib _ _
    _ = ∑ i, ((c i : ℤ) : ZMod p) * α' i v
          - (∑ i, ((c i : ℤ) : ZMod p) * ((X i j : ℤ) : ZMod p)) * α' j v := by
          rw [Finset.sum_mul]
    _ = ∑ i, ((ggSReflR X j c i : ℤ) : ZMod p) * α' i v :=
          (latw_root_split j c v).symm

private theorem latw_word_root {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V] {N : Type}
    [Fintype N] [DecidableEq N]
    {ι : Additive ↥Bs ≃+ V} {X : Matrix N N ℤ} {φ' : N → MulAut ↥Bs} {h' : N → V}
    {α' : N → Module.Dual (ZMod p) V} (hD : GGExtDatum ι X φ' h' α') (ψ : List N) (k : N) :
    ∀ v, α' k ((ggLin (p := p) ι ((ψ.map φ').prod))⁻¹ v)
      = ∑ i, ((ggSWordR X ψ (Pi.single k 1) i : ℤ) : ZMod p) * α' i v := by
  induction ψ with
  | nil =>
      intro v
      show α' k ((ggLin (p := p) ι (1 : MulAut ↥Bs))⁻¹ v)
        = ∑ i, (((Pi.single k (1 : ℤ) : N → ℤ) i : ℤ) : ZMod p) * α' i v
      rw [map_one, inv_one]
      rw [show (1 : V ≃ₗ[ZMod p] V) v = v from rfl]
      calc α' k v = ∑ i, ((Pi.single k (1 : ZMod p) : N → ZMod p) i) * α' i v :=
            (latw_single_mul_sum k (fun i => α' i v)).symm
        _ = ∑ i, (((Pi.single k (1 : ℤ) : N → ℤ) i : ℤ) : ZMod p) * α' i v := by
              refine Finset.sum_congr rfl (fun i _ => ?_)
              rw [latw_single_cast]
  | cons j ψ ih =>
      intro v
      have hP : (List.map φ' (j :: ψ)).prod = φ' j * (List.map φ' ψ).prod := by
        rw [List.map_cons, List.prod_cons]
      rw [hP, map_mul, mul_inv_rev, latw_inv_reflection hD j, LinearEquiv.mul_apply]
      rw [ih (ggLin (p := p) ι (φ' j) v)]
      rw [latw_root_apply_sum hD j]
      rfl

private theorem latw_conj_word {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V] {N : Type}
    [Fintype N] [DecidableEq N]
    {ι : Additive ↥Bs ≃+ V} {X : Matrix N N ℤ} {φ' : N → MulAut ↥Bs} {h' : N → V}
    {α' : N → Module.Dual (ZMod p) V} (hD : GGExtDatum ι X φ' h' α') (ψ : List N) (k : N)
    (w : V) :
    ggLin (p := p) ι ((ψ.map φ').prod * φ' k * ((ψ.map φ').prod)⁻¹) w
      = w - (∑ i, ((ggSWordR X ψ (Pi.single k 1) i : ℤ) : ZMod p) * α' i w) •
          ∑ i, ((ggSWord X ψ (Pi.single k 1) i : ℤ) : ZMod p) • h' i := by
  have hmap : ggLin (p := p) ι ((ψ.map φ').prod * φ' k * ((ψ.map φ').prod)⁻¹)
      = ggLin (p := p) ι ((ψ.map φ').prod) * ggLin (p := p) ι (φ' k)
        * (ggLin (p := p) ι ((ψ.map φ').prod))⁻¹ := by
    rw [map_mul, map_mul, map_inv]
  rw [hmap, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  rw [hD.lin k, map_sub, map_smul]
  rw [show ggLin (p := p) ι ((ψ.map φ').prod)
        ((ggLin (p := p) ι ((ψ.map φ').prod))⁻¹ w) = w from by
      rw [LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]]
  rw [latw_word_coroot hD ψ k, latw_word_root hD ψ k w]

theorem ggExtDatum_word {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {N : Type} [Fintype N] [DecidableEq N]
    {ι : Additive ↥Bs ≃+ V} {X : Matrix N N ℤ} {φ' : N → MulAut ↥Bs} {h' : N → V}
    {α' : N → Module.Dual (ZMod p) V} (hD : GGExtDatum ι X φ' h' α') (ψ : List N) (k : N) :
    ggLin (p := p) ι ((ψ.map φ').prod) (h' k) =
        ∑ i, ((ggSWord X ψ (Pi.single k 1) i : ℤ) : ZMod p) • h' i ∧
      (∀ v, α' k ((ggLin (p := p) ι ((ψ.map φ').prod))⁻¹ v) =
        ∑ i, ((ggSWordR X ψ (Pi.single k 1) i : ℤ) : ZMod p) * α' i v) ∧
      ∀ w, ggLin (p := p) ι ((ψ.map φ').prod * φ' k * ((ψ.map φ').prod)⁻¹) w =
        w - (∑ i, ((ggSWordR X ψ (Pi.single k 1) i : ℤ) : ZMod p) * α' i w) •
          ∑ i, ((ggSWord X ψ (Pi.single k 1) i : ℤ) : ZMod p) • h' i := by
  exact ⟨latw_word_coroot hD ψ k, fun v => latw_word_root hD ψ k v,
    fun w => latw_conj_word hD ψ k w⟩

@[expose] def ggLCoroots {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    (X : Matrix (Option Λ) (Option Λ) ℤ) : Set (Option Λ → ℤ) :=
  {v | ∃ (ψ : List Λ) (i : Λ), v = ggSWord X (ψ.map some) (Pi.single (some i) 1)}


end Datum

end CFSG.StandardType
