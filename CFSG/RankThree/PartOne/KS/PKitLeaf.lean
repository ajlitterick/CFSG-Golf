module

public import CFSG.RankThree.PartOne.KS.PKit

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Monster.B.Mathieu CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.Certificates.ChainArrays

@[expose] def ptailOKQ (n : ℕ) (L : Array Level) (base : Array ℕ) (x : Array ℕ)
    (xs : Array (Array ℕ)) (rels : List (ℕ × ℕ × ℕ)) (T : Array ℕ → Bool) :
    ℕ → ℕ → Array ℕ → Bool
  | 0, _, acc => !(commA n acc x) || T acc
  | fuel + 1, i, acc => allLt (L[i]!).pts.size fun k =>
      !(relOK base xs rels i acc (L[i]!).pts[k]!) ||
        ptailOKQ n L base x xs rels T fuel (i + 1) (compA n acc (L[i]!).tr[k]!)

section Facts

variable {n : ℕ} {Q : RawSchreierDatum n} {O S : Array (Array ℕ)} {base : Array ℕ}
  {W : Array (List ℤ)} {chunks : ℕ}
  (hA : ChainArrays Q O S base W) (hF : ChainCheckFacts n O S base W chunks)
  (hQ : ValidSchreier Q)
include hA hF hQ

theorem ptailOKQ_spec {x : Array ℕ} {X : Equiv.Perm (Fin n)} (hx : Rep n x X)
    {xs : Array (Array ℕ)} (hxs : ∀ e < xs.size, Rep n xs[e]! (X ^ e))
    {rels : List (ℕ × ℕ × ℕ)}
    (hrels : ∀ r ∈ rels, r.2.2 < xs.size ∧ r.1 < base.size ∧ r.2.1 < base.size ∧
      (xs[r.2.2]!)[base[r.1]!]! = base[r.2.1]!) {T : Array ℕ → Bool} :
    ∀ fuel i, i + fuel = Q.baseCount → ∀ (acc : Array ℕ) (A : Equiv.Perm (Fin n)), Rep n acc A →
      ptailOKQ n (rawLevels n S base) base x xs rels T fuel i acc = true →
      ∀ h ∈ Q.levelSubgroup i, A * h * X = X * (A * h) →
        ∃ e, Rep n e (A * h) ∧ T e = true := by
  intro fuel
  induction fuel with
  | zero =>
    intro i hi acc A hacc htail h hh hcomm
    rw [Nat.add_zero] at hi
    subst hi
    rw [Q.levelSubgroup_terminal_eq_bot hQ, Subgroup.mem_bot] at hh
    subst hh
    rw [mul_one] at hcomm ⊢
    have hc : commA n acc x = true := (commA_iff hacc hx).2 hcomm
    simp only [ptailOKQ, hc, Bool.not_true, Bool.false_or] at htail
    exact ⟨acc, hacc, htail⟩
  | succ fuel ih =>
    intro i hi acc A hacc htail h hh hcomm
    have hib : i < Q.baseCount := by omega
    obtain ⟨k, hk, hpt, hk'⟩ := exists_levT_inv_mul_mem hA hF hQ hib hh
    have hstep := allLt_spec htail hk
    have hcX : Commute (A * h) X := hcomm
    have hbase : ∀ m (hm : m < Q.baseCount), ((Q.base.get ⟨m, hm⟩ : Fin n) : ℕ) = base[m]! :=
      fun m hm => hA.base_val ⟨m, hm⟩
    have himg : ∀ m (hm : m ≤ i), relImg base i acc ((rawLevels n S base)[i]!).pts[k]! m =
        ((A * h) (Q.base.get ⟨m, by omega⟩) : ℕ) := by
      intro m hm
      rcases Nat.lt_or_eq_of_le hm with hlt | rfl
      · rw [relImg, ite_eq_left hlt, ← hbase m (by omega), hacc, Equiv.Perm.mul_apply,
          Q.levelSubgroup_fixes_base_index i h hh ⟨m, by omega⟩ hlt]
      · rw [relImg, ite_eq_right (lt_irrefl _), show ((rawLevels n S base)[m]!).pts[k]! =
          (lev n S base m).pts[k]! from rfl, hpt, hacc, Equiv.Perm.mul_apply]
    have hrel : relOK base xs rels i acc ((rawLevels n S base)[i]!).pts[k]! = true := by
      rw [relOK, List.all_eq_true]
      intro r hr
      obtain ⟨he, hl, hl', hrx⟩ := hrels r hr
      rw [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, beq_iff_eq]
      by_cases hmax : max r.1 r.2.1 = i
      · right
        have hl1 : r.1 ≤ i := hmax ▸ le_max_left _ _
        have hl2 : r.2.1 ≤ i := hmax ▸ le_max_right _ _
        have hbs := hA.base_size
        have hXe : (X ^ r.2.2) (Q.base.get ⟨r.1, by omega⟩) = Q.base.get ⟨r.2.1, by omega⟩ := by
          apply Fin.ext
          rw [← hxs r.2.2 he, hbase r.1 (by omega), hbase r.2.1 (by omega), hrx]
        rw [himg r.2.1 hl2, himg r.1 hl1, hxs r.2.2 he, ← hXe]
        congr 1
        rw [← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply, (hcX.pow_right r.2.2).eq]
      · exact Or.inl hmax
    rw [hrel, Bool.not_true, Bool.false_or] at hstep
    have hrep : Rep n (compA n acc ((rawLevels n S base)[i]!).tr[k]!) (A * levT n S base i k) :=
      rep_compA hacc (hA.rep_levT hF hib hk)
    have e : A * h = A * levT n S base i k * ((levT n S base i k)⁻¹ * h) := by group
    rw [e] at hcomm ⊢
    exact ih (i + 1) (by omega) _ _ hrep hstep _ hk' hcomm

theorem centralizer_subset_of_ptailOKQ {x : Array ℕ} {X : Equiv.Perm (Fin n)} (hx : Rep n x X)
    {xs : Array (Array ℕ)} (hxs : ∀ e < xs.size, Rep n xs[e]! (X ^ e))
    {rels : List (ℕ × ℕ × ℕ)}
    (hrels : ∀ r ∈ rels, r.2.2 < xs.size ∧ r.1 < base.size ∧ r.2.1 < base.size ∧
      (xs[r.2.2]!)[base[r.1]!]! = base[r.2.1]!) {T : Array ℕ → Bool}
    (htail : ptailOKQ n (rawLevels n S base) base x xs rels T Q.baseCount 0 (idA n) = true)
    {g : Equiv.Perm (Fin n)} (hg : g ∈ Subgroup.centralizer {X} ⊓ Q.originalSubgroup) :
    ∃ e, Rep n e g ∧ T e = true := by
  obtain ⟨hgc, hgP⟩ := Subgroup.mem_inf.1 hg
  rw [← Q.levelSubgroup_zero_eq_original hQ] at hgP
  have hcomm : 1 * g * X = X * (1 * g) := by
    rw [one_mul]
    exact Subgroup.mem_centralizer_singleton_iff.1 hgc
  obtain ⟨e, hre, hT⟩ := ptailOKQ_spec hA hF hQ hx hxs hrels Q.baseCount 0 (by omega) (idA n) 1
    rep_idA htail g hgP hcomm
  rw [one_mul] at hre
  exact ⟨e, hre, hT⟩

end Facts

theorem conj_mem_closure_of_gens {G : Type*} [Group G] {T : Set G} {g : G}
    (h : ∀ t ∈ T, g * t * g⁻¹ ∈ Subgroup.closure T) :
    ∀ r ∈ Subgroup.closure T, g * r * g⁻¹ ∈ Subgroup.closure T := by
  intro r hr
  induction hr using Subgroup.closure_induction with
  | mem t ht => exact h t ht
  | one => simp
  | mul a b _ _ ha hb =>
    have e : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ ha hb
  | inv a _ ha =>
    have e : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ ha

@[expose] def bucketIdx (n : ℕ) (a : Array ℕ) : ℕ := a[0]! * n + a[1]!

@[expose] def mkBuckets (n : ℕ) (E : List (Array ℕ)) : Array (List (Array ℕ)) :=
  E.foldl (fun B e => B.set! (bucketIdx n e) (e :: B[bucketIdx n e]!)) (Array.replicate (n * n) [])


@[expose] def leafNC (n : ℕ) (gR : Array (Array ℕ)) (B : Array (List (Array ℕ)))
    (a : Array ℕ) : Bool :=
  let ai := invCand n a
  isInvA n a ai &&
    allLt gR.size (fun l =>
      let c := compA n a (compA n gR[l]! ai)
      (B[bucketIdx n c]!).any (eqA n c)) &&
    (!(allLt gR.size fun l => commA n a gR[l]!) || (B[bucketIdx n a]!).any (eqA n a))


@[expose] def centNormOKP (p n : ℕ) (S : Array (Array ℕ)) (base x : Array ℕ)
    (rels : List (ℕ × ℕ × ℕ)) (gR : Array (Array ℕ)) (ps : List ℕ) (cR : ArrCert) (N : ℕ) :
    Bool :=
  relsOKP p n base x rels && enumOK n gR ps cR && cR.pts.size == N &&
    allLt gR.size (fun k => commA n gR[k]! x) &&
    allLt gR.size (fun k => siftA n (rawLevels n S base) base 0 gR[k]!) &&
    siftA n (rawLevels n S base) base 0 x &&
    ptailOKQ n (rawLevels n S base) base x (powPA p n x) rels
      (leafNC n gR (mkBuckets n cR.pts.toList)) base.size 0 (idA n)

section Spec


end Spec

end CFSG.RankThree.PartOne
