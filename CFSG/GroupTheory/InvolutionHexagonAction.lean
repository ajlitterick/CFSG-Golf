module

public import CFSG.GroupTheory.InvolutionHexagonLines
public import CFSG.GroupTheory.InvolutionHexagonMoore

public section

namespace CFSG.GroupTheory.InvolutionHexagon

open CFSG.Assembly CFSG.GroupTheory.SevenInvolutionWreathLaw CFSG.LinearGroups.UnitaryThreeOverNine

variable {G : Type*} [Group G]

@[expose] def conjPoint (g : G) (p : {x : G // orderOf x = 2}) : {x : G // orderOf x = 2} :=
  ⟨MulAut.conj g p, by rw [MulEquiv.orderOf_eq]; exact p.2⟩

theorem coe_conjPoint (g : G) (p : {x : G // orderOf x = 2}) :
    (conjPoint g p : G) = g * p * g⁻¹ :=
  MulAut.conj_apply g p

theorem conjPoint_one (p : {x : G // orderOf x = 2}) : conjPoint 1 p = p :=
  Subtype.ext (by rw [coe_conjPoint, one_mul, inv_one, mul_one])

theorem conjPoint_mul (g g' : G) (p : {x : G // orderOf x = 2}) :
    conjPoint (g * g') p = conjPoint g (conjPoint g' p) :=
  Subtype.ext (by simp only [coe_conjPoint, mul_inv_rev, mul_assoc])

@[expose] def conjLine (g : G) (T : InvLine G) : InvLine G :=
  ⟨MulAut.conj g '' T.1, by
    obtain ⟨u, v, hu, hv, huv, hc, hT⟩ := T.2
    refine ⟨MulAut.conj g u, MulAut.conj g v, by rw [MulEquiv.orderOf_eq]; exact hu,
      by rw [MulEquiv.orderOf_eq]; exact hv, (MulAut.conj g).injective.ne huv,
      by rw [← map_mul, ← map_mul, hc], ?_⟩
    rw [hT, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton, map_mul]⟩

theorem conjPoint_mem_conjLine (g : G) (p : {x : G // orderOf x = 2}) (T : InvLine G) :
    (conjPoint g p : G) ∈ (conjLine g T).1 ↔ (p : G) ∈ T.1 :=
  (MulAut.conj g).injective.mem_set_image

theorem conjLine_one (T : InvLine G) : conjLine 1 T = T :=
  Subtype.ext (by
    show MulAut.conj (1 : G) '' T.1 = T.1
    rw [map_one, MulAut.coe_one, Set.image_id])

theorem conjLine_mul (g g' : G) (T : InvLine G) :
    conjLine (g * g') T = conjLine g (conjLine g' T) :=
  Subtype.ext (by
    show MulAut.conj (g * g') '' T.1 = MulAut.conj g '' (MulAut.conj g' '' T.1)
    rw [map_mul, MulAut.coe_mul, Set.image_comp])

@[expose] def conjAut (g : G) : incidenceGraph (invInc G) ≃g incidenceGraph (invInc G) where
  toFun := Sum.map (conjPoint g) (conjLine g)
  invFun := Sum.map (conjPoint g⁻¹) (conjLine g⁻¹)
  left_inv := by
    rintro (p | T)
    · rw [Sum.map_inl, Sum.map_inl, ← conjPoint_mul, inv_mul_cancel, conjPoint_one]
    · rw [Sum.map_inr, Sum.map_inr, ← conjLine_mul, inv_mul_cancel, conjLine_one]
  right_inv := by
    rintro (p | T)
    · rw [Sum.map_inl, Sum.map_inl, ← conjPoint_mul, mul_inv_cancel, conjPoint_one]
    · rw [Sum.map_inr, Sum.map_inr, ← conjLine_mul, mul_inv_cancel, conjLine_one]
  map_rel_iff' := by
    rintro (p | T) (q | T')
    · simp only [Equiv.coe_fn_mk, Sum.map_inl, not_incidenceGraph_adj_inl_inl]
    · simp only [Equiv.coe_fn_mk, Sum.map_inl, Sum.map_inr, incidenceGraph_adj_inl_inr]
      exact conjPoint_mem_conjLine g p T'
    · simp only [Equiv.coe_fn_mk, Sum.map_inl, Sum.map_inr, incidenceGraph_adj_inr_inl]
      exact conjPoint_mem_conjLine g q T
    · simp only [Equiv.coe_fn_mk, Sum.map_inr, not_incidenceGraph_adj_inr_inr]

theorem conjAut_inl (g : G) (p : {x : G // orderOf x = 2}) :
    conjAut g (Sum.inl p) = Sum.inl (conjPoint g p) :=
  rfl

theorem conjAut_inr (g : G) (T : InvLine G) : conjAut g (Sum.inr T) = Sum.inr (conjLine g T) :=
  rfl

variable (G) in
@[expose] def conjAction : G →* (incidenceGraph (invInc G) ≃g incidenceGraph (invInc G)) where
  toFun := conjAut
  map_one' := RelIso.ext fun v => by
    rcases v with p | T
    · rw [conjAut_inl, conjPoint_one]
      rfl
    · rw [conjAut_inr, conjLine_one]
      rfl
  map_mul' g g' := RelIso.ext fun v => by
    rcases v with p | T
    · rw [conjAut_inl, conjPoint_mul, RelIso.mul_apply, conjAut_inl, conjAut_inl]
    · rw [conjAut_inr, conjLine_mul, RelIso.mul_apply, conjAut_inr, conjAut_inr]

theorem conjAction_apply (g : G) : conjAction G g = conjAut g :=
  rfl


theorem conjAction_injective [IsSimpleGroup G] [Finite G]
    (hcard : Nat.card {g : G // orderOf g = 2} = 63)
    (hval : ∀ z : {g : G // orderOf g = 2}, ((involutionGraph G).neighborSet z).ncard = 6) :
    Function.Injective (conjAction G) := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (conjAction G).ker with h | h
  · exact (MonoidHom.ker_eq_bot_iff _).mp h
  · exfalso
    obtain ⟨p⟩ : Nonempty {g : G // orderOf g = 2} :=
      (Nat.card_pos_iff.mp (by rw [hcard]; norm_num)).1
    have hall : ∀ q : {g : G // orderOf g = 2}, q ≠ p → (involutionGraph G).Adj p q := by
      intro q hqp
      have hq : (q : G) ∈ (conjAction G).ker := by rw [h]; exact Subgroup.mem_top _
      have := DFunLike.congr_fun (MonoidHom.mem_ker.mp hq) (Sum.inl p)
      rw [conjAction_apply, conjAut_inl, RelIso.one_apply, Sum.inl.injEq] at this
      have hc : (q : G) * p * (q : G)⁻¹ = p := by rw [← coe_conjPoint, this]
      refine adj_iff_ne_and_commute.mpr ⟨Ne.symm hqp, ?_⟩
      calc (p : G) * q = (q * p * (q : G)⁻¹) * q := by rw [hc]
        _ = q * p := by group
    have hset : (involutionGraph G).neighborSet p = Set.univ \ {p} := by
      ext q
      simp only [SimpleGraph.mem_neighborSet, Set.mem_sdiff, Set.mem_univ, true_and,
        Set.mem_singleton_iff]
      exact ⟨fun hadj => fun hqp => (hqp ▸ hadj).ne rfl, fun hqp => hall q hqp⟩
    have h6 := hval p
    rw [hset, Set.ncard_sdiff_singleton_of_mem (Set.mem_univ p), Set.ncard_univ, hcard] at h6
    omega


theorem dist_le_two_of_commute {x y z : {g : G // orderOf g = 2}} (hxy : (x : G) * y = y * x)
    (hyz : (y : G) * z = z * y) : (involutionGraph G).dist x z ≤ 2 := by
  by_cases hxz : x = z
  · rw [hxz, SimpleGraph.dist_self]
    omega
  by_cases hc : (x : G) * z = z * x
  · have hadj : (involutionGraph G).Adj x z := adj_iff_ne_and_commute.mpr ⟨hxz, hc⟩
    have := SimpleGraph.dist_le (SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil)
    rw [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at this
    omega
  · have hxy' : x ≠ y := by
      rintro rfl
      exact hc hyz
    have hyz' : y ≠ z := by
      rintro rfl
      exact hc hxy
    have h1 : (involutionGraph G).Adj x y := adj_iff_ne_and_commute.mpr ⟨hxy', hxy⟩
    have h2 : (involutionGraph G).Adj y z := adj_iff_ne_and_commute.mpr ⟨hyz', hyz⟩
    have := SimpleGraph.dist_le (SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2
      SimpleGraph.Walk.nil))
    rw [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_cons,
      SimpleGraph.Walk.length_nil] at this
    exact this

theorem eq_one_of_conj_eq [Finite G] {x z : {g : G // orderOf g = 2}} {S : Subgroup G}
    (hS : Nat.card S = 32) (hSx : ∀ s ∈ S, s * (x : G) = x * s)
    (hz : (involutionGraph G).dist x z = 3) {s : G} (hs : s ∈ S) (hsz : s * z * s⁻¹ = z) :
    s = 1 := by
  by_contra hs1
  set C : Subgroup G := S ⊓ Subgroup.centralizer {(z : G)} with hC
  have hsC : s ∈ C := ⟨hs, Subgroup.mem_centralizer_singleton_iff.mpr (by
    calc s * z = (s * z * s⁻¹) * s := by group
      _ = z * s := by rw [hsz])⟩
  have hC1 : Nat.card C ≠ 1 := by
    intro h1
    have hbot := Subgroup.eq_bot_of_card_eq C h1
    rw [hbot] at hsC
    exact hs1 (Subgroup.mem_bot.mp hsC)
  have hdvd : Nat.card C ∣ 2 ^ 5 := by
    have := Subgroup.card_dvd_of_le (inf_le_left : C ≤ S)
    rwa [hS] at this
  obtain ⟨k, hk5, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have h2 : 2 ∣ Nat.card C := by
    rcases k with _ | k
    · exact absurd (by rw [hk, pow_zero]) hC1
    · rw [hk, pow_succ]
      exact dvd_mul_left 2 _
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hy2 : orderOf (y : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hy
  have hxy : (x : G) * y = y * x := (hSx y y.2.1).symm
  have hyz : (y : G) * z = z * y := Subgroup.mem_centralizer_singleton_iff.mp y.2.2
  have := dist_le_two_of_commute (y := ⟨(y : G), hy2⟩) hxy hyz
  omega


end CFSG.GroupTheory.InvolutionHexagon
