
module

public import CFSG.Sporadic.Co1.Module.InvSpec
public import Certificates.Data.CFSGNative.Co1.TwoB

public section

namespace CFSG.Sporadic.Co1.Module.TwoB

open CFSG.Blueprint CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Co1.InvNative CFSG.Sporadic.Co1.TwoBNative Matrix

theorem validRows_getD {x : Array ℕ} (h : validRows x = true) (j : ℕ) :
    x[j]?.getD 0 < 2 ^ 24 := by
  by_cases hj : j < x.size
  · simp only [validRows, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true, decide_eq_true_eq] at h
    have := h.2 j hj
    simpa [hj] using this
  · simp [Array.getElem?_eq_none (not_lt.1 hj)]

theorem validRows_mulRows {X Y : Array ℕ} (hX : validRows X = true) (hY : validRows Y = true) :
    validRows (mulRows 24 X Y) = true := by
  have hXs := validRows_size hX
  simp only [validRows, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true, decide_eq_true_eq]
  refine ⟨by simp [mulRows, hXs], fun i hi => ?_⟩
  simp only [mulRows, Array.getElem_map]
  exact vecMulN_lt Y (validRows_getD hY) _

theorem gtOK_sound {G : Array (Array ℕ)} {T : GTree} (h : gtOK G T = true)
    (gg : ℕ → NativeSporadic.Co1) (hg : ∀ l < G.size, matHom (gg l) = rowsMatrix 24 G[l]!) :
    ∃ f : ℕ → NativeSporadic.Co1,
      (∀ i < T.pts.size, f i ∈ Submonoid.closure (gg '' {l | l < G.size}) ∧
        matHom (f i) = rowsMatrix 24 T.pts[i]!) ∧
      (∀ i < T.pts.size, ∀ j < T.pts.size, f i = f j → i = j) ∧
      (∀ i < T.pts.size, ∀ l < G.size, ∃ j < T.pts.size, f j = f i * gg l) ∧
      f 0 = 1 ∧ 0 < T.pts.size := by
  unfold gtOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨hpos, hpar⟩, hlab⟩, hall⟩, hdist⟩, hclosed⟩ := h
  have hpt := CFSG.Sporadic.Th.allIn_eq_true.1 hall
  have hvalid : ∀ i < T.pts.size, validRows T.pts[i]! = true := by
    intro i hi
    have hp := hpt i (Nat.zero_le _) hi
    simp only [gtPointOK, Bool.and_eq_true] at hp
    exact hp.1
  have hroot : T.pts[0]! = idRows 24 := by
    have hp := hpt 0 (Nat.zero_le _) hpos
    simp only [gtPointOK, Bool.and_eq_true, beq_self_eq_true, ↓reduceIte, beq_iff_eq] at hp
    exact hp.2
  have hmain : ∀ i < T.pts.size, ∃ x ∈ Submonoid.closure (gg '' {l | l < G.size}),
      matHom x = rowsMatrix 24 T.pts[i]! := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      have hp := hpt i (Nat.zero_le _) hi
      simp only [gtPointOK, Bool.and_eq_true] at hp
      obtain ⟨-, hp2⟩ := hp
      by_cases hi0 : i = 0
      · subst hi0
        refine ⟨1, Submonoid.one_mem _, ?_⟩
        rw [hroot, map_one, rowsMatrix_idRows]
      · simp only [beq_iff_eq, hi0, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hp2
        obtain ⟨⟨hpar', hlab'⟩, hpt'⟩ := hp2
        obtain ⟨x', hx', hxe⟩ := ih (T.par[i]!) hpar' (by omega)
        refine ⟨x' * gg (T.lab[i]!), Submonoid.mul_mem _ hx'
          (Submonoid.subset_closure ⟨_, hlab', rfl⟩), ?_⟩
        rw [hpt', rowsMatrix_mulRows, map_mul, hxe, hg _ hlab']
  choose! x hx using hmain
  have hinj : ∀ i < T.pts.size, ∀ j < T.pts.size, x i = x j → i = j := by
    intro i hi j hj hij
    have hm : rowsMatrix 24 T.pts[i]! = rowsMatrix 24 T.pts[j]! := by
      rw [← (hx i hi).2, ← (hx j hj).2, hij]
    have hpe := rowsMatrix_injective_of_valid (hvalid i hi) (hvalid j hj) hm
    have hnd := distinctKeys_nodup hdist
    have hlen : (T.pts.toList.map rowsKey).length = T.pts.size := by simp
    have hgi : (T.pts.toList.map rowsKey)[i]'(hlen ▸ hi) = rowsKey T.pts[i]! := by
      simp [getElem!_pos T.pts i hi]
    have hgj : (T.pts.toList.map rowsKey)[j]'(hlen ▸ hj) = rowsKey T.pts[j]! := by
      simp [getElem!_pos T.pts j hj]
    exact (List.Nodup.getElem_inj_iff hnd).1
      (hgi.trans ((congrArg rowsKey hpe).trans hgj.symm))
  have hclosed' : ∀ i < T.pts.size, ∀ l < G.size,
      ∃ j < T.pts.size, T.pts[j]! = mulRows 24 T.pts[i]! G[l]! := by
    intro i hi l hl
    unfold gtClosed at hclosed
    have h1 := CFSG.Sporadic.Th.allIn_eq_true.1 hclosed i (Nat.zero_le _) hi
    have h2 := CFSG.Sporadic.Th.allIn_eq_true.1 h1 l (Nat.zero_le _) hl
    rw [Std.HashSet.contains_ofList] at h2
    have h3 := List.contains_iff_mem.1 h2
    obtain ⟨j, hj, hje⟩ := List.getElem_of_mem h3
    have hj' : j < T.pts.size := by simpa using hj
    refine ⟨j, hj', ?_⟩
    rw [getElem!_pos T.pts j hj']
    simpa using hje
  refine ⟨x, fun i hi => ⟨(hx i hi).1, (hx i hi).2⟩, hinj, ?_, ?_, hpos⟩
  · intro i hi l hl
    obtain ⟨j, hj, hje⟩ := hclosed' i hi l hl
    refine ⟨j, hj, ?_⟩
    apply matHom_injective
    rw [(hx j hj).2, hje, rowsMatrix_mulRows, map_mul, (hx i hi).2, hg l hl]
  · apply matHom_injective
    rw [(hx 0 hpos).2, hroot, rowsMatrix_idRows, map_one]

theorem gtOK_closure_eq [Finite NativeSporadic.Co1] {G : Array (Array ℕ)} {T : GTree}
    (h : gtOK G T = true) (gg : ℕ → NativeSporadic.Co1)
    (hg : ∀ l < G.size, matHom (gg l) = rowsMatrix 24 G[l]!) :
    ∃ f : ℕ → NativeSporadic.Co1,
      (∀ i < T.pts.size, matHom (f i) = rowsMatrix 24 T.pts[i]!) ∧
      Set.InjOn f (Set.Iio T.pts.size) ∧
      (Subgroup.closure (gg '' {l | l < G.size}) : Set NativeSporadic.Co1) =
        f '' Set.Iio T.pts.size := by
  obtain ⟨f, hf1, hf2, hf3, hf4, hpos⟩ := gtOK_sound h gg hg
  refine ⟨f, fun i hi => (hf1 i hi).2, fun i hi j hj e => hf2 i hi j hj e, ?_⟩
  have hsub : ((Subgroup.closure (gg '' {l | l < G.size}) : Subgroup NativeSporadic.Co1) :
      Set NativeSporadic.Co1) = Submonoid.closure (gg '' {l | l < G.size}) := by
    have := congrArg (fun K : Submonoid NativeSporadic.Co1 => (K : Set NativeSporadic.Co1))
      (Subgroup.closure_toSubmonoid_of_finite (s := gg '' {l | l < G.size}))
    simpa using this
  rw [hsub]
  ext x
  constructor
  · intro hx
    induction hx using Submonoid.closure_induction_right with
    | one => exact ⟨0, hpos, hf4⟩
    | mul_right x _ y hy ih =>
      obtain ⟨i, hi, rfl⟩ := ih
      obtain ⟨l, hl, rfl⟩ := hy
      obtain ⟨j, hj, hje⟩ := hf3 i hi l hl
      exact ⟨j, hj, hje⟩
  · rintro ⟨i, hi, rfl⟩
    exact (hf1 i hi).1

theorem gtOK_card [Finite NativeSporadic.Co1] {G : Array (Array ℕ)} {T : GTree}
    (h : gtOK G T = true) (gg : ℕ → NativeSporadic.Co1)
    (hg : ∀ l < G.size, matHom (gg l) = rowsMatrix 24 G[l]!) :
    Nat.card ↥(Subgroup.closure (gg '' {l | l < G.size})) = T.pts.size := by
  obtain ⟨f, -, hinj, heq⟩ := gtOK_closure_eq h gg hg
  have h1 : Nat.card ↥(Subgroup.closure (gg '' {l | l < G.size})) =
      ((Subgroup.closure (gg '' {l | l < G.size}) : Subgroup NativeSporadic.Co1) :
        Set NativeSporadic.Co1).ncard :=
    Nat.card_coe_set_eq (Subgroup.closure (gg '' {l | l < G.size}) : Set NativeSporadic.Co1)
  rw [h1, heq, Set.InjOn.ncard_image hinj, Set.ncard_Iio_nat]


end CFSG.Sporadic.Co1.Module.TwoB
