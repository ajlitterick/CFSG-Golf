module

public import CFSG.LieType.Chevalley.E6SignedGraphBruhat

public noncomputable section

namespace CFSG.LieType.Chevalley.E6SignedGraph

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
open scoped Pointwise

variable {K : Type} [Field K]


theorem gen_mem_weylGroup
    (i : Fin 4) : gen i ∈ weylGroup :=
  Subgroup.subset_closure ⟨i, rfl⟩

theorem signedCell_eq
    {x y : ModGL TwistTag.E6.tag K} (hxS : x ∈ rootGenerated K)
    (hyS : y ∈ rootGenerated K) (hxN : x ∈ monomialSubgroup TwistTag.E6.tag K)
    (hyN : y ∈ monomialSubgroup TwistTag.E6.tag K) {w : WeylGroup TwistTag.E6.tag}
    (hxw : MapsRootLines x w) (hyw : MapsRootLines y w) : signedCell K x = signedCell K y := by
  have ht : x * y⁻¹ ∈ torusPart K := by
    have hmaps : MapsRootLines (x * y⁻¹) 1 := by simpa using hxw.mul hyw.inv
    obtain ⟨k, hk, hke⟩ := eq_torus_mul_canonicalRep (mul_mem hxN (inv_mem hyN)) hmaps
    rw [canonicalRep_one, mul_one] at hke
    exact Subgroup.mem_inf.2 ⟨mul_mem hxS (inv_mem hyS), hke ▸ hk⟩
  have hB : x * y⁻¹ ∈ borelPart K := le_sup_left (b := posFixed K) ht
  ext g
  rw [mem_signedCell, mem_signedCell]
  constructor
  · rintro ⟨b, hb, b', hb', rfl⟩
    exact ⟨b * (x * y⁻¹), mul_mem hb hB, b', hb', by group⟩
  · rintro ⟨b, hb, b', hb', rfl⟩
    exact ⟨b * (x * y⁻¹)⁻¹, mul_mem hb (inv_mem hB), b', hb', by group⟩

theorem inv_signedCell
    (x : ModGL TwistTag.E6.tag K) : (signedCell K x)⁻¹ = signedCell K x⁻¹ := by
  ext y
  rw [Set.mem_inv, mem_signedCell, mem_signedCell]
  constructor
  · rintro ⟨b, hb, b', hb', h⟩
    refine ⟨b'⁻¹, inv_mem hb', b⁻¹, inv_mem hb, ?_⟩
    rw [← inv_inv y, ← h]
    group
  · rintro ⟨b, hb, b', hb', rfl⟩
    exact ⟨b'⁻¹, inv_mem hb', b⁻¹, inv_mem hb, by group⟩

theorem simpleOrbit_isRoot
    (i : Fin 4) : ∀ α ∈ simpleOrbit i, IsRoot TwistTag.E6.tag α :=
  fun _ hα => TwistTag.E6.isRoot_of_mem_diagramOrbit (isRoot_simpleRoot i) hα

theorem conj_inv_mem_posFixed_of_pos
    {w : WeylGroup TwistTag.E6.tag} (hw : w ∈ weylGroup)
    {d : ModGL TwistTag.E6.tag K} (hdS : d ∈ rootGenerated K)
    (hdN : d ∈ monomialSubgroup TwistTag.E6.tag K) (hdw : MapsRootLines d w) (i : Fin 4)
    (hpos : 0 < height (w⁻¹ • simpleVec i)) {q : ModGL TwistTag.E6.tag K}
    (hq : q ∈ orbitFixed K (simpleOrbit i)) : d⁻¹ * q * d ∈ posFixed K := by
  have hmap := map_orbitFixed_conj (inv_mem hdN) hdw.inv
    (inv_mem (rootGenerated_le_fixedGroup hdS)) (simpleOrbit_isRoot i)
  have hmem : d⁻¹ * q * d ∈ orbitFixed K ((simpleOrbit i).image fun α => w⁻¹ • α) := by
    rw [← hmap]
    exact ⟨q, hq, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩
  obtain ⟨hP, hPv⟩ := smul_mem_orbits (weylGroup_le_parityGroup (inv_mem hw))
    (simpleOrbit_spec i).1
  have hsub := (height_orbitVec_pos_iff hP).1 (by rw [hPv, (simpleOrbit_spec i).2]; exact hpos)
  exact inf_le_inf_right _ (rootSpan_le_posUnipotent hsub) hmem

theorem conj_inv_mem_posFixed_of_neg
    {w : WeylGroup TwistTag.E6.tag} (hw : w ∈ weylGroup)
    {d : ModGL TwistTag.E6.tag K} (hdS : d ∈ rootGenerated K)
    (hdN : d ∈ monomialSubgroup TwistTag.E6.tag K) (hdw : MapsRootLines d w) (i : Fin 4)
    (hneg : height (w⁻¹ • simpleVec i) < 0) {l : ModGL TwistTag.E6.tag K}
    (hl : l ∈ orbitFixed K ((simpleOrbit i).image fun α => -α)) : d⁻¹ * l * d ∈ posFixed K := by
  have hroots : ∀ α ∈ (simpleOrbit i).image (fun α => -α), IsRoot TwistTag.E6.tag α := by
    intro α hα
    obtain ⟨β, hβ, rfl⟩ := Finset.mem_image.1 hα
    exact IsRoot.neg (simpleOrbit_isRoot i β hβ)
  have hmap := map_orbitFixed_conj (inv_mem hdN) hdw.inv
    (inv_mem (rootGenerated_le_fixedGroup hdS)) hroots
  have hmem : d⁻¹ * l * d ∈
      orbitFixed K (((simpleOrbit i).image fun α => -α).image fun α => w⁻¹ • α) := by
    rw [← hmap]
    exact ⟨l, hl, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩
  obtain ⟨hP, hPv⟩ := smul_mem_orbits (weylGroup_le_parityGroup (inv_mem hw))
    (simpleOrbit_spec i).1
  have hsub := (height_orbitVec_neg_iff hP).1 (by rw [hPv, (simpleOrbit_spec i).2]; exact hneg)
  have hsub' : ∀ α ∈ (((simpleOrbit i).image fun α => -α).image fun α => w⁻¹ • α : Set E6Vec),
      IsRoot TwistTag.E6.tag α ∧ 0 < height α := by
    intro α hα
    obtain ⟨β, hβ, rfl⟩ := Finset.mem_image.1 hα
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.1 hβ
    have h := hsub (Finset.mem_coe.2 (Finset.mem_image_of_mem (fun α => w⁻¹ • α) hγ))
    rw [smul_neg]
    refine ⟨IsRoot.neg h.1, ?_⟩
    rw [height_neg]
    linarith [h.2]
  exact inf_le_inf_right _ (rootSpan_le_posUnipotent hsub') hmem

theorem inversionFixed_gen_le
    (hK : ringChar K ≠ 2) (i : Fin 4) {z : ModGL TwistTag.E6.tag K}
    (hzS : z ∈ rootGenerated K) (hzN : z ∈ monomialSubgroup TwistTag.E6.tag K)
    (hzw : MapsRootLines z (gen i)) :
    inversionFixed K (gen i) ≤ orbitFixed K (simpleOrbit i) := by
  intro u hu
  set Oi := simpleOrbit i with hOi
  have hzΓ := rootGenerated_le_fixedGroup hzS
  have hOiX : Oi ∈ {P | P ∈ orbits ∧ 0 < height (orbitVec P)} :=
    ⟨(simpleOrbit_spec i).1, by rw [(simpleOrbit_spec i).2]; exact (simpleVec_mem_posVecs i).2⟩
  have hfin : ({P | P ∈ orbits ∧ 0 < height (orbitVec P)} \ {Oi}).Finite :=
    finite_diagramRootOrbits.subset fun _ hP => hP.1.1.1
  obtain ⟨m, E, hE⟩ := hfin.fin_embedding
  have hEmem : ∀ j, (E j ∈ orbits ∧ 0 < height (orbitVec (E j))) ∧ E j ≠ Oi := fun j => by
    have h : E j ∈ Set.range E := Set.mem_range_self j
    rw [hE] at h
    exact ⟨h.1, h.2⟩
  set O := Fin.append E (fun _ : Fin 1 => Oi) with hOdef
  have hO : Function.Injective O := Fin.append_injective_iff.2
    ⟨E.injective, fun _ _ _ => Subsingleton.elim _ _, fun j _ h => (hEmem j).2 h⟩
  have hrange : Set.range O = {P | P ∈ orbits ∧ 0 < height (orbitVec P)} := by
    ext P
    constructor
    · rintro ⟨j, rfl⟩
      induction j using Fin.addCases with
      | left j =>
        rw [hOdef, Fin.append_left]
        exact (hEmem j).1
      | right j =>
        rw [hOdef, Fin.append_right]
        exact hOiX
    · intro hP
      by_cases hPO : P = Oi
      · exact ⟨Fin.natAdd m 0, by rw [hOdef, Fin.append_right, hPO]⟩
      · have h : P ∈ Set.range E := by
          rw [hE]
          exact ⟨hP, hPO⟩
        obtain ⟨j, rfl⟩ := h
        exact ⟨Fin.castAdd 1 j, by rw [hOdef, Fin.append_left]⟩
  have huU : u ∈ posFixed K := inversionFixed_le_posFixed (gen i) hu
  have hu' : u ∈ Set.range (fun g : (j : Fin (m + 1)) → ↥(orbitFixed K (O j)) =>
      (List.ofFn fun j => (g j : ModGL TwistTag.E6.tag K)).prod) := by
    rw [(posFixed_list_prod hK O hO hrange).2]
    exact huU
  obtain ⟨g, hg⟩ := hu'
  simp only at hg
  have hOlast : O (Fin.last m) = Oi := Fin.append_right E _ 0
  have hOcast : ∀ j, O (Fin.castSucc j) = E j := fun j => Fin.append_left E _ j
  set P := (List.ofFn fun j => (g (Fin.castSucc j) : ModGL TwistTag.E6.tag K)).prod with hPdef
  set glast := (g (Fin.last m) : ModGL TwistTag.E6.tag K) with hglast
  have hsplit : u = P * glast := by
    rw [← hg, List.ofFn_succ', List.prod_concat]
  have hmemQ : ∀ (Q : Finset E6Vec) (x : ModGL TwistTag.E6.tag K), x ∈ orbitFixed K Q →
      ∀ Q' : Finset E6Vec, Q = Q' → x ∈ orbitFixed K Q' := fun Q x hx Q' hQ => hQ ▸ hx
  have hglastQ : glast ∈ orbitFixed K Oi := hmemQ _ _ (g (Fin.last m)).2 _ hOlast
  have hPpos : z * P * z⁻¹ ∈ posUnipotent TwistTag.E6.tag K := by
    rw [hPdef, conj_ofFn_prod]
    refine Subgroup.list_prod_mem _ fun y hy => ?_
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hy
    have hgj : (g (Fin.castSucc j) : ModGL TwistTag.E6.tag K) ∈ orbitFixed K (E j) :=
      hmemQ _ _ (g (Fin.castSucc j)).2 _ (hOcast j)
    have hroots : ∀ α ∈ E j, IsRoot TwistTag.E6.tag α := fun α hα => by
      obtain ⟨⟨⟨⟨β, hβ, hβE⟩, -⟩, -⟩, -⟩ := hEmem j
      rw [← hβE] at hα
      exact TwistTag.E6.isRoot_of_mem_diagramOrbit hβ hα
    have hconj : z * (g (Fin.castSucc j) : ModGL TwistTag.E6.tag K) * z⁻¹ ∈
        orbitFixed K ((E j).image fun α => gen i • α) := by
      rw [← map_orbitFixed_conj hzN hzw hzΓ hroots]
      exact ⟨_, hgj, rfl⟩
    obtain ⟨hP', hP'v⟩ := smul_mem_orbits (gen_mem_parityGroup i) (hEmem j).1.1
    have hv : orbitVec (E j) ∈ posVecs \ {simpleVec i} := by
      refine ⟨⟨⟨E j, (hEmem j).1.1, rfl⟩, (hEmem j).1.2⟩, fun h => (hEmem j).2 ?_⟩
      exact injOn_orbitVec (hEmem j).1.1 (simpleOrbit_spec i).1
        ((Set.mem_singleton_iff.1 h).trans (simpleOrbit_spec i).2.symm)
    have hgv := (bijOn_gen i).1 hv
    have hsub := (height_orbitVec_pos_iff hP').1 (by rw [hP'v]; exact hgv.1.2)
    exact rootSpan_le_posUnipotent hsub (Subgroup.mem_inf.1 hconj).1
  have hlastneg : z * glast * z⁻¹ ∈ negUnipotent TwistTag.E6.tag K := by
    have hconj : z * glast * z⁻¹ ∈ orbitFixed K (Oi.image fun α => gen i • α) := by
      rw [← map_orbitFixed_conj hzN hzw hzΓ (simpleOrbit_isRoot i)]
      exact ⟨_, hglastQ, rfl⟩
    obtain ⟨hP', hP'v⟩ := smul_mem_orbits (gen_mem_parityGroup i) (simpleOrbit_spec i).1
    have hneg : height (orbitVec (Oi.image fun α => gen i • α)) < 0 := by
      rw [hP'v, (simpleOrbit_spec i).2, gen_smul_simpleVec, height_neg]
      linarith [(simpleVec_mem_posVecs i).2]
    exact rootSpan_le_negUnipotent ((height_orbitVec_neg_iff hP').1 hneg)
      (Subgroup.mem_inf.1 hconj).1
  have huneg : z * u * z⁻¹ ∈ negUnipotent TwistTag.E6.tag K := by
    obtain ⟨k, hk, rfl⟩ := eq_torus_mul_canonicalRep hzN hzw
    have h1 := canonicalRep_conj_mem_negUnipotent (K := K) (Subgroup.mem_inf.1 hu).1
    have h2 := (Subgroup.mem_normalizer_iff.1 (torusGroup_le_normalizer_negUnipotent hk) _).1 h1
    rw [show k * canonicalRep (coxeterSystem TwistTag.E6.tag) K (gen i) * u *
      (k * canonicalRep (coxeterSystem TwistTag.E6.tag) K (gen i))⁻¹ =
        k * (canonicalRep (coxeterSystem TwistTag.E6.tag) K (gen i) * u *
          (canonicalRep (coxeterSystem TwistTag.E6.tag) K (gen i))⁻¹) * k⁻¹ by group]
    exact h2
  have hPneg : z * P * z⁻¹ ∈ negUnipotent TwistTag.E6.tag K := by
    have e : z * P * z⁻¹ = (z * u * z⁻¹) * (z * glast * z⁻¹)⁻¹ := by
      rw [hsplit]
      group
    rw [e]
    exact mul_mem huneg (inv_mem hlastneg)
  have hP1 : z * P * z⁻¹ = 1 := by
    have h := Subgroup.mem_inf.2 ⟨hPpos, hPneg⟩
    rw [posUnipotent_inf_negUnipotent, Subgroup.mem_bot] at h
    exact h
  have hP1' : P = 1 :=
    calc P = z⁻¹ * (z * P * z⁻¹) * z := by group
      _ = z⁻¹ * 1 * z := by rw [hP1]
      _ = 1 := by group
  rw [hsplit, hP1', one_mul]
  exact hglastQ

theorem exists_of_mem_signedCell_gen
    (hK : ringChar K ≠ 2) (i : Fin 4)
    {z : ModGL TwistTag.E6.tag K} (hzS : z ∈ rootGenerated K)
    (hzN : z ∈ monomialSubgroup TwistTag.E6.tag K) (hzw : MapsRootLines z (gen i))
    {y : ModGL TwistTag.E6.tag K} (hy : y ∈ signedCell K z) :
    ∃ b ∈ borelPart K, ∃ q ∈ orbitFixed K (simpleOrbit i), y = b * z * q := by
  obtain ⟨⟨u, h, v⟩, ⟨hu, hh, hv⟩, rfl⟩ :=
    (signed_cell_bijOn (gen_mem_weylGroup i) hzS hzN hzw).2.2 hy
  exact ⟨u * h, mul_mem (le_sup_right (a := torusPart K) hu) (le_sup_left (b := posFixed K) hh),
    v, inversionFixed_gen_le hK i hzS hzN hzw hv, rfl⟩

theorem exists_of_mem_mul
    (hK : ringChar K ≠ 2) (i : Fin 4) {z d : ModGL TwistTag.E6.tag K}
    (hzS : z ∈ rootGenerated K) (hzN : z ∈ monomialSubgroup TwistTag.E6.tag K)
    (hzw : MapsRootLines z (gen i)) {x : ModGL TwistTag.E6.tag K}
    (hx : x ∈ signedCell K z * signedCell K d) :
    ∃ b ∈ borelPart K, ∃ q ∈ orbitFixed K (simpleOrbit i), ∃ b' ∈ borelPart K,
      x = b * z * q * d * b' := by
  obtain ⟨y, hy, y', hy', rfl⟩ := hx
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := mem_signedCell.1 hy'
  have hyb : y * b₁ ∈ signedCell K z := by
    obtain ⟨c₁, hc₁, c₂, hc₂, rfl⟩ := mem_signedCell.1 hy
    exact mem_signedCell.2 ⟨c₁, hc₁, c₂ * b₁, mul_mem hc₂ hb₁, by group⟩
  obtain ⟨b, hb, q, hq, he⟩ := exists_of_mem_signedCell_gen hK i hzS hzN hzw hyb
  refine ⟨b, hb, q, hq, b₂, hb₂, ?_⟩
  calc y * (b₁ * d * b₂) = (y * b₁) * d * b₂ := by group
    _ = b * z * q * d * b₂ := by rw [he]

theorem signedCell_mul_subset
    {z d : ModGL TwistTag.E6.tag K} :
    signedCell K (z * d) ⊆ signedCell K z * signedCell K d := by
  intro x hx
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_signedCell.1 hx
  exact ⟨b * z, mem_signedCell.2 ⟨b, hb, 1, one_mem _, by group⟩, d * b',
    mem_signedCell.2 ⟨1, one_mem _, b', hb', by group⟩, by group⟩

theorem signedCell_mul_of_pos
    (hK : ringChar K ≠ 2) (i : Fin 4) {w : WeylGroup TwistTag.E6.tag}
    (hw : w ∈ weylGroup) {z d : ModGL TwistTag.E6.tag K} (hzS : z ∈ rootGenerated K)
    (hzN : z ∈ monomialSubgroup TwistTag.E6.tag K) (hzw : MapsRootLines z (gen i))
    (hdS : d ∈ rootGenerated K) (hdN : d ∈ monomialSubgroup TwistTag.E6.tag K)
    (hdw : MapsRootLines d w) (hpos : 0 < height (w⁻¹ • simpleVec i)) :
    signedCell K z * signedCell K d = signedCell K (z * d) := by
  refine Set.Subset.antisymm (fun x hx => ?_) signedCell_mul_subset
  obtain ⟨b, hb, q, hq, b', hb', rfl⟩ := exists_of_mem_mul hK i hzS hzN hzw hx
  have hu := conj_inv_mem_posFixed_of_pos hw hdS hdN hdw i hpos hq
  exact mem_signedCell.2 ⟨b, hb, d⁻¹ * q * d * b', mul_mem (le_sup_right (a := torusPart K) hu)
    hb', by group⟩

section Lifts

variable
    {v : Fin 4 → WeylGroup TwistTag.E6.tag} {a : Fin 4 → Fin TwistTag.E6.foldedTag.rank}
  (hva : ∀ i, v i ∈ relWeylTwist TwistTag.E6 ∧ orbitImage (v i) (a i) = simpleOrbit i)
include hva


omit hva in
theorem signedCell_mul_left_inc
    (hK : ringChar K ≠ 2) (i : Fin 4)
    {w : WeylGroup TwistTag.E6.tag} (hw : w ∈ weylGroup) {z d e : ModGL TwistTag.E6.tag K}
    (hz : z ∈ rootGenerated K ∧ z ∈ monomialSubgroup TwistTag.E6.tag K ∧ MapsRootLines z (gen i))
    (hd : d ∈ rootGenerated K ∧ d ∈ monomialSubgroup TwistTag.E6.tag K ∧ MapsRootLines d w)
    (he : e ∈ rootGenerated K ∧ e ∈ monomialSubgroup TwistTag.E6.tag K ∧
      MapsRootLines e (gen i * w))
    (hlen : wordLength (gen i * w) = wordLength w + 1) :
    signedCell K z * signedCell K d = signedCell K e := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h19, -⟩ :=
    E6_signed_graph_root_system_and_Weyl_stabilizer
  have hpos : 0 < height (w⁻¹ • simpleVec i) := by
    rcases lt_trichotomy (height (w⁻¹ • simpleVec i)) 0 with h | h | h
    · have := ((h19 w hw i).2.2 h)
      omega
    · exact absurd h (height_ne_zero_of_mem_vecs (smul_mem_vecs
        (weylGroup_le_parityGroup (inv_mem hw)) ⟨_, (simpleOrbit_spec i).1,
          (simpleOrbit_spec i).2⟩))
    · exact h
  rw [signedCell_eq he.1 (mul_mem hz.1 hd.1) he.2.1 (mul_mem hz.2.1 hd.2.1) he.2.2
    (hz.2.2.mul hd.2.2)]
  exact signedCell_mul_of_pos hK i hw hz.1 hz.2.1 hz.2.2 hd.1 hd.2.1 hd.2.2 hpos


omit hva in
theorem lift_inv
    {x : ModGL TwistTag.E6.tag K} {w : WeylGroup TwistTag.E6.tag}
    (hx : x ∈ rootGenerated K ∧ x ∈ monomialSubgroup TwistTag.E6.tag K ∧ MapsRootLines x w) :
    x⁻¹ ∈ rootGenerated K ∧ x⁻¹ ∈ monomialSubgroup TwistTag.E6.tag K ∧ MapsRootLines x⁻¹ w⁻¹ :=
  ⟨inv_mem hx.1, inv_mem hx.2.1, hx.2.2.inv⟩

omit hva in
theorem signedCell_mul_right_inc
    (hK : ringChar K ≠ 2) (i : Fin 4)
    {w : WeylGroup TwistTag.E6.tag} (hw : w ∈ weylGroup) {z d e : ModGL TwistTag.E6.tag K}
    (hz : z ∈ rootGenerated K ∧ z ∈ monomialSubgroup TwistTag.E6.tag K ∧ MapsRootLines z (gen i))
    (hd : d ∈ rootGenerated K ∧ d ∈ monomialSubgroup TwistTag.E6.tag K ∧ MapsRootLines d w)
    (he : e ∈ rootGenerated K ∧ e ∈ monomialSubgroup TwistTag.E6.tag K ∧
      MapsRootLines e (w * gen i))
    (hlen : wordLength (w * gen i) = wordLength w + 1) :
    signedCell K d * signedCell K z = signedCell K e := by
  have hz' := lift_inv hz
  rw [gen_inv] at hz'
  have he' := lift_inv he
  rw [mul_inv_rev, gen_inv] at he'
  have hlen' : wordLength (gen i * w⁻¹) = wordLength w⁻¹ + 1 := by
    rw [wordLength_inv, ← wordLength_inv (gen i * w⁻¹), mul_inv_rev, inv_inv, gen_inv, hlen]
  have h := signedCell_mul_left_inc hK i (inv_mem hw) hz' (lift_inv hd) he' hlen'
  rw [← inv_signedCell, ← inv_signedCell, ← inv_signedCell, ← mul_inv_rev] at h
  exact inv_injective h


end Lifts

end CFSG.LieType.Chevalley.E6SignedGraph

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
  E6SignedGraph
open scoped Pointwise


end CFSG.LieType.Chevalley
