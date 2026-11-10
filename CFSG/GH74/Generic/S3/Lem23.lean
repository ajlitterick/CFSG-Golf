module

public import CFSG.GH74.Generic.S3.Lem36

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.Blueprint CFSG.ABGLocalTools Subgroup
open scoped MatrixGroups

section Counting

variable {G : Type} [Group G]

@[expose] def IsSL2Comp (F : Type*) [Field F] (w₁ e : G) (J : Subgroup G) : Prop :=
  J ≤ centralizer ({w₁, e} : Set G) ∧ IsComponent (J.subgroupOf (centralizer ({w₁, e} : Set G))) ∧
    e ∈ J ∧ Nonempty (SL(2, F) ≃* J)

variable {F : Type*} [Field F] {w₁ e : G} {J : Subgroup G}

theorem IsSL2Comp.mem (h : IsSL2Comp F w₁ e J) : e ∈ J := h.2.2.1

theorem IsSL2Comp.iso (h : IsSL2Comp F w₁ e J) : Nonempty (SL(2, F) ≃* J) := h.2.2.2

theorem IsSL2Comp.commute (h : IsSL2Comp F w₁ e J) :
    ∀ j ∈ J, j * w₁ = w₁ * j ∧ j * e = e * j := by
  intro j hj
  have := h.1 hj
  have h1 := mem_centralizer_iff.1 this w₁ (by simp)
  have h2 := mem_centralizer_iff.1 this e (by simp)
  exact ⟨h1.symm, h2.symm⟩

theorem centralizer_pair_mul (w₁ e : G) :
    centralizer ({w₁ * e, e} : Set G) = centralizer ({w₁, e} : Set G) := by
  ext g
  simp only [mem_centralizer_iff, Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp,
    forall_eq]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    have : w₁ * g = g * w₁ := by
      calc w₁ * g = (w₁ * e) * e⁻¹ * g := by group
        _ = (w₁ * e) * (e⁻¹ * g) := by rw [mul_assoc]
        _ = (w₁ * e) * (g * e⁻¹) := by
            congr 1
            have : e * g = g * e := h2
            calc e⁻¹ * g = e⁻¹ * (g * e) * e⁻¹ := by group
              _ = e⁻¹ * (e * g) * e⁻¹ := by rw [this]
              _ = g * e⁻¹ := by group
        _ = g * (w₁ * e) * e⁻¹ := by rw [← mul_assoc, h1, mul_assoc]
        _ = g * w₁ := by group
    exact this
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    calc (w₁ * e) * g = w₁ * (e * g) := by rw [mul_assoc]
      _ = w₁ * (g * e) := by rw [h2]
      _ = (w₁ * g) * e := by rw [mul_assoc]
      _ = (g * w₁) * e := by rw [h1]
      _ = g * (w₁ * e) := by rw [mul_assoc]

theorem IsSL2Comp.mul (h : IsSL2Comp F w₁ e J) : IsSL2Comp F (w₁ * e) e J := by
  unfold IsSL2Comp at *
  rw [centralizer_pair_mul]
  exact h

theorem isComponent_subgroupOf_of_le {L K H : Subgroup G} (hLK : L ≤ K) (hKH : K ≤ H)
    (h : IsComponent (L.subgroupOf H)) : IsComponent (L.subgroupOf K) := by
  refine ⟨?_, ?_⟩
  · exact LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLK).symm
      (LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe (hLK.trans hKH)) h.1)
  · have := h.2.comap (Subgroup.inclusion hKH)
    convert this using 1
    ext x
    simp [Subgroup.mem_subgroupOf]

theorem IsSL2Comp.of_isCompC {I : Subgroup G} {w₁ e : G} (hI : IsCompC I e)
    (hw : I ≤ centralizer ({w₁} : Set G)) (he : e ∈ I) (hF : Nonempty (SL(2, F) ≃* I)) :
    IsSL2Comp F w₁ e I := by
  have hIC : I ≤ centralizer ({w₁, e} : Set G) := by
    intro i hi
    rw [mem_centralizer_iff]
    intro h hh
    rcases hh with rfl | rfl
    · exact (mem_centralizer_singleton_iff.1 (hw hi)).symm
    · exact (mem_centralizer_singleton_iff.1 (hI.1 hi)).symm
  have hCe : centralizer ({w₁, e} : Set G) ≤ centralizer ({e} : Set G) :=
    Subgroup.centralizer_le (by simp)
  exact ⟨hIC, isComponent_subgroupOf_of_le hIC hCe hI.2, he, hF⟩


structure Count23Setup (V : Subgroup G) (w : G) : Prop where
  card_V : Nat.card ↥V = 4
  V_comm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a
  V_sq : ∀ a ∈ V, a * a = 1
  w_sq : w * w = 1
  w_comm : ∀ a ∈ V, a * w = w * a
  w_notin : w ∉ V

@[expose] def Wset (V : Subgroup G) (w : G) : Set G := {g | w * g ∈ V}

@[expose] def Vsharp (V : Subgroup G) : Set G := {a | a ∈ V ∧ a ≠ 1}

variable {V : Subgroup G} {w : G}

theorem Wset_mul {g a : G} (hg : g ∈ Wset V w) (ha : a ∈ V) : g * a ∈ Wset V w := by
  show w * (g * a) ∈ V
  rw [← mul_assoc]
  exact V.mul_mem hg ha

theorem Wset_inv_mul {g h : G} (hg : g ∈ Wset V w) (hh : h ∈ Wset V w) : g⁻¹ * h ∈ V := by
  have := V.mul_mem (V.inv_mem hg) hh
  have e : (w * g)⁻¹ * (w * h) = g⁻¹ * h := by group
  rwa [e] at this


section Layers

variable {F : Type*} [Field F]

@[expose] def S23 (F : Type*) [Field F] (V : Subgroup G) (w : G) : Set (G × G × Subgroup G) :=
  {t | t.1 ∈ Wset V w ∧ t.2.1 ∈ Vsharp V ∧ IsSL2Comp F t.1 t.2.1 t.2.2}

theorem S23_fibre (hs : Count23Setup V w)
    (hD : ∀ w₁ ∈ Wset V w, ∀ e ∈ Vsharp V, ∀ J : Subgroup G, IsSL2Comp F w₁ e J →
      ∀ e' ∈ Vsharp V, e' ≠ e → ∃ j ∈ J, j * e' ≠ e' * j)
    {w₁ e w' e' : G} {J : Subgroup G} (hw₁ : w₁ ∈ Wset V w) (he : e ∈ Vsharp V)
    (hP : IsSL2Comp F w₁ e J) (hw' : w' ∈ Wset V w) (he' : e' ∈ Vsharp V)
    (hP' : IsSL2Comp F w' e' J) : e' = e ∧ (w' = w₁ ∨ w' = w₁ * e) := by
  have hDJ := hD w₁ hw₁ e he J hP
  have hee : e' = e := by
    by_contra hne
    obtain ⟨j, hj, hjn⟩ := hDJ e' he' hne
    exact hjn ((hP'.commute j hj).2)
  refine ⟨hee, ?_⟩
  have ha : w'⁻¹ * w₁ ∈ V := Wset_inv_mul hw' hw₁
  have hcomm : ∀ j ∈ J, j * (w'⁻¹ * w₁) = (w'⁻¹ * w₁) * j := by
    intro j hj
    have h1 := (hP'.commute j hj).1
    have h2 := (hP.commute j hj).1
    have h1' : j * w'⁻¹ = w'⁻¹ * j := by
      calc j * w'⁻¹ = w'⁻¹ * (w' * j) * w'⁻¹ := by group
        _ = w'⁻¹ * (j * w') * w'⁻¹ := by rw [h1]
        _ = w'⁻¹ * j := by group
    calc j * (w'⁻¹ * w₁) = (j * w'⁻¹) * w₁ := by rw [mul_assoc]
      _ = (w'⁻¹ * j) * w₁ := by rw [h1']
      _ = w'⁻¹ * (j * w₁) := by rw [mul_assoc]
      _ = w'⁻¹ * (w₁ * j) := by rw [h2]
      _ = (w'⁻¹ * w₁) * j := by rw [mul_assoc]
  by_cases ha1 : w'⁻¹ * w₁ = 1
  · exact Or.inl (inv_mul_eq_one.1 ha1)
  · right
    by_cases hae : w'⁻¹ * w₁ = e
    · have he2 : e * e = 1 := hs.V_sq e he.1
      have h3 : w₁ = w' * e := by
        calc w₁ = w' * (w'⁻¹ * w₁) := by group
          _ = w' * e := by rw [hae]
      calc w' = w' * e * e := by rw [mul_assoc, he2, mul_one]
        _ = w₁ * e := by rw [← h3]
    · exfalso
      obtain ⟨j, hj, hjn⟩ := hDJ (w'⁻¹ * w₁) ⟨ha, ha1⟩ hae
      exact hjn (hcomm j hj)


theorem S23_eq_image (huniq : ∀ w₁ ∈ Wset V w, ∀ e ∈ Vsharp V, ∃! J : Subgroup G, IsSL2Comp F w₁ e J) :
    ∃ Jf : G → G → Subgroup G,
      (∀ w₁ ∈ Wset V w, ∀ e ∈ Vsharp V, IsSL2Comp F w₁ e (Jf w₁ e) ∧
        ∀ J : Subgroup G, IsSL2Comp F w₁ e J → J = Jf w₁ e) ∧
      S23 F V w = (fun p : G × G => (p.1, p.2, Jf p.1 p.2)) '' (Wset V w ×ˢ Vsharp V) := by
  choose! Jf hJf using huniq
  refine ⟨Jf, hJf, ?_⟩
  ext t
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨(t.1, t.2.1), ⟨h1, h2⟩, ?_⟩
    have := (hJf t.1 h1 t.2.1 h2).2 t.2.2 h3
    ext <;> simp [this]
  · rintro ⟨⟨w₁, e⟩, ⟨h1, h2⟩, rfl⟩
    exact ⟨h1, h2, (hJf w₁ h1 e h2).1⟩


theorem lemma23_A3 [Finite G] (hs : Count23Setup V w)
    (huniq : ∀ w₁ ∈ Wset V w, ∀ e ∈ Vsharp V, ∃! J : Subgroup G, IsSL2Comp F w₁ e J)
    (hD : ∀ w₁ ∈ Wset V w, ∀ e ∈ Vsharp V, ∀ J : Subgroup G, IsSL2Comp F w₁ e J →
      ∀ e' ∈ Vsharp V, e' ≠ e → ∃ j ∈ J, j * e' ≠ e' * j)
    (hcomp : ∀ w₁ ∈ Wset V w, ∀ e ∈ Vsharp V, ∀ J : Subgroup G, IsSL2Comp F w₁ e J → IsCompC J e)
    {v v₁ : G} (hv : v ∈ Vsharp V) (hv₁ : v₁ ∈ Vsharp V) (hne : v ≠ v₁) :
    ∃ J₀ J₁ J₂ : Subgroup G,
      IsSL2Comp F w v J₀ ∧ IsSL2Comp F w v₁ J₁ ∧ IsSL2Comp F (w * v₁) v J₂ ∧ J₀ ≠ J₂ ∧
      (∀ a ∈ J₀, ∀ b ∈ J₂, a * b = b * a) ∧
      GLS.LU.IsCentralInvolutionIn v J₀ ∧ GLS.LU.IsCentralInvolutionIn v₁ J₁ ∧
      GLS.LU.IsCentralInvolutionIn v J₂ ∧ A3Reflection w v₁ ![J₀, J₁, J₂] ∧
      (∀ I : Subgroup G, IsSL2Comp F w v I → I = J₀) ∧ (∀ I : Subgroup G, IsSL2Comp F w v₁ I → I = J₁) ∧
      (∀ I : Subgroup G, IsSL2Comp F (w * v₁) v I → I = J₂) := by
  have hwW : w ∈ Wset V w := by
    show w * w ∈ V
    rw [hs.w_sq]
    exact V.one_mem
  have hw₂ : w * v₁ ∈ Wset V w := Wset_mul hwW hv₁.1
  obtain ⟨Jf, hJf, -⟩ := S23_eq_image huniq
  have hP₀ := (hJf w hwW v hv).1
  have hP₁ := (hJf w hwW v₁ hv₁).1
  have hP₂ := (hJf (w * v₁) hw₂ v hv).1
  have hne02 : Jf w v ≠ Jf (w * v₁) v := by
    intro heq
    have hP₂' : IsSL2Comp F (w * v₁) v (Jf w v) := heq ▸ hP₂
    obtain ⟨-, h⟩ := S23_fibre hs hD hwW hv hP₀ hw₂ hv hP₂'
    rcases h with h | h
    · exact hv₁.2 (mul_eq_left.1 h)
    · exact hne (mul_left_cancel h).symm
  have hcent : ∀ {w₁ e : G} {J : Subgroup G}, e ∈ Vsharp V → IsSL2Comp F w₁ e J →
      GLS.LU.IsCentralInvolutionIn e J := by
    intro w₁ e J he hP
    refine ⟨hP.mem, orderOf_eq_prime (by rw [sq]; exact hs.V_sq e he.1) he.2, fun u hu => ?_⟩
    exact (hP.commute u hu).2
  refine ⟨Jf w v, Jf w v₁, Jf (w * v₁) v, hP₀, hP₁, hP₂, hne02, ?_, hcent hv hP₀, hcent hv₁ hP₁,
    hcent hv hP₂, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rcases (hcomp w hwW v hv _ hP₀).eq_or_commute (hcomp (w * v₁) hw₂ v hv _ hP₂) with h | h
    · exact absurd h hne02
    · exact h
  · intro g hg
    exact (hP₀.commute g hg).1
  · intro g hg
    exact (hP₁.commute g hg).1
  · intro g hg
    exact (hP₂.commute g hg).1
  · exact fun I hI => (hJf w hwW v hv).2 I hI
  · exact fun I hI => (hJf w hwW v₁ hv₁).2 I hI
  · exact fun I hI => (hJf (w * v₁) hw₂ v hv).2 I hI

end Layers

end Counting


end CFSG.GH74.Generic.S3
