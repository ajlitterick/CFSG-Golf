module

public import CFSG.ClassicalInvolution.Balance.BootstrapFrameFactsRankFour

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Generic.DeltaClosure (OmegaConnected)
open scoped commutatorElement

section NAdj

variable {G : Type} [Group G]

@[expose] def NAdj (z : G) (J L : Subgroup G) : Prop :=
  ∀ x ∈ J, ∀ y ∈ L, ⁅x, y⁆ ∈ oddCoreIn (Subgroup.centralizer ({z} : Set G))

theorem NAdj.symm {z : G} {J L : Subgroup G} (h : NAdj z J L) : NAdj z L J := fun x hx y hy => by
  have := (oddCoreIn (Subgroup.centralizer ({z} : Set G))).inv_mem (h y hy x hx)
  rwa [commutatorElement_inv] at this


theorem NAdj.mono {z : G} {J L J' L' : Subgroup G} (h : NAdj z J L) (hJ : J' ≤ J) (hL : L' ≤ L) :
    NAdj z J' L' := fun x hx y hy => h x (hJ hx) y (hL hy)

end NAdj

section Conj

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_centralizes_of_commutator_mem {z u : G} {A : Subgroup G} (hA : IsPGroup 2 A)
    (hAC : A ≤ Subgroup.centralizer ({z} : Set G)) (hu : u * u = 1)
    (huC : u ∈ Subgroup.centralizer ({z} : Set G))
    (hcomm : ∀ x ∈ A, ⁅x, u⁆ ∈ oddCoreIn (Subgroup.centralizer ({z} : Set G))) :
    ∃ n ∈ oddCoreIn (Subgroup.centralizer ({z} : Set G)),
      ∀ x ∈ A, x * (n * u * n⁻¹) = (n * u * n⁻¹) * x := by
  have hu' : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  obtain ⟨n, hn, hfix⟩ := exists_conj_fixed_of_isPGroup (A := A)
    (N := oddCoreIn (Subgroup.centralizer ({z} : Set G))) hA (odd_card_oddCoreIn _)
    (fun x hx m hm => conj_mem_oddCoreIn (hAC hx) hm) hu
    (fun m hm => conj_mem_oddCoreIn huC hm) (by
      intro x hx
      have h1 := (oddCoreIn (Subgroup.centralizer ({z} : Set G))).inv_mem (hcomm x hx)
      rw [commutatorElement_inv] at h1
      have e : u * (x * u * x⁻¹) = ⁅u, x⁆ := by
        simp only [commutatorElement_def, hu']
        group
      rw [e]
      exact h1)
  refine ⟨n, hn, fun x hx => ?_⟩
  have := hfix x hx
  exact mul_inv_eq_iff_eq_mul.mp this

theorem exists_conj_commute_of_nadj {z t u : G} {J L : Subgroup G} (hJL : NAdj z J L)
    (hJC : J ≤ Subgroup.centralizer ({z} : Set G)) (hLC : L ≤ Subgroup.centralizer ({z} : Set G))
    (htJ : t ∈ J) (huL : u ∈ L) (ht : t * t = 1) (hu : u * u = 1) :
    ∃ n ∈ oddCoreIn (Subgroup.centralizer ({z} : Set G)),
      t * (n * u * n⁻¹) = (n * u * n⁻¹) * t := by
  obtain ⟨n, hn, h⟩ := exists_conj_centralizes_of_commutator_mem
    (A := Subgroup.zpowers t) (isPGroup_zpowers_of_mul_self_eq_one ht)
    ((Subgroup.zpowers_le.mpr htJ).trans hJC) hu (hLC huL)
    (fun x hx => hJL x ((Subgroup.zpowers_le.mpr htJ) hx) u huL)
  exact ⟨n, hn, h t (Subgroup.mem_zpowers t)⟩

end Conj

section Equivariance

variable {G : Type} [Group G] [Finite G]

theorem oddCoreIn_conjSub_eq (g : G) (X : Subgroup G) :
    oddCoreIn (conjSub g X) = conjSub g (oddCoreIn X) := by
  have key : ∀ (g : G) (X : Subgroup G), conjSub g (oddCoreIn X) ≤ oddCoreIn (conjSub g X) := by
    intro g X
    refine le_oddCoreIn_of_normalizes (conjSub_mono (oddCoreIn_le X)) ?_ ?_
    · intro y hy
      rw [Subgroup.mem_normalizer_iff]
      intro s
      have hy' : g⁻¹ * y * g ∈ X := mem_conjSub_iff.mp hy
      have e : g⁻¹ * (y * s * y⁻¹) * g = (g⁻¹ * y * g) * (g⁻¹ * s * g) * (g⁻¹ * y * g)⁻¹ := by
        group
      constructor
      · intro hs
        have hs' : g⁻¹ * s * g ∈ oddCoreIn X := mem_conjSub_iff.mp hs
        rw [mem_conjSub_iff, e]
        exact conj_mem_oddCoreIn hy' hs'
      · intro hs
        have hs' : g⁻¹ * (y * s * y⁻¹) * g ∈ oddCoreIn X := mem_conjSub_iff.mp hs
        rw [e] at hs'
        rw [mem_conjSub_iff]
        have e2 : g⁻¹ * s * g = (g⁻¹ * y * g)⁻¹ *
            ((g⁻¹ * y * g) * (g⁻¹ * s * g) * (g⁻¹ * y * g)⁻¹) * ((g⁻¹ * y * g)⁻¹)⁻¹ := by group
        rw [e2]
        exact conj_mem_oddCoreIn (X.inv_mem hy') hs'
    · rw [conjSub, Subgroup.card_map_of_injective (MulAut.conj g).injective]
      exact odd_card_oddCoreIn X
  refine le_antisymm ?_ (key g X)
  have h2 := conjSub_mono (n := g) (key g⁻¹ (conjSub g X))
  rw [conjSub_conjSub_inv, conjSub_inv_conjSub] at h2
  exact h2

omit [Finite G] in
theorem centralizer_singleton_conj_eq (g d : G) :
    Subgroup.centralizer ({g * d * g⁻¹} : Set G) =
      conjSub g (Subgroup.centralizer ({d} : Set G)) := by
  ext x
  rw [Subgroup.mem_centralizer_singleton_iff, mem_conjSub_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have : x * (g * d * g⁻¹) * g = g * d * g⁻¹ * x * g := by rw [h]
    calc g⁻¹ * x * g * d = g⁻¹ * (x * (g * d * g⁻¹) * g) := by group
      _ = g⁻¹ * (g * d * g⁻¹ * x * g) := by rw [this]
      _ = d * (g⁻¹ * x * g) := by group
  · intro h
    have : g * (g⁻¹ * x * g * d) * g⁻¹ = g * (d * (g⁻¹ * x * g)) * g⁻¹ := by rw [h]
    calc x * (g * d * g⁻¹) = g * (g⁻¹ * x * g * d) * g⁻¹ := by group
      _ = g * (d * (g⁻¹ * x * g)) * g⁻¹ := this
      _ = g * d * g⁻¹ * x := by group

theorem involutionOddCore_conj (g d : G) :
    CFSG.Assembly.Dichotomy.involutionOddCore (g * d * g⁻¹) =
      conjSub g (CFSG.Assembly.Dichotomy.involutionOddCore d) := by
  rw [involutionOddCore_eq_oddCoreIn, involutionOddCore_eq_oddCoreIn, centralizer_singleton_conj_eq,
    oddCoreIn_conjSub_eq]

theorem deltaCore_conjSub (g : G) (D : Subgroup G) :
    deltaCore (conjSub g D) = conjSub g (deltaCore D) := by
  ext x
  rw [mem_deltaCore_iff, mem_conjSub_iff, mem_deltaCore_iff]
  constructor
  · intro h d hd hd1
    have := h (g * d * g⁻¹) (mem_conjSub_iff.mpr (by simpa [mul_assoc] using hd)) (by
      intro h1
      apply hd1
      have : g * d * g⁻¹ = 1 := h1
      calc d = g⁻¹ * (g * d * g⁻¹) * g := by group
        _ = 1 := by rw [this]; group)
    rw [involutionOddCore_conj, mem_conjSub_iff] at this
    exact this
  · intro h d hd hd1
    have hd' : g⁻¹ * d * g ∈ D := mem_conjSub_iff.mp hd
    have := h (g⁻¹ * d * g) hd' (by
      intro h1
      apply hd1
      calc d = g * (g⁻¹ * d * g) * g⁻¹ := by group
        _ = 1 := by rw [h1]; group)
    have e : d = g * (g⁻¹ * d * g) * g⁻¹ := by group
    rw [e, involutionOddCore_conj, mem_conjSub_iff]
    simpa [mul_assoc] using this

theorem uCore_conjSub (g : G) (F : Subgroup G) : uCore (conjSub g F) = conjSub g (uCore F) := by
  apply le_antisymm
  · refine iSup₂_le fun f hf => iSup_le fun hf1 => ?_
    have hf' : g⁻¹ * f * g ∈ F := mem_conjSub_iff.mp hf
    have e : f = g * (g⁻¹ * f * g) * g⁻¹ := by group
    rw [e, involutionOddCore_conj]
    refine conjSub_mono (involutionOddCore_le_uCore hf' ?_)
    intro h1
    apply hf1
    calc f = g * (g⁻¹ * f * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  · show (uCore F).map (MulAut.conj g).toMonoidHom ≤ _
    rw [uCore, Subgroup.map_iSup]
    refine iSup_le fun f => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hf => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hf1 => ?_
    have hmem : g * f * g⁻¹ ∈ conjSub g F := mem_conjSub_iff.mpr (by simpa [mul_assoc] using hf)
    have hne : g * f * g⁻¹ ≠ 1 := by
      intro h1
      apply hf1
      calc f = g⁻¹ * (g * f * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group
    have := involutionOddCore_le_uCore hmem hne
    rwa [involutionOddCore_conj] at this

omit [Finite G] in
theorem normalClosureIn_conjSub (g : G) (H L : Subgroup G) :
    normalClosureIn (conjSub g H) (conjSub g L) = conjSub g (normalClosureIn H L) := by
  apply le_antisymm
  · refine normalClosureIn_le fun h' hh' => ?_
    have hh : g⁻¹ * h' * g ∈ H := mem_conjSub_iff.mp hh'
    have e : h' = g * (g⁻¹ * h' * g) * g⁻¹ := by group
    show (L.map (MulAut.conj g).toMonoidHom).map (MulAut.conj h').toMonoidHom ≤
      (normalClosureIn H L).map (MulAut.conj g).toMonoidHom
    rw [map_map_conj]
    have : h' * g = g * (g⁻¹ * h' * g) := by group
    rw [this, ← map_map_conj]
    exact Subgroup.map_mono (le_iSup₂_of_le (g⁻¹ * h' * g) hh le_rfl)
  · show (normalClosureIn H L).map (MulAut.conj g).toMonoidHom ≤ _
    unfold normalClosureIn
    rw [Subgroup.map_iSup]
    refine iSup_le fun h => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hh => ?_
    have hmem : g * h * g⁻¹ ∈ conjSub g H := mem_conjSub_iff.mpr (by simpa [mul_assoc] using hh)
    refine le_iSup₂_of_le (g * h * g⁻¹) hmem ?_
    show (L.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom ≤
      (L.map (MulAut.conj g).toMonoidHom).map (MulAut.conj (g * h * g⁻¹)).toMonoidHom
    rw [map_map_conj, map_map_conj]
    have : g * h * g⁻¹ * g = g * h := by group
    rw [this]

theorem alphaCore_conjSub (g : G) (F : Subgroup G) :
    alphaCore (conjSub g F) = conjSub g (alphaCore F) := by
  unfold alphaCore
  rw [uCore_conjSub, deltaCore_conjSub]
  have hcomm : ⁅conjSub g (uCore F), conjSub g F⁆ = conjSub g ⁅uCore F, F⁆ := by
    show ⁅(uCore F).map (MulAut.conj g).toMonoidHom, F.map (MulAut.conj g).toMonoidHom⁆ =
      ⁅uCore F, F⁆.map (MulAut.conj g).toMonoidHom
    rw [Subgroup.map_commutator]
  rw [hcomm, ← normalClosureIn_conjSub]
  congr 1
  show _ = ((⁅uCore F, F⁆ ⊔ deltaCore F).map (MulAut.conj g).toMonoidHom)
  rw [Subgroup.map_sup]
  rfl

end Equivariance

section AlphaStep

variable {G : Type} [Group G] [Finite G] {A B : Subgroup G}

omit [Finite G] in
theorem closure_pair_conj (g u v : G) :
    Subgroup.closure ({g * u * g⁻¹, g * v * g⁻¹} : Set G) =
      conjSub g (Subgroup.closure ({u, v} : Set G)) := by
  show _ = (Subgroup.closure ({u, v} : Set G)).map (MulAut.conj g).toMonoidHom
  rw [MonoidHom.map_closure, Set.image_pair]
  rfl


omit [Finite G] in
theorem mem_closure_pair_cases {x y g : G} (hx : x * x = 1) (hy : y * y = 1) (hxy : x * y = y * x)
    (hg : g ∈ Subgroup.closure ({x, y} : Set G)) : g = 1 ∨ g = x ∨ g = y ∨ g = x * y := by
  have c : y * x = x * y := hxy.symm
  have s1' : ∀ b, x * (x * b) = b := fun b => by rw [← mul_assoc, hx, one_mul]
  have c' : ∀ b, y * (x * b) = x * (y * b) := fun b => by rw [← mul_assoc, c, mul_assoc]
  have i1 : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have i2 : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  refine Subgroup.closure_induction
    (p := fun g _ => g = 1 ∨ g = x ∨ g = y ∨ g = x * y) ?_ ?_ ?_ ?_ hg
  · intro u hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with hu | hu <;> subst hu <;> simp
  · simp
  · rintro a b - - (ha | ha | ha | ha) (hb | hb | hb | hb) <;> subst ha <;> subst hb <;>
      simp [mul_assoc, hx, hy, s1', c, c']
  · rintro a - (ha | ha | ha | ha) <;> subst ha <;> simp [i1, i2, c]


end AlphaStep

section Propagation

variable {G : Type} [Group G] [Finite G]


omit [Finite G] in
theorem OmegaConnected.mono {Ω : Set (Subgroup G)} (h : OmegaConnected Ω)
    {E : Subgroup G → Subgroup G → Prop} (hE : ∀ M N, Commutes M N → E M N) :
    ∀ L ∈ Ω, ∀ L' ∈ Ω, Relation.ReflTransGen (fun M N : Subgroup G => N ∈ Ω ∧ E M N) L L' :=
  fun L hL L' hL' => Relation.ReflTransGen.mono
    (fun (_ N : Subgroup G) (hMN : N ∈ Ω ∧ Commutes _ N) => ⟨hMN.1, hE _ _ hMN.2⟩) L L'
    (h L hL L' hL')

end Propagation

end CFSG.ClassicalInvolution.Balance.Bootstrap
