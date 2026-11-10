module

public import Certificates.Data.G2ThreeMaxCheck

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87.G2ThreeCert

open CFSG.Monster.B.TwoA.Census Certificates.G2ThreeMax


@[expose] def wordElem {G : Type*} [Group G] (gens : ℕ → G) (w : List ℕ) : G := (w.map gens).prod

section Stage

variable {G X : Type*} [Group G] [MulAction G X]

theorem tab_spec {act : ℕ → ℕ → ℕ} {ngen : ℕ} {valid : ℕ → Bool} {root : ℕ} {c : NatCert}
    (h : natCertOK act ngen valid root c = true) {dec : ℕ → X} {gens : ℕ → G}
    (hact : ∀ k < ngen, ∀ a, valid a = true → dec (act k a) = gens k • dec a)
    {k : ℕ} (hk : k < ngen) {i : ℕ} (hi : i < c.pts.size) :
    tabOf c k i < c.pts.size ∧ dec c.pts[tabOf c k i]! = gens k • dec c.pts[i]! := by
  obtain ⟨hj, e⟩ := natCertOK_edge h hi hk
  refine ⟨hj, ?_⟩
  unfold tabOf
  rw [e, hact k hk _ (natCertOK_valid h hi)]

theorem word_spec {act : ℕ → ℕ → ℕ} {ngen : ℕ} {valid : ℕ → Bool} {root : ℕ} {c : NatCert}
    (h : natCertOK act ngen valid root c = true) {dec : ℕ → X} {gens : ℕ → G}
    (hact : ∀ k < ngen, ∀ a, valid a = true → dec (act k a) = gens k • dec a) (w : List ℕ)
    (hw : ∀ k ∈ w, k < ngen) :
    ∀ i < c.pts.size, applyW c w i < c.pts.size ∧
      dec c.pts[applyW c w i]! = wordElem gens w • dec c.pts[i]! := by
  induction w with
  | nil => intro i hi; simpa [applyW, wordElem] using hi
  | cons k w ih =>
    intro i hi
    have hk : k < ngen := hw k (by simp)
    obtain ⟨h1, h2⟩ := ih (fun x hx => hw x (by simp [hx])) i hi
    obtain ⟨h3, h4⟩ := tab_spec h hact hk h1
    refine ⟨?_, ?_⟩
    · simpa [applyW] using h3
    · have e : applyW c (k :: w) i = tabOf c k (applyW c w i) := rfl
      have hwe : wordElem gens (k :: w) = gens k * wordElem gens w := by simp [wordElem]
      rw [e, h4, h2, hwe, mul_smul]

theorem orbit_mem_of_natCertOK {act : ℕ → ℕ → ℕ} {ngen N root : ℕ} {c : NatCert} {d : ℕ → X}
    {gs : ℕ → G} (h : natCertOK act ngen (fun u => decide (u < N)) root c = true)
    (hact : ∀ k < ngen, ∀ a < N, d (act k a) = gs k • d a) {i : ℕ} (hi : i ∈ c.pts.toList) :
    ∃ m ∈ Subgroup.closure (gs '' {k | k < ngen}), d i = m • d root := by
  have h' := orbit_of_natCertOK h (dec := d) (gens := gs)
    (fun k hk a ha => hact k hk a (by simpa using ha))
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hi
  have hj' : j < c.pts.size := by simpa using hj
  have hmem : d c.pts[j]! ∈ MulAction.orbit (Subgroup.closure (gs '' {k | k < ngen})) (d root) := by
    rw [h']
    exact ⟨j, hj', rfl⟩
  obtain ⟨⟨m, hm⟩, hmx⟩ := hmem
  refine ⟨m, hm, ?_⟩
  have hmx' : m • d root = d c.pts[j]! := hmx
  have hi' : c.pts.toList[j] = c.pts[j]! := by simp [getElem!_pos c.pts j hj']
  rw [hi']
  exact hmx'.symm

theorem isCoatom_stabilizer_of_cover {G X : Type*} [Group G] [MulAction G X] (x₀ : X)
    (hnt : ∃ g : G, g • x₀ ≠ x₀) (Hs : Subgroup G) (hHs : Hs ≤ MulAction.stabilizer G x₀)
    (reps : Set G)
    (hcov : ∀ g : G, g • x₀ ≠ x₀ → ∃ r ∈ reps, ∃ h ∈ Hs, g • x₀ = (h * r) • x₀)
    (htrans : ∀ r ∈ reps, ∀ g : G, ∃ m ∈ Subgroup.closure ((Hs : Set G) ∪ {r}), g • x₀ = m • x₀) :
    IsCoatom (MulAction.stabilizer G x₀) := by
  refine ⟨?_, fun M hM => ?_⟩
  · intro h
    obtain ⟨g, hg⟩ := hnt
    apply hg
    have : g ∈ MulAction.stabilizer G x₀ := by rw [h]; exact Subgroup.mem_top g
    exact this
  · obtain ⟨m, hmM, hmS⟩ := IsConcreteLE.exists_of_lt hM
    have hm : m • x₀ ≠ x₀ := fun h => hmS h
    obtain ⟨r, hr, h, hh, hmr⟩ := hcov m hm
    have hs : (h * r)⁻¹ * m ∈ MulAction.stabilizer G x₀ := by
      rw [MulAction.mem_stabilizer_iff, mul_smul, hmr, inv_smul_smul]
    have hsM : (h * r)⁻¹ * m ∈ M := hM.le hs
    have h1 : h * r ∈ M := by
      have : h * r = m * ((h * r)⁻¹ * m)⁻¹ := by group
      rw [this]
      exact M.mul_mem hmM (M.inv_mem hsM)
    have hhM : h ∈ M := hM.le (hHs hh)
    have hrM : r ∈ M := by
      have : r = h⁻¹ * (h * r) := by group
      rw [this]
      exact M.mul_mem (M.inv_mem hhM) h1
    have hcl : Subgroup.closure ((Hs : Set G) ∪ {r}) ≤ M := by
      rw [Subgroup.closure_le]
      intro x hx
      rcases hx with hx | hx
      · exact hM.le (hHs hx)
      · rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact hrM
    rw [Subgroup.eq_top_iff']
    intro g
    obtain ⟨m', hm', hgm'⟩ := htrans r hr g
    have hs' : m'⁻¹ * g ∈ MulAction.stabilizer G x₀ := by
      rw [MulAction.mem_stabilizer_iff, mul_smul, hgm', inv_smul_smul]
    have h2 : m'⁻¹ * g ∈ M := hM.le hs'
    have : g = m' * (m'⁻¹ * g) := by group
    rw [this]
    exact M.mul_mem (hcl hm') h2


theorem permArr_get (c : NatCert) (w : List ℕ) {a : ℕ} (ha : a < c.pts.size) :
    (permArr c w)[a]! = applyW c w a := by
  unfold permArr
  rw [getElem!_pos _ a (by simpa using ha)]
  simp


end Stage


end CFSG.GH74.GLS.Stage2.Signalizer.Odd87.G2ThreeCert
