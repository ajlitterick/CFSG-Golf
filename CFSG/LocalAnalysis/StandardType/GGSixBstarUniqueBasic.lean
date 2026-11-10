module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveRank
public import CFSG.LocalAnalysis.StandardType.GGTableBRank

public section

namespace CFSG.StandardType

open CFSG.Assembly

variable {G : Type} [Group G]

@[expose] def GGNoOffender (p : ℕ) (N Bs : Subgroup G) : Prop :=
  ∀ E : Subgroup G, E ≤ N → E ≤ Subgroup.normalizer (Bs : Set G) → IsElemAbelian p E →
    E ≤ Subgroup.centralizer (Bs : Set G) ∨
      Nat.card (Bs ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) * Nat.card E <
        Nat.card Bs * Nat.card (E ⊓ Subgroup.centralizer (Bs : Set G) : Subgroup G)

theorem GGNoOffender.mono {p : ℕ} {N N' Bs : Subgroup G} (h : GGNoOffender p N Bs)
    (hN : N' ≤ N) : GGNoOffender p N' Bs :=
  fun E hE => h E (hE.trans hN)

theorem le_centralizer_of_isElemAbelian {p : ℕ} {E : Subgroup G} (hE : IsElemAbelian p E) :
    E ≤ Subgroup.centralizer (E : Set G) := by
  intro e he
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact TableB.IsElemAbelian.comm hE hy he

variable [Finite G]

theorem card_le_of_noOffender {p : ℕ} {N Bs E : Subgroup G}
    (hΩ : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hNO : GGNoOffender p N Bs) (hEN : E ≤ N) (hEB : E ≤ Subgroup.normalizer (Bs : Set G))
    (hE : IsElemAbelian p E) :
    Nat.card E ≤ Nat.card Bs ∧ (Nat.card E = Nat.card Bs → E = Bs) := by
  rcases hNO E hEN hEB hE with hC | hlt
  · have hle : E ≤ Bs := fun e he => hΩ e (hC he) (hE.2 e he)
    exact ⟨Subgroup.card_le_of_le hle, fun hcard => Subgroup.eq_of_le_of_card_ge hle hcard.ge⟩
  · have hle : E ⊓ Subgroup.centralizer (Bs : Set G) ≤
        Bs ⊓ Subgroup.centralizer (E : Set G) := fun e he =>
      ⟨hΩ e he.2 (hE.2 e he.1), le_centralizer_of_isElemAbelian hE he.1⟩
    have h1 := Subgroup.card_le_of_le hle
    have hlt' : Nat.card E < Nat.card Bs := by
      by_contra hcon
      rw [not_lt] at hcon
      have h2 := Nat.mul_le_mul h1 hcon
      have h3 : Nat.card Bs * Nat.card (E ⊓ Subgroup.centralizer (Bs : Set G) : Subgroup G) ≤
          Nat.card (Bs ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) * Nat.card E := by
        rw [mul_comm]
        exact h2
      omega
    exact ⟨hlt'.le, fun h => absurd h hlt'.ne⟩

theorem le_normalizer_of_noOffender {p : ℕ} (hp : p.Prime) {N Bs S : Subgroup G}
    (hBs : IsElemAbelian p Bs)
    (hΩ : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hNO : GGNoOffender p N Bs) (hSN : S ≤ N) (hS : IsPGroup p S) (hBsS : Bs ≤ S) :
    S ≤ Subgroup.normalizer (Bs : Set G) := by
  have : Fact p.Prime := ⟨hp⟩
  by_contra hne
  have hlt : S ⊓ Subgroup.normalizer (Bs : Set G) < S :=
    lt_of_le_of_ne inf_le_left fun h => hne (h ▸ inf_le_right)
  obtain ⟨s, hsS, hsN, hsNB⟩ := exists_mem_normalizer_not_mem hS hlt
  have hsB : s ∉ Subgroup.normalizer (Bs : Set G) := fun h => hsNB ⟨hsS, h⟩
  set E := Bs.map (MulAut.conj s).toMonoidHom with hEdef
  have hBsle : Bs ≤ S ⊓ Subgroup.normalizer (Bs : Set G) := le_inf hBsS Subgroup.le_normalizer
  have hEle : E ≤ S ⊓ Subgroup.normalizer (Bs : Set G) := by
    rw [hEdef, ← map_conj_eq_of_mem_normalizer hsN]
    exact Subgroup.map_mono hBsle
  have hEcard : Nat.card E = Nat.card Bs :=
    Subgroup.card_map_of_injective (MulAut.conj s).injective
  have hEq := (card_le_of_noOffender hΩ hNO (hEle.trans (inf_le_left.trans hSN))
    (hEle.trans inf_le_right) (isElemAbelian_map_conj hBs s)).2 hEcard
  exact hsB (mem_normalizer_iff_map_conj.mpr hEq)

theorem unique_of_noOffender {p : ℕ} (hp : p.Prime) {N Bs S : Subgroup G}
    (hBs : IsElemAbelian p Bs)
    (hΩ : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hNO : GGNoOffender p N Bs) (hSN : S ≤ N) (hS : IsPGroup p S) (hBsS : Bs ≤ S)
    {E : Subgroup G} (hES : E ≤ S) (hE : IsElemAbelian p E) :
    Nat.card E ≤ Nat.card Bs ∧ (Nat.card E = Nat.card Bs → E = Bs) :=
  card_le_of_noOffender hΩ hNO (hES.trans hSN)
    (hES.trans (le_normalizer_of_noOffender hp hBs hΩ hNO hSN hS hBsS)) hE


end CFSG.StandardType
