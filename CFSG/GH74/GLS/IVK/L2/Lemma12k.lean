module

public import CFSG.GH74.GLS.IVK.L2.Hilbert90
public import CFSG.GH74.GLS.IVK.L2.Twist
public import CFSG.GH74.GLS.IVK.L2.FieldProj
public import CFSG.GH74.GLS.IVK.L2.Lemma12
public import CFSG.GH74.GLS.IVK.L2.DihedralAux
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralCore

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.GorensteinWalter

section K

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K] (e : K ≃* L2 F)

theorem card_le_four_of_le_inf (hF : L2Field F) (T : Sylow 2 (MulAut K)) (X : Subgroup (MulAut K))
    (hT : X ≤ (T : Subgroup (MulAut K))) (hG : X ≤ innDiagSub e)
    (hcomm : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) (hsq : ∀ x ∈ X, x * x = 1) : Nat.card X ≤ 4 := by
  obtain ⟨m, hm, ⟨φ⟩⟩ := dihedral_of_sylow_inf_innDiag e hF T
  set M : Subgroup (MulAut K) := (T : Subgroup (MulAut K)) ⊓ innDiagSub e with hM
  have hXM : X ≤ M := le_inf hT hG
  have hne : NeZero (2 ^ m) := ⟨by positivity⟩
  let X' : Subgroup ↥M := X.subgroupOf M
  have hcard1 : Nat.card X' = Nat.card X :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXM).toEquiv
  let X'' : Subgroup (DihedralGroup (2 ^ m)) := X'.map φ.toMonoidHom
  have hcard2 : Nat.card X'' = Nat.card X' := Subgroup.card_map_of_injective φ.injective
  have hb : Nat.card X'' ≤ 4 := by
    apply DihedralAux.card_le_four_of_elemAbelian
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hcomm a ha b hb)
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_mul]
      have : a * a = 1 := Subtype.ext (hsq a ha)
      rw [this, map_one]
  omega

include e in
theorem card_le_eight_of_elemAbelian (hF : L2Field F) (A : Subgroup (MulAut K))
    (hA : IsElementaryAbelian 2 ↥A) : Nat.card ↥A ≤ 8 := by
  have := hA
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpow : ∀ a : ↥A, a ^ 2 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 ↥A)
  have hsq : ∀ x ∈ A, x * x = 1 := by
    intro x hx
    have := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := A) x hx
    rwa [pow_two] at this
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
    intro x hx y hy
    exact congrArg Subtype.val (hA.toIsMulCommutative.is_comm.comm (⟨x, hx⟩ : A) ⟨y, hy⟩)
  have hA2 : IsPGroup 2 A := IsElementaryAbelian.isPGroup 2 A
  obtain ⟨T', hT'⟩ := hA2.exists_le_sylow
  set φ : ↥A →* (F ≃+* F) := (fieldProj e).comp A.subtype with hφ
  have hker : Nat.card φ.ker ≤ 4 := by
    set X : Subgroup (MulAut K) := φ.ker.map A.subtype with hX
    have hXA : X ≤ A := by
      rintro _ ⟨a, _, rfl⟩
      exact a.2
    have hXG : X ≤ innDiagSub e := by
      rintro _ ⟨a, ha, rfl⟩
      exact (mem_innDiagSub_iff e _).mpr (MonoidHom.mem_ker.mp ha)
    have hcard : Nat.card X = Nat.card φ.ker :=
      Subgroup.card_map_of_injective A.subtype_injective
    have := card_le_four_of_le_inf e hF T' X (hXA.trans hT') hXG
      (fun x hx y hy => hcomm x (hXA hx) y (hXA hy)) (fun x hx => hsq x (hXA hx))
    omega
  have hrange : Nat.card φ.range ≤ 2 := by
    have := ringAut_isCyclic F
    have : IsCyclic φ.range := Subgroup.isCyclic _
    have h1 : Monoid.exponent φ.range ∣ 2 := by
      rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      rintro ⟨_, a, rfl⟩
      apply Subtype.ext
      show φ a ^ 2 = 1
      rw [← map_pow, hpow a, map_one]
    rw [IsCyclic.exponent_eq_card] at h1
    exact Nat.le_of_dvd (by norm_num) h1
  have := Subgroup.card_ker_mul_card_range φ
  nlinarith


end K

end CFSG.GH74.GLS.IVK
