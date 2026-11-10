module

public import CFSG.Monster.B.Final.Simple
public import CFSG.Monster.B.TwoA.Co2Inv.KerElts
public import CFSG.Monster.B.TwoA.Co2Inv.SixAction

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B

open Matrix MulOpposite Bin CFSG.Blueprint CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin
  CFSG.Monster.SpinLattice CFSG.Monster.Visible CFSG.Monster.B.Rep4371

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)

@[expose] noncomputable def qA : Q := pauliQ (false, 1078, 64)

theorem qA_eq : qA = qElt 1 * qElt 2 * qElt 4 * qElt 5 * qElt 10 * qElt 17 := by
  simp only [qElt_eq, ← pauliQ_mul]
  rw [qA]
  congr 1

theorem qA_mul_rStar : qA * Short.rStar = Short.rStar * qA := by
  have h : Model.Pauli.mul (false, 1078, 64) (false, 0, 191) =
      Model.Pauli.mul (false, 0, 191) (false, 1078, 64) := by decide
  rw [qA, rStar_eq, ← pauliQ_mul, ← pauliQ_mul, h]

theorem qA_mem : qA ∈ Subgroup.centralizer {Short.rStar} :=
  Subgroup.mem_centralizer_singleton_iff.2 qA_mul_rStar

@[expose] noncomputable def a0 : Cbar :=
  kappa ⟨rhoEquiv qA * hElt 5, Cgen.mul_mem (rhoEquiv_mem_Cgen qA_mem) (hElt_mem_Cgen 5)⟩

@[expose] noncomputable def WB : Sbp := wordS gSeq conjWord0

@[expose] noncomputable def aB : Sbp := WB⁻¹ * op a0 * WB

@[expose] noncomputable def bB : Sbp := op taubar

@[expose] noncomputable def HB : Subgroup Sbp := Subgroup.closure {aB, bB}

theorem gSeq_six : gSeq 6 = kappa ⟨hElt 5, hElt_mem_Cgen 5⟩ := by
  rw [gSeq_of_lt (by norm_num)]
  exact selGen_succ 5

theorem gSeq_zero : gSeq 0 = kappa ⟨rhoEquiv (qElt 1), rhoEquiv_qElt_mem_Cgen 1⟩ := by
  rw [gSeq_of_lt (by norm_num)]
  exact selGen_zero


theorem packetElt_kappa_qElt (k : Fin 23) :
    packetElt ⟨k, by omega⟩ = kappa ⟨rhoEquiv (qElt k), rhoEquiv_qElt_mem_Cgen k⟩ := by
  rw [packetElt, packetGen_of_lt (k := ⟨k, by omega⟩) k.2]

theorem a0_eq : a0 = Dyadic.a0Elt := by
  have hρ : rhoEquiv qA = rhoEquiv (qElt 17) * rhoEquiv (qElt 10) * rhoEquiv (qElt 5) *
      rhoEquiv (qElt 4) * rhoEquiv (qElt 2) * rhoEquiv (qElt 1) := by
    rw [qA_eq]
    simp only [rhoEquiv_mul, mul_assoc]
  have e : (⟨rhoEquiv qA * hElt 5, Cgen.mul_mem (rhoEquiv_mem_Cgen qA_mem) (hElt_mem_Cgen 5)⟩ :
      Cgen) = ⟨rhoEquiv (qElt 17), rhoEquiv_qElt_mem_Cgen 17⟩ *
        ⟨rhoEquiv (qElt 10), rhoEquiv_qElt_mem_Cgen 10⟩ *
        ⟨rhoEquiv (qElt 5), rhoEquiv_qElt_mem_Cgen 5⟩ *
        ⟨rhoEquiv (qElt 4), rhoEquiv_qElt_mem_Cgen 4⟩ *
        ⟨rhoEquiv (qElt 2), rhoEquiv_qElt_mem_Cgen 2⟩ *
        ⟨rhoEquiv (qElt 1), rhoEquiv_qElt_mem_Cgen 1⟩ * ⟨hElt 5, hElt_mem_Cgen 5⟩ := by
    apply Subtype.ext
    show rhoEquiv qA * hElt 5 = rhoEquiv (qElt 17) * rhoEquiv (qElt 10) * rhoEquiv (qElt 5) *
      rhoEquiv (qElt 4) * rhoEquiv (qElt 2) * rhoEquiv (qElt 1) * hElt 5
    rw [hρ]
  have h1 : packetElt ⟨1, by norm_num⟩ = kappa ⟨rhoEquiv (qElt 1), rhoEquiv_qElt_mem_Cgen 1⟩ :=
    packetElt_kappa_qElt 1
  have h2 : packetElt ⟨2, by norm_num⟩ = kappa ⟨rhoEquiv (qElt 2), rhoEquiv_qElt_mem_Cgen 2⟩ :=
    packetElt_kappa_qElt 2
  have h4 : packetElt ⟨4, by norm_num⟩ = kappa ⟨rhoEquiv (qElt 4), rhoEquiv_qElt_mem_Cgen 4⟩ :=
    packetElt_kappa_qElt 4
  have h5 : packetElt ⟨5, by norm_num⟩ = kappa ⟨rhoEquiv (qElt 5), rhoEquiv_qElt_mem_Cgen 5⟩ :=
    packetElt_kappa_qElt 5
  have h10 : packetElt ⟨10, by norm_num⟩ =
      kappa ⟨rhoEquiv (qElt 10), rhoEquiv_qElt_mem_Cgen 10⟩ := packetElt_kappa_qElt 10
  have h17 : packetElt ⟨17, by norm_num⟩ =
      kappa ⟨rhoEquiv (qElt 17), rhoEquiv_qElt_mem_Cgen 17⟩ := packetElt_kappa_qElt 17
  have h28 : packetElt ⟨28, by norm_num⟩ = kappa ⟨hElt 5, hElt_mem_Cgen 5⟩ := by
    have h := gSeq_six
    rw [gSeq_of_lt (by norm_num)] at h
    exact h
  rw [a0, e, Dyadic.a0Elt, h1, h2, h4, h5, h10, h17, h28]
  simp only [map_mul]

theorem aB_eq : aB = aS gSeq := by
  rw [aB, aS, WB, a0_eq]


theorem orderOf_betaRow {β : Cbar →* GL (Fin 4370) (ZMod 2)} (hinj : Function.Injective β)
    (s : Sbp) : orderOf s = orderOf ((betaRow β s : MatBˣ) : MatB) := by
  rw [orderOf_units, orderOf_injective (betaRow β) (betaRow_injective hinj) s]


section Explicit

variable {β : Cbar →* GL (Fin 4370) (ZMod 2)} (hβ : IsExplicitBinary β)


include hβ in
theorem betaRow_aB : ((betaRow β aB : MatBˣ) : MatB) = Fmat := by
  rw [aB_eq]
  exact betaRow_aS β gSeq hβ.gen hβ.a0

include hβ in
theorem betaRow_bB : ((betaRow β bB : MatBˣ) : MatB) = Dyadic.Qmat 25 := by
  rw [bB, ← gSeq_last, hβ.gen 25 (by norm_num), Qn_25]


end Explicit

theorem closure_bA_eq_top :
    Subgroup.closure ({bA₁, bA₂} : Set NativeSporadic.B) = ⊤ := by
  set H := Subgroup.closure ({bA₁, bA₂} : Set NativeSporadic.B)
  have key : ∀ p ∈ NativeSporadic.seedMonoid 2 4370 1 NativeSporadic.BSeed1 NativeSporadic.BSeed2,
      ∃ u ∈ H, bMat u = p := by
    intro p hp
    induction hp using Submonoid.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact ⟨bA₁, Subgroup.subset_closure (Set.mem_insert _ _), rfl⟩
      · exact ⟨bA₂, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl), rfl⟩
    | one => exact ⟨1, H.one_mem, map_one bMat⟩
    | mul x y _ _ hx hy =>
      obtain ⟨u, hu, rfl⟩ := hx
      obtain ⟨v, hv, rfl⟩ := hy
      exact ⟨u * v, H.mul_mem hu hv, map_mul bMat u v⟩
  rw [eq_top_iff]
  intro u _
  obtain ⟨v, hv, hvu⟩ := key _ (u : NativeSporadic.seedMonoid 2 4370 1 NativeSporadic.BSeed1
    NativeSporadic.BSeed2).2
  have : v = u := bMat_injective hvu
  rw [← this]
  exact hv

section Explicit

variable {β : Cbar →* GL (Fin 4370) (ZMod 2)} (hβ : IsExplicitBinary β)

include hβ in
theorem iota_facts :
    ∃ ι : NativeSporadic.B →* Sbp, Function.Injective ι ∧
    (∀ X, ((betaRow β (ι X) : MatBˣ) : MatB) = Tmat * bMat X * Tmat⁻¹) ∧
    ι bA₁ = aB ∧ ι bA₂ = bB ∧ ι.range = HB := by
  obtain ⟨ι, hι, hιβ⟩ := exists_iota β gSeq hβ.gen hβ.injective gSeq_last aB (betaRow_aB hβ)
  obtain ⟨-, -, -, -, hFT, hQT, -⟩ := pair_matrix_facts
  have h1 : ι bA₁ = aB := by
    apply betaRow_inj hβ.injective
    rw [hιβ, bMat_bA₁, betaRow_aB hβ, ← hFT, Matrix.mul_assoc, Tmat_mul_inv, Matrix.mul_one]
  have h2 : ι bA₂ = bB := by
    apply betaRow_inj hβ.injective
    rw [hιβ, bMat_bA₂, betaRow_bB hβ, ← hQT, Matrix.mul_assoc, Tmat_mul_inv, Matrix.mul_one]
  refine ⟨ι, hι, hιβ, h1, h2, ?_⟩
  rw [MonoidHom.range_eq_map, ← closure_bA_eq_top, MonoidHom.map_closure, Set.image_pair, h1, h2,
    HB]


include hβ in
theorem pinned_B_explicit_native_isomorphism :
    HB = ⊤ ∧ ∃ e : NativeSporadic.B ≃* Sbp,
      (∀ X, ((betaRow β (e X) : MatBˣ) : MatB) = Tmat * bMat X * Tmat⁻¹) ∧
      e bA₁ = aB ∧ e bA₂ = bB ∧ IsSimpleGroup NativeSporadic.B := by
  obtain ⟨ι, hι, hιβ, h1, h2, hrange⟩ := iota_facts hβ
  have hsurj :=
    iota_surjective β hβ.injective gSeq hβ.gen gSeq_last gSeq_zero_mem gSeq_mem_Jbar ι hιβ
  refine ⟨?_, MulEquiv.ofBijective ι ⟨hι, hsurj⟩, hιβ, h1, h2, isSimpleGroup_B_of_explicit hβ⟩
  rw [← hrange]
  exact MonoidHom.range_eq_top.2 hsurj

end Explicit

end CFSG.Monster.B
