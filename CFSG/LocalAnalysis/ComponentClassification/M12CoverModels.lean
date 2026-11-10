module

public import CFSG.LocalAnalysis.ComponentClassification.M12CoverModelsBeta
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverModelsGroups
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverSylowSplit

public section

namespace CFSG.ComponentClassification.M12Cover.InternalSylow

open CFSG.Blueprint CFSG.ComponentClassification.CentralCover

@[expose] noncomputable def equivNative : S ≃* M12Cover.S :=
  (MulEquiv.subgroupCongr S_eq_map).trans
    (((M12Cover.S.subgroupOf NativeSporadic.M12).equivMapOfInjective
      (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).symm.trans
      (Subgroup.subgroupOfEquivOfLe S_le_M12))

theorem involutionCocyclesSplit : InvolutionCocyclesSplit S :=
  involutionCocyclesSplit_S.of_mulEquiv equivNative

theorem f_class_unique (f' : NormCocycle S) (hd : ∀ q : S, orderOf q = 2 → f' q q = f q q) :
    ∃ ν : S → ZMod 2, ∀ s t, f' s t = f s t + ν s + ν t + ν (s * t) := by
  obtain ⟨ν, hν⟩ := involutionCocyclesSplit (fun s t => f' s t + f s t)
    (fun t => by simp [f'.map_one_left, f_one_left]) (fun s => by
      simp [f'.map_one_right, f_one_right])
    (fun s t u => by
      have h1 := f'.cocycle s t u
      have h2 := f_cocycle s t u
      grind)
    (fun q hq => by rw [hd q hq]; exact zmod2_add_self _)
  refine ⟨ν, fun s t => ?_⟩
  have := hν s t
  have h := zmod2_add_self (f s t)
  grind

theorem transport_beta {E : Type*} [Group E] [Group.IsPerfect E]
    {π : E →* NativeSporadic.M12} {z : E} (hπ : IsCentralDoubleExt π z) (ι : S.comap π ≃* R)
    (hι : ∀ x, ((ι x).snd : NativeSporadic.M12) = π x) :
    ∃ ι' : S.comap π ≃* R, (∀ x : S.comap π, ((ι' x).snd : NativeSporadic.M12) = π x) ∧
      ((ι'.symm ⟨1, 1⟩ : S.comap π) : E) = z ∧
      ∀ φ : E ≃* E, (∀ x, π (φ x) = beta (π x)) →
        ∀ (x : E) (hx : π x ∈ S) (hφx : π (φ x) ∈ S), ι' ⟨φ x, hφx⟩ = tau (ι' ⟨x, hx⟩) := by
  have hodd : Odd (Fintype.card (Fin 1485)) := by
    rw [Fintype.card_fin]
    decide
  obtain ⟨-, -, -, -, -, -, Ψ, -, -, -, ι', hι', hz, -, hact⟩ :=
    isRightTransversal.odd_index_central_double_cover_transfer_and_automorphism_transport hodd
      tau0_snd mu transfer₂_add_coboundary_mu hπ ι hι
  refine ⟨ι', fun x => by rw [hι'], hz, fun φ hφ x hx hφx => ?_⟩
  rw [hact φ hφ x hx hφx, restrictAut_eq_tau]


end CFSG.ComponentClassification.M12Cover.InternalSylow
