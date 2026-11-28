import Green51GoldIsotropy
import Green51BCHSmallFields
import Green51BCHPlateau

/-! # Exact scalar profiles for the projected BCH double -/

open Green51BCH Green51BCHCompression Green51BCHOptimality Finset
open scoped Pointwise
namespace Green51GoldForms
local notation "F" => ZMod 2
variable {K : Type*} [Field K] [CharP K 2] [Algebra F K] [Fintype K]

/-- The largest flat has dimension exactly floor(m/2)+1. -/
theorem scalar_profile (l : K →ₗ[F] F) (nl : l≠0) (room : 4≤Module.finrank F K)
    (six : Module.finrank F K≠6) :
    (∃ (p : Space K × F) (W : Submodule F (Space K × F)),
      Module.finrank F W=Module.finrank F K/2+1 ∧
      p+ᵥ (W:Set _) ⊆ Set.range (lifted l)+Set.range (lifted l)) ∧
    ∀ (p : Space K × F) (W : Submodule F (Space K × F)),
      p+ᵥ (W:Set _) ⊆ Set.range (lifted l)+Set.range (lifted l) →
      Module.finrank F W≤Module.finrank F K/2+1 := by
  have bound (p : Space K × F) (W : Submodule F (Space K × F))
      (h : p+ᵥ (W:Set _) ⊆ Set.range (lifted l)+Set.range (lifted l)) :
      Module.finrank F W≤Module.finrank F K/2+1 := by
    by_contra! high
    have b := half_bound l nl p W h (by omega)
    omega
  obtain ⟨p,W,lo,inside⟩ := maximal_of_meeting l nl (Green51BCHCompression.meets_except_six room six)
  exact ⟨⟨p,W,le_antisymm (bound p W inside) lo,inside⟩,bound⟩

open Green50Downsets Finset Green51SparseBounds Green51LocalFlats in
/-- One additional binary coordinate above the first three BCH coordinates
bounds the original Green 51 guarantee. -/
theorem scalar_guarantee {m : ℕ} (room : 2 ≤ m) {α : ℝ}
    (density : α≤(2:ℝ)^m/2^(3*m+1)) :
    Green51.guaranteedMaxCosetDim (3*m+1) α ≤ m/2+1 := by
  classical
  let E := GaloisField 2 m
  let _ : Fintype E := Fintype.ofFinite E
  have dim : Module.finrank F E=m := GaloisField.finrank 2 (by omega)
  obtain ⟨l,nl,_⟩ := trace_functional (K:=E)
  let j : (Space E × F) ≃ₗ[F] Cube (3*m+1) := LinearEquiv.ofFinrankEq _ _ (by
    simp [Space,Cube,dim];omega)
  obtain ⟨A,card,free⟩ := transport_dimension (d:=m/2+1) l j (fun p W inside => by
    by_contra! high
    have h := half_bound l nl p W inside (by omega)
    omega)
  have cardE : Fintype.card E=2^m := by rw [←Nat.card_eq_fintype_card];exact GaloisField.card _ _ (by omega)
  have adm : α≤(A.dens:ℝ) := by rw [Finset.nnratCast_dens,card,cardE];simpa [Cube] using density
  have upper : Green51.guaranteedMaxCosetDim (3*m+1) α ≤ maxCosetDim F (𝔽₂ (3*m+1)) ↑(A+A) :=
    csInf_le (OrderBot.bddBelow _) ⟨A,adm,rfl⟩
  apply upper.trans
  by_contra! hi
  obtain ⟨W,p,rank,flat⟩ := (le_iff_coset (by omega : 0 < m/2+1+1) _).mp hi
  exact (Nat.not_succ_le_self (m/2+1)) (rank.symm.trans_le (free W p flat))

end Green51GoldForms
#print axioms Green51GoldForms.scalar_profile
#print axioms Green51GoldForms.scalar_guarantee
