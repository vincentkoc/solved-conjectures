import Green51BCHFlatDimensions
import Green51BCHSubfieldFlats
import Green51BCHPlateau

/-! # Exact projection ranks for subfield dimensions and an upper bound for Green 51 -/

open Green50Downsets Green51BCH Green51BCHCompression
open scoped Pointwise
namespace Green51BracketRank
local notation "F" => ZMod 2
variable {K : Type*} [Field K] [Algebra F K] [CharP K 2] [Fintype K]

/-- Among seventh-coordinate projections with prescribed kernel rank, a
flat of proper subfield dimension at least three occurs exactly at ranks
at least that dimension. -/
theorem attainable_iff {d r : ℕ} (three : 3≤d) (dvd : d∣Module.finrank F K)
    (proper : d<Module.finrank F K) (room : r≤Module.finrank F K) :
    (∃ S : Submodule F K, Module.finrank F S=r ∧
      ∃ (p : Space K × (K ⧸ S)) (W : Submodule F (Space K × (K ⧸ S))),
        Module.finrank F W=d ∧ p+ᵥ (W:Set _) ⊆ Set.range (lifted S.mkQ)+Set.range (lifted S.mkQ)) ↔ d≤r := by
  constructor
  · rintro ⟨S,sr,p,W,wr,inside⟩
    have bound := dim_le_kernel S.mkQ p W inside (by omega)
    rwa [wr,Submodule.ker_mkQ,sr] at bound
  · intro dr
    obtain ⟨S,sz,p,W,wr,flat⟩ := flat_of_divisor (K:=K) d (by omega) dvd proper
    obtain ⟨t,U,nt,ht,du,kill⟩ := input_of_flat S.mkQ p W flat (by omega)
    have rq := S.finrank_quotient_add_finrank
    obtain ⟨e,inj⟩ := finrank_le_iff_exists_linearMap.mp
      (show Module.finrank F (Cube (r-d))≤Module.finrank F (K ⧸ S) by simp only [Cube,Module.finrank_fin_fun];omega)
    let T := e.range.comap S.mkQ
    have ker : S.mkQ.ker≤T := by
      intro x hx
      change S.mkQ x∈e.range
      rw [show S.mkQ x=0 from hx]
      exact e.range.zero_mem
    have sub : S≤T := by simpa only [Submodule.ker_mkQ] using ker
    have eq : T.map S.mkQ=e.range := Submodule.map_comap_eq_self (by rw [Submodule.range_mkQ];exact le_top)
    have rt := Green51QuadraticFlats.map_rank S.mkQ T ker
    rw [eq,e.finrank_range_of_inj inj,Submodule.ker_mkQ,sz] at rt
    simp only [Cube,Module.finrank_fin_fun] at rt
    have zero (b) (hb : b∈U) (c) (hc : c∈U) : T.mkQ (moore t b c)=0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr (sub ((Submodule.Quotient.mk_eq_zero _).mp (kill b hb c hc)))
    obtain ⟨z,Z,dz,inside⟩ := produces_flat T.mkQ U t ht nt zero
    exact ⟨T,by omega,z,Z,by omega,inside⟩

open Finset in
/-- Keeping 4m-r binary coordinates preserves all 2^m input labels and
bounds the affine dimensions in their double by max(2,r). -/
theorem compressed_example (m r : ℕ) (pos : 0 < m) (room : r ≤ m) :
    ∃ A : Finset (Cube (4*m-r)), A.card=2^m ∧
      ∀ (W : Submodule F (Cube (4*m-r))) (p : Cube (4*m-r)),
        p+ᵥ (W:Set (Cube (4*m-r))) ⊆ ↑(A+A) → Module.finrank F W ≤ max 2 r := by
  classical
  let E := GaloisField 2 m
  let _ : Fintype E := Fintype.ofFinite E
  have dim : Module.finrank F E=m := GaloisField.finrank 2 (by omega)
  obtain ⟨e,inj⟩ := finrank_le_iff_exists_linearMap.mp
    (show Module.finrank F (Cube r)≤Module.finrank F E by simpa only [Cube,Module.finrank_fin_fun,dim] using room)
  let S := e.range
  have sr : Module.finrank F S=r := by simpa only [Cube,Module.finrank_fin_fun] using e.finrank_range_of_inj inj
  let G := Space E × (E ⧸ S)
  have dq := S.finrank_quotient_add_finrank
  let j : G ≃ₗ[F] Cube (4*m-r) := LinearEquiv.ofFinrankEq _ _ (by
    simp only [G,Space,Cube,Module.finrank_prod,Module.finrank_fin_fun,dim];omega)
  obtain ⟨A,card,free⟩ := transport_dimension (d:=max 2 r) S.mkQ j (fun p W inside => by
    by_cases h : Module.finrank F W≤2
    · exact h.trans (le_max_left ..)
    · have b := dim_le_kernel S.mkQ p W inside (by omega)
      rw [Submodule.ker_mkQ,sr] at b
      exact b.trans (le_max_right ..))
  refine ⟨A,card.trans ?_,free⟩
  rw [←Nat.card_eq_fintype_card]
  exact GaloisField.card 2 m (by omega)

open Finset Green51SparseBounds Green51LocalFlats in
/-- The compressed examples bound the original affine guarantee at every
density at most their own. -/
theorem guaranteed_dimension {m r : ℕ} (pos : 0 < m) (room : r ≤ m) {α : ℝ}
    (density : α≤(2:ℝ)^m/2^(4*m-r)) :
    Green51.guaranteedMaxCosetDim (4*m-r) α ≤ max 2 r := by
  classical
  obtain ⟨A,card,free⟩ := compressed_example m r pos room
  have adm : α≤(A.dens:ℝ) := by rw [Finset.nnratCast_dens,card];simpa [Cube] using density
  have upper : Green51.guaranteedMaxCosetDim (4*m-r) α ≤ maxCosetDim F (𝔽₂ (4*m-r)) ↑(A+A) :=
    csInf_le (OrderBot.bddBelow _) ⟨A,adm,rfl⟩
  apply upper.trans
  by_contra! hi
  obtain ⟨W,p,rank,flat⟩ := (le_iff_coset (by omega : 0 < max 2 r+1) _).mp hi
  exact (Nat.not_succ_le_self (max 2 r)) (rank.symm.trans_le (free W p flat))

end Green51BracketRank
#print axioms Green51BracketRank.attainable_iff
#print axioms Green51BracketRank.compressed_example
#print axioms Green51BracketRank.guaranteed_dimension
