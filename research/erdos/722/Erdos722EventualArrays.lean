import Erdos722DiagonalArrays
import Erdos722ArrayArithmetic
import Erdos722FiveMaster

/-!
# Orthogonal arrays at every sufficiently large order

The CRT supplies the two group sizes. Composing the corresponding arrays
over the blocks of the truncated transversal gives the desired array.
-/

namespace Erdos722.PairDesign
open Erdos722.Quartet

def ArrayAt (k n : ℕ) := Nonempty (DiagonalArray (Fin k) (Fin n))

theorem array_of_directions {k n : ℕ} (D : Directions k n) : ArrayAt k n :=
  ⟨(DiagonalArray.ofDirections D).relabel (Fintype.equivFinOfCardEq D.card)⟩

theorem array_of_cover {k n : ℕ} (H : Has (ArrayAt k) n) : ArrayAt k n := by
  classical
  let C := H.some
  refine ⟨DiagonalArray.glue C fun B => ?_⟩
  exact ((C.size B.val B.property).some).relabel (Fintype.equivFinOfCardEq (Fintype.card_coe B.val)).symm

/-- For every fixed number of columns at least two, there is a diagonal
orthogonal array on every sufficiently large finite alphabet. -/
theorem eventual_arrays {k : ℕ} (hk : 2 ≤ k) : ∃ N, ∀ n ≥ N, ArrayAt k n := by
  let F := k.factorial
  have hF : 2 ≤ F := hk.trans (Nat.self_le_factorial k)
  let s := F^k-1
  have hbig := (Nat.lt_two_pow_self (n:=k)).trans_le (Nat.pow_le_pow_left hF k)
  have hs : k ≤ s := by dsimp [s]; omega
  have hpow : s+1=F^k := by dsimp [s]; omega
  obtain ⟨N,hN⟩ := array_group_sizes (by omega : 0<k) hs (hpow ▸ dvd_refl _)
  have hcop : (F^k).Coprime s := (Nat.coprime_self_sub_right (by omega : 1 ≤ F^k)).mpr (by simp)
  have As : ArrayAt k s := array_of_directions (Six.modular (by omega) (hcop.of_dvd_left (dvd_pow_self F (by omega))))
  have As' : ArrayAt k (s+1) := array_of_directions (Six.large_factors (by omega) (hpow ▸ dvd_refl _)).some
  refine ⟨N,fun n hn => ?_⟩
  obtain ⟨t,r,he,hrt,⟨Dt⟩,⟨Dr⟩⟩ := hN n hn
  rw [he]
  apply array_of_cover
  exact Five.truncate_with (a:=0) Dt As As' hrt (by decide)
    (Has.single (array_of_directions (Six.restrict Dt hs))) (Has.single (array_of_directions Dr))

#print axioms eventual_arrays
end Erdos722.PairDesign
