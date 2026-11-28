import Erdos478EffectiveEvenComplete
import Erdos478SievedEvenScale

/-!
# An explicit prime ceiling for triangularly many factorial collisions

At lengths twice the indices from one through `n`, the number of
reflection pairs is triangular. Bounding the word degree by the largest
length to this triangular power keeps the quadratic Schur estimate.
-/

namespace Erdos478.EffectiveResolvent
open Finset Polynomial

def pairCount (n : ℕ) := ∑ i : Fin n, (i.val+1)

theorem twice_pairCount (n : ℕ) : 2*pairCount n = n*(n+1) := by
  induction n with
  | zero => simp [pairCount]
  | succ n ih =>
    have step : pairCount (n+1) = pairCount n + (n+1) := by
      unfold pairCount
      rw [Fin.sum_univ_castSucc]
      rfl
    rw [step,mul_add,ih]
    ring

def pairedDegrees (n : ℕ) := ∏ i : Fin n, (2*(i.val+1))^(i.val+1)

/-- Size estimates for the height and excluded discriminants, using
separate parameters for the largest length and the number of pairs. -/
theorem paired_sizes (n : ℕ) :
    let b := 2*n+4
    let A := b^2
    let N := pairCount n
    let m := b^N
    let D := pairedDegrees n
    let U := 2*n+1
    let V := wordBound N D U
    D ≤ m ∧ m ≤ 2^(A^2) ∧ V ≤ 2^(heightExp A) ∧
      (2*U)^((2*N)^2)*(2*V)^(D^2) ≤ 2^(badExp A m) := by
  let b := 2*n+4
  let A := b^2
  let N := pairCount n
  let m := b^N
  let D := pairedDegrees n
  let U := 2*n+1
  let V := wordBound N D U
  have ha : 4≤A := by dsimp [A,b]; ring_nf; omega
  have hN : 2*N ≤ A := by rw [show 2*N = _ from twice_pairCount n]; dsimp [A,b]; nlinarith
  have hn : N ≤ A := by omega
  have hu : U ≤ A := by dsimp [A,U,b]; nlinarith
  have hb : b ≤ A := by dsimp [A,b]; nlinarith
  have hD : D ≤ m := by
    change _ ≤ b ^ (∑ i : Fin n, (i.val+1))
    rw [← Finset.prod_pow_eq_pow_sum]
    apply prod_le_prod'
    intro i _
    exact Nat.pow_le_pow_left (by dsimp [b]; omega) _
  have ha' := (Nat.lt_two_pow_self.le : A ≤ 2^A)
  have hm : m ≤ 2^(A^2) := by simpa only [pow_two] using pow_bound (hb.trans ha') hn
  have hD' := hD.trans hm
  have hU := hu.trans ha'
  have one : 1 ≤ (2:ℕ)^0 := by decide
  have two : 2 ≤ (2:ℕ)^1 := by decide
  have height :=
    mul_bound (mul_bound (hn.trans ha') hU)
      (pow_bound (add_bound (mul_bound (hn.trans ha') (pow_bound hD' (le_refl 2))) one) hn)
  have hV : V ≤ 2^(heightExp A) := height
  have hA : 2*N ≤ A*A := hN.trans (Nat.le_mul_self A)
  have hE := mul_bound (pow_bound (mul_bound two hU) (show (2*N)^2 ≤ (A*A)*(A*A) by simpa [pow_two] using Nat.mul_le_mul hA hA))
    (pow_bound (mul_bound two hV) (show D^2 ≤ m*m by simpa [pow_two] using Nat.mul_le_mul hD hD))
  refine ⟨hD,hm,hV,hE.trans (Nat.pow_le_pow_right (by decide) ?_)⟩
  change (1+A)*((A*A)*(A*A))+(1+heightExp A)*(m*m) ≤ badExp A m
  unfold badExp
  omega

def CompleteEvenWitness (n p : ℕ) : Prop :=
  p.Prime ∧ (evenGapProduct (ZMod p) (fun i : Fin n => i.val+1)).Splits ∧
    (evenGapProduct (ZMod p) (fun i : Fin n => i.val+1)).Separable ∧
    ((Ico 1 p).image (fun i => i.factorial % p)).card + n*(n+1) ≤ p-1

/-- A prime through the explicit ceiling splits every gap at lengths
`2,4,...,2*n` and gives `n*(n+1)` distinct collision endpoints. -/
theorem complete_even_prime (n : ℕ) (hn : 0<n) :
    ∃ p ≤ 2^((2*n+4)^(n*(n+1)+34)), CompleteEvenWitness n p := by
  let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  let r : Fin n ↪ ℕ := ⟨fun i => i.val+1,fun i j h => Fin.ext (by dsimp at h; omega)⟩
  have hr (i : Fin n) : 0 < r i := Nat.succ_pos i.val
  have hu (i : Fin n) : 2*r i+1 ≤ 2*n+1 := by
    change 2*(i.val+1)+1 ≤ 2*n+1
    omega
  obtain ⟨e,he,p,hp,hprime,_,hs,hd,hc⟩ := effective_even_complete (I := Fin n) r hr
    (2*n+1) 1 hu (by decide) sievedSchur
  let b := 2*n+4
  let A := b^2
  let N := pairCount n
  let D := pairedDegrees n
  let m := b^N
  let U := 2*n+1
  let V := wordBound N D U
  let B := (2*U)^((2*N)^2)*(2*V)^(D^2)
  change e ≤ D at he
  simp only [one_mul] at hp
  change p ≤ sievedSchurBound e V B at hp
  change _+2*pairCount n ≤ p-1 at hc
  rw [twice_pairCount] at hc
  have ha : 4≤A := by dsimp [A,b]; ring_nf; omega
  obtain ⟨hD,hm,hV,hB⟩ := paired_sizes n
  have hbits : sieveBits e B ≤ A^6 := bit_budget ha hm ((he.trans hD).trans hm) hB
  have hceil := schur_bound_of_bits (he.trans hD) ((he.trans hD).trans hm) hV hbits
  have hmpos : 1 ≤ m := Nat.one_le_pow _ _ (by dsimp [b]; omega)
  refine ⟨p,hp.trans (hceil.trans (Nat.pow_le_pow_right (by decide)
    ((base_exponent_bound A m ha hmpos).trans ?_))),hprime,hs,hd,hc⟩
  change (b^2)^17*(b^N)^2 ≤ b^(n*(n+1)+34)
  rw [← pow_mul,← pow_mul,← pow_add,← twice_pairCount n]
  exact Nat.pow_le_pow_right (by dsimp [b]; omega) (by dsimp [N]; omega)

#print axioms twice_pairCount
#print axioms paired_sizes
#print axioms complete_even_prime

end Erdos478.EffectiveResolvent
