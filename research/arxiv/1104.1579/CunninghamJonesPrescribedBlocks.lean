import CunninghamJonesBlockPatterns
import CunninghamJonesPrescribedPrimes

/-! Choosing the prime bases for an arbitrary list of positive multiplicities. -/

namespace CunninghamChain.JonesSplitParity
open Finset

/-- Any finite nonempty list of positive exponents can be realized by distinct
increasing primes above B whose prime-power blocks meet the split criterion. -/
theorem exists_prescribed_blocks (e : ℕ → ℕ) (n B : ℕ) (he : ∀ i ≤ n, 0 < e i) :
    ∃ (q : ℕ → ℕ) (k c : ℕ), BlockPattern (fun i => q i ^ e i) q n k c ∧
      StrictMonoOn q (Set.Iio (n+1)) ∧ ∀ i ≤ n, (q i).Prime ∧ B < q i := by
  let E := ∏ i ∈ range (n+1),e i
  let w (i : ℕ) := e (min i n)
  have hE : 0 < E := prod_pos fun i hi => he i (Nat.lt_succ_iff.mp (mem_range.mp hi))
  have hw (i : ℕ) : 0 < w i := he _ (min_le_right ..)
  have hd (i : ℕ) : w i ∣ E := dvd_prod_of_mem e (mem_range.mpr (Nat.lt_succ_of_le (min_le_right ..)))
  let G := 4*E+1
  let c := G^E
  let k := c^n+n+2
  let W := 2^(k+1)
  let D := 4*E*W
  let exp (i : ℕ) := if i=n then 2^k-n else 1
  let residue (i : ℕ) := G^((E / w i)*exp i)
  have hG : G.Coprime (4*E) := by simp [G]
  have htwo : G.Coprime 2 := Nat.coprime_two_right.mpr ⟨2*E,by dsimp [G]; omega⟩
  have hGD : G.Coprime D := hG.mul_right (htwo.pow_right _)
  have hstep (i : ℕ) : 4*w (i+1) ∣ 4*E := Nat.mul_dvd_mul_left _ (hd _)
  have hone (i : ℕ) : residue i ≡ 1 [MOD 4*w (i+1)] := by
    have hz := Nat.modEq_zero_iff_dvd.mpr (hstep i)
    have hb : G ≡ 1 [MOD 4*w (i+1)] := hz.add_right 1
    simpa [residue] using hb.pow ((E / w i)*exp i)
  obtain ⟨q,h⟩ := exists_prescribed_prefix D B residue w (by dsimp [D,W]; positivity) hw
    (fun i => hGD.pow_left _) (fun i => (hstep i).trans (dvd_mul_right ..)) hone (n+1)
  have weights (i : ℕ) (hi : i ≤ n) : w i=e i := by simp [w,min_eq_left hi]
  have block_mod (i : ℕ) (hi : i ≤ n) : ((q i ^ e i : ℕ) : ZMod W) = (c:ZMod W)^(exp i) := by
    have hh := ((h.residues i (Nat.lt_succ_of_le hi)).of_dvd (dvd_mul_left W (4*E))).pow (e i)
    have de : ((E / w i)*exp i)*e i=E*exp i := by
      rw [←weights i hi,Nat.mul_right_comm,Nat.div_mul_cancel (hd i)]
    change q i ^ e i ≡ (G^((E/w i)*exp i))^(e i) [MOD W] at hh
    rw [←pow_mul,de,pow_mul] at hh
    simpa [c] using (ZMod.natCast_eq_natCast_iff ..).mpr hh
  have first (i : ℕ) (hi : i<n) : ((q i ^ e i : ℕ) : ZMod W) = c := by
    simpa [exp,hi.ne] using block_mod i hi.le
  have hn : n ≤ 2^k := by have : k<2^k := Nat.lt_two_pow_self; dsimp [k] at *; omega
  refine ⟨q,k,c,⟨?_,?_,?_,?_,?_,first,?_,?_,?_⟩,h.increasing,?_⟩
  · intro i hi
    exact ((h.prime i (by omega)).odd_of_ne_two (by have := h.large i (by omega); omega)).pow
  · intro i hi; have := h.large i (by omega); omega
  · intro i hi; exact dvd_pow_self _ (he i hi).ne'
  · exact Nat.one_lt_pow hE.ne' (by dsimp [G]; omega)
  · have : k+1<2^(k+1) := Nat.lt_two_pow_self
    dsimp [k] at *; omega
  · change ((∏ i ∈ range (n+1),q i ^ e i : ℕ):ZMod W)=1
    rw [prod_range_succ,Nat.cast_mul]
    have hp := prod_congr (s₁:=range n) (s₂:=range n) rfl (fun i hi => first i (mem_range.mp hi))
    rw [Nat.cast_prod,hp]
    simp only [prod_const,card_range]
    rw [block_mod n (le_refl _),show exp n=2^k-n by simp [exp],←pow_add,Nat.add_sub_of_le hn]
    have hf := Nat.ModEq.pow_totient ((htwo.pow_left E).pow_right (k+1))
    rw [Nat.totient_prime_pow_succ Nat.prime_two] at hf
    simpa [W,c] using (ZMod.natCast_eq_natCast_iff ..).mpr hf
  · intro i hi
    simpa [weights (i+1) (by omega)] using h.nextSquare i (by omega)
  · intro i j hij hj
    push_cast
    rw [h.laterResidues i j hij (by omega),one_pow]
  · intro i hi
    exact ⟨h.prime i (by omega),(le_max_right ..).trans_lt (h.large i (by omega))⟩

#print axioms exists_prescribed_blocks

end CunninghamChain.JonesSplitParity
