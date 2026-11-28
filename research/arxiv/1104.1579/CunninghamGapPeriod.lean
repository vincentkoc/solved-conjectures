import CunninghamGapLocalMean

/-! Complete-period means and the incomplete-period error for a finite prime cutoff. -/

namespace CunninghamChain.GapMean

open Finset BatemanHornConjecture

private lemma full_sum {M : ℕ} [NeZero M] (f : ZMod M → ℝ) :
    ∑ n ∈ range M, f (n:ZMod M) = ∑ a : ZMod M, f a := by
  classical
  apply sum_bij' (fun (n : ℕ) _ => (n:ZMod M)) (fun (a : ZMod M) _ => a.val)
  · simp
  · exact fun a _ => mem_range.mpr a.val_lt
  · intro n hn
    simpa using Nat.mod_eq_of_lt (mem_range.mp hn : n<M)
  · simp
  · simp

/-- A leftover interval costs at most one full period of nonnegative weights. -/
theorem periodic_error {M : ℕ} [NeZero M] (g : ZMod M → ℝ) (nn : ∀ x, 0≤g x) (N : ℕ) :
    |(∑ n ∈ range N, g (n:ZMod M)) - (N:ℝ)*((∑ a : ZMod M, g a)/M)| ≤
      ∑ a : ZMod M, g a := by
  let f (t : ℕ) := ∑ n ∈ range t, g (n:ZMod M)
  have pos : 0<M := Nat.pos_of_ne_zero (NeZero.ne M)
  have mp : (0:ℝ)<M := by exact_mod_cast pos
  have shift (t u : ℕ) : f (M*t+u) = f (M*t)+f u := by unfold f; rw [sum_range_add]; simp
  have blocks (t : ℕ) : f (M*t)=(t:ℝ)*f M := by
    induction t with
    | zero => simp [f]
    | succ t ih => rw [Nat.mul_succ,shift,ih]; push_cast; ring
  have mono (a b : ℕ) (h : a≤b) : f a ≤ f b :=
    sum_le_sum_of_subset_of_nonneg (range_mono h) (fun n _ _ => nn n)
  have fp : 0≤f (N%M) := sum_nonneg fun n _ => nn n
  have fm : 0≤f M := sum_nonneg fun n _ => nn n
  have bound := mono _ _ (Nat.mod_lt N pos).le
  have size : ((N%M:ℕ):ℝ)≤M := by exact_mod_cast (Nat.mod_lt N pos).le
  have scaled : ((N%M:ℕ):ℝ)*(f M/M)≤f M := by
    calc _ ≤ (M:ℝ)*(f M/M) := mul_le_mul_of_nonneg_right size (div_nonneg fm mp.le)
         _ = _ := by field_simp
  have eq : f N - (N:ℝ)*(f M/M) = f (N%M)-((N%M:ℕ):ℝ)*(f M/M) := by
    conv_lhs => rw [←Nat.div_add_mod N M]
    rw [shift,blocks]; push_cast; field_simp; ring
  rw [←full_sum]
  change |f N-(N:ℝ)*(f M/M)|≤f M
  rw [eq,abs_le]
  exact ⟨by linarith,by linarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) (N%M)) (div_nonneg fm mp.le)]⟩

#print axioms periodic_error

/-- A finite truncation, also defined at the exceptional gaps. -/
noncomputable def factor (k l q : ℕ) (x : ZMod q) : ℝ :=
  if h : q.Prime then by letI : Fact q.Prime := ⟨h⟩; exact pairFactor k l q x else 1

noncomputable def pairProduct (k l Y h : ℕ) : ℝ :=
  ∏ q ∈ Y.primesBelow, factor k l q h

private lemma factor_nonneg (k l q : ℕ) (x : ZMod q) : 0≤factor k l q x := by
  unfold factor
  split_ifs with h
  · let : Fact q.Prime := ⟨h⟩
    have p : (1:ℝ)<q := by exact_mod_cast h.one_lt
    have zero : 0<1-1/(q:ℝ) := sub_pos.mpr ((div_lt_one (by linarith)).mpr p)
    unfold pairFactor
    positivity
  · norm_num

/-- The complete-period average is the product of the pinned single-prefix partial products.
Starting the gap interval at any offset changes the sum by at most one period's contribution. -/
theorem truncated_gap_mean (k l Y N offset : ℕ) :
    let P := ∏ q ∈ Y.primesBelow, q
    let B := BatemanHornPartialProduct (chainForms 1 k) Y * BatemanHornPartialProduct (chainForms 1 l) Y
    |(∑ n ∈ range N, pairProduct k l Y (n+offset)) - (N:ℝ)*B| ≤ (P:ℝ)*B := by
  classical
  let T := Y.primesBelow
  have prime (q : T) : (q:ℕ).Prime := Nat.prime_of_mem_primesBelow q.2
  let (q : T) : Fact (q:ℕ).Prime := ⟨prime q⟩
  let M := ∏ q : T, (q:ℕ)
  have pos : 0<M := prod_pos fun q _ => (prime q).pos
  let : NeZero M := ⟨pos.ne'⟩
  let e := ZMod.prodEquivPi (fun q : T => (q:ℕ)) (fun a b hab =>
    (Nat.coprime_primes (prime a) (prime b)).mpr fun he => hab (Subtype.ext he))
  let V (x : ZMod M) := ∏ q : T, factor k l q (e x q)
  let G (x : ZMod M) := V (x+offset)
  have non (x) : 0≤G x := prod_nonneg fun q _ => factor_nonneg ..
  have natval (n : ℕ) : G (n:ZMod M) = pairProduct k l Y (n+offset) := by
    dsimp only [G,V]
    rw [←Nat.cast_add,map_natCast]
    exact prod_coe_sort T (fun q => factor k l q ((n+offset:ℕ):ZMod q))
  have total : (∑ x : ZMod M, G x) = ∏ q : T, ∑ z : ZMod (q:ℕ), factor k l q z := calc
    _ = ∑ x : ZMod M, V x := Equiv.sum_comp (Equiv.addRight (offset:ZMod M)) V
    _ = ∑ x : ((q : T) → ZMod (q:ℕ)), ∏ q : T, factor k l q (x q) := e.toEquiv.sum_comp (fun x => ∏ q : T, factor k l q (x q))
    _ = _ := by simpa using (prod_univ_sum (fun q : T => (univ : Finset (ZMod (q:ℕ))))
      (fun (q : T) z => factor k l q z)).symm
  have localMean (q : T) : (∑ z : ZMod (q:ℕ), factor k l q z)/(q:ℝ)=
      singleFactor k q * singleFactor l q := by simpa [factor,prime q] using mean_pairFactor k l q
  have prodSingle (m : ℕ) : (∏ q : T, singleFactor m q) = BatemanHornPartialProduct (chainForms 1 m) Y := by
    unfold BatemanHornPartialProduct
    rw [chainForms_count]
    exact prod_coe_sort T (fun q => (1-1/(q:ℝ))^(-(m:ℤ))*(1-(OmegaP (chainForms 1 m) q:ℝ)/q))
  let B := BatemanHornPartialProduct (chainForms 1 k) Y * BatemanHornPartialProduct (chainForms 1 l) Y
  have mean : (∑ x : ZMod M, G x)/(M:ℝ)=B := by
    rw [total,show (M:ℝ)=∏ q : T, (q:ℝ) by dsimp [M]; push_cast; rfl,←prod_div_distrib]
    simp_rw [localMean]
    rw [prod_mul_distrib,prodSingle,prodSingle]
  have sumEq := (div_eq_iff (show (M:ℝ)≠0 by exact_mod_cast pos.ne')).mp mean
  have res := periodic_error G non N
  simp_rw [natval] at res
  rw [mean,sumEq,mul_comm B] at res
  simpa only [M,prod_coe_sort T (fun q => q)] using res

#print axioms truncated_gap_mean

end CunninghamChain.GapMean
