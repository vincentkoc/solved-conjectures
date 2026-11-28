import Green50Sharp

/-!
# Positive-density Hamming balls with a growing twofold obstruction

The central binomial recurrence gives an elementary effective lower bound for the mass
of balls of radius just below half the dimension in an odd binary cube.
-/

namespace Green50HammingDensity

open Finset Green50Downsets Green50Sharp

/-- The cardinality of a binary Hamming ball. -/
theorem ball_count (n k : ℕ) : (ball n k).card = ∑ i ∈ range (k+1), n.choose i := by
  classical
  let vec (s : Finset (Fin n)) : Cube n := fun j => if j ∈ s then 1 else 0
  have hvec (s : Finset (Fin n)) : supp (vec s) = s := by ext j; simp [supp, vec]
  have hleft (x : Cube n) : vec (supp x) = x := by
    funext j
    have hb : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
    rcases hb (x j) with h | h <;> simp [vec,supp,h]
  have hcard (i : ℕ) : (univ.filter (fun x : Cube n => (supp x).card = i)).card = n.choose i := by
    conv_rhs => rw [show n = (univ : Finset (Fin n)).card by simp, ← card_powersetCard]
    exact card_bij' (fun x _ => supp x) (fun s _ => vec s)
      (fun x hx => mem_powersetCard.mpr ⟨subset_univ _, (mem_filter.mp hx).2⟩)
      (fun s hs => mem_filter.mpr ⟨mem_univ _, by rw [hvec,(mem_powersetCard.mp hs).2]⟩)
      (fun x _ => hleft x) (fun s _ => hvec s)
  simp_rw [←hcard, sum_card_fiberwise_eq_card_filter]
  simp only [ball, mem_range, Nat.lt_succ_iff]
private theorem central_binomial_bound (m : ℕ) : m.centralBinom ^ 2 * (m+1) ≤ 16^m := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    have h : ((m+1)*((m+1).centralBinom))^2 =
        (2*(2*m+1)*m.centralBinom)^2 := congrArg (·^2) (Nat.succ_mul_centralBinom_succ m)
    have hc : (2*m+1)^2*(m+2) ≤ 4*(m+1)^3 := by nlinarith
    have h1 : (m+1)^2 * ((m+1).centralBinom^2 * (m+2)) ≤ (m+1)^2*(16^m*16) := calc
      _ = (2*(2*m+1)*m.centralBinom)^2*(m+2) := by
        rw [←h]; ring
      _ = (m.centralBinom^2*4)*((2*m+1)^2*(m+2)) := by ring
      _ ≤ (m.centralBinom^2*4)*(4*(m+1)^3) := Nat.mul_le_mul_left _ hc
      _ = (m+1)^2 * ((m.centralBinom^2*(m+1))*16) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ ih)
    simpa [pow_succ] using (Nat.le_of_mul_le_mul_left h1 (by positivity))

private theorem lower_binomial_tail (m s : ℕ) (hs : s ≤ m) :
    4^m ≤ (∑ i ∈ range (m-s+1), (2*m+1).choose i) + 2*s*m.centralBinom := by
  have hrest : (∑ i ∈ Ico (m-s+1) (m+1), (2*m+1).choose i) ≤ s*(2*m.centralBinom) := calc
    _ ≤ ∑ _i ∈ Ico (m-s+1) (m+1), 2*m.centralBinom := by
      apply sum_le_sum
      intro i hi
      cases i with
      | zero => simpa using (show 1 ≤ 2*m.centralBinom by have := m.centralBinom_pos; omega)
      | succ i =>
        rw [Nat.choose_succ_succ]
        simpa only [two_mul] using Nat.add_le_add (Nat.choose_le_centralBinom i m) (Nat.choose_le_centralBinom i.succ m)
    _ = _ := by simp [show m+1-(m-s+1)=s by omega]
  have hsum := sum_range_add_sum_Ico (fun i => (2*m+1).choose i) (show m-s+1 ≤ m+1 by omega)
  rw [Nat.sum_range_choose_halfway] at hsum
  nlinarith

/-- The density loss from one half is at most `1/q` once `m ≥ (q*s)²`. -/
theorem ball_near_half (m s q : ℕ) (hq : 0 < q) (hm : (q*s)^2 ≤ m) :
    1/2 - 1/(q:ℝ) ≤ ((ball (2*m+1) (m-s)).dens : ℝ) := by
  have hsq : s ≤ q*s := by simpa using Nat.mul_le_mul_right s hq
  have hs : s ≤ m := by nlinarith
  have hcl : q*s*m.centralBinom ≤ 4^m := by
    have h1 : (q*s*m.centralBinom)^2 ≤ (4^m)^2 := calc
      _ = m.centralBinom^2*(q*s)^2 := by ring
      _ ≤ m.centralBinom^2*(m+1) := Nat.mul_le_mul_left _ (by omega)
      _ ≤ 16^m := central_binomial_bound m
      _ = (4^m)^2 := by rw [← pow_right_comm]; norm_num
    exact le_of_not_gt (fun hlt => (not_lt_of_ge h1) (Nat.pow_lt_pow_left hlt (by decide)))
  have h := lower_binomial_tail m s hs
  rw [← ball_count] at h
  have bound : q*4^m ≤ q*(ball (2*m+1) (m-s)).card + 2*4^m := calc
    _ ≤ _ := Nat.mul_le_mul_left q h
    _ = q*(ball (2*m+1) (m-s)).card + 2*(q*s*m.centralBinom) := by ring
    _ ≤ _ := by gcongr
  have hh : (q:ℝ)*4^m ≤ q*((ball (2*m+1) (m-s)).card : ℝ) + 2*4^m := by exact_mod_cast bound
  have card : Fintype.card (Cube (2*m+1)) = 2^(2*m+1) := by simp [Cube,Fintype.card_pi]
  have da : ((ball (2*m+1) (m-s)).dens : ℝ) = ((ball (2*m+1) (m-s)).card : ℝ) / 2^(2*m+1) := by
    simp [Finset.dens,card]
  rw [da,le_div_iff₀ (by positivity),pow_succ,pow_mul]
  have hq' : (0:ℝ) < q := by exact_mod_cast hq
  norm_num
  field_simp
  nlinarith

/-- If `16 s² ≤ m`, the radius `m-s` Hamming ball in `2m+1` dimensions has density at least `1/4`. -/
theorem ball_quarter (m s : ℕ) (hs : 16*s^2 ≤ m) :
    1/4 ≤ ((ball (2*m+1) (m-s)).dens : ℝ) := by
  have h := ball_near_half m s 4 (by decide) (by nlinarith)
  norm_num at h
  exact h


/-- At every fixed density below one half, there are balls with arbitrarily large gaps
between the dimension and the maximum twofold weight. -/
theorem near_half_gap (ρ : ℝ) (hρ : ρ < 1/2) (T N : ℕ) :
    ∃ n ≥ N, ∃ k, ρ < ((ball n k).dens : ℝ) ∧ T+2*k < n := by
  obtain ⟨q,hq⟩ := exists_nat_one_div_lt (sub_pos.mpr hρ)
  let s := T+N+1
  let m := ((q+1)*s)^2
  have hqs : s ≤ (q+1)*s := Nat.le_mul_of_pos_left _ (by omega)
  have hs : s ≤ m := by dsimp [m]; nlinarith
  have hn : N ≤ 2*m+1 := by dsimp [s] at hs; omega
  have ha := ball_near_half m s (q+1) (by omega) (le_refl _)
  rw [Nat.cast_add,Nat.cast_one] at ha
  refine ⟨2*m+1,hn,m-s,by linarith,?_⟩
  dsimp [s] at hs ⊢
  omega

#print axioms Green50HammingDensity.near_half_gap
#print axioms Green50HammingDensity.ball_near_half
#print axioms Green50HammingDensity.ball_count
#print axioms Green50HammingDensity.ball_quarter

end Green50HammingDensity
