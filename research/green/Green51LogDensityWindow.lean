import Green51GirthColouring

/-! # A logarithmic density window for the guaranteed dimension in a double -/

open Finset Green53ParityThreshold Green51NearThreshold
open scoped Classical Pointwise symmDiff

namespace Green51GirthFrame
open Green51Hyperplane

/-- Every double above the lower threshold contains the kernel of two linear coordinates. -/
theorem kernel_above (s n d : ℕ) (rank : n ≤ 2 * (s + 1) + d) (room : 2 ^ d * (d + 2) + 4 ≤ 2 * (2 * (s + 1)))
    (A : Finset (𝔽₂ n)) (large : threshold (2 * s) < (A.dens : ℝ)) :
    ∃ f : (𝔽₂ n) →ₗ[F] F × F, ∀ x ∈ f.ker, x ∈ A + A := by
  classical
  let D := (A + A)ᶜ
  have size : Fintype.card (𝔽₂ n) * 2 ^ (2 * s) <
      2 * A.card * 2 ^ (2 * s) + Fintype.card (𝔽₂ n) * (2 * s).choose s := by
    rw [threshold, Nat.mul_div_cancel_left _ (by decide : 0 < 2), nnratCast_dens] at large
    unfold halfLayer at large
    have nz : (Fintype.card (𝔽₂ n) : ℝ) ≠ 0 := by positivity
    field_simp at large
    exact_mod_cast (show (Fintype.card (𝔽₂ n) : ℝ) * 2 ^ (2 * s) <
      2 * (A.card : ℝ) * 2 ^ (2 * s) + (Fintype.card (𝔽₂ n) : ℝ) * ((2 * s).choose s : ℝ) by linarith)
  have short (R : Finset (𝔽₂ n)) (rd : R ⊆ D) (odd : Odd R.card) (zero : (∑ a ∈ R, a) = 0) :
      2 * (s + 1) + 1 ≤ R.card := by
    rw [Nat.odd_iff] at odd
    obtain ⟨p, hp⟩ := card_pos.mp (show 0 < R.card by omega)
    have eq := circuit_complement_sum (singleton_subset_iff.mpr hp) zero
    have total : (∑ x ∈ R.erase p, x) = p := by simpa [sdiff_singleton_eq_erase] using eq
    have card := card_erase_of_mem hp
    by_contra! small
    have bad := no_short_relation A s size (R.erase p)
      (fun x hx => Finset.mem_compl.mp (rd (mem_erase.mp hx).2)) (by omega) (by omega)
    rw [total] at bad
    exact bad (Finset.mem_compl.mp (rd hp))
  have rk : Module.finrank F (𝔽₂ n) ≤ (2 * (s + 1) + 1) - 1 + d := by simpa [𝔽₂, 𝔽] using rank
  obtain ⟨f, nz⟩ := linear_four_colouring D (2 * (s + 1) + 1) d rk (by simpa using room) short
  exact ⟨f, fun x hx => by
    by_contra absent
    exact nz x (by simpa [D] using absent) (LinearMap.mem_ker.mp hx)⟩

/-- Throughout the stated density interval the guaranteed affine dimension is exactly n − 2. -/
theorem exact_interval (s n d : ℕ) (hn : 2 ≤ n) (rank : n ≤ 2 * (s + 1) + d)
    (room : 2 ^ d * (d + 2) + 4 ≤ 2 * (2 * (s + 1))) {α : ℝ} (lower : threshold (2 * s)<α) (upper : α ≤ threshold n) :
    Green51.guaranteedMaxCosetDim n α = n - 2 := by
  have one : α ≤ 1 := by
    apply upper.trans
    change 1 / 2 - halfLayer (n / 2) ≤ 1
    linarith [halfLayer_pos (n / 2)]
  have no := mt (guaranteed_hyperplane_iff hn one).mp (not_lt_of_ge upper)
  have lo := guaranteed_lower_of_two_coordinates (n := n) one (fun A ha =>
    kernel_above s n d rank room A (lower.trans_le ha))
  omega

/-- In dimension sixteen the guarantee is fourteen for minimum sizes 25,377 through 26,333. -/
theorem sixteen {α : ℝ} (lower : 25376 / 65536<α) (upper : α ≤ 26333 / 65536) :
    Green51.guaranteedMaxCosetDim 16 α = 14 := by
  apply exact_interval 6 16 2 (by decide) (by decide) (by decide)
  · convert lower using 1; norm_num [threshold, halfLayer, Nat.choose]
  · convert upper using 1; norm_num [threshold, halfLayer, Nat.choose]
/-- In dimension twelve the guarantee is ten for minimum sizes 1,489 through 1,586. -/
theorem twelve {α : ℝ} (lower : 1488 / 4096<α) (upper : α ≤ 1586 / 4096) :
    Green51.guaranteedMaxCosetDim 12 α = 10 := by
  apply exact_interval 4 12 2 (by decide) (by decide) (by decide)
  · convert lower using 1; norm_num [threshold, halfLayer, Nat.choose]
  · convert upper using 1; norm_num [threshold, halfLayer, Nat.choose]
end Green51GirthFrame

namespace Green51GirthFrame
open Green51Hyperplane

/-- Logarithmic allowance for additional independent directions. -/
def logWidth (n : ℕ) : ℕ := Nat.log 2 n - Nat.log 2 (Nat.log 2 n + 2)

/-- The logarithmic width satisfies the total slice budget. -/
theorem log_room {n : ℕ} (hn : 16 ≤ n) :
    2 ^ (logWidth n) * (logWidth n + 2) + 4 ≤ 2 * (2 * ((n - logWidth n - 1) / 2 + 1)) := by
  let k := Nat.log 2 n
  let j := Nat.log 2 (k + 2)
  let d := k - j
  change 2 ^ d * (d + 2) + 4 ≤ 2 * (2 * ((n - d - 1) / 2 + 1))
  have hk : 4 ≤ k := Nat.le_log_of_pow_le (by decide) (by simpa using hn)
  have hj : 2 ≤ j := Nat.le_log_of_pow_le (by decide) (by change 4 ≤ k + 2; omega)
  have kn : 2 ^ k ≤ n := Nat.pow_log_le_self 2 (by omega)
  have kn' : k < n := Nat.log_lt_self 2 (by omega)
  by_cases pos : 0 < d
  · have sum : d + j = k := by dsimp [d] at *; omega
    have low : d < 2 ^ d := Nat.lt_pow_self (by decide)
    have kp : k + 2 < 2 ^ (j + 1) := Nat.lt_pow_succ_log_self (by decide) (k + 2)
    have slack : d + 2 + 3 ≤ 2 ^ (j + 1) := by omega
    have mult := Nat.mul_le_mul_left (2 ^ d) slack
    rw [←pow_add, show d + (j + 1) = k + 1 by omega, pow_succ] at mult
    rw [Nat.mul_add] at mult
    omega
  · have : d = 0 := by omega
    simp only [this, pow_zero, zero_add, one_mul, Nat.sub_zero]
    omega

/-- The guaranteed dimension stays at n − 2 across logarithmically many ambient dimension steps. -/
theorem logarithmic_interval {n : ℕ} (hn : 16 ≤ n) {α : ℝ}
    (lower : threshold (n - logWidth n - 1)<α) (upper : α ≤ threshold n) :
    Green51.guaranteedMaxCosetDim n α = n - 2 := by
  let s := (n - logWidth n - 1) / 2
  have dn : logWidth n < n := lt_of_le_of_lt (Nat.sub_le ..) (Nat.log_lt_self 2 (by omega))
  apply exact_interval s n (logWidth n) (by omega) (by dsimp [s]; omega) (log_room hn) _ upper
  simpa [s, threshold, Nat.mul_div_cancel_left _ (by decide : 0 < 2)] using lower

end Green51GirthFrame

#print axioms Green51GirthFrame.kernel_above
#print axioms Green51GirthFrame.exact_interval
#print axioms Green51GirthFrame.log_room
#print axioms Green51GirthFrame.logarithmic_interval
#print axioms Green51GirthFrame.twelve
#print axioms Green51GirthFrame.sixteen
