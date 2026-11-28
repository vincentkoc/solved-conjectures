import Green51OddDirections
/-! # Wallis bounds at the critical density -/
open scoped Pointwise
open Filter Finset Green53ParityThreshold Real Green51Hyperplane Green51NearThreshold
namespace Green51CriticalWindow


/-- A sumset above the previous even threshold contains a codimension-two
linear subspace in every ambient rank through the next odd dimension. -/
theorem two_coordinates_above (s n : ℕ) (hs : 0<s) (rank : n≤2*(s+1)+1)
    (A : Finset (𝔽₂ n)) (large : threshold (2*s)<(A.dens:ℝ)) :
    ∃ f : (𝔽₂ n) →ₗ[F] F×F, ∀ x∈f.ker,x∈A+A := by
  classical
  let D := (((A+A : Finset _) : Set (𝔽₂ n))ᶜ)
  have r : Module.finrank F (𝔽₂ n)≤2*(s+1)+1 := by simpa [𝔽₂,𝔽] using rank
  have size : Fintype.card (𝔽₂ n)*2^(2*s) <
      2*A.card*2^(2*s)+Fintype.card (𝔽₂ n)*(2*s).choose s := by
    rw [threshold,Nat.mul_div_cancel_left _ (by decide : 0<2),nnratCast_dens] at large
    unfold halfLayer at large
    have nz : (Fintype.card (𝔽₂ n):ℝ)≠0 := by positivity
    field_simp at large
    exact_mod_cast (show (Fintype.card (𝔽₂ n):ℝ)*2^(2*s) <
      2*(A.card:ℝ)*2^(2*s)+(Fintype.card (𝔽₂ n):ℝ)*((2*s).choose s:ℝ) by linarith)
  obtain ⟨f,miss⟩ := Green51OddDirections.two_coordinate_projection (s+1) (by omega) r D
    (fun T sub parity length => no_short_relation A s size T sub parity (by omega))
  refine ⟨f,fun x hx => ?_⟩
  by_contra absent
  exact miss x absent (LinearMap.mem_ker.mp hx)

/-- The odd-dimensional interval has guaranteed dimension exactly two below
the rank for every odd rank at least five, with the same endpoints as in the preceding rank. -/
theorem guaranteed_odd_next_interval (s : ℕ) (hs : 0<s) {α : ℝ}
    (large : threshold (2*s)<α) (boundary : α≤threshold (2*(s+1)+1)) :
    Green51.guaranteedMaxCosetDim (2*(s+1)+1) α=2*s+1 := by
  let n := 2*(s+1)+1
  have hn : 2≤n := by dsimp [n];omega
  have one : α≤1 := by
    apply boundary.trans
    change 1/2-halfLayer (n/2)≤1
    linarith [halfLayer_pos (n/2)]
  have ub := mt (guaranteed_hyperplane_iff hn one).mp (not_lt_of_ge boundary)
  apply le_antisymm
  · change ¬2*(s+1)+1≤Green51.guaranteedMaxCosetDim (2*(s+1)+1) α+1 at ub
    omega
  have lo := guaranteed_lower_of_two_coordinates (n:=2*(s+1)+1) one (fun A ha =>
    two_coordinates_above s _ hs le_rfl A (large.trans_le ha))
  omega

private theorem wallis_strict (k : ℕ) : Wallis.W k < π/2 := by
  apply lt_of_lt_of_le _ (Wallis.W_le (k+1))
  rw [Wallis.W_succ]
  suffices h : 1 < ((2*(k:ℝ)+2)/(2*k+1))*((2*k+2)/(2*k+3)) by
    simpa using mul_lt_mul_of_pos_left h (Wallis.W_pos k)
  rw [div_mul_div_comm,lt_div_iff₀ (by positivity)]
  nlinarith

private theorem past_odd_layer (k m : ℕ) (hm : 2*k+1 ≤ m) :
    1/Real.sqrt (2*π)/Real.sqrt m<halfLayer k := by
  have identity := wallis_identity k
  have positive := halfLayer_pos k
  have sm : 0<(m:ℝ) := by exact_mod_cast (show 0 < m by omega)
  have sp : 0<2*π := by positivity
  have low : 2*(k:ℝ)+1 ≤ m := by exact_mod_cast hm
  have w := mul_lt_mul_of_pos_left (wallis_strict k)
    (by positivity : 0<halfLayer k^2*(2*(k:ℝ)+1))
  have upper := mul_le_mul_of_nonneg_right low (by positivity : 0≤(π/2)*(halfLayer k)^2)
  have sq : 1 < (halfLayer k*Real.sqrt m*Real.sqrt (2*π))^2 := by
    rw [mul_pow,mul_pow,Real.sq_sqrt sm.le,Real.sq_sqrt sp.le]
    nlinarith only [identity,w,upper]
  rw [div_lt_iff₀ (Real.sqrt_pos.mpr sm),div_lt_iff₀ (Real.sqrt_pos.mpr sp)]
  have non : 0≤halfLayer k*Real.sqrt m*Real.sqrt (2*π) := by positivity
  nlinarith


/-- At the limiting coefficient for the hyperplane question, the exact
guarantee loses two dimensions in every even rank and one in every odd rank. -/
theorem critical_value (n : ℕ) (hn : 2≤n) :
    Green51.guaranteedMaxCosetDim n (1/2-(1/Real.sqrt (2*π))/Real.sqrt n)=n-2+n%2 := by
  let α := 1/2-(1/Real.sqrt (2*π))/Real.sqrt n
  have small : α≤1/2 := by dsimp [α]; exact sub_le_self _ (by positivity)
  let k := n/2
  by_cases odd : n%2=1
  · have h := past_odd_layer k n (by dsimp [k]; omega)
    have above : threshold n<α := by unfold threshold; change 1/2-halfLayer k<_; dsimp [α]; linarith
    rw [guaranteed_above_threshold hn above (by linarith),if_pos small,odd]; omega
  · have kn : 0<k := by dsimp [k]; omega
    let s := k-1
    have eq : n=2*(s+1) := by dsimp [s,k] at *; omega
    have h := past_odd_layer s n (by omega)
    have below := even_layer_strict (s+1)
    have sn : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0<n))
    have kdim : 2*((s+1:ℕ):ℝ)=n := by exact_mod_cast eq.symm
    rw [kdim] at below
    have comp : halfLayer (s+1)<(1/Real.sqrt (2*π))/Real.sqrt n := by
      apply (lt_div_iff₀ sn).mpr; rwa [mul_comm]
    have lb : threshold (2*s)<α := by
      rw [threshold,Nat.mul_div_cancel_left _ (by decide : 0<2)]; dsimp [α]; linarith
    have ub : α≤threshold (2*(s+1)) := by
      rw [threshold,Nat.mul_div_cancel_left _ (by decide : 0<2)]; dsimp [α]; linarith
    change Green51.guaranteedMaxCosetDim n α=_
    calc
      _ = Green51.guaranteedMaxCosetDim (2*(s+1)) α := congrArg (fun n => Green51.guaranteedMaxCosetDim n α) eq
      _ = 2*s := guaranteed_even_next_interval s lb ub
      _ = _ := by omega


/-- At the critical coefficient the host's eventual statement holds with
codimension two. Codimension one fails at the same coefficient. -/
theorem critical_codimension :
    (∀ᶠ n : ℕ in Filter.atTop, ∀ α : ℝ, α>1/2-(1/Real.sqrt (2*π))/Real.sqrt n → α≤1 →
      n≤Green51.guaranteedMaxCosetDim n α+2) ∧
    ¬(∀ᶠ n : ℕ in Filter.atTop, ∀ α : ℝ, α>1/2-(1/Real.sqrt (2*π))/Real.sqrt n → α≤1 →
      n≤Green51.guaranteedMaxCosetDim n α+1) := by
  constructor
  · filter_upwards [Filter.eventually_ge_atTop 2] with n hn
    intro α lo hi
    have monotone : Green51.guaranteedMaxCosetDim n (1/2-(1/Real.sqrt (2*π))/Real.sqrt n) ≤
        Green51.guaranteedMaxCosetDim n α := by
      unfold Green51.guaranteedMaxCosetDim
      apply le_csInf
      · exact ⟨_,univ,by simpa using hi,rfl⟩
      · rintro _ ⟨A,hA,rfl⟩
        exact csInf_le (OrderBot.bddBelow _) ⟨A,lo.le.trans hA,rfl⟩
    rw [critical_value n hn] at monotone
    omega
  · intro one
    exact (lt_irrefl _) ((one_half_codimension_one_iff _ (by positivity)).mp one)

end Green51CriticalWindow
#print axioms Green51CriticalWindow.two_coordinates_above
#print axioms Green51CriticalWindow.guaranteed_odd_next_interval
#print axioms Green51CriticalWindow.critical_value
#print axioms Green51CriticalWindow.critical_codimension
