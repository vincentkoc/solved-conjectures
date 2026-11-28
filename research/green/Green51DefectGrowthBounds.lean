import Green51LabelledKernelBound
import Green51SingleRowGrowth
import Green51SubspaceGrowth

/-! # Finite upper and lower bounds for the universal class number -/
namespace Green51FrameIsomorphisms
open Green53ParityThreshold

theorem upper_growth (h : ℕ) :
    universalDefectNumber h ≤ h^h * (h+1) * 2^(h*h/4+h) := by
  have hdim : Module.finrank F (Fin h →₀ F)=h := by simp
  simpa [Nat.mul_assoc] using (labelled_kernel_bound h).trans
    (Nat.mul_le_mul_left _ (Green51SubspaceGrowth.all_subspaces_le _ hdim))

theorem lower_growth_at_rank {h d : ℕ} (pos : 0<d) (dim : d<h) (room : h≤2^(d-1)) :
    2^(d*(h-d)) ≤ universalDefectNumber h * h^h * 2^(h+d) := by
  have width : 2^d=2^(d-1)*2 := by
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero pos.ne'
    simp [pow_succ]
  have atLeast : 2^(d-1)≤2^d+1-h := by omega
  have falling := (Nat.pow_le_pow_left atLeast h).trans ((2^d).pow_sub_le_descFactorial h)
  rw [Nat.descFactorial_eq_factorial_mul_choose] at falling
  have c := single_row_count (show 0<h by omega) (show d≤h-1 by omega)
  have budget := falling.trans (Nat.mul_le_mul (Nat.factorial_le_pow h) c)
  rw [←pow_mul] at budget
  have exp1 : d*(h-d)+d*d=(d-1)*h+h := by
    obtain ⟨a,rfl⟩ := Nat.exists_eq_succ_of_ne_zero pos.ne'
    obtain ⟨b,rfl⟩ := Nat.exists_eq_add_of_le dim.le
    simp only [Nat.add_sub_cancel_left,Nat.add_one_sub_one]
    simp only [Nat.succ_eq_add_one]
    ring
  apply Nat.le_of_mul_le_mul_right _ (by positivity : 0<2^(d*d))
  calc
    _ = 2^((d-1)*h)*2^h := by rw [←pow_add,exp1,pow_add]
    _ ≤ _ := Nat.mul_le_mul_right _ budget
    _ = _ := by rw [pow_add,pow_add];ring

private theorem half_square (h : ℕ) : h/2*(h-h/2)=h*h/4 := by
  obtain ⟨k,eq|eq⟩ : ∃ k,h=2*k ∨ h=2*k+1 := ⟨h/2,by omega⟩
  · rw [eq]
    simp only [Nat.mul_div_cancel_left _ (by decide : 0<2)]
    have sub : 2*k-k=k := by omega
    rw [sub,show 2*k*(2*k)=k*k*4 by ring,Nat.mul_div_cancel _ (by decide)]
  · rw [eq]
    have half : (2*k+1)/2=k := by omega
    have sub : 2*k+1-k=k+1 := by omega
    rw [half,sub,show (2*k+1)*(2*k+1)=4*(k*(k+1))+1 by ring]
    omega

private theorem half_room {h : ℕ} (large : 10≤h) : h≤2^(h/2-1) := by
  have bound (k : ℕ) (hk : 5≤k) : 2*k+1≤2^(k-1) := by
    induction k,hk using Nat.le_induction with
    | base => decide
    | succ k hk ih =>
      have eq : k+1-1=(k-1)+1 := by omega
      rw [eq,pow_succ]
      omega
  have b := bound (h/2) (by omega)
  omega

theorem lower_growth {h : ℕ} (large : 10≤h) :
    2^(h*h/4) ≤ universalDefectNumber h * h^h * 2^(h+h/2) := by
  rw [←half_square h]
  exact lower_growth_at_rank (by omega) (by omega) (half_room large)

end Green51FrameIsomorphisms
#print axioms Green51FrameIsomorphisms.upper_growth
#print axioms Green51FrameIsomorphisms.lower_growth
