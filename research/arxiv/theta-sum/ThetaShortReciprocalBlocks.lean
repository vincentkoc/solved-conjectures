import ThetaNondivisibleCone

/-! A denominator block transfers unweighted reciprocal-parity discrepancy
to the lower cotangent triangle of the integer theta sum. -/
namespace Arxiv.«2501.03234».ThetaShortReciprocalBlocks
open Finset Real ThetaCotangentTriangle ThetaNondivisibleCone ThetaDivisibleDiagonal ThetaReciprocalCutoff
noncomputable section
variable {p : ℕ} [Fact p.Prime]

def w (p j : ℕ) := weight p (2*j+1)
def sgn (p : ℕ) [Fact p.Prime] (j k : ℕ) : ℝ := quotientSign p (2*j+1) (2*k+1)
def block (p : ℕ) [Fact p.Prime] (J N : ℕ) :=
  2/(p:ℝ)*∑ j∈Ico J N,w p j*∑ k∈range j,w p k*sgn p j k

theorem triangle_approx : ∃ C : ℝ,0<C ∧ ∀ p : ℕ,[Fact p.Prime] → p%2=1 →
    |(S p:ℝ)-block p 0 (p/2)-(p:ℝ)*log p/2|≤ C*p+2*(p:ℝ)*harmonic (p/2) := by
  obtain ⟨C,hC,H⟩ := S_sub_offDiagonal_asymptotic
  refine ⟨C,hC,?_⟩
  intro p _ hp
  have width := width_cutoff (p:=p) (K:=1) (J:=p/2) (by decide) le_rfl (by omega)
  rw [←full_strip,Nat.cast_one,div_one] at width
  have eqn : cotCone p (p/2) 1=block p 0 (p/2) := by
    simp only [cotCone,block,Nat.Ico_zero_eq_range,one_mul,w,sgn]
    congr 1; apply sum_congr rfl; intro j hj
    congr 1; rw [show (2*j+1)/2=j by omega]
    apply sum_congr rfl; intro k hk
    have hk' := mem_range.mp hk
    have hj' := mem_range.mp hj
    have hd : ¬(2*j+1)∣(2*k+1) := by intro h; have := Nat.le_of_dvd (by omega) h; omega
    rw [nondivSign,if_neg hd,quotient_eq_reciprocal hp (by omega) (by omega) (by omega) (by omega)]
  rw [eqn] at width
  have H' := add_le_add (H p hp) width
  calc _ = |((S p:ℝ)-offDiagonal p-(p:ℝ)*log p/2)+(offDiagonal p-block p 0 (p/2))| := by ring_nf
       _ ≤ _ := (abs_add_le ..).trans H'

/-- A bound on all prefixes in the block suffices, including partial end blocks. -/
theorem block_bound {J N : ℕ} (hN : N≤p/2) {D : ℝ} (hD : 0≤D)
    (H : ∀ k<N,∀ a,J≤a → a≤N → ∀ n≤N-a,|∑ i∈range n,sgn p (a+i) k|≤D) :
    |block p J N| ≤ 2*(p:ℝ)*harmonic N*D/(2*J+1) := by
  have hx : 0<(p:ℝ) := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  have col (k : ℕ) (hk : k<N) :
      |∑ j∈Ico (max J (k+1)) N,w p j*sgn p j k| ≤ D*((p:ℝ)/(2*J+1)) := by
    let a := max J (k+1)
    by_cases ha : a<N
    · rw [sum_Ico_eq_sum_range]
      have W := weighted_abs (fun i => w p (a+i)) (fun i => sgn p (a+i) k) (n:=N-a) hD
        (by dsimp [w]; apply (weight_pos (by omega) (by omega)).le)
        (by intro i hi; dsimp [w]; apply (weight_pos (by omega) (by omega)).le)
        (by intro i hi; dsimp [w]; apply weight_antitone <;> omega)
        (H k hk a (le_max_left ..) ha.le)
      apply W.trans
      apply mul_le_mul_of_nonneg_left _ hD
      dsimp [w]
      apply (weight_le (by omega) (by omega)).trans
      gcongr; exact_mod_cast (show 2*J+1≤2*a+1 by have := le_max_left J (k+1); dsimp [a]; omega)
    · have h : Ico (max J (k+1)) N=∅ := Ico_eq_empty (by dsimp [a] at ha;omega)
      rw [h,sum_empty,abs_zero]; positivity
  rw [block,transpose_tail,abs_mul,abs_of_nonneg (by positivity : 0≤2/(p:ℝ))]
  have B := abs_sum_le_sum_abs (fun k => w p k*∑ j∈Ico (max J (k+1)) N,w p j*sgn p j k) (range N)
  have hW (k) (hk : k∈range N) : 0≤w p k := by
    dsimp [w]; have := mem_range.mp hk; exact (weight_pos (by omega) (by omega)).le
  have h1 := sum_le_sum (s:=range N) (fun k hk =>
    mul_le_mul_of_nonneg_left (col k (mem_range.mp hk)) (hW k hk))
  simp only [←sum_mul] at h1
  have h2 := mul_le_mul_of_nonneg_right (weight_mass (p:=p) hN)
    (mul_nonneg hD (div_nonneg hx.le (by positivity : 0≤2*(J:ℝ)+1)))
  have hf := sum_congr (s₁:=range N) rfl (fun k hk => show |w p k*∑ j∈Ico (max J (k+1)) N,w p j*sgn p j k| = _ from (abs_mul ..).trans (congrArg (· * |∑ j∈Ico (max J (k+1)) N,w p j*sgn p j k|) (abs_of_nonneg (hW k hk))))
  rw [hf] at B
  have hb := B.trans h1
  exact (mul_le_mul_of_nonneg_left (hb.trans h2) (by positivity : 0≤2/(p:ℝ))).trans_eq (by field_simp)

#print axioms triangle_approx
#print axioms block_bound
end
end Arxiv.«2501.03234».ThetaShortReciprocalBlocks
