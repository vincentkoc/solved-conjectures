import CunninghamPrimePowerRationalRoots

/-! A finite denominator search and a density-zero set of exceptional coefficients. -/

namespace CunninghamChain.LinearRoots
open Finset Filter Topology Polynomial

/-- The coefficient determined by the signed denominator and the index. -/
def coefficientAt (d : ℤ) (n : ℕ) : ℕ :=
  d.natAbs^2*(d^n-1).natAbs/(d-1).natAbs^2

private lemma size_of_root {a n : ℕ} {d e : ℤ} (hd : 2≤d.natAbs) (he : e.natAbs=1)
    (eq : (a:ℤ)*(d-1)^2=e*d^2*(d^n-1)) :
    a=coefficientAt d n ∧ 2^n≤4*a+1 := by
  have h := congrArg Int.natAbs eq
  simp only [Int.natAbs_mul,Int.natAbs_pow,Int.natAbs_natCast,he,one_mul] at h
  have hpos : 0<(d-1).natAbs^2 := pow_pos (Int.natAbs_pos.mpr (by omega)) _
  constructor
  · simp [coefficientAt,←h,Nat.mul_div_cancel _ hpos]
  · have bound : (d-1).natAbs ≤ 2*d.natAbs := by have := Int.natAbs_sub_le d 1; omega
    have hz : d.natAbs^2*(d^n-1).natAbs ≤ d.natAbs^2*(4*a) := calc
      _ = a*(d-1).natAbs^2 := h.symm
      _ ≤ a*(2*d.natAbs)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left bound _)
      _ = _ := by ring
    have ht := Nat.le_of_mul_le_mul_left hz (pow_pos (by omega : 0<d.natAbs) 2)
    have hplus := Int.natAbs_add_le (d^n-1) 1
    simp only [sub_add_cancel,Int.natAbs_pow,Int.natAbs_one] at hplus
    exact (Nat.pow_le_pow_left hd n).trans (by omega)

/-- At each positive index the possible denominators of rational roots for the two signs
together are exactly those satisfying the divisor test. Each determines the coefficient. -/
theorem possible_signed_denominator {d : ℤ} {n : ℕ} (hd : 2≤d.natAbs) (hn : 0<n) :
    (∃ a : ℕ, 0<a ∧ ∃ k : Bool, (term k a (-a) n).IsRoot (d:ℚ)⁻¹) ↔ d-1 ∣ (n:ℤ) := by
  have e := fun k a => scaled_root_iff k a n d (by omega) (by omega)
  constructor
  · rintro ⟨a,ha,k,hk⟩
    exact (root_denominator_arithmetic hd hn (show (sign k)^2=1 by cases k <;> norm_num [sign])
      ((e k a).mp hk)).1
  · intro h
    obtain ⟨a,ha,z,hz,he⟩ := exists_scaled_root_equation hd hn h
    rcases hz with rfl|rfl
    · exact ⟨a,ha,true,(e true a).mpr (by simpa [sign] using he)⟩
    · exact ⟨a,ha,false,(e false a).mpr (by simpa [sign] using he)⟩

/-- Positive coefficients through H producing a rational root at any positive index, for either sign. -/
noncomputable def exceptionalCoefficients (H : ℕ) : Finset ℕ :=
  open Classical in (Icc 1 H).filter fun a => ∃ k : Bool, ∃ n>0, ∃ x : ℚ, (term k a (-a) n).IsRoot x

/-- A uniform squared-logarithmic bound counts all exceptional coefficients, with no index cutoff. -/
theorem exceptional_coefficients_bound (H : ℕ) :
    (exceptionalCoefficients H).card ≤ ((4*H+1).log2+1)*(2*(4*H+1).log2+3) := by
  classical
  let L := (4*H+1).log2
  let D := Icc (-(L:ℤ)-1) ((L:ℤ)+1)
  let pairs := (range (L+1)) ×ˢ D
  have hsub : exceptionalCoefficients H ⊆ pairs.image (fun t => coefficientAt t.2 t.1) := by
    intro a ha
    obtain ⟨hI,k,n,hn,x,hx⟩ := mem_filter.mp ha
    have lim := mem_Icc.mp hI
    obtain ⟨d,hd,_,he⟩ := (rational_root_iff_denominator k a n lim.1 hn x).mp hx
    have ⟨eq,bound⟩ := size_of_root hd (show (sign k).natAbs=1 by cases k <;> decide) he
    have hl : n≤L := (Nat.le_log2 (by omega : 4*H+1≠0)).mpr (by omega)
    have hm := (root_denominator_arithmetic hd hn (show (sign k)^2=1 by cases k <;> decide) he).1
    have hdv : (d-1).natAbs ∣ n := by simpa using Int.natAbs_dvd_natAbs.mpr hm
    have hdle := Nat.le_of_dvd hn hdv
    refine mem_image.mpr ⟨(n,d),mem_product.mpr ⟨mem_range.mpr (by omega),mem_Icc.mpr ?_⟩,eq.symm⟩
    constructor <;> omega
  calc
    _ ≤ (pairs.image (fun t => coefficientAt t.2 t.1)).card := card_le_card hsub
    _ ≤ pairs.card := card_image_le
    _ = _ := by
      have len : D.card=2*L+3 := by rw [show D=Icc (-(L:ℤ)-1) ((L:ℤ)+1) by rfl,Int.card_Icc]; omega
      simp [pairs,len,L]

/-- The proportion of positive coefficients producing any rational root tends to zero. -/
theorem exceptional_coefficients_density_zero :
    Tendsto (fun H : ℕ => ((exceptionalCoefficients H).card:ℝ)/H) atTop (𝓝 0) := by
  let L (H : ℕ) := (4*H+1).log2
  have hL : Tendsto L atTop atTop := by
    apply tendsto_atTop.mpr
    intro n
    filter_upwards [eventually_ge_atTop (2^n)] with H hH
    exact (Nat.le_log2 (by omega : 4*H+1≠0)).mpr (by omega)
  have ratio : Tendsto (fun n : ℕ => (n:ℝ)^2/2^n) atTop (𝓝 0) :=
    tendsto_pow_const_div_const_pow_of_one_lt 2 (by norm_num : (1:ℝ)<2)
  have lim : Tendsto (fun H : ℕ => 50*((L H:ℝ)^2/2^(L H))) atTop (𝓝 0) := by
    simpa using (ratio.comp hL).const_mul 50
  apply squeeze_zero' (Eventually.of_forall fun H => by positivity) _ lim
  filter_upwards [eventually_ge_atTop 1,hL.eventually_ge_atTop 1] with H hH hl
  have hpos : (0:ℝ)<H := by exact_mod_cast (by omega : 0<H)
  have powb : 2^(L H)≤5*H := (Nat.log2_self_le (by omega : 4*H+1≠0)).trans (by omega)
  have bound : (exceptionalCoefficients H).card≤10*(L H)^2 := by
    have h := exceptional_coefficients_bound H
    change _≤(L H+1)*(2*L H+3) at h
    exact h.trans (by nlinarith [Nat.mul_le_mul hl hl, Nat.mul_le_mul_left (L H) hl])
  have br : ((exceptionalCoefficients H).card:ℝ)≤10*(L H:ℝ)^2 := by exact_mod_cast bound
  have pw : (2:ℝ)^(L H)≤5*(H:ℝ) := by exact_mod_cast powb
  rw [←mul_div_assoc,div_le_div_iff₀ hpos (by positivity)]
  have prod := mul_le_mul br pw (by positivity) (by positivity)
  nlinarith only [prod]

#print axioms possible_signed_denominator
#print axioms exceptional_coefficients_bound
#print axioms exceptional_coefficients_density_zero

end CunninghamChain.LinearRoots
