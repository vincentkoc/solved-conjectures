import ThetaIdentityHarmonics
import ThetaIdentityRow

/-! Reciprocal harmonic rows at a prescribed odd inverse residue. -/
namespace Arxiv.«2501.03234».ThetaInverseResidueRows
open Finset ThetaRowCorrelations ThetaCotangentTriangle ThetaOddHarmonicTriangle
noncomputable section

private lemma wave_abs (n d w : ℕ) : |(wave n d w:ℝ)|≤1 := by
  unfold wave reciprocalSign; split_ifs <;> norm_num

private lemma same_sign {a n d w : ℕ} (ha : Odd a) (hn : n.Coprime d)
    (he : (n:ZMod d)⁻¹=(a:ZMod d)) (hlt : w*a<d) :
    wave n d w=wave 1 d w := by
  by_cases h : d%2=1 ∧ w%2=1 ∧ w.Coprime d
  · rw [wave,wave,if_pos ⟨hn,h⟩,if_pos ⟨Nat.coprime_one_left _,h⟩,
      reciprocalSign,reciprocalSign,he,←Nat.cast_mul,ZMod.val_natCast_of_lt hlt]
    have hwp : Odd w := Nat.odd_iff.mpr h.2.1
    have hodd := Nat.odd_iff.mp (hwp.mul ha)
    have hle : w≤w*a := Nat.le_mul_of_pos_right _ ha.pos
    simp [hodd,ZMod.val_natCast_of_lt (hle.trans_lt hlt),h.2.1]
  · rw [wave,wave,if_neg (fun H => h H.2),if_neg (fun H => h H.2)]

private lemma after_period {d : ℕ} (hd : 1<d) (n K : ℕ) (hk : 2*d≤K) :
    |row d K n-row d (2*d) n|≤1 := by
  let D := 2*d
  let v (j : ℕ) : ℝ := wave n d j
  let w (i : ℕ) := ((D:ℝ)+i+1)⁻¹
  have hv (i) : ‖v i‖≤1 := wave_abs ..
  have hz : v 0=0 := by simp [v,wave]
  have hper (i) : v (2*d+i)=v i := by simp [v,wave_period]
  have hr (j : ℕ) (hj : j≤2*d) : v (2*d-j)= -v j := by dsimp [v]; exact_mod_cast wave_reflect hd n hj
  have hm : Antitone w := by
    intro i j hij; dsimp [w]; apply inv_anti₀ (by positivity); exact_mod_cast (show D+i+1≤D+j+1 by omega)
  have h := ThetaUniformWindows.weighted_prefix (fun i => v (i+1)) w ((D:ℝ)*1)
    (fun i => by dsimp [w]; positivity) hm
    (ThetaUniformWindows.period_prefix (by omega : 0<d) v hv hper (ThetaUniformWindows.reflect_period v hz hr)) (K-D)
  have he : row d K n=row d D n+∑ i∈range (K-D), w i • v (i+1) := by
    dsimp only [row]; nth_rw 1 [show K=D+(K-D) by dsimp [D]; omega]; rw [sum_range_add]
    congr 1; apply sum_congr rfl; intro i _
    rw [Nat.add_assoc,wave_period]; simp [v,w]
  change |row d K n-row d D n|≤1
  rw [he,add_sub_cancel_left,←Real.norm_eq_abs]
  apply h.trans
  dsimp [w]; rw [Nat.cast_zero,add_zero,mul_one,←div_eq_inv_mul,div_le_one (by positivity)]
  linarith

private lemma first_period {a d n : ℕ} (ha : Odd a) (hd : 1<d) (hn : n.Coprime d)
    (he : (n:ZMod d)⁻¹=(a:ZMod d)) :
    |row d (2*d) n-row d (2*d) 1|≤4*a := by
  have hdp : (0:ℝ)<d := by exact_mod_cast (show 0<d by omega)
  unfold row; rw [←sum_sub_distrib]
  apply (abs_sum_le_sum_abs ..).trans
  calc
    _ ≤ ∑ i∈range (2*d),2*(a:ℝ)/d := by
      apply sum_le_sum; intro i _
      by_cases h : (i+1)*a<d
      · rw [same_sign ha hn he h,sub_self,abs_zero]; positivity
      have hf : |(wave n d (i+1):ℝ)-(wave 1 d (i+1):ℝ)|≤2 := (abs_sub _ _).trans
        (by linarith only [wave_abs n d (i+1),wave_abs 1 d (i+1)])
      rw [←mul_sub,abs_mul,abs_of_nonneg (by positivity : 0≤((i:ℝ)+1)⁻¹)]
      have hi : 0<(i:ℝ)+1 := by positivity
      have hdiv : ((i:ℝ)+1)⁻¹≤(a:ℝ)/d := by
        rw [inv_eq_one_div,div_le_div_iff₀ hi hdp,one_mul]
        have h' : (d:ℝ)≤((i:ℝ)+1)*a := by exact_mod_cast le_of_not_gt h
        linarith only [h']
      exact (mul_le_mul hdiv hf (abs_nonneg _) (by positivity)).trans_eq (by ring)
    _ = _ := by simp only [sum_const,card_range,nsmul_eq_mul,Nat.cast_mul,Nat.cast_ofNat]; field_simp; ring

/-- Outside the primes dividing the prescribed odd inverse a, a captured
denominator loses at most 4a+3 from its identity harmonic mass, uniformly in d. -/
theorem captured_lower {a n d K : ℕ} (ha : Odd a) (hd : 1<d) (ho : Odd d) (hK : 2*d≤K)
    (hn : n.Coprime d) (he : (n:ZMod d)⁻¹=(a:ZMod d)) :
    U d-(4*a+3)≤row d K n := by
  have h := ThetaIdentityHarmonics.lower hd ho (show d≤K by omega)
  have hnK := after_period hd n K hK
  have h₁K := after_period hd 1 K hK
  have hP := first_period ha hd hn he
  linarith only [h,(abs_le.mp hnK).1,(abs_le.mp h₁K).2,(abs_le.mp hP).1]

end
end Arxiv.«2501.03234».ThetaInverseResidueRows
#print axioms Arxiv.«2501.03234».ThetaInverseResidueRows.captured_lower
