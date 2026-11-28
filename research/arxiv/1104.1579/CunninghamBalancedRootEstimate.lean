import Mathlib

/-! A two-region bound for the roots of both linear-seed Cunningham recurrences. -/

namespace CunninghamChain.LinearRoots

private lemma pow_one_add_reciprocal (D : ℕ) (hD : 0<D) :
    (1+1/(D:ℝ))^D < 3 := by
  have hd : (0:ℝ)<D := by exact_mod_cast hD
  calc (1+1/(D:ℝ))^D ≤ (Real.exp (1/D))^D := by
          apply pow_le_pow_left₀ (by positivity)
          simpa [add_comm] using Real.add_one_le_exp (1/(D:ℝ))
       _ = Real.exp 1 := by rw [←Real.exp_nat_mul]; congr 1; field_simp
       _ < 3 := Real.exp_one_lt_three

/-- For the moduli R=|z|, B=|z−1| the root equation makes R^k B strictly less
than one, with the same k=s4^s throughout the indicated interval of indices. -/
theorem balanced_root_estimate {R B p : ℝ} (hR : 0≤R) (hB : 0≤B)
    (hplus : R≤1+B) (hminus : B≤1+R) {s n : ℕ}
    (hp : 2*((4:ℝ)^s)^2 < p) (hn : n≤4*s^2*4^s)
    (hroot : p*R^n*B^2 ≤ 1+R^n) : R^(s*4^s)*B < 1 := by
  let D : ℕ := 4^s
  let K := s*D
  have hD : 0<D := by dsimp [D]; positivity
  have hd : (0:ℝ)<D := by exact_mod_cast hD
  have hsize : 2*(D:ℝ)^2 < p := by simpa [D] using hp
  have hP : 0<p := by linarith [sq_nonneg (D:ℝ)]
  change R^K*B < 1
  by_cases hin : R≤1
  · by_contra! bad
    have hu : R^K≤1 := pow_le_one₀ hR hin
    have hb1 : 1≤B := bad.trans (mul_le_of_le_one_left hB hu)
    have htwo : 1≤2*R^K := bad.trans (by nlinarith [mul_nonneg (pow_nonneg hR K) (show 0≤2-B by linarith)])
    have index : n≤K*(4*s) := by
      dsimp [K,D]
      convert hn using 1; ring
    have powid : (2:ℝ)^(4*s)=(D:ℝ)^2 := by
      dsimp [D]
      push_cast
      rw [pow_mul,←pow_mul (4:ℝ),Nat.mul_comm s 2,pow_mul]
      norm_num
    have hlo : 1≤(D:ℝ)^2*R^n := calc
      1 ≤ (2*R^K)^(4*s) := one_le_pow₀ htwo
      _ = (D:ℝ)^2*R^(K*(4*s)) := by rw [mul_pow,powid,←pow_mul]
      _ ≤ (D:ℝ)^2*R^n := mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one hR hin index) (sq_nonneg _)
    have hRn : 0<R^n := lt_of_le_of_ne (pow_nonneg hR n) (by rintro e; rw [←e,mul_zero] at hlo; linarith)
    have upper : p*R^n≤2 := calc
      p*R^n ≤ p*R^n*B^2 := le_mul_of_one_le_right (by positivity) (one_le_pow₀ hb1)
      _ ≤ 1+R^n := hroot
      _ ≤ 2 := by linarith [pow_le_one₀ hR hin (n := n)]
    nlinarith [mul_lt_mul_of_pos_right hsize hRn]
  · have hr1 : 1≤R := by linarith
    have hRn := one_le_pow₀ (n := n) hr1
    have hsmall : p*B^2≤2 := by
      apply le_of_mul_le_mul_right (a := R^n) _ (by linarith : 0<R^n)
      nlinarith only [hroot,hRn]
    have hdb : (D:ℝ)*B<1 := by
      by_contra! hb
      have hbpos : 0<B := by by_contra! e; have : B=0 := le_antisymm e hB; norm_num [this] at hb
      have large := mul_lt_mul_of_pos_right hsize (sq_pos_of_pos hbpos)
      nlinarith only [large,hsmall,one_le_pow₀ (n := 2) hb]
    have hR' : R≤1+1/D := by
      have := (lt_div_iff₀ hd).mpr (by linarith : B*(D:ℝ)<1)
      linarith
    have bound : R^D<3 := (pow_le_pow_left₀ hR hR' D).trans_lt (pow_one_add_reciprocal D hD)
    have lead : R^K≤D := by
      dsimp [K]
      rw [Nat.mul_comm s D,pow_mul]
      have h4 : R^D ≤ 4 := by linarith
      simpa [D] using pow_le_pow_left₀ (pow_nonneg hR _) h4 s
    exact (mul_le_mul_of_nonneg_right lead hB).trans_lt hdb

#print axioms balanced_root_estimate

end CunninghamChain.LinearRoots
