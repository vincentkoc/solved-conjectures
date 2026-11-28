import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Tactic

/-! Positive Fourier quadrature for uniform convolutions on small common cyclic supports. -/

open Finset Polynomial

namespace Green33RealQuadrature

/-- The roots of this mask include the first inverse powers of the step. -/
noncomputable def mask (w : ℂ) : ℕ → ℂ[X]
  | 0 => 1
  | n+1 => mask w n * (1-C (w^(n+1))*X)

private lemma twist (w : ℂ) (n : ℕ) :
    (mask w n).comp (C w*X) * (1-C w*X) =
      mask w n * (1-C (w^(n+1))*X) := by
  induction n with
  | zero => simp [mask]
  | succ n ih =>
    rw [mask, mul_comp, sub_comp, one_comp, mul_comp, C_comp, X_comp]
    rw [show C (w^(n+1))*(C w*X) = C (w^(n+2))*X by rw [← mul_assoc,← C_mul,pow_succ w (n+1)]]
    linear_combination (1-C (w^(n+2))*X)*ih

private theorem coeff_step (w : ℂ) (n j : ℕ) :
    (mask w n).coeff (j+1) * (w^(j+1)-1) =
      (mask w n).coeff j * (w^(j+1)-w^(n+1)) := by
  have h := congrArg (fun P : ℂ[X] => P.coeff (j+1)) (twist w n)
  simp only [mul_sub,mul_one,← mul_assoc,coeff_sub,coeff_mul_X,coeff_mul_C,
    comp_C_mul_X_coeff] at h
  linear_combination h

private lemma coeff_zero_mask (w : ℂ) (n : ℕ) : (mask w n).coeff 0 = 1 := by
  induction n with
  | zero => simp [mask]
  | succ n h => simp [mask,mul_sub,← mul_assoc,h]

/-- Evaluating at any of the first inverse powers kills the mask. -/
theorem mask_zero {w : ℂ} (hw : w ≠ 0) {j n : ℕ} (hj : 0<j) (hn : j ≤ n) :
    (mask w n).eval ((w^j)⁻¹) = 0 := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le hn with eq|lt
    · subst j
      simp [mask,pow_ne_zero _ hw]
    · simp [mask,ih (by omega)]


/-- Unit complex number of argument `x` radians. -/
noncomputable def phase (x : ℝ) : ℂ := Complex.exp ((x:ℂ)*Complex.I)

private lemma phase_add (x y : ℝ) : phase (x+y) = phase x * phase y := by
  simp [phase,add_mul,Complex.exp_add]

private lemma phase_pow (x : ℝ) (j : ℕ) : (phase x)^j = phase (j*x) := by
  induction j with
  | zero => simp [phase]
  | succ j ih => rw [pow_succ,ih,Nat.cast_succ,add_mul,one_mul,phase_add]

private lemma phase_subtract (x y : ℝ) :
    phase (2*x)-phase (2*y) = 2*Complex.I*phase (x+y)*(Real.sin (x-y):ℂ) := by
  have sinform (u : ℝ) : (Real.sin u:ℂ) = (phase (-u)-phase u)*Complex.I/2 := by
    simp only [Complex.ofReal_sin,Complex.sin,phase,Complex.ofReal_neg]
  rw [sinform]
  have a := (phase_add (x+y) (-(x-y))).symm
  have b := (phase_add (x+y) (x-y)).symm
  rw [show x+y+ -(x-y)=2*y by ring] at a
  rw [show x+y+(x-y)=2*x by ring] at b
  rw [← a,← b]
  linear_combination -phase (x+y)*(phase (-(x-y))-phase (x-y)) * Complex.I_mul_I

private lemma phase_zero : phase 0 = 1 := by simp [phase]
private lemma phase_ne (x : ℝ) : phase x ≠ 0 := Complex.exp_ne_zero _

private lemma sine_step (θ : ℝ) (n j : ℕ) :
    let w := phase (2*θ)
    (mask w n).coeff (j+1) * Real.sin ((j+1:ℝ)*θ) =
      (mask w n).coeff j * (-phase ((n+1:ℝ)*θ)) * Real.sin (((n+1:ℝ)-(j+1))*θ) := by
  dsimp only
  let x := (j+1:ℝ)*θ
  let y := (n+1:ℝ)*θ
  have h := coeff_step (phase (2*θ)) n j
  have wp (a : ℕ) : phase (2*θ)^(a+1) = phase (2*((a+1:ℝ)*θ)) := by
    rw [phase_pow,Nat.cast_succ]; congr 1; ring
  rw [wp,wp] at h
  change _ * (phase (2*x)-1) = _ * (phase (2*x)-phase (2*y)) at h
  have left : phase (2*x)-1 = 2*Complex.I*phase x*(Real.sin x:ℂ) := by
    simpa only [mul_zero,phase_zero,add_zero,sub_zero] using phase_subtract x 0
  have right := phase_subtract x y
  rw [show x-y= -(y-x) by ring,Real.sin_neg,Complex.ofReal_neg,phase_add] at right
  rw [left,right] at h
  rw [sub_mul]
  change _ * (Real.sin x:ℂ) = _ * (-phase y) * (Real.sin (y-x):ℂ)
  apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero (by norm_num : (2:ℂ) ≠ 0) Complex.I_ne_zero) (phase_ne x))
  linear_combination h

/-- The mask coefficients have a common phase increment and strictly positive
radial factors when all the first angles lie between zero and pi. -/
private theorem sector_coeff (θ : ℝ) (n : ℕ) (pos : 0 < θ) (last : n*θ < Real.pi)
    (j : ℕ) (hj : j ≤ n) :
    ∃ s : ℝ, 0 < s ∧ (mask (phase (2*θ)) n).coeff j = s * (-phase ((n+1:ℝ)*θ))^j := by
  induction j with
  | zero => exact ⟨1,by norm_num,by simp [coeff_zero_mask]⟩
  | succ j ih =>
    obtain ⟨s,hs,eq⟩ := ih (by omega)
    let a := (j+1:ℝ)*θ
    let b := ((n+1:ℝ)-(j+1))*θ
    have hj' : (j+1:ℝ) ≤ n := by exact_mod_cast hj
    have ja : 0 < a := by dsimp [a]; positivity
    have jb : 0 < b := mul_pos (by linarith) pos
    have sa := Real.sin_pos_of_pos_of_lt_pi ja (lt_of_le_of_lt (mul_le_mul_of_nonneg_right hj' pos.le) last)
    have sb := Real.sin_pos_of_pos_of_lt_pi jb (lt_of_le_of_lt (mul_le_mul_of_nonneg_right (by
      linarith [Nat.cast_nonneg (α:=ℝ) j]) pos.le) last)
    refine ⟨s * Real.sin b / Real.sin a, div_pos (mul_pos hs sb) sa, ?_⟩
    have h := sine_step θ n j
    dsimp only at h
    change _ * (Real.sin a:ℂ) = _ * _ * (Real.sin b:ℂ) at h
    rw [eq] at h
    simp only [Complex.ofReal_div,Complex.ofReal_mul]
    rw [div_mul_eq_mul_div,eq_div_iff (show (Real.sin a:ℂ) ≠ 0 by exact_mod_cast sa.ne'),pow_succ]
    linear_combination h

private lemma phase_conj (x : ℝ) : (starRingEnd ℂ) (phase x) = phase (-x) := by
  simp [phase,← Complex.exp_conj]

private lemma phase_turn (x : ℝ) : -phase x = phase (x-Real.pi) := by
  rw [sub_eq_add_neg,phase_add]
  have e : phase (-Real.pi) = -1 := by
    rw [← phase_conj]
    simp [phase,Complex.exp_pi_mul_I]
  rw [e,mul_neg_one]

/-- Each pair of coefficients gives a positive real weight. This permits
placing the weights at sums of the two coefficient indices. -/
theorem positive_pair (θ : ℝ) (n : ℕ) (pos : 0 < θ) (last : n*θ < Real.pi)
    (narrow : n*|((n+1:ℝ)*θ)-Real.pi| < Real.pi/2)
    {j k : ℕ} (hj : j ≤ n) (hk : k ≤ n) :
    0 < ((mask (phase (2*θ)) n).coeff j *
      (starRingEnd ℂ) ((mask (phase (2*θ)) n).coeff k)).re := by
  obtain ⟨s,hs,ej⟩ := sector_coeff θ n pos last j hj
  obtain ⟨v,hv,ek⟩ := sector_coeff θ n pos last k hk
  let δ := (n+1:ℝ)*θ-Real.pi
  rw [ej,ek,phase_turn,phase_pow,phase_pow,map_mul,Complex.conj_ofReal,phase_conj]
  change 0 < ((s:ℂ) * phase (j*δ) * ((v:ℂ)*phase (-(k*δ)))).re
  rw [show (s:ℂ)*phase (j*δ)*((v:ℂ)*phase (-(k*δ))) =
    ((s*v:ℝ):ℂ)*phase (j*δ+ -(k*δ)) by rw [phase_add,Complex.ofReal_mul];ring]
  rw [Complex.ofReal_mul']
  simp only [phase,Complex.exp_ofReal_mul_I_re]
  apply mul_pos (mul_pos hs hv)
  apply Real.cos_pos_of_mem_Ioo
  apply abs_lt.mp
  rw [show (j:ℝ)*δ+ -(k*δ) = (j-k:ℝ)*δ by ring,abs_mul]
  apply lt_of_le_of_lt _ narrow
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  have jn : (j:ℝ) ≤ n := by exact_mod_cast hj
  have kn : (k:ℝ) ≤ n := by exact_mod_cast hk
  exact abs_le.mpr ⟨by linarith [Nat.cast_nonneg (α:=ℝ) j],by linarith [Nat.cast_nonneg (α:=ℝ) k]⟩

private lemma mask_degree (w : ℂ) (n : ℕ) : (mask w n).natDegree ≤ n := by
  induction n with
  | zero => simp [mask]
  | succ n ih =>
    rw [mask]
    apply natDegree_mul_le.trans
    apply Nat.add_le_add ih
    exact (natDegree_sub_le _ _).trans (max_le (by simp) (by
      apply natDegree_mul_le.trans
      simp))

private theorem pair_eval (P : ℂ[X]) {n : ℕ} (hn : P.natDegree < n) (x : ℂ) :
    ∑ j ∈ range n, ∑ k ∈ range n,
        (((P.coeff j * (starRingEnd ℂ) (P.coeff k)).re : ℂ) * x^(j+k)) =
      P.eval x * (starRingEnd ℂ) (P.eval ((starRingEnd ℂ) x)) := by
  let c := P.coeff
  have raw : ∑ j ∈ range n, ∑ k ∈ range n,
      (c j * (starRingEnd ℂ) (c k)) * x^(j+k) =
      P.eval x * (starRingEnd ℂ) (P.eval ((starRingEnd ℂ) x)) := by
    rw [eval_eq_sum_range' hn x,eval_eq_sum_range' hn ((starRingEnd ℂ) x)]
    simp only [map_sum,map_mul,map_pow,RingHomCompTriple.comp_apply]
    rw [sum_mul]
    simp only [mul_sum,pow_add]
    apply sum_congr rfl; intro i _
    apply sum_congr rfl; intro k _
    dsimp [c]; ring
  let f (j k : ℕ) := (c j*(starRingEnd ℂ) (c k))*x^(j+k)
  have pair (j k : ℕ) : ((c j*(starRingEnd ℂ) (c k)).re:ℂ)*x^(j+k) =
      (f j k+f k j)/2 := by
    rw [Complex.re_eq_add_conj,map_mul,Complex.conj_conj]
    simp only [f,add_comm k j]
    ring
  change ∑ j ∈ range n, ∑ k ∈ range n, ((c j*(starRingEnd ℂ) (c k)).re:ℂ)*x^(j+k) = _
  rw [← raw]
  simp only [pair,← sum_div,sum_add_distrib]
  rw [Finset.sum_comm (f:=fun j k => f k j)]
  change ((∑ j ∈ range n, ∑ k ∈ range n, f j k)+(∑ j ∈ range n, ∑ k ∈ range n, f j k))/2 = _
  exact add_self_div_two _

/-- The real pair weights annihilate the first positive Fourier modes. -/
theorem quadrature_zero (θ : ℝ) (n : ℕ) {h : ℕ} (hh : 0<h) (hn : h ≤ n) :
    let w := phase (2*θ)
    let P := mask w n
    ∑ j ∈ range (n+1), ∑ k ∈ range (n+1),
      ((P.coeff j*(starRingEnd ℂ) (P.coeff k)).re:ℂ) * (w^h)^(j+k) = 0 := by
  dsimp only
  rw [pair_eval _ (Nat.lt_succ_of_le (mask_degree _ _))]
  have hc (z : ℝ) : (starRingEnd ℂ) (phase z) = (phase z)⁻¹ := by
    rw [phase_conj]
    simp [phase,Complex.exp_neg]
  rw [map_pow,hc,inv_pow,mask_zero (phase_ne _) hh hn,map_zero,mul_zero]

/-- On orders one away from a multiple of four, positive weights on the
cyclic indices `4(j+k)` annihilate every frequency from one through `n`. -/
theorem near_four_quadrature (p n : ℕ) (order : p+1=4*(n+1) ∨ p=4*(n+1)+1) :
    ∃ W : ℕ → ℕ → ℝ, (∀ j ≤ n, ∀ k ≤ n, 0 < W j k) ∧
      ∀ h : ℕ, 0<h → h ≤ n →
        ∑ j ∈ range (n+1), ∑ k ∈ range (n+1),
          (W j k:ℂ)*phase (2*Real.pi*(h:ℝ)*(4*(j+k:ℕ):ℕ)/p) = 0 := by
  let θ := 4*Real.pi/(p:ℝ)
  let P := mask (phase (2*θ)) n
  have hp : (0:ℝ)<p := by exact_mod_cast (show 0<p by omega)
  have pos : 0 < θ := by dsimp [θ]; positivity
  have np : (4:ℝ)*n < p := by exact_mod_cast (show 4*n<p by omega)
  have last : n*θ < Real.pi := by
    dsimp [θ]
    rw [← mul_div_assoc,div_lt_iff₀ hp]
    nlinarith [mul_pos (sub_pos.mpr np) Real.pi_pos]
  have narrow : n*|((n+1:ℝ)*θ)-Real.pi| < Real.pi/2 := by
    have eye : |((n+1:ℝ)*θ)-Real.pi| = Real.pi/(p:ℝ) := by
      rcases order with h|h
      · have e : (p:ℝ)+1=4*((n:ℝ)+1) := by exact_mod_cast h
        have H : ((n+1:ℝ)*θ)-Real.pi=Real.pi/(p:ℝ) := by
          dsimp [θ]; field_simp; nlinarith [congrArg (fun a:ℝ => a*Real.pi) e]
        rw [H,abs_of_pos (by positivity)]
      · have e : (p:ℝ)=4*((n:ℝ)+1)+1 := by exact_mod_cast h
        have H : ((n+1:ℝ)*θ)-Real.pi= -(Real.pi/(p:ℝ)) := by
          dsimp [θ]; field_simp; nlinarith [congrArg (fun a:ℝ => a*Real.pi) e]
        rw [H,abs_neg,abs_of_pos (by positivity)]
    rw [eye,← mul_div_assoc,div_lt_iff₀ hp]
    nlinarith [mul_pos (sub_pos.mpr np) Real.pi_pos,mul_nonneg (Nat.cast_nonneg (α:=ℝ) n) Real.pi_pos.le]
  refine ⟨fun j k => (P.coeff j*(starRingEnd ℂ) (P.coeff k)).re,
    fun j hj k hk => positive_pair θ n pos last narrow hj hk,?_⟩
  intro h hh hn
  have freq (j k : ℕ) : (phase (2*θ)^h)^(j+k) =
      phase (2*Real.pi*(h:ℝ)*(4*(j+k:ℕ):ℕ)/p) := by
    rw [phase_pow,phase_pow]
    dsimp [θ]
    push_cast
    congr 1; ring
  simpa only [P,freq] using quadrature_zero θ n hh hn

/-- The omitted sites consist of disjoint adjacent pairs. The positive
quadrature stays outside them, including where an index winds past the order. -/
theorem adjacent_gaps (p n : ℕ) [NeZero p]
    (order : p+1=4*(n+1) ∨ p=4*(n+1)+1) :
    ∃ a : Fin n → ZMod p, Function.Injective (fun ij : Fin n × Fin 2 => a ij.1+ij.2.val) ∧
      ∀ j ≤ n, ∀ k ≤ n, ∀ i : Fin n, ∀ b : Fin 2, (4*(j+k):ℕ) ≠ a i+b.val := by
  let off := if p=4*(n+1)+1 then 1 else 2
  have off_choice : (p=4*(n+1)+1 ∧ off=1) ∨ (p+1=4*(n+1) ∧ off=2) := by
    dsimp only [off]
    split_ifs with h
    · exact Or.inl ⟨h,rfl⟩
    · exact Or.inr ⟨order.resolve_right h,rfl⟩
  let a (i : Fin n) := ((4*i.val+off:ℕ):ZMod p)
  have eq (i : Fin n) (b : Fin 2) : (a i+b.val).val=4*i.val+off+b.val := by
    change (((4*i.val+off:ℕ):ZMod p)+b.val).val=_
    rw [← Nat.cast_add,ZMod.val_natCast_of_lt]
    rcases off_choice with ⟨_,_⟩|⟨_,_⟩ <;> omega
  refine ⟨a,?_,?_⟩
  · rintro ⟨i,b⟩ ⟨i',b'⟩ e
    have h := congrArg ZMod.val e
    change (a i+b.val).val=(a i'+b'.val).val at h
    rw [eq,eq] at h
    apply Prod.ext <;> apply Fin.ext <;> dsimp only <;> omega
  · intro j hj k hk i b e
    have h := congrArg ZMod.val e
    rw [eq,ZMod.val_natCast] at h
    by_cases small : 4*(j+k)<p
    · rw [Nat.mod_eq_of_lt small] at h
      rcases off_choice with ⟨_,_⟩|⟨_,_⟩ <;> omega
    · have red : 4*(j+k)%p=4*(j+k)-p := by
        rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega)]
      rw [red] at h
      rcases off_choice with ⟨_,_⟩|⟨_,_⟩ <;> omega

section Second
variable {p : ℕ} [NeZero p]

private noncomputable abbrev χ : ZMod p → ℂ := ZMod.stdAddChar

private lemma chi_val (x : ZMod p) : χ x = phase (2*Real.pi*x.val/p) := by
  rw [χ,ZMod.stdAddChar_apply,ZMod.toCircle_apply]
  dsimp [phase]; push_cast; congr 1; ring

private lemma chi_nat (j : ℕ) : χ (j : ZMod p) = phase (2*Real.pi*j/p) := by
  rw [χ,ZMod.stdAddChar_apply,ZMod.toCircle_natCast]
  dsimp [phase]; push_cast; congr 1; ring

private lemma chi_ne (x : ZMod p) : χ x ≠ 0 := by rw [chi_val]; exact phase_ne _

private lemma chi_sub (x a : ZMod p) : χ (x-a) = χ x/χ a := by
  rw [eq_div_iff (chi_ne _),χ,← AddChar.map_add_eq_mul,sub_add_cancel]

private lemma conj_phase_inv (x : ℝ) : (starRingEnd ℂ) (phase x) = (phase x)⁻¹ := by
  rw [phase_conj]; simp [phase,Complex.exp_neg]

private noncomputable def notch (y : ZMod p) : ℝ :=
  2*Real.sin (Real.pi*y.val/p)*Real.sin (Real.pi*(y.val-1:ℝ)/p)

private lemma notch_nonneg (y : ZMod p) : 0 ≤ notch y := by
  have hp : (0:ℝ)<p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  by_cases z : y.val=0
  · simp [notch,z]
  have yp : (1:ℝ) ≤ y.val := by exact_mod_cast (show 1 ≤ y.val by omega)
  have lt : (y.val:ℝ)<p := by exact_mod_cast y.val_lt
  have s (d : ℝ) (h : 0 ≤ d) (l : d ≤ p) : 0 ≤ Real.sin (Real.pi*d/p) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) ((div_le_iff₀ hp).mpr
      (mul_le_mul_of_nonneg_left l Real.pi_pos.le))
  exact mul_nonneg (mul_nonneg (by norm_num) (s _ (by positivity) lt.le)) (s _ (by linarith) (by linarith))

private lemma notch_pos (y : ZMod p) (ne0 : y ≠ 0) (ne1 : y ≠ 1) : 0 < notch y := by
  have hp : (0:ℝ)<p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have val : 1 < y.val := by
    by_contra! le
    have e : y.val=0 ∨ y.val=1 := by omega
    rcases e with e|e
    · exact ne0 (by simpa [e] using (ZMod.natCast_zmod_val y).symm)
    · exact ne1 (by simpa [e] using (ZMod.natCast_zmod_val y).symm)
  have yp : (1:ℝ)<y.val := by exact_mod_cast val
  have lt : (y.val:ℝ)<p := by exact_mod_cast y.val_lt
  have s (d : ℝ) (h : 0 < d) (l : d < p) : 0 < Real.sin (Real.pi*d/p) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) ((div_lt_iff₀ hp).mpr
      (mul_lt_mul_of_pos_left l Real.pi_pos))
  exact mul_pos (mul_pos (by norm_num) (s _ (by positivity) lt)) (s _ (by linarith) (by linarith))

omit [NeZero p] in
private lemma notch_zeros (hp : 1<p) : notch (0:ZMod p)=0 ∧ notch (1:ZMod p)=0 := by
  have one : (1:ZMod p).val=1 := by simpa using ZMod.val_natCast_of_lt hp
  simp [notch,one]

omit [NeZero p] in
private lemma notch_cos (y : ZMod p) : notch y =
    Real.cos (Real.pi/p)-Real.cos (2*Real.pi*y.val/p-Real.pi/p) := by
  rw [notch,Real.two_mul_sin_mul_sin]
  congr 2 <;> ring

private noncomputable def notchPoly (a : ZMod p) : ℂ[X] :=
  let h := phase (-(Real.pi/p))/χ a
  C (-h/2)*X^2 + C (Real.cos (Real.pi/p):ℂ)*X - C (h⁻¹/2)

private lemma notch_eval (a x : ZMod p) :
    (notch (x-a):ℂ)*χ x = (notchPoly a).eval (χ x) := by
  let h := phase (-(Real.pi/p))/χ a
  let u := 2*Real.pi*(x-a).val/p-Real.pi/p
  have phase_eq : phase u = h*χ x := by
    dsimp [u,h]
    rw [sub_eq_add_neg,phase_add,← chi_val,chi_sub]
    ring
  have hne : h ≠ 0 := div_ne_zero (phase_ne _) (chi_ne _)
  have co : (Real.cos u:ℂ) = (h*χ x+(h*χ x)⁻¹)/2 := by
    rw [← phase_eq,← conj_phase_inv,← Complex.re_eq_add_conj]
    simp [phase,Complex.exp_ofReal_mul_I_re]
  rw [notch_cos,Complex.ofReal_sub,co]
  change _ = (C (-h/2)*X^2+C (Real.cos (Real.pi/p):ℂ)*X-C (h⁻¹/2)).eval _
  simp only [eval_sub,eval_add,eval_mul,eval_C,eval_X,eval_pow]
  field_simp [hne,chi_ne x]
  ring

private lemma notch_degree (a : ZMod p) : (notchPoly a).natDegree ≤ 2 := by
  apply natDegree_sub_le_of_le (m:=2) (n:=2) _ _ <;> try simp
  apply natDegree_add_le_of_le (m:=2) (n:=2) _ _ <;>
    exact natDegree_mul_le.trans (by simp)

private lemma mask_second {n : ℕ} (a : Fin n → ZMod p) :
    ∃ P : ℂ[X], P.natDegree ≤ 2*n ∧ ∀ x : ZMod p,
      ((∏ i, notch (x-a i):ℝ):ℂ)*χ x^n = P.eval (χ x) := by
  refine ⟨∏ i, notchPoly (a i),?_,?_⟩
  · calc
      _ ≤ ∑ i, (notchPoly (a i)).natDegree := natDegree_prod_le _ _
      _ ≤ ∑ _i : Fin n, 2 := sum_le_sum fun i _ => notch_degree _
      _ = _ := by simp [mul_comm]
  · intro x
    rw [eval_prod]
    simp only [← notch_eval,prod_mul_distrib,Complex.ofReal_prod,prod_const,card_univ,Fintype.card_fin]

private lemma chi_conj (x : ZMod p) : (starRingEnd ℂ) (χ x) = (χ x)⁻¹ := by
  rw [chi_val,conj_phase_inv]

private lemma annihilate_signed {α : Type*} [Fintype α] (b : α → ZMod p) (W : α → ℝ)
    {n : ℕ} (zero : ∀ h : ℕ, 0<h → h ≤ n → ∑ i, (W i:ℂ)*χ (b i)^h = 0)
    {e : ℤ} (he : e ≠ 0) (le : e.natAbs ≤ n) : ∑ i, (W i:ℂ)*χ (b i)^e = 0 := by
  cases e with
  | ofNat j => exact zero j (Nat.pos_of_ne_zero fun t => he (by simp [t])) le
  | negSucc j =>
    have h := congrArg (starRingEnd ℂ) (zero (j+1) (by omega) le)
    simpa only [map_sum,map_mul,map_pow,Complex.conj_ofReal,chi_conj,inv_pow,
      zpow_negSucc,map_zero] using h

private lemma filtered {α : Type*} [Fintype α] (b : α → ZMod p) (W : α → ℝ)
    {n : ℕ} (zero : ∀ h : ℕ, 0<h → h ≤ n → ∑ i, (W i:ℂ)*χ (b i)^h = 0)
    (g : ZMod p → ℝ) (P : ℂ[X]) (deg : P.natDegree ≤ 2*n)
    (eval : ∀ x : ZMod p, (g x:ℂ)*χ x^n = P.eval (χ x)) (x : ZMod p) :
    ∑ j, (W j:ℂ)*g (x-b j) = P.coeff n*∑ j, (W j:ℂ) := by
  have expand (j) : (g (x-b j):ℂ) = ∑ i ∈ range (2*n+1),
      P.coeff i*χ x^(i-n:ℤ)*χ (b j)^(n-i:ℤ) := by
    have eg := (eq_div_iff (pow_ne_zero n (chi_ne (x-b j)))).mpr (eval (x-b j))
    rw [eg,eval_eq_sum_range' (Nat.lt_succ_of_le deg),sum_div]
    apply sum_congr rfl
    intro i _
    rw [mul_div_assoc,← zpow_natCast,← zpow_natCast (χ (x-b j)) n,
      ← zpow_sub₀ (chi_ne _),chi_sub,div_zpow,show (n:ℤ)-i = -((i:ℤ)-n) by ring,
      zpow_neg]
    ring
  calc
    _ = ∑ j, ∑ i ∈ range (2*n+1), (P.coeff i*χ x^(i-n:ℤ))*((W j:ℂ)*χ (b j)^(n-i:ℤ)) := by
      simp only [expand,mul_sum]
      apply sum_congr rfl; intro j _
      apply sum_congr rfl; intro i _
      ring
    _ = ∑ i ∈ range (2*n+1), (P.coeff i*χ x^(i-n:ℤ))*(∑ j, (W j:ℂ)*χ (b j)^(n-i:ℤ)) := by
      rw [sum_comm]; simp only [mul_sum]
    _ = _ := by
      rw [sum_eq_single n]
      · simp
      · intro i hi ine
        have hi' := mem_range.mp hi
        rw [annihilate_signed b W zero (e := (n:ℤ)-i) (by omega) (by omega),mul_zero]
      · intro h; exact (h (mem_range.mpr (by omega))).elim

/-- Positive quadrature and a nonnegative partner have constant convolution on an
odd cycle while omitting two common labels per cancelled positive mode. -/
theorem positive_constant_convolution (n : ℕ) (order : p+1=4*(n+1) ∨ p=4*(n+1)+1) :
    ∃ (A : Finset (ZMod p)) (b : Fin (n+1) × Fin (n+1) → A)
      (W : Fin (n+1) × Fin (n+1) → ℝ) (g : ZMod p → ℝ),
      A.card+2*n=p ∧ (∀ i, 0<W i) ∧ (∀ x, 0 ≤ g x) ∧
      (∀ x ∈ A, 0 < g x) ∧ (∀ x ∉ A, g x=0) ∧ ∀ z : ZMod p,
        ∑ i, W i*g (z-(b i:ZMod p)) = ∑ i, W i*g (0-(b i:ZMod p)) := by
  classical
  obtain ⟨a,inj,gaps⟩ := adjacent_gaps p n order
  obtain ⟨w,wp,freq⟩ := near_four_quadrature p n order
  let holes := (univ : Finset (Fin n × Fin 2)).image (fun ij => a ij.1+ij.2.val)
  let A := holesᶜ
  let b₀ (i : Fin (n+1) × Fin (n+1)) := ((4*(i.1.val+i.2.val):ℕ):ZMod p)
  have good (i) : b₀ i ∈ A := by
    apply mem_compl.mpr
    rintro h
    obtain ⟨⟨j,k⟩,_,e⟩ := mem_image.mp h
    exact gaps _ (by omega : i.1.val ≤ n) _ (by omega : i.2.val ≤ n) j k e.symm
  let b (i) : A := ⟨b₀ i,good i⟩
  let W (i : Fin (n+1) × Fin (n+1)) := w i.1 i.2
  let g (x : ZMod p) := ∏ i, notch (x-a i)
  refine ⟨A,b,W,g,?_,fun i => wp _ (by omega) _ (by omega),fun x => prod_nonneg (fun i _ => notch_nonneg _),?_,?_,?_⟩
  · have hc : holes.card=n*2 := by simp [holes,card_image_of_injective _ inj]
    have both := card_compl_add_card holes
    simpa only [A,hc,ZMod.card,mul_comm n 2] using both
  · intro x hx
    apply prod_pos
    intro i _
    apply notch_pos
    · intro e
      apply (mem_compl.mp hx)
      exact mem_image.mpr ⟨(i,0),mem_univ _,by simpa using (sub_eq_zero.mp e).symm⟩
    · intro e
      apply (mem_compl.mp hx)
      exact mem_image.mpr ⟨(i,1),mem_univ _,by simpa [add_comm] using (sub_eq_iff_eq_add.mp e).symm⟩
  · intro x hx
    have h : x ∈ holes := by simpa [A] using hx
    obtain ⟨⟨i,k⟩,_,rfl⟩ := mem_image.mp h
    apply prod_eq_zero (mem_univ i)
    have z := notch_zeros (p:=p) (by omega : 1<p)
    fin_cases k <;> simpa using (by first | exact z.1 | exact z.2)
  · intro z
    obtain ⟨P,deg,repr⟩ := mask_second a
    have zero (h : ℕ) (hp : 0<h) (le : h ≤ n) :
        ∑ i, (W i:ℂ)*χ (b₀ i)^h=0 := by
      have f (j k : ℕ) : χ ((4*(j+k):ℕ):ZMod p)^h =
          phase (2*Real.pi*(h:ℝ)*(4*(j+k:ℕ):ℕ)/p) := by
        rw [chi_nat,phase_pow]
        congr 1; ring
      rw [Fintype.sum_prod_type]
      simpa only [W,b₀,f,← Fin.sum_univ_eq_sum_range] using (freq h hp le)
    apply Complex.ofReal_injective
    push_cast
    exact (filtered b₀ W zero g P deg repr z).trans (filtered b₀ W zero g P deg repr 0).symm

end Second

#print axioms mask_zero
#print axioms positive_pair
#print axioms quadrature_zero
#print axioms near_four_quadrature
#print axioms adjacent_gaps
#print axioms positive_constant_convolution
end Green33RealQuadrature
