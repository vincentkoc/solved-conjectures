import ThetaRationalRows
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-! Sampling the parity correlation in a window of canonical Hardy rows. -/

namespace Arxiv.«2501.03234».ThetaThirdWindow

open Finset

private noncomputable def boundary (p M t : ℕ) : ℕ := ⌈((t:ℝ)*p)/M⌉₊

private lemma boundary_le {p M t x : ℕ} (hM : 0<M) :
    boundary p M t ≤ x ↔ t*p ≤ M*x := by
  unfold boundary
  rw [Nat.ceil_le, div_le_iff₀ (by exact_mod_cast hM : (0:ℝ)<M), mul_comm (x:ℝ)]
  norm_cast

private lemma bin_eq {p M t : ℕ} (hp : 0<p) (hM : 0<M) (ht : t<M) :
    (range p).filter (fun x => M*x/p=t) = Ico (boundary p M t) (boundary p M (t+1)) := by
  ext x
  simp only [mem_filter, mem_range, mem_Ico, boundary_le hM,
    show x < boundary p M (t+1) ↔ M*x < (t+1)*p by
      rw [lt_iff_not_ge, boundary_le hM, not_le]]
  constructor
  · rintro ⟨_, he⟩
    exact ⟨(Nat.le_div_iff_mul_le hp).mp he.ge,(Nat.div_lt_iff_lt_mul hp).mp (by omega)⟩
  · rintro ⟨hl,hh⟩
    refine ⟨?_, Nat.div_eq_of_lt_le hl hh⟩
    have hm := Nat.mul_le_mul_right p (show t+1≤M by omega)
    exact (Nat.mul_lt_mul_left hM).mp (hh.trans_le hm)

private lemma bin_error {p M t : ℕ} (hp : 0<p) (hM : 0<M) (ht : t<M) :
    |(((range p).filter (fun x => M*x/p=t)).card : ℝ) - (p:ℝ)/M| ≤ 1 := by
  let c (i : ℕ) : ℝ := i*(p:ℝ)/M
  have hm (i : ℕ) : c i ≤ (boundary p M i : ℝ) := Nat.le_ceil _
  have hn (i : ℕ) : (boundary p M i : ℝ) < c i + 1 := Nat.ceil_lt_add_one (by positivity)
  have hadd : c (t+1) = c t + (p:ℝ)/M := by simp only [c,Nat.cast_add,Nat.cast_one]; ring
  have hmon : boundary p M t ≤ boundary p M (t+1) := by
    apply Nat.ceil_mono
    change c t ≤ c (t+1)
    rw [hadd]; exact le_add_of_nonneg_right (by positivity)
  rw [bin_eq hp hM ht, Nat.card_Ico, Nat.cast_sub hmon, abs_le]
  constructor <;> linarith [hm t, hn t, hm (t+1), hn (t+1)]

/-- The equal-bin rule for a bounded test function on the p-point grid has error at most M. -/
theorem sample_error {p M : ℕ} (hp : 0<p) (hM : 0<M) (f : ℕ → ℝ)
    (hf : ∀ t<M, |f t| ≤ 1) :
    |(∑ x ∈ range p, f (M*x/p)) - (p:ℝ)/M*(∑ t ∈ range M, f t)| ≤ M := by
  have hmap (x : ℕ) (hx : x∈range p) : M*x/p ∈ range M :=
    mem_range.mpr ((Nat.div_lt_iff_lt_mul hp).mpr (Nat.mul_lt_mul_of_pos_left (mem_range.mp hx) hM))
  have he := sum_fiberwise_of_maps_to' hmap f
  rw [← he, mul_sum, ← sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ t ∈ range M, (1:ℝ) := by
      apply sum_le_sum; intro t ht
      simp only [sum_const, nsmul_eq_mul, ← sub_mul, abs_mul]
      exact (mul_le_mul (bin_error hp hM (mem_range.mp ht)) (hf t (mem_range.mp ht))
        (abs_nonneg _) (by norm_num)).trans (by norm_num)
    _ = _ := by simp

open ThetaDiagonal (U oddReps rep)
open ThetaRationalRows (row)

variable {p : ℕ} [Fact p.Prime]

/-- A pointwise Hardy row estimate from sampling the two parity waves. -/
theorem row_ratio_error {u v : ℕ} (hu : u%2=1) (hv : v%2=1) (hc : u.Coprime v)
    (hp : p%2=1) (a b : U p) (ha : (a : ZMod p)=u) (hb : (b : ZMod p)=v) :
    |(row (a/b) : ℝ) - (p:ℝ)/(u*v)| ≤ u*v+1 := by
  have hu0 : 0<u := by omega
  have hv0 : 0<v := by omega
  let f (t : ℕ) : ℝ := (-1 : ℝ)^(t/v+t/u)
  have hf (t : ℕ) (_ : t<u*v) : |f t| ≤ 1 := by simp [f,abs_pow]
  have hgrid : ∑ t ∈ range (u*v), f t = 1 := by
    dsimp [f]; exact_mod_cast ThetaRationalRows.parity_grid_sum hu hv hc
  have hs := sample_error (p := p) (Fact.out : p.Prime).pos (mul_pos hu0 hv0) f hf
  have hx (x : ℕ) : f (u*v*x/p) = (-1 : ℝ)^(u*x/p+v*x/p) := by
    dsimp [f]; rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul,
      show u*v*x=v*(u*x) by ring, mul_comm p v, Nat.mul_div_mul_left _ _ hv0,
      show v*(u*x)=u*(v*x) by ring, mul_comm p u, Nat.mul_div_mul_left _ _ hu0]
  have hrow : (∑ x ∈ range p, f (u*v*x/p)) = (row (a/b) : ℝ)+1 := by
    rw [ThetaRationalRows.row_ratio_floor_sum hu hv hp a b ha hb]
    push_cast
    conv_lhs => rw [show p = (p-1)+1 from (Nat.sub_add_cancel (Fact.out : p.Prime).one_le).symm, sum_range_succ']
    simp only [Nat.sub_add_cancel (Fact.out : p.Prime).one_le, hx, Nat.mul_zero, Nat.zero_div,
      show f 0 = 1 by simp [f]]
  rw [hrow,hgrid,mul_one,Nat.cast_mul] at hs
  rw [abs_le] at hs ⊢
  constructor <;> linarith

private def unitOfIndex (n : ℕ) (hn : 0<n) (hl : n<p) : U p :=
  Units.mk0 _ (show (n : ZMod p) ≠ 0 by
    intro h; have he := congrArg ZMod.val h
    rw [ZMod.val_natCast_of_lt hl,ZMod.val_zero] at he; omega)

private lemma reflected_row_error {a v : ℕ} {s : ℤ} (hp : p%2=1) (hp3 : 3<p)
    (ha : a%2=1) (hal : a<p) (hv : v%2=1) (hvl : v<p) (hc : v.Coprime 3)
    (hs : s=1 ∨ s= -1) (he : 3*(a:ℤ) = 2*p+s*v) :
    |(S' (p-a) p : ℝ) - (s : ℝ)*p/(3*v)| ≤ 3*v+1 := by
  let A := unitOfIndex a (by omega) hal
  let V := unitOfIndex v (by omega) hvl
  let D := unitOfIndex 3 (by decide) hp3
  have hA : rep A = a := ZMod.val_natCast_of_lt hal
  have hS : S' (p-a) p = row A := by
    rw [ThetaRationalRows.row_eq_S' hp (a := A) (mem_filter.mpr ⟨mem_univ _,hA ▸ ha⟩), hA]
  have hR := row_ratio_error hv (by decide : 3%2=1) hc hp V D rfl rfl
  rw [hS]; norm_num at hR
  have hz := congrArg (fun z : ℤ => (z : ZMod p)) he
  push_cast at hz
  rw [ZMod.natCast_self,mul_zero,zero_add] at hz
  rcases hs with rfl|rfl
  · have hh : A = V/D := (eq_div_iff_mul_eq').mpr (Units.ext (by
      change (a : ZMod p)*3=v; simpa [mul_comm] using hz))
    rw [hh]; simpa [mul_comm] using hR
  · have hh : -A = V/D := (eq_div_iff_mul_eq').mpr (Units.ext (by
      change -(a : ZMod p)*3=v; push_cast at hz; linear_combination -hz))
    rw [← hh, ThetaRationalRows.row_neg hp, Int.cast_neg] at hR
    rw [abs_le] at hR ⊢; push_cast; rw [mul_comm (3 : ℝ), neg_one_mul, neg_div]
    constructor <;> linarith

/-- Odd reflected indices in the symmetric interval |3a−2p| < 6L. -/
def window (p L : ℕ) : Finset ℕ :=
  (Ico 1 p).filter fun a => a%2=1 ∧ 2*p < 3*a+6*L ∧ 3*a < 2*p+6*L

/-- Signed sum of the original even-numerator rows in the interval about p/3. -/
def windowSum (p L : ℕ) : ℤ := ∑ a ∈ window p L, S' (p-a) p

private def above (p k : ℕ) := 2*((p+1)/3)+1+2*k
private def below (p k : ℕ) := 2*((p+1)/3)-1-2*k

private lemma residue_class (hp : 3<p) : p%6=1 ∨ p%6=5 := by
  have h₁ := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have h₂ : ¬3 ∣ p := fun h => ((Nat.dvd_prime (Fact.out : p.Prime)).mp h).elim (by omega) (by omega)
  rw [Nat.odd_iff] at h₁
  have : p%3≠0 := fun h => h₂ (Nat.dvd_of_mod_eq_zero h)
  omega

omit [Fact p.Prime] in
private lemma interval_decomposition {L : ℕ} (hg : 6*L+3<p) (_hc : p%6=1 ∨ p%6=5) :
    window p L = (range L).image (above p) ∪ (range L).image (below p) := by
  ext a
  simp only [window, mem_filter, mem_Ico, mem_union, mem_image, mem_range, above, below]
  constructor
  · rintro ⟨⟨ha,hap⟩,ho,h₁,h₂⟩
    by_cases ht : 2*((p+1)/3)<a
    · left; exact ⟨(a-2*((p+1)/3)-1)/2, by omega, by omega⟩
    · right; exact ⟨(2*((p+1)/3)-1-a)/2, by omega, by omega⟩
  · rintro (⟨k,hk,rfl⟩|⟨k,hk,rfl⟩) <;> omega

omit [Fact p.Prime] in
private lemma sum_window_map {L : ℕ} (hg : 6*L+3<p) (hc : p%6=1 ∨ p%6=5) (g : ℕ → ℤ) :
    ∑ a ∈ window p L, g a = ∑ k ∈ range L, (g (above p k) + g (below p k)) := by
  have hi : Set.InjOn (above p) (range L) := by
    intro i _ j _ h; dsimp only [above] at h; omega
  have hj : Set.InjOn (below p) (range L) := by
    intro i hi j hj h
    have := mem_range.mp hi; have := mem_range.mp hj
    dsimp only [below] at h; omega
  have hd : Disjoint ((range L).image (above p)) ((range L).image (below p)) := by
    rw [disjoint_left]
    intro x hx hy; obtain ⟨i,_,rfl⟩ := mem_image.mp hx
    obtain ⟨j,_,h⟩ := mem_image.mp hy; dsimp only [above,below] at h; omega
  rw [interval_decomposition hg hc, sum_union hd, sum_image hi, sum_image hj, sum_add_distrib]

/-- The expected sign on the two prime classes modulo three. -/
def classSign (p : ℕ) : ℤ := if p%3=1 then 1 else -1

/-- The alternating reciprocal sum governing the signed bias of the window. -/
noncomputable def bias (L : ℕ) : ℝ :=
  ∑ k ∈ range L, (1/(6*(k:ℝ)+1) - 1/(6*(k:ℝ)+5))

private def nearOffset (p k : ℕ) := if p%3=1 then 6*k+1 else 6*k+5
private def farOffset (p k : ℕ) := if p%3=1 then 6*k+5 else 6*k+1

private lemma side_errors {k L : ℕ} (hk : k<L) (hg : 6*L+3<p) (hc : p%6=1 ∨ p%6=5) :
    |(S' (p-above p k) p : ℝ) - (p:ℝ)/(3*nearOffset p k)| ≤ 3*nearOffset p k+1 ∧
    |(S' (p-below p k) p : ℝ) + (p:ℝ)/(3*farOffset p k)| ≤ 3*farOffset p k+1 := by
  have hmod : p%2=1 := by omega
  have hp3 : 3<p := by omega
  have h₁ : (6*k+1).Coprime 3 := by
    rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm, Nat.gcd_rec]; simp [show (6*k+1)%3=1 by omega]
  have h₅ : (6*k+5).Coprime 3 := by
    rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm, Nat.gcd_rec]; simp [show (6*k+5)%3=2 by omega]
  have hu := reflected_row_error (a := above p k) (v := nearOffset p k) hmod hp3
    (by dsimp [above]; omega) (by dsimp [above]; omega) (by unfold nearOffset; split <;> omega)
    (by unfold nearOffset; split <;> omega) (by unfold nearOffset; split <;> assumption)
    (Or.inl rfl : (1:ℤ)=1 ∨ (1:ℤ)= -1) (by unfold above nearOffset; split <;> omega)
  have hd := reflected_row_error (a := below p k) (v := farOffset p k) hmod hp3
    (by dsimp [below]; omega) (by dsimp [below]; omega) (by unfold farOffset; split <;> omega)
    (by unfold farOffset; split <;> omega) (by unfold farOffset; split <;> assumption)
    (Or.inr rfl : (-1:ℤ)=1 ∨ (-1:ℤ)= -1) (by unfold below farOffset; split <;> omega)
  exact ⟨by simpa using hu, by simpa [neg_div] using hd⟩

private lemma pair_error {k L : ℕ} (hk : k<L) (hg : 6*L+3<p) (hc : p%6=1 ∨ p%6=5) :
    |(classSign p : ℝ)*((S' (p-above p k) p : ℝ) + S' (p-below p k) p)
      - (p:ℝ)/3*(1/(6*(k:ℝ)+1)-1/(6*(k:ℝ)+5))| ≤ 36*k+20 := by
  obtain ⟨hU,hD⟩ := side_errors hk hg hc
  rw [abs_le] at hU hD ⊢
  rw [mul_sub,mul_one_div,mul_one_div]
  by_cases h : p%3=1 <;>
    simp [classSign,nearOffset,farOffset,h,div_mul_eq_div_div] at hU hD ⊢ <;>
    constructor <;> linarith only [hU.1,hU.2,hD.1,hD.2]

private lemma error_total (L : ℕ) :
    (∑ k ∈ range L, (36*(k:ℝ)+20)) = 18*(L:ℝ)^2+2*L := by
  induction L with
  | zero => simp
  | succ L ih => rw [sum_range_succ, ih]; push_cast; ring

/-- Finite signed estimate for the complete interval of even Hardy numerators about p/3. -/
theorem window_error {L : ℕ} (hg : 6*L+3<p) :
    |(classSign p : ℝ)*(windowSum p L : ℝ) - (p:ℝ)/3*bias L| ≤ 18*L^2+2*L := by
  have hc := residue_class (p := p) (by omega)
  rw [windowSum, sum_window_map hg hc, Int.cast_sum, bias, mul_sum, mul_sum, ← sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  rw [← error_total]
  apply sum_le_sum; intro k hk
  simpa only [Int.cast_add] using pair_error (mem_range.mp hk) hg hc

private lemma bias_lower {L : ℕ} (hL : 0<L) : (4:ℝ)/5 ≤ bias L := by
  have hpos (k : ℕ) : 0 ≤ 1/(6*(k:ℝ)+1)-1/(6*(k:ℝ)+5) := by
    apply sub_nonneg.mpr
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hh := sum_le_sum_of_subset_of_nonneg (s := range 1) (t := range L)
    (f := fun k : ℕ => 1/(6*(k:ℝ)+1)-1/(6*(k:ℝ)+5))
    (range_mono (show 1≤L from hL)) (fun k _ _ => hpos k)
  norm_num at hh
  simpa only [bias,sum_sub_distrib,one_div] using hh

/-- The window has signed magnitude at least p/5 throughout the square-root range. -/
theorem window_signed_lower {L : ℕ} (hL : 0<L) (hp : 300*L^2≤p) :
    (p:ℝ)/5 ≤ (classSign p : ℝ)*(windowSum p L : ℝ) := by
  have hg : 6*L+3<p := by nlinarith [Nat.le_mul_self L]
  have he := (abs_le.mp (window_error hg)).1
  have hh := mul_le_mul_of_nonneg_left (bias_lower hL) (show 0≤(p:ℝ)/3 by positivity)
  have hp' : 300*(L:ℝ)^2≤p := by exact_mod_cast hp
  have hl : (L:ℝ)≤(L:ℝ)^2 := by exact_mod_cast (show L≤L^2 by simpa [sq] using Nat.le_mul_self L)
  nlinarith only [he,hh,hp',hl]

/-- The sign of the complete window reverses between primes one and two modulo three. -/
theorem window_sign {L : ℕ} (hL : 0<L) (hp : 300*L^2≤p) :
    (p%3=1 → 0<windowSum p L) ∧ (p%3=2 → windowSum p L<0) := by
  have h := window_signed_lower hL hp
  have hpos : (0:ℝ)<p := by exact_mod_cast (Fact.out : p.Prime).pos
  constructor <;> intro hc
  · simp [classSign,hc] at h
    exact_mod_cast (show 0<(windowSum p L : ℝ) by linarith)
  · simp [classSign,hc] at h
    exact_mod_cast (show (windowSum p L : ℝ)<0 by linarith)

private noncomputable def kernelWeight (x : ℝ) : ℝ := (1+x^2)/(1+x^2+x^4)

private lemma weight_cont : Continuous kernelWeight := by
  unfold kernelWeight; exact (by fun_prop : Continuous (fun x : ℝ => 1+x^2)).div
    (by fun_prop) (fun x => ne_of_gt (by positivity))

private lemma weight_integral :
    (∫ x in (0:ℝ)..1, kernelWeight x) = Real.pi/(2*Real.sqrt 3) := by
  let r := Real.sqrt 3
  have hr : 0<r := Real.sqrt_pos.mpr (by norm_num)
  have hr2 : r^2=3 := Real.sq_sqrt (by norm_num)
  let F (x : ℝ) := (Real.arctan ((2*x-1)/r) + Real.arctan ((2*x+1)/r))/r
  have dF (x : ℝ) : HasDerivAt F (kernelWeight x) x := by
    have h₁ := (((hasDerivAt_id x).const_mul 2).sub_const 1).div_const r
    have h₂ := (((hasDerivAt_id x).const_mul 2).add_const 1).div_const r
    have h := (h₁.arctan.add h₂.arctan).div_const r
    apply h.congr_deriv
    dsimp [kernelWeight]
    field_simp
    linear_combination (norm := ring_nf) (-(1+x^2)*r^2-4*x^4-9*x^2-1)*hr2
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => dF x) (weight_cont.intervalIntegrable ..)]
  have h3 : 3/r=r := (div_eq_iff hr.ne').mpr (by nlinarith only [hr2])
  simp only [F,mul_one,mul_zero,zero_sub,zero_add]
  norm_num only
  rw [h3, neg_div, Real.arctan_neg, one_div]
  dsimp only [r]; rw [Real.arctan_inv_sqrt_three, Real.arctan_sqrt_three]; ring

private lemma weight_remainder (L : ℕ) (x : ℝ) :
    (∑ k ∈ range L, (x^(6*k)-x^(6*k+4))) + kernelWeight x*x^(6*L) = kernelWeight x := by
  induction L with
  | zero => simp
  | succ L ih =>
    have hw : kernelWeight x * (1-x^6) = 1-x^4 := by
      unfold kernelWeight
      field_simp [show 1+x^2+x^4≠0 by positivity]; ring
    rw [sum_range_succ, Nat.mul_succ, pow_add, pow_add]
    linear_combination ih - x^(6*L)*hw

/-- Effective convergence of the reciprocal bias to π/(2√3). -/
theorem bias_error (L : ℕ) : |Real.pi/(2*Real.sqrt 3) - bias L| ≤ 1/(6*L+1) := by
  let g (x : ℝ) := ∑ k ∈ range L, (x^(6*k)-x^(6*k+4))
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hpoly (n : ℕ) : (∫ x in (0:ℝ)..1, x^n) = 1/(n+1) := by
    rw [integral_pow]; simp
  have hgint : (∫ x in (0:ℝ)..1, g x) = bias L := by
    dsimp only [g,bias]
    rw [intervalIntegral.integral_finsetSum (by intro k _; exact (by fun_prop : Continuous
      (fun x : ℝ => x^(6*k)-x^(6*k+4))).intervalIntegrable ..)]
    apply sum_congr rfl; intro k _
    rw [intervalIntegral.integral_sub ((continuous_pow _).intervalIntegrable ..)
      ((continuous_pow _).intervalIntegrable ..), hpoly, hpoly]
    push_cast; ring
  have hg' : Continuous (fun x : ℝ => kernelWeight x*x^(6*L)) := weight_cont.mul (by fun_prop)
  have he : (∫ x in (0:ℝ)..1, kernelWeight x*x^(6*L)) = Real.pi/(2*Real.sqrt 3) - bias L := by
    rw [← weight_integral, ← hgint, ← intervalIntegral.integral_sub (weight_cont.intervalIntegrable ..)
      (hg.intervalIntegrable ..)]
    apply intervalIntegral.integral_congr; intro x _
    dsimp [g]; linarith only [weight_remainder L x]
  rw [← he, abs_of_nonneg]
  · have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) (by norm_num : (0:ℝ)≤1)
        (hg'.intervalIntegrable ..) ((continuous_pow (6*L)).intervalIntegrable ..)
        (fun x hx => mul_le_of_le_one_left (pow_nonneg hx.1 _) (by
          unfold kernelWeight; apply (div_le_one (by positivity)).mpr; nlinarith [sq_nonneg (x^2)]))
    simpa [hpoly] using h
  · exact intervalIntegral.integral_nonneg (by norm_num) (fun x hx => by
      unfold kernelWeight; exact mul_nonneg (by positivity) (pow_nonneg hx.1 _))

/-- Signed asymptotic with an explicit finite error at every admissible prime and width. -/
theorem window_pi_error {L : ℕ} (hg : 6*L+3<p) :
    |(classSign p : ℝ)*(windowSum p L : ℝ) - Real.pi*p/(6*Real.sqrt 3)| ≤
      18*L^2+2*L+(p:ℝ)/(3*(6*L+1)) := by
  have hw := window_error hg
  have hb := mul_le_mul_of_nonneg_left (bias_error L) (show 0≤(p:ℝ)/3 by positivity)
  rw [← abs_of_nonneg (show 0≤(p:ℝ)/3 by positivity), ← abs_mul, abs_le] at hb
  rw [abs_le] at hw ⊢
  rw [abs_of_nonneg (show 0≤(p:ℝ)/3 by positivity)] at hb
  simp only [mul_sub, div_eq_mul_inv, mul_inv_rev, one_mul] at *
  constructor <;> linarith only [hb.1,hb.2,hw.1,hw.2]

/-- The signed contribution from one side of 2p/3 in the odd-index parametrization. -/
def sideSum (p L : ℕ) (upper : Bool) : ℤ :=
  ∑ a ∈ window p L, if (if upper then 2*p<3*a else 3*a<2*p) then S' (p-a) p else 0

omit [Fact p.Prime] in
private lemma sideSum_eq {L : ℕ} (hg : 6*L+3<p) (hc : p%6=1 ∨ p%6=5) :
    sideSum p L true = ∑ k ∈ range L, S' (p-above p k) p ∧
    sideSum p L false = ∑ k ∈ range L, S' (p-below p k) p := by
  have hU (k : ℕ) (_ : k∈range L) : 2*p<3*above p k := by dsimp [above]; omega
  have hD (k : ℕ) (_ : k∈range L) : 3*below p k<2*p := by dsimp [below]; omega
  constructor <;> rw [sideSum,sum_window_map hg hc] <;> apply sum_congr rfl <;> intro k hk <;>
    simp [hU k hk,hD k hk,(hU k hk).asymm,(hD k hk).asymm]

private lemma side_terms {L k : ℕ} (hk : k<L) (hg : 6*L+3<p) (hc : p%6=1 ∨ p%6=5) :
    (p:ℝ)/18*((k:ℝ)+1)⁻¹ - (18*k+16) ≤ (S' (p-above p k) p : ℝ) ∧
    (p:ℝ)/18*((k:ℝ)+1)⁻¹ - (18*k+16) ≤ -(S' (p-below p k) p : ℝ) := by
  obtain ⟨hU,hD⟩ := side_errors hk hg hc
  rw [abs_le] at hU hD
  have h (z : ℕ) (hz : 0<z) (hz' : z≤6*k+5) :
      (p:ℝ)/18*((k:ℝ)+1)⁻¹ ≤ (p:ℝ)/(3*z) ∧ 3*(z:ℝ)+1≤18*k+16 := by
    have hz'' : (z:ℝ)≤6*(k:ℝ)+5 := by exact_mod_cast hz'
    constructor
    · rw [← div_eq_mul_inv, div_div]
      apply div_le_div_of_nonneg_left (by positivity) (by positivity); linarith
    · linarith
  have h₁ := h (nearOffset p k) (by unfold nearOffset; split <;> omega)
    (by unfold nearOffset; split <;> omega)
  have h₂ := h (farOffset p k) (by unfold farOffset; split <;> omega)
    (by unfold farOffset; split <;> omega)
  constructor <;> linarith only [hU.1,hD.2,h₁.1,h₁.2,h₂.1,h₂.2]

/-- The two contiguous sides have opposite signed subtotals with a common harmonic lower bound. -/
theorem sideSum_harmonic {L : ℕ} (hg : 6*L+3<p) :
    (p:ℝ)/18*(harmonic L : ℝ) - (9*L^2+7*L) ≤
      min (sideSum p L true : ℝ) (-(sideSum p L false : ℝ)) := by
  have hc := residue_class (p := p) (by omega)
  obtain ⟨hU,hD⟩ := sideSum_eq hg hc
  have ht (n : ℕ) : (∑ k ∈ range n, (18*(k:ℝ)+16)) = 9*(n:ℝ)^2+7*n := by
    induction n with
    | zero => simp
    | succ n ih => rw [sum_range_succ, ih]; push_cast; ring
  rw [hU,hD,Int.cast_sum,Int.cast_sum,← sum_neg_distrib,le_min_iff,← ht]
  have hh : (p:ℝ)/18*(harmonic L : ℝ) = ∑ k ∈ range L, (p:ℝ)/18*((k:ℝ)+1)⁻¹ := by
    simp [harmonic,mul_sum]
  rw [hh,← sum_sub_distrib]
  exact ⟨sum_le_sum (fun k hk => (side_terms (mem_range.mp hk) hg hc).1),
    sum_le_sum (fun k hk => (side_terms (mem_range.mp hk) hg hc).2)⟩

/-- For any prescribed multiple of p, both one-sided signed contributions exceed it in
magnitude, in a fixed width window, at every sufficiently large prime. -/
theorem sideSum_eventually_large (C : ℝ) : ∃ L N : ℕ, ∀ (p : ℕ) [Fact p.Prime], N<p →
    C*p < min (sideSum p L true : ℝ) (-(sideSum p L false : ℝ)) := by
  obtain ⟨L,hL⟩ := exists_nat_gt (Real.exp (18*(C+1)))
  have hh : 18*(C+1) ≤ (harmonic L : ℝ) := by
    apply le_trans _ (log_add_one_le_harmonic L)
    rw [← Real.log_exp (18*(C+1))]
    apply Real.log_le_log (Real.exp_pos _); push_cast; linarith
  refine ⟨L, 9*L^2+7*L+6*L+3, ?_⟩
  intro p _ hp
  apply lt_of_lt_of_le _ (sideSum_harmonic (show 6*L+3<p by omega))
  have hcost : 9*(L:ℝ)^2+7*L < p := by exact_mod_cast (show 9*L^2+7*L<p by omega)
  have h := mul_le_mul_of_nonneg_left hh (show 0≤(p:ℝ)/18 by positivity)
  nlinarith only [h,hcost]

omit [Fact p.Prime] in
/-- In the source indexing this is the entire even-numerator interval |3h−p| < 6L. -/
theorem windowSum_eq_even_interval {L : ℕ} (hp : p%2=1) :
    windowSum p L = ∑ h ∈ (Ico 1 p).filter (fun h => h%2=0 ∧ p<3*h+6*L ∧ 3*h<p+6*L),
      S' h p := by
  unfold windowSum
  apply sum_nbij' (fun a => p-a) (fun h => p-h)
  · intro a ha; rcases mem_filter.mp ha with ⟨hi,ho,h₁,h₂⟩
    obtain ⟨_,_⟩ := mem_Ico.mp hi
    exact mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega,by omega⟩,by omega,by omega,by omega⟩
  · intro a ha; rcases mem_filter.mp ha with ⟨hi,ho,h₁,h₂⟩
    obtain ⟨_,_⟩ := mem_Ico.mp hi
    exact mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega,by omega⟩,by omega,by omega,by omega⟩
  · intro a ha; have := (mem_Ico.mp (mem_filter.mp ha).1).2; omega
  · intro a ha; have := (mem_Ico.mp (mem_filter.mp ha).1).2; omega
  · intros; rfl

end Arxiv.«2501.03234».ThetaThirdWindow

#print axioms Arxiv.«2501.03234».ThetaThirdWindow.sample_error
#print axioms Arxiv.«2501.03234».ThetaThirdWindow.row_ratio_error
#print axioms Arxiv.«2501.03234».ThetaThirdWindow.window_error
#print axioms Arxiv.«2501.03234».ThetaThirdWindow.window_signed_lower
#print axioms Arxiv.«2501.03234».ThetaThirdWindow.window_sign
#print axioms Arxiv.«2501.03234».ThetaThirdWindow.bias_error
#print axioms Arxiv.«2501.03234».ThetaThirdWindow.window_pi_error
#print axioms Arxiv.«2501.03234».ThetaThirdWindow.sideSum_harmonic
#print axioms Arxiv.«2501.03234».ThetaThirdWindow.sideSum_eventually_large
#print axioms Arxiv.«2501.03234».ThetaThirdWindow.windowSum_eq_even_interval
