import ThetaReciprocalCutoff
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.Normed.Group.Tannery

/-! The harmonic contribution from exact multiples in the full cotangent sum. -/

namespace Arxiv.«2501.03234».ThetaDivisibleDiagonal

open Finset ThetaCotangentTriangle

/-- Harmonic sum over the first n positive odd integers. -/
noncomputable def oddHarmonic (n : ℕ) : ℝ :=
  ∑ k ∈ range n, (2*(k:ℝ)+1)⁻¹

private lemma oddHarmonic_compare (n : ℕ) :
    0 ≤ oddHarmonic n-(harmonic n:ℝ)/2 ∧
    oddHarmonic n-(harmonic n:ℝ)/2 ≤ 1-((n:ℝ)+1)⁻¹ := by
  induction n with
  | zero => simp [oddHarmonic,harmonic]
  | succ n ih =>
    have he : oddHarmonic (n+1)=oddHarmonic n+(2*(n:ℝ)+1)⁻¹ := sum_range_succ ..
    rw [he,harmonic_succ]
    push_cast
    have h₁ : 0 ≤ (2*(n:ℝ)+1)⁻¹-((n:ℝ)+1)⁻¹/2 := by
      field_simp; nlinarith [Nat.cast_nonneg (α:=ℝ) n]
    have h₂ : (2*(n:ℝ)+1)⁻¹-((n:ℝ)+1)⁻¹/2 ≤
        ((n:ℝ)+1)⁻¹-((n:ℝ)+1+1)⁻¹ := by
      field_simp; nlinarith [Nat.cast_nonneg (α:=ℝ) n,sq_nonneg (n:ℝ)]
    constructor <;> linarith only [ih.1,ih.2,h₁,h₂]

/-- The error in replacing the odd reciprocal sum by half a logarithm is uniformly bounded. -/
theorem oddHarmonic_log (n : ℕ) :
    0 ≤ oddHarmonic n-Real.log ((n:ℝ)+1)/2 ∧
    oddHarmonic n-Real.log ((n:ℝ)+1)/2 ≤ 3/2 := by
  have he := oddHarmonic_compare n
  have hl := log_add_one_le_harmonic n
  push_cast at hl
  by_cases hn : n=0
  · norm_num [hn,oddHarmonic]
  have hreal : 0<(n:ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hu := harmonic_le_one_add_log n
  have hm := Real.log_le_log hreal (show (n:ℝ)≤n+1 by linarith)
  constructor <;> linarith [inv_nonneg.mpr (show 0≤(n:ℝ)+1 by positivity)]

/-- Total mass of the squared inverse odd indices. -/
theorem odd_reciprocal_square :
    HasSum (fun n : ℕ => ((2*(n:ℝ)+1)^2)⁻¹) (Real.pi^2/8) := by
  let f (n : ℕ) : ℝ := 1/(n:ℝ)^2
  have h : HasSum f (Real.pi^2/6) := hasSum_zeta_two
  have he : HasSum (fun n : ℕ => f (2*n)) ((1/4)*(Real.pi^2/6)) := by
    apply (h.mul_left (1/4)).congr_fun
    intro n; dsimp [f]; push_cast; ring
  have ho : Summable (fun n : ℕ => f (2*n+1)) := h.summable.comp_injective (by intro a b he; dsimp at he; omega)
  have hh := (he.even_add_odd ho.hasSum).unique h
  have heq : ∑' n : ℕ, f (2*n+1) = Real.pi^2/8 := by linarith
  rw [← heq]; apply ho.hasSum.congr_fun; intro n
  dsimp [f]; push_cast; ring

/-- Odd multipliers for which g*u < p. -/
def multiplierCount (p u : ℕ) : ℕ := ((p-1)/u+1)/2

/-- Harmonic proxy for the exact-divisibility contribution. -/
noncomputable def harmonicDiagonal (p : ℕ) : ℝ :=
  ∑ j ∈ range (p/2), ((2*(j:ℝ)+1)^2)⁻¹ * oddHarmonic (multiplierCount p (2*j+1))

/-- Exact cotangent contribution indexed by odd pairs (u,v) with u dividing v. -/
noncomputable def divisibleDiagonal (p : ℕ) : ℝ :=
  2/(p:ℝ)*∑ j ∈ range (p/2), weight p (2*j+1) *
    ∑ k ∈ range (multiplierCount p (2*j+1)), weight p ((2*j+1)*(2*k+1))

private lemma odd_multipliers_log {p u : ℕ} (hu : 0<u) (hp : u<p) :
    |oddHarmonic (multiplierCount p u)-Real.log ((p:ℝ)/u)/2| ≤ 3 := by
  let s := (p-1)/u
  let n := multiplierCount p u
  have hs : s*u≤p := (Nat.div_mul_le_self _ _).trans (Nat.sub_le ..)
  have hs' : p≤(s+1)*u := by
    have h := (Nat.div_lt_iff_lt_mul hu).mp (show (p-1)/u < s+1 from Nat.lt_succ_self s)
    omega
  have hn : n ≤ s := (show ∀ a : ℕ, (a+1)/2 ≤ a by intro a; omega) s
  have hn' : s+1 ≤ 2*(n+1) := (show ∀ a : ℕ, a+1 ≤ 2*((a+1)/2+1) by intro a; omega) s
  have hur : 0<(u:ℝ) := by exact_mod_cast hu
  have hbr : 1 ≤ (p:ℝ)/u := (one_le_div hur).mpr (by exact_mod_cast hp.le)
  have hbp : 0<(p:ℝ)/u := lt_of_lt_of_le zero_lt_one hbr
  have hlo : (p:ℝ)/u ≤ 2*((n:ℝ)+1) := by
    rw [div_le_iff₀ hur]
    exact_mod_cast hs'.trans (Nat.mul_le_mul_right u hn')
  have hhi : (n:ℝ)+1 ≤ 2*((p:ℝ)/u) := by
    have ht : (s:ℝ) ≤ (p:ℝ)/u := (le_div_iff₀ hur).mpr (by exact_mod_cast hs)
    have h := (show (n:ℝ) ≤ s by exact_mod_cast hn).trans ht
    linarith
  have h₁ := Real.log_le_log hbp hlo
  have h₂ := Real.log_le_log (show 0<(n:ℝ)+1 by positivity) hhi
  rw [Real.log_mul (by norm_num) (by positivity)] at h₁
  rw [Real.log_mul (by norm_num) hbp.ne'] at h₂
  have h := oddHarmonic_log n
  change |oddHarmonic n-_ / 2|≤3
  rw [abs_le]; constructor <;> linarith [Real.log_le_self (by norm_num : (0:ℝ)≤2),h.1,h.2]

/-- Membership in the multiplier range is exactly the strict inequality used by the full
Fourier sum. This includes every diagonal term u=v. -/
theorem multiplier_mem {p u k : ℕ} (hu : 0<u) (hp : 0<p) :
    k ∈ range (multiplierCount p u) ↔ u*(2*k+1)<p := by
  rw [mem_range,multiplierCount]
  have h : k < ((p-1)/u+1)/2 ↔ 2*k+1 ≤ (p-1)/u := by omega
  rw [h,Nat.le_div_iff_mul_le hu,mul_comm]
  omega

private noncomputable def majorant (j : ℕ) : ℝ :=
  let u := 2*(j:ℝ)+1
  u^(-2:ℝ)*3 + u^(-3/2:ℝ)

private lemma majorant_summable : Summable majorant := by
  have hs (a : ℝ) (ha : a < -1) : Summable (fun j : ℕ => (2*(j:ℝ)+1)^a) := by
    have h := (Real.summable_nat_rpow.mpr ha).comp_injective
      (show Function.Injective (fun j : ℕ => 2*j+1) by intro i j e; dsimp at e; omega)
    simpa [Function.comp_def] using h
  exact ((hs (-2) (by norm_num)).mul_right 3).add (hs (-3/2) (by norm_num))

private noncomputable def rowTerm (p j : ℕ) : ℝ :=
  if j < p/2 then ((2*(j:ℝ)+1)^2)⁻¹ * oddHarmonic (multiplierCount p (2*j+1)) else 0

private lemma row_estimate {p : ℕ} (hp : 0<p) (j : ℕ) :
    |rowTerm p j - ((2*(j:ℝ)+1)^2)⁻¹ * (Real.log p/2)| ≤ majorant j := by
  let u : ℝ := 2*(j:ℝ)+1
  have hu₁ : 1≤u := by dsimp [u]; linarith [Nat.cast_nonneg (α:=ℝ) j]
  have hu : 0<u := zero_lt_one.trans_le hu₁
  have hp' : 0<(p:ℝ) := by exact_mod_cast hp
  have hulog := Real.log_nonneg hu₁
  have hweight : 0≤(u^2)⁻¹ := by positivity
  have ht : (u^2)⁻¹*(3+Real.log u/2) ≤ majorant j := by
    have hlog := Real.log_le_rpow_div hu.le (show (0:ℝ)<1/2 by norm_num)
    have hpow : (u^2)⁻¹ = u^(-2:ℝ) := by rw [Real.rpow_neg hu.le,Real.rpow_two]
    change _ ≤ u^(-2:ℝ)*3 + u^(-3/2:ℝ)
    rw [mul_add,hpow,show (-3/2:ℝ) = -2+1/2 by norm_num,Real.rpow_add hu]
    apply add_le_add le_rfl
    exact mul_le_mul_of_nonneg_left (by linarith : Real.log u/2≤u^(1/2:ℝ)) (Real.rpow_nonneg hu.le _)
  apply le_trans _ ht
  by_cases hj : j < p/2
  · have hlt : 2*j+1 < p := by omega
    have herr := odd_multipliers_log (u:=2*j+1) (by omega) hlt
    push_cast at herr
    change |oddHarmonic _ - Real.log ((p:ℝ)/u)/2| ≤ 3 at herr
    rw [Real.log_div hp'.ne' hu.ne'] at herr
    simp only [rowTerm,if_pos hj]
    change |(u^2)⁻¹ * _ - (u^2)⁻¹ * _| ≤ _
    rw [← mul_sub,abs_mul,abs_of_nonneg hweight]
    apply mul_le_mul_of_nonneg_left _ hweight
    rw [abs_le] at herr ⊢
    constructor <;> linarith [herr.1,herr.2]
  · have hle : (p:ℝ) ≤ u := by dsimp [u]; exact_mod_cast (show p ≤ 2*j+1 by omega)
    have hlog := Real.log_le_log hp' hle
    have hp₁ : 1≤(p:ℝ) := by exact_mod_cast hp
    simp only [rowTerm,if_neg hj,zero_sub,abs_neg]
    change |(u^2)⁻¹ * (Real.log p/2)| ≤ _
    rw [abs_of_nonneg (mul_nonneg hweight (by linarith [Real.log_nonneg hp₁]))]
    apply mul_le_mul_of_nonneg_left _ hweight
    linarith

/-- The full odd-divisor harmonic diagonal has an absolute bounded error.
Its logarithmic coefficient is half the odd Basel sum. -/
theorem harmonicDiagonal_log : ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, 0 < p →
    |harmonicDiagonal p - (Real.pi^2/16)*Real.log p| ≤ C := by
  have hs := majorant_summable.hasSum
  have hn : 0 ≤ ∑' j, majorant j := tsum_nonneg (by intro j; dsimp [majorant]; positivity)
  refine ⟨(∑' j, majorant j)+1, by linarith, ?_⟩
  intro p hp
  have hf : HasSum (rowTerm p) (harmonicDiagonal p) := by
    have h := hasSum_sum_of_ne_finset_zero (L:=.unconditional ℕ) (s:=range (p/2)) (f:=rowTerm p)
      (by intro j hj; simp only [mem_range] at hj; simp [rowTerm,hj])
    convert h using 1
    apply sum_congr rfl
    intro j hj
    simp [rowTerm,mem_range.mp hj]
  have he := hf.sub (odd_reciprocal_square.mul_right (Real.log p/2))
  have hhi := hasSum_le (fun j => (abs_le.mp (row_estimate hp j)).2) he hs
  have hlo := hasSum_le (fun j => (abs_le.mp (row_estimate hp j)).1) hs.neg he
  rw [abs_le]
  constructor <;> linarith

open ThetaReciprocalCutoff (linearWeight product_error)

private lemma odd_sum (n : ℕ) : ∑ k ∈ range n, (2*(k:ℝ)+1) = (n:ℝ)^2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ,ih]; push_cast; ring

theorem row_linearization {p u : ℕ} (hu : 0<u) (hul : u<p) :
    |weight p u * (∑ k ∈ range (multiplierCount p u), weight p (u*(2*k+1))) -
      (2*p/Real.pi)^2 * ((u:ℝ)^2)⁻¹ * oddHarmonic (multiplierCount p u)| ≤
      ((p:ℝ)/u)^2 := by
  let n := multiplierCount p u
  have hpr : 0<(p:ℝ) := by exact_mod_cast hu.trans hul
  have hur : 0<(u:ℝ) := by exact_mod_cast hu
  have he : (2*p/Real.pi)^2 * ((u:ℝ)^2)⁻¹ * oddHarmonic n =
      ∑ k ∈ range n, linearWeight p u * linearWeight p (u*(2*k+1)) := by
    rw [oddHarmonic,mul_sum]
    apply sum_congr rfl
    intro k _
    dsimp [linearWeight]; push_cast
    have hg : 0 < 2*(k:ℝ)+1 := by positivity
    field_simp
  change |weight p u * (∑ k ∈ range n, _) - _ * oddHarmonic n| ≤ _
  rw [he,mul_sum,← sum_sub_distrib]
  apply (abs_sum_le_sum_abs ..).trans
  calc
    _ ≤ ∑ k ∈ range n, (2*(k:ℝ)+1) := by
      apply sum_le_sum
      intro k hk
      have hm := (multiplier_mem hu (hu.trans hul)).mp hk
      have hle : u ≤ u*(2*k+1) := Nat.le_mul_of_pos_right _ (by omega)
      have h := product_error (p:=p) hu hle hm
      rw [mul_comm (weight _ _),mul_comm (linearWeight _ _)] at h
      push_cast at h
      exact h.trans_eq (by field_simp)
    _ = (n:ℝ)^2 := odd_sum n
    _ ≤ ((p:ℝ)/u)^2 := by
      have hn : n ≤ (p-1)/u :=
        (show ∀ a : ℕ, (a+1)/2 ≤ a by intro a; omega) _
      have hnu : n*u≤p := (Nat.mul_le_mul_right u hn).trans
        ((Nat.div_mul_le_self _ _).trans (Nat.sub_le ..))
      have hle : (n:ℝ)≤(p:ℝ)/u := (le_div_iff₀ hur).mpr (by exact_mod_cast hnu)
      gcongr

/-- Linearizing the divisible pairs costs at most a constant times p, uniformly. -/
theorem divisibleDiagonal_linearization {p : ℕ} (hp : 0<p) :
    |divisibleDiagonal p - (8*p/Real.pi^2)*harmonicDiagonal p| ≤ (Real.pi^2/4)*p := by
  let a (j : ℕ) := weight p (2*j+1) *
    ∑ k ∈ range (multiplierCount p (2*j+1)), weight p ((2*j+1)*(2*k+1))
  let b (j : ℕ) := ((2*(j:ℝ)+1)^2)⁻¹ * oddHarmonic (multiplierCount p (2*j+1))
  let m : ℝ := (2*p/Real.pi)^2
  have hp' : 0<(p:ℝ) := by exact_mod_cast hp
  have he : 8*p/Real.pi^2 = (2/(p:ℝ))*m := by dsimp [m]; field_simp; ring
  change |2/(p:ℝ)*(∑ j ∈ range (p/2), a j) - (8*p/Real.pi^2)*(∑ j ∈ range (p/2), b j)| ≤ _
  rw [he,mul_assoc,← mul_sub,mul_sum,← sum_sub_distrib,abs_mul,abs_of_nonneg (by positivity : 0≤2/(p:ℝ))]
  have hr (j) (hj : j ∈ range (p/2)) : |a j-m*b j| ≤ (p:ℝ)^2 * ((2*(j:ℝ)+1)^2)⁻¹ := by
    have h := row_linearization (p:=p) (u:=2*j+1) (by omega) (by have := mem_range.mp hj; omega)
    dsimp only [a,m,b]
    rw [← mul_assoc]
    push_cast at h
    exact h.trans_eq (by rw [div_pow,div_eq_mul_inv])
  have hmass := odd_reciprocal_square.summable.sum_le_tsum (range (p/2)) (by intros; positivity)
  rw [odd_reciprocal_square.tsum_eq] at hmass
  apply (mul_le_mul_of_nonneg_left ((abs_sum_le_sum_abs ..).trans (sum_le_sum hr)) (by positivity)).trans
  rw [← mul_sum]
  calc
    _ ≤ 2/(p:ℝ)*((p:ℝ)^2*(Real.pi^2/8)) := by gcongr
    _ = _ := by field_simp; ring

/-- The whole cotangent diagonal v = g*u (g odd) supplies (p/2) log p with O(p)
error, uniformly for positive p. -/
theorem divisibleDiagonal_asymptotic : ∃ C : ℝ, 0<C ∧ ∀ p : ℕ, 0<p →
    |divisibleDiagonal p - (p:ℝ)*Real.log p/2| ≤ C*p := by
  obtain ⟨C,hC,h⟩ := harmonicDiagonal_log
  refine ⟨Real.pi^2/4 + (8/Real.pi^2)*C, by positivity, ?_⟩
  intro p hp
  have he : (p:ℝ)*Real.log p/2 =
      (8*p/Real.pi^2)*((Real.pi^2/16)*Real.log p) := by field_simp; ring
  rw [he]
  apply (abs_sub_le _ ((8*p/Real.pi^2)*harmonicDiagonal p) _).trans
  rw [← mul_sub,abs_mul,abs_of_nonneg (by positivity : 0≤8*(p:ℝ)/Real.pi^2)]
  exact (add_le_add (divisibleDiagonal_linearization hp)
    (mul_le_mul_of_nonneg_left (h p hp) (by positivity))).trans_eq (by ring)

private lemma quotientSign_multiple {p u g : ℕ} [Fact p.Prime] (hu : 0<u) (hul : u<p)
    (hg : g%2=1) (hgl : g<p) : quotientSign p u (u*g) = 1 := by
  have hu' : (u : ZMod p)≠0 := by
    intro he; have h := congrArg ZMod.val he
    rw [ZMod.val_natCast_of_lt hul,ZMod.val_zero] at h; omega
  simp [quotientSign,Nat.cast_mul,mul_div_cancel_left₀ _ hu',ZMod.val_natCast_of_lt hgl,hg]

private lemma multiple_row {p u : ℕ} [Fact p.Prime] (hu : u%2=1) (hul : u<p) :
    ∑ k ∈ (range (p/2)).filter (fun k => u ∣ 2*k+1),
      weight p (2*k+1)*(quotientSign p u (2*k+1):ℝ) =
    ∑ k ∈ range (multiplierCount p u), weight p (u*(2*k+1)) := by
  have hu₀ : 0<u := by omega
  have hp₀ := hu₀.trans hul
  have index (k : ℕ) : 2*((u*(2*k+1))/2)+1 = u*(2*k+1) := by
    have h : (u*(2*k+1))%2=1 := by rw [Nat.mul_mod,hu]; omega
    omega
  symm
  apply sum_bij (fun (k : ℕ) _ => (u*(2*k+1))/2)
  · intro k hk
    have hl := (multiplier_mem hu₀ hp₀).mp hk
    exact mem_filter.mpr ⟨mem_range.mpr (by have := index k; omega),by rw [index]; exact dvd_mul_right ..⟩
  · intro a ha b hb he
    have he' : u*(2*a+1) = u*(2*b+1) := by rw [← index a,← index b,he]
    have := Nat.eq_of_mul_eq_mul_left hu₀ he'; omega
  · intro k hk
    obtain ⟨hk',hdiv⟩ := mem_filter.mp hk
    obtain ⟨g,hg⟩ := hdiv
    have hgo : g%2=1 := by have e := congrArg (·%2) hg; rw [Nat.mul_mod,hu,one_mul,Nat.mod_mod] at e; omega
    have eg : 2*(g/2)+1=g := by omega
    refine ⟨g/2,(multiplier_mem hu₀ hp₀).mpr ?_,?_⟩
    · rw [eg,← hg]; have := mem_range.mp hk'; omega
    · rw [eg,← hg]; omega
  · intro k hk
    rw [index]
    have hlt := (multiplier_mem hu₀ hp₀).mp hk
    have hgl : 2*k+1<p := (Nat.le_mul_of_pos_left _ hu₀).trans_lt hlt
    rw [quotientSign_multiple hu₀ hul (by omega) hgl]
    simp

/-- The remaining signed cotangent sum after removing all exact multiples. -/
noncomputable def offDiagonal (p : ℕ) : ℝ :=
  2/(p:ℝ)*∑ j ∈ range (p/2), weight p (2*j+1) *
    ∑ k ∈ (range (p/2)).filter (fun k => ¬(2*j+1)∣(2*k+1)),
      weight p (2*k+1)*(reciprocalSign p (2*j+1) (2*k+1):ℝ)

/-- Exact identity in the pinned theta sum, for every odd prime. -/
theorem S_eq_diagonal_add_offDiagonal {p : ℕ} [Fact p.Prime] (hp : p%2=1) :
    (S p:ℝ)=divisibleDiagonal p + offDiagonal p := by
  have hrow (u : ℕ) (hu : u%2=1) (hul : u<p) :
      ∑ k ∈ range (p/2), weight p (2*k+1)*(quotientSign p u (2*k+1):ℝ) =
      (∑ k ∈ range (multiplierCount p u), weight p (u*(2*k+1))) +
      ∑ k ∈ (range (p/2)).filter (fun k => ¬u∣2*k+1), weight p (2*k+1)*(reciprocalSign p u (2*k+1):ℝ) := by
    rw [← sum_filter_add_sum_filter_not (range (p/2)) (fun k => u∣2*k+1),multiple_row hu hul]
    congr 1
    apply sum_congr rfl; intro k hk
    obtain ⟨hk',hnd⟩ := mem_filter.mp hk
    rw [quotient_eq_reciprocal_of_not_dvd hp hu (by omega) hnd hul (by have := mem_range.mp hk'; omega)]
  have h := S_cotangent hp
  rw [sum_congr rfl (fun j hj => congrArg (weight p (2*j+1) * ·)
    (hrow _ (by omega) (by have := mem_range.mp hj; omega)))] at h
  simp_rw [mul_add (weight p _) _ _,sum_add_distrib] at h
  unfold divisibleDiagonal offDiagonal
  have hne : (p:ℝ)≠0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  field_simp
  linear_combination h

/-- For the canonical S(p), the error after subtracting its logarithmic diagonal
and the nondivisible reciprocal sum is uniformly O(p). -/
theorem S_sub_offDiagonal_asymptotic : ∃ C : ℝ, 0<C ∧ ∀ (p : ℕ) [Fact p.Prime], p%2=1 →
    |(S p:ℝ)-offDiagonal p-(p:ℝ)*Real.log p/2| ≤ C*p := by
  obtain ⟨C,hC,h⟩ := divisibleDiagonal_asymptotic
  refine ⟨C,hC,?_⟩
  intro p _ hp
  rw [S_eq_diagonal_add_offDiagonal hp,add_sub_cancel_right]
  exact h p (Fact.out : p.Prime).pos

/-- The exact divisible part differs by O(p) from p times the odd harmonic sum
in the existing OMA main-term reduction. -/
theorem divisibleDiagonal_oddHarmonic : ∃ C : ℝ, 0<C ∧ ∀ p : ℕ, 1<p →
    |divisibleDiagonal p - (p:ℝ)*oddHarmonic (p/2)| ≤ C*p := by
  obtain ⟨C,hC,h⟩ := divisibleDiagonal_asymptotic
  refine ⟨C+3,by linarith,?_⟩
  intro p hp
  have hcount : multiplierCount p 1=p/2 := by simp [multiplierCount]; omega
  have hh := odd_multipliers_log (u:=1) (by decide) hp
  rw [hcount] at hh
  norm_num at hh
  have hμ : |(p:ℝ)*Real.log p/2-(p:ℝ)*oddHarmonic (p/2)| ≤ (p:ℝ)*3 := by
    rw [mul_div_assoc,← mul_sub,abs_mul,abs_of_nonneg (Nat.cast_nonneg p),abs_sub_comm]
    exact mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg p)
  exact (abs_sub_le _ _ _).trans ((add_le_add (h p (by omega)) hμ).trans_eq (by ring))

/-- Summing pointwise centered odd-harmonic limits against the odd-square
weights is justified by the same summable majorant as the logarithmic bound. -/
theorem harmonic_diagonal_limit {L : ℕ → ℝ}
    (hL : ∀ j : ℕ, Filter.Tendsto (fun p : ℕ => oddHarmonic (multiplierCount p (2*j+1))-Real.log p/2)
      Filter.atTop (nhds (L j))) :
    Filter.Tendsto (fun p : ℕ => harmonicDiagonal p-(Real.pi^2/16)*Real.log p)
      Filter.atTop (nhds (∑' j : ℕ, ((2*(j:ℝ)+1)^2)⁻¹*L j)) := by
  let f (p j : ℕ) := rowTerm p j-((2*(j:ℝ)+1)^2)⁻¹*(Real.log p/2)
  have h (j : ℕ) : Filter.Tendsto (fun p => f p j) Filter.atTop (nhds (((2*(j:ℝ)+1)^2)⁻¹*L j)) := by
    apply ((hL j).const_mul _).congr'
    filter_upwards [Filter.eventually_ge_atTop (2*j+2)] with p hp
    have hj : j<p/2 := by omega
    dsimp [f,rowTerm]; rw [if_pos hj]; ring
  have hb : ∀ᶠ p : ℕ in Filter.atTop, ∀ j, ‖f p j‖ ≤ majorant j := by
    filter_upwards [Filter.eventually_ge_atTop 1] with p hp j
    exact row_estimate hp j
  have H := tendsto_tsum_of_dominated_convergence majorant_summable h hb
  apply H.congr'; apply Filter.Eventually.of_forall; intro p
  have hf : HasSum (rowTerm p) (harmonicDiagonal p) := by
    have hh := hasSum_sum_of_ne_finset_zero (L:=.unconditional ℕ) (s:=range (p/2)) (f:=rowTerm p)
      (by intro j hj; simp only [mem_range] at hj; simp [rowTerm,hj])
    convert hh using 1
    apply sum_congr rfl; intro j hj; simp [rowTerm,mem_range.mp hj]
  have he := (hf.sub (odd_reciprocal_square.mul_right (Real.log p/2))).tsum_eq
  change (∑' j,f p j)=_
  convert he using 1; ring

end Arxiv.«2501.03234».ThetaDivisibleDiagonal
#print axioms Arxiv.«2501.03234».ThetaDivisibleDiagonal.harmonic_diagonal_limit
#print axioms Arxiv.«2501.03234».ThetaDivisibleDiagonal.row_linearization
#print axioms Arxiv.«2501.03234».ThetaDivisibleDiagonal.oddHarmonic_log
#print axioms Arxiv.«2501.03234».ThetaDivisibleDiagonal.odd_reciprocal_square
#print axioms Arxiv.«2501.03234».ThetaDivisibleDiagonal.multiplier_mem
#print axioms Arxiv.«2501.03234».ThetaDivisibleDiagonal.harmonicDiagonal_log
#print axioms Arxiv.«2501.03234».ThetaDivisibleDiagonal.divisibleDiagonal_linearization
#print axioms Arxiv.«2501.03234».ThetaDivisibleDiagonal.divisibleDiagonal_asymptotic
#print axioms Arxiv.«2501.03234».ThetaDivisibleDiagonal.S_eq_diagonal_add_offDiagonal
#print axioms Arxiv.«2501.03234».ThetaDivisibleDiagonal.S_sub_offDiagonal_asymptotic
#print axioms Arxiv.«2501.03234».ThetaDivisibleDiagonal.divisibleDiagonal_oddHarmonic
