import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import ThetaCharacterThree

/-! The mod-six numerator sum in the modulo-three character transform. -/
namespace Arxiv.«2501.03234».ThetaCharacterNumerator
open Finset Filter Real ThetaCharacterThree
open scoped Topology

noncomputable def block (k : ℕ) : ℝ := 1/(6*(k:ℝ)+1)-1/(6*(k:ℝ)+5)

private lemma sixth_not_integer : (1/6 : ℂ) ∈ Complex.integerComplement := by
  rw [Complex.mem_integerComplement_iff]
  rintro ⟨n,hn⟩
  have hr := congrArg Complex.re hn
  norm_num at hr
  have hpos : 0 < n := by exact_mod_cast (show (0:ℝ) < n by linarith)
  have hlt : n < 1 := by exact_mod_cast (show (n:ℝ) < 1 by linarith)
  omega

/-- Paired numerator terms sum to π/(2√3). -/
theorem bare_blocks_limit :
    Tendsto (fun N => ∑ k ∈ range N, block k) atTop (𝓝 (Real.pi/(2*Real.sqrt 3))) := by
  let t (k : ℕ) : ℝ := 1/(1/6-((k:ℝ)+1))+1/(1/6+((k:ℝ)+1))
  have ht (k : ℕ) : cotTerm (1/6:ℂ) k = (t k : ℂ) := by
    dsimp only [t,cotTerm]
    push_cast
    ring
  have hc : Complex.cot ((Real.pi:ℂ)*(1/6)) = (Real.sqrt 3 : ℝ) := by
    rw [show (Real.pi:ℂ)*(1/6) = ((Real.pi/6 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cot,← Real.tan_inv_eq_cot,Real.tan_pi_div_six]
    simp
  have h := tendsto_logDeriv_euler_cot_sub sixth_not_integer
  simp only [ht,← Complex.ofReal_sum,hc] at h
  have hR := Complex.continuous_re.continuousAt.tendsto.comp h
  have hlim : Tendsto (fun N => ∑ k ∈ range N,t k) atTop (𝓝 (Real.pi*Real.sqrt 3-6)) := by
    convert hR using 1 <;> norm_num [Function.comp_def]
  have hstep (k : ℕ) : block k = t k/6 + 1/(6*(k:ℝ)+1)-1/(6*(k:ℝ)+7) := by
    dsimp [block,t]
    rw [show (1/6:ℝ)-((k:ℝ)+1) = -(6*k+5)/6 by ring,
      show (1/6:ℝ)+((k:ℝ)+1) = (6*k+7)/6 by ring]
    field_simp
    ring
  have hprefix (N : ℕ) : ∑ k ∈ range N, block k =
      1+(∑ k ∈ range N,t k)/6-1/(6*(N:ℝ)+1) := by
    induction N with
    | zero => norm_num
    | succ n ih =>
      rw [sum_range_succ,sum_range_succ,ih,hstep]
      push_cast
      ring
  have htop : Tendsto (fun N : ℕ => 6*(N:ℝ)+1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop b] with N hN
    linarith [Nat.cast_nonneg (α := ℝ) N]
  have H := ((tendsto_const_nhds (x := (1:ℝ))).add (hlim.div_const 6)).sub (htop.const_div_atTop 1)
  have hr := Real.sq_sqrt (show (0:ℝ)≤3 by norm_num)
  have hv : 1+(Real.pi*Real.sqrt 3-6)/6-0 = Real.pi/(2*Real.sqrt 3) := by
    field_simp
    nlinarith only [congrArg (Real.pi*·) hr]
  rw [hv] at H
  exact H.congr' (Eventually.of_forall fun N => (hprefix N).symm)

#print axioms bare_blocks_limit

private lemma bare_shift (m j : ℕ) : bareTerm (6*m+j) =
    if j%6=1 then 1/((6:ℝ)*m+j) else if j%6=5 then -(1/((6:ℝ)*m+j)) else 0 := by
  simp [bareTerm,Nat.add_mod,one_div]

private lemma prefix_sixes (m : ℕ) :
    ∑ j ∈ range (6*m), bareTerm j = ∑ k ∈ range m,block k := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ,sum_range_add,ih,sum_range_succ]
    simp_rw [bare_shift]
    norm_num [sum_range_succ,block]
    ring

private lemma prefix_split (n : ℕ) :
    ∑ j ∈ range n, bareTerm j = (∑ k ∈ range (n/6),block k) +
        (if 1<n%6 then 1/(6*((n/6:ℕ):ℝ)+1) else 0) := by
  conv_lhs => rw [show n = 6*(n/6)+n%6 by omega]
  rw [sum_range_add,prefix_sixes]
  congr 1
  simp_rw [bare_shift]
  have h := Nat.mod_lt n (by decide : 0<6)
  interval_cases n%6 <;> norm_num [sum_range_succ]

/-- The ordinary (possibly incomplete) cutoff of the signed odd reciprocal
numerators has the same limit as the paired six-block sum. -/
theorem bare_prefix_limit :
    Tendsto (fun n => ∑ j ∈ range n,bareTerm j) atTop (𝓝 (Real.pi/(2*Real.sqrt 3))) := by
  have hdiv : Tendsto (fun n : ℕ => n/6) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop (6*b)] with n h
    omega
  have htop : Tendsto (fun n : ℕ => 6*((n/6:ℕ):ℝ)+1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [((tendsto_natCast_atTop_atTop (R := ℝ)).comp hdiv).eventually_ge_atTop b] with n h
    change b ≤ ((n/6:ℕ):ℝ) at h
    linarith [Nat.cast_nonneg (α:=ℝ) (n/6)]
  have hrest : Tendsto (fun n : ℕ => if 1<n%6 then 1/(6*((n/6:ℕ):ℝ)+1) else 0) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (htop.const_div_atTop 1)
    · exact Eventually.of_forall fun n => by split_ifs <;> positivity
    · exact Eventually.of_forall fun n => by split_ifs <;> first | rfl | positivity
  have H := (bare_blocks_limit.comp hdiv).add hrest
  rw [add_zero] at H
  exact H.congr' (Eventually.of_forall fun n => (prefix_split n).symm)

#print axioms bare_prefix_limit

/-- Exact limiting character numerator for each odd denominator divisible by three. -/
theorem row_character_numerator_limit {d : ℕ} [NeZero d] (hd : Odd d) (h3 : 3 ∣ d) :
    Tendsto (fun K => ∑ u : (ZMod d)ˣ,
      (chi (u:ZMod d).val:ℝ)*ThetaRowCorrelations.row d K (u:ZMod d).val)
      atTop (𝓝 (((2*∏ p∈d.primeFactors.erase 3,(1-chi p):ℤ):ℝ) *
        (Real.pi/(2*Real.sqrt 3)*∏ p∈d.primeFactors.erase 3,(1-(chi p:ℝ)/p)))) :=
  row_transform_limit bare_prefix_limit hd h3

#print axioms row_character_numerator_limit

end Arxiv.«2501.03234».ThetaCharacterNumerator
