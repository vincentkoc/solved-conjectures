import Erdos478IdealMertens
import Mathlib.Algebra.Order.Field.GeomSum

/-!
# First Mertens estimate for degree-one prime ideals

Separate the degree-one first powers in the log-norm convolution. All the
remaining prime powers give a bounded contribution after division by the cutoff.
-/

namespace Erdos478.IdealMertens
open NumberField Ideal Finset Erdos478.MeanDeficit Filter Topology

variable {K : Type*} [Field K] [NumberField K]

attribute [local instance] Int.ideal_span_isMaximal_of_prime

private theorem degree_sum_le (p : ℕ) (hp : p.Prime) :
    ∑ J ∈ abovePrime K p, J.inertiaDeg ℤ ≤ Module.finrank ℚ K := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let P := span {(p : ℤ)}
  let : Fintype (P.primesOver (𝓞 K)) := Fintype.ofFinite _
  have he : (↑(abovePrime K p) : Set _) = P.primesOver (𝓞 K) :=
    IsDedekindDomain.coe_primesOverFinset (p := P) (by simp [P,hp.ne_zero]) _
  let e := Equiv.setCongr he
  rw [← RingOfIntegers.rank,← Ideal.sum_ramification_inertia_eq_finrank P,← sum_coe_sort]
  apply (Fintype.sum_equiv e (fun J => J.val.inertiaDeg ℤ) (fun J => J.val.inertiaDeg ℤ)
    (fun _ => rfl)).le.trans
  apply sum_le_sum
  intro J _
  have : J.val.IsPrime := J.property.1
  exact Nat.le_mul_of_pos_left _ (J.val.ramificationIdx_pos ℤ)

private theorem sum_high_powers {p : ℕ} (hp : p.Prime) (X : ℕ) :
    ∑ j ∈ Icc 2 X, (p:ℝ)⁻¹ ^ j ≤ 2/(p:ℝ)^2 := by
  have h2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  have h0 : (0:ℝ) < p := by linarith
  rw [← Ico_add_one_right_eq_Icc]
  refine (geom_sum_Ico_le_of_lt_one (inv_nonneg.mpr h0.le) (inv_lt_one_of_one_lt₀ (by linarith))).trans ?_
  have hh : (p:ℝ)⁻¹ ≤ 1/2 := by rw [inv_eq_one_div]; gcongr
  rw [div_le_iff₀ (by linarith : 0 < 1-(p:ℝ)⁻¹),inv_pow]
  have hn : 0 ≤ ((p:ℝ)^2)⁻¹ := by positivity
  simp only [div_eq_mul_inv]
  nlinarith [mul_nonneg hn (sub_nonneg.mpr hh)]

private noncomputable def term (K : Type*) [Field K] [NumberField K] (X q j : ℕ) : ℝ :=
  (idealsUpTo K (X / q^j)).card

private theorem term_le (C : ℝ) (hC : ∀ y : ℝ, 0 ≤ y → ((idealsUpTo K ⌊y⌋₊).card : ℝ) ≤ C*y)
    (X q j : ℕ) : term K X q j ≤ C * X * (q:ℝ)⁻¹^j := by
  have h := hC ((X:ℝ) / (q^j : ℕ)) (by positivity)
  rw [Nat.floor_div_natCast,Nat.floor_natCast] at h
  simpa [term,Nat.cast_pow,div_eq_mul_inv,mul_assoc,inv_pow] using h

private noncomputable def localLog (K : Type*) [Field K] [NumberField K] (X : ℕ) (P : Ideal (𝓞 K)) :=
  ∑ j ∈ Icc 1 X, term K X (absNorm P) j * Real.log (absNorm P)

private noncomputable def leading (K : Type*) [Field K] [NumberField K] (X p : ℕ) (P : Ideal (𝓞 K)) :=
  if P.inertiaDeg ℤ = 1 then term K X p 1 * Real.log p else 0

private theorem local_error (C : ℝ) (hc : 0 ≤ C)
    (hC : ∀ y : ℝ, 0 ≤ y → ((idealsUpTo K ⌊y⌋₊).card : ℝ) ≤ C*y)
    {X p : ℕ} (hp : p.Prime) (hX : p ≤ X) {P : Ideal (𝓞 K)} (hP : P ∈ abovePrime K p) :
    0 ≤ localLog K X P - leading K X p P ∧
    localLog K X P - leading K X p P ≤
      C*X * (P.inertiaDeg ℤ : ℝ) * (3 * Real.log p / (p:ℝ)^2) := by
  classical
  let f := P.inertiaDeg ℤ
  let q := absNorm P
  have ⟨hn,hf⟩ := norm_over hp hP
  change q = p^f at hn
  have hpos : 0 < f := hf
  have hp' : (0:ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1:ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hlog := Real.log_nonneg hp1
  have hq : p ≤ q := by rw [hn]; simpa using Nat.pow_le_pow_right hp.pos (show 1≤f from hpos)
  have hlogq : Real.log q = f * Real.log p := by rw [hn,Nat.cast_pow,Real.log_pow]
  have logpos : 0 ≤ Real.log q := hlogq ▸ mul_nonneg (Nat.cast_nonneg f) hlog
  let T := ∑ j ∈ Icc 2 X, term K X q j * Real.log q
  have ts : 0 ≤ T := sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _) logpos
  have tail : T ≤ C*X*Real.log q * (2/(p:ℝ)^2) := by
    calc
      _ ≤ ∑ j ∈ Icc 2 X, (C*X*Real.log q) * (p:ℝ)⁻¹^j := by
        apply sum_le_sum
        intro j _
        calc
          _ ≤ (C*X*(q:ℝ)⁻¹^j)*Real.log q := mul_le_mul_of_nonneg_right (term_le C hC ..) logpos
          _ ≤ (C*X*(p:ℝ)⁻¹^j)*Real.log q := by gcongr
          _ = _ := by ring
      _ = (C*X*Real.log q) * (∑ j ∈ Icc 2 X, (p:ℝ)⁻¹^j) := by rw [mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (sum_high_powers hp X) (by positivity)
  have h1 : 1 ∈ Icc 1 X := mem_Icc.mpr ⟨le_rfl,hp.one_le.trans hX⟩
  have hloc : localLog K X P = term K X q 1 * Real.log q + T := by
    unfold localLog
    rw [← add_sum_erase _ _ h1,Icc_erase_left]
    rfl
  rw [hloc]
  by_cases he : f = 1
  · have eq : q = p := by simp [hn,he]
    simp only [leading,show P.inertiaDeg ℤ = 1 from he,if_true,eq,add_sub_cancel_left]
    refine ⟨ts,?_⟩
    rw [eq] at tail
    calc
      T ≤ _ := tail
      _ ≤ C*X*Real.log p * (3/(p:ℝ)^2) := by gcongr; norm_num
      _ = _ := by push_cast; ring
  · have hq2 : p^2 ≤ q := by rw [hn]; exact Nat.pow_le_pow_right hp.pos (by omega)
    have hb : term K X q 1 ≤ C * X / (p:ℝ)^2 := by
      have hh := term_le C hC X q 1
      rw [pow_one,← div_eq_mul_inv] at hh
      apply hh.trans
      gcongr
      exact_mod_cast hq2
    simp only [leading,show P.inertiaDeg ℤ ≠ 1 from he,if_false,sub_zero]
    refine ⟨add_nonneg (mul_nonneg (Nat.cast_nonneg _) logpos) ts,?_⟩
    apply (add_le_add (mul_le_mul_of_nonneg_right hb logpos) tail).trans_eq
    rw [hlogq]
    change _ = C*X*(f:ℝ)*(3*Real.log p/(p:ℝ)^2)
    ring

private theorem prime_log_square_sum :
    ∃ U : ℝ, 0 ≤ U ∧ ∀ X : ℕ, ∑ p ∈ Nat.primesLE X, Real.log p / (p:ℝ)^2 ≤ U := by
  let g (n : ℕ) := 2 * (n:ℝ)^(-(3/2 : ℝ))
  have hs : Summable g := (Real.summable_nat_rpow.mpr (by norm_num : -(3/2:ℝ) < -1)).mul_left 2
  have hg (n : ℕ) : 0 ≤ g n := by dsimp [g]; positivity
  refine ⟨∑' n, g n,tsum_nonneg hg,fun X => ?_⟩
  refine (sum_le_sum (g := g) ?_).trans (hs.sum_le_tsum _ (fun i _ => hg i))
  intro p hp
  have hpos := Nat.cast_pos (α := ℝ).mpr (Nat.mem_primesLE.mp hp).2.pos
  have hb := Real.log_le_rpow_div hpos.le (by norm_num : (0:ℝ)<1/2)
  apply (div_le_div_of_nonneg_right hb (sq_nonneg _)).trans_eq
  rw [show (p:ℝ)^2 = (p:ℝ)^(2:ℝ) by norm_num, div_div, mul_comm (1/2:ℝ), ← div_div,
    ← Real.rpow_sub hpos]
  dsimp [g]
  norm_num
  ring

private noncomputable def firstConvolution (K : Type*) [Field K] [NumberField K] (X : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE X, (linearCount K p : ℝ) * (term K X p 1 * Real.log p)

private theorem degree_one_convolution (K : Type*) [Field K] [NumberField K] :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ X : ℕ,
      0 ≤ (∑ I ∈ idealsUpTo K X, Real.log (absNorm I.val)) - firstConvolution K X ∧
      (∑ I ∈ idealsUpTo K X, Real.log (absNorm I.val)) - firstConvolution K X ≤ E*X := by
  classical
  obtain ⟨C,hc,hC⟩ := count_le_linear K
  obtain ⟨U,hU,hUs⟩ := prime_log_square_sum
  let d : ℝ := Module.finrank ℚ K
  have hd : 0 ≤ d := Nat.cast_nonneg _
  refine ⟨C*d*3*U,by positivity,fun X => ?_⟩
  let S := (Nat.primesLE X).biUnion (abovePrime K)
  have hs (J) (hJ : J ∈ S) : Irreducible J := by
    obtain ⟨p,hp,hm⟩ := mem_biUnion.mp hJ
    have hp' := (Nat.mem_primesLE.mp hp).2
    refine (Ideal.prime_of_isPrime ?_ ((mem_over hp' J).mp hm).1).irreducible
    intro h0
    have hN := (norm_over hp' hm).1
    rw [h0,absNorm_bot] at hN
    exact (pow_ne_zero _ hp'.ne_zero) hN.symm
  have he (p) : (linearCount K p : ℝ) * (term K X p 1 * Real.log p) =
      ∑ P ∈ abovePrime K p, leading K X p P := by
    simp only [leading,← sum_filter,sum_const,nsmul_eq_mul,linearCount]
  have hf : (∑ I ∈ idealsUpTo K X, Real.log (absNorm I.val)) =
      ∑ p ∈ Nat.primesLE X, ∑ P ∈ abovePrime K p, localLog K X P := by
    rw [log_norm_convolution X S hs (fun _ hi _ hj => primes_support_ideals X hi hj)]
    exact sum_biUnion (over_disjoint X)
  rw [hf,firstConvolution]
  simp_rw [he,← sum_sub_distrib]
  constructor
  · apply sum_nonneg
    intro p hp
    apply sum_nonneg
    intro P hP
    have ⟨hle,hp'⟩ := Nat.mem_primesLE.mp hp
    exact (local_error C hc hC hp' hle hP).1
  · calc
      _ ≤ ∑ p ∈ Nat.primesLE X, C*X*d*3 * (Real.log p/(p:ℝ)^2) := by
        apply sum_le_sum
        intro p hp
        have ⟨hle,hp'⟩ := Nat.mem_primesLE.mp hp
        have hl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp'.one_le)
        calc
          _ ≤ ∑ P ∈ abovePrime K p, C*X*(P.inertiaDeg ℤ:ℝ)*(3*Real.log p/(p:ℝ)^2) :=
            sum_le_sum (fun P hP => (local_error C hc hC hp' hle hP).2)
          _ = C*X*(∑ P ∈ abovePrime K p, (P.inertiaDeg ℤ:ℝ))*(3*Real.log p/(p:ℝ)^2) := by
            rw [mul_sum,sum_mul]
          _ ≤ C*X*d*(3*Real.log p/(p:ℝ)^2) := by
            gcongr
            dsimp [d]
            exact_mod_cast degree_sum_le (K := K) p hp'
          _ = _ := by ring
      _ = C*X*d*3 * ∑ p ∈ Nat.primesLE X, Real.log p / (p:ℝ)^2 := by rw [mul_sum]
      _ ≤ C*X*d*3*U := mul_le_mul_of_nonneg_left (hUs X) (by positivity)
      _ = _ := by ring

/-- The first Mertens sum restricted to prime ideals with residue degree one. -/
noncomputable def degreeOneWeight (K : Type*) [Field K] [NumberField K] (X : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE X, (linearCount K p : ℝ) * Real.log p / p

private theorem weighted_error (K : Type*) [Field K] [NumberField K] {ε : ℝ} (hε : 0<ε) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ X : ℕ,
      |(∑ I ∈ idealsUpTo K X, Real.log (absNorm I.val)) -
        dedekindZeta_residue K * X * degreeOneWeight K X| ≤
        ε*X*degreeOneWeight K X + B*X := by
  classical
  let d : ℝ := Module.finrank ℚ K
  let r := dedekindZeta_residue K
  let w (p : ℕ) := (linearCount K p : ℝ) * Real.log p
  have hw {p : ℕ} (hp : p.Prime) : 0 ≤ w p :=
    mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast hp.one_le))
  obtain ⟨C,hC,ha⟩ := ideal_count_error K hε
  obtain ⟨E,hE,hF⟩ := degree_one_convolution K
  have hd : 0 ≤ d := Nat.cast_nonneg _
  have hl : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  refine ⟨E+C*d*Real.log 4,by positivity,fun X => ?_⟩
  have hsum : ∑ p ∈ Nat.primesLE X, w p ≤ d * (Real.log 4 * X) := by
    calc
      _ ≤ ∑ p ∈ Nat.primesLE X, d * Real.log p := by
        apply sum_le_sum
        intro p hp
        have hpr := (Nat.mem_primesLE.mp hp).2
        exact mul_le_mul_of_nonneg_right (by dsimp [d]; exact_mod_cast linearCount_le (K := K) hpr)
          (Real.log_nonneg (by exact_mod_cast hpr.one_le))
      _ = d * Chebyshev.theta X := by rw [Chebyshev.theta_eq_sum_primesLE_log,mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg _)) hd
  have hf : firstConvolution K X = ∑ p ∈ Nat.primesLE X, w p * term K X p 1 :=
    sum_congr rfl (fun _ _ => by dsimp [w]; ring)
  have hdiff : firstConvolution K X - r*X*degreeOneWeight K X =
      ∑ p ∈ Nat.primesLE X, w p*(term K X p 1-r*((X:ℝ)/p)) := by
    rw [hf,degreeOneWeight,mul_sum,← sum_sub_distrib]
    apply sum_congr rfl
    intro p _
    dsimp [w]
    ring
  have hdif := Finset.abs_sum_le_sum_abs (fun p => w p*(term K X p 1-r*((X:ℝ)/p))) (Nat.primesLE X)
  have hs : |firstConvolution K X-r*X*degreeOneWeight K X| ≤ ε*X*degreeOneWeight K X + C*(d*(Real.log 4*X)) := by
    rw [hdiff]
    calc
      _ ≤ _ := hdif
      _ ≤ ∑ p ∈ Nat.primesLE X, w p*(ε*((X:ℝ)/p)+C) := by
        apply sum_le_sum
        intro p hp
        rw [abs_mul,abs_of_nonneg (hw (Nat.mem_primesLE.mp hp).2)]
        apply mul_le_mul_of_nonneg_left _ (hw (Nat.mem_primesLE.mp hp).2)
        have hh := ha ((X:ℝ)/p) (by positivity)
        simpa only [term,pow_one,Nat.floor_div_eq_div,r] using hh
      _ = ε*X*degreeOneWeight K X + C * ∑ p ∈ Nat.primesLE X, w p := by
        rw [degreeOneWeight,mul_sum,mul_sum,← sum_add_distrib]
        apply sum_congr rfl
        intro p _
        dsimp [w]
        ring
      _ ≤ _ := add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hsum hC)
  have htri := abs_sub_le (∑ I ∈ idealsUpTo K X, Real.log (absNorm I.val))
    (firstConvolution K X) (r*X*degreeOneWeight K X)
  rw [abs_of_nonneg (hF X).1] at htri
  calc
    _ ≤ _ := htri
    _ ≤ _ := add_le_add (hF X).2 hs
    _ = _ := by ring

private theorem weight_transfer {A S : ℕ → ℝ} {r : ℝ} (hr : 0<r)
    (hA : Tendsto A atTop (𝓝 r))
    (err : ∀ ε : ℝ, 0<ε → ∃ C : ℝ, ∀ᶠ X : ℕ in atTop,
      |A X-r*S X| ≤ ε*S X+C/Real.log X) :
    Tendsto S atTop (𝓝 1) := by
  have zero (C : ℝ) : Tendsto (fun X : ℕ => C / Real.log X) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  apply tendsto_order.mpr
  constructor
  · intro a ha
    let e := r*(1-a)/2
    have he : 0 < e := by dsimp [e]; positivity
    obtain ⟨C,hC⟩ := err e he
    have ht : Tendsto (fun X : ℕ => A X-C/Real.log X) atTop (𝓝 r) := by simpa using hA.sub (zero C)
    have hb : (r+e)*a < r := by
      have h := mul_lt_mul_of_pos_left ha he
      dsimp [e] at h ⊢
      nlinarith
    filter_upwards [ht.eventually_const_lt hb,hC] with X hX h
    by_contra! hh
    have hmul := mul_le_mul_of_nonneg_left hh (by linarith : 0 ≤ r+e)
    have h₁ := (abs_le.mp h).2
    linarith
  · intro b hb
    let e := r*(b-1)/(2*b)
    have hb' : 0 < b := by linarith
    have he : 0 < e := by dsimp [e]; positivity
    have heb : e*b = r*(b-1)/2 := by dsimp [e]; field_simp
    have her : 0 ≤ r-e := by nlinarith [mul_pos hb' hr]
    obtain ⟨C,hC⟩ := err e he
    have ht : Tendsto (fun X : ℕ => A X+C/Real.log X) atTop (𝓝 r) := by simpa using hA.add (zero C)
    have hlim : r < (r-e)*b := by nlinarith
    filter_upwards [ht.eventually_lt_const hlim,hC] with X hX h
    by_contra! hh
    have hmul := mul_le_mul_of_nonneg_left hh her
    have h₁ := (abs_le.mp h).1
    linarith

/-- The degree-one prime ideals have total log-weight asymptotic to log X. -/
theorem degree_one_mertens (K : Type*) [Field K] [NumberField K] :
    Tendsto (fun X : ℕ => degreeOneWeight K X / Real.log X) atTop (𝓝 1) := by
  apply weight_transfer (dedekindZeta_residue_pos K) (total_log_limit K)
  intro ε hε
  obtain ⟨B,_,hB⟩ := weighted_error K hε
  refine ⟨B,?_⟩
  filter_upwards [eventually_ge_atTop 2] with X hX
  have hx : (0:ℝ)<X := by exact_mod_cast (by omega : 0<X)
  have hl : 0 < Real.log X := Real.log_pos (by exact_mod_cast (by omega : 1<X))
  have h := div_le_div_of_nonneg_right (hB X) (mul_nonneg hx.le hl.le)
  rw [← abs_of_pos (mul_pos hx hl),← abs_div,abs_of_pos (mul_pos hx hl)] at h
  refine le_trans ?_ (h.trans_eq ?_)
  · apply le_of_eq
    congr 1
    field_simp
  · field_simp

#print axioms degree_one_mertens

end Erdos478.IdealMertens
