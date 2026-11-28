import ThetaRationalRows
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Algebra.BigOperators.Module

/-! The triangular contribution to the cotangent expansion of the theta sum. -/

namespace Arxiv.«2501.03234».ThetaCotangentTriangle

open Finset

/-- Parity of the least residue of the quotient in the prime field. -/
noncomputable def quotientSign (p : ℕ) [Fact p.Prime] (u v : ℕ) : ℤ :=
  if ((v : ZMod p) / (u : ZMod p)).val % 2 = 1 then 1 else -1

private def carry {p u : ℕ} (hc : p.Coprime u) (v : ℕ) : ZMod u :=
  -(v : ZMod u) * ↑(ZMod.unitOfCoprime p hc)⁻¹

private lemma carry_mul {p u : ℕ} (hc : p.Coprime u) (v : ℕ) :
    carry hc v * (p : ZMod u) = -v := by
  rw [carry, ← ZMod.coe_unitOfCoprime p hc, mul_assoc, Units.inv_mul, mul_one]

private lemma sign_eq_carry {p u v : ℕ} [Fact p.Prime] (hc : p.Coprime u)
    (hp : p%2=1) (hu : u%2=1) (hv : v%2=1) (hul : u<p) (hvl : v<p) :
    quotientSign p u v = if (carry hc v).val % 2 = 0 then 1 else -1 := by
  have hu0 : 0<u := by omega
  let : NeZero u := ⟨hu0.ne'⟩
  let k := (carry hc v).val
  have hk : k<u := ZMod.val_lt _
  have hd : u ∣ v+k*p := by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    push_cast
    change (v : ZMod u) + ((carry hc v).val : ZMod u) * p = 0
    rw [ZMod.natCast_zmod_val, carry_mul, add_neg_cancel]
  let r := (v+k*p)/u
  have he : r*u=v+k*p := Nat.div_mul_cancel hd
  have hr : r < p := by
    apply (Nat.mul_lt_mul_right hu0).mp
    rw [he]
    calc v+k*p < (k+1)*p := by nlinarith
         _ ≤ p*u := by rw [mul_comm p]; exact Nat.mul_le_mul_right p hk
  have hne : (u : ZMod p) ≠ 0 := by
    intro h; have := congrArg ZMod.val h
    rw [ZMod.val_natCast_of_lt hul,ZMod.val_zero] at this; omega
  have hq : (v : ZMod p)/(u : ZMod p) = r := by
    apply (div_eq_iff hne).mpr
    have hz := congrArg (fun n : ℕ => (n : ZMod p)) he
    push_cast at hz; simpa using hz.symm
  have hpar := congrArg (· % 2) he
  change (r*u)%2 = (v+k*p)%2 at hpar
  rw [Nat.mul_mod,hu,Nat.add_mod,hv,Nat.mul_mod k,hp] at hpar
  simp only [mul_one,Nat.mod_mod] at hpar
  simp only [quotientSign,hq,ZMod.val_natCast_of_lt hr]
  change (if r%2=1 then _ else _) = (if k%2=0 then _ else _)
  split_ifs <;> omega

private def parityWave {p u : ℕ} (hc : p.Coprime u) (i : ℕ) : ℤ :=
  (-1) ^ (carry hc (u+2*i)).val

private lemma wave_modulus {p u : ℕ} (hc : p.Coprime u) (hu : u%2=1) (j : ℕ) :
    ∑ i ∈ range u, parityWave hc (j+i) = 1 := by
  have hu0 : 0<u := by omega
  let : NeZero u := ⟨hu0.ne'⟩
  let key (i : ℕ) := (carry hc (u+2*(j+i))).val
  have hinj : Set.InjOn key (range u) := by
    intro a ha b hb h
    have he := congrArg (fun n : ℕ => (n : ZMod u) * p) h
    dsimp [key] at he
    simp only [ZMod.natCast_zmod_val,carry_mul,neg_inj,Nat.cast_add,Nat.cast_mul,
      Nat.cast_ofNat,ZMod.natCast_self,zero_add] at he
    have h2 : IsUnit (2 : ZMod u) := by
      have := (ZMod.unitOfCoprime 2 (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr hu))).isUnit
      simpa using this
    have hab : (a : ZMod u) = b := add_left_cancel (h2.mul_left_cancel he)
    simpa only [ZMod.val_natCast_of_lt (mem_range.mp ha),ZMod.val_natCast_of_lt (mem_range.mp hb)]
      using congrArg ZMod.val hab
  have him : (range u).image key = range u := by
    apply eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨i,_,rfl⟩ := mem_image.mp hx
      exact mem_range.mpr (ZMod.val_lt _)
    · rw [card_image_of_injOn hinj]
  have hw : ∑ t ∈ range u, (-1 : ℤ)^t = 1 := by
    have h := geom_sum_mul (-1 : ℤ) u
    rw [neg_one_pow_eq_pow_mod_two,hu,pow_one] at h
    linarith
  change ∑ i ∈ range u, (-1 : ℤ)^(key i) = 1
  rwa [← sum_image (f := fun n : ℕ => (-1 : ℤ)^n) hinj,him]

private lemma wave_prefix {p u : ℕ} (hc : p.Coprime u) (hu : u%2=1) (n : ℕ) :
    -(u/2 : ℕ) ≤ (∑ i ∈ range n, parityWave hc i : ℤ) := by
  have hu0 : 0<u := by omega
  have hw (i : ℕ) : parityWave hc i = 1 ∨ parityWave hc i = -1 := by
    dsimp [parityWave]; rw [neg_one_pow_eq_ite]; split <;> simp
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : u ≤ n
    · have h := ih (n-u) (by omega)
      rw [← Nat.sub_add_cancel hn, sum_range_add, wave_modulus hc hu]
      omega
    · have h₁ := card_nsmul_le_sum (range n) (parityWave hc) (-1) (fun i _ => by rcases hw i with h|h <;> omega)
      have h₂ := sum_le_card_nsmul (range (u-n)) (fun i => parityWave hc (n+i)) 1
        (fun i _ => by rcases hw (n+i) with h|h <;> omega)
      have ht := sum_range_add (parityWave hc) n (u-n)
      rw [Nat.add_sub_of_le (by omega : n≤u)] at ht
      have he := wave_modulus hc hu 0
      simp only [zero_add] at he
      simp only [card_range,nsmul_eq_mul,mul_one,mul_neg,mul_one] at h₁ h₂
      rw [Nat.cast_sub (by omega : n≤u)] at h₂
      rw [he] at ht
      by_cases h : n≤u/2
      · exact (neg_le_neg (by exact_mod_cast h : (n:ℤ) ≤ (u/2 : ℕ))).trans h₁
      · have hd : (u : ℤ) - n ≤ (u/2 : ℕ) + 1 := by omega
        linarith only [ht,h₂,hd]

/-- A prefix of the upper Fourier triangle has deficit at most half its odd denominator. -/
theorem quotient_prefix_lower {p u : ℕ} [Fact p.Prime] (hp : p%2=1) (hu : u%2=1)
    (hul : u<p) (n : ℕ) (hn : ∀ i<n, u+2*i<p) :
    -(u/2 : ℕ) ≤ (∑ i ∈ range n, quotientSign p u (u+2*i) : ℤ) := by
  have hc : p.Coprime u := (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
    (fun h => hul.not_ge (Nat.le_of_dvd (by omega) h))
  have he (i : ℕ) (hi : i ∈ range n) : quotientSign p u (u+2*i) = parityWave hc i := by
    rw [sign_eq_carry hc hp hu (by omega) hul (hn i (mem_range.mp hi))]
    simp [parityWave,neg_one_pow_eq_ite,Nat.even_iff]
  rw [sum_congr rfl he]
  exact wave_prefix hc hu n

theorem weighted_prefix_lower (w g : ℕ → ℝ) {n : ℕ} {D : ℝ} (hD : 0≤D) (hw₀ : 0≤w 0)
    (hw : ∀ i<n, 0≤w i) (hm : ∀ i, i+1<n → w (i+1)≤w i)
    (hg : ∀ k≤n, -D ≤ ∑ i ∈ range k, g i) :
    -D * w 0 ≤ ∑ i ∈ range n, w i * g i := by
  by_cases hn : n=0
  · simp [hn, neg_mul]
    exact mul_nonneg hD hw₀
  have step (k : ℕ) (hk : k+1≤n) :
      w k * (D + ∑ i ∈ range (k+1), g i) ≤
        D*w 0 + ∑ i ∈ range (k+1), w i*g i := by
    induction k with
    | zero => simp; ring_nf; rfl
    | succ k ih =>
      have hpos : 0 ≤ D + ∑ i ∈ range (k+1), g i := by linarith [hg (k+1) (by omega)]
      have h := (mul_le_mul_of_nonneg_right (hm k (by omega)) hpos).trans (ih (by omega))
      rw [sum_range_succ (f := g),sum_range_succ (f := fun i => w i*g i)]
      linarith
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have hh := step k (le_refl _)
  have hpos : 0≤ w k * (D + ∑ i ∈ range (k+1), g i) := by
    apply mul_nonneg (hw k (by omega)); linarith [hg (k+1) (le_refl _)]
  linarith

private noncomputable def angle (p u : ℕ) : ℝ := Real.pi * u / (2*p)

/-- Positive Fourier weight at an odd frequency index. -/
noncomputable def weight (p u : ℕ) : ℝ := (Real.tan (angle p u))⁻¹

private lemma angle_mem {p u : ℕ} (hu : 0<u) (hul : u<p) :
    0<angle p u ∧ angle p u<Real.pi/2 := by
  have hp : 0<(p:ℝ) := by exact_mod_cast hu.trans hul
  have huu : (u:ℝ)<p := by exact_mod_cast hul
  constructor
  · dsimp [angle]; positivity
  · rw [angle, div_lt_iff₀ (by positivity)]
    nlinarith [mul_lt_mul_of_pos_left huu Real.pi_pos]

theorem weight_pos {p u : ℕ} (hu : 0<u) (hul : u<p) : 0<weight p u :=
  inv_pos.mpr (Real.tan_pos_of_pos_of_lt_pi_div_two (angle_mem hu hul).1 (angle_mem hu hul).2)

theorem weight_antitone {p u v : ℕ} (hu : 0<u) (hv : v<p) (huv : u≤v) :
    weight p v ≤ weight p u := by
  have ha := angle_mem hu (lt_of_le_of_lt huv hv)
  have hb := angle_mem (hu.trans_le huv) hv
  have htan := Real.strictMonoOn_tan.monotoneOn
    (show angle p u ∈ Set.Ioo (-(Real.pi/2)) (Real.pi/2) from ⟨by linarith [Real.pi_pos],ha.2⟩)
    (show angle p v ∈ Set.Ioo (-(Real.pi/2)) (Real.pi/2) from ⟨by linarith [Real.pi_pos],hb.2⟩)
    (show angle p u ≤ angle p v by
      unfold angle; gcongr)
  exact inv_anti₀ (Real.tan_pos_of_pos_of_lt_pi_div_two ha.1 ha.2) htan

theorem weight_upper {p u : ℕ} (hu : 0<u) (hul : u<p) :
    weight p u ≤ 2*p/(Real.pi*u) := by
  have ha := angle_mem hu hul
  have h := inv_anti₀ ha.1 (Real.le_tan ha.1.le ha.2)
  simpa [weight,angle,inv_div] using h

/-- The part of a frequency row whose odd numerator is at least its odd denominator. -/
noncomputable def upperRow (p : ℕ) [Fact p.Prime] (u : ℕ) : ℝ :=
  ∑ i ∈ range ((p-u)/2), weight p (u+2*i) * quotientSign p u (u+2*i)

/-- The negative contribution of an upper frequency row is at most p/π. -/
theorem upperRow_lower {p u : ℕ} [Fact p.Prime] (hp : p%2=1) (hu : u%2=1) (hul : u<p) :
    -(p:ℝ)/Real.pi ≤ upperRow p u := by
  have hu0 : 0<u := by omega
  let n := (p-u)/2
  have hlt (i : ℕ) (hi : i<n) : u+2*i<p := by dsimp [n] at hi; omega
  have hw := weighted_prefix_lower (fun i => weight p (u+2*i))
    (fun i => (quotientSign p u (u+2*i) : ℝ)) (n := n) (D := (u/2 : ℕ))
    (by positivity) (by simpa using (weight_pos hu0 hul).le)
    (fun i hi => (weight_pos (by omega) (hlt i hi)).le)
    (fun i hi => weight_antitone (by omega) (hlt _ hi) (by omega))
    (fun k hk => by exact_mod_cast quotient_prefix_lower hp hu hul k (fun i hi => hlt i (hi.trans_le hk)))
  simp only [mul_zero,add_zero] at hw
  apply le_trans _ hw
  have hhalf : (2:ℝ) * (u/2 : ℕ) ≤ u := by exact_mod_cast (show 2*(u/2)≤u by omega)
  have hub := mul_le_mul_of_nonneg_left (weight_upper hu0 hul) (show 0≤((u/2:ℕ):ℝ) by positivity)
  have hup : 0<(u:ℝ) := by exact_mod_cast hu0
  have hp0 : 0<(p:ℝ) := by exact_mod_cast hu0.trans hul
  have hr : ((u/2:ℕ):ℝ)*(2*p/(Real.pi*u)) ≤ p/Real.pi := by
    field_simp [Real.pi_pos.ne',hup.ne']
    nlinarith [mul_le_mul_of_nonneg_right hhalf hp0.le]
  simpa only [neg_div,neg_mul] using neg_le_neg (hub.trans hr)

private lemma weight_lower {p u : ℕ} (hu : 0<u) (hut : 3*u≤p) :
    3*p/(2*Real.pi*u) ≤ weight p u := by
  have hul : u<p := by omega
  have ha := angle_mem hu hul
  have hp : 0<(p:ℝ) := by exact_mod_cast hu.trans hul
  have hur : 0<(u:ℝ) := by exact_mod_cast hu
  have h₆ : angle p u ≤ Real.pi / 6 := by
    rw [angle, div_le_iff₀ (by positivity)]
    have h : (3:ℝ)*u ≤ p := by exact_mod_cast hut
    nlinarith [mul_le_mul_of_nonneg_left h Real.pi_pos.le]
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi ha.1.le (by linarith [Real.pi_pos]) h₆
  rw [Real.cos_pi_div_six] at hcos
  have hc : (3:ℝ)/4 ≤ Real.cos (angle p u) := by
    nlinarith [Real.sq_sqrt (by norm_num : 0≤(3:ℝ)),Real.sqrt_nonneg (3:ℝ)]
  have hs := Real.sin_le ha.1.le
  have hsp := Real.sin_pos_of_pos_of_lt_pi ha.1 (by linarith [ha.2,Real.pi_pos])
  rw [weight,Real.tan_eq_sin_div_cos,inv_div,le_div_iff₀ hsp]
  calc 3*p/(2*Real.pi*u)*Real.sin (angle p u)
        ≤ 3*p/(2*Real.pi*u)*angle p u := by gcongr
       _ = 3/4 := by dsimp [angle]; field_simp; ring
       _ ≤ _ := hc

private noncomputable def mass (p : ℕ) : ℝ :=
  ∑ j ∈ range (p/2), weight p (2*j+1)

private lemma mass_lower {p : ℕ} (hp : 0<p) :
    (3*p/(4*Real.pi) : ℝ) * harmonic (p/6) ≤ mass p := by
  have hp0 : 0<(p:ℝ) := by exact_mod_cast hp
  have hmass : (harmonic (p/6) : ℝ) = ∑ j ∈ range (p/6), ((j:ℝ)+1)⁻¹ := by
    simp [harmonic]
  rw [hmass,mul_sum]
  calc
    _ ≤ ∑ j ∈ range (p/6), weight p (2*j+1) := by
      apply sum_le_sum; intro j hj
      have hj' := mem_range.mp hj
      apply le_trans _ (weight_lower (by omega) (by omega : 3*(2*j+1)≤p))
      push_cast
      rw [← div_eq_mul_inv]
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      field_simp
      nlinarith [Real.pi_pos]
    _ ≤ mass p := by
      apply sum_le_sum_of_subset_of_nonneg (range_mono (by omega : p/6≤p/2))
      intro j hj _
      have := mem_range.mp hj
      exact (weight_pos (by omega) (by omega)).le

/-- Contribution from the triangular set of odd frequencies with numerator at least denominator. -/
noncomputable def upperTriangle (p : ℕ) [Fact p.Prime] : ℝ :=
  2/(p:ℝ) * ∑ j ∈ range (p/2), weight p (2*j+1) * upperRow p (2*j+1)

private lemma upperRow_one {p : ℕ} [Fact p.Prime] (hp : p%2=1) : upperRow p 1 = mass p := by
  rw [upperRow,mass,show (p-1)/2=p/2 by omega]
  apply sum_congr rfl; intro j hj
  have hh := mem_range.mp hj
  have ho : (1+2*j)%2=1 := by omega
  have hs : quotientSign p 1 (1+2*j) = 1 := by
    simp only [quotientSign,Nat.cast_one,div_one,ZMod.val_natCast_of_lt (show 1+2*j<p by omega),ho,if_true]
  rw [hs]; simp [add_comm 1]

/-- The upper triangle alone dominates a positive harmonic multiple of p. -/
theorem upperTriangle_harmonic {p : ℕ} [Fact p.Prime] (hp : p%2=1) :
    3*p/(4*Real.pi^2)*harmonic (p/6) ≤ upperTriangle p := by
  have hp₂ := (Fact.out : p.Prime).two_le
  have hp0 : 0<(p:ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hmass : 0 ≤ mass p := by
    apply sum_nonneg; intro j hj
    have hj' := mem_range.mp hj
    exact (weight_pos (by omega) (by omega)).le
  have h₀ : 0 ∈ range (p/2) := mem_range.mpr (by omega)
  let a (j : ℕ) := weight p (2*j+1)
  have hnon (j : ℕ) (hj : j ∈ range (p/2)) : 0≤a j := by
    have hj' := mem_range.mp hj; exact (weight_pos (by omega) (by omega)).le
  have htail := sum_le_sum (s := (range (p/2)).erase 0) (fun j hj =>
    mul_le_mul_of_nonneg_left (upperRow_lower hp (show (2*j+1)%2=1 by omega)
      (show 2*j+1<p by have := mem_range.mp (mem_erase.mp hj).2; omega)) (hnon j (mem_erase.mp hj).2))
  change ∑ j ∈ (range (p/2)).erase 0, a j * (-(p:ℝ)/Real.pi) ≤ _ at htail
  rw [← sum_mul] at htail
  have ha : (∑ j ∈ (range (p/2)).erase 0, a j) ≤ mass p :=
    sum_le_sum_of_subset_of_nonneg (erase_subset ..) (fun j hj _ => hnon j hj)
  have he : mass p * (-(p:ℝ)/Real.pi) ≤ _ :=
    (mul_le_mul_of_nonpos_right ha (div_nonpos_of_nonpos_of_nonneg (by linarith) Real.pi_pos.le)).trans htail
  have hw := weight_lower (p := p) (u := 1) (by decide) (by omega)
  simp only [Nat.cast_one,mul_one] at hw
  have hcore : p/(2*Real.pi) * mass p ≤
      ∑ j ∈ range (p/2), a j * upperRow p (2*j+1) := by
    rw [← sum_erase_add _ _ h₀]
    simp only [mul_zero,zero_add,upperRow_one hp,a] at *
    have hww := mul_le_mul_of_nonneg_right hw hmass
    calc _ = mass p * (-(p:ℝ)/Real.pi) + 3*p/(2*Real.pi)*mass p := by field_simp; ring
         _ ≤ _ := add_le_add he hww
  have hfront := mul_le_mul_of_nonneg_left hcore (by positivity : 0≤2/(p:ℝ))
  have hm := mul_le_mul_of_nonneg_right (mass_lower (p := p) (by omega)) (inv_nonneg.mpr Real.pi_pos.le)
  change _ ≤ 2/(p:ℝ) * ∑ j ∈ range (p/2), a j * upperRow p (2*j+1)
  apply le_trans _ hfront
  convert hm using 1 <;> field_simp

open ThetaDiagonal (U sign rep oddReps)
open ThetaRationalRows (row)

variable {p : ℕ} [Fact p.Prime]

noncomputable def coeff (t : ZMod p) : ℂ :=
  ∑ x : U p, (sign x : ℂ) * ZMod.stdAddChar ((x : ZMod p)*t)

private lemma coeff_neg (hp : p%2=1) (t : ZMod p) : coeff (-t) = -coeff t := by
  have e := Equiv.sum_comp (Equiv.neg (U p))
    (fun x : U p => (sign x : ℂ) * ZMod.stdAddChar ((x : ZMod p)*(-t)))
  change (∑ x : U p, (sign (-x) : ℂ) * ZMod.stdAddChar (((-x : U p) : ZMod p) * (-t))) = coeff (-t) at e
  rw [← e]
  simp [ThetaDiagonal.sign_neg hp,coeff,sum_neg_distrib]

private lemma char_sum (x : ZMod p) :
    ∑ t : ZMod p, ZMod.stdAddChar (x*t) = if x=0 then (p : ℂ) else 0 := by
  split_ifs with hx
  · simp [hx,ZMod.card]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar p hx)

private lemma row_transform (a : U p) :
    (p:ℂ) * (row a : ℂ) = ∑ t : ZMod p, coeff t * coeff (-(a:ZMod p)*t) := by
  let A (x y : U p) := (sign x : ℂ)*(sign y : ℂ)
  have hprod (t : ZMod p) : coeff t * coeff (-(a:ZMod p)*t) =
      ∑ y : U p, ∑ x : U p, A x y * ZMod.stdAddChar (((x:ZMod p) - ((a*y : U p) : ZMod p))*t) := by
    rw [coeff,coeff,mul_sum]
    apply sum_congr rfl; intro y _
    rw [sum_mul]
    apply sum_congr rfl; intro x _
    dsimp [A]
    rw [mul_mul_mul_comm, ← AddChar.map_add_eq_mul]
    congr 2
    ring
  simp_rw [hprod]
  rw [sum_comm]
  simp_rw [sum_comm (s := (univ : Finset (ZMod p))) (t := (univ : Finset (U p))), ← mul_sum,char_sum]
  have hy (y : U p) :
      ∑ x : U p, A x y * (if (x:ZMod p)-((a*y:U p) : ZMod p)=0 then (p:ℂ) else 0) = p * A (a*y) y := by
    simp only [sub_eq_zero,Units.val_inj,mul_ite,mul_zero,sum_ite_eq',mem_univ,if_true]
    ring
  simp_rw [hy]
  simp only [row,Int.cast_sum,Int.cast_mul,A,← mul_sum]
  congr 1
  apply sum_congr rfl; intro x _; ring

private lemma sum_nonzero {M : Type*} [AddCommMonoid M] (f : ZMod p → M) (hf : f 0 = 0) :
    ∑ t : ZMod p, f t = ∑ t : U p, f t := by
  rw [← sum_erase_add _ _ (mem_univ (0 : ZMod p)),hf,add_zero]
  symm
  apply sum_bij (fun (t : U p) _ => (t : ZMod p))
  · intro t _; exact mem_erase.mpr ⟨t.ne_zero,mem_univ _⟩
  · intro a _ b _ hab; exact Units.ext hab
  · intro b hb
    exact ⟨Units.mk0 b (mem_erase.mp hb).1,mem_univ _,rfl⟩
  · intros; rfl

private lemma S_twice_rows (hp : p%2=1) :
    2*(S p : ℂ) = ∑ a : U p, (sign a : ℂ)*(row a : ℂ) := by
  rw [ThetaDiagonal.sum_by_sign hp,ThetaRationalRows.S_eq_sum_rows hp,Int.cast_sum,mul_sum]
  apply sum_congr rfl; intro a ha
  have hsign : sign a = 1 := if_pos (mem_filter.mp ha).2
  simp [ThetaDiagonal.sign_neg hp,ThetaRationalRows.row_neg hp,hsign,two_mul]

private lemma coeff_rational (hp : p%2=1) (t : ZMod p) :
    coeff t * (1+ZMod.stdAddChar t) = ZMod.stdAddChar t-1 := by
  let z := ZMod.stdAddChar t
  have hpow (n : ℕ) : ZMod.stdAddChar ((n:ZMod p)*t) = z^n := by
    simpa only [nsmul_eq_mul,z] using ZMod.stdAddChar.map_nsmul_eq_pow n t
  have hz : z^p=1 := by rw [← hpow]; simp
  have hx (a : U p) : (sign a : ℂ)*ZMod.stdAddChar ((a:ZMod p)*t) = -(-z)^(rep a) := by
    have ht : ZMod.stdAddChar ((a:ZMod p)*t) = z^(rep a) := by
      simpa [rep] using hpow (rep a)
    rw [ht]
    by_cases ho : rep a%2=1
    · rw [show sign a=1 by exact if_pos ho,(Nat.odd_iff.mpr ho).neg_pow]
      simp
    · rw [show sign a= -1 by exact if_neg ho,(Nat.even_iff.mpr (by omega : rep a%2=0)).neg_pow]
      simp
  have hrel : coeff t = 1 - ∑ n ∈ range p, (-z)^n := by
    simp only [coeff,hx,sum_neg_distrib,← ThetaDiagonal.sum_units,
      sum_Ico_eq_sub _ (Fact.out : p.Prime).one_le,sum_range_one,pow_zero]
    ring
  have hg := geom_sum_mul (-z) p
  rw [(Nat.odd_iff.mpr hp).neg_pow,hz] at hg
  change coeff t*(1+z)=z-1
  rw [hrel]
  linear_combination hg

private lemma coeff_at_nat (hp : p%2=1) (k : ℕ) (hk : 2*k<p) :
    coeff (k : ZMod p) = Complex.I * (Real.tan (Real.pi*k/p) : ℂ) := by
  let x := Real.pi*k/p
  have hp0 : 0<(p:ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hx₀ : 0≤x := by dsimp [x]; positivity
  have hx₁ : x<Real.pi/2 := by
    dsimp [x]; rw [div_lt_iff₀ hp0]
    have hk' : (2:ℝ)*k < p := by exact_mod_cast hk
    nlinarith [mul_lt_mul_of_pos_left hk' Real.pi_pos]
  have hcos : Complex.cos (x:ℂ) ≠ 0 := by
    rw [← Complex.ofReal_cos,Complex.ofReal_ne_zero]
    exact (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],hx₁⟩).ne'
  let E := Complex.exp ((x:ℂ)*Complex.I)
  have hE : E≠0 := Complex.exp_ne_zero _
  have hneg : Complex.exp (-(x:ℂ)*Complex.I)=E⁻¹ := by
    rw [neg_mul,Complex.exp_neg]
  have hz : ZMod.stdAddChar (k : ZMod p) = E^2 := by
    rw [← Int.cast_natCast k,ZMod.stdAddChar_coe]
    dsimp [E,x]; rw [← Complex.exp_nat_mul]
    push_cast; congr 1; ring
  have hplus : 1+E^2 = (2 * Complex.cos (x:ℂ))*E := by
    rw [Complex.two_cos,hneg]; change _=(E+E⁻¹)*E
    field_simp; ring
  have hminus : E^2-1 = Complex.I*(2*Complex.sin (x:ℂ))*E := by
    rw [Complex.two_sin,hneg]; change _=Complex.I*((E⁻¹-E)*Complex.I)*E
    have hi := Complex.I_mul_I
    field_simp
    linear_combination (E^2-1)*hi
  have h := coeff_rational hp (k:ZMod p)
  rw [hz,hplus,hminus] at h
  change coeff (k:ZMod p) = Complex.I * (Real.tan x : ℂ)
  rw [Complex.ofReal_tan,Complex.tan]
  field_simp
  apply mul_right_cancel₀ hE
  linear_combination h/2

private def dilation (hp : p%2=1) : U p :=
  -(ZMod.unitOfCoprime 2 (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr hp)))⁻¹

private lemma coeff_dilated (hp : p%2=1) (a : U p) (ha : a∈oddReps p) :
    coeff ((dilation hp : ZMod p)*(a : ZMod p)) = Complex.I * (weight p (rep a) : ℂ) := by
  have hodd := (mem_filter.mp ha).2
  change rep a%2=1 at hodd
  have hlt : rep a<p := ZMod.val_lt _
  let k := (p-rep a)/2
  have hn : 2*k+rep a=p := by dsimp [k]; omega
  have hk : 2*k<p := by omega
  let two := ZMod.unitOfCoprime 2 (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr hp))
  have htwo : (two : ZMod p)=2 := ZMod.coe_unitOfCoprime ..
  have hd : (two:ZMod p)*(dilation hp : ZMod p) = -1 := by
    change (two:ZMod p)*(-↑two⁻¹) = -1
    rw [mul_neg,Units.mul_inv]
  have hz := congrArg (fun n : ℕ => (n : ZMod p)) hn
  push_cast at hz
  have ha' : (rep a : ZMod p) = a := ZMod.natCast_zmod_val _
  rw [ha',ZMod.natCast_self] at hz
  have he : (dilation hp : ZMod p)*a = k := by
    apply two.isUnit.mul_left_cancel
    rw [← mul_assoc,hd,htwo,neg_one_mul]; linear_combination -hz
  rw [he,coeff_at_nat hp k hk]
  have hp0 : 0<(p:ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have heq : Real.pi*k/p = Real.pi/2-angle p (rep a) := by
    dsimp [angle]; field_simp
    have hr : (2:ℝ)*k + rep a = p := by exact_mod_cast hn
    nlinarith [congrArg (Real.pi * ·) hr]
  rw [heq,Real.tan_pi_div_two_sub,weight]

private lemma row_dilated (hp : p%2=1) (a d : U p) :
    (p:ℂ)*(row a : ℂ) = -(∑ t : U p,
      coeff ((d*t : U p) : ZMod p) * coeff ((d*(a*t) : U p) : ZMod p)) := by
  have hzero : coeff (0 : ZMod p) = 0 := by
    have h := coeff_neg hp (0:ZMod p)
    rw [neg_zero] at h; linear_combination h/2
  rw [row_transform,sum_nonzero _ (by simp [hzero])]
  rw [← Equiv.sum_comp (Equiv.mulLeft d)]
  simp only [Equiv.coe_mulLeft,Units.val_mul,neg_mul,coeff_neg hp,mul_neg,sum_neg_distrib]
  apply congrArg Neg.neg
  apply sum_congr rfl; intro t _
  ring_nf

private lemma sum_even (hp : p%2=1) (f : U p → ℂ) (h : ∀ x, f (-x)=f x) :
    ∑ x : U p, f x = 2*∑ x ∈ oddReps p, f x := by
  rw [ThetaDiagonal.sum_by_sign hp,mul_sum]
  apply sum_congr rfl; intro x _; rw [h,two_mul]

private lemma full_transform (hp : p%2=1) (d : U p) :
    2*p*(S p : ℂ) = -(∑ t : U p, ∑ v : U p,
      (sign (v/t) : ℂ)*coeff ((d*t : U p):ZMod p)*coeff ((d*v : U p):ZMod p)) := by
  rw [show 2*(p:ℂ)*(S p : ℂ)=p*(2*(S p : ℂ)) by ring,S_twice_rows hp,mul_sum]
  have hr (a : U p) : (p:ℂ)*((sign a : ℂ)*(row a : ℂ)) =
      -(∑ t : U p, (sign a : ℂ)*coeff ((d*t:U p):ZMod p)*coeff ((d*(a*t):U p):ZMod p)) := by
    rw [mul_left_comm, row_dilated hp a d,mul_neg,mul_sum]
    simp only [mul_assoc]
  simp_rw [hr]
  rw [sum_neg_distrib,sum_comm]
  apply congrArg Neg.neg
  apply sum_congr rfl; intro t _
  have e := Equiv.sum_comp (Equiv.mulRight t)
    (fun v : U p => (sign (v/t) : ℂ)*coeff ((d*t:U p):ZMod p)*coeff ((d*v:U p):ZMod p))
  simpa using e

private lemma odd_transform (hp : p%2=1) :
    (p:ℝ)*(S p : ℝ) = 2*∑ t ∈ oddReps p, ∑ v ∈ oddReps p,
      (sign (v/t) : ℝ)*weight p (rep t)*weight p (rep v) := by
  let d := dilation hp
  let g (t v : U p) := (sign (v/t) : ℂ)*coeff ((d*t:U p):ZMod p)*coeff ((d*v:U p):ZMod p)
  have ht (t v : U p) : g (-t) v=g t v := by
    simp [g,div_neg,mul_neg,ThetaDiagonal.sign_neg hp,coeff_neg hp]
  have hv (t v : U p) : g t (-v)=g t v := by
    simp [g,neg_div,mul_neg,ThetaDiagonal.sign_neg hp,coeff_neg hp]
  have h := full_transform hp d
  change 2*p*(S p : ℂ) = -(∑ t : U p, ∑ v : U p, g t v) at h
  rw [sum_even hp _ (by intro t; simp only [ht])] at h
  simp_rw [sum_even hp _ (hv _)] at h
  have hodd (t : U p) (ht : t∈oddReps p) (v : U p) (hv : v∈oddReps p) :
      g t v = -((sign (v/t):ℂ)*(weight p (rep t):ℂ)*(weight p (rep v):ℂ)) := by
    dsimp only [g,d]
    rw [Units.val_mul,coeff_dilated hp t ht,Units.val_mul,coeff_dilated hp v hv]
    linear_combination (sign (v/t):ℂ)*(weight p (rep t):ℂ)*(weight p (rep v):ℂ)*Complex.I_mul_I
  have hsum (t : U p) (ht : t∈oddReps p) := sum_congr rfl (hodd t ht)
  have hmain := sum_congr rfl (fun t ht => congrArg (fun z : ℂ => 2*z) (hsum t ht))
  rw [hmain] at h
  simp only [sum_neg_distrib,mul_neg,← mul_sum,neg_neg] at h
  apply Complex.ofReal_injective
  push_cast
  linear_combination h/2

theorem sum_odd_indices (hp : p%2=1) {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∑ a ∈ oddReps p, f (rep a) = ∑ j ∈ range (p/2), f (2*j+1) := by
  apply sum_bij (fun (a : U p) _ => rep a/2)
  · intro a ha
    have ho : rep a%2=1 := (mem_filter.mp ha).2
    have hl : rep a<p := ZMod.val_lt _
    exact mem_range.mpr (by omega)
  · intro a ha b hb he
    have h₁ : rep a%2=1 := (mem_filter.mp ha).2
    have h₂ : rep b%2=1 := (mem_filter.mp hb).2
    exact Units.ext (ZMod.val_injective p (show rep a=rep b by omega))
  · intro j hj
    have hl : 2*j+1<p := by have := mem_range.mp hj; omega
    have hn : ((2*j+1 : ℕ) : ZMod p)≠0 := by
      intro h; have := congrArg ZMod.val h
      rw [ZMod.val_natCast_of_lt hl,ZMod.val_zero] at this; omega
    let a := Units.mk0 _ hn
    have hrep : rep a=2*j+1 := ZMod.val_natCast_of_lt hl
    exact ⟨a,mem_filter.mpr ⟨mem_univ _,by rw [hrep]; omega⟩,by rw [hrep]; omega⟩
  · intro a ha
    have ho : rep a%2=1 := (mem_filter.mp ha).2
    congr 1; omega

/-- Discrete cotangent expansion of the pinned integer theta sum. -/
theorem S_cotangent (hp : p%2=1) :
    (p:ℝ)*(S p : ℝ) = 2*∑ j ∈ range (p/2), weight p (2*j+1) *
      ∑ k ∈ range (p/2), weight p (2*k+1)*quotientSign p (2*j+1) (2*k+1) := by
  have h (t v : U p) : sign (v/t)=quotientSign p (rep t) (rep v) := by
    simp only [sign,quotientSign,rep,ZMod.natCast_zmod_val,Units.val_div_eq_div_val]
  rw [odd_transform hp]
  congr 1
  simp_rw [h]
  let f (u v : ℕ) := weight p v*(quotientSign p u v : ℝ)
  calc
    _ = ∑ t ∈ oddReps p, weight p (rep t) * ∑ v ∈ oddReps p, f (rep t) (rep v) := by
      apply sum_congr rfl; intro t _
      rw [mul_sum]; apply sum_congr rfl; intro v _; dsimp [f]; ring
    _ = _ := by
      simp_rw [sum_odd_indices hp]
      exact sum_odd_indices hp (fun u => weight p u * ∑ k ∈ range (p/2), f u (2*k+1))

/-- On the lower triangle, the sign is read modulo the smaller odd denominator. -/
noncomputable def reciprocalSign (p u v : ℕ) : ℤ :=
  if ((v : ZMod u)*(p : ZMod u)⁻¹).val%2=1 then 1 else -1

theorem quotient_eq_reciprocal (hp : p%2=1) {u v : ℕ} (hu : u%2=1) (hv : v%2=1)
    (hvu : v<u) (hul : u<p) : quotientSign p u v = reciprocalSign p u v := by
  have hc : p.Coprime u := (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
    (fun h => hul.not_ge (Nat.le_of_dvd (by omega) h))
  let : NeZero u := ⟨by omega⟩
  let r := (v : ZMod u)*(p : ZMod u)⁻¹
  have hr : r≠0 := by
    intro he
    have hh := congrArg (·*(p:ZMod u)) he
    dsimp [r] at hh
    rw [mul_assoc,mul_comm ((p:ZMod u)⁻¹),ZMod.coe_mul_inv_eq_one p hc,mul_one,zero_mul] at hh
    have := congrArg ZMod.val hh
    rw [ZMod.val_natCast_of_lt hvu,ZMod.val_zero] at this; omega
  have he : carry hc v = -r := by change -(v:ZMod u)*(p:ZMod u)⁻¹= -_; rw [neg_mul]
  let : NeZero r := ⟨hr⟩
  rw [sign_eq_carry hc hp hu hv hul (hvu.trans hul),he,ZMod.val_neg_of_ne_zero r]
  change (if (u-r.val)%2=0 then _ else _) = (if r.val%2=1 then _ else _)
  have := ZMod.val_lt r
  split_ifs <;> omega

/-- Complementary triangular sum; each arithmetic sign uses modulus 2j+1. -/
noncomputable def lowerTriangle (p : ℕ) : ℝ :=
  2/(p:ℝ) * ∑ j ∈ range (p/2), weight p (2*j+1) *
    ∑ k ∈ range j, weight p (2*k+1)*reciprocalSign p (2*j+1) (2*k+1)

/-- Exact decomposition into the positive harmonic triangle and the smaller-modulus remainder. -/
theorem S_eq_triangles (hp : p%2=1) :
    (S p : ℝ) = upperTriangle p + lowerTriangle p := by
  let f (u v : ℕ) := weight p v*(quotientSign p u v : ℝ)
  have hs (j : ℕ) (hj : j ∈ range (p/2)) :
      ∑ k ∈ range (p/2), f (2*j+1) (2*k+1) =
      upperRow p (2*j+1) + ∑ k ∈ range j, weight p (2*k+1)*reciprocalSign p (2*j+1) (2*k+1) := by
    have hj' := mem_range.mp hj
    have hk := sum_range_add (fun k => f (2*j+1) (2*k+1)) j (p/2-j)
    rw [Nat.add_sub_of_le hj'.le] at hk
    rw [hk,add_comm,upperRow,show (p-(2*j+1))/2=p/2-j by omega]
    congr 1
    · apply sum_congr rfl; intro k _; dsimp [f]; rw [show 2*(j+k)+1=2*j+1+2*k by omega]
    · apply sum_congr rfl; intro k hh; dsimp [f]
      rw [quotient_eq_reciprocal hp (by omega) (by omega) (by have := mem_range.mp hh; omega) (by omega)]
  have h := S_cotangent hp
  change (p:ℝ)*(S p:ℝ) = 2*∑ j ∈ range (p/2), weight p (2*j+1) * ∑ k ∈ range (p/2), f (2*j+1) (2*k+1) at h
  rw [sum_congr rfl (fun j hj => congrArg (weight p (2*j+1) * ·) (hs j hj))] at h
  simp_rw [mul_add,sum_add_distrib] at h
  unfold upperTriangle lowerTriangle
  have hne : (p:ℝ)≠0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  field_simp
  linear_combination h

/-- A fully explicit one-sided bound for S in terms of the reciprocal sums at smaller moduli. -/
theorem S_sub_lowerTriangle_harmonic (hp : p%2=1) :
    3*p/(4*Real.pi^2)*harmonic (p/6) ≤ (S p : ℝ)-lowerTriangle p := by
  rw [S_eq_triangles hp,add_sub_cancel_right]
  exact upperTriangle_harmonic hp

/-- Every odd prime has a positive logarithmic contribution after the reciprocal remainder is removed. -/
theorem S_sub_lowerTriangle_log (hp : p%2=1) :
    3/(4*Real.pi^2)*p*Real.log ((p:ℝ)/6) ≤ (S p : ℝ)-lowerTriangle p := by
  have hpos : 0<(p:ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hh : Real.log ((p:ℝ)/6) ≤ (harmonic (p/6) : ℝ) := by
    apply le_trans _ (log_add_one_le_harmonic _)
    apply Real.log_le_log (by positivity)
    rw [div_le_iff₀ (by norm_num : (0:ℝ)<6)]
    exact_mod_cast (show p≤(p/6+1)*6 by omega)
  apply le_trans _ (S_sub_lowerTriangle_harmonic hp)
  rw [show (3:ℝ)*p/(4*Real.pi^2) = 3/(4*Real.pi^2)*p by ring]
  exact mul_le_mul_of_nonneg_left hh (by positivity)

open Filter in
/-- A one-sided estimate on the smaller-modulus triangle suffices for the exact
lower-growth conclusion of the pinned Conjecture 4.4. -/
theorem growth_of_lowerTriangle (b : ℝ) (hb : b<3/(4*Real.pi^2))
    (hR : ∀ᶠ p : ℕ in atTop, p.Prime → Odd p →
      -b*p*Real.log p ≤ lowerTriangle p) (n : ℕ) :
    ∀ᶠ p : ℕ in atTop, p.Prime → Odd p → n*p < S p := by
  let c : ℝ := 3/(4*Real.pi^2)
  have hcb : 0<c-b := sub_pos.mpr hb
  obtain ⟨N,hN⟩ := exists_nat_gt (Real.exp ((n+c*Real.log 6)/(c-b)))
  filter_upwards [hR,eventually_ge_atTop N] with p h hpN
  intro hp ho
  let : Fact p.Prime := ⟨hp⟩
  have hp0 : 0<(p:ℝ) := by exact_mod_cast hp.pos
  have ht : (n+c*Real.log 6)/(c-b) < Real.log p := by
    rw [← Real.exp_lt_exp,Real.exp_log hp0]
    exact hN.trans_le (by exact_mod_cast hpN)
  have hh := mul_lt_mul_of_pos_right ((div_lt_iff₀ hcb).mp ht) hp0
  have hS := S_sub_lowerTriangle_log (Nat.odd_iff.mp ho)
  rw [Real.log_div hp0.ne' (by norm_num)] at hS
  change c*p*(Real.log p-Real.log 6) ≤ (S p:ℝ)-lowerTriangle p at hS
  have hres := h hp ho
  have hr : (n:ℝ)*p < (S p:ℝ) := by linarith only [hh,hS,hres]
  exact_mod_cast hr

end Arxiv.«2501.03234».ThetaCotangentTriangle
#print axioms Arxiv.«2501.03234».ThetaCotangentTriangle.quotient_prefix_lower
#print axioms Arxiv.«2501.03234».ThetaCotangentTriangle.upperRow_lower
#print axioms Arxiv.«2501.03234».ThetaCotangentTriangle.upperTriangle_harmonic
#print axioms Arxiv.«2501.03234».ThetaCotangentTriangle.S_cotangent
#print axioms Arxiv.«2501.03234».ThetaCotangentTriangle.quotient_eq_reciprocal
#print axioms Arxiv.«2501.03234».ThetaCotangentTriangle.S_eq_triangles
#print axioms Arxiv.«2501.03234».ThetaCotangentTriangle.S_sub_lowerTriangle_harmonic
#print axioms Arxiv.«2501.03234».ThetaCotangentTriangle.S_sub_lowerTriangle_log
#print axioms Arxiv.«2501.03234».ThetaCotangentTriangle.growth_of_lowerTriangle
