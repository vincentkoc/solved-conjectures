import ThetaPrimeSieve
import ThetaDenominatorTails

/-! Cancellation of theta rows over common residue classes. -/
namespace Arxiv.«2501.03234».ThetaRowCorrelations

open Finset ThetaPeriodMeans ThetaReciprocalFibers ThetaReciprocalInversion ThetaCotangentTriangle

/-- The signed primitive numerator on unit arguments, extended by zero elsewhere. -/
noncomputable def wave (n d w : ℕ) : ℤ :=
  if n.Coprime d ∧ d%2=1 ∧ w%2=1 ∧ w.Coprime d then reciprocalSign n d w else 0

private theorem wave_eq {n d : ℕ} (h : n.Coprime d) (w : ℕ) :
    (wave n d w : ℂ)=primitiveTerm n d w := by
  by_cases H : d%2=1 ∧ w%2=1 ∧ w.Coprime d
  · rw [wave,primitiveTerm,if_pos ⟨h,H⟩,if_pos H]
  · rw [wave,primitiveTerm,if_neg (fun hh => H hh.2),if_neg H,Int.cast_zero]

/-- The reciprocal sign equals the parity sign of the reduced representative. -/
theorem sign_neg_pow (n d w : ℕ) :
    reciprocalSign n d w = -(-1:ℤ)^(((w:ZMod d)*(n:ZMod d)⁻¹).val) := by
  unfold reciprocalSign
  rcases Nat.even_or_odd (((w:ZMod d)*(n:ZMod d)⁻¹).val) with he|ho
  · rw [he.neg_one_pow,if_neg (by have := Nat.even_iff.mp he; omega)]
  · rw [ho.neg_one_pow,if_pos (Nat.odd_iff.mp ho)]; norm_num

/-- At each primitive numerator, a residue class of step q has signed mass
at most the divisor count of the quotient modulus. -/
theorem wave_fiber {q m k : ℕ} (hq : 0<q) (hm : 0 < m) (hk : k<q) (w : ℕ) :
    |∑ i ∈ range m, wave (k+q*i) (q*m) w| ≤ m.divisors.card := by
  by_cases hw : (q*m)%2=1 ∧ w%2=1 ∧ w.Coprime (q*m)
  · by_cases hkc : k.Coprime q
    · let : NeZero q := ⟨hq.ne'⟩
      let : NeZero (q*m) := ⟨(Nat.mul_pos hq hm).ne'⟩
      let a := ZMod.unitOfCoprime k hkc
      let v := ZMod.unitOfCoprime w hw.2.2
      have ha : (a : ZMod q).val=k := by simp [a,ZMod.val_natCast_of_lt hk]
      have hod := Nat.odd_iff.mpr hw.1
      have hq' := Nat.odd_iff.mp (hod.of_dvd_nat (Nat.dvd_mul_right q m))
      have hm' := Nat.odd_iff.mp (hod.of_dvd_nat (Nat.dvd_mul_left m q))
      have H := reciprocal_unit_fiber hm' hq' v a
      let f (n : ℕ) : ℤ := (-1:ℤ)^(((w:ZMod (q*m))*(n:ZMod (q*m))⁻¹).val)
      have hf (x : (ZMod (q*m))ˣ) : f (x : ZMod (q*m)).val = (-1:ℤ)^((↑(v/x):ZMod (q*m)).val) := by
        simp only [f,ZMod.natCast_zmod_val,div_eq_mul_inv,Units.val_mul,← ZMod.inv_coe_unit]; rfl
      have he := sum_unit_fiber (m:=m) a f
      simp_rw [hf] at he
      rw [he,ha] at H
      have hterm (i : ℕ) : wave (k+q*i) (q*m) w =
          -(if (k+q*i).Coprime m then f (k+q*i) else 0) := by
        have hqk : (k+q*i).Coprime q := by simpa using hkc
        by_cases h : (k+q*i).Coprime m
        · rw [wave,if_pos ⟨Nat.coprime_mul_iff_right.mpr ⟨hqk,h⟩,hw⟩,if_pos h]
          exact sign_neg_pow ..
        · rw [wave,if_neg (fun hh => h (Nat.coprime_mul_iff_right.mp hh.1).2),if_neg h,neg_zero]
      simp_rw [hterm]; rwa [sum_neg_distrib,abs_neg]
    · have H (i : ℕ) : ¬(k+q*i).Coprime (q*m) := by
        intro hc; exact hkc (by simpa using (Nat.coprime_mul_iff_right.mp hc).1)
      simp [wave,H]
  · have H (i : ℕ) : wave (k+q*i) (q*m) w=0 := if_neg (fun h => hw h.2)
    simp [H]

/-- A signed row with a finite reciprocal numerator window. -/
noncomputable def row (d K n : ℕ) : ℝ :=
  ∑ i ∈ range K, ((i:ℝ)+1)⁻¹*(wave n d (i+1):ℝ)

private theorem wave_of_not_coprime {n d : ℕ} (h : ¬n.Coprime d) (j : ℕ) :
    wave n d j=0 := if_neg (fun H => h H.1)

private theorem wave_period (n d j : ℕ) : wave n d (2*d+j)=wave n d j := by
  by_cases hc : n.Coprime d
  · apply Int.cast_injective (α:=ℂ)
    rw [wave_eq hc,wave_eq hc,ThetaDenominatorTails.primitive_period]
  · rw [wave_of_not_coprime hc,wave_of_not_coprime hc]

private theorem wave_reflect {d : ℕ} (hd : 1<d) (n : ℕ) {j : ℕ} (hj : j≤2*d) :
    wave n d (2*d-j)= -wave n d j := by
  by_cases hc : n.Coprime d
  · apply Int.cast_injective (α:=ℂ)
    rw [Int.cast_neg,wave_eq hc,wave_eq hc,ThetaDenominatorTails.primitive_reflect hd hc hj]
  · rw [wave_of_not_coprime hc,wave_of_not_coprime hc,neg_zero]

/-- Cancellation survives summation over the numerator window, uniformly in its endpoint. -/
theorem row_fiber {q m k : ℕ} (hq : 0<q) (hm : 0 < m) (hd : 1<q*m) (hk : k<q) (K : ℕ) :
    |∑ i ∈ range m, row (q*m) K (k+q*i)| ≤ 3*((harmonic (q*m):ℝ)*m.divisors.card) := by
  let v (w : ℕ) : ℝ := ∑ i ∈ range m,(wave (k+q*i) (q*m) w:ℝ)
  have hv (w) : ‖v w‖ ≤ m.divisors.card := by
    rw [Real.norm_eq_abs]; dsimp [v]; exact_mod_cast wave_fiber hq hm hk w
  have hz : v 0=0 := by simp [v,wave]
  have hp (j) : v (2*(q*m)+j)=v j := by simp only [v,wave_period]
  have hr (j) (hj : j≤2*(q*m)) : v (2*(q*m)-j)= -v j := by
    simp only [v,wave_reflect hd _ hj,Int.cast_neg,sum_neg_distrib]
  have H := ThetaUniformWindows.reciprocal_window (d:=q*m) (by omega) v hv hz hp hr K
  unfold row; rw [sum_comm]
  simpa only [v,smul_eq_mul,mul_sum,Real.norm_eq_abs] using H

/-- The argument of each row enters only through its residue mod d. -/
theorem row_onMod (d K : ℕ) : OnMod d (row d K) := by
  intro n
  have hc : (n%d).Coprime d ↔ n.Coprime d := by
    rw [← ZMod.isUnit_iff_coprime,← ZMod.isUnit_iff_coprime,ZMod.natCast_mod]
  unfold row
  simp only [wave,hc,reciprocalSign,ZMod.natCast_mod]

/-- A common-denominator covariance estimate, uniform in both window lengths.
Here the periods are g*m and g*n with coprime quotient periods. -/
theorem row_pair {g m n : ℕ} (hg : 0<g) (hm : 0 < m) (hn : 0 < n)
    (hd : 1<g*m) (he : 1<g*n) (hc : m.Coprime n) (K J : ℕ) :
    |mean (g*(m*n)) (fun x => row (g*m) K x * row (g*n) J x)| ≤
      (3*(harmonic (g*m):ℝ)*m.divisors.card)/(m:ℝ) *
      ((3*(harmonic (g*n):ℝ)*n.divisors.card)/(n:ℝ)) := by
  rw [mean_fiber_product hg hm hn hc (row_onMod (g*m) K) (row_onMod (g*n) J),abs_div,
    abs_of_nonneg (by positivity : 0≤(g:ℝ)*(m:ℝ)*n)]
  let B := 3*((harmonic (g*m):ℝ)*m.divisors.card)
  let D := 3*((harmonic (g*n):ℝ)*n.divisors.card)
  have hsum : |∑ k∈range g, (∑ i∈range m, row (g*m) K (k+g*i))*
      (∑ j∈range n, row (g*n) J (k+g*j))| ≤ g*(B*D) := by
    apply (abs_sum_le_sum_abs ..).trans
    calc
      _ ≤ ∑ _k∈range g,B*D := by
        apply sum_le_sum; intro k hk; rw [abs_mul]
        exact mul_le_mul (row_fiber hg hm hd (mem_range.mp hk) K) (row_fiber hg hn he (mem_range.mp hk) J)
          (abs_nonneg _) ((abs_nonneg _).trans (row_fiber hg hm hd (mem_range.mp hk) K))
      _ = _ := by simp
  refine (div_le_div_of_nonneg_right hsum (by positivity)).trans_eq ?_
  dsimp [B,D]
  field_simp [Nat.cast_ne_zero.mpr hg.ne',Nat.cast_ne_zero.mpr hm.ne',Nat.cast_ne_zero.mpr hn.ne']

/-- Inverse powers used to sum the common divisor and the two coprime quotients. -/
noncomputable def decay (s : ℝ) (n : ℕ) : ℝ := ((n:ℝ)^s)⁻¹

private lemma polar_row {g m : ℕ} (hg : 0<g) (hm : 0 < m) :
    ((g:ℝ)*m)^(1/8:ℝ)/((g:ℝ)*m) * ((3*(harmonic (g*m):ℝ)*m.divisors.card)/m) ≤
      270*decay (3/4) g*decay (9/8) m := by
  have gp : (0:ℝ)<g := Nat.cast_pos.mpr hg
  have mp : (0:ℝ)< m := Nat.cast_pos.mpr hm
  have g1 : (1:ℝ)≤g := by exact_mod_cast hg
  have hdiv := ThetaReciprocalBlocks.harmonic_divisors hg hm
  have hlog : 1+Real.log g≤9*(g:ℝ)^(1/8:ℝ) := by
    have h := Real.log_natCast_le_rpow_div g (show (0:ℝ)<1/8 by norm_num)
    linarith only [h,Real.one_le_rpow g1 (show (0:ℝ)≤1/8 by norm_num)]
  have hmexp : (m:ℝ)^(1/8:ℝ)*((m:ℝ)^(5/4:ℝ))⁻¹ = decay (9/8) m := by
    rw [decay,← Real.rpow_neg mp.le,← Real.rpow_add mp,← Real.rpow_neg mp.le]; norm_num
  have hgexp : (g:ℝ)^(1/8:ℝ)*(g:ℝ)^(1/8:ℝ)/g = decay (3/4) g := by
    rw [← Real.rpow_add gp,decay,← Real.rpow_neg gp.le,div_eq_iff gp.ne']
    conv_rhs => rhs; rw [← Real.rpow_one (g:ℝ)]
    rw [← Real.rpow_add gp]; norm_num
  rw [Real.mul_rpow gp.le mp.le]
  calc
    _ = (3*(g:ℝ)^(1/8:ℝ)/g*(m:ℝ)^(1/8:ℝ))*
          ((harmonic (g*m):ℝ)*m.divisors.card/(m:ℝ)^2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hdiv (by positivity)
    _ = 30*((g:ℝ)^(1/8:ℝ)/g*decay (9/8) m)*(1+Real.log g) := by
      rw [← hmexp]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hlog (by unfold decay; positivity)
    _ = _ := by rw [← hgexp]; ring

/-- Absolute covariance with the reciprocal unit-density correction and both
row weights 1/d and 1/e. -/
noncomputable def kernel (d e K J : ℕ) : ℝ :=
  let L := d.lcm e
  ((L:ℝ)/L.totient)*|mean L (fun x => row d K x*row e J x)|/((d:ℝ)*e)

private noncomputable def factor : ℝ := (1+8/Real.log 2)*270^2

private lemma factor_nonneg : 0≤factor := by unfold factor; positivity

private lemma kernel_bound {g m n : ℕ} (hg : 0<g) (hm : 0 < m) (hn : 0 < n)
    (hd : 1<g*m) (he : 1<g*n) (hc : m.Coprime n) (K J : ℕ) :
    kernel (g*m) (g*n) K J ≤ factor*decay (3/2) g*decay (9/8) m*decay (9/8) n := by
  have gp : (0:ℝ)<g := Nat.cast_pos.mpr hg
  have mp : (0:ℝ)< m := Nat.cast_pos.mpr hm
  have np : (0:ℝ)<n := Nat.cast_pos.mpr hn
  have hL : (g*m).lcm (g*n)=g*(m*n) := by rw [Nat.lcm_mul_left,hc.lcm_eq_mul]
  let L := g*(m*n)
  have hH : (0:ℝ)≤harmonic (g*n) := by exact_mod_cast (harmonic_pos (Nat.mul_pos hg hn).ne').le
  have hLpos : 0<L := Nat.mul_pos hg (Nat.mul_pos hm hn)
  have hle : (L:ℝ)^(1/8:ℝ) ≤ ((g:ℝ)*m)^(1/8:ℝ)*((g:ℝ)*n)^(1/8:ℝ) := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
    have h1 : (1:ℝ)≤g := by exact_mod_cast hg
    dsimp [L]; push_cast
    nlinarith only [mul_nonneg (sub_nonneg.mpr h1) (mul_nonneg (mul_nonneg gp.le mp.le) np.le)]
  have hcost := (unit_density_power hLpos).trans (mul_le_mul_of_nonneg_left hle
    (by positivity : 0≤1+8/Real.log 2))
  have hh := mul_le_mul hcost (row_pair hg hm hn hd he hc K J) (abs_nonneg _) (by positivity)
  have hgexp : decay (3/4) g * decay (3/4) g = decay (3/2) g := by
    unfold decay; rw [← mul_inv,← Real.rpow_add gp]; norm_num
  unfold kernel; rw [hL]; dsimp only []
  dsimp only [L] at hh
  push_cast at hh ⊢
  apply (div_le_div_of_nonneg_right hh (by positivity : (0:ℝ)≤((g:ℝ)*m)*((g:ℝ)*n))).trans
  calc
    _ = (1+8/Real.log 2) *
        ((((g:ℝ)*m)^(1/8:ℝ)/((g:ℝ)*m)*((3*(harmonic (g*m):ℝ)*m.divisors.card)/m))*
         (((g:ℝ)*n)^(1/8:ℝ)/((g:ℝ)*n)*((3*(harmonic (g*n):ℝ)*n.divisors.card)/n))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul (polar_row hg hm) (polar_row hg hn)
      (by positivity) (by unfold decay; positivity)) (by positivity)
    _ = _ := by rw [← hgexp]; unfold factor; ring

/-- Fractional denominator weight used to control the omitted rows. -/
noncomputable def denominatorWeight (d : ℕ) : ℝ := (d:ℝ)^(1/16:ℝ)
private lemma weight_times_decay {d : ℕ} (hd : 0<d) (x y : ℝ) (h : x=y+1/16) :
    denominatorWeight d*decay x d=decay y d := by
  have hpos : (0:ℝ)<d := by exact_mod_cast hd
  unfold denominatorWeight decay
  rw [h,Real.rpow_add hpos,mul_inv_rev]
  have ht := (Real.rpow_pos_of_pos hpos (1/16:ℝ)).ne'
  field_simp
private lemma weight_majorant {g m n : ℕ} (hg : 0<g) (hm : 0 < m) (hn : 0 < n) (U : ℝ) :
    denominatorWeight (g*m)*denominatorWeight (g*n)*(U*decay (3/2) g*decay (9/8) m*decay (9/8) n)=
      U*decay (11/8) g*decay (17/16) m*decay (17/16) n := by
  have hmul (a b : ℕ) : denominatorWeight (a*b)=denominatorWeight a*denominatorWeight b := by
    unfold denominatorWeight; rw [Nat.cast_mul,Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  rw [hmul,hmul]
  calc
    _ = U*(denominatorWeight g*(denominatorWeight g*decay (3/2) g))*(denominatorWeight m*decay (9/8) m)*(denominatorWeight n*decay (9/8) n) := by ring
    _ = _ := by rw [weight_times_decay hg _ (23/16) (by norm_num),weight_times_decay hg _ (11/8) (by norm_num),
                     weight_times_decay hm _ (17/16) (by norm_num),weight_times_decay hn _ (17/16) (by norm_num)]

/-- A positive fractional moment of the absolute covariance is summable. -/
theorem weighted_kernel_sum : ∃ C : ℝ, 0≤C ∧ ∀ (T : ℕ) (K : ℕ → ℕ),
    ∑ d∈Icc 2 T, ∑ e∈Icc 2 T, denominatorWeight d*denominatorWeight e*kernel d e (K d) (K e) ≤ C := by
  classical
  let Z (s : ℝ) := ∑' i : ℕ, decay s i
  have hp (s : ℝ) (n : ℕ) : 0≤decay s n := by unfold decay; positivity
  have hz (s) : 0≤Z s := tsum_nonneg (hp s)
  refine ⟨factor*Z (11/8)*(Z (17/16)*Z (17/16)),mul_nonneg (mul_nonneg factor_nonneg (hz _)) (mul_nonneg (hz _) (hz _)),?_⟩
  intro T K
  let S := Icc 2 T
  let A := Icc 1 T
  let ix (z : ℕ×ℕ) : ℕ×ℕ×ℕ := (z.1.gcd z.2,z.1/(z.1.gcd z.2),z.2/(z.1.gcd z.2))
  let F (x : ℕ×ℕ×ℕ) := factor*decay (11/8) x.1*decay (17/16) x.2.1*decay (17/16) x.2.2
  let recov (x : ℕ×ℕ×ℕ) := (x.1*x.2.1,x.1*x.2.2)
  have hrec (z : ℕ×ℕ) : recov (ix z)=z := Prod.ext (Nat.mul_div_cancel' (Nat.gcd_dvd_left ..))
      (Nat.mul_div_cancel' (Nat.gcd_dvd_right ..))
  have hi : Set.InjOn ix ↑(S ×ˢ S) := by
    intro a _ b _ h; rw [← hrec a,← hrec b,h]
  have hmem {z : ℕ×ℕ} (h : z∈S ×ˢ S) :
      1≤(ix z).1 ∧ 1≤(ix z).2.1 ∧ 1≤(ix z).2.2 ∧ ix z∈A ×ˢ (A ×ˢ A) := by
    obtain ⟨hd,he⟩ := mem_product.mp h
    obtain ⟨hd,hdT⟩ := mem_Icc.mp hd; obtain ⟨he,heT⟩ := mem_Icc.mp he
    have hg := Nat.gcd_pos_of_pos_left z.2 (by omega : 0<z.1)
    have hgd := Nat.gcd_le_left z.2 (by omega : 0<z.1)
    have hge := Nat.gcd_le_right z.1 (by omega : 0<z.2)
    have hm := Nat.div_pos hgd hg; have hn := Nat.div_pos hge hg
    exact ⟨hg,hm,hn,mem_product.mpr ⟨mem_Icc.mpr ⟨hg,hgd.trans hdT⟩,mem_product.mpr
      ⟨mem_Icc.mpr ⟨hm,(Nat.div_le_self ..).trans hdT⟩,mem_Icc.mpr ⟨hn,(Nat.div_le_self ..).trans heT⟩⟩⟩⟩
  have hk (z : ℕ×ℕ) (h : z∈S ×ˢ S) : denominatorWeight z.1*denominatorWeight z.2*kernel z.1 z.2 (K z.1) (K z.2) ≤ F (ix z) := by
    obtain ⟨hg,hm,hn,_⟩ := hmem h
    have h₁ := congrArg Prod.fst (hrec z); have h₂ := congrArg Prod.snd (hrec z)
    have h₁' : (ix z).1*(ix z).2.1=z.1 := h₁
    have h₂' : (ix z).1*(ix z).2.2=z.2 := h₂
    have H := kernel_bound hg hm hn (h₁' ▸ (mem_Icc.mp (mem_product.mp h).1).1)
      (h₂' ▸ (mem_Icc.mp (mem_product.mp h).2).1) (Nat.coprime_div_gcd_div_gcd hg) (K z.1) (K z.2)
    have hu := mul_le_mul_of_nonneg_left H (show 0≤denominatorWeight ((ix z).1*(ix z).2.1)*denominatorWeight ((ix z).1*(ix z).2.2) by
      unfold denominatorWeight; positivity)
    rw [weight_majorant hg hm hn] at hu
    simpa only [h₁',h₂'] using hu
  have hsub : (S ×ˢ S).image ix ⊆ A ×ˢ (A ×ˢ A) := by
    intro x hx; obtain ⟨z,hz,rfl⟩ := mem_image.mp hx; exact (hmem hz).2.2.2
  have sum_le {s : ℝ} (hs : 1<s) : ∑ i∈A, decay s i≤Z s :=
    (Real.summable_nat_rpow_inv.mpr hs).sum_le_tsum _ (fun i _ => hp s i)
  rw [← sum_product']
  calc
    _ ≤ ∑ z∈S ×ˢ S,F (ix z) := sum_le_sum hk
    _ = ∑ x∈(S ×ˢ S).image ix,F x := (sum_image hi).symm
    _ ≤ ∑ x∈A ×ˢ (A ×ˢ A),F x := by
      apply sum_le_sum_of_subset_of_nonneg hsub
      intro i _ _; exact mul_nonneg (mul_nonneg (mul_nonneg factor_nonneg (hp _ _)) (hp _ _)) (hp _ _)
    _ = factor*(∑ g∈A,decay (11/8) g)*((∑ m∈A,decay (17/16) m)*(∑ n∈A,decay (17/16) n)) := by
      rw [sum_product]; simp_rw [sum_product]; dsimp only [F]
      simp_rw [← mul_sum,← sum_mul,← mul_sum,← sum_mul,← mul_sum]; ring
    _ ≤ _ := by
      have hnn (s : ℝ) : 0≤∑ i∈A,decay s i := sum_nonneg (fun i _ => hp s i)
      exact mul_le_mul (mul_le_mul_of_nonneg_left (sum_le (by norm_num)) factor_nonneg)
        (mul_le_mul (sum_le (by norm_num)) (sum_le (by norm_num)) (hnn _) (hz _))
        (mul_nonneg (hnn _) (hnn _)) (mul_nonneg factor_nonneg (hz _))

/-- Summing the absolute corrected row covariances uniformly in both windows. -/
theorem kernel_sum : ∃ C : ℝ, 0≤C ∧ ∀ (T : ℕ) (K : ℕ → ℕ),
    ∑ d∈Icc 2 T, ∑ e∈Icc 2 T, kernel d e (K d) (K e) ≤ C := by
  obtain ⟨C,hC,H⟩ := weighted_kernel_sum
  refine ⟨C,hC,?_⟩; intro T K
  apply le_trans _ (H T K)
  have h (d : ℕ) (hd : d∈Icc 2 T) : 1≤denominatorWeight d := by
    apply Real.one_le_rpow _ (by norm_num)
    exact_mod_cast (show 1≤d by have := (mem_Icc.mp hd).1; omega)
  apply sum_le_sum; intro d hd; apply sum_le_sum; intro e he
  exact le_mul_of_one_le_left (by unfold kernel; positivity) (one_le_mul_of_one_le_of_one_le (h d hd) (h e he))

/-- The assertion on a complete period of the smaller modulus transfers to
the square sieve on a common period. -/
theorem weighted_pair {d e R P : ℕ} (hd : 0<d) (he : 0<e) (hR : 1≤R) (hP : 0<P)
    (hdP : d∣P) (heP : e∣P) (hr : ∀ r∈ThetaPrimeSieve.moduli R,r∣P) (K J : ℕ) :
    |mean P (fun x => ThetaPrimeSieve.weight R x*(row d K x*row e J x))| ≤
      (ThetaPrimeSieve.normalizer R)⁻¹*((d.lcm e:ℝ)/(d.lcm e).totient)*
        |mean (d.lcm e) (fun x => row d K x*row e J x)| := by
  have H {n q j : ℕ} (hc : ¬n.Coprime q) : row q j n=0 := by
    simp [row,wave_of_not_coprime hc]
  apply ThetaPrimeSieve.weighted_period (Nat.lcm_pos hd he) hR hP (Nat.lcm_dvd hdP heP) hr
  · intro n
    exact congrArg₂ (·*·) (onMod_lift (Nat.dvd_lcm_left d e) (row_onMod d K) n)
      (onMod_lift (Nat.dvd_lcm_right d e) (row_onMod e J) n)
  · intro n hn
    by_cases h : n.Coprime d
    · have hn' : ¬n.Coprime e := fun he => hn ((h.mul_right he).coprime_dvd_right (Nat.lcm_dvd_mul d e))
      rw [H hn',mul_zero]
    · rw [H h,zero_mul]

/-- The low-denominator row sum with independent bounded coefficients. -/
noncomputable def low (T : ℕ) (K : ℕ → ℕ) (a : ℕ → ℝ) (x : ℕ) :=
  ∑ d∈Icc 2 T, (a d/d)*row d (K d) x

/-- The unit-sieved complete second moment permits a fractional growth factor in each coefficient. -/
theorem weighted_low_complete : ∃ C : ℝ, 0≤C ∧ ∀ (T R P : ℕ), 1≤R → 0<P →
    (∀ d∈Icc 2 T,d∣P) → (∀ r∈ThetaPrimeSieve.moduli R,r∣P) →
    ∀ (K : ℕ → ℕ) (a : ℕ → ℝ) (B : ℝ), 0≤B → (∀ d∈Icc 2 T,|a d|≤B*denominatorWeight d) →
    mean P (fun x => ThetaPrimeSieve.weight R x*(low T K a x)^2) ≤
      (ThetaPrimeSieve.normalizer R)⁻¹*B^2*C := by
  obtain ⟨C,hC,hkernel⟩ := weighted_kernel_sum
  refine ⟨C,hC,?_⟩; intro T R P hR hP hdP hr K a B hB ha
  let W := ThetaPrimeSieve.weight R
  let G := (ThetaPrimeSieve.normalizer R)⁻¹
  have hg : 0≤G := by dsimp [G,ThetaPrimeSieve.normalizer]; positivity
  let S := Icc 2 T
  let F d e x := W x*(row d (K d) x*row e (K e) x)
  let b (d) := a d/d
  have hexp (x) : W x*low T K a x^2=∑ d∈S,∑ e∈S,(b d*b e)*F d e x := by
    unfold low; rw [pow_two,sum_mul_sum]
    simp only [S,mul_sum]; apply sum_congr rfl; intro d _; apply sum_congr rfl; intro e _
    dsimp [b,F]; ring
  have avg : mean P (fun x => W x*(low T K a x)^2) =
      ∑ d∈S,∑ e∈S,(b d*b e)*mean P (F d e) := by
    unfold mean; simp_rw [hexp]; rw [sum_comm]
    simp_rw [sum_div]; apply sum_congr rfl; intro d _; rw [sum_comm]
    apply sum_congr rfl; intro e _; simp only [mul_sum,mul_div_assoc]
  have entry (d) (hd : d∈S) (e) (he : e∈S) :
      (b d*b e)*mean P (F d e) ≤ (G*B^2)*(denominatorWeight d*denominatorWeight e*kernel d e (K d) (K e)) := by
    have hd' : 0<d := by have := (mem_Icc.mp hd).1; omega
    have he' : 0<e := by have := (mem_Icc.mp he).1; omega
    have hav := weighted_pair hd' he' hR hP (hdP d hd) (hdP e he) hr (K d) (K e)
    have hcoef : |b d*b e| ≤ (B*denominatorWeight d)*(B*denominatorWeight e)/((d:ℝ)*e) := by
      dsimp [b]; rw [abs_mul,abs_div,abs_div,abs_of_nonneg (Nat.cast_nonneg d (α:=ℝ)),
        abs_of_nonneg (Nat.cast_nonneg e (α:=ℝ)),div_mul_div_comm]
      exact div_le_div_of_nonneg_right (mul_le_mul (ha _ hd) (ha _ he) (abs_nonneg _) (mul_nonneg hB (by unfold denominatorWeight; positivity))) (by positivity)
    apply (le_abs_self _).trans; rw [abs_mul]
    apply (mul_le_mul hcoef hav (abs_nonneg _) (by unfold denominatorWeight; positivity)).trans_eq
    dsimp [kernel,G]; ring
  rw [avg]
  apply (sum_le_sum (fun d hd => sum_le_sum (fun e he => entry d hd e he))).trans
  simp_rw [← mul_sum]
  exact mul_le_mul_of_nonneg_left (hkernel T K) (mul_nonneg hg (sq_nonneg B))

/-- The sieve-weighted second moment of the low rows on a complete period is
uniform in both cutoffs, apart from the inverse sieve normalizer. -/
theorem low_complete : ∃ C : ℝ, 0≤C ∧ ∀ (T R P : ℕ), 1≤R → 0<P →
    (∀ d∈Icc 2 T,d∣P) → (∀ r∈ThetaPrimeSieve.moduli R,r∣P) →
    ∀ (K : ℕ → ℕ) (a : ℕ → ℝ) (B : ℝ), 0≤B → (∀ d∈Icc 2 T,|a d|≤B) →
    mean P (fun x => ThetaPrimeSieve.weight R x*(low T K a x)^2) ≤
      (ThetaPrimeSieve.normalizer R)⁻¹*B^2*C := by
  obtain ⟨C,hC,H⟩ := weighted_low_complete
  refine ⟨C,hC,?_⟩; intro T R P hR hP hdP hr K a B hB ha
  apply H T R P hR hP hdP hr K a B hB
  intro d hd; apply (ha d hd).trans
  apply le_mul_of_one_le_right hB (Real.one_le_rpow _ (by norm_num))
  exact_mod_cast (show 1≤d by have := (mem_Icc.mp hd).1; omega)


/-- Removing the first T denominators gains a factor T^(-1/8) in the complete
sieved second moment, uniformly in both windows and in the larger cutoff. -/
theorem tail_low_complete : ∃ C : ℝ, 0≤C ∧ ∀ (N R P T : ℕ), 1≤R → 0<P → 0<T →
    (∀ d∈Icc 2 N,d∣P) → (∀ r∈ThetaPrimeSieve.moduli R,r∣P) →
    ∀ (K : ℕ → ℕ) (a : ℕ → ℝ) (B : ℝ), 0≤B → (∀ d∈Icc 2 N,|a d|≤B) →
    mean P (fun x => ThetaPrimeSieve.weight R x*
      (low N K (fun d => if T<d then a d else 0) x)^2) ≤
      (ThetaPrimeSieve.normalizer R)⁻¹*(B/denominatorWeight T)^2*C := by
  obtain ⟨C,hC,H⟩ := weighted_low_complete
  refine ⟨C,hC,?_⟩; intro N R P T hR hP hT hdP hr K a B hB ha
  have hpos : 0<denominatorWeight T := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hT) _
  apply H N R P hR hP hdP hr K _ _ (div_nonneg hB hpos.le)
  intro d hd; split_ifs with hh
  · apply (ha d hd).trans
    rw [div_mul_eq_mul_div,le_div_iff₀ hpos]
    apply mul_le_mul_of_nonneg_left _ hB
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hh.le) (by norm_num)
  · rw [abs_zero]; unfold denominatorWeight; positivity

/-- At a prime argument coprime to every retained modulus, the scalar low rows
are exactly the part removed from the Fourier interpolation. -/
theorem window_split {T Y p : ℕ} (hTY : T≤Y) (K : ℕ → ℕ) (hK : K 1=0)
    (hc : ∀ d∈Icc 1 Y,p.Coprime d) :
    windowExtension K Y p-windowExtension (ThetaDenominatorTails.above T K) Y p =
      (low T K (ThetaReciprocalBlocks.commonWeight Y) p : ℂ) := by
  classical
  have hrow (d : ℕ) (hd : d∈Icc 1 Y) :
      (row d (K d) p : ℂ) =
        ∑ i∈range (K d), (↑(i+1:ℕ):ℂ)⁻¹ * primitiveTerm p d (i+1) := by
    unfold row; push_cast
    apply sum_congr rfl; intro i _
    rw [← wave_eq (hc d hd)]
  have hS : Icc 2 T=(Icc 1 Y).filter (fun d => 1<d ∧ d≤T) := by
    ext d; simp only [mem_Icc,mem_filter]; omega
  rw [window_primitive_rows K hc,window_primitive_rows _ hc,← sum_sub_distrib]
  unfold low; push_cast; rw [hS,sum_filter]
  apply sum_congr rfl; intro d hd
  obtain ⟨hd',_⟩ := mem_Icc.mp hd
  by_cases h : d≤T
  · by_cases h₁ : 1<d
    · rw [if_pos ⟨h₁,h⟩,hrow d hd]
      simp [ThetaDenominatorTails.above,h]
    · have he : d=1 := by omega
      subst d; simp [ThetaDenominatorTails.above,h,hK]
  · rw [if_neg (fun H => h H.2)]
    simp [ThetaDenominatorTails.above,h]

/-- Natural-order convergence of a reciprocal row for each fixed residue. -/
theorem row_cauchy {d : ℕ} (hd : 1<d) (n : ℕ) : CauchySeq (fun K => row d K n) := by
  let v (j : ℕ) : ℝ := wave n d j
  have hb (j : ℕ) : ‖v j‖≤1 := by
    unfold v wave ThetaCotangentTriangle.reciprocalSign
    split_ifs <;> norm_num
  exact ThetaUniformWindows.reciprocal_window_cauchy (by omega : 0<d) v hb (by simp [v,wave])
    (fun j => by simp [v,wave_period]) (fun j hj => by simp [v,wave_reflect hd n hj])

end Arxiv.«2501.03234».ThetaRowCorrelations
#print axioms Arxiv.«2501.03234».ThetaRowCorrelations.row_cauchy
#print axioms Arxiv.«2501.03234».ThetaRowCorrelations.weighted_kernel_sum
#print axioms Arxiv.«2501.03234».ThetaRowCorrelations.weighted_low_complete
#print axioms Arxiv.«2501.03234».ThetaRowCorrelations.tail_low_complete
#print axioms Arxiv.«2501.03234».ThetaRowCorrelations.window_split
#print axioms Arxiv.«2501.03234».ThetaRowCorrelations.sign_neg_pow
#print axioms Arxiv.«2501.03234».ThetaRowCorrelations.weighted_pair
#print axioms Arxiv.«2501.03234».ThetaRowCorrelations.low_complete
#print axioms Arxiv.«2501.03234».ThetaRowCorrelations.kernel_sum
#print axioms Arxiv.«2501.03234».ThetaRowCorrelations.wave_fiber
#print axioms Arxiv.«2501.03234».ThetaRowCorrelations.row_fiber
#print axioms Arxiv.«2501.03234».ThetaRowCorrelations.row_onMod
#print axioms Arxiv.«2501.03234».ThetaRowCorrelations.row_pair
