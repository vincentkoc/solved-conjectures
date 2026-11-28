import ThetaReciprocalBlocks

/-! Regrouping rational cutoff terms and their finite Fourier frequencies by reduced fractions. -/

namespace Arxiv.«2501.03234».ThetaReciprocalInversion

open Finset ThetaReciprocalFibers

/-- Reducing all fractions k/d with 0 ≤ k < Kd preserves the numerator window. -/
theorem sum_reduced_window (K : ℕ) {A : Type*} [AddCommMonoid A] {d : ℕ} (hd : 0<d) (f : ℕ → A) :
    (∑ q ∈ d.divisors, ∑ h ∈ (range (K*q)).filter (·.Coprime q), f ((d/q)*h)) =
      ∑ k ∈ range (K*d), f k := by
  rw [sum_sigma']
  let s := d.divisors.sigma (fun q => (range (K*q)).filter (·.Coprime q))
  let lift (z : Σ _ : ℕ, ℕ) := (d/z.1)*z.2
  have hdvd {z : Σ _ : ℕ, ℕ} (hz : z ∈ s) : z.1 ∣ d := Nat.dvd_of_mem_divisors (mem_sigma.mp hz).1
  have hg {z : Σ _ : ℕ, ℕ} (hz : z ∈ s) : 0<d/z.1 :=
    Nat.div_pos (Nat.divisor_le (mem_sigma.mp hz).1) (Nat.pos_of_mem_divisors (mem_sigma.mp hz).1)
  have hgcd {z : Σ _ : ℕ, ℕ} (hz : z ∈ s) : (lift z).gcd d=d/z.1 := by
    have he := Nat.div_mul_cancel (hdvd hz)
    have hc := (mem_filter.mp (mem_sigma.mp hz).2).2
    dsimp [lift]
    conv_lhs => arg 2; rw [← he]
    rw [Nat.gcd_mul_left,hc.gcd_eq_one,mul_one]
  apply sum_bij (fun z _ => lift z)
  · intro z hz
    have hlt := mem_range.mp (mem_filter.mp (mem_sigma.mp hz).2).1
    apply mem_range.mpr
    apply (Nat.mul_lt_mul_of_pos_left hlt (hg hz)).trans_eq
    calc (d/z.1)*(K*z.1) = K*((d/z.1)*z.1) := by ring
         _ = K*d := by rw [Nat.div_mul_cancel (hdvd hz)]
  · intro a ha b hb H
    have h : d/a.1=d/b.1 := (hgcd ha).symm.trans ((congrArg (fun k : ℕ => k.gcd d) H).trans (hgcd hb))
    have hq : a.1=b.1 := by
      simpa only [Nat.div_div_self (hdvd ha) hd.ne',Nat.div_div_self (hdvd hb) hd.ne']
        using congrArg (fun z => d/z) h
    have hh : a.2=b.2 := by
      dsimp [lift] at H; rw [← hq] at H
      exact Nat.eq_of_mul_eq_mul_left (hg ha) H
    cases a; cases b; simp_all
  · intro k hk
    let g := k.gcd d
    have hg' : 0<g := Nat.gcd_pos_of_pos_right _ hd
    have hgd : g ∣ d := Nat.gcd_dvd_right k d
    have hgk : g ∣ k := Nat.gcd_dvd_left k d
    have hq := Nat.div_dvd_of_dvd hgd
    have hlt : k/g < K*(d/g) := (Nat.div_lt_iff_lt_mul hg').mpr (by
      rw [Nat.mul_assoc,Nat.div_mul_cancel hgd]; exact mem_range.mp hk)
    refine ⟨⟨d/g,k/g⟩,mem_sigma.mpr ⟨Nat.mem_divisors.mpr ⟨hq,hd.ne'⟩,
      mem_filter.mpr ⟨mem_range.mpr hlt,Nat.coprime_div_gcd_div_gcd hg'⟩⟩,?_⟩
    dsimp [lift]
    rw [Nat.div_div_self hgd hd.ne',Nat.mul_div_cancel' hgk]
  · intros; rfl

/-- Every fraction k/d, including zero, occurs once after reduction. -/
theorem sum_reduced {A : Type*} [AddCommMonoid A] {d : ℕ} (hd : 0<d) (f : ℕ → A) :
    (∑ q ∈ d.divisors, ∑ h ∈ (range q).filter (·.Coprime q), f ((d/q)*h)) =
      ∑ k ∈ range d, f k := by
  simpa only [one_mul] using sum_reduced_window 1 hd f

/-- A positive product cutoff can be summed first over the product or over either factor. -/
theorem sum_by_product {A : Type*} [AddCommMonoid A] (Y : ℕ) (f : ℕ → ℕ → A) :
    (∑ q ∈ Icc 1 Y, ∑ m ∈ Icc 1 (Y/q), f q m) =
    ∑ d ∈ Icc 1 Y, ∑ q ∈ d.divisors, f q (d/q) := by
  rw [sum_sigma',sum_sigma']
  apply sum_bij (fun (z : Σ _ : ℕ, ℕ) _ => ⟨z.1*z.2,z.1⟩)
  · intro ⟨q,m⟩ hz; obtain ⟨hq,hm⟩ := mem_sigma.mp hz
    obtain ⟨hq₁,hqY⟩ := mem_Icc.mp hq
    obtain ⟨hm₁,hmY⟩ := mem_Icc.mp hm
    have hp := Nat.mul_pos hq₁ hm₁
    refine mem_sigma.mpr ⟨mem_Icc.mpr ⟨hp,?_⟩,Nat.mem_divisors.mpr ⟨dvd_mul_right _ _,hp.ne'⟩⟩
    simpa only [mul_comm m q] using (Nat.le_div_iff_mul_le hq₁).mp hmY
  · intro ⟨q,m⟩ ha ⟨s,n⟩ hb H
    have he : q*m=s*n := congrArg Sigma.fst H
    have hq : q=s := congrArg (fun z : Σ _ : ℕ, ℕ => z.2) H
    subst s
    have h := (mem_Icc.mp (mem_sigma.mp ha).1).1
    have hm := Nat.eq_of_mul_eq_mul_left h he
    cases hm; rfl
  · intro ⟨d,q⟩ hz
    obtain ⟨hd,hq⟩ := mem_sigma.mp hz
    obtain ⟨hd₁,hdY⟩ := mem_Icc.mp hd
    have hq₁ := Nat.pos_of_mem_divisors hq
    have hqd := Nat.divisor_le hq
    have hdiv := Nat.dvd_of_mem_divisors hq
    refine ⟨⟨q,d/q⟩,mem_sigma.mpr ⟨mem_Icc.mpr ⟨hq₁,hqd.trans hdY⟩,
      mem_Icc.mpr ⟨Nat.div_pos hqd hq₁,Nat.div_le_div_right hdY⟩⟩,?_⟩
    dsimp; rw [Nat.mul_div_cancel' hdiv]
  · intro ⟨q,m⟩ hz
    have h := (mem_Icc.mp (mem_sigma.mp hz).1).1
    dsimp; rw [Nat.mul_div_cancel_left _ h]

/-- Negative additive phase used for Fourier synthesis. -/
noncomputable def phase (t : ℝ) (n : ℕ) : ℂ := Complex.exp (-(2*Real.pi*Complex.I*t*n))

private lemma char_nat {q : ℕ} [NeZero q] (n : ℕ) :
    ZMod.stdAddChar (n : ZMod q) = Complex.exp (2*Real.pi*Complex.I*n/q) := by
  rw [ZMod.stdAddChar_apply,ZMod.toCircle_natCast]

private lemma phase_char {d : ℕ} [NeZero d] (k n : ℕ) :
    phase ((k:ℝ)/d) n = ZMod.stdAddChar (-((n : ZMod d)*(k : ZMod d))) := by
  rw [AddChar.map_neg_eq_inv,← Nat.cast_mul,char_nat,← Complex.exp_neg]
  unfold phase; push_cast; congr 1; ring

private lemma char_project (q m : ℕ) [NeZero q] [NeZero m] [NeZero (q*m)]
    (x : (ZMod (q*m))ˣ) (h : ℕ) :
    ZMod.stdAddChar ((reduceUnit q m x : ZMod q)*(h : ZMod q)) =
      ZMod.stdAddChar ((x : ZMod (q*m))*((m*h : ℕ) : ZMod (q*m))) := by
  let a := (x : ZMod (q*m)).val
  have ha : (a : ZMod (q*m))=(x : ZMod (q*m)) := ZMod.natCast_zmod_val _
  change ZMod.stdAddChar (ZMod.castHom _ _ (x : ZMod (q*m)) * _) = _
  rw [← ha,map_natCast,← Nat.cast_mul,← Nat.cast_mul,char_nat,char_nat]
  have hmc : (m:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne _)
  have hqc : (q:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne _)
  push_cast; congr 1; field_simp

private noncomputable def fullCoeff (d w k : ℕ) : ℂ :=
  if H : d%2=1 ∧ w%2=1 ∧ w.Coprime d then
    let _ : NeZero d := ⟨by omega⟩
    let v := ZMod.unitOfCoprime w H.2.2
    (-(∑ x : (ZMod d)ˣ, ((-1 : ℤ)^((↑(v/x) : ZMod d).val) : ℂ) *
      ZMod.stdAddChar ((x : ZMod d)*(k : ZMod d))) / (d:ℂ))
  else 0

private lemma coefficient_project {q m : ℕ} [NeZero q] [NeZero m] (w h : ℕ) :
    ThetaReciprocalBlocks.numeratorVector q m w (h : ZMod q) = fullCoeff (q*m) w (m*h) := by
  have hp : (q*m)%2=1 ↔ m%2=1 ∧ q%2=1 := by rw [Nat.mul_mod]; rcases Nat.mod_two_eq_zero_or_one q with hq|hq <;> rcases Nat.mod_two_eq_zero_or_one m with hm|hm <;> simp [hq,hm]
  unfold ThetaReciprocalBlocks.numeratorVector fullCoeff
  split_ifs with H H' H'
  · simp only [reciprocalCoeff,Nat.cast_mul]
    congr 2
    apply sum_congr rfl; intro x _
    rw [← Nat.cast_mul,← char_project]
  · exact (H' ⟨hp.mpr ⟨H.1,H.2.1⟩,H.2.2⟩).elim
  · exact (H ⟨(hp.mp H'.1).1,(hp.mp H'.1).2,H'.2⟩).elim
  · rfl

private lemma freq_orthog {d : ℕ} [NeZero d] (a : ZMod d) :
    ∑ k ∈ range d, ZMod.stdAddChar (a*(k : ZMod d)) = if a=0 then (d:ℂ) else 0 := by
  calc
    _ = ∑ t : ZMod d, ZMod.stdAddChar (a*t) := by
      apply sum_bij (fun (k : ℕ) _ => (k : ZMod d))
      · intros; exact mem_univ _
      · intro k hk j hj H
        simpa only [ZMod.val_natCast_of_lt (mem_range.mp hk),ZMod.val_natCast_of_lt (mem_range.mp hj)]
          using congrArg ZMod.val H
      · intro t _; exact ⟨t.val,mem_range.mpr t.val_lt,ZMod.natCast_zmod_val _⟩
      · intros; rfl
    _ = _ := by
      split_ifs with ha
      · simp [ha,ZMod.card]
      · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar d ha)

/-- Parity on a primitive numerator, with both parity and unit support made explicit. -/
noncomputable def primitiveTerm (p d w : ℕ) : ℂ :=
  if d%2=1 ∧ w%2=1 ∧ w.Coprime d then ThetaCotangentTriangle.reciprocalSign p d w else 0

private lemma full_inversion {d p : ℕ} (hc : p.Coprime d) (w : ℕ) :
    ∑ k ∈ range d, fullCoeff d w k * phase ((k:ℝ)/d) p = primitiveTerm p d w := by
  unfold fullCoeff primitiveTerm
  split_ifs with H
  · let : NeZero d := ⟨by omega⟩
    let v := ZMod.unitOfCoprime w H.2.2
    let n := ZMod.unitOfCoprime p hc
    let s (x : (ZMod d)ˣ) : ℂ := ((-1 : ℤ)^((↑(v/x) : ZMod d).val) : ℂ)
    have he (x : (ZMod d)ˣ) (k : ℕ) : ZMod.stdAddChar ((x : ZMod d)*(k : ZMod d))*phase ((k:ℝ)/d) p =
        ZMod.stdAddChar (((x:ZMod d)-(p:ZMod d))*(k:ZMod d)) := by
      rw [phase_char,← AddChar.map_add_eq_mul,sub_mul,sub_eq_add_neg]
    have hh : (∑ k ∈ range d, (-(∑ x : (ZMod d)ˣ, s x*ZMod.stdAddChar ((x : ZMod d)*(k : ZMod d)))/d) *
        phase ((k:ℝ)/d) p) = -s n := by
      simp_rw [div_mul_eq_mul_div,neg_mul,sum_mul,mul_assoc,he]
      rw [← sum_div,sum_neg_distrib,sum_comm]
      simp_rw [← mul_sum,freq_orthog,sub_eq_zero]
      have hxn (x : (ZMod d)ˣ) : (x : ZMod d)=(p : ZMod d) ↔ x=n := by
        change (x : ZMod d)=(n : ZMod d) ↔ _; exact Units.val_inj
      simp_rw [hxn,mul_ite,mul_zero,sum_ite_eq',mem_univ,if_true]
      field_simp [show (d:ℂ) ≠ 0 from Nat.cast_ne_zero.mpr (NeZero.ne _)]
    change _ = (ThetaCotangentTriangle.reciprocalSign p d w : ℂ)
    rw [hh]
    have hr : (↑(v/n) : ZMod d) = (w : ZMod d)*(p : ZMod d)⁻¹ := by
      rw [div_eq_mul_inv,Units.val_mul,← ZMod.inv_coe_unit]; rfl
    dsimp only [s]; rw [hr]
    unfold ThetaCotangentTriangle.reciprocalSign
    simp only [Int.cast_neg,Int.cast_one]
    rcases Nat.even_or_odd ((w : ZMod d)*(p : ZMod d)⁻¹).val with he|ho
    · rw [he.neg_one_pow,if_neg (by have := Nat.even_iff.mp he; omega)]; norm_num
    · rw [ho.neg_one_pow,if_pos (Nat.odd_iff.mp ho)]; norm_num
  · simp

private lemma select_freq {d p : ℕ} (hd : 0<d) (hc : p.Coprime d) (w : ℕ) :
    (∑ q ∈ d.divisors, ∑ h ∈ (range q).filter (·.Coprime q),
      (if hq : q=0 then 0 else
        let _ : NeZero q := ⟨hq⟩
        ThetaReciprocalBlocks.numeratorVector q (d/q) w (h : ZMod q)) * phase ((h:ℝ)/q) p) =
    primitiveTerm p d w := by
  rw [← full_inversion hc w,← sum_reduced hd]
  apply sum_congr rfl; intro q hq
  apply sum_congr rfl; intro h _
  have hq' := Nat.pos_of_mem_divisors hq
  let : NeZero q := ⟨hq'.ne'⟩
  have hm := Nat.div_pos (Nat.divisor_le hq) hq'
  let : NeZero (d/q) := ⟨hm.ne'⟩
  rw [dif_neg hq'.ne',coefficient_project,Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hq)]
  congr 2
  have he : (d:ℝ) = q*(↑(d/q : ℕ) : ℝ) := by exact_mod_cast (Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hq)).symm
  have hmr : (↑(d/q : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  push_cast; rw [he]; field_simp


open ThetaReciprocalBlocks

private noncomputable def scaledTerm (p d w : ℕ) : ℂ :=
  ((w:ℂ)⁻¹) * primitiveTerm p d w

private noncomputable def rawTerm (p u v : ℕ) : ℂ :=
  if u%2=1 ∧ v%2=1 then (ThetaCotangentTriangle.reciprocalSign p u v : ℂ)/((u:ℂ)*v) else 0

private lemma odd_prod (a b : ℕ) : (a*b)%2=1 ↔ a%2=1 ∧ b%2=1 := by
  rw [Nat.mul_mod]; rcases Nat.mod_two_eq_zero_or_one a with ha|ha <;>
    rcases Nat.mod_two_eq_zero_or_one b with hb|hb <;> simp [ha,hb]

private lemma raw_scaled {p g d w : ℕ} (hc : p.Coprime (g*d)) (hd : 0<d) (hw : w.Coprime d) :
    rawTerm p (g*d) (g*w) =
      (if g%2=1 then ((g:ℂ)^2)⁻¹ else 0) * ((d:ℂ)⁻¹*scaledTerm p d w) := by
  unfold rawTerm scaledTerm primitiveTerm
  simp only [odd_prod]
  by_cases hg : g%2=1 <;> by_cases hd' : d%2=1 <;> by_cases hw' : w%2=1 <;> simp [hg,hd',hw']
  rw [reciprocalSign_cancel hg hd hc,if_pos hw]
  ring

private lemma hidden_coprime {p d w : ℕ} (h : ¬w.Coprime d) : scaledTerm p d w=0 := by
  simp [scaledTerm,primitiveTerm,h]

private lemma factor_rows (K Y : ℕ) (F f₀ : ℕ → ℕ → ℂ)
    (hscaled : ∀ g d w, 0<g → 0<d → g*d≤Y → w.Coprime d →
      F (g*d) (g*w) = (if g%2=1 then ((g:ℂ)^2)⁻¹ else 0)*((d:ℂ)⁻¹*f₀ d w))
    (hzero : ∀ d w, ¬w.Coprime d → f₀ d w=0) :
    (∑ u ∈ Icc 1 Y, ∑ v ∈ range (K*u), F u v) =
    ∑ d ∈ Icc 1 Y, (commonWeight Y d : ℂ)/(d:ℂ) *
      ∑ w ∈ range (K*d), f₀ d w := by
  let f (d g : ℕ) : ℂ := (if g%2=1 then ((g:ℂ)^2)⁻¹ else 0) *
      ((d:ℂ)⁻¹*∑ w ∈ range (K*d), f₀ d w)
  calc
    _ = ∑ u ∈ Icc 1 Y, ∑ d ∈ u.divisors, f d (u/d) := by
      apply sum_congr rfl; intro u hu
      rw [← sum_reduced_window K (mem_Icc.mp hu).1]
      apply sum_congr rfl; intro d hd
      have he := Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd)
      have H : ∀ w, w.Coprime d → F u ((u/d)*w) =
          (if (u/d)%2=1 then ((↑(u/d) : ℂ)^2)⁻¹ else 0)*((d:ℂ)⁻¹*f₀ d w) := by
        intro w hw
        calc
          _ = F ((u/d)*d) ((u/d)*w) := by rw [he]
          _ = _ := hscaled _ _ _ (Nat.div_pos (Nat.divisor_le hd) (Nat.pos_of_mem_divisors hd)) (Nat.pos_of_mem_divisors hd) (by rw [he]; exact (mem_Icc.mp hu).2) hw
      dsimp [f]; rw [mul_sum,mul_sum,sum_filter]
      apply sum_congr rfl; intro w _
      by_cases hw : w.Coprime d
      · rw [if_pos hw]; exact H w hw
      · rw [if_neg hw,hzero d w hw]; simp
    _ = ∑ d ∈ Icc 1 Y, ∑ g ∈ Icc 1 (Y/d), f d g := (sum_by_product Y f).symm
    _ = _ := by
      apply sum_congr rfl; intro d _
      unfold commonWeight
      push_cast
      dsimp [f]; rw [← sum_mul,sum_filter]
      ring

private lemma reduced_rows {p Y : ℕ} (hp : ∀ d ∈ Icc 1 Y, p.Coprime d) :
    (∑ u ∈ Icc 1 Y, ∑ v ∈ range u, rawTerm p u v) =
    ∑ d ∈ Icc 1 Y, ((commonWeight Y d : ℝ) : ℂ)/(d:ℂ) *
      ∑ w ∈ range d, scaledTerm p d w := by
  simpa only [one_mul] using factor_rows 1 Y (rawTerm p) (scaledTerm p)
    (fun g d w hg hd hY hw => raw_scaled (hp _ (mem_Icc.mpr ⟨Nat.mul_pos hg hd,hY⟩)) hd hw)
    (fun _ _ => hidden_coprime)

/-- Enumerate the odd members of a finite interval by their half indices. -/
theorem odds_interval {A : Type*} [AddCommMonoid A] (s : Finset ℕ) (J : ℕ)
    (hs : ∀ n, n ∈ s → n%2=1 → n/2<J)
    (ht : ∀ j<J, 2*j+1 ∈ s) (f : ℕ → A) :
    (∑ n ∈ s, if n%2=1 then f n else 0) = ∑ j ∈ range J, f (2*j+1) := by
  rw [← sum_filter]
  apply sum_bij (fun n _ => n/2)
  · intro n hn; exact mem_range.mpr (hs _ (mem_filter.mp hn).1 (mem_filter.mp hn).2)
  · intro a ha b hb hab
    have := (mem_filter.mp ha).2; have := (mem_filter.mp hb).2; omega
  · intro j hj
    refine ⟨2*j+1,mem_filter.mpr ⟨ht _ (mem_range.mp hj),by omega⟩,by omega⟩
  · intro n hn; congr 1; have := (mem_filter.mp hn).2; omega

private lemma raw_as_rational (p J : ℕ) :
    (∑ u ∈ Icc 1 (2*J), ∑ v ∈ range u, rawTerm p u v) =
      (ThetaReciprocalCutoff.rationalPrefix p J : ℂ) := by
  let f (u v : ℕ) : ℂ := (ThetaCotangentTriangle.reciprocalSign p u v : ℂ)/((u:ℂ)*v)
  have hr (u : ℕ) : ∑ v ∈ range u, rawTerm p u v =
      (if u%2=1 then ∑ v ∈ range u, (if v%2=1 then f u v else 0) else 0) := by
    by_cases hu : u%2=1 <;> simp [f,rawTerm,hu]
  simp_rw [hr]
  rw [odds_interval _ J (by intro n hn; have := (mem_Icc.mp hn).2; omega)
    (by intro j hj; apply mem_Icc.mpr; omega)]
  unfold ThetaReciprocalCutoff.rationalPrefix
  push_cast
  apply sum_congr rfl; intro j _
  rw [odds_interval _ j (by intro n hn; have := mem_range.mp hn; omega)
    (by intro k hk; exact mem_range.mpr (by omega))]
  apply sum_congr rfl; intro k _
  dsimp [f]; push_cast; ring

private noncomputable def scalarCoeff (q m w h : ℕ) : ℂ :=
  if hq : q=0 then 0 else
    let _ : NeZero q := ⟨hq⟩
    numeratorVector q m w (h : ZMod q)

private lemma block_expanded (L : ℕ → ℕ) (Y q h : ℕ) (hq : 0<q) :
    windowCoordinate L Y q h = ∑ m ∈ Icc 1 (Y/q),
      ((commonWeight Y (q*m) : ℂ) / ((q*m : ℕ) : ℂ)) *
      ∑ k ∈ range (L (q*m)), ((↑(k+1 : ℕ) : ℂ)⁻¹)*scalarCoeff q m (k+1) h := by
  let : NeZero q := ⟨hq.ne'⟩
  let e : EuclideanSpace ℂ (ZMod q) →ₗ[ℝ] ℂ := PiLp.projₗ 2 _ (h : ZMod q)
  rw [windowCoordinate,dif_neg hq.ne']
  change e (windowBlock L Y q) = _
  unfold windowBlock numeratorWindow
  simp only [map_sum,map_smul,Complex.real_smul]
  unfold scalarCoeff
  simp only [dif_neg hq.ne']
  apply sum_congr rfl; intro m _
  push_cast; rfl

/-- Fourier synthesis of the rational extension on every integer. -/
noncomputable def windowExtension (L : ℕ → ℕ) (Y n : ℕ) : ℂ :=
  ∑ q ∈ Icc 1 Y, ∑ h ∈ (range q).filter (·.Coprime q),
    windowCoordinate L Y q h * phase ((h:ℝ)/q) n

private lemma window_rows (L : ℕ → ℕ) {Y p : ℕ} (hp : ∀ d ∈ Icc 1 Y, p.Coprime d) :
    windowExtension L Y p = ∑ d ∈ Icc 1 Y, (commonWeight Y d : ℂ)/(d:ℂ) *
      ∑ k ∈ range (L d), scaledTerm p d (k+1) := by
  let F (q m : ℕ) := (commonWeight Y (q*m) : ℂ) / ((q*m : ℕ) : ℂ) *
      ∑ k ∈ range (L (q*m)), (↑(k+1 : ℕ) : ℂ)⁻¹ *
        ∑ h ∈ (range q).filter (·.Coprime q), scalarCoeff q m (k+1) h * phase ((h:ℝ)/q) p
  calc
    windowExtension L Y p = ∑ q ∈ Icc 1 Y, ∑ m ∈ Icc 1 (Y/q), F q m := by
      unfold windowExtension
      apply sum_congr rfl; intro q hq
      simp_rw [block_expanded L Y q _ (mem_Icc.mp hq).1,sum_mul]
      rw [sum_comm]
      apply sum_congr rfl; intro m _
      dsimp [F]
      simp_rw [mul_assoc,sum_mul,mul_assoc,← mul_sum]
      congr 1
      rw [sum_comm]; simp_rw [← mul_sum]
    _ = ∑ d ∈ Icc 1 Y, ∑ q ∈ d.divisors, F q (d/q) := sum_by_product Y F
    _ = _ := by
      apply sum_congr rfl; intro d hd
      have hF (q : ℕ) (hq : q ∈ d.divisors) : F q (d/q) = (commonWeight Y d : ℂ)/(d:ℂ) *
          ∑ k ∈ range (L d), (↑(k+1 : ℕ) : ℂ)⁻¹ *
            ∑ h ∈ (range q).filter (·.Coprime q), scalarCoeff q (d/q) (k+1) h * phase ((h:ℝ)/q) p := by
        dsimp only [F]; rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hq)]
      rw [sum_congr rfl hF,← mul_sum,sum_comm]
      congr 1
      have he (w : ℕ) : (∑ q ∈ d.divisors, ∑ h ∈ (range q).filter (·.Coprime q),
          scalarCoeff q (d/q) w h * phase ((h:ℝ)/q) p) = primitiveTerm p d w :=
        select_freq (mem_Icc.mp hd).1 (hp d hd) w
      simp_rw [← mul_sum,he]
      rfl

/-- Fourier synthesis for the lower triangle. -/
noncomputable def extension : ℕ → ℕ → ℂ := windowExtension (fun d => d-1)

private lemma extension_rows {Y p : ℕ} (hp : ∀ d ∈ Icc 1 Y, p.Coprime d) :
    extension Y p = ∑ d ∈ Icc 1 Y, (commonWeight Y d : ℂ)/(d:ℂ) *
      ∑ w ∈ range d, scaledTerm p d w := by
  rw [extension,window_rows _ hp]
  apply sum_congr rfl; intro d hd
  congr 1
  have hf := sum_range_succ' (scaledTerm p d) (d-1)
  rw [Nat.sub_add_cancel (mem_Icc.mp hd).1] at hf
  simpa [scaledTerm] using hf.symm

/-- For every argument coprime to the denominators, the extension exactly interpolates the
previous rational cutoff. In particular it interpolates every prime above the cutoff. -/
theorem extension_rationalPrefix {p J : ℕ} (hp : ∀ d ∈ Icc 1 (2*J), p.Coprime d) :
    extension (2*J) p = (ThetaReciprocalCutoff.rationalPrefix p J : ℂ) := by
  rw [extension_rows hp,← reduced_rows hp,raw_as_rational]

theorem extension_at_prime {p J : ℕ} (hp : Nat.Prime p) (hJ : 2*J<p) :
    extension (2*J) p = (ThetaReciprocalCutoff.rationalPrefix p J : ℂ) := by
  apply extension_rationalPrefix
  intro d hd
  exact hp.coprime_iff_not_dvd.mpr fun h =>
    ((mem_Icc.mp hd).2.trans_lt hJ).not_ge (Nat.le_of_dvd (mem_Icc.mp hd).1 h)

/-- At reduced denominator one every numerator is an exact multiple. Otherwise
the cone of width K has positive numerators 1 through Kd−1. -/
def coneWindow (K d : ℕ) : ℕ := if d=1 then 0 else K*d-1

/-- On arguments coprime to all denominators, the wide Fourier expansion gives
the complete rational cone with exact multiples removed. -/
theorem windowExtension_nondivisible {p Y K : ℕ} (hK : 0<K) (hp : ∀ d ∈ Icc 1 Y, p.Coprime d) :
    windowExtension (coneWindow K) Y p =
      ∑ u ∈ Icc 1 Y, ∑ v ∈ range (K*u),
        (if u%2=1 ∧ v%2=1 ∧ ¬u∣v then
          (ThetaCotangentTriangle.reciprocalSign p u v:ℂ)/((u:ℂ)*v) else 0) := by
  let F (u v : ℕ) : ℂ := if u∣v then 0 else rawTerm p u v
  let f (d w : ℕ) : ℂ := if d=1 then 0 else scaledTerm p d w
  have hr := factor_rows K Y F f (by
    intro g d w hg hd hY hw
    have hh : g*d ∣ g*w ↔ d=1 := by
      rw [Nat.mul_dvd_mul_iff_left hg]
      exact ⟨fun h => by simpa only [Nat.gcd_eq_right h] using hw.gcd_eq_one,fun h => h ▸ one_dvd _⟩
    by_cases h : d=1
    · simp [F,f,h]
    · simpa only [F,f,if_neg h,if_neg (mt hh.mp h)] using
        raw_scaled (g:=g) (w:=w) (hp _ (mem_Icc.mpr ⟨Nat.mul_pos hg hd,hY⟩)) hd hw) (by
    intro d w hw; simp [f,hidden_coprime hw])
  rw [window_rows _ hp]
  apply Eq.trans _ (hr.symm.trans ?_)
  · apply sum_congr rfl; intro d hd
    congr 1
    by_cases h : d=1
    · simp [coneWindow,h,f]
    · simp only [coneWindow,if_neg h,f]
      have hk : 0<K*d := Nat.mul_pos hK (mem_Icc.mp hd).1
      have hf := sum_range_succ' (scaledTerm p d) (K*d-1)
      rw [Nat.sub_add_cancel hk] at hf
      simpa [scaledTerm] using hf.symm
  · apply sum_congr rfl; intro u _
    apply sum_congr rfl; intro v _
    dsimp [F,rawTerm]; split_ifs <;> simp_all

end Arxiv.«2501.03234».ThetaReciprocalInversion
#print axioms Arxiv.«2501.03234».ThetaReciprocalInversion.sum_reduced
#print axioms Arxiv.«2501.03234».ThetaReciprocalInversion.sum_by_product
#print axioms Arxiv.«2501.03234».ThetaReciprocalInversion.extension_rationalPrefix
#print axioms Arxiv.«2501.03234».ThetaReciprocalInversion.extension_at_prime
#print axioms Arxiv.«2501.03234».ThetaReciprocalInversion.sum_reduced_window
#print axioms Arxiv.«2501.03234».ThetaReciprocalInversion.odds_interval
#print axioms Arxiv.«2501.03234».ThetaReciprocalInversion.windowExtension_nondivisible
