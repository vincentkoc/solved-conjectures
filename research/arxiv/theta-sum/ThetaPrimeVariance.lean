import ThetaSievedWindows
import ThetaPrimeMeanSquare

/-! A bounded prime-normalized second moment for the canonical signed theta sum. -/
namespace Arxiv.«2501.03234».ThetaPrimeVariance

open Finset ThetaReciprocalInversion ThetaReciprocalBlocks ThetaDenominatorTails ThetaRowCorrelations

private noncomputable def E (p : ℕ) : ℝ := (S p:ℝ)/p-Real.log p/2

/-- The elementary Chebyshev bound for a subset of the prime scale. -/
theorem band_card {N : ℕ} (hN : 2≤N) (s : Finset ℕ)
    (hs : ∀ p∈s, p.Prime ∧ N<p ∧ p≤N^64) :
    (s.card:ℝ) ≤ Real.log 4*(N:ℝ)^64/Real.log N := by
  have hp : (1:ℝ)<N := by exact_mod_cast hN
  rw [le_div_iff₀ (Real.log_pos hp)]
  have hsub : s⊆Nat.primesLE (N^64) := fun p h => Nat.mem_primesLE.mpr ⟨(hs p h).2.2,(hs p h).1⟩
  calc
    _ = ∑ _ ∈ s,Real.log N := by simp
    _ ≤ ∑ p∈s,Real.log p := sum_le_sum (fun p h => Real.log_le_log (by linarith) (by exact_mod_cast (hs p h).2.1.le))
    _ ≤ ∑ p∈Nat.primesLE (N^64),Real.log p := sum_le_sum_of_subset_of_nonneg hsub
      (fun p h _ => Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primesLE h).pos))
    _ ≤ Real.log 4*((N^64:ℕ):ℝ) := (Chebyshev.theta_eq_sum_primesLE_log (N^64)).symm.le.trans
      (Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg (N^64) (α:=ℝ)))
    _ = _ := by rw [Nat.cast_pow]

private theorem scale_second : ∃ C : ℝ, 0≤C ∧ ∀ N : ℕ, 2≤N →
    ∑ p∈Nat.primesLE (N^64),E p^2 ≤ C*(N:ℝ)^64/Real.log N := by
  obtain ⟨A,hA,hw⟩ := ThetaPrimeMeanSquare.scale_window_control
  obtain ⟨V,hV,hvar⟩ := cut_variance
  obtain ⟨U,hU,hlow⟩ := ThetaSievedWindows.low_prime_band
  let B := ∑' g : ℕ, ((g:ℝ)^2)⁻¹
  let c := 8/Real.pi^2
  let M := |E 2|+17000
  have hB : 0≤B := tsum_nonneg (fun i => by positivity)
  have hc : 0≤c := by dsimp [c]; positivity
  refine ⟨M^2+3*A^2*Real.log 4+3*c^2*(U*B^2+64*V),by positivity,?_⟩
  intro N hN
  let P := Nat.primesLE (N^64)
  let Q := P.filter (fun p => N^56≤p)
  let R := P.filter (fun p => ¬N^56≤p)
  let Y := 2*N^52
  have h1 : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  have hl : 0<Real.log N := Real.log_pos (by exact_mod_cast (show 1<N by omega))
  have hY : N≤Y := by dsimp [Y]; have := Nat.le_self_pow (by decide : 52≠0) N; omega
  have hQ (p : ℕ) (hp : p∈Q) : p.Prime ∧ N<p ∧ p≤N^64 := by
    obtain ⟨hp',hlo⟩ := mem_filter.mp hp
    exact ⟨Nat.prime_of_mem_primesLE hp',hY.trans_lt (ThetaPrimeDensity.cutoff_inside hN hlo),
      Nat.le_of_mem_primesLE hp'⟩
  obtain ⟨K,hK,hctrl⟩ := hw N hN
  let a := commonWeight Y
  let L := low N K a
  let H := windowExtension (above N K) Y
  have hb (d) (_ : d∈Icc 2 N) : |a d|≤B := by
    rw [abs_of_nonneg (commonWeight_bounds Y d).1]; exact (commonWeight_bounds Y d).2
  have Hlow := hlow N hN K a B hB hb Q hQ
  have hcut : ∀ d≤N, above N K d=0 := fun d hd => if_pos hd
  have hsub : Q⊆range (N^64+1) := fun p hp => mem_range.mpr (Nat.lt_succ_of_le (hQ p hp).2.2)
  have Hhigh : ∑ p∈Q,‖H p‖^2 ≤ 64*V*(N:ℝ)^64/Real.log N := by
    apply (sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)).trans
      ((hvar (show 1≤N by omega) _ hcut N (by omega)).trans ?_)
    have hx := Real.log_natCast_le_rpow_div N (show (0:ℝ)<1/64 by norm_num)
    have hn : 0<(N:ℝ)^(1/64:ℝ) := Real.rpow_pos_of_pos (by linarith) _
    rw [div_le_div_iff₀ hn hl]
    have hy := mul_le_mul_of_nonneg_left hx (show 0≤V*(N:ℝ)^64 by positivity)
    linarith only [hy]
  have hcard := band_card hN Q hQ
  have hbig (p) (hp : p∈Q) : E p^2 ≤ 3*A^2+3*c^2*(L p^2+‖H p‖^2) := by
    have Hctrl := hctrl p (hQ p hp).1 (mem_filter.mp hp).2 (hQ p hp).2.2
    have hYp := ThetaPrimeDensity.cutoff_inside hN (mem_filter.mp hp).2
    have hcop (d) (hd : d∈Icc 1 Y) : p.Coprime d := (hQ p hp).1.coprime_iff_not_dvd.mpr
      (fun h => ((mem_Icc.mp hd).2.trans_lt hYp).not_ge (Nat.le_of_dvd (mem_Icc.mp hd).1 h))
    have hh := window_split hY K hK hcop
    have hnorm : ‖windowExtension K Y p‖ ≤ |L p|+‖H p‖ := by
      rw [sub_eq_iff_eq_add.mp hh]; simpa only [Complex.norm_real,Real.norm_eq_abs] using norm_add_le (L p:ℂ) (H p)
    have hh' : |E p| ≤ A+c*(|L p|+‖H p‖) := Hctrl.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hnorm hc))
    have hs := pow_le_pow_left₀ (abs_nonneg _) hh' 2
    rw [sq_abs] at hs
    nlinarith only [hs,sq_nonneg (A-c*|L p|),sq_nonneg (A-c*‖H p‖),sq_nonneg (c*|L p|-c*‖H p‖),sq_abs (L p)]
  have hQB : ∑ p∈Q,E p^2 ≤ (3*A^2*Real.log 4+3*c^2*(U*B^2+64*V))*(N:ℝ)^64/Real.log N := by
    apply (sum_le_sum hbig).trans
    rw [sum_add_distrib,sum_const,nsmul_eq_mul,← mul_sum,sum_add_distrib]
    have H := add_le_add (mul_le_mul_of_nonneg_right hcard (show 0≤3*A^2 by positivity))
      (mul_le_mul_of_nonneg_left (add_le_add Hlow Hhigh) (show 0≤3*c^2 by positivity))
    exact H.trans_eq (by ring)
  have hR : R⊆range (N^56) := fun p hp => mem_range.mpr (lt_of_not_ge (mem_filter.mp hp).2)
  have hcardR : (R.card:ℝ)≤(N:ℝ)^56 := by
    have H := card_le_card hR; rw [card_range] at H; exact_mod_cast H
  have hRB : ∑ p∈R,E p^2 ≤ M^2*(N:ℝ)^64/Real.log N := by
    have he (p) (hp : p∈R) : E p^2≤(M*(N:ℝ)^2)^2 := by
      obtain ⟨hp',_⟩ := mem_filter.mp hp
      simpa only [E,M,Nat.cast_ofNat,sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (ThetaPrimeMeanSquare.small_scale_error hN
        (Nat.prime_of_mem_primesLE hp') (Nat.le_of_mem_primesLE hp')) 2
    apply (sum_le_sum he).trans
    rw [sum_const,nsmul_eq_mul]
    apply (mul_le_mul_of_nonneg_right hcardR (sq_nonneg _)).trans
    rw [le_div_iff₀ hl]
    calc
      _ ≤ (N:ℝ)^56*(M*(N:ℝ)^2)^2*N := mul_le_mul_of_nonneg_left (Real.log_le_self (Nat.cast_nonneg _)) (by positivity)
      _ = M^2*(N:ℝ)^61 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1 (by decide)) (sq_nonneg _)
  have he := sum_filter_add_sum_filter_not P (fun p => N^56≤p) (fun p => E p^2)
  change ∑ p∈Q,E p^2+∑ p∈R,E p^2=∑ p∈P,E p^2 at he
  change ∑ p∈P,E p^2≤_
  rw [← he]; exact (add_le_add hQB hRB).trans_eq (by ring)

/-- The total squared additive error of the original signed theta sum is
bounded on the scale of the number of primes. -/
theorem prime_second_moment : ∃ C : ℝ, 0<C ∧ ∀ X : ℕ, 2≤X →
    ∑ p∈Nat.primesLE X,((S p:ℝ)/p-Real.log p/2)^2 ≤ C*X/Real.log X := by
  obtain ⟨C,hC,h⟩ := scale_second
  refine ⟨64*(C+1)*2^64,by positivity,?_⟩
  intro X hX
  let r := Nat.nthRoot 64 X
  let N := r+1
  have hr : 1≤r := (Nat.le_nthRoot_iff (by decide : (64:ℕ)≠0)).mpr (by simpa using (show 1≤X by omega))
  have hN : 2≤N := by dsimp [N]; omega
  have hL : X<N^64 := Nat.lt_pow_nthRoot_add_one (by decide) X
  have hl : r^64≤X := Nat.pow_nthRoot_le (Or.inl (by decide))
  have hnr : N^64≤2^64*X := calc
    _ ≤ (2*r)^64 := Nat.pow_le_pow_left (by dsimp [N]; omega) _
    _ = _ := Nat.mul_pow ..
    _ ≤ _ := Nat.mul_le_mul_left _ hl
  have hsub : Nat.primesLE X⊆Nat.primesLE (N^64) := by
    intro p hp; obtain ⟨hh,hp'⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨hh.trans hL.le,hp'⟩
  change ∑ p∈Nat.primesLE X,E p^2≤_
  apply (sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)).trans ((h N hN).trans ?_)
  have hx : (1:ℝ)<X := by exact_mod_cast hX
  have hn : (1:ℝ)<N := by exact_mod_cast hN
  have hsize : (N:ℝ)^64≤2^64*(X:ℝ) := by exact_mod_cast hnr
  have hlog := Real.log_le_log (by linarith : (0:ℝ)<X) (show (X:ℝ)≤(N:ℝ)^64 by exact_mod_cast hL.le)
  rw [Real.log_pow] at hlog
  rw [div_le_div_iff₀ (Real.log_pos hn) (Real.log_pos hx)]
  have H := mul_le_mul hsize hlog (Real.log_pos hx).le (by positivity)
  have hh := mul_le_mul_of_nonneg_left H hC
  have rest := mul_nonneg (show (0:ℝ)≤(2:ℝ)^64*X by positivity) (Real.log_pos hn).le
  norm_num only [Nat.cast_ofNat] at hh
  nlinarith only [hh,rest]

/-- Bounded mean squared error per prime. The denominator is the actual number of primes. -/
theorem prime_mean_squared_error : ∃ C : ℝ, 0<C ∧ ∀ᶠ X : ℕ in Filter.atTop,
    (∑ p∈Nat.primesLE X,((S p:ℝ)/p-Real.log p/2)^2)/Nat.primeCounting X ≤ C := by
  obtain ⟨A,hA,H⟩ := prime_second_moment
  let b := Real.log 2/2
  have hb : 0<b := by dsimp [b]; positivity
  refine ⟨A/b,by positivity,?_⟩
  filter_upwards [ThetaPrimeDensity.prime_count_lower,Filter.eventually_ge_atTop 2] with X hcount hX
  have hx : (1:ℝ)<X := by exact_mod_cast hX
  have hl := Real.log_pos hx
  change b*(X:ℝ)≤(Nat.primeCounting X:ℝ)*Real.log X at hcount
  have hp : 0<(Nat.primeCounting X:ℝ) := by
    nlinarith only [hcount,mul_pos hb (show (0:ℝ)<X by linarith),hl,Nat.cast_nonneg (Nat.primeCounting X) (α:=ℝ)]
  have hh := (le_div_iff₀ hl).mp (H X hX)
  rw [div_le_iff₀ hp,div_mul_eq_mul_div,le_div_iff₀ hb]
  apply le_of_mul_le_mul_right ?_ hl
  calc
    _ = ((∑ p∈Nat.primesLE X,((S p:ℝ)/p-Real.log p/2)^2)*Real.log X)*b := by ring
    _ ≤ (A*X)*b := mul_le_mul_of_nonneg_right hh hb.le
    _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hcount hA.le]

private noncomputable def rel (p : ℕ) : ℝ := (S p:ℝ)/((p:ℝ)*Real.log p)-1/2

private lemma rel_eq {p : ℕ} (hp : p.Prime) : rel p=E p/Real.log p := by
  have h1 : (1:ℝ)<p := by exact_mod_cast hp.two_le
  dsimp [rel,E]; field_simp [Real.log_ne_zero_of_pos_of_ne_one (by linarith : (0:ℝ)<p) h1.ne']

private lemma sqrt_log_cube {X : ℕ} (hX : 4≤X) :
    (X.sqrt:ℝ)*(Real.log X)^3 ≤ 216*(X:ℝ) := by
  let z := (X:ℝ)^(1/6:ℝ)
  have hz : 0≤z := by dsimp [z]; positivity
  have hz₆ : z^6=X := by dsimp [z]; rw [← Real.rpow_mul_natCast (Nat.cast_nonneg X)]; norm_num
  have hr : (X.sqrt:ℝ)^2≤X := by exact_mod_cast Nat.sqrt_le' X
  have hr' : (X.sqrt:ℝ)≤z^3 := by
    have h : (X.sqrt:ℝ)^2≤(z^3)^2 := by nlinarith only [hz₆,hr]
    exact le_of_pow_le_pow_left₀ (by decide : 2≠0) (by positivity) h
  have hlog := Real.log_nonneg (show (1:ℝ)≤X by exact_mod_cast (show 1≤X by omega))
  have hl : Real.log X≤6*z := by
    dsimp [z]; linarith only [Real.log_natCast_le_rpow_div X (show (0:ℝ)<1/6 by norm_num)]
  have H := mul_le_mul hr' (pow_le_pow_left₀ hlog hl 3) (by positivity) (by positivity)
  nlinarith only [H,hz₆]

/-- Finite two-sided relative mean-square rate, prior to normalization by the prime count. -/
theorem relative_square_sum : ∃ C : ℝ, 0<C ∧ ∀ X : ℕ, 4≤X →
    (∑ p∈Nat.primesLE X,((S p:ℝ)/((p:ℝ)*Real.log p)-1/2)^2)*(Real.log X)^3 ≤ C*X := by
  classical
  obtain ⟨A,hA,H⟩ := prime_second_moment
  obtain ⟨B,hB,G⟩ := ThetaPrimeMeanSquare.prime_error_second_moment
  let b := Real.log 2
  have hb : 0<b := Real.log_pos (by norm_num)
  refine ⟨216*(B/b^2)+4*A,by positivity,?_⟩
  intro X hX
  let R := X.sqrt
  let P := Nat.primesLE X
  let J := P.filter (fun p => p≤R)
  let K := P.filter (fun p => ¬p≤R)
  have hR : 2≤R := Nat.le_sqrt'.mpr (by simpa using hX)
  have hlog := Real.log_pos (show (1:ℝ)<X by exact_mod_cast (show 1<X by omega))
  have hJ : J⊆Nat.primesLE R := by
    intro p hp; obtain ⟨hP,hpR⟩ := mem_filter.mp hp; exact Nat.mem_primesLE.mpr ⟨hpR,Nat.prime_of_mem_primesLE hP⟩
  have hsmall : (∑ p∈J,rel p^2)*b^2 ≤ B*R := by
    rw [sum_mul]
    apply (sum_le_sum (g:=fun p => E p^2) _).trans
      ((sum_le_sum_of_subset_of_nonneg hJ (by intros; positivity)).trans (G R hR))
    intro p hp; have hpr := Nat.prime_of_mem_primesLE (mem_filter.mp hp).1
    have hl : b≤Real.log p := Real.log_le_log (by norm_num) (by exact_mod_cast hpr.two_le)
    rw [rel_eq hpr,div_pow,div_mul_eq_mul_div,div_le_iff₀ (sq_pos_of_pos (hb.trans_le hl))]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb.le hl 2) (sq_nonneg _)
  have hbig : (∑ p∈K,rel p^2)*(Real.log X)^2 ≤ 4*(A*X/Real.log X) := by
    rw [sum_mul]
    calc
      _ ≤ ∑ p∈K,4*E p^2 := by
        apply sum_le_sum; intro p hp
        obtain ⟨hP,hr⟩ := mem_filter.mp hp
        have hpr := Nat.prime_of_mem_primesLE hP
        have hℓ := Real.log_pos (show (1:ℝ)<p by exact_mod_cast hpr.two_le)
        have h := Real.log_le_log (show (0:ℝ)<X by exact_mod_cast (show 0<X by omega))
          (show (X:ℝ)≤(p:ℝ)^2 by exact_mod_cast (Nat.sqrt_lt'.mp (lt_of_not_ge hr)).le)
        rw [Real.log_pow] at h; norm_num at h
        rw [rel_eq hpr,div_pow,div_mul_eq_mul_div,div_le_iff₀ (sq_pos_of_pos hℓ)]
        have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog.le h 2) (sq_nonneg (E p))
        nlinarith only [hh]
      _ ≤ _ := by
        rw [← mul_sum]
        exact mul_le_mul_of_nonneg_left ((sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; positivity)).trans (H X (by omega))) (by norm_num)
  have hsmall' := mul_le_mul_of_nonneg_right ((le_div_iff₀ (sq_pos_of_pos hb)).mpr hsmall)
    (pow_nonneg hlog.le 3)
  have hx := mul_le_mul_of_nonneg_left (sqrt_log_cube hX) (show 0≤B/b^2 by positivity)
  have hbig' := mul_le_mul_of_nonneg_right hbig hlog.le
  rw [show 4*(A*X/Real.log X)*Real.log X = 4*A*X by field_simp] at hbig'
  have he := sum_filter_add_sum_filter_not P (fun p => p≤R) (fun p => rel p^2)
  change ∑ p∈J,rel p^2+∑ p∈K,rel p^2=∑ p∈P,rel p^2 at he
  change (∑ p∈P,rel p^2)*_≤_
  rw [← he,add_mul]
  dsimp only [R] at hsmall'
  rw [show B*(X.sqrt:ℝ)/b^2*(Real.log X)^3 = (B/b^2)*((X.sqrt:ℝ)*(Real.log X)^3) by ring] at hsmall'
  rw [show (∑ p∈K,rel p^2)*(Real.log X)^3 = (∑ p∈K,rel p^2)*(Real.log X)^2*Real.log X by ring]
  exact (add_le_add (hsmall'.trans hx) hbig').trans_eq (by ring)

/-- The root-mean-square relative error per prime is O(1/log X). -/
theorem prime_mean_relative_squared : ∃ C : ℝ, 0<C ∧ ∀ᶠ X : ℕ in Filter.atTop,
    (∑ p∈Nat.primesLE X,((S p:ℝ)/((p:ℝ)*Real.log p)-1/2)^2)/Nat.primeCounting X ≤
      C/(Real.log X)^2 := by
  obtain ⟨A,hA,H⟩ := relative_square_sum
  let b := Real.log 2/2
  have hb : 0<b := by dsimp [b]; positivity
  refine ⟨A/b,by positivity,?_⟩
  filter_upwards [ThetaPrimeDensity.prime_count_lower,Filter.eventually_ge_atTop 4] with X hcount hX
  let V := ∑ p∈Nat.primesLE X,rel p^2
  have hx : (1:ℝ)<X := by exact_mod_cast (show 1<X by omega)
  have hl := Real.log_pos hx
  change b*(X:ℝ)≤(Nat.primeCounting X:ℝ)*Real.log X at hcount
  have hp : 0<(Nat.primeCounting X:ℝ) := by nlinarith only [hcount,mul_pos hb (show (0:ℝ)<X by linarith),hl,Nat.cast_nonneg (Nat.primeCounting X) (α:=ℝ)]
  have hh : V*(Real.log X)^3≤A*X := H X hX
  change V/(Nat.primeCounting X)≤(A/b)/(Real.log X)^2
  rw [div_div,div_le_div_iff₀ hp (mul_pos hb (sq_pos_of_pos hl))]
  apply le_of_mul_le_mul_right ?_ hl
  nlinarith only [mul_le_mul_of_nonneg_right hh hb.le,mul_le_mul_of_nonneg_left hcount hA.le]

/-- A single constant bounds the prime count outside every additive window. -/
theorem prime_window_count : ∃ C : ℝ, 0<C ∧ ∀ X : ℕ, 2≤X → ∀ t : ℝ, 0<t →
    ((ThetaPrimeDensity.primeSet (fun p => t≤|(S p:ℝ)/p-Real.log p/2|) X).card:ℝ) ≤
      C*X/(Real.log X*t^2) := by
  classical
  obtain ⟨C,hC,H⟩ := prime_second_moment
  refine ⟨C,hC,?_⟩; intro X hX t ht
  let F := ThetaPrimeDensity.primeSet (fun p => t≤|E p|) X
  have hs : F⊆Nat.primesLE X := filter_subset _ _
  rw [← div_div,le_div_iff₀ (sq_pos_of_pos ht)]
  calc
    _ = ∑ _ ∈ F,t^2 := by simp [F,E]
    _ ≤ ∑ p∈F,E p^2 := by
      apply sum_le_sum; intro p hp; have he : t≤|E p| := (mem_filter.mp hp).2
      simpa only [sq_abs] using pow_le_pow_left₀ ht.le he 2
    _ ≤ _ := (sum_le_sum_of_subset_of_nonneg hs (by intros; positivity)).trans (H X hX)

/-- With the actual prime count as denominator, the mean absolute relative
error is O(1/log X). -/
theorem prime_mean_absolute_relative : ∃ C : ℝ, 0<C ∧ ∀ᶠ X : ℕ in Filter.atTop,
    (∑ p∈Nat.primesLE X,|(S p:ℝ)/((p:ℝ)*Real.log p)-1/2|)/Nat.primeCounting X ≤
      C/Real.log X := by
  obtain ⟨A,hA,H⟩ := prime_mean_relative_squared
  refine ⟨Real.sqrt A,Real.sqrt_pos.mpr hA,?_⟩
  filter_upwards [H,Filter.eventually_ge_atTop 2] with X h hX
  let P := Nat.primesLE X
  have hcard : 0<(Nat.primeCounting X:ℝ) := by
    have hh : 2∈P := Nat.mem_primesLE.mpr ⟨hX,Nat.prime_two⟩
    exact_mod_cast (Nat.primesLE_card_eq_primeCounting X ▸ (card_pos.mpr ⟨2,hh⟩ : 0<(Nat.primesLE X).card))
  have hl : 0<Real.log X := Real.log_pos (by exact_mod_cast hX)
  have hcs := sum_mul_sq_le_sq_mul_sq P (fun _ => (1:ℝ)) (fun p => |rel p|)
  simp only [one_mul,one_pow,sum_const,nsmul_eq_mul,mul_one,sq_abs] at hcs
  rw [show P.card=Nat.primeCounting X from Nat.primesLE_card_eq_primeCounting X] at hcs
  change (∑ p∈P,rel p^2)/Nat.primeCounting X≤A/(Real.log X)^2 at h
  have hr : ((∑ p∈P,|rel p|)/Nat.primeCounting X)^2 ≤ A/(Real.log X)^2 := by
    apply le_trans _ h
    rw [div_pow,div_le_div_iff₀ (sq_pos_of_pos hcard) hcard]
    nlinarith only [mul_le_mul_of_nonneg_right hcs hcard.le]
  change (∑ p∈P,|rel p|)/Nat.primeCounting X ≤ _
  rw [← Real.sqrt_sq hl.le,← Real.sqrt_div hA.le,Real.le_sqrt (by positivity) (by positivity)]
  exact hr

end Arxiv.«2501.03234».ThetaPrimeVariance
#print axioms Arxiv.«2501.03234».ThetaPrimeVariance.prime_window_count
#print axioms Arxiv.«2501.03234».ThetaPrimeVariance.prime_mean_absolute_relative
#print axioms Arxiv.«2501.03234».ThetaPrimeVariance.relative_square_sum
#print axioms Arxiv.«2501.03234».ThetaPrimeVariance.prime_mean_relative_squared
#print axioms Arxiv.«2501.03234».ThetaPrimeVariance.band_card
#print axioms Arxiv.«2501.03234».ThetaPrimeVariance.prime_second_moment
#print axioms Arxiv.«2501.03234».ThetaPrimeVariance.prime_mean_squared_error
