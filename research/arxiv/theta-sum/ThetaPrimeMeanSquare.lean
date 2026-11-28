import ThetaUniformWindows
import ThetaPrimeAsymptotic

/-! Mean square of the original signed theta sum on primes. -/

namespace Arxiv.«2501.03234».ThetaPrimeMeanSquare

open Finset ThetaReciprocalInversion ThetaPrimeAsymptotic ThetaPrimeDensity
open ThetaDivisibleDiagonal ThetaNondivisibleCone

private def coneWidth (N : ℕ) : ℕ := 2*((N-1)/2)+1

private lemma scale_control : ∃ C : ℝ, 0<C ∧ ∀ {N p : ℕ}, 2≤N → p.Prime → N^56≤p → p≤N^64 →
    |(S p:ℝ)/p-Real.log p/2| ≤ C+(8/Real.pi^2)*
      ‖windowExtension (coneWindow (coneWidth N)) (2*N^52) p‖ := by
  obtain ⟨C,hC,hdiag⟩ := S_sub_offDiagonal_asymptotic
  refine ⟨C+2300300,by positivity,?_⟩
  intro N p hN hp hlo hhi
  let K := coneWidth N
  have hK : K%2=1 := by dsimp [K,coneWidth]; omega
  have hKN : K≤N := by dsimp [K,coneWidth]; omega
  have hNK : (N:ℝ)≤2*(K:ℝ) := by exact_mod_cast (show N≤2*K by dsimp [K,coneWidth]; omega)
  have hKr : (1:ℝ)≤K := by exact_mod_cast (show 1≤K by omega)
  have hKpos : (0:ℝ)<K := by linarith
  let : Fact p.Prime := ⟨hp⟩
  have hpr : 0<(p:ℝ) := by exact_mod_cast hp.pos
  have ho : p%2=1 := by
    rcases hp.eq_two_or_odd with h|h
    · have := cutoff_inside hN hlo; have := Nat.one_le_pow 52 N (by omega); omega
    · exact h
  have hNr : (0:ℝ)≤N := Nat.cast_nonneg _
  have hlog : Real.log p≤64*(N:ℝ) := by
    have hh := Real.log_le_log hpr (show (p:ℝ)≤(N:ℝ)^64 by exact_mod_cast hhi)
    rw [Real.log_pow] at hh; norm_num at hh
    linarith only [hh,Real.log_le_self hNr]
  have htail : (2*(p:ℝ)/K)*(1+Real.log p)≤300*p := by
    rw [div_mul_eq_mul_div,div_le_iff₀ hKpos]
    have h := mul_le_mul_of_nonneg_left (show 2*(1+Real.log p)≤300*K by linarith) hpr.le
    nlinarith only [h]
  have hU := uniform_approximation hN hK hKN hlo hhi ho
  let B := (rationalCone p (N^52) K:ℝ)
  let c := 8/Real.pi^2
  have hc : 0<c := by dsimp [c]; positivity
  have ho' : |offDiagonal p| ≤ 2300300*(p:ℝ)+c*p*|B| := by
    have hh := abs_sub_le (offDiagonal p) ((8*p/Real.pi^2)*B) 0
    simp only [sub_zero,abs_mul,abs_of_pos (show 0<(8*p/Real.pi^2:ℝ) by positivity)] at hh
    change |offDiagonal p - _*B| ≤ _ at hU
    rw [show (8:ℝ)*p/Real.pi^2=c*p by dsimp [c]; ring] at hh hU
    linarith only [hh,hU,htail]
  have hS := abs_sub_le ((S p:ℝ)-(p:ℝ)*Real.log p/2) (offDiagonal p) 0
  simp only [sub_zero] at hS
  rw [sub_right_comm] at hS
  rw [cone_interpolation hK hp (cutoff_inside hN hlo),← Complex.ofReal_ratCast,Complex.norm_real,Real.norm_eq_abs]
  change _ ≤ C+2300300+c*|B|
  rw [show (S p:ℝ)/p-Real.log p/2=((S p:ℝ)-(p:ℝ)*Real.log p/2)/p by field_simp,
    abs_div,abs_of_pos hpr,div_le_iff₀ hpr]
  nlinarith only [hS,ho',hdiag p ho]


private noncomputable def error (p : ℕ) := (S p:ℝ)/p-Real.log p/2

private lemma small_error {N p : ℕ} (hN : 2≤N) (hp : p.Prime) (hhi : p≤N^64) :
    |error p| ≤ (|error 2|+17000)*(N:ℝ)^2 := by
  have hNr : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  have hn₂ : 1≤(N:ℝ)^2 := one_le_pow₀ hNr
  rcases hp.eq_two_or_odd with he|ho
  · subst p
    exact (le_mul_of_one_le_right (abs_nonneg _) hn₂).trans
      (mul_le_mul_of_nonneg_right (by linarith : |error 2|≤|error 2|+17000) (sq_nonneg (N:ℝ)))
  have hpr : 0<(p:ℝ) := by exact_mod_cast hp.pos
  have hl₀ := Real.log_nonneg (show (1:ℝ)≤p by exact_mod_cast hp.pos)
  have hl := Real.log_le_log hpr (show (p:ℝ)≤(N:ℝ)^64 by exact_mod_cast hhi)
  rw [Real.log_pow] at hl; norm_num at hl
  have hl' : Real.log p≤64*(N:ℝ) := by linarith [Real.log_le_self (Nat.cast_nonneg N)]
  have habs : |(S p:ℝ)/p|≤1+4*(1+Real.log p)^2 := by
    rw [abs_div,abs_of_pos hpr,div_le_iff₀ hpr,mul_comm]
    exact ThetaFourier.abs_S_le_log_sq p hp (Nat.odd_iff.mpr ho)
  have hs := abs_sub_le ((S p:ℝ)/p) 0 (Real.log p/2)
  rw [sub_zero,zero_sub,abs_neg,abs_of_nonneg (by positivity : 0≤Real.log p/2)] at hs
  have hsq := pow_le_pow_left₀ (by positivity : 0≤1+Real.log p)
    (show 1+Real.log p≤65*(N:ℝ) by linarith) 2
  change |(S p:ℝ)/p-Real.log p/2|≤_
  nlinarith only [hs,habs,hsq,hl',hn₂,pow_le_pow_right₀ hNr (by decide : 1≤2),
    mul_nonneg (abs_nonneg (error 2)) (sq_nonneg (N:ℝ))]

private lemma scale_moment : ∃ C : ℝ, 0≤C ∧ ∀ N : ℕ, 2≤N →
    ∑ p ∈ Nat.primesLE (N^64), error p^2 ≤ C*(N:ℝ)^64 := by
  obtain ⟨A,hA,hcontrol⟩ := scale_control
  obtain ⟨V,hV,hvar⟩ := ThetaUniformWindows.window_variance_uniform
  let c := 8/Real.pi^2
  let T := |error 2|+17000
  refine ⟨T^2+4*A^2+2*c^2*V,by positivity,?_⟩
  intro N hN
  let P := Nat.primesLE (N^64)
  let Q := P.filter (fun p => N^56≤p)
  let R := P.filter (fun p => ¬ N^56≤p)
  let L := coneWindow (coneWidth N)
  let F := windowExtension L (2*N^52)
  have hN' : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  have hn64 : 1≤(N:ℝ)^64 := one_le_pow₀ hN'
  have hc : 0≤c := by dsimp [c]; positivity
  have hL : L 1=0 := by simp [L,coneWindow]
  have hQ (p : ℕ) (hp : p ∈ Q) : error p^2 ≤ 2*A^2+2*c^2*‖F p‖^2 := by
    obtain ⟨hprime,hlo⟩ := mem_filter.mp hp
    have h := hcontrol hN (Nat.prime_of_mem_primesLE hprime) hlo (Nat.le_of_mem_primesLE hprime)
    change |error p| ≤ A+c*‖F p‖ at h
    have hs := pow_le_pow_left₀ (abs_nonneg _) h 2
    rw [sq_abs] at hs
    nlinarith only [hs,sq_nonneg (A-c*‖F p‖)]
  have hsub : Q ⊆ range (N^64+1) := by
    intro p hp; exact mem_range.mpr (Nat.lt_succ_of_le (Nat.le_of_mem_primesLE (mem_filter.mp hp).1))
  have hcard : (Q.card:ℝ)≤2*(N:ℝ)^64 := by
    have hh := card_le_card hsub; rw [card_range] at hh
    have hh' : (Q.card:ℝ)≤(N:ℝ)^64+1 := by exact_mod_cast hh
    linarith
  have hsumF : ∑ p ∈ Q, ‖F p‖^2 ≤ V*(N:ℝ)^64 :=
    (sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)).trans (hvar L hL N (by omega))
  have hbig : ∑ p ∈ Q, error p^2 ≤ (4*A^2+2*c^2*V)*(N:ℝ)^64 := by
    apply (sum_le_sum hQ).trans
    rw [sum_add_distrib,sum_const,nsmul_eq_mul,← mul_sum]
    nlinarith only [mul_le_mul_of_nonneg_right hcard (by positivity : 0≤2*A^2),
      mul_le_mul_of_nonneg_left hsumF (by positivity : 0≤2*c^2)]
  have hR : R ⊆ range (N^56) := by
    intro p hp; exact mem_range.mpr (lt_of_not_ge (mem_filter.mp hp).2)
  have hcardR : (R.card:ℝ)≤(N:ℝ)^56 := by
    have hh := card_le_card hR; rw [card_range] at hh; exact_mod_cast hh
  have hsmall : ∑ p ∈ R, error p^2 ≤ T^2*(N:ℝ)^64 := by
    have hh (p : ℕ) (hp : p ∈ R) : error p^2≤(T*(N:ℝ)^2)^2 := by
      have hh' := (mem_filter.mp hp).1
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _)
        (small_error hN (Nat.prime_of_mem_primesLE hh') (Nat.le_of_mem_primesLE hh')) 2
    apply (sum_le_sum hh).trans
    rw [sum_const,nsmul_eq_mul]
    have hc' := mul_le_mul_of_nonneg_right hcardR (sq_nonneg (T*(N:ℝ)^2))
    nlinarith only [hc',mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hN' (by decide : 60≤64)) (sq_nonneg T)]
  have he := sum_filter_add_sum_filter_not P (fun p => N^56≤p) (fun p => error p^2)
  change ∑ p ∈ Q, error p^2 + ∑ p ∈ R, error p^2 = ∑ p ∈ P, error p^2 at he
  change ∑ p ∈ P, error p^2 ≤ _
  rw [← he]; linarith only [hbig,hsmall]

/-- Finite prime mean square for the canonical signed theta sum. The constant
is absolute and the assertion includes every prime up to X. -/
theorem prime_error_second_moment : ∃ C : ℝ, 0<C ∧ ∀ X : ℕ, 2≤X →
    ∑ p ∈ Nat.primesLE X, ((S p:ℝ)/p-Real.log p/2)^2 ≤ C*X := by
  obtain ⟨C,hC,h⟩ := scale_moment
  refine ⟨(C+1)*2^64,by positivity,?_⟩
  intro X hX
  let r := Nat.nthRoot 64 X
  let N := r+1
  have hr : 1≤r := (Nat.le_nthRoot_iff (by decide : (64:ℕ)≠0)).mpr (by simpa using (show 1≤X by omega))
  have hN : 2≤N := by dsimp [N]; omega
  have hL : X<N^64 := Nat.lt_pow_nthRoot_add_one (by decide) X
  have hl : r^64≤X := Nat.pow_nthRoot_le (Or.inl (by decide))
  have hnr : N^64≤2^64*X := by
    calc
      _ ≤ (2*r)^64 := Nat.pow_le_pow_left (by dsimp [N]; omega) _
      _ = _ := Nat.mul_pow ..
      _ ≤ _ := Nat.mul_le_mul_left _ hl
  have hsub : Nat.primesLE X ⊆ Nat.primesLE (N^64) := by
    intro p hp; obtain ⟨hh,hp'⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨hh.trans hL.le,hp'⟩
  apply (sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)).trans ((h N hN).trans ?_)
  have he : (N:ℝ)^64≤2^64*(X:ℝ) := by exact_mod_cast hnr
  nlinarith only [mul_le_mul_of_nonneg_left he hC,(Nat.cast_nonneg X : (0:ℝ)≤X)]


/-- One absolute constant bounds the number of primes with additive error at
least t, simultaneously for every positive real threshold t. -/
theorem prime_error_count : ∃ C : ℝ, 0<C ∧ ∀ X : ℕ, 2≤X → ∀ t : ℝ, 0<t →
    ((primeSet (fun p => t≤|(S p:ℝ)/p-Real.log p/2|) X).card:ℝ) ≤ C*X/t^2 := by
  classical
  obtain ⟨C,hC,H⟩ := prime_error_second_moment
  refine ⟨C,hC,?_⟩; intro X hX t ht
  let F := primeSet (fun p => t≤|error p|) X
  have hs : F ⊆ Nat.primesLE X := filter_subset _ _
  rw [le_div_iff₀ (sq_pos_of_pos ht)]
  change (F.card:ℝ)*t^2 ≤ C*X
  calc
    _ = ∑ _ ∈ F, t^2 := by simp
    _ ≤ ∑ p ∈ F, error p^2 := by
      apply sum_le_sum; intro p hp
      have he : t≤|error p| := (mem_filter.mp hp).2
      simpa only [sq_abs] using pow_le_pow_left₀ ht.le he 2
    _ ≤ ∑ p ∈ Nat.primesLE X, error p^2 := sum_le_sum_of_subset_of_nonneg hs (by intros; positivity)
    _ ≤ _ := H X hX


private noncomputable def relativeError (p : ℕ) := (S p:ℝ)/((p:ℝ)*Real.log p)-1/2

private lemma relative_eq {p : ℕ} (hp : p.Prime) : relativeError p = error p/Real.log p := by
  have hpr : 0<(p:ℝ) := by exact_mod_cast hp.pos
  have hℓ := Real.log_pos (show 1<(p:ℝ) by exact_mod_cast hp.one_lt)
  dsimp [relativeError,error]; field_simp

private lemma small_log_scale {X : ℕ} (hX : 4≤X) :
    (X.sqrt:ℝ)*(Real.log X)^2 ≤ 16*(X:ℝ) := by
  let z := (X:ℝ)^(1/4:ℝ)
  have hz₀ : 0≤z := by dsimp [z]; positivity
  have hz₄ : z^4=(X:ℝ) := by dsimp [z]; rw [← Real.rpow_mul_natCast (Nat.cast_nonneg _)]; norm_num
  have hR : (X.sqrt:ℝ)^2≤(X:ℝ) := by exact_mod_cast Nat.sqrt_le' X
  have hR' : (X.sqrt:ℝ)≤z^2 := by nlinarith only [hz₄,hR,sq_nonneg z]
  have hl₀ := Real.log_nonneg (show (1:ℝ)≤X by exact_mod_cast (show 1≤X by omega))
  have hl : Real.log X≤4*z := by
    have := Real.log_natCast_le_rpow_div X (show (0:ℝ)<1/4 by norm_num)
    dsimp [z]; linarith only [this]
  have hb := mul_le_mul hR' (pow_le_pow_left₀ hl₀ hl 2) (sq_nonneg (Real.log X)) (sq_nonneg z)
  nlinarith only [hb,hz₄]

/-- The relative error in the original S(p)/(p log p) has total square
O(X/(log X)²) over primes up to X. -/
theorem relative_second_moment : ∃ C : ℝ, 0<C ∧ ∀ X : ℕ, 4≤X →
    (∑ p ∈ Nat.primesLE X, ((S p:ℝ)/((p:ℝ)*Real.log p)-1/2)^2)*(Real.log X)^2 ≤ C*X := by
  classical
  obtain ⟨C,hC,H⟩ := prime_error_second_moment
  let b := Real.log 2
  have hb : 0<b := Real.log_pos (by norm_num)
  refine ⟨16*(C/b^2)+4*C,by positivity,?_⟩
  intro X hX
  let P := Nat.primesLE X
  let R := X.sqrt
  let J := P.filter (fun p => p≤R)
  let K := P.filter (fun p => ¬p≤R)
  have hR : 2≤R := Nat.le_sqrt'.mpr (by simpa using hX)
  have hXP := H X (by omega)
  have hRP := H R hR
  have hJ : J ⊆ Nat.primesLE R := by
    intro p hp; obtain ⟨hP,hpR⟩ := mem_filter.mp hp
    exact Nat.mem_primesLE.mpr ⟨hpR,Nat.prime_of_mem_primesLE hP⟩
  have hsmall : (∑ p ∈ J, relativeError p^2)*b^2 ≤ C*R := by
    rw [sum_mul]
    apply (sum_le_sum (g:=fun p => error p^2) _).trans
      ((sum_le_sum_of_subset_of_nonneg hJ (by intros; positivity)).trans hRP)
    intro p hp
    have hh := Nat.prime_of_mem_primesLE (hJ hp)
    have hl : b≤Real.log p := Real.log_le_log (by norm_num) (by exact_mod_cast hh.two_le)
    have hpℓ := hb.trans_le hl
    rw [relative_eq hh,div_pow,div_mul_eq_mul_div,div_le_iff₀ (sq_pos_of_pos hpℓ)]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb.le hl 2) (sq_nonneg _)
  have hbig : (∑ p ∈ K, relativeError p^2)*(Real.log X)^2 ≤ 4*(C*X) := by
    rw [sum_mul]
    calc
      _ ≤ ∑ p ∈ K, 4*(error p)^2 := by
        apply sum_le_sum; intro p hp
        obtain ⟨hP,hr⟩ := mem_filter.mp hp
        have hh := Nat.prime_of_mem_primesLE hP
        have hℓ := Real.log_pos (show (1:ℝ)<p by exact_mod_cast hh.one_lt)
        have hXp : 0<(X:ℝ) := by exact_mod_cast (show 0<X by omega)
        have hx : X<p^2 := Nat.sqrt_lt'.mp (lt_of_not_ge hr)
        have hl := Real.log_le_log hXp (show (X:ℝ)≤(p:ℝ)^2 by exact_mod_cast hx.le)
        rw [Real.log_pow] at hl; norm_num at hl
        rw [relative_eq hh,div_pow,div_mul_eq_mul_div,div_le_iff₀ (sq_pos_of_pos hℓ)]
        have he := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.log_nonneg (by exact_mod_cast (show 1≤X by omega))) hl 2) (sq_nonneg (error p))
        nlinarith only [he]
      _ ≤ _ := by
        rw [← mul_sum]
        exact mul_le_mul_of_nonneg_left ((sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; positivity)).trans hXP) (by norm_num)
  have hdiv : (∑ p ∈ J, relativeError p^2) ≤ C*R/b^2 := (le_div_iff₀ (sq_pos_of_pos hb)).mpr hsmall
  have hlow := mul_le_mul_of_nonneg_right hdiv (sq_nonneg (Real.log X))
  have hs := mul_le_mul_of_nonneg_left (small_log_scale hX) (show 0≤C/b^2 by positivity)
  have he := sum_filter_add_sum_filter_not P (fun p => p≤R) (fun p => relativeError p^2)
  change ∑ p ∈ J, relativeError p^2 + ∑ p ∈ K, relativeError p^2 = ∑ p ∈ P, relativeError p^2 at he
  change (∑ p ∈ P, relativeError p^2)*_≤_
  rw [← he,add_mul]
  dsimp only [R] at hlow
  rw [show C*(X.sqrt:ℝ)/b^2*(Real.log X)^2 = (C/b^2)*((X.sqrt:ℝ)*(Real.log X)^2) by ring] at hlow
  exact (add_le_add (hlow.trans hs) hbig).trans_eq (by ring)


/-- With the number of primes as denominator the mean squared relative error
is O(1/log X). In particular the root mean square is O(1/sqrt(log X)). -/
theorem prime_mean_relative_square : ∃ C : ℝ, 0<C ∧ ∀ᶠ X : ℕ in Filter.atTop,
    (∑ p ∈ Nat.primesLE X, ((S p:ℝ)/((p:ℝ)*Real.log p)-1/2)^2)/(Nat.primeCounting X) ≤ C/Real.log X := by
  obtain ⟨A,hA,H⟩ := relative_second_moment
  let b := Real.log 2/2
  have hb : 0<b := by dsimp [b]; positivity
  refine ⟨A/b,by positivity,?_⟩
  filter_upwards [prime_count_lower,Filter.eventually_ge_atTop 4] with X hcount hX
  let E := ∑ p ∈ Nat.primesLE X, relativeError p^2
  have hxp : 0<(X:ℝ) := by exact_mod_cast (show 0<X by omega)
  have hℓ : 0<Real.log X := Real.log_pos (by exact_mod_cast (show 1<X by omega))
  change b*(X:ℝ)≤(Nat.primeCounting X:ℝ)*Real.log X at hcount
  have hp : 0<(Nat.primeCounting X:ℝ) := by nlinarith only [hcount,mul_pos hb hxp,hℓ,Nat.cast_nonneg (Nat.primeCounting X) (α:=ℝ)]
  have he : E*(Real.log X)^2≤A*X := H X hX
  change E/(Nat.primeCounting X)≤(A/b)/Real.log X
  rw [div_le_div_iff₀ hp hℓ]
  apply le_of_mul_le_mul_right (a:=Real.log X) _ hℓ
  apply le_of_mul_le_mul_right (a:=b) _ hb
  have hh := mul_le_mul_of_nonneg_left hcount hA.le
  have hh' := mul_le_mul_of_nonneg_right he hb.le
  calc
    _ ≤ (A*X)*b := by linarith only [show (E*Real.log X*Real.log X)*b=(E*(Real.log X)^2)*b by ring,hh']
    _ ≤ A*((Nat.primeCounting X:ℝ)*Real.log X) := by linarith only [show (A*X)*b=A*(b*X) by ring,hh]
    _ = _ := by field_simp

/-- The mean absolute difference between S(p)/(p log p) and one half tends
to zero over the primes, with quantitative rate O(1/sqrt(log X)). -/
theorem prime_mean_absolute_rate : ∃ C : ℝ, 0<C ∧ ∀ᶠ X : ℕ in Filter.atTop,
    (∑ p ∈ Nat.primesLE X, |(S p:ℝ)/((p:ℝ)*Real.log p)-1/2|)/(Nat.primeCounting X) ≤ C/Real.sqrt (Real.log X) := by
  obtain ⟨A,hA,H⟩ := prime_mean_relative_square
  refine ⟨Real.sqrt A,Real.sqrt_pos.mpr hA,?_⟩
  filter_upwards [H,Filter.eventually_ge_atTop 2] with X h hX
  let S := Nat.primesLE X
  have hcard : 0<(Nat.primeCounting X:ℝ) := by
    have hh : 2 ∈ S := Nat.mem_primesLE.mpr ⟨hX,Nat.prime_two⟩
    exact_mod_cast (Nat.primesLE_card_eq_primeCounting X ▸ (card_pos.mpr ⟨2,hh⟩ : 0<(Nat.primesLE X).card))
  have hℓ : 0<Real.log X := Real.log_pos (by exact_mod_cast (show 1<X by omega))
  have hcs := sum_mul_sq_le_sq_mul_sq S (fun _ => (1:ℝ)) (fun p => |relativeError p|)
  simp only [one_mul,one_pow,sum_const,nsmul_eq_mul,mul_one,sq_abs] at hcs
  rw [show S.card=Nat.primeCounting X from Nat.primesLE_card_eq_primeCounting X] at hcs
  change (∑ p ∈ S, relativeError p^2)/(Nat.primeCounting X)≤A/Real.log X at h
  have hr : ((∑ p ∈ S, |relativeError p|)/(Nat.primeCounting X))^2 ≤ A/Real.log X := by
    apply le_trans _ h
    rw [div_pow,div_le_div_iff₀ (sq_pos_of_pos hcard) hcard]
    nlinarith only [mul_le_mul_of_nonneg_right hcs hcard.le]
  change (∑ p ∈ S, |relativeError p|)/(Nat.primeCounting X) ≤ _
  rw [← Real.sqrt_div hA.le,Real.le_sqrt (by positivity) (by positivity)]
  exact hr

end Arxiv.«2501.03234».ThetaPrimeMeanSquare
#print axioms Arxiv.«2501.03234».ThetaPrimeMeanSquare.prime_error_second_moment
#print axioms Arxiv.«2501.03234».ThetaPrimeMeanSquare.prime_error_count
#print axioms Arxiv.«2501.03234».ThetaPrimeMeanSquare.relative_second_moment
#print axioms Arxiv.«2501.03234».ThetaPrimeMeanSquare.prime_mean_relative_square
#print axioms Arxiv.«2501.03234».ThetaPrimeMeanSquare.prime_mean_absolute_rate
