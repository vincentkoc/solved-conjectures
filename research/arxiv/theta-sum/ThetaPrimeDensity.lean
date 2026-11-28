import ThetaReciprocalVariance
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas

/-! Prime-density lower growth for the canonical arithmetic sum S. -/

namespace Arxiv.«2501.03234».ThetaPrimeDensity

open Finset Filter ThetaReciprocalCutoff ThetaCotangentTriangle ThetaReciprocalInversion ThetaReciprocalVariance

/-- Uniform harmonic estimate on the 64th-power scale. -/
theorem small_harmonic {k N : ℕ} (hN : 1≤N) (hk : k≤N^64) :
    (harmonic k : ℝ) ≤ 65*N := by
  apply (harmonic_le_one_add_log _).trans
  have hN' : (1:ℝ)≤N := by exact_mod_cast hN
  by_cases h : k=0
  · simp [h]; linarith
  have hlog := Real.log_le_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero h))
    (show (k:ℝ) ≤ (N:ℝ)^64 by exact_mod_cast hk)
  rw [Real.log_pow] at hlog; norm_num at hlog
  linarith [Real.log_le_self (Nat.cast_nonneg N)]

/-- Primes in the top part of the scale exceed all denominator cutoffs. -/
theorem cutoff_inside {N p : ℕ} (hN : 2≤N) (hlo : N^56≤p) : 2*N^52<p := by
  calc
    _ ≤ N^52*N := by rw [mul_comm]; exact Nat.mul_le_mul_left _ hN
    _ = N^53 := by ring
    _ < N^56 := Nat.pow_lt_pow_right (by omega) (by decide)
    _ ≤ p := hlo

/-- The Kloosterman discrepancy at p ≤ N^64 costs at most a constant times N^50. -/
theorem scale_discrepancy {N p : ℕ} (hN : 1≤N) (hhi : p≤N^64) :
    discrepancy p ≤ 17424*(N:ℝ)^50 := by
  have hH := small_harmonic hN ((Nat.div_le_self p 2).trans hhi)
  have hNr : 1≤(N:ℝ) := by exact_mod_cast hN
  have hpow := Real.rpow_le_rpow (Nat.cast_nonneg p)
    (show (p:ℝ)≤(N:ℝ)^64 by exact_mod_cast hhi) (by norm_num : (0:ℝ)≤3/4)
  rw [← Real.rpow_natCast_mul (Nat.cast_nonneg _)] at hpow
  norm_num at hpow
  have hH₀ : (0:ℝ)≤harmonic (p/2) := by exact_mod_cast (show 0≤harmonic (p/2) by unfold harmonic; positivity)
  unfold discrepancy
  have he := pow_le_pow_left₀ (by positivity : (0:ℝ)≤1+harmonic (p/2))
    (show 1+(harmonic (p/2):ℝ) ≤ 66*N by linarith) 2
  nlinarith only [mul_le_mul hpow he (sq_nonneg _) (pow_nonneg (Nat.cast_nonneg N : (0:ℝ)≤N) 48)]

private lemma uniform_cutoff {N p : ℕ} [Fact p.Prime] (hN : 2≤N) (hlo : N^56≤p) (hhi : p≤N^64)
    (ho : p%2=1) :
    |lowerTriangle p - (8*p/Real.pi^2)*(rationalPrefix p (N^52) : ℝ)| ≤ 2300000*(p:ℝ) := by
  have hN₁ : 1≤N := by omega
  have hNr : (1:ℝ)≤N := by exact_mod_cast hN₁
  have hp : 0<(p:ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hs := cutoff_inside hN hlo
  have hJ : N^52≤p/2 := by omega
  have hH := small_harmonic hN₁ ((Nat.div_le_self p 2).trans hhi)
  have hJH := small_harmonic hN₁ (Nat.pow_le_pow_right hN₁ (by decide : 52≤64))
  have hH₀ : (0:ℝ)≤harmonic (p/2) := by exact_mod_cast (show 0≤harmonic (p/2) by unfold harmonic; positivity)
  have hD := scale_discrepancy hN₁ hhi
  have ht : 2*discrepancy p*p*harmonic (p/2)/(2*(↑(N^52 : ℕ):ℝ)+1) ≤ 2265120*p := by
    rw [div_le_iff₀ (by positivity)]; push_cast
    have he := mul_le_mul hD hH hH₀ (by positivity)
    have h51 := pow_le_pow_right₀ hNr (by decide : 51≤52)
    nlinarith only [mul_le_mul_of_nonneg_right he hp.le,mul_le_mul_of_nonneg_right h51 hp.le,hp.le,
      mul_nonneg (pow_nonneg (Nat.cast_nonneg N : (0:ℝ)≤N) 52) hp.le]
  have hr : (N:ℝ)^56≤p := by exact_mod_cast hlo
  have hsmooth : 4*(↑(N^52 : ℕ):ℝ)^2*harmonic (N^52)/p ≤ 260*p := by
    rw [div_le_iff₀ hp]; push_cast
    have hh := mul_le_mul_of_nonneg_left hJH (show 0≤(N:ℝ)^104 by positivity)
    nlinarith only [hh,pow_le_pow_right₀ hNr (by decide : 105≤112),
      pow_le_pow_left₀ (by positivity) hr 2]
  exact (rational_cutoff_error ho hJ).trans (by linarith)

private noncomputable def lead : ℝ := 3/(4*Real.pi^2)
private noncomputable def coeff : ℝ := 8/Real.pi^2

private lemma bad_forces_large {c : ℝ} (hc : c<lead) :
    ∃ δ : ℝ, 0<δ ∧ ∀ᶠ N : ℕ in atTop, ∀ p : ℕ, p.Prime → N^56≤p → p≤N^64 →
    (S p:ℝ) ≤ c*p*Real.log p → δ*Real.log N ≤ ‖extension (2*N^52) p‖ := by
  have hc' : 0<lead-c := sub_pos.mpr hc
  have hd : 0<coeff := by dsimp [coeff]; positivity
  let M := 2300000+lead*Real.log 6
  obtain ⟨N₀,h₀⟩ := exists_nat_gt (Real.exp (2*M/(lead-c)))
  refine ⟨(lead-c)/(2*coeff),by positivity,?_⟩
  filter_upwards [eventually_ge_atTop N₀,eventually_ge_atTop 3] with N hN₀ hN
  intro p hp hl hh hbad
  let : Fact p.Prime := ⟨hp⟩
  have hNp : N≤p := (Nat.le_self_pow (by decide : (56:ℕ)≠0) N).trans hl
  have hp3 : 2<p := by omega
  have ho := (hp.eq_two_or_odd).resolve_left (by omega : p≠2)
  have hpos : 0<(p:ℝ) := Nat.cast_pos.mpr hp.pos
  have hNpos : 0<(N:ℝ) := Nat.cast_pos.mpr (by omega)
  have hlog : 2*M/(lead-c)<Real.log N := by
    rw [Real.lt_log_iff_exp_lt hNpos]; exact h₀.trans_le (by exact_mod_cast hN₀)
  have hl' := Real.log_le_log hNpos (show (N:ℝ)≤p by exact_mod_cast hNp)
  have hU := S_sub_lowerTriangle_log ho
  rw [Real.log_div hpos.ne' (by norm_num)] at hU
  change lead*p*(Real.log p-Real.log 6) ≤ (S p:ℝ)-lowerTriangle p at hU
  have hR := (abs_le.mp (uniform_cutoff (by omega : 2≤N) hl hh ho)).1
  rw [show (8:ℝ)*p/Real.pi^2=coeff*p by dsimp [coeff]; ring] at hR
  have H : (lead-c)*Real.log p ≤ M - coeff*(rationalPrefix p (N^52):ℝ) := by
    apply le_of_mul_le_mul_right (a := (p:ℝ)) _ hpos
    dsimp [M]; linarith only [hbad,hR,hU]
  rw [extension_at_prime hp (cutoff_inside (by omega) hl)]
  have hn : ‖(↑(rationalPrefix p (N^52)):ℂ)‖ = |(rationalPrefix p (N^52):ℝ)| := by
    rw [← Complex.ofReal_ratCast,Complex.norm_real,Real.norm_eq_abs]
  rw [hn]
  have h₁ := mul_le_mul_of_nonneg_left hl' hc'.le
  have h₂ := (div_lt_iff₀ hc').mp hlog
  have h₃ := mul_le_mul_of_nonneg_left (neg_le_abs (rationalPrefix p (N^52):ℝ)) hd.le
  rw [div_mul_eq_mul_div,div_le_iff₀ (by positivity)]
  linarith only [H,h₁,h₂,h₃]

/-- Primes satisfying a specified exceptional-event predicate. -/
noncomputable def primeSet (P : ℕ → Prop) (X : ℕ) : Finset ℕ := by
  classical exact (Nat.primesLE X).filter P

/-- Primes up to X whose original theta sum is at most c p log p. -/
noncomputable def exceptions (c : ℝ) := primeSet (fun p => (S p:ℝ) ≤ c*p*Real.log p)

private lemma primeSet_mem {P : ℕ → Prop} {X p : ℕ} :
    p ∈ primeSet P X ↔ p≤X ∧ p.Prime ∧ P p := by
  classical simp only [primeSet,mem_filter,Nat.mem_primesLE,and_assoc]

private lemma primeSet_mono (P : ℕ → Prop) {X Z : ℕ} (h : X≤Z) : primeSet P X ⊆ primeSet P Z := by
  intro p hp; obtain ⟨hp,hp',hs⟩ := primeSet_mem.mp hp
  exact primeSet_mem.mpr ⟨hp.trans h,hp',hs⟩

private lemma scale_exceptions (P : ℕ → Prop) (F : ℕ → ℕ → ℂ)
    (hv : ∃ K : ℝ, 0≤K ∧ ∀ N : ℕ, 1≤N → ∑ n ∈ range (N^64+1), ‖F N n‖^2 ≤ K*(N:ℝ)^64)
    (hf : ∃ δ : ℝ, 0<δ ∧ ∀ᶠ N : ℕ in atTop, ∀ p : ℕ, p.Prime → N^56≤p → p≤N^64 →
      P p → δ*Real.log N ≤ ‖F N p‖) :
    ∃ A : ℝ, 0≤A ∧ ∀ᶠ N : ℕ in atTop,
      ((primeSet P (N^64)).card : ℝ)*(Real.log N)^2 ≤ A*(N:ℝ)^64 := by
  obtain ⟨K,hK,hvar⟩ := hv
  obtain ⟨δ,hδ,hforce⟩ := hf
  refine ⟨1+K/δ^2,by positivity,?_⟩
  filter_upwards [hforce,eventually_ge_atTop 2] with N hforce hN
  let E := primeSet P (N^64)
  let L := E.filter (fun p => N^56≤p)
  let U := E.filter (fun p => ¬N^56≤p)
  have hℓ : 0≤Real.log N := Real.log_nonneg (by exact_mod_cast (show 1≤N by omega))
  have hN₀ : (0:ℝ)≤N := Nat.cast_nonneg _
  have hN₁ : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  have hlarge : (L.card:ℝ)*(δ*Real.log N)^2 ≤ K*(N:ℝ)^64 := by
    calc
      _ = ∑ p ∈ L, (δ*Real.log N)^2 := by simp
      _ ≤ ∑ p ∈ L, ‖F N p‖^2 := by
        apply sum_le_sum; intro p hp
        obtain ⟨hE,hpL⟩ := mem_filter.mp hp
        obtain ⟨hh,hp',hs⟩ := primeSet_mem.mp hE
        exact pow_le_pow_left₀ (mul_nonneg hδ.le hℓ) (hforce p hp' hpL hh hs) _
      _ ≤ ∑ p ∈ range (N^64+1), ‖F N p‖^2 := by
        apply sum_le_sum_of_subset_of_nonneg _ (by intros; positivity)
        intro p hp; exact mem_range.mpr (Nat.lt_succ_of_le (primeSet_mem.mp (mem_filter.mp hp).1).1)
      _ ≤ _ := hvar N (by omega)
  have hsmall : U.card ≤ N^56 := by
    calc
      _ ≤ (range (N^56)).card := card_le_card (by
        intro p hp; exact mem_range.mpr (lt_of_not_ge (mem_filter.mp hp).2))
      _ = _ := card_range _
  have hS := mul_le_mul (show (U.card:ℝ)≤(N:ℝ)^56 by exact_mod_cast hsmall)
    (pow_le_pow_left₀ hℓ (Real.log_le_self hN₀) 2) (sq_nonneg _) (pow_nonneg hN₀ _)
  have hS' : (U.card:ℝ)*(Real.log N)^2 ≤ (N:ℝ)^64 := by
    nlinarith only [hS,pow_le_pow_right₀ hN₁ (by decide : 58≤64)]
  have hL' : (L.card:ℝ)*(Real.log N)^2 ≤ (K/δ^2)*(N:ℝ)^64 := by
    rw [div_mul_eq_mul_div,le_div_iff₀ (by positivity)]; linarith only [hlarge]
  have he : L.card + U.card = E.card := card_filter_add_card_filter_not ..
  change (E.card:ℝ)*(Real.log N)^2 ≤ _
  rw [← he,Nat.cast_add]; linarith only [hS',hL']

/-- A finite first-moment estimate after restriction to primes. The rational cutoff is
sampled only where its equality with the periodic extension is exact. -/
theorem prime_first_moment : ∃ K : ℝ, 0≤K ∧ ∀ N : ℕ, 1≤N →
    (∑ p ∈ (Nat.primesLE (N^64)).filter (fun p => 2*N^52<p),
      |(rationalPrefix p (N^52):ℝ)|)^2 ≤ Nat.primeCounting (N^64)*K*(N:ℝ)^64 := by
  obtain ⟨K,hK,hV⟩ := interval_variance
  refine ⟨K,hK,?_⟩; intro N hN
  let s := (Nat.primesLE (N^64)).filter (fun p => 2*N^52<p)
  let f (p : ℕ) := |(rationalPrefix p (N^52):ℝ)|
  have H := sum_mul_sq_le_sq_mul_sq s (fun _ => (1:ℝ)) f
  simp only [one_mul,one_pow,sum_const,nsmul_eq_mul,mul_one] at H
  have he (p : ℕ) (hp : p ∈ s) : f p = ‖extension (2*N^52) p‖ := by
    rw [extension_at_prime (Nat.prime_of_mem_primesLE (mem_filter.mp hp).1) (mem_filter.mp hp).2,
      ← Complex.ofReal_ratCast,Complex.norm_real,Real.norm_eq_abs]
  have ht : ∑ p ∈ s, (f p)^2 ≤ K*(N:ℝ)^64 := by
    rw [sum_congr rfl (fun p hp => congrArg (·^2) (he p hp))]
    apply (sum_le_sum_of_subset_of_nonneg _ (by intros; positivity)).trans (hV N hN)
    exact fun p hp => mem_range.mpr (Nat.lt_succ_of_le (Nat.le_of_mem_primesLE (mem_filter.mp hp).1))
  have hc : s.card ≤ Nat.primeCounting (N^64) := by
    rw [← Nat.primesLE_card_eq_primeCounting]; exact card_le_card (filter_subset _ _)
  apply H.trans
  rw [mul_assoc]; exact mul_le_mul (by exact_mod_cast hc) ht (sum_nonneg fun _ _ => sq_nonneg _)
    (Nat.cast_nonneg _)

private lemma count_trivial (P : ℕ → Prop) (X : ℕ) : (primeSet P X).card ≤ X+1 := by
  calc
    _ ≤ (range (X+1)).card := card_le_card (by
      intro p hp; exact mem_range.mpr (Nat.lt_succ_of_le (primeSet_mem.mp hp).1))
    _ = _ := card_range _

set_option maxHeartbeats 600000 in
/-- A uniformly bounded cutoff variance gives an X/log² X prime exception bound
whenever the exception forces a cutoff value of logarithmic size. -/
theorem count_from_variance (P : ℕ → Prop) (F : ℕ → ℕ → ℂ)
    (hv : ∃ K : ℝ, 0≤K ∧ ∀ N : ℕ, 1≤N → ∑ n ∈ range (N^64+1), ‖F N n‖^2 ≤ K*(N:ℝ)^64)
    (hf : ∃ δ : ℝ, 0<δ ∧ ∀ᶠ N : ℕ in atTop, ∀ p : ℕ, p.Prime → N^56≤p → p≤N^64 →
      P p → δ*Real.log N ≤ ‖F N p‖) :
    ∃ C : ℝ, 0<C ∧ ∀ X : ℕ, 2≤X → ((primeSet P X).card:ℝ) ≤ C*X/(Real.log X)^2 := by
  obtain ⟨A,hA,hscale⟩ := scale_exceptions P F hv hf
  obtain ⟨N₀,h₀⟩ := eventually_atTop.mp hscale
  let Z := (N₀+1)^64
  let K := (4096*A)*(2:ℝ)^64 + 2*(Z:ℝ)^2 + 1
  have hK : 0<K := by dsimp [K]; positivity
  refine ⟨K,hK,?_⟩
  intro X hX
  have hXr : (1:ℝ)<X := by exact_mod_cast hX
  have hXp := (zero_lt_one.trans hXr)
  have hlog := Real.log_pos hXr
  rw [le_div_iff₀ (by positivity)]
  by_cases hz : Z≤X
  · let r := Nat.nthRoot 64 X
    let N := r+1
    have hr : N₀+1≤r := (Nat.le_nthRoot_iff (by decide : (64:ℕ)≠0)).mpr hz
    have hr₁ : 1≤r := by omega
    have hN : N₀≤N := by dsimp [N]; omega
    have hL : X<N^64 := Nat.lt_pow_nthRoot_add_one (by decide) X
    have hl : r^64≤X := Nat.pow_nthRoot_le (Or.inl (by decide))
    have hnr : N^64≤2^64*X := by
      calc
        _ ≤ (2*r)^64 := Nat.pow_le_pow_left (by dsimp [N]; omega) _
        _ = _ := Nat.mul_pow ..
        _ ≤ _ := Nat.mul_le_mul_left _ hl
    have hlogN := Real.log_nonneg (show (1:ℝ)≤N by exact_mod_cast (by dsimp [N]; omega : 1≤N))
    have hh := Real.log_le_log hXp (show (X:ℝ)≤(N:ℝ)^64 by exact_mod_cast hL.le)
    rw [Real.log_pow] at hh; norm_num at hh
    have hE := card_le_card (primeSet_mono P hL.le)
    have hs := h₀ N hN
    have hcross := mul_le_mul (show ((primeSet P X).card:ℝ) ≤ (primeSet P (N^64)).card by exact_mod_cast hE)
      (pow_le_pow_left₀ hlog.le hh 2) (sq_nonneg _) (Nat.cast_nonneg _)
    have hn' : (N:ℝ)^64 ≤ (2:ℝ)^64*X := by exact_mod_cast hnr
    have hk : (4096*A)*(2:ℝ)^64 ≤ K := by dsimp [K]; linarith [sq_nonneg (Z:ℝ)]
    linarith only [hcross,hs,mul_le_mul_of_nonneg_left hn' hA,mul_le_mul_of_nonneg_right hk hXp.le]
  · have h1 : ((primeSet P X).card:ℝ) ≤ 2*X := by
      have h : ((primeSet P X).card:ℝ) ≤ X+1 := by exact_mod_cast count_trivial P X
      linarith
    have h2 : Real.log X ≤ Z := (Real.log_le_self hXp.le).trans (by exact_mod_cast (lt_of_not_ge hz).le)
    have he := mul_le_mul h1 (pow_le_pow_left₀ hlog.le h2 2) (sq_nonneg _) (by positivity)
    have hK' : 2*(Z:ℝ)^2 ≤ K := by
      change _ ≤ (4096*A)*(2:ℝ)^64 + 2*(Z:ℝ)^2 + 1
      linarith only [mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤4096) hA) (by positivity : (0:ℝ)≤2^64)]
    linarith only [he,mul_le_mul_of_nonneg_right hK' hXp.le]

/-- For every c below 3/(4π²), the original double sum has at most C X/(log X)^2
exceptional primes up to X, for every integer X≥2. -/
theorem prime_exception_bound {c : ℝ} (hc : c<3/(4*Real.pi^2)) :
    ∃ C : ℝ, 0<C ∧ ∀ X : ℕ, 2≤X →
      ((exceptions c X).card : ℝ) ≤ C*X/(Real.log X)^2 :=
  count_from_variance _ (fun N => extension (2*N^52)) interval_variance (bad_forces_large hc)

/-- An eventual Chebyshev lower bound for the prime-counting denominator. -/
theorem prime_count_lower : ∀ᶠ X : ℕ in atTop,
    Real.log 2/2*(X:ℝ) ≤ Nat.primeCounting X*Real.log X := by
  have htwo : 0<Real.log 2 := Real.log_pos (by norm_num)
  have h := (Real.isLittleO_log_id_atTop.bound (show 0<Real.log 2/4 by positivity))
  have ht : Tendsto (fun X : ℕ => (X:ℝ)+1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x:=(1:ℝ)))
  filter_upwards [ht.eventually h,eventually_ge_atTop 2] with X he hX
  have hXr : (1:ℝ)<X := by exact_mod_cast hX
  have hlog := Real.log_pos hXr
  have hp := Chebyshev.pi_ge X
  rw [div_le_iff₀ hlog] at hp
  simp only [id_eq,Real.norm_eq_abs] at he
  rw [abs_of_pos (by linarith : 0<(X:ℝ)+1)] at he
  linarith [le_abs_self (Real.log ((X:ℝ)+1)),mul_le_mul_of_nonneg_left hXr.le htwo.le]

/-- The exceptional proportion among primes tends to zero for every finite
X/log² X count. -/
theorem density_from_count (P : ℕ → Prop) (hb : ∃ C : ℝ, 0<C ∧ ∀ X : ℕ, 2≤X →
    ((primeSet P X).card:ℝ) ≤ C*X/(Real.log X)^2) :
    Tendsto (fun X : ℕ => ((primeSet P X).card:ℝ) / Nat.primeCounting X) atTop (nhds 0) := by
  obtain ⟨C,hC,hbound⟩ := hb
  have htwo : 0<Real.log 2 := Real.log_pos (by norm_num)
  have ht : Tendsto (fun X : ℕ => Real.log (X:ℝ)) atTop atTop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall : Tendsto (fun X : ℕ => (2*C/Real.log 2)/Real.log X) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop ht
  apply squeeze_zero' (Eventually.of_forall (by intro X; positivity)) _ hsmall
  filter_upwards [prime_count_lower,eventually_ge_atTop 2] with X hp hX
  have hXr : (1:ℝ)<X := by exact_mod_cast hX
  have hxp := zero_lt_one.trans hXr
  have hlog := Real.log_pos hXr
  have hπ : 0<(Nat.primeCounting X:ℝ) := by nlinarith [mul_pos htwo hxp]
  have hb := (le_div_iff₀ (sq_pos_of_pos hlog)).mp (hbound X hX)
  rw [div_le_div_iff₀ hπ hlog,div_mul_eq_mul_div,le_div_iff₀ htwo]
  have h₁ := mul_le_mul_of_nonneg_right hp (show 0≤2*C by positivity)
  have h₂ := mul_le_mul_of_nonneg_left hb htwo.le
  apply le_of_mul_le_mul_right (a:=Real.log X) _ hlog
  linarith only [h₁,h₂]

/-- The relative density of the exceptions among primes is zero. -/
theorem prime_density_one {c : ℝ} (hc : c<3/(4*Real.pi^2)) :
    Tendsto (fun X : ℕ => ((exceptions c X).card:ℝ) / Nat.primeCounting X) atTop (nhds 0) :=
  density_from_count _ (prime_exception_bound hc)

private lemma primeCounting_pos_real {X : ℕ} (hX : 2≤X) : 0<(Nat.primeCounting X:ℝ) := by
  have h : 0<(Nat.primesLE X).card := card_pos.mpr ⟨2,Nat.mem_primesLE.mpr ⟨hX,Nat.prime_two⟩⟩
  rw [Nat.primesLE_card_eq_primeCounting] at h; exact_mod_cast h

/-- After division by the number of primes, the mean absolute cutoff on the interpolated
prime range has square at most a constant times log X, where X = N^64. -/
theorem normalized_prime_first_moment : ∃ C : ℝ, 0≤C ∧ ∀ᶠ N : ℕ in atTop,
    ((∑ p ∈ (Nat.primesLE (N^64)).filter (fun p => 2*N^52<p),
      |(rationalPrefix p (N^52):ℝ)|) / Nat.primeCounting (N^64))^2 ≤ C*Real.log (N^64 : ℕ) := by
  obtain ⟨K,hK,hfirst⟩ := prime_first_moment
  have hlog : 0<Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨2*K/Real.log 2,by positivity,?_⟩
  have ht : Tendsto (fun N : ℕ => N^64) atTop atTop := tendsto_pow_atTop (by decide)
  filter_upwards [ht.eventually prime_count_lower,eventually_ge_atTop 2] with N hcount hN
  have hp := primeCounting_pos_real (hN.trans (Nat.le_self_pow (by decide : (64:ℕ)≠0) _))
  have H := hfirst N (by omega)
  rw [div_pow,div_le_iff₀ (by positivity)]
  apply H.trans
  rw [Nat.cast_pow] at hcount
  rw [div_mul_eq_mul_div,div_mul_eq_mul_div,le_div_iff₀ hlog]
  push_cast
  nlinarith only [mul_le_mul_of_nonneg_left hcount (mul_nonneg hp.le hK)]

/-- The same density conclusion in every prime family whose count is eventually a fixed
positive fraction of all primes. This isolates the exact external input for a progression. -/
theorem prime_family_density {c : ℝ} (hc : c<3/(4*Real.pi^2)) (F : ℕ → Finset ℕ)
    {a : ℝ} (ha : 0<a) (hF : ∀ᶠ X : ℕ in atTop, a*Nat.primeCounting X ≤ (F X).card) :
    Tendsto (fun X : ℕ => (((F X ∩ exceptions c X).card : ℝ) / (F X).card)) atTop (nhds 0) := by
  have H := (prime_density_one hc).div_const a
  rw [zero_div] at H
  apply squeeze_zero' (Eventually.of_forall (by intro X; positivity)) _ H
  filter_upwards [hF,eventually_ge_atTop 2] with X hF hX
  have hp := primeCounting_pos_real hX
  have he : ((F X ∩ exceptions c X).card : ℝ) ≤ (exceptions c X).card := by
    exact_mod_cast card_le_card (inter_subset_right (s₁:=F X) (s₂:=exceptions c X))
  rw [div_div,mul_comm _ a]
  exact div_le_div₀ (Nat.cast_nonneg _) he (mul_pos ha hp) hF

end Arxiv.«2501.03234».ThetaPrimeDensity
#print axioms Arxiv.«2501.03234».ThetaPrimeDensity.prime_first_moment
#print axioms Arxiv.«2501.03234».ThetaPrimeDensity.prime_exception_bound
#print axioms Arxiv.«2501.03234».ThetaPrimeDensity.prime_density_one
#print axioms Arxiv.«2501.03234».ThetaPrimeDensity.normalized_prime_first_moment
#print axioms Arxiv.«2501.03234».ThetaPrimeDensity.prime_family_density
#print axioms Arxiv.«2501.03234».ThetaPrimeDensity.small_harmonic
#print axioms Arxiv.«2501.03234».ThetaPrimeDensity.cutoff_inside
#print axioms Arxiv.«2501.03234».ThetaPrimeDensity.scale_discrepancy
#print axioms Arxiv.«2501.03234».ThetaPrimeDensity.count_from_variance
#print axioms Arxiv.«2501.03234».ThetaPrimeDensity.density_from_count
#print axioms Arxiv.«2501.03234».ThetaPrimeDensity.prime_count_lower
