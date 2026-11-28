import ThetaPrimeMeanSquare

/-! Common denominator cutoffs from bounds for complete Kloosterman sums. -/
namespace Arxiv.«2501.03234».ThetaCalibratedCone
open Finset Real ThetaPrimeAsymptotic ThetaPrimeDensity ThetaNondivisibleCone
open ThetaPrimeMeanSquare ThetaDivisibleDiagonal ThetaReciprocalCutoff ThetaReciprocalInversion
noncomputable section

/-- Number of dyadic levels through N. -/
def levels (N : ℕ) := Nat.log 2 N+1

/-- Common denominator cutoff for all primes in the 64th-power band. -/
def cutoff (e N : ℕ) := N^e*(levels N)^3

/-- Uniform Kloosterman bound on the 64th-power prime band. -/
def Kernel (e : ℕ) : Prop := ∀ {N p : ℕ} [Fact p.Prime], p≤N^64 →
  ∀ a b : ZMod p,b≠0 → ‖kloosterman a b‖≤2*(N:ℝ)^e

theorem elementary_kernel : Kernel 48 := by
  intro N p _ hh a b hb
  apply (kloosterman_bound a b hb).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  have h := rpow_le_rpow (Nat.cast_nonneg p) (show (p:ℝ)≤(N:ℝ)^64 by exact_mod_cast hh)
    (by norm_num : (0:ℝ)≤3/4)
  rw [←rpow_natCast_mul (Nat.cast_nonneg _)] at h
  norm_num at h
  exact h

theorem levels_bounds {N : ℕ} (hN : 1≤N) : log N≤(levels N:ℝ) ∧
    (levels N:ℝ)≤2*(1+log N) ∧ levels N≤N := by
  have hn : 0<(N:ℝ) := by exact_mod_cast hN
  have he := Nat.lt_pow_succ_log_self (by decide : 1<2) N
  have hu := log_le_log hn (show (N:ℝ)≤(2:ℝ)^(levels N) by exact_mod_cast he.le)
  have hl := log_le_log (show 0<(2:ℝ)^(Nat.log 2 N) by positivity)
    (show (2:ℝ)^(Nat.log 2 N)≤N by exact_mod_cast Nat.pow_log_le_self 2 (by omega : N≠0))
  rw [log_pow] at hu hl
  refine ⟨hu.trans ?_,?_,Nat.log_lt_self 2 (by omega : N≠0)⟩
  · exact mul_le_of_le_one_right (Nat.cast_nonneg _) (by linarith [log_two_lt_d9])
  · dsimp [levels];push_cast
    have h := mul_le_mul_of_nonneg_left (show (1/2:ℝ)≤log 2 by linarith [log_two_gt_d9])
      (Nat.cast_nonneg (Nat.log 2 N))
    linarith

theorem cutoff_bounds {e N : ℕ} (he : 32≤e) (he48 : e≤48) (hN : 1≤N) : N^2≤cutoff e N ∧ cutoff e N≤N^51 ∧
    (cutoff e N:ℝ)≤8*(N:ℝ)^e*(1+log N)^3 := by
  obtain ⟨_,hu,hl⟩ := levels_bounds hN
  refine ⟨(Nat.pow_le_pow_right hN (by omega : 2≤e)).trans (Nat.le_mul_of_pos_right _
    (pow_pos (Nat.succ_pos _) 3)),?_,?_⟩
  · exact (Nat.mul_le_mul (Nat.pow_le_pow_right hN he48) (Nat.pow_le_pow_left hl 3)).trans_eq (by ring)
  · unfold cutoff;push_cast
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hu 3)
      (pow_nonneg (Nat.cast_nonneg N) e)).trans_eq (by ring)

private theorem harmonic_bound {k N : ℕ} (hN : 1≤N) (hk : k≤N^64) :
    (harmonic k:ℝ)≤65*(levels N:ℝ) := by
  have hl := (levels_bounds hN).1
  have hb : 1≤(levels N:ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
  apply (harmonic_le_one_add_log _).trans
  by_cases h : k=0
  · simp [h];linarith
  have hlog := log_le_log (show 0<(k:ℝ) by exact_mod_cast Nat.pos_of_ne_zero h)
    (show (k:ℝ)≤(N:ℝ)^64 by exact_mod_cast hk)
  rw [log_pow] at hlog
  norm_num at hlog
  linarith

private theorem denominator_error {e N p : ℕ} (he : 32≤e) (hN : 1≤N) (hh : p≤N^64) :
    2*(kernelDiscrepancy p (2*(N:ℝ)^e)+2*(p.sqrt:ℝ))*p*harmonic (p/2)/(2*(cutoff e N:ℝ)+1) ≤ 2300000*(p:ℝ) := by
  let b := (levels N:ℝ)
  have hb : 1≤b := by dsimp [b]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le (Nat.log 2 N))
  have hpos : 0≤b := by linarith
  have hn : 1≤(N:ℝ) := by exact_mod_cast hN
  have hH : (harmonic (p/2):ℝ)≤65*b := harmonic_bound hN ((Nat.div_le_self p 2).trans hh)
  have hH0 : 0≤(harmonic (p/2):ℝ) := by unfold harmonic;positivity
  have hsq := pow_le_pow_left₀ (by positivity : (0:ℝ)≤1+harmonic (p/2))
    (show 1+(harmonic (p/2):ℝ)≤66*b by linarith) 2
  have hd : kernelDiscrepancy p (2*(N:ℝ)^e) ≤17424*(N:ℝ)^e*b^2 := by
    unfold kernelDiscrepancy
    nlinarith only [mul_le_mul_of_nonneg_left hsq (pow_nonneg (Nat.cast_nonneg N) e)]
  have hs : p.sqrt≤N^32 := by
    apply (Nat.sqrt_le_sqrt hh).trans_eq
    rw [show N^64=(N^32)*(N^32) by ring,Nat.sqrt_eq]
  have hs' : (p.sqrt:ℝ)≤(N:ℝ)^e*b^2 :=
    (show (p.sqrt:ℝ)≤(N:ℝ)^e by exact_mod_cast hs.trans (Nat.pow_le_pow_right hN he)).trans
      (le_mul_of_one_le_right (by positivity) (one_le_pow₀ hb))
  have hd' : kernelDiscrepancy p (2*(N:ℝ)^e)+2*(p.sqrt:ℝ) ≤17426*(N:ℝ)^e*b^2 := by linarith
  have he := mul_le_mul hd' hH hH0 (by positivity : 0≤17426*(N:ℝ)^e*b^2)
  rw [div_le_iff₀ (by positivity)]
  unfold cutoff;push_cast
  change _≤2300000*(p:ℝ)*(2*((N:ℝ)^e*b^3)+1)
  nlinarith only [mul_le_mul_of_nonneg_right he (Nat.cast_nonneg p),Nat.cast_nonneg p (α:=ℝ),
    mul_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg N) e) (pow_nonneg hpos 3)) (Nat.cast_nonneg p)]

/-- The same rational cone approximates all band primes with an absolute error
after division by p, including at the smaller common denominator cutoff. -/
theorem cone_error {e N p : ℕ} (he : 32≤e) (he48 : e≤48) (kernel : Kernel e) (hN : 2≤N) (hp : p.Prime) (hl : N^56≤p) (hh : p≤N^64) :
    |offDiagonal p-(8*p/π^2)*(rationalCone p (cutoff e N) (coneWidth N):ℝ)|≤2301000*(p:ℝ) := by
  let : Fact p.Prime := ⟨hp⟩
  let J := cutoff e N
  let K := coneWidth N
  have hN₁ : 1≤N := by omega
  have hKN : K≤N := by dsimp [K,coneWidth];omega
  have hNK : N≤2*K := by dsimp [K,coneWidth];omega
  have hKr : 0<(K:ℝ) := by exact_mod_cast (show 0<K by dsimp [K,coneWidth];omega)
  have hJ : J≤N^52 := (cutoff_bounds he he48 hN₁).2.1.trans (Nat.pow_le_pow_right hN₁ (by decide))
  have hjp := (Nat.mul_le_mul_left 2 hJ).trans_lt (cutoff_inside hN hl)
  have hwidth : N*(2*J)≤p := calc
    _ ≤ N*(N*N^52) := Nat.mul_le_mul_left _ (Nat.mul_le_mul hN hJ)
    _ = N^54 := by ring
    _ ≤ N^56 := Nat.pow_le_pow_right hN₁ (by decide)
    _ ≤ p := hl
  have hw := (Nat.mul_le_mul_right (2*J) hKN).trans hwidth
  have hJN : J*N≤p := by rw [mul_comm];apply (Nat.mul_le_mul_left N (by omega : J≤2*J)).trans hwidth
  have hKJ : K*J≤N^64 := calc
    _ ≤ N*N^52 := Nat.mul_le_mul hKN hJ
    _ = N^53 := by ring
    _ ≤ N^64 := Nat.pow_le_pow_right hN₁ (by decide)
  have hH := small_harmonic hN₁ (hJ.trans (Nat.pow_le_pow_right hN₁ (by decide : 52≤64)))
  have hH' := small_harmonic hN₁ hKJ
  have hpr : 0<(p:ℝ) := by exact_mod_cast hp.pos
  have hn : 1≤(N:ℝ) := by exact_mod_cast hN₁
  have ht : 2*(p:ℝ)*harmonic J/K≤260*p := by
    rw [div_le_iff₀ hKr]
    have he : (harmonic J:ℝ)≤130*K := by linarith only [hH,show (N:ℝ)≤2*(K:ℝ) by exact_mod_cast hNK]
    nlinarith only [mul_le_mul_of_nonneg_right he hpr.le]
  have hlin : 2*(J:ℝ)^2*(2*(harmonic (K*J):ℝ)+(K:ℝ)^2)/p ≤ 262*p := by
    rw [div_le_iff₀ hpr]
    have hK2 := pow_le_pow_left₀ hKr.le (show (K:ℝ)≤N by exact_mod_cast hKN) 2
    have he : 2*(harmonic (K*J):ℝ)+(K:ℝ)^2 ≤131*(N:ℝ)^2 := by
      nlinarith only [hH',hK2,mul_nonneg (Nat.cast_nonneg N (α:=ℝ)) (sub_nonneg.mpr hn)]
    have hjp' : (J:ℝ)*N≤p := by exact_mod_cast hJN
    nlinarith only [mul_le_mul_of_nonneg_left he (sq_nonneg (J:ℝ)),
      pow_le_pow_left₀ (by positivity : 0≤(J:ℝ)*N) hjp' 2]
  have ho : p%2=1 := by
    rcases hp.eq_two_or_odd with h|h
    · have hbig := Nat.pow_le_pow_left hN 56
      norm_num at hbig
      omega
    · exact h
  apply (offDiagonal_cone_error_of_kernel (by positivity : 0≤2*(N:ℝ)^e) (kernel hh) ho (show K%2=1 by dsimp [K,coneWidth];omega) (by omega) hw).trans
  linarith only [denominator_error he hN₁ hh,ht,hlin,hpr.le]

theorem scale_window_control {e : ℕ} (he : 32≤e) (he48 : e≤48) (kernel : Kernel e) : ∃ C : ℝ, 0<C ∧ ∀ {N p : ℕ}, 2≤N → p.Prime → N^56≤p → p≤N^64 →
    |(S p:ℝ)/p-log p/2| ≤ C+(8/π^2)*‖windowExtension (coneWindow (coneWidth N)) (2*cutoff e N) p‖ := by
  obtain ⟨C,hC,hdiag⟩ := S_sub_offDiagonal_asymptotic
  refine ⟨C+2301000,by positivity,?_⟩
  intro N p hN hp hl hh
  let : Fact p.Prime := ⟨hp⟩
  have hJ := (cutoff_bounds he he48 (show 1≤N by omega)).2.1
  have hY := (Nat.mul_le_mul_left 2 (hJ.trans (Nat.pow_le_pow_right (by omega : 0<N) (by decide : 51≤52)))).trans_lt
    (cutoff_inside hN hl)
  have ho : p%2=1 := by
    rcases hp.eq_two_or_odd with h|h
    · have hx := Nat.pow_le_pow_left hN 56
      norm_num at hx
      omega
    · exact h
  have hpr : 0<(p:ℝ) := by exact_mod_cast hp.pos
  let B := (rationalCone p (cutoff e N) (coneWidth N):ℝ)
  let D := (S p:ℝ)-p*log p/2
  have h1 : |D-offDiagonal p|≤C*p := by dsimp [D];rw [sub_right_comm];exact hdiag p ho
  have h2 : |offDiagonal p-(8*p/π^2)*B|≤2301000*(p:ℝ) := cone_error he he48 kernel hN hp hl hh
  have h3 := (abs_sub_le D (offDiagonal p) ((8*p/π^2)*B)).trans (add_le_add h1 h2)
  have h4 := abs_sub_le D ((8*p/π^2)*B) 0
  simp only [sub_zero,abs_mul,abs_of_pos (show 0<(8*p/π^2:ℝ) by positivity)] at h4
  rw [cone_interpolation (show coneWidth N%2=1 by dsimp [coneWidth];omega) hp hY,
    ← Complex.ofReal_ratCast,Complex.norm_real,Real.norm_eq_abs,
    show (S p:ℝ)/p-log p/2 = D/p by dsimp [D];field_simp,abs_div,abs_of_pos hpr,div_le_iff₀ hpr]
  change |D|≤(C+2301000+(8/π^2)*|B|)*p
  exact (h4.trans (add_le_add_left h3 _)).trans_eq (by ring)

#print axioms elementary_kernel
#print axioms cone_error
#print axioms scale_window_control
#print axioms cutoff_bounds
end
end Arxiv.«2501.03234».ThetaCalibratedCone
