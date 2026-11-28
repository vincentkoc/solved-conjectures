import ThetaCalibratedCone

/-! An extra dyadic level in the denominator cutoff gives a vanishing
normalized error throughout the same power band. -/
namespace Arxiv.«2501.03234».ThetaLocalVanishingCone
open Real Finset Filter ThetaCalibratedCone ThetaNondivisibleCone ThetaPrimeMeanSquare
open ThetaPrimeDensity ThetaDivisibleDiagonal ThetaReciprocalCutoff ThetaReciprocalInversion
noncomputable section

def fine (e N : ℕ) := ThetaCalibratedCone.cutoff e N * levels N

theorem bounds {e N : ℕ} (he : 32≤e) (h48 : e≤48) (hN : 1≤N) :
    N^2≤fine e N ∧ fine e N≤N^52 ∧
    (fine e N:ℝ)≤16*(N:ℝ)^e*(1+log N)^4 := by
  obtain ⟨hl,hu,hc⟩ := cutoff_bounds he h48 hN
  obtain ⟨_,hlog,hLN⟩ := levels_bounds hN
  refine ⟨hl.trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos _)),?_,?_⟩
  · exact (Nat.mul_le_mul hu hLN).trans_eq (by ring)
  · unfold fine; push_cast
    exact (mul_le_mul hc hlog (Nat.cast_nonneg _) (by positivity [log_nonneg (by exact_mod_cast hN : (1:ℝ)≤N)])).trans_eq (by ring)

theorem square_fit : ∀ᶠ N : ℕ in atTop, (levels N)^2≤N := by
  have ht := tendsto_natCast_atTop_atTop (R:=ℝ)
  have hh := ht.eventually ((isLittleO_log_rpow_rpow_atTop (2:ℝ) (by norm_num : (0:ℝ)<1)).bound
    (by norm_num : (0:ℝ)<1/16))
  filter_upwards [hh,(tendsto_log_atTop.comp ht).eventually_ge_atTop (1:ℝ),eventually_ge_atTop (1:ℕ)] with N h hL hN
  change 1≤log (N:ℝ) at hL
  have hq := (levels_bounds hN).2.1
  rw [show (2:ℝ)=((2:ℕ):ℝ) by norm_num,rpow_natCast,rpow_one,Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg _),Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg _)] at h
  have hh := pow_le_pow_left₀ (Nat.cast_nonneg (levels N) : 0≤(levels N:ℝ))
     (show (levels N:ℝ)≤4*log N by linarith only [hq,hL]) 2
  exact_mod_cast (show (levels N:ℝ)^2≤N by nlinarith only [hh,h])

/-- A quantitative error for the off-diagonal part, before the signed row split. -/
theorem estimate {e N p : ℕ} (he : 32≤e) (h48 : e≤48) (hk : Kernel e)
    (hN : 2≤N) (hfit : (levels N)^2≤N) (hp : p.Prime) (hl : N^56≤p) (hh : p≤N^64) :
    |offDiagonal p-(8*p/π^2)*(rationalCone p (fine e N) (coneWidth N):ℝ)|≤
      4600600*(p:ℝ)/levels N := by
  let : Fact p.Prime := ⟨hp⟩
  let J := fine e N
  let K := coneWidth N
  let L := (levels N:ℝ)
  have hN1 : 1≤N := by omega
  have hL : 1≤L := by dsimp [L,levels]; exact_mod_cast Nat.le_add_left 1 _
  have hLp : 0<L := by linarith
  have hLN := (levels_bounds hN1).2.2
  have hn : 1≤(N:ℝ) := by exact_mod_cast hN1
  have hD1 := (cutoff_bounds he h48 hN1).1
  have hD : (1:ℝ)≤ThetaCalibratedCone.cutoff e N := by exact_mod_cast (Nat.one_le_pow 2 N (by omega)).trans hD1
  have hJ : J≤N^52 := (bounds he h48 hN1).2.1
  have hjp := (Nat.mul_le_mul_left 2 hJ).trans_lt (cutoff_inside hN hl)
  have hKN : K≤N := by dsimp [K,coneWidth];omega
  have hNK : N≤2*K := by dsimp [K,coneWidth];omega
  have hKp : 0<(K:ℝ) := by exact_mod_cast (show 0<K by dsimp [K,coneWidth];omega)
  have hw : K*(2*J)≤p := calc
    _ ≤ N*(N*N^52) := Nat.mul_le_mul hKN (Nat.mul_le_mul hN hJ)
    _ = N^54 := by ring
    _ ≤ N^56 := Nat.pow_le_pow_right hN1 (by decide)
    _ ≤ p := hl
  have hJN : J*N*levels N≤p := calc
    _ ≤ N^52*N*N := Nat.mul_le_mul (Nat.mul_le_mul_right N hJ) hLN
    _ = N^54 := by ring
    _ ≤ N^56 := Nat.pow_le_pow_right hN1 (by decide)
    _ ≤ p := hl
  have hKJ : K*J≤N^64 := calc
    _ ≤ N*N^52 := Nat.mul_le_mul hKN hJ
    _ = N^53 := by ring
    _ ≤ N^64 := Nat.pow_le_pow_right hN1 (by decide)
  have hpr : 0<(p:ℝ) := by exact_mod_cast hp.pos
  have h₁ : 2*(kernelDiscrepancy p (2*(N:ℝ)^e)+2*(p.sqrt:ℝ))*p*harmonic (p/2)/(2*(J:ℝ)+1) ≤
      4600000*(p:ℝ)/L := by
    have hd := denominator_error he hN1 hh
    rw [div_le_iff₀ (by positivity)] at hd
    rw [div_le_iff₀ (by positivity),div_mul_eq_mul_div,le_div_iff₀ hLp]
    have hl' := mul_le_mul_of_nonneg_right hd hLp.le
    simp only [J,fine,Nat.cast_mul]
    change _≤4600000*(p:ℝ)*(2*((ThetaCalibratedCone.cutoff e N:ℝ)*L)+1)
    apply hl'.trans
    have hd' : (2*(ThetaCalibratedCone.cutoff e N:ℝ)+1)*L≤2*(2*((ThetaCalibratedCone.cutoff e N:ℝ)*L)+1) := by
      nlinarith only [mul_le_mul_of_nonneg_right hD hLp.le,hLp]
    nlinarith only [mul_le_mul_of_nonneg_left hd' hpr.le]
  have h₂ : 2*(p:ℝ)*harmonic J/K≤260*p/L := by
    have H := harmonic_bound hN1 (hJ.trans (Nat.pow_le_pow_right hN1 (by decide : 52≤64)))
    change (harmonic J:ℝ)≤65*L at H
    have hsq : L^2≤2*K := (show L^2≤(N:ℝ) by dsimp [L]; exact_mod_cast hfit).trans (by exact_mod_cast hNK)
    rw [div_le_div_iff₀ hKp hLp]
    nlinarith only [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right H hLp.le) hpr.le,mul_le_mul_of_nonneg_left hsq hpr.le]
  have h₃ : 2*(J:ℝ)^2*(2*(harmonic (K*J):ℝ)+(K:ℝ)^2)/p≤262*p/L := by
    have H := harmonic_bound hN1 hKJ
    have H' : (harmonic (K*J):ℝ)≤65*N := H.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hLN) (by norm_num))
    have hK2 := pow_le_pow_left₀ hKp.le (show (K:ℝ)≤N by exact_mod_cast hKN) 2
    have hb : 2*(harmonic (K*J):ℝ)+(K:ℝ)^2≤131*(N:ℝ)^2 := by
      nlinarith only [H',hK2,mul_nonneg (Nat.cast_nonneg N (α:=ℝ)) (sub_nonneg.mpr hn)]
    have hA : (J:ℝ)*N*L≤p := by dsimp [L]; exact_mod_cast hJN
    have hs := pow_le_pow_left₀ (by positivity : 0≤(J:ℝ)*N*L) hA 2
    have haux : (J:ℝ)^2*N^2*L≤(J:ℝ)^2*N^2*L^2 := by
      have h := mul_le_mul_of_nonneg_left hL hLp.le
      exact mul_le_mul_of_nonneg_left (by nlinarith only [h] : L≤L^2) (by positivity)
    rw [div_le_div_iff₀ hpr hLp]
    nlinarith only [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb (sq_nonneg (J:ℝ))) hLp.le,hs,haux]
  have ho := hp.eq_two_or_odd.resolve_left (by have := Nat.pow_le_pow_left hN 56; omega)
  apply (offDiagonal_cone_error_of_kernel (by positivity : 0≤2*(N:ℝ)^e) (hk hh) ho
    (show K%2=1 by dsimp [K,coneWidth];omega) (by omega) hw).trans
  change _≤4600600*(p:ℝ)/L
  apply (add_le_add (add_le_add h₁ h₂) h₃).trans
  rw [←add_div,←add_div,div_le_div_iff_of_pos_right hLp]
  linarith only [hpr]

#print axioms square_fit
#print axioms estimate
end
end Arxiv.«2501.03234».ThetaLocalVanishingCone
