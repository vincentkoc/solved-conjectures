import ThetaWindowFiniteMoments

/-! Finite exceptional counts for the original signed theta sum. -/
namespace Arxiv.«2501.03234».ThetaWindowPrimeBand
open Finset Real ThetaReciprocalInversion ThetaRowCorrelations ThetaSmoothConditionalModel
open ThetaDenominatorTails ThetaIdentityModels
noncomputable section

/-- Markov on a low-row moment and the high-row variance. The moment order and
denominator cutoff can both grow with the endpoint. -/
theorem prime_band : ∃ C a K B : ℝ, 0<C ∧ 0<a ∧ 0<K ∧ 0≤B ∧
    ∀ {N T : ℕ}, 2≤N → 2≤T → T≤2*N^52 → ∀ (k : ℕ) {u : ℝ}, 0<u → ∀ s : Finset ℕ,
    (∀ p∈s,p.Prime ∧ N^56≤p ∧ p≤N^64 ∧
      C+(8/Real.pi^2)*(u+1)≤|(S p:ℝ)/p-log p/2|) →
    (s.card:ℝ) ≤ B*(N:ℝ)^64/(T:ℝ)^(1/64:ℝ) +
      ((((N^64+1:ℕ):ℝ)*K*((2*k:ℕ)/a)^(2*k) + 2*(6*Z*(T:ℝ)^2)^(2*k))/u^(2*k)) := by
  obtain ⟨C,hC,ctrl⟩ := ThetaPrimeMeanSquare.scale_window_control
  obtain ⟨a,K,ha,hK,hm⟩ := ThetaWindowFiniteMoments.finite_moment
  obtain ⟨B,hB,hv⟩ := cut_variance
  refine ⟨C,a,K,B,hC,ha,hK,hB,?_⟩
  intro N T hN hT hTY k u hu s hs
  obtain ⟨L,hL,hctrl⟩ := ctrl N hN
  let Y := 2*N^52
  let W : Window := ⟨L,Y⟩
  let F := windowExtension (above T L) Y
  let G := rowModel T W
  have hF := hv (T:=T) (by omega) (above T L) (fun d hd => by simp [above,hd]) N (by omega)
  have hG := hm T W hT (N^64+1) (2*k)
  have hden : 0<u^(2*k) := pow_pos hu _
  have hs' : s⊆range (N^64+1) := fun p hp => mem_range.mpr (Nat.lt_succ_of_le (hs p hp).2.2.1)
  have he (p : ℕ) (hp : p∈s) : 1≤‖F p‖^2+(G p)^(2*k)/u^(2*k) := by
    obtain ⟨hpr,hlo,hhi,he⟩ := hs p hp
    have hY := ThetaPrimeDensity.cutoff_inside hN hlo
    have hcop (d : ℕ) (hd : d∈Icc 1 Y) : p.Coprime d :=
      hpr.coprime_iff_not_dvd.mpr (fun hdiv => (lt_of_le_of_lt (mem_Icc.mp hd).2 hY).not_ge
        (Nat.le_of_dvd (mem_Icc.mp hd).1 hdiv))
    have hsplit : windowExtension L Y p=(G p:ℂ)+F p :=
      sub_eq_iff_eq_add.mp (window_split hTY L hL hcop)
    have hh := hctrl p hpr hlo hhi
    have hnorm := norm_add_le ((G p:ℝ):ℂ) (F p)
    have hc : 0<8/Real.pi^2 := by positivity
    rw [show 2*N^52=Y from rfl,hsplit] at hh
    rw [Complex.norm_real,Real.norm_eq_abs] at hnorm
    by_cases hhi' : 1≤‖F p‖
    · have hx : 1≤‖F p‖^2 := one_le_pow₀ hhi'
      have hg : 0≤(G p)^(2*k)/u^(2*k) := by rw [← pow_abs_two_mul]; positivity
      linarith only [hx,hg]
    · have hg : u≤|G p| := by
        by_contra! hl
        have hl' : ‖(G p:ℂ)+F p‖<u+1 := by linarith
        linarith only [hh,he,mul_lt_mul_of_pos_left hl' hc]
      have hh' := pow_le_pow_left₀ hu.le hg (2*k)
      rw [pow_abs_two_mul] at hh'
      have hx : 1≤(G p)^(2*k)/u^(2*k) := by rw [le_div_iff₀ hden,one_mul];exact hh'
      linarith only [hx,sq_nonneg ‖F p‖]
  calc
    _ = ∑ _p∈s,(1:ℝ) := by simp
    _ ≤ ∑ p∈s,(‖F p‖^2+(G p)^(2*k)/u^(2*k)) := sum_le_sum he
    _ ≤ ∑ p∈range (N^64+1),(‖F p‖^2+(G p)^(2*k)/u^(2*k)) :=
      sum_le_sum_of_subset_of_nonneg hs' (by intro p _ _;rw [← pow_abs_two_mul];positivity)
    _ ≤ _ := by
      rw [sum_add_distrib,← sum_div]
      exact add_le_add hF (div_le_div_of_nonneg_right hG hden.le)

#print axioms prime_band
end
end Arxiv.«2501.03234».ThetaWindowPrimeBand
