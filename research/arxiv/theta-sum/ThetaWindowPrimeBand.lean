import ThetaWindowFiniteMoments

/-! Finite exceptional counts for the original signed theta sum. -/
namespace Arxiv.«2501.03234».ThetaWindowPrimeBand
open Finset Real ThetaReciprocalInversion ThetaRowCorrelations ThetaSmoothConditionalModel
open ThetaDenominatorTails ThetaIdentityModels
noncomputable section

/-- Transfer two nonnegative moments restricted to the exceptional primes. -/
theorem on_subset {N T Y : ℕ} (hN : 2≤N) (hTY : T≤Y) (hYcap : Y≤2*N^52) (M k : ℕ) (s : Finset ℕ) {u C V U A : ℝ}
    (hu : 0<u) (L : ℕ → ℕ) (hL : L 1=0)
    (hctrl : ∀ p : ℕ,p.Prime → N^56≤p → p≤N^64 →
      |(S p:ℝ)/p-log p/2|≤C+8/Real.pi^2*‖windowExtension L Y p‖)
    (hF : ∑ i∈s,‖windowExtension (above T L) Y (M+i)‖^2≤V)
    (g : ℕ → ℝ) (happrox : ∀ i∈s, |rowModel T ⟨L,Y⟩ (M+i)|≤|g i|+A)
    (hG : ∑ i∈s,(g i)^(2*k)≤U)
    (hs : ∀ i∈s, (M+i).Prime ∧ N^56≤M+i ∧ M+i≤N^64 ∧
      C+(8/Real.pi^2)*(u+A+1)≤|(S (M+i):ℝ)/(M+i:ℕ)-log (M+i:ℕ)/2|) :
    (s.card:ℝ)≤V+U/u^(2*k) := by
  let W : Window := ⟨L,Y⟩
  let F (i : ℕ) := windowExtension (above T L) Y (M+i)
  let G (i : ℕ) := g i
  let G₀ (i : ℕ) := rowModel T W (M+i)
  have hden : 0<u^(2*k) := pow_pos hu _
  have he (i : ℕ) (hi : i∈s) : 1≤‖F i‖^2+(G i)^(2*k)/u^(2*k) := by
    let p := M+i
    obtain ⟨hpr,hlo,hhi,he⟩ := hs i hi
    have hY := hYcap.trans_lt (ThetaPrimeDensity.cutoff_inside hN hlo)
    have hcop (d : ℕ) (hd : d∈Icc 1 Y) : p.Coprime d :=
      hpr.coprime_iff_not_dvd.mpr (fun hdiv => (lt_of_le_of_lt (mem_Icc.mp hd).2 hY).not_ge
        (Nat.le_of_dvd (mem_Icc.mp hd).1 hdiv))
    have hsplit : windowExtension L Y p= (G₀ i:ℂ)+F i :=
      sub_eq_iff_eq_add.mp (window_split hTY L hL hcop)
    have hh := hctrl p hpr hlo hhi
    have hnorm := norm_add_le ((G₀ i:ℝ):ℂ) (F i)
    have hc : 0<8/Real.pi^2 := by positivity
    rw [hsplit] at hh
    rw [Complex.norm_real,Real.norm_eq_abs] at hnorm
    by_cases hhi' : 1≤‖F i‖
    · have hx : 1≤‖F i‖^2 := one_le_pow₀ hhi'
      have hg : 0≤(G i)^(2*k)/u^(2*k) := by rw [← pow_abs_two_mul]; positivity
      linarith only [hx,hg]
    · have hg : u≤|G i| := by
        by_contra! hl
        have hb : |G₀ i|≤|G i|+A := happrox i hi
        have hl' : ‖(G₀ i:ℂ)+F i‖<u+A+1 := by linarith
        linarith only [hh,he,mul_lt_mul_of_pos_left hl' hc]
      have hh' := pow_le_pow_left₀ hu.le hg (2*k)
      rw [pow_abs_two_mul] at hh'
      have hx : 1≤(G i)^(2*k)/u^(2*k) := by rw [le_div_iff₀ hden,one_mul];exact hh'
      linarith only [hx,sq_nonneg ‖F i‖]
  calc
    _ = ∑ _p∈s,(1:ℝ) := by simp
    _ ≤ ∑ i∈s,(‖F i‖^2+(G i)^(2*k)/u^(2*k)) := sum_le_sum he
    _ ≤ _ := by
      rw [sum_add_distrib,← sum_div]
      exact add_le_add hF (div_le_div_of_nonneg_right hG hden.le)

/-- Transfer a variance and an even moment on a translated interval to an
exceptional count for the signed theta sum. -/
theorem from_approximation {N T Y : ℕ} (hN : 2≤N) (hTY : T≤Y) (hYcap : Y≤2*N^52) (M H k : ℕ) {u C V U A : ℝ}
    (hu : 0<u) (L : ℕ → ℕ) (hL : L 1=0)
    (hctrl : ∀ p : ℕ,p.Prime → N^56≤p → p≤N^64 →
      |(S p:ℝ)/p-log p/2|≤C+8/Real.pi^2*‖windowExtension L Y p‖)
    (hF : ∑ i∈range H,‖windowExtension (above T L) Y (M+i)‖^2≤V)
    (g : ℕ → ℝ) (happrox : ∀ i<H, |rowModel T ⟨L,Y⟩ (M+i)|≤|g i|+A)
    (hG : ∑ i∈range H,(g i)^(2*k)≤U)
    (s : Finset ℕ) (hs : ∀ i∈s,i<H ∧ (M+i).Prime ∧ N^56≤M+i ∧ M+i≤N^64 ∧
      C+(8/Real.pi^2)*(u+A+1)≤|(S (M+i):ℝ)/(M+i:ℕ)-log (M+i:ℕ)/2|) :
    (s.card:ℝ)≤V+U/u^(2*k) := by
  have hsub : s⊆range H := fun i hi => mem_range.mpr (hs i hi).1
  apply on_subset hN hTY hYcap M k s hu L hL hctrl
    ((sum_le_sum_of_subset_of_nonneg hsub (by intros;positivity)).trans hF) g
    (fun i hi => happrox i (hs i hi).1)
    ((sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => Even.pow_nonneg (even_two_mul k) _)).trans hG)
    (fun i hi => (hs i hi).2)

theorem from_moments {N T Y : ℕ} (hN : 2≤N) (hTY : T≤Y) (hYcap : Y≤2*N^52) (M H k : ℕ) {u C V U : ℝ}
    (hu : 0<u) (L : ℕ → ℕ) (hL : L 1=0)
    (hctrl : ∀ p : ℕ,p.Prime → N^56≤p → p≤N^64 →
      |(S p:ℝ)/p-log p/2|≤C+8/Real.pi^2*‖windowExtension L Y p‖)
    (hF : ∑ i∈range H,‖windowExtension (above T L) Y (M+i)‖^2≤V)
    (hG : ∑ i∈range H,(rowModel T ⟨L,Y⟩ (M+i))^(2*k)≤U)
    (s : Finset ℕ) (hs : ∀ i∈s,i<H ∧ (M+i).Prime ∧ N^56≤M+i ∧ M+i≤N^64 ∧
      C+(8/Real.pi^2)*(u+1)≤|(S (M+i):ℝ)/(M+i:ℕ)-log (M+i:ℕ)/2|) :
    (s.card:ℝ)≤V+U/u^(2*k) := by
  apply from_approximation (A:=0) hN hTY hYcap M H k hu L hL hctrl hF
    (fun i => rowModel T ⟨L,Y⟩ (M+i)) (by intros;simp) hG s
  simpa only [add_zero] using hs

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
  apply from_moments hN hTY le_rfl 0 (N^64+1) k hu L hL hctrl
  · simpa only [zero_add] using hv (T:=T) (by omega) (above T L) (fun d hd => by simp [above,hd]) N (by omega)
  · simpa only [zero_add] using hm T ⟨L,2*N^52⟩ hT (N^64+1) (2*k)
  · intro p hp
    simpa only [zero_add] using And.intro (Nat.lt_succ_of_le (hs p hp).2.2.1) (hs p hp)

#print axioms from_moments
#print axioms prime_band
end
end Arxiv.«2501.03234».ThetaWindowPrimeBand
