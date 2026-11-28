import ThetaLocalPowerDiscrepancy
import ThetaLocalMomentBudgets

/-! A moving model, shifted and tested by fixed periodic functions, has the
same normalized moments in all admissible intervals at one endpoint. -/
namespace Arxiv.«2501.03234».ThetaLocalSampledPowers
open Real Filter Finset ThetaPeriodMeans ThetaConditionalRows ThetaPrimeTailTransfer
open ThetaReciprocalBlocks ThetaRowCorrelations ThetaPrimeMeanSquare ThetaReciprocalInversion
open ThetaSmoothConditionalModel ThetaIdentityModels ThetaWindowFiniteMoments ThetaLocalPrimeCounts
open ThetaRowProgressionDiscrepancy
noncomputable section

private theorem shifted {q Y : ℕ} (hq : 0<q) (hY : 1≤Y) {k : ℕ} (N : ℕ)
    {A D : ℝ} (g w : ℕ → ℝ) (hg : OnMod q g) (hw : OnMod q w)
    (hA : ∀ n, |g n|≤A) (hD : ∀ n, |w n|≤D) {s : Finset ℕ} {M δ : ℝ} (hδ : 0≤δ)
    (hc : ∀ d : ℕ, 0<d → d≤q*Y^k → Classes s d M δ) :
    let P := q*Y.factorial
    letI : NeZero P := ⟨(Nat.mul_pos hq (Nat.factorial_pos _)).ne'⟩
    let S (n : ℕ) := g n*(w n+(8/π^2)*model Y N n)^k
    |(∑ n∈s,S n)-M*unitMean P S|≤δ*q*A*((D+(8/π^2)*(6*Z))*(Y:ℝ)^2)^k := by
  classical
  let c := 8/π^2
  have hcpos : 0<c := by dsimp [c];positivity
  let W : Window := ⟨coneWindow (coneWidth N),2*N^52⟩
  let line (d n : ℕ) := (commonWeight W.weightCutoff d/d)*row d (W.width d) n
  let f (d n : ℕ) := if d=1 then w n else c*line d n
  have hZ : 0≤Z := tsum_nonneg fun _ => by positivity
  have hDp := (abs_nonneg _).trans (hD 0)
  let P := q*Y.factorial
  let : NeZero P := ⟨(Nat.mul_pos hq (Nat.factorial_pos _)).ne'⟩
  have hperiod (d : ℕ) (_hd : d∈Icc 1 Y) : OnMod (q.lcm d) (f d) := by
    by_cases he : d=1
    · simpa only [f,if_pos he] using onMod_lift (Nat.dvd_lcm_left q d) hw
    · intro n
      simp only [f,if_neg he,line]
      rw [onMod_lift (Nat.dvd_lcm_right q d) (row_onMod d (W.width d)) n]
  have hbound (d : ℕ) (hd : d∈Icc 1 Y) (n : ℕ) : |f d n|≤D+c*(6*Z) := by
    by_cases he : d=1
    · simp only [f,if_pos he]; exact (hD n).trans (le_add_of_nonneg_right (by positivity))
    · have hh := weighted_bound (by have := (mem_Icc.mp hd).1;omega : 1<d) W n
      simp only [f,if_neg he,abs_mul,abs_of_pos hcpos]
      exact (mul_le_mul_of_nonneg_left hh hcpos.le).trans (le_add_of_nonneg_left hDp)
  have hmodel (n : ℕ) : (∑ d∈Icc 1 Y,f d n)=w n+c*model Y N n := by
    have he : Icc 1 Y=insert 1 (Icc 2 Y) := by ext d;simp only [mem_Icc,mem_insert];omega
    rw [he,sum_insert (by simp)]
    simp only [f,if_pos rfl]
    congr 1
    change _=c*∑ d∈Icc 2 Y,line d n
    rw [mul_sum]
    apply sum_congr rfl;intro d hd
    rw [if_neg (by have := (mem_Icc.mp hd).1;omega)]
  have hs := ThetaLocalPowerDiscrepancy.mixed (P:=P) hq (dvd_mul_right q _) (dvd_mul_left _ _)
    g hg hA f s k hδ (show 0≤D+c*(6*Z) by positivity) hperiod hbound hc
  simpa only [hmodel] using hs

/-- Ordinary short-interval prime counts transfer every fixed mixed moment,
uniformly over all logarithmic denominator cutoffs and all numerator widths. -/
theorem original {θ : ℝ} (h : Ordinary θ) {q : ℕ} (hq : 0<q) {A D : ℝ}
    (g w : ℕ → ℝ) (hg : OnMod q g) (hw : OnMod q w) (hA : ∀ n, |g n|≤A) (hD : ∀ n, |w n|≤D)
    (k j : ℕ) {ε : ℝ} (hε : 0<ε) : ∀ᶠ X : ℕ in atTop, ∀ {Y : ℕ}, 1≤Y →
    (Y:ℝ)≤(log X)^j → ∀ N H : ℕ, H≤X → (X:ℝ)^θ≤H →
    let P := q*Y.factorial
    letI : NeZero P := ⟨(Nat.mul_pos hq (Nat.factorial_pos _)).ne'⟩
    let S (n : ℕ) := g n*(w n+(8/π^2)*model Y N n)^k
    |(∑ n∈sample X H,S n)-mass X H*unitMean P S|≤ε*mass X H := by
  let b := D+(8/π^2)*(6*Z)
  have hZ : 0≤Z := tsum_nonneg fun _ => by positivity
  have hA₀ := (abs_nonneg _).trans (hA 0)
  have hb : 0≤b := by have := (abs_nonneg _).trans (hD 0);dsimp [b];positivity
  let u := j*(2*k)
  let t := j*k+1
  have ht := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [classes h t (u+2),ht.eventually_ge_atTop (q:ℝ),ht.eventually_ge_atTop (1:ℝ),
    ht.eventually_ge_atTop (2*q*A*b^k/ε),eventually_ge_atTop (2:ℕ)] with X hcl hqL hL hcost hx
  intro Y hY hy N H hHX hlen
  let L := log (X:ℝ)
  change 1≤L at hL
  have hLp : 0<L := zero_lt_one.trans_le hL
  have hmods (d : ℕ) (hd : d≤q*Y^k) : (d:ℝ)≤L^t := by
    have hh : (d:ℝ)≤q*(Y:ℝ)^k := by exact_mod_cast hd
    apply hh.trans
    calc (q:ℝ)*(Y:ℝ)^k ≤ L*(L^j)^k :=
           mul_le_mul hqL (pow_le_pow_left₀ (Nat.cast_nonneg _) hy k) (by positivity) hLp.le
         _ = _ := by rw [←pow_mul];dsimp [t];ring
  have H₀ := shifted (k:=k) hq hY N g w hg hw hA hD (by positivity : 0≤(H:ℝ)/L^(u+2))
    (fun d hd hsize => hcl H hHX hlen d hd (hmods d hsize))
  apply H₀.trans
  have hmass := mass_lower hx hHX
  apply le_trans _ (mul_le_mul_of_nonneg_left hmass hε.le)
  have hy' : (Y:ℝ)^(2*k)≤L^u := (pow_le_pow_left₀ (Nat.cast_nonneg _) hy (2*k)).trans_eq (by rw [←pow_mul])
  have hcost' := (div_le_iff₀ hε).mp hcost
  change 2*(q:ℝ)*A*b^k≤L*ε at hcost'
  change (H:ℝ)/L^(u+2)*q*A*(b*(Y:ℝ)^2)^k≤ε*(H/(2*L))
  rw [mul_pow,←pow_mul]
  apply (mul_le_mul_of_nonneg_left hy' (show 0≤(H:ℝ)/L^(u+2)*q*A*b^k by positivity)).trans' ?_ |>.trans ?_
  · ring_nf;exact le_rfl
  · rw [pow_add L u 2]
    have hh : (H:ℝ)/(L^u*L^2)*q*A*b^k*L^u = (q*A*b^k/(2*L))*(H:ℝ)*2/L := by field_simp
    rw [hh]
    field_simp
    nlinarith only [mul_le_mul_of_nonneg_right hcost' (Nat.cast_nonneg H (α:=ℝ))]

#print axioms original
end
end Arxiv.«2501.03234».ThetaLocalSampledPowers
