import ThetaLocalMomentComparison
import ThetaResidualMoments

/-! Transfer an ordinary global prime moment to every admitted short interval. -/
namespace Arxiv.«2501.03234».ThetaLocalPrimeMomentLimits
open Real Filter Finset ThetaCharacterPrimeMeans ThetaNaturalPrimeMeans ThetaLocalDyadicReference
open ThetaLocalPrimeCounts ThetaLocalModelComparison ThetaLocalMomentComparison ThetaCalibratedCone ThetaPeriodMeans
open scoped Topology
noncomputable section

theorem dyadic {θ : ℝ} (hθ : θ≤1) (h : Ordinary θ) {f : ℕ → ℝ} {a : ℝ}
    (hf : Tendsto (primeMean f) atTop (𝓝 a)) : Tendsto (fun X : ℕ => avg X X f) atTop (𝓝 a) := by
  obtain ⟨C,hC,hπ⟩ := pi_bound
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let t := ε/(8*C)
  let u := ε/(4*(|a|+1))
  have ht : 0<t := by dsimp [t];positivity
  have hu : 0<u := by dsimp [u];positivity
  have he := Metric.tendsto_nhds.mp hf t ht
  have hsmall : 2*C*t+|a| *u<ε := by
    have hh : 8*C*t=ε := by dsimp [t];field_simp
    have H : (|a|+1)*u=ε/4 := by dsimp [u];field_simp
    linarith only [hh,H,hε,hu]
  have hin : ∀ᶠ X : ℕ in atTop, |(∑ p∈Nat.primesLE X,f p)-a*X.primeCounting|≤t*X.primeCounting := by
    filter_upwards [he,Nat.tendsto_primeCounting.eventually_gt_atTop (0:ℕ)] with X hx hX
    have hp : 0<(X.primeCounting:ℝ) := by exact_mod_cast hX
    rw [Real.dist_eq] at hx
    change |(∑ p∈Nat.primesLE X,f p)/X.primeCounting-a|<t at hx
    have heq : (∑ p∈Nat.primesLE X,f p)/X.primeCounting-a=
        ((∑ p∈Nat.primesLE X,f p)-a*X.primeCounting)/X.primeCounting := by field_simp
    rw [heq,abs_div,abs_of_pos hp,div_lt_iff₀ hp] at hx
    exact hx.le
  filter_upwards [hin,twice.eventually hin,hπ,relative_count h hu,ThetaLocalMomentBudgets.count h,
    eventually_ge_atTop (1:ℕ)] with X h₁ h₂ htop hcnt hcount hx
  have hl := full_length hx hθ
  let M := mass X X
  have hm : 0<M := (hcount X le_rfl hl).1
  have hc := hcnt X le_rfl hl
  have hp : (X.primeCounting:ℝ)≤(2*X).primeCounting := by
    exact_mod_cast Nat.monotone_primeCounting (show X≤2*X by omega)
  have H := dyadic_add X f
  have HH := dyadic_add X (fun _ => (1:ℝ))
  simp only [sum_const,nsmul_eq_mul,mul_one,Nat.primesLE_card_eq_primeCounting] at HH
  let F := ∑ p∈sample X X,f p
  have hset : F-a*(sample X X).card =
      ((∑ p∈Nat.primesLE (2*X),f p)-a*(2*X).primeCounting)-((∑ p∈Nat.primesLE X,f p)-a*X.primeCounting) := by
    dsimp [F]; nlinarith only [H,congrArg (fun z : ℝ => a*z) HH]
  have hA : |F-a*(sample X X).card|≤2*t*C*M := by
    rw [hset];apply (abs_sub ..).trans
    change _≤t*(2*X).primeCounting at h₂
    linarith only [h₁,h₂,mul_le_mul_of_nonneg_left (hp.trans htop) ht.le,mul_le_mul_of_nonneg_left htop ht.le]
  have hB : |a*((sample X X).card-M)|≤|a| *(u*M) := by
    rw [abs_mul];exact mul_le_mul_of_nonneg_left hc (abs_nonneg _)
  rw [Real.dist_eq]
  have hnorm : |avg X X f-a|≤2*C*t+|a| *u := by
    apply normalized hm
    change |F-M*a|≤_
    rw [show F-M*a=F-a*(sample X X).card+a*((sample X X).card-M) by ring]
    exact (abs_add_le ..).trans (by linarith only [hA,hB])
  exact hnorm.trans_lt hsmall

theorem transfer {e : ℕ} (he : 32≤e) (h48 : e≤48) (hk : Kernel e)
    {θ : ℝ} (hθ : (e:ℝ)/64<θ) (hθ₁ : θ≤1) (h : Ordinary θ)
    {q : ℕ} (hq : 0<q) (g w : ℕ → ℝ) (hg : OnMod q g) (hw : OnMod q w)
    (hA : ∀ n, |g n|≤1) {D : ℝ} (hD : ∀ n, |w n|≤D) (k : ℕ) {a : ℝ}
    (hf : Tendsto (primeMean (fun p => g p*(w p+residual p)^k)) atTop (𝓝 a)) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ X : ℕ in atTop, ∀ H : ℕ, H≤X → (X:ℝ)^θ≤H →
    |avg X H (fun p => g p*(w p+residual p)^k)-a|<ε := by
  filter_upwards [Metric.tendsto_nhds.mp (dyadic hθ₁ h hf) (ε/2) (half_pos hε),
      original he h48 hk hθ hθ₁ h hq g w hg hw hA hD k (half_pos hε)] with X hd hs
  intro H hHX hlen
  let f (p : ℕ) := g p*(w p+residual p)^k
  rw [Real.dist_eq] at hd
  change |avg X X f-a|<ε/2 at hd
  have hh : |avg X H f-avg X X f|≤ε/2 := hs H hHX hlen
  exact (abs_sub_le (avg X H f) (avg X X f) a).trans_lt (by linarith only [hh,hd])

#print axioms dyadic
#print axioms transfer
end
end Arxiv.«2501.03234».ThetaLocalPrimeMomentLimits
