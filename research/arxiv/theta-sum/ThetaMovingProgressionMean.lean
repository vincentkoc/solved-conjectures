import ThetaRowProgressionDiscrepancy
import ThetaMovingPrimeModelError
import ThetaReflectedWindowMeans

/-! Signed means on growing refinements of any reduced class at a finite prime endpoint. -/
namespace Arxiv.«2501.03234».ThetaMovingProgressionMean
open Finset Filter Real ThetaPrimeTailTransfer ThetaConditionalRows ThetaIdentityModels
open ThetaIdentityFiber ThetaRowProgressionDiscrepancy ThetaCompactModulus
noncomputable section

private theorem aggregate : ∃ C : ℝ, 0<C ∧ ∀ {N Y m r : ℕ} (s : Finset ℕ) {M δ L z : ℝ},
    |z|=1 → 2≤N → 0 < m → r < m → r.Coprime m → m≤Y → Y≤N → 0≤M → 0≤δ →
    (∀ p∈s,p.Prime ∧ N^56≤p ∧ p≤N^64) →
    Classes s m M δ → (∀ d∈Icc 2 Y,Classes s (m*d) M δ) →
    let w := M/(m.totient:ℝ)
    δ≤w → Y*(3*Z*(1+log Y)*δ)≤w → (N:ℝ)^64/(log N*(Y:ℝ)^(1/128:ℝ))≤w →
    letI : NeZero Y.factorial := ⟨Nat.factorial_ne_zero _⟩
    L ≤ z*(m.totient*unitMean Y.factorial (fun n => selectClass r m n*model Y N n)) →
    w*((8/Real.pi^2)*L-C) ≤
      ∑ p∈s.filter (fun n => n%m=r),z*((S p:ℝ)/p-log p/2) := by
  obtain ⟨D,B,hD,hB,H⟩ := ThetaMovingPrimeModelError.square
  let c := 8/Real.pi^2
  have hc : 0<c := by dsimp [c]; positivity
  refine ⟨c+2*(1+D)+B,by positivity,?_⟩
  intro N Y m r s M δ L z hz hN hm hr hcop hmY hYN hM hδ hs hcl hrows w hδw herr hhigh hL
  let : NeZero Y.factorial := ⟨Nat.factorial_ne_zero _⟩
  let A := s.filter (fun n => n%m=r)
  have hw : 0≤w := div_nonneg hM (Nat.cast_nonneg _)
  have hφ : 0<(m.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hm
  have hA : (A.card:ℝ)≤2*w := by
    have hh := (abs_le.mp (hcl r hr)).2
    simp only [if_pos hcop] at hh
    change (A.card:ℝ)-w≤δ at hh
    linarith
  let R (p : ℕ) := (S p:ℝ)/p-log p/2
  let f := model Y N
  let e (p : ℕ) := R p-c*f p
  have hE := H hN (by omega : 1≤Y) hYN A (fun p hp => hs p (mem_filter.mp hp).1)
  change (∑ p∈A,(e p)^2)≤_ at hE
  have hE' : (∑ p∈A,(e p)^2)≤(2*D+B)*w := by
    rw [mul_div_assoc] at hE
    nlinarith only [hE,mul_le_mul_of_nonneg_left hhigh hB,mul_le_mul_of_nonneg_left hA hD.le]
  have hdiff : (∑ p∈A,(c*(z*f p)-z*R p))≤(2+2*D+B)*w := by
    calc _ ≤ ∑ p∈A,(1+(e p)^2) := by
             apply sum_le_sum; intro p _
             calc c*(z*f p)-z*R p ≤ |z*(-e p)| := by
                     rw [show c*(z*f p)-z*R p=z*(-e p) by dsimp [e]; ring]; exact le_abs_self _
                  _ = |e p| := by rw [abs_mul,hz,one_mul,abs_neg]
                  _ ≤ _ := by nlinarith only [sq_nonneg (|e p|-1/2),sq_abs (e p)]
         _ ≤ _ := by simp only [sum_add_distrib,sum_const,nsmul_eq_mul,mul_one]; linarith
  have hmod := selected_model (V:=N) hm hr hmY hδ hrows
  let u := unitMean Y.factorial (fun n => selectClass r m n*f n)
  have hsum : (∑ n∈s,selectClass r m n*f n)=∑ n∈A,f n := by
    unfold A selectClass; rw [sum_filter]; apply sum_congr rfl; intro n _; split_ifs <;> simp
  change |(∑ n∈s,selectClass r m n*f n)-M*u|≤_ at hmod
  rw [hsum] at hmod
  have hscale : w*(m.totient:ℝ)=M := by dsimp [w]; field_simp
  have hmain : w*L≤z*(M*u) := by
    calc _ ≤ w*(z*(m.totient*u)) := mul_le_mul_of_nonneg_left hL hw
         _ = _ := by rw [←hscale]; ring
  have hms : |z*(∑ n∈A,f n)-z*(M*u)|≤w := by rw [←mul_sub,abs_mul,hz,one_mul]; exact hmod.trans herr
  have hlow : w*L-w≤z*∑ n∈A,f n := by linarith [(abs_le.mp hms).1]
  rw [sum_sub_distrib,←mul_sum,←mul_sum] at hdiff
  change w*(c*L-(c+2*(1+D)+B))≤∑ p∈A,z*R p
  nlinarith only [hdiff,mul_le_mul_of_nonneg_left hlow hc.le]

/-- For every fixed reduced progression there is a growing refinement on which
the finite sum of the signed original residual is quantitatively positive. -/
theorem uniform : ∃ η : ℝ, 0<η ∧ ∀ᶠ T : ℕ in atTop,
    ∀ q r : ℕ, 0 < q → r < q → r.Coprime q → Real.log q≤η*Real.log T → ∀ z : ℝ, |z|=1 →
    let m := modulus T
    1 < m ∧ q∣m ∧ ∃ b < m, b.Coprime m ∧ b%q=r ∧
    ∀ {N Y : ℕ} (s : Finset ℕ) {M δ : ℝ}, max m 3≤N → m≤Y → Y≤N → 0≤M → 0≤δ →
    (∀ p∈s,p.Prime ∧ N^56≤p ∧ p≤N^64) →
    Classes s m M δ → (∀ d∈Icc 2 Y,Classes s (m*d) M δ) →
    let w := M/(m.totient:ℝ)
    δ≤w → Y*(3*Z*(1+log Y)*δ)≤w → (N:ℝ)^64/(log N*(Y:ℝ)^(1/128:ℝ))≤w →
    w*(log T)^2/(16*Real.pi^2) ≤ ∑ p∈s.filter (fun n => n%m=b),z*((S p:ℝ)/p-log p/2) := by
  obtain ⟨C,hC,H⟩ := aggregate
  let c := 8/Real.pi^2
  have hc : 0<c := by dsimp [c]; positivity
  have ht : Tendsto (fun t : ℕ => (log (t:ℝ))^2) atTop atTop :=
    (tendsto_pow_atTop (n:=2) (by decide)).comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  obtain ⟨η,hη,U⟩ := ThetaReflectedWindowMeans.uniform
  refine ⟨η,hη,?_⟩
  filter_upwards [U,ht.eventually_ge_atTop (128*C/c)] with T Hm hL
  intro q r hq hr hcq hqt z hz
  have hb := Hm q r hq hr hcq hqt z hz
  obtain ⟨hm,hqm,b,hb,hcop,hbr,hu⟩ := hb
  refine ⟨hm,hqm,b,hb,hcop,hbr,?_⟩
  intro N Y s M δ hmN hmY hYN hM hδ hs hcl hrows w hδw herr hhigh
  have hU := hu Y hmY N hmN
  have h := H s hz (by omega) (by omega) hb hcop hmY hYN hM hδ hs hcl hrows hδw herr hhigh hU
  change w*(c*((log T)^2/64)-C)≤_ at h
  apply le_trans _ h
  have hw : 0≤w := div_nonneg hM (Nat.cast_nonneg _)
  have hL' := (div_le_iff₀ hc).mp hL
  calc w*(log T)^2/(16*Real.pi^2) = w*(c*((log T)^2/128)) := by dsimp [c]; ring
       _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith only [hL']) hw

#print axioms uniform
end
end Arxiv.«2501.03234».ThetaMovingProgressionMean
