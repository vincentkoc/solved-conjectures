import ThetaUniformPrimeClasses

/-! Quasipolynomial bound for a prime of any fixed theta slope in each large modulus. -/
namespace Arxiv.«2501.03234».ThetaLeastSlopePrime
open Filter Real Finset ThetaOccupancyScales ThetaUniformPrimeClasses ThetaPrimeDensity
noncomputable section
open scoped Classical

private theorem scales (X₀ : ℕ) : ∀ᶠ q : ℕ in atTop, ∃ X : ℕ,X₀≤X ∧ q^8≤X ∧
    (q:ℝ)≤exp (saving X) ∧ (X:ℝ)≤(q:ℝ)^(4294967296*(1+log (log q))) := by
  have hn := tendsto_natCast_atTop_atTop (R:=ℝ)
  have hl := tendsto_log_atTop.comp hn
  have hu := tendsto_log_atTop.comp hl
  filter_upwards [eventually_ge_atTop X₀,hn.eventually_gt_atTop 0,hl.eventually_ge_atTop 1,
    hu.eventually_ge_atTop 1,hu.eventually_ge_atTop (log 4294967296)] with q hq hpos hL hu hC
  let L := log (q:ℝ)
  let u := log L
  let z := 2147483648*L*(1+u)
  let X := ⌈exp z⌉₊
  change 1≤L at hL
  change 1≤u at hu
  change log 4294967296≤u at hC
  have hp : 0<L := by linarith
  have hz : 8*L≤z := by dsimp [z];nlinarith only [hL,mul_nonneg hp.le (by linarith : 0≤u)]
  have he : 2≤exp z := by linarith only [add_one_le_exp z,hz,hL]
  have hlo : exp z≤(X:ℝ) := Nat.le_ceil _
  have hhi : (X:ℝ)≤exp (2*z) := by
    calc _ ≤ exp z+1 := (Nat.ceil_lt_add_one (exp_pos _).le).le
         _ ≤ exp z*exp z := by nlinarith only [he,sq_nonneg (exp z-1)]
         _ = _ := by rw [←exp_add];congr 1;ring
  have hxp : 0<(X:ℝ) := (exp_pos _).trans_le hlo
  have hxl : z≤log (X:ℝ) := (le_log_iff_exp_le hxp).mpr hlo
  have hxu : log (X:ℝ)≤2*z := (log_le_iff_le_exp hxp).mpr hhi
  have hxl' : 1≤log (X:ℝ) := by linarith only [hxl,hz,hL]
  have hw : log (log (X:ℝ))≤3*u := by
    have h := log_le_log (by linarith : 0<log (X:ℝ)) hxu
    have hiden : 2*z=4294967296*L*(1+u) := by dsimp [z];ring
    rw [hiden,log_mul (by positivity) (by linarith),log_mul (by norm_num) hp.ne'] at h
    have hu' := log_le_sub_one_of_pos (show 0<1+u by linarith)
    change _ ≤ log 4294967296+u+log (1+u) at h
    linarith
  have hxq : (q:ℝ)≤X := by
    calc (q:ℝ) = exp L := (exp_log hpos).symm
         _ ≤ exp z := exp_le_exp.mpr (by linarith only [hL,hz])
         _ ≤ _ := hlo
  refine ⟨X,hq.trans (Nat.cast_le.mp hxq),?_,?_,?_⟩
  · have h : (q:ℝ)^8 ≤ X := by
      calc _ = exp (8*L) := by rw [show (8:ℝ)=(8:ℕ) by norm_num,exp_nat_mul,exp_log hpos]
           _ ≤ exp z := exp_le_exp.mpr hz
           _ ≤ _ := hlo
    exact_mod_cast h
  · rw [←log_le_iff_le_exp hpos]
    change L ≤ log (X:ℝ)/(1+log (log X))/268435456
    rw [le_div_iff₀ (by norm_num),le_div_iff₀ (by linarith only [log_nonneg hxl'])]
    have h := mul_le_mul_of_nonneg_left hw (by positivity : 0≤L*268435456)
    dsimp [z] at hxl
    nlinarith only [h,hxl,hL,mul_nonneg hp.le (by linarith : 0≤u)]
  · rw [rpow_def_of_pos hpos]
    convert hhi using 2
    dsimp [z,L,u]
    ring

private theorem witness (P : ℕ → Prop) {X q a : ℕ}
    (h : 0<((primes X q a).filter (fun p => ¬P p)).card) :
    ∃ p : ℕ,p.Prime ∧ p%q=a ∧ ¬P p ∧ p≤X := by
  obtain ⟨p,hp⟩ := card_pos.mp h
  obtain ⟨hp,hs⟩ := mem_filter.mp hp
  obtain ⟨hp,hr⟩ := mem_filter.mp hp
  obtain ⟨hle,hpr⟩ := Nat.mem_primesLE.mp hp
  exact ⟨p,hpr,hr,hs,hle⟩

private theorem least (H : Maynard) (P : ℕ → Prop)
    (hP : ∀ᶠ X : ℕ in atTop,((primeSet P X).card:ℝ)≤X.primeCounting*exp (-(log X/(1+log (log X))/33554432))) :
    ∀ᶠ q : ℕ in atTop,∀ a : ℕ,a<q → a.Coprime q →
    ∃ p : ℕ,p.Prime ∧ p%q=a ∧ ¬P p ∧ (p:ℝ)≤(q:ℝ)^(4294967296*(1+log (log q))) := by
  have hscale (X : ℕ) : log (X:ℝ)/(1+log (log X))/33554432=8*saving X := by unfold saving;ring
  simp_rw [hscale] at hP
  obtain ⟨Q,h⟩ := relative H _ hP
  obtain ⟨X₀,h₀⟩ := eventually_atTop.mp h
  filter_upwards [eventually_ge_atTop Q,scales X₀] with q hq ht a ha hg
  obtain ⟨X,hX,h8,he,hbound⟩ := ht
  obtain ⟨p,hpr,hr,hs,hle⟩ := witness P (h₀ X hX q a hq he h8 ha hg).2
  exact ⟨p,hpr,hr,hs,(Nat.cast_le.mpr hle).trans hbound⟩

theorem original (H : Maynard) (k : ℕ) : ∀ᶠ q : ℕ in atTop,∀ a : ℕ,a<q → a.Coprime q →
    ∃ p : ℕ,p.Prime ∧ p%q=a ∧ (k:ℤ)*p<S p ∧
      (p:ℝ)≤(q:ℝ)^(4294967296*(1+log (log q))) := by
  simpa only [not_le] using least H _ (ThetaMultiscaleExceptions.original_slope k)

theorem centered (H : Maynard) : ∃ A : ℝ,0<A ∧ ∀ᶠ q : ℕ in atTop,∀ a : ℕ,a<q → a.Coprime q →
    ∃ p : ℕ,p.Prime ∧ p%q=a ∧ |(S p:ℝ)/p-log p/2|<A*(1+log (log p))^2 ∧
      (p:ℝ)≤(q:ℝ)^(4294967296*(1+log (log q))) := by
  obtain ⟨A,hA,h⟩ := ThetaMultiscaleExceptions.original_centered
  exact ⟨A,hA,by simpa only [not_le] using least H _ h⟩

#print axioms centered
#print axioms original
end
end Arxiv.«2501.03234».ThetaLeastSlopePrime
