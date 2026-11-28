import ThetaUniformPrimeTails

/-! A finite quantile bound for the original signed theta residual. -/
namespace Arxiv.«2501.03234».ThetaPrimeQuantiles
open Real Filter Finset ThetaMovingOriginalTail ThetaPrimeDensity
noncomputable section

def residual (p : ℕ) := |(S p:ℝ)/p-log p/2|
def height (L t : ℝ) := (1+log t)^2+(t^2/L)^2

theorem member {d : ℝ} {p X : ℕ} : p∈ThetaMovingOriginalTail.exceptions d X ↔
    p≤X ∧ p.Prime ∧ d≤residual p := by
  classical
  simp only [ThetaMovingOriginalTail.exceptions,primeSet,mem_filter,Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hl,hp⟩,hh⟩
    refine ⟨hl,hp,?_⟩
    have h : 0<(p:ℝ) := by exact_mod_cast hp.pos
    have he : ((S p:ℝ)/p-log p/2)*p=(S p:ℝ)-p*log p/2 := by field_simp
    rwa [←he,abs_mul,abs_of_pos h,mul_le_mul_iff_left₀ h] at hh
  · rintro ⟨hl,hp,hh⟩
    refine ⟨⟨hl,hp⟩,?_⟩
    have h : 0<(p:ℝ) := by exact_mod_cast hp.pos
    have he : ((S p:ℝ)/p-log p/2)*p=(S p:ℝ)-p*log p/2 := by field_simp
    rwa [←he,abs_mul,abs_of_pos h,mul_le_mul_iff_left₀ h]

theorem pointwise : ∃ M : ℝ, 0<M ∧ ∀ X p : ℕ, 1≤log X → p.Prime → p≤X →
    residual p≤M*(log X)^2 := by
  refine ⟨residual 2+24,by unfold residual;positivity,?_⟩
  intro X p hL hp hpX
  have hR : 0≤residual 2 := abs_nonneg _
  have hLp := log_nonneg (show (1:ℝ)≤p by exact_mod_cast hp.pos)
  have hX := log_le_log (show 0<(p:ℝ) by exact_mod_cast hp.pos) (show (p:ℝ)≤X by exact_mod_cast hpX)
  have hv : 1≤(log (X:ℝ))^2 := one_le_pow₀ hL
  rcases hp.eq_two_or_odd with h|h
  · subst p;nlinarith only [mul_le_mul_of_nonneg_left hv hR,hv]
  have habs : |(S p:ℝ)/p|≤1+4*(1+log p)^2 := by
    have hpr : 0<(p:ℝ) := by exact_mod_cast hp.pos
    rw [abs_div,abs_of_pos hpr,div_le_iff₀ hpr,mul_comm]
    exact ThetaFourier.abs_S_le_log_sq p hp (Nat.odd_iff.mpr h)
  have hsum := abs_sub ((S p:ℝ)/p) (log p/2)
  rw [abs_of_nonneg (by linarith : 0≤log (p:ℝ)/2)] at hsum
  have hs := pow_le_pow_left₀ (by linarith : 0≤1+log (p:ℝ)) (by linarith : 1+log (p:ℝ)≤2*log (X:ℝ)) 2
  change |(S p:ℝ)/p-log p/2|≤(residual 2+24)*(log X)^2
  nlinarith only [hsum,habs,hs,hX,hL,hv,mul_nonneg hR (sq_nonneg (log (X:ℝ))),sq_nonneg (log (X:ℝ)-1)]

private theorem select_height {A H : ℝ} (hA : 0<A) (hH : 1≤H) :
    ∃ C : ℝ, 0<C ∧ ∀ {L t : ℝ}, 1024*H≤L → 1≤t → 33554432*t≤L →
    ∃ h : ℝ, H≤h ∧ 512*h≤L ∧ A*h^2≤C*height L t ∧
      512*t≤h*min (exp (h/8)) (sqrt (L/(128*h))) := by
  let K : ℝ := 33554432
  let B := max (H+8*log 512+8) K
  have hB : 0<B := lt_of_lt_of_le (by norm_num : (0:ℝ)<33554432) (le_max_right ..)
  refine ⟨2*A*B^2,by positivity,?_⟩
  intro L t hbig ht hfit
  have hL : 0<L := by linarith
  have ht' : 0<t := by linarith
  let z := t^2/L
  have hz : 0≤z := by dsimp [z];positivity
  let h := H+8*log (512*t)+K*z
  have hlt : 0≤log t := log_nonneg ht
  have hlt' : 0≤log (512*t) := log_nonneg (by linarith)
  have hk : 0<K := by norm_num [K]
  have hH' : H≤h := by dsimp [h];linarith only [hlt',mul_nonneg hk.le hz]
  have hh₁ := hH.trans hH'
  have hh₀ : 0<h := by linarith
  have hsmall : K*z≤t := by
    dsimp [z,K];rw [←mul_div_assoc,div_le_iff₀ hL]
    nlinarith only [mul_le_mul_of_nonneg_right hfit ht'.le]
  have hcap : 512*h≤L := by
    have hlog := log_le_self (show 0≤512*t by positivity)
    dsimp only [h]
    linarith only [hlog,hsmall,hbig,hfit,ht'.le]
  have htB : h≤B*((1+log t)+z) := by
    have h₁ : H+8*log 512+8≤B := le_max_left ..
    have h₂ : K≤B := le_max_right ..
    have hlog := log_nonneg (by norm_num : (1:ℝ)≤512)
    dsimp only [h]
    rw [log_mul (by norm_num) ht'.ne']
    nlinarith only [h₁,mul_le_mul_of_nonneg_right h₁ hlt,mul_le_mul_of_nonneg_right h₂ hz,
      mul_nonneg (by linarith : 0≤H+8*log 512) hlt]
  refine ⟨h,hH',hcap,?_,?_⟩
  · have hs := pow_le_pow_left₀ hh₀.le htB 2
    change A*h^2≤2*A*B^2*((1+log t)^2+z^2)
    nlinarith only [mul_le_mul_of_nonneg_left hs hA.le,mul_nonneg (mul_nonneg hA.le (sq_nonneg B)) (sq_nonneg (1+log t-z))]
  · rw [mul_min_of_nonneg _ _ hh₀.le]
    apply le_min
    · have hl : log (512*t)≤h/8 := by dsimp only [h];linarith only [mul_nonneg hk.le hz,hH]
      have hlow : 512*t≤exp (h/8) := by rwa [←exp_log (by positivity : 0<512*t),exp_le_exp]
      exact hlow.trans (le_mul_of_one_le_left (exp_pos _).le hh₁)
    · have hsq : (512*t/h)^2≤L/(128*h) := by
        have hbase : K*z≤h := by dsimp only [h];linarith
        dsimp only [z,K] at hbase
        rw [←mul_div_assoc,div_le_iff₀ hL] at hbase
        rw [div_pow,div_le_div_iff₀ (sq_pos_of_pos hh₀) (by positivity)]
        nlinarith only [mul_le_mul_of_nonneg_right hbase hh₀.le]
      have he := (div_le_iff₀ hh₀).mp (Real.le_sqrt_of_sq_le hsq)
      linarith only [he]

/-- All upper quantiles hold simultaneously at every sufficiently large endpoint,
including levels t well above log X where the pointwise Fourier bound applies. -/
theorem original : ∃ C : ℝ, 0<C ∧ ∀ᶠ X : ℕ in atTop, ∀ t : ℝ, 1≤t →
    ((ThetaMovingOriginalTail.exceptions (C*height (log X) t) X).card:ℝ)≤
      Nat.primeCounting X*exp (-t) := by
  classical
  obtain ⟨A,H,hA,hH,hb⟩ := ThetaUniformPrimeTails.original
  obtain ⟨C,hC,hchoose⟩ := select_height hA hH
  obtain ⟨M,hM,hpoint⟩ := pointwise
  let K : ℝ := 33554432
  let D := max C ((M+1)*K^4)
  have hD : 0<D := hC.trans_le (le_max_left ..)
  refine ⟨D,hD,?_⟩
  have hlog := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [hb,hlog.eventually_ge_atTop (1024*H)] with X hX hL
  intro t ht
  let L := log (X:ℝ)
  change 1024*H≤L at hL
  have hL' : 1≤L := by linarith
  have hLp : 0<L := by linarith
  have ht' : 0<t := by linarith
  have hf : 0≤height L t := by unfold height;positivity
  by_cases hfit : K*t≤L
  · obtain ⟨h,hH',hcap,hsize,hcut⟩ := hchoose hL ht hfit
    have hsub : ThetaMovingOriginalTail.exceptions (D*height L t) X⊆ThetaMovingOriginalTail.exceptions (A*h^2) X := by
      intro p hp
      obtain ⟨hl,hp,hr⟩ := member.mp hp
      exact member.mpr ⟨hl,hp,(hsize.trans (mul_le_mul_of_nonneg_right (le_max_left ..) hf)).trans hr⟩
    apply (Nat.cast_le.mpr (card_le_card hsub)).trans ((hX h hH' hcap).trans ?_)
    exact mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by linarith only [hcut])) (Nat.cast_nonneg _)
  · have hfalse : ThetaMovingOriginalTail.exceptions (D*height L t) X=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro p hp
      obtain ⟨hl,hp,he⟩ := member.mp hp
      have hr := hpoint X p hL' hp hl
      change residual p≤M*L^2 at hr
      have hpos : 0<K := by norm_num [K]
      have hfit' : L≤K*t := le_of_not_ge hfit
      have hv : L≤K^2*(t^2/L) := by
        rw [←mul_div_assoc,le_div_iff₀ hLp]
        nlinarith only [pow_le_pow_left₀ hLp.le hfit' 2]
      have hlarge := pow_le_pow_left₀ hLp.le hv 2
      have hh : (M+1)*K^4*(t^2/L)^2≤D*height L t := by
        apply (mul_le_mul_of_nonneg_right (le_max_right ..) (sq_nonneg (t^2/L))).trans
        exact mul_le_mul_of_nonneg_left (by unfold height;linarith only [sq_nonneg (1+log t)]) hD.le
      nlinarith only [hr,he,hh,mul_le_mul_of_nonneg_left hlarge (by linarith : 0≤M+1),sq_pos_of_pos hLp]
    change ((ThetaMovingOriginalTail.exceptions (D*height L t) X).card:ℝ)≤_
    rw [hfalse,card_empty,Nat.cast_zero];positivity

#print axioms original
end
end Arxiv.«2501.03234».ThetaPrimeQuantiles
