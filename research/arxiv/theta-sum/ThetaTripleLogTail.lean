import ThetaMovingOriginalTail

/-! A triple-logarithmic moving error window for the signed double sum. -/
namespace Arxiv.«2501.03234».ThetaTripleLogTail
open Real Filter Finset ThetaMovingOriginalTail
noncomputable section

private theorem choice (m : ℕ) (H D : ℝ) :
    ∀ᶠ t : ℝ in atTop, ∃ k : ℕ, let h := 8*((m:ℝ)+2)*log t
      H≤h ∧ 1≤k ∧ (k:ℝ)≤exp (h/8) ∧ 128*(k:ℝ)^2*h≤exp t ∧
      log D+t+t^m≤(k:ℝ)*h/128 := by
  let b := 8*((m:ℝ)+2)
  have hb : 0<b := by dsimp [b];positivity
  have hbt := tendsto_log_atTop.const_mul_atTop hb
  have he := (tendsto_exp_div_pow_atTop (2*(m+1)+1)).eventually_ge_atTop (512*b)
  filter_upwards [eventually_ge_atTop (2:ℝ),eventually_ge_atTop (log D),
    hbt.eventually_ge_atTop H,hbt.eventually_ge_atTop 384,he] with t ht hD hH h384 hbudget
  let h := b*log t
  let z := t^(m+1)
  let k := ⌈z⌉₊
  have ht₁ : 1≤t := by linarith
  have htp : 0<t := by linarith
  have hz : 1≤z := one_le_pow₀ ht₁
  have hk : z≤(k:ℝ) := Nat.le_ceil _
  have hk' : (k:ℝ)≤2*z := by linarith only [hz,Nat.ceil_lt_add_one (by linarith only [hz] : 0≤z)]
  have hk₀ : 1≤k := by exact_mod_cast hz.trans hk
  have hlarge : 384≤h := h384
  have hpos : 0≤h := by linarith
  refine ⟨k,hH,hk₀,?_,?_,?_⟩
  · change (k:ℝ)≤exp (h/8)
    have heq : exp (h/8)=t^(m+2) := by
      have hx : h/8=((m+2:ℕ):ℝ)*log t := by dsimp [h,b];push_cast;ring
      rw [hx,exp_nat_mul,exp_log htp]
    rw [heq,show m+2=(m+1)+1 by omega,pow_succ]
    exact hk'.trans (by dsimp [z];nlinarith only [mul_le_mul_of_nonneg_right ht (pow_nonneg htp.le (m+1))])
  · change 128*(k:ℝ)^2*h≤exp t
    have hlog : h≤b*t := mul_le_mul_of_nonneg_left (le_trans (log_le_sub_one_of_pos htp) (by linarith)) hb.le
    have hprod := mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) hk' 2) hlog hpos (sq_nonneg _)
    have hupper : 128*(k:ℝ)^2*h≤(512*b)*t^(2*(m+1)+1) := calc
      _ ≤ 128*((2*z)^2*(b*t)) := by linarith only [hprod]
      _ = _ := by rw [pow_succ t (2*(m+1)),show 2*(m+1)=(m+1)*2 by omega,pow_mul];dsimp [z];ring
    exact hupper.trans ((le_div_iff₀ (pow_pos htp _)).mp hbudget)
  · change log D+t+t^m≤(k:ℝ)*h/128
    have ht' : t≤z := by simpa only [pow_one] using (pow_le_pow_right₀ ht₁ (show 1 ≤ m+1 by omega))
    have hm' : t^m≤z := pow_le_pow_right₀ ht₁ (by omega : m ≤ m+1)
    nlinarith only [hD,ht',hm',hk,mul_le_mul_of_nonneg_left hlarge (Nat.cast_nonneg (α:=ℝ) k)]

/-- In the upper half on a logarithmic scale, three iterated logarithms
at the endpoint are eventually at most twice those at the prime. -/
private theorem compare : ∀ᶠ X : ℕ in atTop, ∀ p : ℕ, X≤p^2 →
    0≤log (log (log (X:ℝ))) ∧ log (log (log (X:ℝ)))≤2*log (log (log (p:ℝ))) := by
  have hL := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have ht := tendsto_log_atTop.comp hL
  have hv := tendsto_log_atTop.comp ht
  obtain ⟨P,hP⟩ := eventually_atTop.mp ((hL.eventually_gt_atTop 0).and
    ((ht.eventually_ge_atTop 1).and (hv.eventually_ge_atTop 1)))
  filter_upwards [eventually_ge_atTop (P^2),eventually_ge_atTop 1,hL.eventually_gt_atTop 0,
    ht.eventually_gt_atTop 0,hv.eventually_ge_atTop 0] with X hx hX hLX htX hvX
  intro p hxp
  have hPp : P≤p := by by_contra! h;exact (Nat.pow_lt_pow_left h (by decide : 2≠0)).not_ge (hx.trans hxp)
  obtain ⟨hLp,htp,hvp⟩ := hP p hPp
  have hx' : 0<(X:ℝ) := by exact_mod_cast (show 0<X by omega)
  have hl := log_le_log hx' (show (X:ℝ)≤(p:ℝ)^2 by exact_mod_cast hxp)
  rw [log_pow] at hl
  simp only [Function.comp_apply] at hLX htX hLp htp hvp
  norm_num at hl
  have hl' := log_le_log hLX hl
  rw [log_mul (by norm_num : (2:ℝ)≠0) hLp.ne'] at hl'
  have htwo : log (2:ℝ)≤1 := by linarith only [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have H : log (log (X:ℝ))≤2*log (log (p:ℝ)) := by change 1≤log (log (p:ℝ)) at htp;linarith
  have H' := log_le_log htX H
  rw [log_mul (by norm_num) (show log (log (p:ℝ))≠0 by change 1≤log (log (p:ℝ)) at htp;linarith)] at H'
  exact ⟨hvX,by change 1≤log (log (log (p:ℝ))) at hvp;linarith⟩

/-- The same absolute coefficient works at every order m, with a quadratic
factor (m+2)². The error threshold is evaluated at each prime. -/
theorem original : ∃ C : ℝ, 0<C ∧ ∀ m : ℕ, ∀ᶠ X : ℕ in atTop,
    ((ThetaPrimeDensity.primeSet (fun p => C*((m:ℝ)+2)^2*(log (log (log (p:ℝ))))^2*(p:ℝ)≤
        |(S p:ℝ)-(p:ℝ)*log p/2|) X).card:ℝ)≤
      Nat.primeCounting X*exp (-((log (log X))^m)) := by
  obtain ⟨A,D,H,hA,hD,_,hb⟩ := ThetaMovingOriginalTail.original_of
  refine ⟨256*A,by positivity,?_⟩
  intro m
  let b := 8*((m:ℝ)+2)
  have hb₀ : 0<b := by dsimp [b];positivity
  have hL := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have htt := tendsto_log_atTop.comp hL
  filter_upwards [htt.eventually (choice m H D),hL.eventually_ge_atTop 1,hb,compare] with X hchoice hpos hbound hcomp
  let t := log (log (X:ℝ))
  let h := b*log t
  obtain ⟨k,hH,hk₀,hk,hbudget,hpay⟩ := hchoice
  have hl₁ : 1≤log (X:ℝ) := hpos
  have ht : exp t=log X := exp_log (by linarith)
  have hbudget' : 128*(k:ℝ)^2*h≤log X := hbudget.trans_eq ht
  apply (hbound hH hk₀ hk hbudget' _ ?_).trans
  · have hfac : D*exp (-((k:ℝ)*h)/128)≤exp (-(t^m)) := calc
      _ = exp (log D-((k:ℝ)*h)/128) := by rw [sub_eq_add_neg,exp_add,exp_log hD];congr 2;ring
      _ ≤ _ := exp_le_exp.mpr (by
        change log D+t+t^m≤(k:ℝ)*h/128 at hpay
        have hp : 0≤t := log_nonneg hl₁
        linarith)
    calc D*Nat.primeCounting X*exp (-((k:ℝ)*h)/128) = Nat.primeCounting X*(D*exp (-((k:ℝ)*h)/128)) := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_left hfac (Nat.cast_nonneg _)
  · intro p _ _ hxp hdev
    obtain ⟨hn,hl⟩ := hcomp p hxp
    have hsq := pow_le_pow_left₀ hn hl 2
    apply le_trans _ hdev
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg (α:=ℝ) p)
    change A*h^2≤(256*A)*((m:ℝ)+2)^2*(log (log (log (p:ℝ))))^2
    dsimp [b,h,t]
    nlinarith only [mul_le_mul_of_nonneg_left hsq (by positivity : 0≤64*A*((m:ℝ)+2)^2)]

#print axioms original
end
end Arxiv.«2501.03234».ThetaTripleLogTail
