import ThetaSievedCenteredMoment
import ThetaWindowPrimeBand
import ThetaSievedConcentration
import ThetaMovingScales

/-! Uniform finite prime counts after sieving every centered moment. -/
namespace Arxiv.«2501.03234».ThetaUniformPrimeBand
open Real Finset Filter ThetaSmoothConditionalModel ThetaCenteredWindow ThetaReciprocalInversion
open ThetaIdentityModels ThetaTiltBudget
noncomputable section

theorem finite : ∃ C B : ℝ, 0<C ∧ 0≤B ∧ ∀ᶠ U : ℕ in atTop,
    ∀ {N T : ℕ}, 2≤N → 2≤T → T≤N → ∀ (k : ℕ) {u : ℝ}, 0<u → ∀ s : Finset ℕ,
    (∀ p∈s,p.Prime ∧ N^56≤p ∧ p≤N^64 ∧
      C+(8/Real.pi^2)*(u+ThetaModelExponentialMoment.height U+1)≤|(S p:ℝ)/p-log p/2|) →
    (s.card:ℝ)≤B*(N:ℝ)^64/(log N*(T:ℝ)^(1/128:ℝ))+
      ((((N^64+1:ℕ):ℝ)*(Z/log N)*(2*exp total)*(((2*k:ℕ):ℝ)/tilt U)^(2*k)+
        2*(N:ℝ)^6*(12*Z*(T:ℝ)^2)^(2*k))/u^(2*k)) := by
  obtain ⟨C,hC,ctrl⟩ := ThetaPrimeMeanSquare.scale_window_control
  obtain ⟨B,hB,hv⟩ := ThetaSievedConcentration.high_variance
  refine ⟨C,B,hC,hB,?_⟩
  have hl := (tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop 1
  filter_upwards [ThetaSievedCenteredMoment.primes,hl,eventually_ge_atTop 2] with U hm hlog hU
  intro N T hN hT hTN k u hu s hs
  obtain ⟨L,hL,hctrl⟩ := ctrl N hN
  let Y := 2*N^52
  let W : Window := ⟨L,Y⟩
  have hNY : N≤Y := by dsimp [Y];have := Nat.le_self_pow (by decide : 52≠0) N;omega
  have hlogN := Real.log_pos (show (1:ℝ)<N by exact_mod_cast hN)
  have hTp : 0<(T:ℝ) := by exact_mod_cast (show 0<T by omega)
  have hhigh := (le_div_iff₀ (mul_pos hlogN (rpow_pos_of_pos hTp _))).mpr
    (hv hN (by omega : 1≤T) hTN L hL s (fun p hp => ⟨(hs p hp).1,(hs p hp).2.1,(hs p hp).2.2.1⟩))
  have hlow := hm T N hN hTN W (N^64+1) k s (by
    intro p hp
    obtain ⟨hpr,hlo,hhi,_⟩ := hs p hp
    exact ⟨hpr,hNY.trans_lt (ThetaPrimeDensity.cutoff_inside hN hlo),Nat.lt_succ_of_le hhi⟩)
  apply ThetaWindowPrimeBand.on_subset (A:=ThetaModelExponentialMoment.height U) hN (hTN.trans hNY) le_rfl 0 k s hu L hL hctrl
    (by simpa only [zero_add] using hhigh) (center T U W) _ hlow
  · simpa only [zero_add] using hs
  · intro i _
    have hb := ThetaOrbitProjection.smooth_baseline hT hU hlog W i
    have hh := abs_add_le (center T U W i) (ThetaOrbitProjection.smooth T U (rowModel T W) i)
    simp only [center,sub_add_cancel] at hh
    rw [zero_add]
    change |rowModel T W i|≤|center T U W i|+ThetaModelExponentialMoment.height U
    unfold center
    exact hh.trans (add_le_add_right hb _)

#print axioms finite

/-- At deviation A h² in S(p)/p − (log p)/2 the exponent is −kh/128
throughout the range k≤exp(h/8) and 2k²h≤log N. -/
theorem band : ∃ A D : ℝ, 0<A ∧ 0<D ∧ ∀ᶠ h : ℝ in atTop,
    ∀ {N k : ℕ}, 2≤N → 1≤k → (k:ℝ)≤exp (h/8) → 2*(k:ℝ)^2*h≤log N →
    ∀ s : Finset ℕ, (∀ p∈s,p.Prime ∧ N^56≤p ∧ p≤N^64 ∧
      A*h^2≤|(S p:ℝ)/p-log p/2|) →
      (s.card:ℝ)*log N≤D*(N:ℝ)^64*exp (-((k:ℝ)*h)/128) := by
  obtain ⟨C,B,hC,hB,h⟩ := finite
  obtain ⟨U₀,h₀⟩ := eventually_atTop.mp h
  let c := 8/Real.pi^2
  have hc : 0<c := by dsimp [c];positivity
  let K := 2*exp total
  have hK : 0<K := by dsimp [K];positivity
  have hZ : 0≤Z := tsum_nonneg (fun _ => by positivity)
  let V := 12*Z
  have hV : 0≤V := mul_nonneg (by norm_num) (tsum_nonneg (fun _ => by positivity))
  let A := C+c*(3+V+952*envelope)
  have hA : 0<A := by dsimp [A];positivity [envelope_nonneg]
  refine ⟨A,B+2*Z*K+2,hA,by positivity,?_⟩
  filter_upwards [ThetaMovingScales.parameters hV U₀,eventually_ge_atTop (1:ℝ)] with h hpar hh
  intro N k hN hk hke hsize s hs
  let L := log (N:ℝ)
  let Q := (k:ℝ)*h
  let u := (2+V)*h^2
  have hhp : 0<h := by linarith
  have hu : 0<u := by dsimp [u];positivity
  have hnr : 0<(N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have hkr : (1:ℝ)≤k := by exact_mod_cast hk
  have hL : 0<L := log_pos (by exact_mod_cast hN)
  have hQ : 2*Q≤L := by
    have hj : (k:ℝ)≤(k:ℝ)^2 := by nlinarith only [mul_le_mul_of_nonneg_left hkr (Nat.cast_nonneg (α:=ℝ) k)]
    change 2*(k:ℝ)^2*h≤L at hsize
    dsimp [Q];linarith only [mul_le_mul_of_nonneg_right hj hhp.le,hsize]
  have hQ₀ : 0≤Q := by dsimp [Q];positivity
  obtain ⟨U,T,hU,hT,hheight,hTl,hTh,hk',hend⟩ := hpar k hk hke
  have hTY : T≤N := by
    have ht : (T:ℝ)≤N := calc
      _ ≤ exp (2*Q) := by simpa only [Q,mul_assoc] using hTh
      _ ≤ exp L := exp_le_exp.mpr hQ
      _ = _ := exp_log hnr
    exact_mod_cast ht
  have H := h₀ U hU hN hT hTY k hu s (by
    intro p hps
    obtain ⟨hp,hl,ht,hdev⟩ := hs p hps
    refine ⟨hp,hl,ht,le_trans ?_ hdev⟩
    change C+c*(u+ThetaModelExponentialMoment.height U+1)≤A*h^2
    dsimp only [u,A]
    have hh₂ : 1≤h^2 := one_le_pow₀ hh
    nlinarith only [mul_le_mul_of_nonneg_left hheight hc.le,
      mul_le_mul_of_nonneg_left hh₂ (add_nonneg hC.le hc.le)])
  have hd : 1/(T:ℝ)^(1/128:ℝ)≤exp (-Q/128) := calc
    _ ≤ 1/exp Q^(1/128:ℝ) := one_div_le_one_div_of_le (rpow_pos_of_pos (exp_pos _) _) (rpow_le_rpow (exp_pos _).le hTl (by norm_num))
    _ = _ := by rw [←exp_mul,one_div,←exp_neg];congr 1;ring
  have hm : (((2*k:ℕ):ℝ)/(tilt U*u))^(2*k)≤exp (-Q/128) :=
    hk'.trans (exp_le_exp.mpr (by change -Q/4≤-Q/128;linarith))
  have hpN : (N:ℝ)^64=exp (64*L) := by rw [show (64:ℝ)=(64:ℕ) by norm_num,exp_nat_mul,exp_log hnr]
  let E := exp (-Q/128)
  have hend' : (N:ℝ)^6*exp (8*(k:ℝ)^2*h)*L≤(N:ℝ)^64*E := by
    calc _ ≤ (N:ℝ)^6*exp (8*(k:ℝ)^2*h)*N := mul_le_mul_of_nonneg_left (log_le_self hnr.le) (by positivity)
         _ = exp (7*L+8*(k:ℝ)^2*h) := by
           rw [exp_add,show (7:ℝ)=(7:ℕ) by norm_num,exp_nat_mul,exp_log hnr]
           ring
         _ ≤ _ := by
           rw [hpN,show E=exp (-Q/128) from rfl,←exp_add,exp_le_exp]
           change 2*(k:ℝ)^2*h≤L at hsize
           linarith
  let M := ((N^64+1:ℕ):ℝ)
  have hM : M≤2*(N:ℝ)^64 := by
    have hpow : 1≤(N:ℝ)^64 := one_le_pow₀ (by exact_mod_cast (show 1≤N by omega))
    dsimp [M];push_cast;linarith
  change (V*(T:ℝ)^2/u)^(2*k)≤_ at hend
  have he := (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hend (by positivity : 0≤(N:ℝ)^6)) hL.le).trans hend'
  have hm' := mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hM hZ) hK.le) hm
    (by positivity [show 0≤tilt U by unfold tilt;positivity]) (by positivity : 0≤2*(N:ℝ)^64*Z*K)
  have hhi := mul_le_mul_of_nonneg_left hd (by positivity : 0≤B*(N:ℝ)^64)
  apply (mul_le_mul_of_nonneg_right H hL.le).trans
  change (B*(N:ℝ)^64/(L*(T:ℝ)^(1/128:ℝ))+
        (M*(Z/L)*K*(((2*k:ℕ):ℝ)/tilt U)^(2*k)+2*(N:ℝ)^6*(V*(T:ℝ)^2)^(2*k))/u^(2*k))*L ≤ _
  have hdiv : (M*(Z/L)*K*(((2*k:ℕ):ℝ)/tilt U)^(2*k)+2*(N:ℝ)^6*(V*(T:ℝ)^2)^(2*k))/u^(2*k) =
    M*(Z/L)*K*(((2*k:ℕ):ℝ)/(tilt U*u))^(2*k)+2*(N:ℝ)^6*(V*(T:ℝ)^2/u)^(2*k) := by
    rw [add_div,mul_div_assoc,mul_div_assoc (2*(N:ℝ)^6),←div_pow,←div_pow,div_div]
  rw [hdiv,add_mul,add_mul,show B*(N:ℝ)^64/(L*(T:ℝ)^(1/128:ℝ))*L =
    B*(N:ℝ)^64*(1/(T:ℝ)^(1/128:ℝ)) by field_simp]
  have hmid (z : ℝ) : M*(Z/L)*K*z*L=M*Z*K*z := by field_simp
  rw [hmid]
  change _ ≤ (B+2*Z*K+2)*(N:ℝ)^64*E
  change _ ≤ _*E at hm' hhi
  linarith only [he,hm',hhi]

#print axioms band
end
end Arxiv.«2501.03234».ThetaUniformPrimeBand
