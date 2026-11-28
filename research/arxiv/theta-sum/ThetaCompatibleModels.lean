import ThetaCompatibleCapture
import ThetaCompatibleUnits
import ThetaFactorialSequence

/-! Uniform lower bounds for the finite models on compatible unit classes. -/
namespace Arxiv.«2501.03234».ThetaCompatibleModels
open Finset Filter Real ThetaRowCorrelations ThetaIdentityFiber ThetaDivisorLogMean ThetaSmoothRows
open ThetaPeriodMeans ThetaConditionalRows ThetaReciprocalBlocks ThetaPrimeTailTransfer
open ThetaPrimeMeanSquare ThetaReciprocalInversion ThetaFactorialSequence ThetaIdentityModels
open scoped Topology
noncomputable section

theorem budget {m r Y V : ℕ} (hm2 : 2≤ m) (hr : r< m) (hc : r.Coprime m)
    (hY : m≤ Y) {E : ℝ}
    (hBad : ∀ D : Finset ℕ, (∀ d∈D, 0< d ∧ d≤ Y ∧ ¬d∣m) →
      (1080*Z)*∑ d∈D,logWeight (m.gcd d)*tailWeight (d/(m.gcd d)) ≤ E) :
    letI : NeZero Y.factorial := ⟨Nat.factorial_ne_zero _⟩
    (∑ d∈m.divisors,ThetaCompatibleCapture.value (commonWeight (2*V^52))
      (coneWindow (coneWidth V)) r d)-E≤
       m.totient*unitMean Y.factorial (fun n => selectClass r m n*model Y V n) := by
  classical
  have hZ : 0≤ Z := tsum_nonneg fun _ => by positivity
  let P := Y.factorial
  let : NeZero P := ⟨Nat.factorial_ne_zero _⟩
  have hmP : m∣P := Nat.dvd_factorial (by omega) hY
  let K := coneWindow (coneWidth V)
  let a := commonWeight (2*V^52)
  let u (d : ℕ) := a d/d*residueMean r m d P (K d)
  let G := (Icc 2 Y).filter (·∣m)
  let D := (Icc 2 Y).filter (fun d => ¬d∣m)
  have hscale : (m.totient:ℝ)*unitMean P (fun n => selectClass r m n*model Y V n)=∑ d∈Icc 2 Y,u d := by
    change (m.totient:ℝ)*unitMean P (fun n => selectClass r m n*low Y K a n)=_
    rw [mean_low,mul_sum]
    apply sum_congr rfl; intro d _
    unfold u residueMean; ring
  rw [hscale,←sum_filter_add_sum_filter_not (Icc 2 Y) (·∣m)]
  have good : (∑ d∈m.divisors,ThetaCompatibleCapture.value a K r d)=∑ d∈G,u d := by
    simp only [ThetaCompatibleCapture.value,←sum_filter]
    apply sum_congr _ _
    · ext d
      simp only [G,mem_filter,mem_Icc,Nat.mem_divisors]
      exact ⟨fun ⟨⟨h,_⟩,hl⟩ => ⟨⟨hl,(Nat.le_of_dvd (by omega) h).trans hY⟩,h⟩,
        fun ⟨⟨h,_⟩,hd⟩ => ⟨⟨hd,by omega⟩,h⟩⟩
    · intro d hd
      obtain ⟨hd,h⟩ := mem_filter.mp hd
      dsimp only [u]
      rw [residue_captured hm2 hr hc (mem_Icc.mp hd).1 hmP h]
      ring
  change _-E≤ (∑ d∈G,u d)+(∑ d∈D,u d)
  rw [show (∑ d∈m.divisors,ThetaCompatibleCapture.value (commonWeight (2*V^52)) (coneWindow (coneWidth V)) r d)=_ from good]
  have hu (d : ℕ) (hd : d∈D) : -u d ≤ (1080*Z)*(logWeight (m.gcd d)*tailWeight (d/(m.gcd d))) := by
    have hd2 := (mem_Icc.mp (mem_filter.mp hd).1).1
    have hdP : d∣P := Nat.dvd_factorial (by omega) (mem_Icc.mp (mem_filter.mp hd).1).2
    have H := residue_envelope hm2 hr hc hd2 hmP hdP (K d)
    obtain ⟨ha,ha'⟩ := commonWeight_bounds (2*V^52) d
    calc _ ≤ |u d| := neg_le_abs _
         _ = a d*(|residueMean r m d P (K d)|/d) := by simp only [u,abs_mul,abs_div,abs_of_nonneg (show 0≤ a d from ha),abs_of_nonneg (Nat.cast_nonneg d : 0≤ (d:ℝ))]; ring
         _ ≤ Z*(1080*logWeight (m.gcd d)*tailWeight (d/(m.gcd d))) :=
               mul_le_mul ha' H (by positivity) hZ
         _ = _ := by ring
  have hh := sum_le_sum hu
  rw [sum_neg_distrib,←mul_sum] at hh
  have herr := hBad D (fun d hd => by obtain ⟨hd,h⟩ := mem_filter.mp hd; obtain ⟨hl,hr⟩ := mem_Icc.mp hd; exact ⟨by omega,hr,h⟩)
  change _ ≤ E at herr
  linarith


/-- A unit class refining any given reduced progression has models of size at
least a fixed multiple of the squared logarithm of the factorial parameter. -/
theorem growing {q r : ℕ} (hq : 0< q) (hr : r< q) (hc : r.Coprime q) :
    ∀ᶠ T : ℕ in atTop, let m := modulus T
      1< m ∧ q∣m ∧ ∃ n< m, n.Coprime m ∧ n%q=r ∧
        ∀ᶠ Y : ℕ in atTop, ∀ᶠ V : ℕ in atTop,
          letI : NeZero Y.factorial := ⟨Nat.factorial_ne_zero _⟩
          m∣Y.factorial ∧ (log T)^2/64≤
           m.totient*unitMean Y.factorial (fun j => selectClass n m j*model Y V j) := by
  have hZ : 1≤ Z := (weight_one (by decide : 0<1) (le_refl 1)).trans (commonWeight_bounds 1 1).2
  let B := 1+3*Z
  obtain ⟨A,hA⟩ := exists_nat_gt (max (128*B) 2)
  obtain ⟨a,ha,hap,H⟩ := ThetaCompatibleUnits.compatible hq hr hc A
  have haA : A< a := (le_max_left ..).trans_lt ha
  have haR : max (128*B) 2 < (a:ℝ) := hA.trans (by exact_mod_cast haA)
  have hodd : Odd a := hap.odd_of_ne_two (by
    have hh : (2:ℝ)< a := (le_max_right ..).trans_lt haR
    exact_mod_cast hh.ne')
  let C := Z*(4*(a:ℝ)+3)
  let F := C+B/a*(1+log a)+1
  have hlog : Tendsto (fun t : ℕ => log (t:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (max 2 q),hlog.eventually_ge_atTop (64*F),
    little (1080*Z) (by positivity) (show (0:ℝ)<1 by norm_num)] with T ht hbig hbad
  let m := modulus T
  have hT : 2≤ T := (le_max_left ..).trans ht
  have hm : 0< m := pow_pos (Nat.factorial_pos _) _
  have hdvd {d : ℕ} (hd : 0< d) (hdT : d≤ T) : d∣m :=
    (Nat.dvd_factorial hd hdT).trans (dvd_pow_self _ (by omega : T≠0))
  have hm2 := Nat.le_of_dvd hm (hdvd (by decide : 0<2) hT)
  have hqdiv := hdvd hq ((le_max_right ..).trans ht)
  obtain ⟨n,hn,hnc,hnq,hinv⟩ := H m hm hqdiv
  refine ⟨hm2,hqdiv,n,hn,hnc,hnq,?_⟩
  filter_upwards [eventually_ge_atTop m] with Y hY
  filter_upwards [eventually_ge_atTop (max m 3)] with V hV
  have hmV := (le_max_left ..).trans hV
  have h3 := (le_max_right ..).trans hV
  let P := Y.factorial
  let : NeZero P := ⟨Nat.factorial_ne_zero _⟩
  refine ⟨Nat.dvd_factorial hm hY,?_⟩
  let A' := commonWeight (2*V^52)
  let K := coneWindow (coneWidth V)
  have hg := ThetaCompatibleCapture.lower hodd hnc hinv A' K hZ (fun d hd => by
    have hdV := (Nat.le_of_dvd hm (Nat.mem_divisors.mp hd).1).trans hmV
    have hp : V≤ V^52 := Nat.le_self_pow (by decide) V
    exact ⟨weight_one (Nat.pos_of_mem_divisors hd) (by omega),(commonWeight_bounds ..).2⟩)
    (fun d _ hd => by
      have hw : 3≤ coneWidth V := by dsimp [coneWidth]; omega
      have hh := Nat.mul_le_mul_right d hw
      simp only [K,coneWindow,if_neg (by omega : d≠1)]
      omega)
  have hb := budget (V:=V) hm2 hn hnc hY (E:=mass m)
    (fun D hD => by simpa only [one_mul] using hbad Y D hD)
  let D := mass m
  have hD : 0≤ D := mass_nonneg _
  have hL : log T ≤ D := ((Real.log_le_log (by positivity) (by exact_mod_cast Nat.le_succ T)).trans
    (log_add_one_le_harmonic T)).trans (factorial_mass (by omega : 0< T))
  have hLM : logMass m ≤ D*(1+4*D) := by
    apply (ThetaDivisorTriangle.smooth_log hm (by omega : 0< T) (fun _ h => factorial_smooth h)).trans
    apply mul_le_mul_of_nonneg_left _ hD; linarith
  have ha₀ : 0<(a:ℝ) := by exact_mod_cast hap.pos
  have hB : 0≤ B := by dsimp [B]; linarith
  have hk : B/a*4≤ 1/32 := by
    rw [div_mul_eq_mul_div,div_le_div_iff₀ ha₀ (by norm_num : (0:ℝ)<32)]
    linarith [(le_max_left ..).trans_lt haR]
  have he : B*((logMass m+log a*D)/a)≤ B/a*(D*(1+4*D)+log a*D) := by
    rw [←mul_div_assoc,div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ ha₀.le
    exact mul_le_mul_of_nonneg_left (add_le_add_left hLM _) hB
  have hsq := mul_le_mul_of_nonneg_right hk (sq_nonneg D)
  have hlin := mul_le_mul_of_nonneg_right (hbig.trans hL) hD
  have hlg := pow_le_pow_left₀ (log_nonneg_nat T) hL 2
  change _≤ (m.totient:ℝ)*unitMean P _
  apply le_trans _ hb
  change D^2/16-C*D-B*((logMass m+log a*D)/a)≤ _ at hg
  dsimp only [F] at hlin
  change _≤ (∑ d∈m.divisors,ThetaCompatibleCapture.value A' K n d)-D
  linarith only [hg,he,hsq,hlin,hlg]

#print axioms budget
#print axioms growing

end
end Arxiv.«2501.03234».ThetaCompatibleModels
