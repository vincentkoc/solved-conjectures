import ThetaCompatibleModels
import ThetaRoughRepresentatives
import ThetaCompactSequence

/-! Uniform lower bounds for the finite models on compatible unit classes. -/
namespace Arxiv.«2501.03234».ThetaCompactModels
open Finset Filter Real ThetaRowCorrelations ThetaIdentityFiber ThetaDivisorLogMean ThetaSmoothRows
open ThetaPeriodMeans ThetaConditionalRows ThetaReciprocalBlocks ThetaPrimeTailTransfer
open ThetaPrimeMeanSquare ThetaReciprocalInversion ThetaCompactModulus ThetaIdentityModels
open scoped Topology
noncomputable section

/-- All reduced classes with q ≤ T^η admit a large positive model at
the same cutoff threshold. The exponent is independent of the class. -/
theorem uniform : ∃ η : ℝ, 0<η ∧ ∀ᶠ T : ℕ in atTop,
    ∀ q r : ℕ, 0 < q → r < q → r.Coprime q → log q≤η*log T →
      let m := modulus T
      1 < m ∧ q∣m ∧ ∃ n < m, n.Coprime m ∧ n%q=r ∧
        ∀ Y ≥ m, ∀ V ≥ max m 3,
          letI : NeZero Y.factorial := ⟨Nat.factorial_ne_zero _⟩
          m∣Y.factorial ∧ (log T)^2/64≤
           m.totient*unitMean Y.factorial (fun j => selectClass n m j*model Y V j) := by
  have hZ : 1≤Z := (weight_one (by decide : 0<1) (le_refl 1)).trans (commonWeight_bounds 1 1).2
  have hz : 0<Z := by linarith
  let B := 1+3*Z
  have hB : 0<B := by dsimp [B]; positivity
  let η := 1/(4096*Z)
  have hη : 0<η := by dsimp [η]; positivity
  have hη1 : η≤1 := by dsimp [η]; rw [div_le_one (by positivity)]; linarith
  have hscale : 4096*Z*η=1 := by dsimp [η]; field_simp
  let P (T : ℕ) := ⌊2*η*log T⌋₊
  have htend : Tendsto (fun T : ℕ => log (T:ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hPL : Tendsto P atTop atTop := tendsto_nat_floor_atTop.comp
    ((tendsto_const_mul_atTop_of_pos (by positivity : 0<2*η)).mpr htend)
  refine ⟨η,hη,?_⟩
  filter_upwards [eventually_ge_atTop 2,hPL.eventually_ge_atTop 2,
    (htend.comp hPL).eventually_ge_atTop (4096*B),
    ((tendsto_const_mul_atTop_of_pos hη).mpr htend).eventually_ge_atTop 1,
    htend.eventually_ge_atTop (1024*Z),
    ThetaCompactSequence.little (1080*Z) (by positivity) (show (0:ℝ)<1 by norm_num)] with T hT hP hLP hηT hlarge hbad
  intro q r hq hr hc hqt
  change 4096*B≤log (P T) at hLP
  change 1≤η*log T at hηT
  have hT0 : 0<(T:ℝ) := by exact_mod_cast (by omega : 0<T)
  have hLT := log_nonneg_nat T
  have hqT : q≤T := by
    exact_mod_cast (log_le_log_iff (by exact_mod_cast hq) hT0).mp
      (hqt.trans (by simpa using mul_le_mul_of_nonneg_right hη1 hLT))
  have hpFloor : (P T:ℝ)≤2*η*log T := Nat.floor_le (by positivity)
  have hsmall : log q≤P T := by
    have hfloor := Nat.lt_floor_add_one (2*η*log T)
    change _<(P T:ℝ)+1 at hfloor
    linarith only [hfloor,hηT,hqt]
  obtain ⟨a,hodd,hla,hδ,H⟩ := ThetaRoughRepresentatives.compatible hq hr hc hP hsmall
  let m := modulus T
  have hm : 0 < m := positive T
  have hdvd {d : ℕ} (hd : 0< d) (hdT : d≤ T) : d∣m :=
    contains hd hdT
  have hm2 := Nat.le_of_dvd hm (hdvd (by decide : 0<2) hT)
  have hqdiv := hdvd hq hqT
  obtain ⟨n,hn,hnc,hnq,hinv⟩ := H m hm hqdiv
  refine ⟨hm2,hqdiv,n,hn,hnc,hnq,?_⟩
  intro Y hY V hV
  have hmV := (le_max_left ..).trans hV
  have h3 := (le_max_right ..).trans hV
  let F := Y.factorial
  let : NeZero F := ⟨Nat.factorial_ne_zero _⟩
  refine ⟨Nat.dvd_factorial hm hY,?_⟩
  let A' := commonWeight (2*V^52)
  let K := coneWindow (coneWidth V)
  have hg := ThetaRoughDivisorBudget.lower hodd hnc hinv A' K hZ (fun d hd => by
    have hdV := (Nat.le_of_dvd hm (Nat.mem_divisors.mp hd).1).trans hmV
    have hp : V≤ V^52 := Nat.le_self_pow (by decide) V
    exact ⟨weight_one (Nat.pos_of_mem_divisors hd) (by omega),(commonWeight_bounds ..).2⟩)
    (fun d _ hd => by
      have hw : 3≤ coneWidth V := by dsimp [coneWidth]; omega
      have hh := Nat.mul_le_mul_right d hw
      simp only [K,coneWindow,if_neg (by omega : d≠1)]
      omega)
  have hb := ThetaCompatibleModels.budget (V:=V) hm2 hn hnc hY (E:=mass m)
    (fun D hD => by simpa only [one_mul] using hbad Y D hD)
  let D := mass m
  have hD : 0≤ D := mass_nonneg _
  have hL : log T ≤ D := ((Real.log_le_log (by positivity) (by exact_mod_cast Nat.le_succ T)).trans
    (log_add_one_le_harmonic T)).trans (bulk T)
  have hLM : logMass m ≤ D*(1+4*D) := by
    apply (ThetaDivisorTriangle.smooth_log hm (by omega : 0< T) (fun _ h => ThetaCompactModulus.smooth h)).trans
    apply mul_le_mul_of_nonneg_left _ hD; linarith
  let δ := ∑ p∈a.primeFactors,(p:ℝ)⁻¹
  have hδ0 : 0≤δ := sum_nonneg (fun _ _ => by positivity)
  have ha₀ : 0<(a:ℝ) := by exact_mod_cast hodd.pos
  have hDlarge := hlarge.trans hL
  have hD1 : 1≤D := by linarith
  have hLoga : log a≤D := by
    have h' := mul_le_mul_of_nonneg_right (show 8*η≤1 by
      dsimp [η]; rw [←mul_div_assoc,div_le_one (by positivity)]; linarith) hLT
    linarith only [hla,hpFloor,h',hL]
  have hC : Z*(2*log (2*(a:ℝ))+5) ≤ D/64 := by
    rw [log_mul (by norm_num) ha₀.ne']
    have hx := mul_le_mul_of_nonneg_left (hla.trans (mul_le_mul_of_nonneg_left hpFloor (by norm_num))) hz.le
    have hs := congrArg (fun t : ℝ => t*log T) hscale
    have htwo := mul_le_mul_of_nonneg_left (log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)) hz.le
    nlinarith only [hx,hs,htwo,hDlarge,hL,hD]
  have hδB : B*δ≤1/1024 := by
    apply (mul_le_mul_of_nonneg_left hδ hB.le).trans
    rw [←mul_div_assoc,div_le_div_iff₀ (log_pos (by exact_mod_cast (show 1<P T by omega))) (by norm_num : (0:ℝ)<1024)]
    linarith only [hLP]
  have hbase : logMass m+log a*D≤6*D^2 := by
    nlinarith only [hLM,mul_le_mul_of_nonneg_right hLoga hD,mul_le_mul_of_nonneg_right hD1 hD]
  have hcost : B*((logMass m+log a*D)*δ)≤6*D^2/1024 := by
    calc _ ≤ B*(6*D^2*δ) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hbase hδ0) hB.le
         _ = B*δ*(6*D^2) := by ring
         _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right hδB (show 0≤6*D^2 by positivity)]
  have hcost' := mul_le_mul_of_nonneg_right hC hD
  have hDsq := mul_le_mul_of_nonneg_right (show (128:ℝ)≤D by linarith) hD
  have hlg := pow_le_pow_left₀ hLT hL 2
  change _≤ (m.totient:ℝ)*unitMean F _
  apply le_trans _ hb
  change D^2/16-Z*(2*log (2*(a:ℝ))+5)*D-B*((logMass m+log a*D)*δ)≤ _ at hg
  change _≤ (∑ d∈m.divisors,ThetaCompatibleCapture.value A' K n d)-D
  nlinarith only [hg,hcost,hcost',hDsq,hlg,sq_nonneg D]

#print axioms uniform

end
end Arxiv.«2501.03234».ThetaCompactModels
