import ThetaCompactOmitted
import ThetaSmoothConditionalModel

/-! On any smooth refinement of the compact modulus, the denominators not
already determined by the original compact residue have small total mean. -/
namespace Arxiv.«2501.03234».ThetaSmoothRefinement
open Finset Real Filter ThetaDivisorBudget ThetaCompactOmitted ThetaCompactModulus
open ThetaFactorialRows ThetaSmoothRows ThetaDivisorLogMean ThetaSmoothConditionalModel
open ThetaIdentityModels ThetaIdentityFiber ThetaReciprocalBlocks
noncomputable section

private theorem covered {m T d : ℕ} (hm : 0 < m) (hm' : modulus T∣m)
    (hs : ∀ p∈m.primeFactors,p≤T) (hd : 0<d) (hmiss : ¬d∣modulus T) (hsmall : d/(m.gcd d)<T) :
    m.gcd d∈coverOf m T := by
  let g := (modulus T).gcd d
  let s := d/g
  have hg : g∣d := Nat.gcd_dvd_right ..
  have hs0 : 0<s := Nat.div_pos (Nat.le_of_dvd hd hg) (Nat.gcd_pos_of_pos_left _ (positive T))
  have hmul : g*s=d := Nat.mul_div_cancel' hg
  have hs1 : s≠1 := by
    intro h; rw [h,mul_one] at hmul
    exact hmiss (hmul ▸ Nat.gcd_dvd_left ..)
  let p := s.minFac
  have hp : p.Prime := Nat.minFac_prime hs1
  have hps : p∣s := Nat.minFac_dvd s
  have hpd : p∣d := hmul ▸ hps.trans (dvd_mul_left s g)
  have hqt : p≤T := by
    by_cases hpM : p∣m
    · exact hs _ (Nat.mem_primeFactors.mpr ⟨hp,hpM,hm.ne'⟩)
    · have hh := Nat.mul_div_cancel' (Nat.gcd_dvd_right m d)
      have hp' := hp.dvd_mul.mp (by rwa [hh] : p∣m.gcd d*(d/(m.gcd d)))
      have hpos := Nat.div_pos (Nat.le_of_dvd hd (Nat.gcd_dvd_right m d)) (Nat.gcd_pos_of_pos_left _ hm)
      exact (Nat.le_of_dvd hpos (hp'.resolve_left (fun h => hpM (h.trans (Nat.gcd_dvd_left ..))))).trans hsmall.le
  have hblock := saturated hp hqt hps
  have hdiv : g∣m.gcd d := Nat.dvd_gcd ((Nat.gcd_dvd_left ..).trans hm') hg
  exact mem_biUnion.mpr ⟨p,mem_Icc.mpr ⟨hp.two_le,hqt⟩,mem_filter.mpr
    ⟨Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left ..,hm.ne'⟩,hblock.trans hdiv⟩⟩

theorem omitted {m T Y : ℕ} (hm : 0 < m) (hT : 0<T) (hm' : modulus T∣m)
    (hs : ∀ p∈m.primeFactors,p≤T) (D : Finset ℕ)
    (hD : ∀ d∈D,0<d ∧ d≤Y ∧ ¬d∣modulus T) :
    ∑ d∈D,logWeight (m.gcd d)*tailWeight (d/(m.gcd d)) ≤
      logMass m*(zetaBound/(T:ℝ)^(1/16:ℝ))+((logMass m+4*log T*mass m)/T)*zetaBound := by
  have h := omitted_by_size hm hT D (coverOf m T) (fun d hd => ⟨(hD d hd).1,(hD d hd).2.1⟩)
    (fun d hd => covered hm hm' hs (hD d hd).1 (hD d hd).2.2)
  exact h.trans (add_le_add_right (mul_le_mul_of_nonneg_right (cover_mass_of m hT)
    (tsum_nonneg fun _ => by positivity : 0≤zetaBound)) _)

theorem error {m T r Y : ℕ} (hm : 1 < m) (hT : 0<T) (hm' : modulus T∣m)
    (hs : ∀ p∈m.primeFactors,p≤T) (hlog : 1≤log T) (hr : r < m) (hc : r.Coprime m)
    (hmP : m∣Y.factorial) (V : Window) :
    let D := (Icc 2 Y).filter (fun d => ¬d∣modulus T)
    |∑ d∈D,term m r Y V d| ≤ (1080*Z)*(612*zetaBound)*(log T)^2/(T:ℝ)^(1/16:ℝ) := by
  let D := (Icc 2 Y).filter (fun d => ¬d∣modulus T)
  intro D'
  let : NeZero Y.factorial := ⟨Nat.factorial_ne_zero _⟩
  have hZ : 0≤Z := tsum_nonneg fun _ => by positivity
  have hz : 0≤zetaBound := tsum_nonneg fun _ => by positivity
  have H (d : ℕ) (hd : d∈D) :
      |term m r Y V d|≤(1080*Z)*(logWeight (m.gcd d)*tailWeight (d/(m.gcd d))) := by
    obtain ⟨h₂,hy⟩ := mem_Icc.mp (mem_filter.mp hd).1
    have hd' : 0<d := by omega
    have h := residue_envelope hm hr hc h₂ hmP (Nat.dvd_factorial hd' hy) (V.width d)
    obtain ⟨ha,ha'⟩ := commonWeight_bounds V.weightCutoff d
    calc _ = (commonWeight V.weightCutoff d)*(|residueMean r m d Y.factorial (V.width d)|/d) := by
               simp only [term,abs_mul,abs_div,abs_of_nonneg ha,abs_of_nonneg (Nat.cast_nonneg d : (0:ℝ)≤d)]; ring
         _ ≤ Z*(1080*logWeight (m.gcd d)*tailWeight (d/(m.gcd d))) := mul_le_mul ha' h (by positivity) hZ
         _ = _ := by ring
  obtain ⟨hD,hL⟩ := smooth_bounds (by omega : 0 < m) hT hlog hs
  let l := log (T:ℝ)
  let t := (T:ℝ)^(1/16:ℝ)
  have ht : 0<t := rpow_pos_of_pos (Nat.cast_pos.mpr hT) _
  have htT : t≤T := by
    simpa only [rpow_one] using rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (show 1≤T by omega) : (1:ℝ)≤T) (by norm_num : (1/16:ℝ)≤1)
  have hsmall : mass m≤34*l := by change 1≤l at hlog; change _≤2+32*l at hD; linarith
  have hlog0 : 0≤l := le_trans (by norm_num : (0:ℝ)≤1) hlog
  have htop : logMass m+4*l*mass m≤374*l^2 := by
    change _≤238*l^2 at hL
    nlinarith only [hL,mul_le_mul_of_nonneg_left hsmall hlog0]
  have hM := omitted (by omega : 0 < m) hT hm' hs D (Y:=Y) (fun d hd => by
    obtain ⟨h,h'⟩ := mem_filter.mp hd; obtain ⟨h₂,hy⟩ := mem_Icc.mp h; exact ⟨by omega,hy,h'⟩)
  have hfrac : (logMass m+4*l*mass m)/T≤374*l^2/t :=
    (div_le_div_of_nonneg_right htop (Nat.cast_nonneg _)).trans (div_le_div_of_nonneg_left (by positivity) ht htT)
  have hsum : ∑ d∈D,logWeight (m.gcd d)*tailWeight (d/(m.gcd d))≤612*zetaBound*l^2/t := by
    apply hM.trans
    have hh := add_le_add (mul_le_mul_of_nonneg_right hL (show 0≤zetaBound/t by positivity))
      (mul_le_mul_of_nonneg_right hfrac hz)
    change _≤238*l^2*(zetaBound/t)+(374*l^2/t)*zetaBound at hh
    exact hh.trans_eq (by ring)
  apply ((abs_sum_le_sum_abs ..).trans (sum_le_sum H)).trans
  rw [←mul_sum]
  exact (mul_le_mul_of_nonneg_left hsum (by positivity : 0≤1080*Z)).trans_eq (by dsimp only [t,l];ring)

/-- The complete smooth conditional mean, uniformly in its precision, is
close to the mean conditioned only on the compact modulus. -/
theorem difference {M T a Y : ℕ} (hT : 2≤T) (hl : 1≤log T) (hdiv : modulus T∣M)
    (hs : ∀ p∈M.primeFactors,p≤T) (ha : a < M) (hc : a.Coprime M)
    (hP : M∣Y.factorial) (V : Window) :
    |cond M a Y V-cond (modulus T) (a%(modulus T)) Y V| ≤
      (2160*Z)*(612*zetaBound)*(log T)^2/(T:ℝ)^(1/16:ℝ) := by
  classical
  let : NeZero Y.factorial := ⟨Nat.factorial_ne_zero _⟩
  let m := modulus T
  have hm := positive T
  have hm2 : 2≤ m := Nat.le_of_dvd hm (contains (by decide : 0<2) hT)
  have hM := Nat.pos_of_dvd_of_pos hP (Nat.factorial_pos _)
  have hM2 := hm2.trans (Nat.le_of_dvd hM hdiv)
  have hau : (a%m).Coprime m := by
    change Nat.gcd (a%m) m=1
    rw [←Nat.gcd_rec]
    exact (hc.coprime_dvd_right hdiv).symm
  let I := Icc 2 Y
  let G := I.filter (·∣m)
  let D := I.filter (fun d => ¬d∣m)
  have good : ∑ d∈G,term M a Y V d = ∑ d∈G,term m (a%m) Y V d := by
    apply sum_congr rfl
    intro d hd
    obtain ⟨hi,hd'⟩ := mem_filter.mp hd
    have hd2 := (mem_Icc.mp hi).1
    unfold term
    rw [residue_captured hM2 ha hc hd2 hP (hd'.trans hdiv),
      residue_captured hm2 (Nat.mod_lt _ hm) hau hd2 (hdiv.trans hP) hd']
    have H := ThetaRowCorrelations.row_onMod d (V.width d)
    rw [←H (a%m),Nat.mod_mod_of_dvd _ hd',H]
  have hsplit (M a : ℕ) : cond M a Y V= (∑ d∈G,term M a Y V d)+(∑ d∈D,term M a Y V d) :=
    (expand ..).trans (sum_filter_add_sum_filter_not I (·∣m) _).symm
  have h₁ := error hM2 (by omega : 0<T) hdiv hs hl ha hc hP V
  have h₂ := error hm2 (by omega : 0<T) (dvd_refl m) (fun _ h => ThetaCompactModulus.smooth h) hl
    (Nat.mod_lt a hm) hau (hdiv.trans hP) V
  rw [hsplit M a,hsplit m (a%m),good,add_sub_add_left_eq_sub]
  exact (abs_sub ..).trans ((add_le_add h₁ h₂).trans_eq (by ring))

#print axioms difference
#print axioms omitted
#print axioms error
end
end Arxiv.«2501.03234».ThetaSmoothRefinement
