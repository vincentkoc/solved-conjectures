import ThetaIdentityModulus
import ThetaPrimeTailTransfer

/-! Congruence classes with uniformly large finite theta models. -/
namespace Arxiv.«2501.03234».ThetaIdentityModels
open Finset Filter ThetaRowCorrelations ThetaIdentityFiber ThetaDivisorLogMean ThetaSmoothRows
open ThetaPeriodMeans ThetaConditionalRows ThetaReciprocalBlocks ThetaPrimeTailTransfer
open ThetaPrimeMeanSquare ThetaReciprocalInversion
open scoped Topology
noncomputable section

def Z : ℝ := ∑' g : ℕ,((g:ℝ)^2)⁻¹
theorem weight_one {d Y : ℕ} (hd : 0< d) (hY : d≤ Y) : 1≤ commonWeight Y d := by
  have h : 1∈(Icc 1 (Y/d)).filter (·%2=1) := mem_filter.mpr ⟨mem_Icc.mpr ⟨le_rfl,Nat.div_pos hY hd⟩,by decide⟩
  unfold commonWeight
  calc (1:ℝ) = (((1:ℕ):ℝ)^2)⁻¹ := by norm_num
       _ ≤ _ := single_le_sum (f:=fun g : ℕ => ((g:ℝ)^2)⁻¹) (fun _ _ => by positivity) h

/-- A lower bound for the captured odd rows, less a uniform bound on the rest. -/
theorem budget {m Y V : ℕ} (hm2 : 2≤ m) (hY : m≤ Y) (hV : m≤ V)
    (f : ℕ → ℝ) (hf : ∀ d,0≤ f d)
    (hr : ∀ d, 1< d → Odd d → d∣m → f d≤ row d (coneWindow (coneWidth V) d) 1)
    {E : ℝ} (hBad : ∀ D : Finset ℕ, (∀ d∈D, 0< d ∧ d≤ Y ∧ ¬d∣m) →
      (1080*Z)*∑ d∈D,logWeight (m.gcd d)*tailWeight (d/(m.gcd d)) ≤ E) :
    letI : NeZero Y.factorial := ⟨Nat.factorial_ne_zero _⟩
    (∑ d∈m.divisors.filter (fun d => Odd d ∧ 1< d), f d/d) - E ≤
      m.totient*unitMean Y.factorial (fun n => select m n*model Y V n) := by
  classical
  have hZ : 0≤ Z := tsum_nonneg fun _ => by positivity
  let P := Y.factorial
  let : NeZero P := ⟨Nat.factorial_ne_zero _⟩
  have hmP : m∣P := Nat.dvd_factorial (by omega) hY
  let K := coneWindow (coneWidth V)
  let a := commonWeight (2*V^52)
  let u (d : ℕ) := a d/d*rowMean m d P (K d)
  let G := (Icc 2 Y).filter (·∣m)
  let D := (Icc 2 Y).filter (fun d => ¬d∣m)
  have hscale : (m.totient:ℝ)*unitMean P (fun n => select m n*model Y V n)=∑ d∈Icc 2 Y,u d := by
    change (m.totient:ℝ)*unitMean P (fun n => select m n*low Y K a n)=_
    rw [mean_low,mul_sum]
    apply sum_congr rfl; intro d _
    unfold u rowMean a K; ring
  rw [hscale,←sum_filter_add_sum_filter_not (Icc 2 Y) (·∣m)]
  have hg (d : ℕ) (hd : d∈G) : (if Odd d then f d/d else 0) ≤ u d := by
    obtain ⟨hd,hdiv⟩ := mem_filter.mp hd
    have hd2 := (mem_Icc.mp hd).1
    dsimp only [u]
    rw [captured hm2 hd2 hmP hdiv]
    split_ifs with ho
    · have H := hr d hd2 ho hdiv
      have hle := Nat.le_of_dvd (by omega : 0< m) hdiv
      have hpow : V≤ V^52 := Nat.le_self_pow (by decide) V
      have hw : 1≤ a d := weight_one (by omega) (by omega)
      calc _ = (1/(d:ℝ))*f d := by ring
           _ ≤ _ := mul_le_mul (div_le_div_of_nonneg_right hw (by positivity)) H (hf d) (by positivity [hw])
    · simp [even_row ho]
  have good : (∑ d∈m.divisors.filter (fun d => Odd d ∧ 1< d), f d/d) ≤ ∑ d∈G,u d := by
    apply le_trans _ (sum_le_sum hg)
    rw [←sum_filter]
    apply le_of_eq; apply sum_congr _ (fun _ _ => rfl)
    ext d
    simp only [G,mem_filter,mem_Icc,Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hd,_⟩,ho,hl⟩
      exact ⟨⟨⟨hl,(Nat.le_of_dvd (by omega : 0< m) hd).trans hY⟩,hd⟩,ho⟩
    · rintro ⟨⟨⟨hl,_⟩,hd⟩,ho⟩; exact ⟨⟨hd,by omega⟩,ho,hl⟩
  have hu (d : ℕ) (hd : d∈D) : -u d ≤ (1080*Z)*(logWeight (m.gcd d)*tailWeight (d/(m.gcd d))) := by
    have hd2 := (mem_Icc.mp (mem_filter.mp hd).1).1
    have hdP : d∣P := Nat.dvd_factorial (by omega) (mem_Icc.mp (mem_filter.mp hd).1).2
    have H := envelope hm2 hd2 hmP hdP (K d)
    obtain ⟨ha,ha'⟩ := commonWeight_bounds (2*V^52) d
    calc _ ≤ |u d| := neg_le_abs _
         _ = a d*(|rowMean m d P (K d)|/d) := by simp only [u,abs_mul,abs_div,abs_of_nonneg (show 0≤ a d from ha),abs_of_nonneg (Nat.cast_nonneg d : 0≤(d:ℝ))]; ring
         _ ≤ Z*(1080*logWeight (m.gcd d)*tailWeight (d/(m.gcd d))) :=
               mul_le_mul ha' H (by positivity) hZ
         _ = _ := by ring
  have hh := sum_le_sum hu
  rw [sum_neg_distrib,←mul_sum] at hh
  have herr := hBad D (fun d hd => by obtain ⟨hd,h⟩ := mem_filter.mp hd; obtain ⟨hl,hr⟩ := mem_Icc.mp hd; exact ⟨by omega,hr,h⟩)
  linarith

/-- An identity class with an arbitrarily large conditional mean at all later
denominator cutoffs and all sufficiently large window sizes. -/
theorem large (B : ℝ) : ∃ m : ℕ, 1 < m ∧ ∀ᶠ Y : ℕ in atTop, ∀ᶠ V : ℕ in atTop,
    letI : NeZero Y.factorial := ⟨(Nat.factorial_ne_zero _)⟩
    m∣Y.factorial ∧ B≤ m.totient*unitMean Y.factorial (fun n => select m n*model Y V n) := by
  classical
  have hZ : 0≤ Z := tsum_nonneg fun _ => by positivity
  obtain ⟨T,A,hT,hA,hMass,hBad⟩ := ThetaIdentityModulus.choose (8*(B+1)) (1080*Z) (by positivity)
  let m := T.factorial^A
  have hm2 : 2≤ m := by
    have h2 : 2∣m := (Nat.dvd_factorial (by decide : 0<2) hT).trans (dvd_pow_self _ hA.ne')
    exact Nat.le_of_dvd (pow_pos (Nat.factorial_pos _) _) h2
  refine ⟨m,hm2,?_⟩
  filter_upwards [eventually_ge_atTop m] with Y hY
  filter_upwards [eventually_ge_atTop m] with V hV
  have hmP : m∣Y.factorial := Nat.dvd_factorial (by omega) hY
  refine ⟨hmP,?_⟩
  have h := budget hm2 hY hV (fun _ => 1/2) (fun _ => by norm_num) (fun d hd ho _ => by
    apply ThetaIdentityRow.lower hd ho
    have hl : 1≤ coneWidth V := by dsimp [coneWidth]; omega
    have ht := Nat.mul_le_mul_right d hl
    simp only [coneWindow,if_neg (show d≠1 by omega)]; omega) (hBad Y)
  have ho := mul_le_mul_of_nonneg_left (odd_mass m) (by norm_num : (0:ℝ)≤1/2)
  simp only [mul_sum] at ho
  simp only [div_eq_mul_inv (1/2:ℝ)] at h
  change _ ≤ mass m at hMass
  linarith
#print axioms budget
#print axioms large
end
end Arxiv.«2501.03234».ThetaIdentityModels
