import ThetaRowProgressionDiscrepancy
import ThetaWindowFiniteMoments

/-! Finite signed moments of prime samples depend only on counts in moduli
up to the product of the row periods occurring in one term. -/
namespace Arxiv.«2501.03234».ThetaLocalPowerDiscrepancy
open Finset ThetaPeriodMeans ThetaConditionalRows ThetaRowProgressionDiscrepancy

/-- A periodic multiplier and a power of a sum of rows can be sampled from any
finite set with reduced-residue discrepancy. The shared period P may be large. -/
theorem mixed {Y P q : ℕ} [NeZero P] (hq : 0<q) (hqP : q∣P) (hYP : Y.factorial∣P)
    (g : ℕ → ℝ) {A : ℝ} (hg : OnMod q g) (hgBound : ∀ n, |g n|≤A)
    (f : ℕ → ℕ → ℝ) (s : Finset ℕ) (k : ℕ) {B M δ : ℝ} (hδ : 0≤δ) (hB : 0≤B)
    (hf : ∀ d∈Icc 1 Y, OnMod (q.lcm d) (f d)) (hb : ∀ d∈Icc 1 Y, ∀ n, |f d n|≤B)
    (hc : ∀ d : ℕ, 0<d → d≤q*Y^k → Classes s d M δ) :
    |(∑ n∈s,g n*(∑ d∈Icc 1 Y,f d n)^k)-
      M*unitMean P (fun n => g n*(∑ d∈Icc 1 Y,f d n)^k)|≤
      δ*q*A*(B*(Y:ℝ)^2)^k := by
  classical
  let D := ↥(Icc 1 Y)
  let period (v : Fin k → D) := univ.lcm (fun i => (v i).val)
  let term (v : Fin k → D) (n : ℕ) := g n*∏ i,f (v i).val n
  have hA := (abs_nonneg (g 0)).trans (hgBound 0)
  have hexp (n : ℕ) : g n*(∑ d∈Icc 1 Y,f d n)^k = ∑ v : Fin k → D,term v n := by
    have he : (∑ d∈Icc 1 Y,f d n)^k = ∑ v : Fin k → D,∏ i,f (v i).val n := by
      rw [← sum_attach]
      calc _ = ∏ _i : Fin k,∑ d : D,f d.val n := by simp [D]
           _ = _ := by simpa using prod_univ_sum (fun _i : Fin k => (univ:Finset D)) (fun _ d => f d.val n)
    rw [he,mul_sum]
  have hper (v : Fin k → D) : period v∣P := (Finset.lcm_dvd (fun i _ =>
    Nat.dvd_factorial (by have := (mem_Icc.mp (v i).property).1;omega) (mem_Icc.mp (v i).property).2)).trans hYP
  have hsize (v : Fin k → D) : period v≤Y^k := by
    have hpos : 0 < ∏ i,(v i).val := prod_pos (fun i _ => by have := (mem_Icc.mp (v i).property).1;omega)
    apply (Nat.le_of_dvd hpos (Finset.lcm_dvd (fun i _ => dvd_prod_of_mem (fun i => (v i).val) (mem_univ i)))).trans
    calc _ ≤ ∏ _i : Fin k,Y := prod_le_prod' (fun i _ => (mem_Icc.mp (v i).property).2)
         _ = _ := by simp
  have hmod (v : Fin k → D) : OnMod (q.lcm (period v)) (term v) := by
    intro n
    dsimp only [term]
    rw [onMod_lift (Nat.dvd_lcm_left ..) hg n]
    congr 1
    apply prod_congr rfl
    intro i _
    exact onMod_lift (Nat.lcm_dvd (Nat.dvd_lcm_left ..) ((dvd_lcm (f:=fun i => (v i).val) (mem_univ i)).trans (Nat.dvd_lcm_right ..))) (hf _ (v i).property) n
  have hbound (v : Fin k → D) (n : ℕ) : |term v n|≤A*B^k := by
    dsimp only [term]
    rw [abs_mul,abs_prod]
    apply mul_le_mul (hgBound n) _ (prod_nonneg (fun _ _ => abs_nonneg _)) hA
    simpa using prod_le_prod (s:=univ) (fun i _ => abs_nonneg (f (v i).val n))
      (fun i _ => hb _ (v i).property n)
  have hh (v : Fin k → D) :
      |(∑ n∈s,term v n)-M*unitMean P (term v)|≤δ*q*A*(Y:ℝ)^k*B^k := by
    let d := q.lcm (period v)
    have hdP : d∣P := Nat.lcm_dvd hqP (hper v)
    have hd : 0<d := Nat.pos_of_dvd_of_pos hdP (NeZero.pos P)
    let : NeZero d := ⟨hd.ne'⟩
    have hs : d≤q*Y^k :=
      (Nat.lcm_le_mul hq (Nat.pos_of_dvd_of_pos (hper v) (NeZero.pos P))).trans
        (Nat.mul_le_mul_left q (hsize v))
    rw [unitMean_lift hdP (hmod v)]
    apply (periodic (hc d hd hs) (hmod v)).trans
    have ht := sum_le_sum (s:=range d) (fun n _ => hbound v n)
    simp only [sum_const,card_range,nsmul_eq_mul] at ht
    calc _ ≤ ((d:ℝ)*(A*B^k))*δ := mul_le_mul_of_nonneg_right ht hδ
         _ ≤ ((q*(Y:ℝ)^k)*(A*B^k))*δ := by
               apply mul_le_mul_of_nonneg_right _ hδ
               apply mul_le_mul_of_nonneg_right _ (mul_nonneg hA (pow_nonneg hB _))
               exact_mod_cast hs
         _ = _ := by ring
  have hmean : (∑ v : Fin k → D,unitMean P (term v)) = unitMean P (fun n => ∑ v,term v n) := by
    simp only [unitMean,← sum_div];rw [sum_comm]
  simp_rw [hexp]
  rw [sum_comm,← hmean,mul_sum,← sum_sub_distrib]
  apply (abs_sum_le_sum_abs ..).trans ((sum_le_sum (s:=univ) (fun v _ => hh v)).trans ?_)
  simp only [sum_const,card_univ,Fintype.card_fun,Fintype.card_fin,nsmul_eq_mul,Nat.cast_pow]
  have hd : (Fintype.card D:ℝ)≤Y := by
    exact_mod_cast (show Fintype.card D≤Y by simp [D,Nat.card_Icc])
  apply (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hd k) (by positivity)).trans_eq
  rw [mul_pow,show ((Y:ℝ)^2)^k=(Y:ℝ)^k*(Y:ℝ)^k by rw [pow_two,mul_pow]]
  ring

#print axioms mixed
end Arxiv.«2501.03234».ThetaLocalPowerDiscrepancy
