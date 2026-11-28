import ThetaCompactModulus
import ThetaFactorialRows

/-! Uniform off-divisor bound for the fourth power of the least common multiple. -/
namespace Arxiv.«2501.03234».ThetaCompactOmitted
open Finset Real ThetaDivisorLogMean ThetaFactorialRows ThetaSmoothRows ThetaCompactModulus
noncomputable section

def cover (T : ℕ) := (Icc 2 T).biUnion fun p => (modulus T).divisors.filter (block T p∣·)

theorem cover_mass {T : ℕ} (hT : 0<T) :
    ∑ g∈cover T,logWeight g ≤
      (logMass (modulus T)+4*log T*mass (modulus T))/T := by
  classical
  let m := modulus T
  let f (p g : ℕ) := if g∈m.divisors ∧ block T p∣g then logWeight g else 0
  have hn (p g : ℕ) : 0≤ f p g := by dsimp [f]; split <;> simp [logWeight_nonneg]
  have hm₀ := mass_nonneg m
  have hm₁ : 0≤ logMass m := sum_nonneg fun g _ => logWeight_nonneg g
  have hl := log_nonneg_nat T
  have hR : 0<(T:ℝ) := by exact_mod_cast hT
  let U := logMass m+4*log T*mass m
  have hU : 0≤U := by dsimp [U]; positivity
  have hsub : cover T ⊆ m.divisors := by
    intro g hg; obtain ⟨p,_,h⟩ := mem_biUnion.mp hg; exact (mem_filter.mp h).1
  have hp (p : ℕ) (hp : p∈Icc 2 T) : ∑ g∈cover T,f p g ≤ U/(T:ℝ)^2 := by
    obtain ⟨h2,ht⟩ := mem_Icc.mp hp
    obtain ⟨hb₁,hb₂⟩ := block_bounds h2 ht
    have hb : 0<block T p := (pow_pos hT 2).trans_le hb₁
    have hlog := log_le_log (by exact_mod_cast hb) (by exact_mod_cast hb₂ : (block T p:ℝ)≤(T:ℝ)^4)
    rw [log_pow] at hlog
    calc _ ≤ ∑ g∈m.divisors,f p g := sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hn p i)
         _ = ∑ g∈m.divisors.filter (block T p∣·),logWeight g := by
              rw [sum_filter]; apply sum_congr rfl; intro g hg; simp only [f,hg,true_and]
         _ ≤ _ := (log_mass_multiple (m:=m) hb).trans (by
              apply (div_le_div_of_nonneg_right (b:=U) _ (Nat.cast_nonneg _)).trans
              · exact div_le_div_of_nonneg_left hU (by positivity) (by exact_mod_cast hb₁)
              · exact add_le_add_right (mul_le_mul_of_nonneg_right (by simpa using hlog) hm₀) _)
  calc _ ≤ ∑ g∈cover T,∑ p∈Icc 2 T,f p g := by
            apply sum_le_sum; intro g hg
            obtain ⟨p,hp,hh⟩ := mem_biUnion.mp hg
            change g∈m.divisors.filter (block T p∣·) at hh
            exact (show logWeight g=f p g by simp only [f,if_pos (mem_filter.mp hh)]).trans_le
              (single_le_sum (fun i _ => hn i g) hp)
       _ = ∑ p∈Icc 2 T,∑ g∈cover T,f p g := sum_comm
       _ ≤ (T:ℝ)*(U/(T:ℝ)^2) := by
            apply (sum_le_sum hp).trans
            rw [sum_const,nsmul_eq_mul,Nat.card_Icc]
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact_mod_cast (by omega : T+1-2≤T)
       _ = _ := by change _=U/T; field_simp

theorem omitted {T Y : ℕ} (hT : 0<T) (D : Finset ℕ)
    (hD : ∀ d∈D,0 < d ∧ d≤Y ∧ ¬d∣modulus T) :
    let m := modulus T
    ∑ d∈D,logWeight (m.gcd d)*tailWeight (d/(m.gcd d)) ≤
      logMass m*(zetaBound/(T:ℝ)^(1/16:ℝ))+((logMass m+4*log T*mass m)/T)*zetaBound := by
  let m := modulus T
  have H := omitted_cover (positive T) hT D (cover T) hD (fun d _ p hp hpT hpd =>
    mem_biUnion.mpr ⟨p,mem_Icc.mpr ⟨hp.two_le,hpT⟩,mem_filter.mpr
      ⟨Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left ..,(positive T).ne'⟩,ThetaCompactModulus.saturated hp hpT hpd⟩⟩)
  exact H.trans (add_le_add_right (mul_le_mul_of_nonneg_right (cover_mass hT)
    (tsum_nonneg fun _ => by positivity : 0≤zetaBound)) _)

#print axioms cover_mass
#print axioms omitted
end
end Arxiv.«2501.03234».ThetaCompactOmitted
