import ThetaDivisorLogMean
import ThetaSmoothRows

/-! Total off-divisor row envelope for a power of a factorial. -/
namespace Arxiv.«2501.03234».ThetaFactorialRows
open Finset ThetaDivisorLogMean ThetaSmoothRows
noncomputable section

def rare (m T A : ℕ) : Finset ℕ := (Icc 2 T).biUnion fun p => m.divisors.filter (p^A∣·)
def zetaBound : ℝ := ∑' n : ℕ, ((n:ℝ)^(9/8:ℝ))⁻¹

theorem rare_mass (m T A : ℕ) :
    ∑ g∈rare m T A,logWeight g ≤ T*((logMass m+A*Real.log T*mass m)/(2:ℝ)^A) := by
  classical
  let f (p g : ℕ) := if g∈m.divisors ∧ p^A∣g then logWeight g else 0
  have hn (p g : ℕ) : 0≤ f p g := by dsimp [f]; split <;> simp [logWeight_nonneg]
  have hsub : rare m T A ⊆ m.divisors := by
    intro g hg; obtain ⟨p,_,h⟩ := mem_biUnion.mp hg; exact (mem_filter.mp h).1
  have hp (p : ℕ) (hp : p∈Icc 2 T) : ∑ g∈rare m T A,f p g ≤
      (logMass m+A*Real.log T*mass m)/(2:ℝ)^A := by
    have h2 := (mem_Icc.mp hp).1
    have hT := (mem_Icc.mp hp).2
    have hp0 : 0< p^A := pow_pos (by omega) _
    have H := log_mass_multiple (m:=m) hp0
    rw [Nat.cast_pow,Real.log_pow] at H
    calc _ ≤ ∑ g∈m.divisors,f p g := sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hn p i)
         _ = ∑ g∈m.divisors.filter (p^A∣·),logWeight g := by
              rw [sum_filter]; apply sum_congr rfl; intro g hg; simp only [f,hg,true_and]
         _ ≤ _ := H.trans (by
              have hp' : (2:ℝ)≤ p := by exact_mod_cast h2
              have hlog := Real.log_le_log (by positivity : 0<(p:ℝ)) (by exact_mod_cast hT : (p:ℝ)≤ T)
              have hpos : 0≤ logMass m := sum_nonneg fun g _ => logWeight_nonneg g
              have hn' : 0≤ logMass m+(A:ℝ)*Real.log p*mass m := by
                have : 0≤ Real.log p := Real.log_nonneg (by linarith); positivity [mass_nonneg m]
              apply (div_le_div_of_nonneg_left hn' (by positivity) (pow_le_pow_left₀ (by norm_num) hp' A)).trans
              apply div_le_div_of_nonneg_right _ (by positivity)
              exact add_le_add_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _)) (mass_nonneg m)) _)
  calc _ ≤ ∑ g∈rare m T A,∑ p∈Icc 2 T,f p g := by
            apply sum_le_sum; intro g hg
            obtain ⟨p,hp,hh⟩ := mem_biUnion.mp hg
            exact (show logWeight g=f p g by simp only [f,if_pos (mem_filter.mp hh)]).trans_le (single_le_sum (fun i _ => hn i g) hp)
       _ = ∑ p∈Icc 2 T,∑ g∈rare m T A,f p g := sum_comm
       _ ≤ _ := by
           apply (sum_le_sum hp).trans
           rw [sum_const,nsmul_eq_mul,Nat.card_Icc]
           apply mul_le_mul_of_nonneg_right
           · exact_mod_cast (by omega : T+1-2≤ T)
           · have hpos : 0≤ logMass m := sum_nonneg fun g _ => logWeight_nonneg g
             have : 0≤ Real.log T := by rcases T with _|T; simp; exact Real.log_nonneg (by exact_mod_cast Nat.succ_pos T)
             positivity [mass_nonneg m]

theorem rectangle {m : ℕ} (D G S : Finset ℕ)
    (h : ∀ d∈D,m.gcd d∈G ∧ d/(m.gcd d)∈S) :
    ∑ d∈D, logWeight (m.gcd d)*tailWeight (d/(m.gcd d)) ≤
      (∑ g∈G,logWeight g)*(∑ s∈S,tailWeight s) := by
  classical
  let f (d : ℕ) := (m.gcd d,d/(m.gcd d))
  have hi : Set.InjOn f D := by
    intro x hx y hy he
    have H := congrArg (fun k : ℕ×ℕ => k.1*k.2) he
    simpa only [f,Nat.mul_div_cancel' (Nat.gcd_dvd_right ..)] using H
  have hsub : D.image f⊆G×ˢS := by
    intro k hk; obtain ⟨x,hx,rfl⟩ := mem_image.mp hk; exact mem_product.mpr (h x hx)
  let v (k : ℕ×ℕ) := logWeight k.1*tailWeight k.2
  calc _ = ∑ k∈D.image f,v k := (sum_image hi).symm
       _ ≤ ∑ k∈G×ˢS,v k := sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => mul_nonneg (logWeight_nonneg _) (by dsimp [tailWeight]; positivity))
       _ = _ := by rw [sum_product,mul_sum,sum_comm]; simp only [v,sum_mul]

/-- All omitted denominators are charged either to a large quotient or to a
divisor saturated by a prime power. Both bounds are uniform in the row cutoff. -/
theorem omitted {T A Y : ℕ} (hT : 0< T) (D : Finset ℕ)
    (hD : ∀ d∈D,0< d ∧ d≤ Y ∧ ¬d∣T.factorial^A) :
    let m := T.factorial^A
    ∑ d∈D, logWeight (m.gcd d)*tailWeight (d/(m.gcd d)) ≤
      logMass m*(zetaBound/(T:ℝ)^(1/16:ℝ))+
      (T*((logMass m+A*Real.log T*mass m)/(2:ℝ)^A))*zetaBound := by
  classical
  let m := T.factorial^A
  have hm : 0< m := pow_pos (Nat.factorial_pos _) _
  let s (d : ℕ) := d/(m.gcd d)
  have hpos {d : ℕ} (hd : d∈D) : 0< s d := Nat.div_pos (Nat.le_of_dvd (hD d hd).1 (Nat.gcd_dvd_right _ _)) (Nat.gcd_pos_of_pos_left _ hm)
  have hu {d : ℕ} (hd : d∈D) : s d≤ Y := (Nat.div_le_self ..).trans (hD d hd).2.1
  let big := D.filter (T≤ s ·)
  let small := D.filter (fun d => ¬T≤ s d)
  have hb := rectangle (m:=m) big m.divisors (Icc T Y) (by
    intro d hd; obtain ⟨h,h'⟩ := mem_filter.mp hd
    exact ⟨Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left ..,hm.ne'⟩,mem_Icc.mpr ⟨h',hu h⟩⟩)
  have hs := rectangle (m:=m) small (rare m T A) (Icc 1 Y) (by
    intro d hd; obtain ⟨h,h'⟩ := mem_filter.mp hd
    have hs1 : s d≠1 := by
      intro he
      have hh := Nat.mul_div_cancel' (Nat.gcd_dvd_right m d)
      change m.gcd d*s d=d at hh
      rw [he,mul_one] at hh
      exact (hD d h).2.2 (hh ▸ Nat.gcd_dvd_left ..)
    let p := (s d).minFac
    have hp := Nat.minFac_prime hs1
    have hpd := Nat.minFac_dvd (s d)
    have hpT : p≤ T := (Nat.le_of_dvd (hpos h) hpd).trans (by omega)
    exact ⟨mem_biUnion.mpr ⟨p,mem_Icc.mpr ⟨hp.two_le,hpT⟩,
      mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left ..,hm.ne'⟩,saturated hp hpT hpd⟩⟩,mem_Icc.mpr ⟨hpos h,hu h⟩⟩)
  have hbig := tail hT (Icc T Y) (fun _ h => (mem_Icc.mp h).1)
  have hsmall := tail (Q:=1) (by decide) (Icc 1 Y) (fun _ h => (mem_Icc.mp h).1)
  norm_num only [Nat.cast_one,Real.one_rpow,div_one] at hsmall
  change _ ≤ logMass m*_+_
  rw [←sum_filter_add_sum_filter_not D (T≤ s ·)]
  exact add_le_add (hb.trans (mul_le_mul_of_nonneg_left hbig (sum_nonneg fun i _ => logWeight_nonneg i)))
    (hs.trans (mul_le_mul (rare_mass m T A) hsmall (sum_nonneg fun i _ => by dsimp [tailWeight]; positivity)
      (by have hlog : 0≤ logMass m := sum_nonneg fun i _ => logWeight_nonneg i
          have := Real.log_nonneg (by exact_mod_cast hT : (1:ℝ)≤ T)
          positivity [mass_nonneg m])))
#print axioms rare_mass
#print axioms omitted
end
end Arxiv.«2501.03234».ThetaFactorialRows
