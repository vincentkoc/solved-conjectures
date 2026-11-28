import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Tactic

/-! Reciprocal divisor mass of a smooth modulus and its logarithmic moment. -/
namespace Arxiv.«2501.03234».ThetaDivisorLogMean
open Finset Real
noncomputable section

def mass (m : ℕ) : ℝ := ∑ g∈m.divisors, (g:ℝ)⁻¹
def logMass (m : ℕ) : ℝ := ∑ g∈m.divisors, (1+log g)/g

private theorem shift {m t : ℕ} (f : ℕ → ℝ) (hf : ∀ n,0≤f n) :
    ∑ g∈m.divisors.filter (t∣·),f (g/t) ≤ ∑ g∈m.divisors,f g := by
  classical
  let D := m.divisors.filter (t∣·)
  have hd {g : ℕ} (h : g∈D) : t∣g := (mem_filter.mp h).2
  have hi : Set.InjOn (fun g : ℕ => g/t) D := by
    intro x hx y hy h
    simpa only [Nat.div_mul_cancel (hd hx),Nat.div_mul_cancel (hd hy)] using congrArg (·*t) h
  have hsub : D.image (·/t) ⊆ m.divisors := by
    intro y hy
    obtain ⟨g,hg,rfl⟩ := mem_image.mp hy
    obtain ⟨hgm,hm⟩ := Nat.mem_divisors.mp (mem_filter.mp hg).1
    exact Nat.mem_divisors.mpr ⟨(Nat.div_dvd_of_dvd (hd hg)).trans hgm,hm⟩
  calc _ = ∑ g∈D.image (·/t),f g := (sum_image hi).symm
       _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hf i)

theorem multiple_mass {m t : ℕ} (ht : 0<t) :
    ∑ g∈m.divisors.filter (t∣·),(g:ℝ)⁻¹ ≤ mass m/t := by
  have h := shift (m:=m) (t:=t) (fun n => (n:ℝ)⁻¹) (fun n => inv_nonneg.mpr (Nat.cast_nonneg n))
  rw [le_div_iff₀ (by exact_mod_cast ht : 0<(t:ℝ)),sum_mul]
  refine le_trans (sum_le_sum fun g hg => le_of_eq ?_) h
  have hd := (mem_filter.mp hg).2
  have htg : (g:ℝ)=(g/t:ℕ)* (t:ℝ) := by exact_mod_cast (Nat.div_mul_cancel hd).symm
  rw [htg,mul_inv_rev]; field_simp

private theorem power_sum {p : ℕ} (hp : p.Prime) (N : ℕ) :
    ∑ i∈range N, ((p:ℝ)^(i+1))⁻¹ ≤ 1/(p-1:ℝ) := by
  have hp' : (1:ℝ)<p := by exact_mod_cast hp.one_lt
  have haux (n : ℕ) : (∑ i∈range n, ((p:ℝ)^(i+1))⁻¹)*(p-1) = 1-((p:ℝ)^n)⁻¹ := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ,add_mul,ih,pow_succ]
      field_simp [show (p:ℝ)≠0 by positivity]
      ring
  rw [le_div_iff₀ (by linarith),haux]; simp

theorem valuation {m p : ℕ} (hp : p.Prime) :
    ∑ g∈m.divisors,(g.factorization p:ℝ)/g ≤ mass m/(p-1:ℝ) := by
  classical
  let e := m.factorization p
  have layer (g : ℕ) (hg : g∈m.divisors) : (g.factorization p:ℝ)/g =
      ∑ i∈range e, if p^(i+1)∣g then (g:ℝ)⁻¹ else 0 := by
    have hg0 := (Nat.pos_of_mem_divisors hg).ne'
    have hm0 := (Nat.mem_divisors.mp hg).2
    have he : g.factorization p ≤ e := (Nat.factorization_le_iff_dvd hg0 hm0).mpr (Nat.mem_divisors.mp hg).1 p
    simp_rw [hp.pow_dvd_iff_le_factorization hg0, Nat.succ_le_iff]
    rw [←sum_filter]
    have hs : (range e).filter (·<g.factorization p)=range (g.factorization p) := by ext i; simp; omega
    rw [hs,sum_const,card_range,nsmul_eq_mul,div_eq_mul_inv]
  rw [sum_congr rfl layer,sum_comm]
  calc _ ≤ ∑ i∈range e,mass m/(p:ℝ)^(i+1) := by
            apply sum_le_sum; intro i hi
            simpa only [←sum_filter,Nat.cast_pow] using (multiple_mass (m:=m) (t:=p^(i+1)) (pow_pos hp.pos _))
       _ = mass m*∑ i∈range e, ((p:ℝ)^(i+1))⁻¹ := by simp only [mul_sum,div_eq_mul_inv]
       _ ≤ _ := by rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left (power_sum hp e) (sum_nonneg fun _ _ => by positivity)

private theorem log_nonneg_nat (g : ℕ) : 0≤log (g:ℝ) := by
  rcases g with _|g
  · simp
  · apply Real.log_nonneg; exact_mod_cast (Nat.succ_pos g)

theorem log_mass_multiple {m t : ℕ} (ht : 0<t) :
    ∑ g∈m.divisors.filter (t∣·), (1+log g)/g ≤ (logMass m + log t*mass m)/t := by
  have h := shift (m:=m) (t:=t) (fun n => (1+log n)/n + log t*(n:ℝ)⁻¹)
    (fun n => add_nonneg (div_nonneg (by linarith [log_nonneg_nat n]) (Nat.cast_nonneg _))
      (mul_nonneg (log_nonneg_nat t) (by positivity)))
  rw [le_div_iff₀ (by exact_mod_cast ht : 0<(t:ℝ)),sum_mul]
  unfold logMass mass
  rw [mul_sum,←sum_add_distrib]
  refine le_trans (sum_le_sum fun g hg => le_of_eq ?_) h
  have hd := (mem_filter.mp hg).2
  have hg0 := Nat.pos_of_mem_divisors (mem_filter.mp hg).1
  have hq : 0<g/t := Nat.div_pos (Nat.le_of_dvd hg0 hd) ht
  have htg : (g:ℝ)=((g/t:ℕ):ℝ)*t := by exact_mod_cast (Nat.div_mul_cancel hd).symm
  conv_lhs => rw [htg,Real.log_mul (by positivity) (by positivity)]
  field_simp; ring

/-- The logarithmic moment costs only two logarithms of the largest prime divisor. -/
theorem smooth {m T : ℕ} (hm : 0<m)
    (hs : ∀ p∈m.primeFactors,p≤T) :
    logMass m ≤ mass m*(1+2*log T*(1+log T)) := by
  classical
  have v (g : ℕ) (hg : g∈m.divisors) : log (g:ℝ)=∑ p∈m.primeFactors,(g.factorization p:ℝ)*log p := by
    rw [Real.log_nat_eq_sum_factorization,Finsupp.sum]
    apply sum_subset_zero_on_sdiff
    · exact Nat.primeFactors_mono (Nat.mem_divisors.mp hg).1 hm.ne'
    · intro p hp
      have hn : p∉g.factorization.support := (mem_sdiff.mp hp).2
      simp [Finsupp.notMem_support_iff.mp hn]
    · intros; rfl
  have hD : 0≤mass m := sum_nonneg fun _ _ => by positivity
  have hex : logMass m=mass m+∑ p∈m.primeFactors,(∑ g∈m.divisors,(g.factorization p:ℝ)/g)*log p := by
    have hx (g : ℕ) (hg : g∈m.divisors) : (1+log g)/g = (g:ℝ)⁻¹ + ∑ p∈m.primeFactors,(g.factorization p:ℝ)/g*log p := by
      rw [add_div,one_div,v g hg,sum_div]; congr 1
      apply sum_congr rfl; intros; ring
    rw [logMass,sum_congr rfl hx,sum_add_distrib,sum_comm (s:=m.divisors) (t:=m.primeFactors)]
    simp only [mass,sum_mul]
  have hpr (p : ℕ) (hp : p∈m.primeFactors) : (1:ℝ)/(p-1:ℝ) ≤ 2/p := by
    have h : (2:ℝ)≤p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    rw [div_le_div_iff₀ (by linarith) (by linarith)]; linarith
  have hH : ∑ p∈m.primeFactors,(p:ℝ)⁻¹ ≤ (harmonic T:ℝ) := by
    simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp; exact mem_Icc.mpr ⟨(Nat.prime_of_mem_primeFactors hp).pos,hs p hp⟩
    · intros; positivity
  rw [hex]
  calc _ ≤ mass m+∑ p∈m.primeFactors,(mass m*2*log T)*(p:ℝ)⁻¹ := by
          apply add_le_add_right; apply sum_le_sum; intro p hp
          have hpos := (Nat.prime_of_mem_primeFactors hp).pos
          calc _ ≤ (mass m/(p-1:ℝ))*log p :=
                  mul_le_mul_of_nonneg_right (valuation (m:=m) (Nat.prime_of_mem_primeFactors hp)) (log_nonneg_nat p)
               _ ≤ (mass m*(2/p))*log T := by
                  rw [div_eq_mul_one_div (mass m)]
                  exact mul_le_mul (mul_le_mul_of_nonneg_left (hpr p hp) hD)
                    (Real.log_le_log (by positivity) (by exact_mod_cast hs p hp))
                    (log_nonneg_nat p) (mul_nonneg hD (by positivity))
               _ = _ := by ring
       _ = mass m+(mass m*2*log T)*∑ p∈m.primeFactors,(p:ℝ)⁻¹ := by rw [mul_sum]
       _ ≤ mass m+(mass m*2*log T)*(1+log T) := by
          gcongr
          exact hH.trans (harmonic_le_one_add_log T)
       _ = _ := by ring

theorem mass_nonneg (m : ℕ) : 0≤mass m := sum_nonneg fun _ _ => by positivity

theorem factorial_smooth {T A p : ℕ} (hp : p∈(T.factorial^A).primeFactors) : p≤T := by
  obtain ⟨hpp,hd,_⟩ := Nat.mem_primeFactors.mp hp
  exact (Nat.Prime.dvd_factorial hpp).mp (hpp.dvd_of_dvd_pow hd)

theorem factorial_mass {T A : ℕ} (hA : 0<A) : (harmonic T:ℝ) ≤ mass (T.factorial^A) := by
  simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
  apply sum_le_sum_of_subset_of_nonneg
  · intro g hg
    obtain ⟨h₁,h₂⟩ := mem_Icc.mp hg
    exact Nat.mem_divisors.mpr ⟨(Nat.dvd_factorial h₁ h₂).trans (dvd_pow_self _ hA.ne'),pow_ne_zero _ (Nat.factorial_ne_zero _)⟩
  · intros; positivity

/-- Odd nontrivial divisors capture at least half the reciprocal mass, minus one. -/
theorem odd_mass (m : ℕ) :
    mass m/2-1 ≤ ∑ g∈m.divisors.filter (fun g => Odd g ∧ 1<g), (g:ℝ)⁻¹ := by
  classical
  have h := multiple_mass (m:=m) (t:=2) (by decide)
  have hsplit := sum_filter_add_sum_filter_not m.divisors (2∣·) (fun g => (g:ℝ)⁻¹)
  have ho : ∑ g∈m.divisors.filter (fun g => ¬2∣g), (g:ℝ)⁻¹ ≤ 1+∑ g∈m.divisors.filter (fun g => Odd g ∧ 1<g), (g:ℝ)⁻¹ := by
    have hr := sum_filter_add_sum_filter_not (m.divisors.filter (fun g => ¬2∣g)) (·=1) (fun g => (g:ℝ)⁻¹)
    rw [←hr]
    apply add_le_add
    · apply le_trans (b:=∑ g∈({1}:Finset ℕ),(g:ℝ)⁻¹)
      · apply sum_le_sum_of_subset_of_nonneg
        · intro g hg; simpa using (mem_filter.mp hg).2
        · intros; positivity
      · simp
    · apply sum_le_sum_of_subset_of_nonneg
      · intro g hg
        obtain ⟨hg,h1⟩ := mem_filter.mp hg
        obtain ⟨hg,hn⟩ := mem_filter.mp hg
        exact mem_filter.mpr ⟨hg,by have := Nat.pos_of_mem_divisors hg; exact ⟨by simpa [Nat.odd_iff, Nat.dvd_iff_mod_eq_zero] using (by omega : g%2=1),by omega⟩⟩
      · intros; positivity
  change _+_=mass m at hsplit
  linarith

/-- A small prime in the reduced denominator forces maximal divisibility in the gcd. -/
theorem saturated {T A d : ℕ} {p : ℕ} (hp : p.Prime) (hpT : p≤T)
    (hps : p∣d/((T.factorial^A).gcd d)) : p^A∣(T.factorial^A).gcd d := by
  let m := T.factorial^A
  let g := m.gcd d
  have hm : 0<m := pow_pos (Nat.factorial_pos _) _
  have hg : 0<g := Nat.gcd_pos_of_pos_left _ hm
  have he : g*(m/g)=m := Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
  have hc : (m/g).Coprime (d/g) := Nat.coprime_div_gcd_div_gcd hg
  have hn : ¬p∣m/g := fun h => hp.not_dvd_one (hc ▸ Nat.dvd_gcd h hps)
  have hb : p^A∣g*(m/g) := he.symm ▸ pow_dvd_pow_of_dvd (Nat.dvd_factorial hp.pos hpT) A
  exact ((hp.coprime_iff_not_dvd.mpr hn).pow_left _).dvd_of_dvd_mul_right hb

#print axioms odd_mass
#print axioms saturated

#print axioms log_mass_multiple
#print axioms smooth

#print axioms valuation
end
end Arxiv.«2501.03234».ThetaDivisorLogMean
