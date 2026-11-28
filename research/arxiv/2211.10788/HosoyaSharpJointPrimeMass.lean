import HosoyaJointPrimeMass
import HosoyaPrimeFibreExamples

/-! A fixed pair of target values attains the full exponent on prime parameters. -/

namespace Arxiv.«2211.10788».LocalPower.CompanionAffine

open ProgressionClosure AlmostPrimeClosure PrimeObstruction Filter Topology CunninghamChain.PrimeMass

private lemma divisible_return {p E a : ℕ} [Fact p.Prime] (ha : 2≤a)
    (base : p^a∣Nat.fib E) (sharp : ¬p^(a+1)∣Nat.fib E) (b : ℕ) :
    p^b∣Nat.fib (E*p^b) := by
  have hp : p.Prime := Fact.out
  let : NeZero (p^a) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let : NeZero (p^b*p^a) := ⟨Nat.mul_ne_zero (pow_ne_zero _ hp.ne_zero) (pow_ne_zero _ hp.ne_zero)⟩
  have eq := sharp_step_rank (p:=p) (by simpa [pow_two] using pow_dvd_pow p ha) base
    (by simpa [pow_succ'] using sharp) b
  exact (dvd_mul_right ..).trans ((fibonacciStepRank_dvd_iff (p^b*p^a) E (p^b)).mp (by rw [eq]))

private lemma constant_on_return {p E : ℕ} (even : Even E) (b : ℕ)
    (deep : p^b∣Nat.fib (E*p^b)) (r d t : ℕ) :
    Hit d r (p^b) (lucasFibonacciSum (r+d)) (1+(2*E*p^b)*t) := by
  let J := (E*p^b)*(d*t)
  have div := deep.trans (Nat.fib_dvd (E*p^b) J (dvd_mul_right ..))
  have je : Even J := (even.mul_right _).mul_right _
  have eq := midpoint_difference (r+d) J
  rw [je.neg_one_pow,one_mul] at eq
  unfold Hit
  push_cast
  rw [show r+d*(1+2*E*p^b*t)=r+d+2*J by dsimp [J]; ring]
  apply Int.ModEq.symm
  rw [Int.modEq_iff_dvd]
  exact eq ▸ (dvd_mul_of_dvd_left (by exact_mod_cast div : (p:ℤ)^b∣(Nat.fib J:ℤ)) _)

/-- The two fixed targets at parameter one already attain order p⁻ᵇ.
The lower bound applies to arbitrary offsets and steps; the same period
works for all the forms. -/
theorem joint_prime_mass_lower (p : ℕ) [Fact p.Prime] :
    ∃ C : ℝ, 0<C ∧ ∀ r d s f b : ℕ, ∀ᶠ x : ℝ in 𝓝[>] 1,
      C/(p:ℝ)^b ≤ (x-1)*mass (jointHits r d s f (p^b)
        (lucasFibonacciSum (r+d)) (lucasFibonacciSum (s+f))) x := by
  have hp : p.Prime := Fact.out
  let E := fibreReturn p 1
  let a := (Nat.fib E).factorization p
  have spec := fibreReturn_spec (p:=p) (d:=1) (by decide)
  simp only [one_mul] at spec
  obtain ⟨pos,even,_,ha,base,sharp⟩ := spec
  change 0<E at pos
  refine ⟨1/(4*(E:ℝ)),by positivity,fun r d s f b => ?_⟩
  let M := 2*E*p^b
  have mp : 0<M := Nat.mul_pos (by omega) (pow_pos hp.pos b)
  let : NeZero M := ⟨mp.ne'⟩
  have tp : 0<(M.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr mp
  have le : (M.totient:ℝ)≤2*E*(p:ℝ)^b := by exact_mod_cast Nat.totient_le M
  have low : 1/(4*(E:ℝ))/(p:ℝ)^b < (M.totient:ℝ)⁻¹ := by
    rw [div_div,←one_div]
    apply one_div_lt_one_div_of_lt tp
    exact le.trans_lt (by nlinarith [show 0<(E:ℝ)*(p:ℝ)^b from mul_pos (by exact_mod_cast pos) (pow_pos (by exact_mod_cast hp.pos) _)])
  have lim := mass_progression (1:ZMod M) isUnit_one
  have deep : p^b∣Nat.fib (E*p^b) := divisible_return ha base sharp b
  filter_upwards [lim.eventually_const_lt low,self_mem_nhdsWithin] with x lb hx
  change 1<x at hx
  have incl (n : ℕ) (pr : n.Prime) (hit : n∈{n : ℕ | (n:ZMod M)=1}) :
      n∈jointHits r d s f (p^b) (lucasFibonacciSum (r+d)) (lucasFibonacciSum (s+f)) := by
    have res : n%M=1 := by
      have eq := (ZMod.natCast_eq_natCast_iff n 1 M).mp (by simpa using hit)
      change n%M=1%M at eq
      rw [Nat.mod_eq_of_lt (by dsimp [M]; nlinarith [pow_pos hp.pos b] : 1<M)] at eq
      exact eq
    have idx : 1+M*(n/M)=n := by rw [←res]; exact Nat.mod_add_div ..
    exact ⟨⟨pr,idx ▸ constant_on_return even b deep r d (n/M)⟩,
      ⟨pr,idx ▸ constant_on_return even b deep s f (n/M)⟩⟩
  exact lb.le.trans (mul_le_mul_of_nonneg_left (prime_mass_mono incl hx) (sub_nonneg.mpr hx.le))

#print axioms joint_prime_mass_lower

/-- At p=13 the two neighboring maps each have square-root fibres on their
own, even though their joint fibres have full-rate decay. -/
theorem thirteen_neighboring_marginals :
    ¬UniformFibreRate 13 0 1 ∧ ¬UniformFibreRate 13 1 1 := by
  let : Fact (Nat.Prime 13) := ⟨by decide⟩
  refine ⟨fibre_rate_thirteen.1,fun reg => ?_⟩
  have hf : 13^2∣Nat.fib (1*182) ∧ ¬13^3∣Nat.fib (1*182) := by rw [←Nat.fastFib_eq]; decide +kernel
  apply (uniform_rate_iff_no_critical_phase (E:=182) (a:=2) (by decide)
    (by decide) (by decide) (by decide) hf.1 hf.2).mp reg
  refine ⟨113,by decide,by decide,?_⟩
  change 13^2 ∣ (2*((2*Nat.fib 115+Nat.fib 117:ℕ):ℤ)-((2*Nat.fib 114+Nat.fib 116:ℕ):ℤ)).natAbs
  simp only [←Nat.fastFib_eq]
  decide +kernel

#print axioms thirteen_neighboring_marginals

end Arxiv.«2211.10788».LocalPower.CompanionAffine
