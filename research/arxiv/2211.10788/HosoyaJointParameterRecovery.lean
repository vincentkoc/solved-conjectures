import HosoyaAffineCompanionBounds
import HosoyaPrimeFibreCriterion

/-! A pair of distinct affine Hosoya indices recovers the fine parameter residue
on every phase, uniformly in both values. -/

namespace Arxiv.«2211.10788».LocalPower.CompanionAffine

private abbrev V (n : ℕ) : ℤ := lucasFibonacciSum n

private lemma deep_return (p K : ℕ) [Fact p.Prime] :
    ∃ E>0, Even E ∧ p∣E ∧ p^K∣Nat.fib E := by
  have hp : p.Prime := Fact.out
  let m := p^K
  let : NeZero m := ⟨pow_ne_zero _ hp.ne_zero⟩
  let T := fibonacciStepRank m 1
  have tp : 0<T := (Nat.find_spec (p:=fun n => 0<n ∧ m∣Nat.fib (1*n)) _).1
  refine ⟨2*p*T,Nat.mul_pos (Nat.mul_pos (by decide) hp.pos) tp,even_iff_two_dvd.mpr (by simp [Nat.mul_assoc]),(dvd_mul_left p 2).trans (dvd_mul_right ..),?_⟩
  simpa using (fibonacciStepRank_dvd_iff m 1 (2*p*T)).mp (dvd_mul_left T _)

private lemma recover_phase {p r d E K A i : ℕ} [Fact p.Prime] (hd : 0<d)
    (pos : 0<E) (even : Even E) (large : 2≤K) (base : p^K∣Nat.fib E)
    (ord : (Nat.fib (d*E)).factorization p≤A)
    (reg : ¬p^K∣(coordinate (r+d*i)).natAbs) (b t u : ℕ)
    (eq : V (r+d*(i+2*E*t)) ≡ V (r+d*(i+2*E*u)) [ZMOD (p:ℤ)^(2*A+b)]) :
    t ≡ u [MOD p^b] := by
  have hp : p.Prime := Fact.out
  let j := d*E
  let a := (Nat.fib j).factorization p
  let s := r+d*i
  let v := (coordinate s).natAbs.factorization p
  have nz : Nat.fib j ≠ 0 := (Nat.fib_pos.mpr (Nat.mul_pos hd pos)).ne'
  have ka : K≤a := (hp.pow_dvd_iff_le_factorization nz).mp (base.trans (Nat.fib_dvd E j (dvd_mul_left ..)))
  have hf : p^a∣Nat.fib j := Nat.ordProj_dvd ..
  have nr : ¬p^a∣(coordinate s).natAbs := fun h => reg ((pow_dvd_pow p ka).trans h)
  have va : v<a := lt_of_not_ge fun h => nr ((hp.pow_dvd_iff_le_factorization
    (Int.natAbs_ne_zero.mpr (coordinate_pos s).ne')).mpr h)
  have sharp := Nat.pow_succ_factorization_not_dvd nz hp
  have iso := midpoint_class_congruence hp (even.mul_left d) (large.trans ka) hf sharp
    (regular_companion_order hp hf nr) b t u
  apply iso.mp
  have alg (z) : r+d*(i+2*E*z)=s+2*j*z := by dsimp [s,j];ring
  rw [alg,alg] at eq
  have ub : a≤A := ord
  exact eq.of_dvd (pow_dvd_pow (p:ℤ) (show a+v+b≤2*A+b by omega))

/-- On each base phase, a common pair of targets at precision H+b determines
the parameter to b further digits. The phase and precision work for every
target and every natural parameter. -/
theorem joint_phase_recovery (p r d s f : ℕ) [Fact p.Prime]
    (hd : 0<d) (hf : 0<f) (distinct : (r,d)≠(s,f)) :
    ∃ P>0, p∣P ∧ ∃ H, ∀ i b t u,
      (lucasFibonacciSum (r+d*(i+P*t)):ℤ) ≡ (lucasFibonacciSum (r+d*(i+P*u)):ℤ) [ZMOD (p:ℤ)^(H+b)] →
      (lucasFibonacciSum (s+f*(i+P*t)):ℤ) ≡ (lucasFibonacciSum (s+f*(i+P*u)):ℤ) [ZMOD (p:ℤ)^(H+b)] →
      t ≡ u [MOD p^b] := by
  have hp : p.Prime := Fact.out
  obtain ⟨M,mp,bound⟩ := affine_companion_gcd_bound r d s f distinct
  let K := M+2
  obtain ⟨E,pos,even,ep,base⟩ := deep_return p K
  let A := max ((Nat.fib (d*E)).factorization p) ((Nat.fib (f*E)).factorization p)
  refine ⟨2*E,by omega,ep.trans (dvd_mul_left ..),2*A,fun i b t u left right => ?_⟩
  by_cases reg : p^K∣(coordinate (r+d*i)).natAbs
  · have other : ¬p^K∣(coordinate (s+f*i)).natAbs := by
      intro both
      have le := Nat.le_of_dvd mp ((Nat.dvd_gcd reg both).trans (bound i))
      have big : M < p^K := (Nat.lt_pow_self hp.one_lt).trans_le
        (Nat.pow_le_pow_right hp.pos (show M≤K by dsimp [K];omega))
      omega
    exact recover_phase hf pos even (by dsimp [K];omega) base (le_max_right ..) other b t u right
  · exact recover_phase hd pos even (by dsimp [K];omega) base (le_max_left ..) reg b t u left

#print axioms joint_phase_recovery

end Arxiv.«2211.10788».LocalPower.CompanionAffine
