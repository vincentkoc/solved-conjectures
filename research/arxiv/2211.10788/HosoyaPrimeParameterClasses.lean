import LucasFibonacciPrimePowerLifts

/-! Prime parameters for a prescribed divisor on an affine upper diagonal. -/

namespace Arxiv.«2211.10788»

private lemma index_rank_spec (m d : ℕ) [NeZero m] :
    0 < fibonacciStepRank m d ∧ m ∣ Nat.fib (d * fibonacciStepRank m d) := by
  unfold fibonacciStepRank
  exact Nat.find_spec (p := fun t => 0 < t ∧ m ∣ Nat.fib (d*t)) _

/-- A single hit, at any parameter s, determines divisibility on the whole
progression, including the part before s. -/
theorem upper_divisor_parameter_class {m r d s : ℕ} [NeZero m]
    (hs : m ∣ lucasFibonacciSum (r+d*s)) (t : ℕ) :
    m ∣ lucasFibonacciSum (r+d*t) ↔ t ≡ s [MOD fibonacciStepRank m d] := by
  let e := fibonacciStepRank m d
  obtain ⟨he,hf⟩ := index_rank_spec m d
  have per : Function.Periodic (fun n => m ∣ lucasFibonacciSum (r+d*n)) e := by
    intro n
    apply propext
    simpa only [Nat.mul_add,← Nat.add_assoc] using
      (lucasFibonacciSum_dvd_shift_iff (s:=r+d*n) hf)
  let w := t+s*e
  have hsw : s ≤ w := by
    have h := Nat.mul_le_mul_left s he
    dsimp [w,e]
    omega
  have shift : (m ∣ lucasFibonacciSum (r+d*w)) = (m ∣ lucasFibonacciSum (r+d*t)) :=
    per.nat_mul s t
  have delta : r+d*w = (r+d*s)+d*(w-s) := by
    conv_lhs => rw [show w=s+(w-s) by omega]
    ring
  have hwt : w ≡ t [MOD e] := by simp [w,Nat.ModEq]
  rw [←shift,delta,lucasFibonacciSum_dvd_after_hit_iff hs,←Nat.modEq_iff_dvd' hsw]
  exact ⟨fun h => (h.trans hwt).symm, fun h => h.symm.trans hwt.symm⟩

/-- If the hit class has a nontrivial common divisor with the return rank,
the gcd is the only possible prime parameter. -/
theorem upper_singular_prime_parameter {m r d s q : ℕ} [NeZero m]
    (hs : m ∣ lucasFibonacciSum (r+d*s)) (hn : ¬ s.Coprime (fibonacciStepRank m d))
    (hq : q.Prime) (hit : m ∣ lucasFibonacciSum (r+d*q)) :
    q = s.gcd (fibonacciStepRank m d) := by
  have he := ((upper_divisor_parameter_class hs q).mp hit).gcd_eq
  have hv := Nat.gcd_dvd_left q (fibonacciStepRank m d)
  rw [he] at hv
  exact ((hq.eq_one_or_self_of_dvd _ hv).resolve_left hn).symm


/-- The existing progression coefficient test, including the two exceptional
primes, written without an existentially quantified index. -/
def UpperProgressionFactor (p r d : ℕ) [NeZero p] : Prop :=
  if p=5 then ¬5 ∣ d ∨ r%5=2
  else p≠11 ∧ p ∣ progressionPowerCoefficient r (fibonacciStepRank p d)

/-- Test the initial progression and the subprogression of multiples of each
prime divisor of its rank. -/
def UpperPrimeParameterTest (p r d : ℕ) [NeZero p] : Prop :=
  UpperProgressionFactor p r d ∧ ∀ l ∈ (fibonacciStepRank p d).primeFactors,
    ¬ UpperProgressionFactor p r (d*l)

private lemma progression_test_iff {p : ℕ} [Fact p.Prime] (r d : ℕ) :
    UpperProgressionFactor p r d ↔ ∃ t, p ∣ lucasFibonacciSum (r+d*t) :=
  (prime_dvd_lucasFibonacciSum_on_progression_iff r d).symm

/-- A divisor occurs at infinitely many prime parameters precisely when
any one hit is coprime to its return rank. -/
theorem upper_prime_parameters_infinite_iff {m r d s : ℕ} [NeZero m]
    (hs : m ∣ lucasFibonacciSum (r+d*s)) :
    {q : ℕ | q.Prime ∧ m ∣ lucasFibonacciSum (r+d*q)}.Infinite ↔
      s.Coprime (fibonacciStepRank m d) := by
  constructor
  · intro hi
    by_contra bad
    apply hi
    apply (Set.finite_singleton (s.gcd (fibonacciStepRank m d))).subset
    intro q h
    exact upper_singular_prime_parameter hs bad h.1 h.2
  · intro hc
    simpa only [upper_divisor_parameter_class hs] using
      Nat.infinite_setOfPred_prime_and_modEq (index_rank_spec m d).1.ne' hc

private lemma prime_test_at_hit {p r d s : ℕ} [Fact p.Prime]
    (hs : p ∣ lucasFibonacciSum (r+d*s)) :
    UpperPrimeParameterTest p r d ↔ s.Coprime (fibonacciStepRank p d) := by
  let e := fibonacciStepRank p d
  have he := (index_rank_spec p d).1.ne'
  have subhit {l : ℕ} (hl : l ∣ e) :
      UpperProgressionFactor p r (d*l) ↔ l ∣ s := by
    rw [progression_test_iff]
    constructor
    · rintro ⟨t,h⟩
      rw [Nat.mul_assoc] at h
      exact (((upper_divisor_parameter_class hs (l*t)).mp h).dvd_iff hl).mp (dvd_mul_right ..)
    · rintro ⟨t,rfl⟩
      exact ⟨t, by simpa only [Nat.mul_assoc] using hs⟩
  constructor
  · rintro ⟨_,h⟩
    by_contra hn
    obtain ⟨l,hp,hs',he'⟩ := Nat.Prime.not_coprime_iff_dvd.mp hn
    exact h l (Nat.mem_primeFactors.mpr ⟨hp,he',he⟩) ((subhit he').mpr hs')
  · intro hu
    refine ⟨(progression_test_iff r d).mpr ⟨s,hs⟩,?_⟩
    intro l hl h
    obtain ⟨hp,he',_⟩ := Nat.mem_primeFactors.mp hl
    exact (Nat.Prime.not_coprime_iff_dvd.mpr ⟨l,hp,(subhit he').mp h,he'⟩) hu

/-- A finite coefficient test decides recurrence at prime parameters for every
prime divisor, offset and step. A failed test allows at most one prime hit. -/
theorem upper_prime_parameter_test_iff {p : ℕ} [Fact p.Prime] (r d : ℕ) :
    UpperPrimeParameterTest p r d ↔
      {q : ℕ | q.Prime ∧ p ∣ lucasFibonacciSum (r+d*q)}.Infinite := by
  constructor
  · intro h
    obtain ⟨s,hs⟩ := (progression_test_iff r d).mp h.1
    exact (upper_prime_parameters_infinite_iff hs).mpr ((prime_test_at_hit hs).mp h)
  · intro hi
    obtain ⟨s,hs⟩ := hi.nonempty
    exact (prime_test_at_hit hs.2).mpr ((upper_prime_parameters_infinite_iff hs.2).mp hi)


private theorem rank_factor_stride {m d l : ℕ} [NeZero m] (hl : l ∣ fibonacciStepRank m d) :
    fibonacciStepRank m (d*l) = fibonacciStepRank m d / l := by
  let e := fibonacciStepRank m d
  let k := e/l
  obtain ⟨he,hF⟩ := index_rank_spec m d
  have hp := Nat.pos_of_dvd_of_pos hl he
  have eq : l*k=e := Nat.mul_div_cancel' hl
  have hk : 0<k := Nat.div_pos (Nat.le_of_dvd he hl) hp
  unfold fibonacciStepRank
  apply (Nat.find_eq_iff _).mpr
  refine ⟨⟨hk, by change m ∣ Nat.fib (d*l*k); rwa [Nat.mul_assoc,eq]⟩, ?_⟩
  intro t ht ht'
  have hmin : e ≤ l*t := Nat.find_min' _ ⟨Nat.mul_pos hp ht'.1,by simpa [Nat.mul_assoc] using ht'.2⟩
  exact (Nat.mul_lt_mul_of_pos_left (show t<k from ht) hp).not_ge (eq ▸ hmin)

/-- At an ordinary prime only the rank e and the powers e/l at its distinct
prime factors need testing. No index logarithm is needed. -/
theorem upper_prime_index_order_test {p : ℕ} [Fact p.Prime] (h5 : p≠5) (h11 : p≠11)
    (r d : ℕ) :
    {q : ℕ | q.Prime ∧ p ∣ lucasFibonacciSum (r+d*q)}.Infinite ↔
      p ∣ progressionPowerCoefficient r (fibonacciStepRank p d) ∧
      ∀ l ∈ (fibonacciStepRank p d).primeFactors,
        ¬ p ∣ progressionPowerCoefficient r (fibonacciStepRank p d/l) := by
  rw [←upper_prime_parameter_test_iff]
  simp only [UpperPrimeParameterTest,UpperProgressionFactor,if_neg h5,and_iff_right h11]
  apply and_congr_right
  intro _
  exact forall_congr' (fun l => forall_congr' fun hl =>
    by rw [rank_factor_stride (Nat.mem_primeFactors.mp hl).2.1])

#print axioms upper_prime_index_order_test

#print axioms upper_prime_parameters_infinite_iff
#print axioms upper_prime_parameter_test_iff

#print axioms upper_divisor_parameter_class
#print axioms upper_singular_prime_parameter

end Arxiv.«2211.10788»
