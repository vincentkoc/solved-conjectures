import HosoyaPrimeCofactorRealization
import HosoyaLeastReturnModulus
import LucasFibonacciIndexCoprimeDensity

/-! A finite decision procedure for the exact common divisor of index and upper value. -/

namespace Arxiv.«2211.10788».IndexDivisors

/-- Smallest positive multiple of m and d which divides its own Fibonacci number,
for positive inputs. Zero inputs give the fallback modulus one. -/
def spectrumModulus (m d : ℕ) : ℕ :=
  if h : 0 < m.lcm d then firstSelfMultiple (m.lcm d) h else 1

private lemma spectrum_modulus_spec {m d : ℕ} (hm : 0 < m) (hd : 0 < d) :
    0 < spectrumModulus m d ∧ m ∣ spectrumModulus m d ∧ d ∣ spectrumModulus m d ∧
      spectrumModulus m d ∣ Nat.fib (spectrumModulus m d) := by
  have h := Nat.lcm_pos hm hd
  obtain ⟨pos,dv,ret⟩ := firstSelfMultiple_spec h
  simpa only [spectrumModulus,dif_pos h] using
    And.intro pos ⟨(Nat.dvd_lcm_left m d).trans dv,(Nat.dvd_lcm_right m d).trans dv,ret⟩

/-- A finite table at any common return modulus decides whether an exact gcd occurs
anywhere on an index progression. -/
theorem exact_gcd_iff_at_return {m d A : ℕ} (hA : 0<A) (hm : m ∣ A) (hd : d ∣ A)
    (ret : A ∣ Nat.fib A) (a : ℕ) :
    (∃ n, 0<n ∧ n ≡ a [MOD m] ∧ n.gcd (lucasFibonacciSum n)=d) ↔
      ∃ t : Fin A, t.val ≡ a [MOD m] ∧ residueGcd A t.val=d := by
  constructor
  · rintro ⟨n,_,cl,eq⟩
    refine ⟨⟨n%A,Nat.mod_lt _ hA⟩,((Nat.mod_modEq n A).of_dvd hm).trans cl,?_⟩
    rw [residueGcd_mod ret,eq,Nat.gcd_eq_right hd]
  · rintro ⟨t,cl,eq⟩
    obtain ⟨q,_,hq,hit,val⟩ := prime_realizes_residue_gcd hA ret t.val 0
    exact ⟨_,Nat.mul_pos (Nat.gcd_pos_of_pos_right _ hA) hq.pos,(hit.of_dvd hm).trans cl,val.trans eq⟩

def fastResidueGcd (A t : ℕ) : ℕ :=
  let pair := Nat.fastFibAux t
  (t.gcd A).gcd (3*pair.1+pair.2)

lemma fastResidueGcd_eq (A t : ℕ) : fastResidueGcd A t = residueGcd A t := by
  simp only [fastResidueGcd,residueGcd,Nat.fastFibAux_eq,lucasFibonacciSum,Nat.fib_add_two]
  congr 1
  omega

/-- The test is executable for every positive modulus and target gcd. -/
def exactGcdTest (m a d : ℕ) : Bool :=
  decide (∃ t : Fin (spectrumModulus m d), t.val ≡ a [MOD m] ∧ fastResidueGcd (spectrumModulus m d) t.val=d)

theorem exactGcdTest_iff {m d : ℕ} (hm : 0 < m) (hd : 0 < d) (a : ℕ) :
    exactGcdTest m a d=true ↔ ∃ n, 0<n ∧ n ≡ a [MOD m] ∧ n.gcd (lucasFibonacciSum n)=d := by
  obtain ⟨pos,mD,dD,ret⟩ := spectrum_modulus_spec hm hd
  simpa only [exactGcdTest,decide_eq_true_eq,fastResidueGcd_eq] using
    (exact_gcd_iff_at_return pos mD dD ret a).symm

/-- Every inhabited fiber contains an unbounded family of prime multiples of one fixed divisor
of the test modulus, with its cofactor in the same reduced progression throughout. -/
theorem exact_gcd_prime_family {m a d : ℕ} (hm : 0 < m) (hd : 0 < d)
    (hit : ∃ n, 0<n ∧ n ≡ a [MOD m] ∧ n.gcd (lucasFibonacciSum n)=d) :
    ∃ g : ℕ, 0<g ∧ g ∣ spectrumModulus m d ∧
      ∀ B, ∃ q : ℕ, B<q ∧ q.Prime ∧ g*q ≡ a [MOD m] ∧
        (g*q).gcd (lucasFibonacciSum (g*q))=d := by
  obtain ⟨pos,mD,dD,ret⟩ := spectrum_modulus_spec hm hd
  obtain ⟨t,cl,eq⟩ := (exact_gcd_iff_at_return pos mD dD ret a).mp hit
  refine ⟨_,Nat.gcd_pos_of_pos_right t.val pos,Nat.gcd_dvd_right ..,fun B => ?_⟩
  obtain ⟨q,big,hq,ht,value⟩ := prime_realizes_residue_gcd pos ret t.val B
  exact ⟨q,big,hq,(ht.of_dvd mD).trans cl,value.trans eq⟩

/-- Failure of the gcd-one test excludes prime upper values throughout the progression. -/
theorem no_prime_of_failed_gcd_test {m a : ℕ} (hm : 0 < m) (fail : exactGcdTest m a 1=false)
    {n : ℕ} (cl : n ≡ a [MOD m]) : ¬(lucasFibonacciSum n).Prime := by
  cases n with
  | zero => decide
  | succ n =>
    intro hp
    have test := (exactGcdTest_iff hm (by decide : 0<1) a).mpr
      ⟨n+1,by omega,cl,coprime_of_prime_upper (by omega) hp⟩
    rw [fail] at test
    contradiction

#print axioms exact_gcd_iff_at_return
#print axioms exactGcdTest_iff
#print axioms exact_gcd_prime_family
#print axioms no_prime_of_failed_gcd_test

end Arxiv.«2211.10788».IndexDivisors
