import Erdos478ShortSieve
import Erdos478BoundedSchurPrime

/-!
# Schur primes with a finite sieve for the exclusions

Small primes divide the step automatically. For the remaining prime divisors
of the excluded integer, each polynomial forbids at most its degree many
residues. A positive survivor replaces the product of the excluded primes.
-/

namespace Erdos478.EffectiveResolvent
open Polynomial Finset SchurSieve
open scoped Polynomial

def sieveBits (D B : ℕ) := Nat.clog 2 (max (D+1) (Nat.log 2 B+1))
def sievedFactor (D B : ℕ) := D.factorial * 2^(32*(D+1)*(sieveBits D B+1)^2)
def sievedSchurBound (D U B : ℕ) := schurBound D U (sievedFactor D B)

theorem sievedSchurBound_mono (D U : ℕ) : Monotone (sievedSchurBound D U) := by
  intro B B' h
  have hb : sieveBits D B ≤ sieveBits D B' := Nat.clog_mono_right 2
    (max_le_max_left _ (Nat.add_le_add_right (Nat.log_mono_right h) _))
  dsimp [sievedSchurBound,schurBound,sievedFactor]
  gcongr
  decide

private theorem count_exclusions {B : ℕ} (hB : 0<B) : B.primeFactors.card ≤ Nat.log 2 B := by
  apply Nat.le_log_of_pow_le (by decide)
  calc
    _ = ∏ _q ∈ B.primeFactors, 2 := by simp
    _ ≤ ∏ q ∈ B.primeFactors, q := prod_le_prod' (fun q hq => (Nat.prime_of_mem_primeFactors hq).two_le)
    _ ≤ B := Nat.le_of_dvd hB (Nat.prod_primeFactors_dvd B)

private noncomputable def forbidden (g : ℤ[X]) (t M p : ℕ) : Finset (ZMod p) := by
  classical
  exact if hp : p.Prime then
    letI : Fact p.Prime := ⟨hp⟩
    univ.filter fun z => (g.map (Int.castRingHom (ZMod p))).IsRoot (t+M*z)
  else ∅

private theorem mem_forbidden {g : ℤ[X]} {t M p : ℕ} (hp : p.Prime) (z : ZMod p) :
    z ∈ forbidden g t M p ↔ (g.map (Int.castRingHom (ZMod p))).IsRoot (t+M*z) := by
  classical simp [forbidden,hp]

private theorem forbidden_card {g : ℤ[X]} (hg : g.Monic) {t M p : ℕ}
    (hp : p.Prime) (hM : ¬ p ∣ M) : (forbidden g t M p).card ≤ g.natDegree := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let f := g.map (Int.castRingHom (ZMod p))
  have hf : f ≠ 0 := (hg.map _).ne_zero
  have hne : (M : ZMod p) ≠ 0 := fun h => hM ((ZMod.natCast_eq_zero_iff ..).mp h)
  calc
    _ ≤ f.roots.toFinset.card :=
      card_le_card_of_injOn (fun z : ZMod p => t+M*z)
        (fun _ hz => Multiset.mem_toFinset.mpr ((mem_roots hf).mpr ((mem_forbidden hp _).mp hz)))
        (fun _ _ _ _ h => mul_left_cancel₀ hne (add_left_cancel h))
    _ ≤ f.natDegree := f.roots.toFinset_card_le.trans f.card_roots'
    _ = _ := hg.natDegree_map _

/-- A prime admitting a root, with only a double logarithm of the excluded
integer entering the bit length of the shift. -/
theorem sieved_prime_root {I : Type*} [Fintype I] [Nonempty I] (g : ℤ[X]) (a : I → ℂ)
    (h : g.map (Int.castRingHom ℂ) = ∏ i, (X-C (a i))) (U B : ℕ) (hB : 0<B)
    (ha : ∀ i, ‖a i‖ ≤ U) :
    ∃ p ≤ sievedSchurBound (Fintype.card I) U B, p.Prime ∧ ¬p ∣ B ∧
      ∃ x : ZMod p, (g.map (Int.castRingHom (ZMod p))).IsRoot x := by
  classical
  let D := Fintype.card I
  let L := sieveBits D B
  have hm : g.Monic := (Function.Injective.monic_map_iff (f := Int.castRingHom ℂ)
    (by exact Int.cast_injective)).mpr (by rw [h]; exact monic_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _))
  have hdeg : g.natDegree=D := by rw [← hm.natDegree_map (Int.castRingHom ℂ),h]; simp [D]
  apply bounded_prime_from_shift g a h U B (sievedFactor D B) ha
  intro t c hc
  let A := (2*U+1)*D.factorial*c
  let M := A*c
  let Q := B.primeFactors.filter (fun p => ¬ p ∣ A)
  have hmax : max (D+1) (Nat.log 2 B+1) ≤ 2^L := Nat.le_pow_clog (by decide) _
  have prime (p) (hp : p ∈ Q) := Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1
  have large (p) (hp : p ∈ Q) : D < p := by
    by_contra! hle
    exact (mem_filter.mp hp).2 (dvd_mul_of_dvd_left
      (dvd_mul_of_dvd_right (Nat.dvd_factorial (prime p hp).pos hle) _) _)
  have small (p) (hp : p ∈ Q) : (forbidden g t M p).card ≤ D := by
    apply (forbidden_card hm (prime p hp) _).trans hdeg.le
    intro hdiv
    rcases (prime p hp).dvd_mul.mp hdiv with h | h
    · exact (mem_filter.mp hp).2 h
    · exact (mem_filter.mp hp).2 (dvd_mul_of_dvd_right h _)
  have hcard : Q.card+1 ≤ 2^L :=
    (Nat.add_le_add_right ((card_filter_le ..).trans (count_exclusions hB)) 1).trans ((le_max_right ..).trans hmax)
  obtain ⟨x,hx,hxw,avoid⟩ := positive_survivor Q D L (forbidden g t M) prime large small hcard ((le_max_left ..).trans hmax)
  refine ⟨D.factorial*x,Nat.mul_le_mul_left _ (hxw.le.trans (window_le D L)),Nat.mul_pos D.factorial_pos hx,?_⟩
  intro p hp hd
  by_cases hpa : p ∣ A
  · left
    simpa only [A,mul_assoc,mul_left_comm,mul_comm] using dvd_mul_of_dvd_left hpa x
  · right
    have hQ : p ∈ Q := mem_filter.mpr ⟨hp.mem_primeFactors hd hB.ne',hpa⟩
    have hn := mt (mem_forbidden hp (x : ZMod p)).mpr (avoid p hQ)
    convert hn using 2
    dsimp [M,A]
    push_cast
    ring

def sievedSchur : RootPrimeBound where
  bound := sievedSchurBound
  mono := sievedSchurBound_mono
  prime_root := sieved_prime_root

#print axioms sievedSchurBound_mono
#print axioms sieved_prime_root

end Erdos478.EffectiveResolvent
