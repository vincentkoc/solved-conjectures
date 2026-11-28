import HosoyaPrimeIndexSieve
import CunninghamPrimeDirichletMass

/-! Logarithmically weighted Dirichlet mass at prime parameters of the
upper Hosoya diagonal. -/

namespace Arxiv.«2211.10788»
open Filter Topology CunninghamChain.PrimeMass

private theorem mass_congr_primes {A B : Set ℕ} (h : ∀ n, n.Prime → (n∈A ↔ n∈B)) (x : ℝ) :
    mass A x = mass B x := by
  unfold mass
  apply tsum_congr
  intro n
  have eq := and_congr_right (h n)
  unfold weight
  by_cases hn : n.Prime ∧ n∈A
  · rw [if_pos hn,if_pos (eq.mp hn)]
  · rw [if_neg hn,if_neg (hn ∘ eq.mpr)]

/-- When a divisor occurs at one parameter s, its prime hits have normalized
logarithmic Dirichlet mass 1/φ(e) in a reduced class and zero otherwise. -/
theorem upper_prime_parameter_mass_at_hit {m r d s : ℕ} [NeZero m]
    (hs : m ∣ lucasFibonacciSum (r+d*s)) :
    Tendsto (fun x : ℝ => (x-1)*mass {n : ℕ | n.Prime ∧ m ∣ lucasFibonacciSum (r+d*n)} x)
      (𝓝[>] 1) (𝓝 (if s.Coprime (fibonacciStepRank m d) then
        (((fibonacciStepRank m d).totient : ℝ)⁻¹) else 0)) := by
  let e := fibonacciStepRank m d
  have he : 0<e := (Nat.find_spec (p := fun t => 0<t ∧ m ∣ Nat.fib (d*t)) _).1
  let : NeZero e := ⟨he.ne'⟩
  split_ifs with hu
  · have eq (x : ℝ) := mass_congr_primes (A:={n : ℕ | n.Prime ∧ m ∣ lucasFibonacciSum (r+d*n)})
      (B:={n : ℕ | (n:ZMod e)=(s:ZMod e)}) (fun n hn => by
        change (n.Prime ∧ m ∣ lucasFibonacciSum (r+d*n)) ↔ _
        rw [and_iff_right hn,upper_divisor_parameter_class hs]
        exact (ZMod.natCast_eq_natCast_iff ..).symm) x
    simp_rw [eq]
    exact mass_progression (s:ZMod e) ((ZMod.isUnit_iff_coprime ..).mpr hu)
  · exact finite_mass_tendsto (Set.not_infinite.mp (fun hi => hu ((upper_prime_parameters_infinite_iff hs).mp hi)))

open Classical in
/-- The finite recurrence test determines the residue of the weighted prime
Dirichlet series, without first finding a hit. -/
theorem upper_prime_parameter_mass {p : ℕ} [Fact p.Prime] (r d : ℕ) :
    Tendsto (fun x : ℝ => (x-1)*mass {n : ℕ | n.Prime ∧ p ∣ lucasFibonacciSum (r+d*n)} x)
      (𝓝[>] 1) (𝓝 (if UpperPrimeParameterTest p r d then
        (((fibonacciStepRank p d).totient : ℝ)⁻¹) else 0)) := by
  split_ifs with ht
  · have hi := (upper_prime_parameter_test_iff r d).mp ht
    obtain ⟨s,hh⟩ := hi.nonempty
    have lu := upper_prime_parameter_mass_at_hit hh.2
    simpa only [if_pos ((upper_prime_parameters_infinite_iff hh.2).mp hi)] using lu
  · exact finite_mass_tendsto (Set.not_infinite.mp (fun hi => ht ((upper_prime_parameter_test_iff r d).mpr hi)))

/-- The reduced classes modulo 120 whose upper terms are coprime to F₁₂₀. -/
def upperPrimeIndexSurvivors120 : Set ℕ := {n | n%120=41 ∨ n%120=89}

/-- The two prime-parameter residue classes which survive period 120 have
exact normalized logarithmic Dirichlet mass 1/16. -/
theorem upper_prime_index_survivor_mass :
    Tendsto (fun x : ℝ => (x-1)*mass upperPrimeIndexSurvivors120 x) (𝓝[>] 1) (𝓝 (1/16 : ℝ)) := by
  let A (a : ℕ) : Set ℕ := {n | (n : ZMod 120)=(a : ZMod 120)}
  have key (x : ℝ) (hx : 1<x) : mass upperPrimeIndexSurvivors120 x=mass (A 41) x+mass (A 89) x := by
    rw [mass,mass,mass,←(summable_weight (A 41) hx).tsum_add (summable_weight (A 89) hx)]
    apply tsum_congr
    intro n
    rw [←add_div]
    congr 1
    have mem (a : ℕ) : n∈A a ↔ n%120=a%120 := ZMod.natCast_eq_natCast_iff' ..
    by_cases h₁ : n%120=41 <;> by_cases h₂ : n%120=89 <;> by_cases h₃ : n.Prime <;>
      simp_all [weight,upperPrimeIndexSurvivors120]
  have lim (a : ℕ) (h : a.Coprime 120) := mass_progression (a:ZMod 120) ((ZMod.isUnit_iff_coprime ..).mpr h)
  have hl := (lim 41 (by decide)).add (lim 89 (by decide))
  have tot : (120:ℕ).totient=32 := by decide +kernel
  apply Filter.Tendsto.congr' (f₂:=fun x : ℝ => (x-1)*mass upperPrimeIndexSurvivors120 x) _ (by
    simpa only [tot,Nat.cast_ofNat,show (32:ℝ)⁻¹+32⁻¹=1/16 by norm_num] using hl)
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [key x hx, mul_add]
  rfl

/-- The normalized prime mass of prime-index prime values eventually lies
below every constant strictly greater than 1/16. -/
theorem upper_prime_index_value_mass_bound (c : ℝ) (hc : 1/16<c) :
    ∀ᶠ x : ℝ in 𝓝[>] 1, (x-1)*mass {n : ℕ | (lucasFibonacciSum n).Prime} x<c := by
  let G : Set ℕ := {2,5}
  have fin : G.Finite := Set.toFinite _
  have lim := upper_prime_index_survivor_mass.add (finite_mass_tendsto fin)
  have lt := (lim.eventually_lt_const (show (1/16:ℝ)+0<c by simpa using hc))
  filter_upwards [self_mem_nhdsWithin,lt] with x hx hlt
  apply lt_of_le_of_lt _ hlt
  rw [←mul_add]
  apply mul_le_mul_of_nonneg_left _ (by exact sub_nonneg.mpr (le_of_lt hx))
  have bound := mass_le_cover (∅ : Finset Unit) (fun _ => (∅ : Set ℕ))
    {n : ℕ | (lucasFibonacciSum n).Prime} upperPrimeIndexSurvivors120 G (fun n h hn => by
      rcases upper_prime_value_at_prime_index hn h with h|h|h
      · exact Or.inr (Or.inr (by simp [G,h]))
      · exact Or.inr (Or.inr (by simp [G,h]))
      · exact Or.inr (Or.inl h)) hx
  simpa using bound

#print axioms upper_prime_parameter_mass_at_hit
#print axioms upper_prime_parameter_mass
#print axioms upper_prime_index_survivor_mass
#print axioms upper_prime_index_value_mass_bound

end Arxiv.«2211.10788»
