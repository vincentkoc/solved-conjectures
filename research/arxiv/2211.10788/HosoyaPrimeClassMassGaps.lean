import HosoyaLocalPrimeFactors
import HosoyaPrimeParameterMass

/-! Positive Dirichlet mass of composite prime-index values inside every reduced class. -/

namespace Arxiv.«2211.10788»
open Filter Topology CunninghamChain.PrimeMass

private def res (m a : ℕ) : Set ℕ := {n | n ≡ a [MOD m]}

private theorem class_mass {m a : ℕ} (hm : 0 < m) (ha : a.Coprime m) :
    Tendsto (fun x : ℝ => (x-1)*mass (res m a) x) (𝓝[>] 1) (𝓝 ((m.totient : ℝ)⁻¹)) := by
  let : NeZero m := ⟨hm.ne'⟩
  simpa only [res,←ZMod.natCast_eq_natCast_iff] using
    (mass_progression (a:ZMod m) ((ZMod.isUnit_iff_coprime ..).mpr ha))

private theorem two_set_bound (P H A G : Set ℕ)
    (hp : ∀ n, n.Prime → n∈P → n∈A ∨ n∈G) (hh : H⊆A)
    (disj : ∀ n, n.Prime → n∈H → n∉P) {x : ℝ} (hx : 1<x) :
    mass P x + mass H x ≤ mass A x + mass G x := by
  have pt (n : ℕ) : weight P n + weight H n ≤ weight A n + weight G n := by
    by_cases hn : n.Prime
    · have hlog : 0≤Real.log (n:ℝ) := Real.log_nonneg (by exact_mod_cast hn.one_le)
      by_cases h₁ : n∈P
      · have h₂ : n∉H := fun h => disj n hn h h₁
        rcases hp n hn h₁ with h|h
        · by_cases g : n∈G <;> simp_all [weight]
        · by_cases a : n∈A <;> simp_all [weight]
      · by_cases h₂ : n∈H
        · have := hh h₂
          by_cases g : n∈G <;> simp_all [weight]
        · simp [weight,hn,h₁,h₂]
          exact add_nonneg (weight_nonneg A n) (weight_nonneg G n)
    · simp [weight,hn]
  unfold mass
  rw [←(summable_weight P hx).tsum_add (summable_weight H hx),
    ←(summable_weight A hx).tsum_add (summable_weight G hx)]
  apply ((summable_weight P hx).add (summable_weight H hx)).tsum_le_tsum _
    ((summable_weight A hx).add (summable_weight G hx))
  intro n
  simpa only [←add_div] using
    (div_le_div_of_nonneg_right (pt n) (by positivity : 0≤(n:ℝ)^x))

private theorem composite_class {m a : ℕ} (hm : 0 < m) (ha : a.Coprime m) :
    ∃ b L : ℕ, 0<L ∧ m ∣ L ∧ b ≡ a [MOD m] ∧ b.Coprime L ∧
      ∀ p, p.Prime → p ≡ b [MOD L] → ¬(lucasFibonacciSum p).Prime := by
  by_cases compat : a ≡ 41 [MOD m.gcd 120] ∨ a ≡ 89 [MOD m.gcd 120]
  · obtain ⟨b,L,hL,hmL,_,hb,hu,_,S,hcard,hs⟩ :=
      (upper_surviving_class_many_factors_iff hm ha 0 2).mp compat
    refine ⟨b,L,hL,hmL,hb,hu,?_⟩
    intro p _ he prime
    have sub : S ⊆ {lucasFibonacciSum p} := by
      intro q hq
      obtain ⟨_,hpr,hit⟩ := hs q hq
      simpa only [Finset.mem_singleton] using (Nat.prime_dvd_prime_iff_eq hpr prime).mp (hit p he)
    have h := Finset.card_le_card sub
    simp [hcard] at h
  · obtain ⟨b,hb,hpr,he⟩ := Nat.forall_exists_prime_gt_and_modEq 10 hm.ne' ha
    have hu : b.Coprime 10 := hpr.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by decide) hb)
    refine ⟨b,m*10,Nat.mul_pos hm (by decide),dvd_mul_right ..,he,
      (show b.Coprime m from he.gcd_eq.trans ha).mul_right hu,?_⟩
    intro p hp hn hv
    have cp : p.Coprime 10 := (hn.of_dvd (dvd_mul_left ..)).gcd_eq.trans hu
    rcases upper_prime_value_in_class hp ((hn.of_dvd (dvd_mul_right ..)).trans he) hv with h|h|h
    · exact (by decide : ¬Nat.Coprime 2 10) (h ▸ cp)
    · exact (by decide : ¬Nat.Coprime 5 10) (h ▸ cp)
    · exact compat h

/-- In every reduced progression the prime-index prime values omit a positive
amount of normalized logarithmic Dirichlet mass. -/
theorem upper_prime_value_mass_gap_in_class {m a : ℕ} (hm : 0 < m) (ha : a.Coprime m) :
    ∃ δ : ℝ, 0<δ ∧ ∀ᶠ x : ℝ in 𝓝[>] 1,
      (x-1)*mass {n : ℕ | n ≡ a [MOD m] ∧ (lucasFibonacciSum n).Prime} x <
        (m.totient:ℝ)⁻¹-δ := by
  obtain ⟨b,L,hL,hmL,hb,hu,bad⟩ := composite_class hm ha
  let D := (L.totient:ℝ)⁻¹
  have hD : 0<D := inv_pos.mpr (by exact_mod_cast (Nat.totient_pos.mpr hL))
  let P := {n : ℕ | n ≡ a [MOD m] ∧ (lucasFibonacciSum n).Prime}
  have lim := (class_mass hm ha).sub (class_mass hL hu)
  have lt := lim.eventually_lt_const (show (m.totient:ℝ)⁻¹-D<(m.totient:ℝ)⁻¹-D/2 by linarith)
  refine ⟨D/2,by positivity,?_⟩
  filter_upwards [self_mem_nhdsWithin,lt] with x hx hx'
  have bound := two_set_bound P (res L b) (res m a) ∅
    (fun _ _ h => Or.inl h.1) (fun _ h => (Nat.ModEq.of_dvd hmL h).trans hb)
    (fun n hp h hv => bad n hp h hv.2) hx
  have empty : mass ∅ x=0 := by simp [mass,weight]
  rw [empty,add_zero] at bound
  have h := mul_le_mul_of_nonneg_left bound (show 0≤x-1 by linarith [show 1<x from hx])
  change (x-1)*mass P x<_
  change (x-1)*mass (res m a) x - (x-1)*mass (res L b) x < _ at hx'
  linarith only [h,hx']


private lemma divisor_67 (n : ℕ) : 67 ∣ lucasFibonacciSum n ↔ n ≡ 41 [MOD 68] := by
  have rank : fibonacciStepRank 67 1=68 := by
    unfold fibonacciStepRank
    apply (Nat.find_eq_iff _).mpr
    refine ⟨⟨by decide,by simp only [one_mul,Nat.fib_eq_fastFib]; decide +kernel⟩,?_⟩
    have test : ∀ i : Fin 68, 0 < i.val → ¬67 ∣ Nat.fastFib i.val := by decide +kernel
    intro i hi h
    exact test ⟨i,hi⟩ h.1 (by simpa only [one_mul,Nat.fastFib_eq] using h.2)
  have hit : 67 ∣ lucasFibonacciSum (0+1*41) := by
    simp only [lucasFibonacciSum,Nat.fib_eq_fastFib]; decide +kernel
  simpa only [zero_add,one_mul,rank] using upper_divisor_parameter_class hit n

private def holes : Set ℕ := res 2040 41 ∪ res 2040 449

private lemma holes_iff (n : ℕ) :
    n∈holes ↔ n∈upperPrimeIndexSurvivors120 ∧ 67 ∣ lucasFibonacciSum n := by
  have t : ∀ i : Fin 2040, (i.val=41 ∨ i.val=449) ↔
      (i.val%120=41 ∨ i.val%120=89) ∧ i.val%68=41 := by decide +kernel
  have h := t ⟨n%2040,Nat.mod_lt _ (by decide)⟩
  rw [divisor_67]
  change (n%2040=41 ∨ n%2040=449) ↔ (n%120=41 ∨ n%120=89) ∧ n%68=41
  simpa only [Fin.val_mk,Nat.mod_mod_of_dvd n (by decide : 120∣2040),
    Nat.mod_mod_of_dvd n (by decide : 68∣2040)] using h

private lemma union_mass (A B : Set ℕ) (h : Disjoint A B) {x : ℝ} (hx : 1<x) :
    mass (A ∪ B) x = mass A x + mass B x := by
  rw [mass,mass,mass,←(summable_weight A hx).tsum_add (summable_weight B hx)]
  apply tsum_congr
  intro n
  rw [←add_div]
  congr 1
  have dis : n∈A → n∉B := fun hn => Set.disjoint_left.mp h hn
  by_cases h₁ : n∈A <;> by_cases h₂ : n∈B <;> by_cases h₃ : n.Prime <;> simp_all [weight]

/-- The two period-120 classes have exact surviving mass 15/256 after adding
the prime divisor 67. -/
theorem upper_prime_index_sieve_67_mass :
    Tendsto (fun x : ℝ => (x-1)*mass {n : ℕ | n∈upperPrimeIndexSurvivors120 ∧
        ¬67 ∣ lucasFibonacciSum n} x) (𝓝[>] 1) (𝓝 (15/256 : ℝ)) := by
  let A := {n : ℕ | n∈upperPrimeIndexSurvivors120 ∧ ¬67 ∣ lucasFibonacciSum n}
  have sep : Disjoint (res 2040 41) (res 2040 449) := by
    apply Set.disjoint_left.mpr
    intro n h₁ h₂
    change n%2040=41 at h₁
    change n%2040=449 at h₂
    omega
  have dis : Disjoint A holes := Set.disjoint_left.mpr fun n h₁ h₂ => h₁.2 ((holes_iff n).mp h₂).2
  have eq : upperPrimeIndexSurvivors120 = A ∪ holes := by
    ext n
    simp only [Set.mem_union,holes_iff]
    by_cases h : 67 ∣ lucasFibonacciSum n <;> simp [A,h]
  have lim := upper_prime_index_survivor_mass.sub
    ((class_mass (m:=2040) (a:=41) (by decide) (by decide)).add
     (class_mass (m:=2040) (a:=449) (by decide) (by decide)))
  have tot : (2040:ℕ).totient=512 := by decide +kernel
  simp only [tot] at lim
  convert (lim.congr' (f₂:=fun x : ℝ => (x-1)*mass A x) ?_) using 1 <;> try norm_num
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [eq,union_mass _ _ dis hx,show mass holes x=_ from union_mass _ _ sep hx]
  ring

/-- A numerical upper bound on the normalized mass of actual prime-index
prime values. Finitely many initial indices do not contribute to the limit. -/
theorem upper_prime_index_value_mass_bound_67 (c : ℝ) (hc : 15/256<c) :
    ∀ᶠ x : ℝ in 𝓝[>] 1, (x-1)*mass {n : ℕ | (lucasFibonacciSum n).Prime} x<c := by
  let A := {n : ℕ | n∈upperPrimeIndexSurvivors120 ∧ ¬67 ∣ lucasFibonacciSum n}
  let G : Set ℕ := {2,5}
  have fin : G.Finite := Set.toFinite _
  have lim := upper_prime_index_sieve_67_mass.add (finite_mass_tendsto fin)
  have lt := lim.eventually_lt_const (show (15/256:ℝ)+0<c by simpa using hc)
  filter_upwards [self_mem_nhdsWithin,lt] with x hx hlt
  have bound := mass_le_cover (∅ : Finset Unit) (fun _ => (∅ : Set ℕ))
    {n : ℕ | (lucasFibonacciSum n).Prime} A G (fun n hv hn => by
      rcases upper_prime_value_at_prime_index hn hv with h|h|h
      · exact Or.inr (Or.inr (by simp [G,h]))
      · exact Or.inr (Or.inr (by simp [G,h]))
      right; left
      refine ⟨h,?_⟩
      intro hd
      have e := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 67) hv).mp hd
      have hnlo : 11 ≤ n+2 := by rcases h with h|h <;> omega
      have grow := Nat.fib_mono hnlo
      have v : Nat.fib 11=89 := by decide
      unfold lucasFibonacciSum at e
      omega) hx
  simp only [Finset.sum_empty,zero_add] at bound
  apply lt_of_le_of_lt _ hlt
  simpa only [mul_add] using mul_le_mul_of_nonneg_left bound (show 0≤x-1 by linarith [show 1<x from hx])

#print axioms upper_prime_index_sieve_67_mass
#print axioms upper_prime_index_value_mass_bound_67

#print axioms upper_prime_value_mass_gap_in_class

end Arxiv.«2211.10788»
