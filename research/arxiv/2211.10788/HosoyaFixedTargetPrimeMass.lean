import HosoyaStableTargetClasses
import HosoyaPrimePowerUniformMass
import HosoyaReducedClassMass

/-! Exact normalized logarithmic mass for prime parameters at a fixed integer target. -/

namespace Arxiv.«2211.10788».LocalPower
open ProgressionClosure AlmostPrimeClosure PrimeObstruction Finset Filter Topology CunninghamChain.PrimeMass

private theorem periodic_prime_mass {M : ℕ} (hm : 0<M) (H : ℕ → Prop) [DecidablePred H]
    (per : Function.Periodic H M) :
    Tendsto (fun x : ℝ => (x-1)*mass {n : ℕ | n.Prime ∧ H n} x) (𝓝[>] 1)
      (𝓝 ((((range M).filter fun i => i.Coprime M ∧ H i).card:ℝ) / M.totient)) := by
  let : NeZero M := ⟨hm.ne'⟩
  classical
  let S : Finset (ZMod M)ˣ := univ.filter fun (u : (ZMod M)ˣ) => H (u:ZMod M).val
  let R := (range M).filter fun i => i.Coprime M ∧ H i
  have count : S.card = R.card := by
    apply card_bij (fun (u : (ZMod M)ˣ) _ => (u:ZMod M).val)
    · intro u hu
      exact mem_filter.mpr ⟨mem_range.mpr (ZMod.val_lt _),ZMod.val_coe_unit_coprime u,
        (mem_filter.mp hu).2⟩
    · intro u _ v _ eq
      exact Units.ext (ZMod.val_injective M eq)
    · intro i hi
      obtain ⟨lt,cop,hit⟩ := mem_filter.mp hi
      let u := ZMod.unitOfCoprime i cop
      have uv : (u:ZMod M).val=i := by
        rw [show (u:ZMod M)=(i:ZMod M) from ZMod.coe_unitOfCoprime ..]
        exact ZMod.val_natCast_of_lt (mem_range.mp lt)
      exact ⟨u,mem_filter.mpr ⟨mem_univ _,uv.symm ▸ hit⟩,uv⟩
  have cls (n : ℕ) : n∈represented S ↔ n.Coprime M ∧ H n := by
    constructor
    · rintro ⟨u,hu,eq⟩
      refine ⟨(ZMod.isUnit_iff_coprime n M).mp (eq ▸ u.isUnit),?_⟩
      have h : H (u:ZMod M).val := (mem_filter.mp hu).2
      rwa [←eq,ZMod.val_natCast,per.map_mod_nat] at h
    · rintro ⟨cop,hit⟩
      let u := ZMod.unitOfCoprime n cop
      have eq : (u:ZMod M)=(n:ZMod M) := ZMod.coe_unitOfCoprime ..
      refine ⟨u,mem_filter.mpr ⟨mem_univ _,?_⟩,eq.symm⟩
      rwa [eq,ZMod.val_natCast,per.map_mod_nat]
  have lim := mass_represented S
  rw [count] at lim
  have upper := lim.add (finite_mass_tendsto (Set.finite_Iic M))
  rw [add_zero] at upper
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' lim upper
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact mul_le_mul_of_nonneg_left (prime_mass_mono (A:=represented S) (B:={n : ℕ | n.Prime ∧ H n}) (fun n hn hc =>
      ⟨hn,((cls n).mp hc).2⟩) hx) (sub_nonneg.mpr (show 1<x from hx).le)
  · filter_upwards [self_mem_nhdsWithin] with x hx
    have inc := mass_le_cover (∅ : Finset Unit) (fun _ => (∅ : Set ℕ))
      {n : ℕ | n.Prime ∧ H n} (represented S) (Set.Iic M) (by
        intro n hit hn
        by_cases big : M<n
        · exact Or.inr (Or.inl ((cls n).mpr ⟨hn.coprime_iff_not_dvd.mpr
            (Nat.not_dvd_of_pos_of_lt hm big),hit.2⟩))
        · exact Or.inr (Or.inr (le_of_not_gt big))) hx
    simp only [sum_empty,zero_add] at inc
    simpa only [mul_add] using mul_le_mul_of_nonneg_left inc (sub_nonneg.mpr (show 1<x from hx).le)

private lemma totient_steps {p P : ℕ} (hp : p.Prime) (div : p ∣ P) (e : ℕ) :
    (P*p^e).totient=P.totient*p^e := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [pow_succ,←Nat.mul_assoc,Nat.mul_comm (P*p^e) p,Nat.totient_mul_of_prime_of_dvd hp
      (div.trans (dvd_mul_right P _)),ih]
    ring

/-- For a fixed target the normalized prime mass is a computable constant
divided by a power of p. The same numerator works at every higher level. -/
theorem fixed_target_prime_mass (p : ℕ) [Fact p.Prime] (r d : ℕ) (hd : 0<d) (y : ℤ) (b : ℕ) :
    Tendsto (fun x : ℝ => (x-1)*mass (primeIndexHits r d (p^(testLevel p d y b)) y) x)
      (𝓝[>] 1) (𝓝 ((targetMultiplicity p r d y:ℝ) /
        ((targetPeriod p y).totient * (p:ℝ)^(targetDepth p y+b)))) := by
  let M := parameterModulus p y b
  let H := Hit d r (p^(testLevel p d y b)) y
  let (n : ℕ) : Decidable (H n) := (inferInstance : Decidable (_ ≡ _ [ZMOD _]))
  have he := periodic_prime_mass (parameterModulus_pos p y b) H (periodic_target_hits p r d hd y b)
  change Tendsto _ _ (𝓝 (((reducedTargetClasses p r d y b).card:ℝ) / M.totient)) at he
  rw [stable_reduced_target_count p r d hd y b] at he
  have den : M.totient = (targetPeriod p y).totient*p^(targetDepth p y+b) :=
    totient_steps (Fact.out : p.Prime) (targetPeriod_spec p y).2 _
  simpa only [den,Nat.cast_mul,Nat.cast_pow,primeIndexHits,H] using he

#print axioms fixed_target_prime_mass

/-- With zero reduced count, every prime hit beyond the threshold is a divisor
of the fixed phase period. This includes the testing prime itself. -/
theorem exceptional_prime_divides_period (p : ℕ) [Fact p.Prime] (r d : ℕ) (hd : 0<d)
    (y : ℤ) (b n : ℕ) (zero : targetMultiplicity p r d y=0) (hn : n.Prime)
    (hit : Hit d r (p^(testLevel p d y b)) y n) : n ∣ targetPeriod p y := by
  let P := targetPeriod p y
  let M := parameterModulus p y b
  by_contra no
  have cop : n.Coprime P := hn.coprime_iff_not_dvd.mpr no
  have cm : n.Coprime M := cop.mul_right ((cop.of_dvd_right (targetPeriod_spec p y).2).pow_right _)
  have modcop : (n%M).Coprime M := by
    change (n%M).gcd M=1
    rw [← Nat.gcd_rec M n,Nat.gcd_comm]
    exact cm
  have mem : n%M∈reducedTargetClasses p r d y b := mem_filter.mpr
    ⟨mem_range.mpr (Nat.mod_lt _ (parameterModulus_pos p y b)),modcop,
      ((periodic_target_hits p r d hd y b).map_mod_nat n).symm ▸ hit⟩
  have pos := card_pos.mpr ⟨_,mem⟩
  rw [stable_reduced_target_count p r d hd y b,zero] at pos
  exact (lt_irrefl 0) pos

#print axioms exceptional_prime_divides_period

/-- Allowing bounded prime witnesses adds exactly the values attained at
prime divisors of the phase period to the positive-mass criterion. -/
theorem fixed_target_prime_closure_iff (p : ℕ) [Fact p.Prime] (r d : ℕ) (hd : 0<d) (y : ℤ) :
    (∀ h : ℕ, ∃ q : ℕ, q.Prime ∧ Hit d r (p^h) y q) ↔
      0<targetMultiplicity p r d y ∨
        ∃ q : ℕ, q.Prime ∧ q ∣ targetPeriod p y ∧ (lucasFibonacciSum (r+d*q):ℤ)=y := by
  constructor
  · intro all
    by_cases pos : 0<targetMultiplicity p r d y
    · exact Or.inl pos
    right
    let P := targetPeriod p y
    let B := lucasFibonacciSum (r+d*P)+y.natAbs
    let h := testLevel p d y B
    obtain ⟨q,hq,hit⟩ := all h
    have div : q ∣ P := exceptional_prime_divides_period p r d hd y B q (by omega) hq hit
    refine ⟨q,hq,div,?_⟩
    have qle := Nat.le_of_dvd (targetPeriod_spec p y).1 div
    have idx : r+d*q≤r+d*P := Nat.add_le_add_left (Nat.mul_le_mul_left _ qle) _
    have value : lucasFibonacciSum (r+d*q)≤lucasFibonacciSum (r+d*P) :=
      Nat.add_le_add (Nat.mul_le_mul_left 2 (Nat.fib_mono idx)) (Nat.fib_mono (Nat.add_le_add_right idx 2))
    have size : (y-(lucasFibonacciSum (r+d*q):ℤ)).natAbs ≤ B :=
      (Int.natAbs_sub_le ..).trans (by dsimp [B]; omega)
    have gap : B<p^h := (Nat.lt_two_pow_self (n:=B)).trans_le
      ((Nat.pow_le_pow_left (Fact.out : p.Prime).two_le B).trans
        (Nat.pow_le_pow_right (Fact.out : p.Prime).pos (by dsimp [h,testLevel]; omega)))
    have dt := Int.natAbs_dvd_natAbs.mpr (Int.ModEq.dvd hit)
    simp only [Int.natAbs_natCast] at dt
    by_contra ne
    have nz := Int.natAbs_ne_zero.mpr (sub_ne_zero.mpr (Ne.symm ne))
    exact (not_lt_of_ge (Nat.le_of_dvd (Nat.pos_of_ne_zero nz) dt)) (size.trans_lt gap)
  · rintro (pos|⟨q,hq,_,eq⟩) h
    · obtain ⟨q,_,hq,hit⟩ := (fixed_target_prime_test_iff p r d hd y).mpr pos h 0
      exact ⟨q,hq,hit⟩
    · exact ⟨q,hq,show Hit d r (p^h) y q from eq ▸ Int.ModEq.refl _⟩

#print axioms fixed_target_prime_closure_iff

end Arxiv.«2211.10788».LocalPower
