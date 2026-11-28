import HosoyaTargetLiftThreshold

/-! The number of reduced parameter classes that survive a fixed Hosoya target
stabilizes after its discriminant threshold. -/

namespace Arxiv.«2211.10788».LocalPower

open Finset ProgressionClosure

def testLevel (p : ℕ) [Fact p.Prime] (d : ℕ) (y : ℤ) (b : ℕ) : ℕ :=
  targetStepOrder p d y + targetDepth p y + b

def parameterModulus (p : ℕ) [Fact p.Prime] (y : ℤ) (b : ℕ) : ℕ :=
  targetPeriod p y * p^(targetDepth p y+b)

private instance decHit (d r M : ℕ) (y : ℤ) (n : ℕ) : Decidable (Hit d r M y n) := by
  unfold Hit
  infer_instance

private instance decGood (p : ℕ) [Fact p.Prime] (r d : ℕ) (y : ℤ) (i : ℕ) :
    Decidable (targetGood p r d y i) := by unfold targetGood; infer_instance

/-- The stable count. Each reduced successful phase contributes exactly
p raised to the valuation of its companion. -/
def targetMultiplicity (p : ℕ) [Fact p.Prime] (r d : ℕ) (y : ℤ) : ℕ :=
  ∑ i ∈ range (targetPeriod p y), if i.Coprime (targetPeriod p y) ∧ targetGood p r d y i
    then p^(companionOrder p (r+d*i)) else 0

def reducedTargetClasses (p : ℕ) [Fact p.Prime] (r d : ℕ) (y : ℤ) (b : ℕ) : Finset ℕ :=
  (range (parameterModulus p y b)).filter fun n =>
    n.Coprime (parameterModulus p y b) ∧ Hit d r (p^(testLevel p d y b)) y n

private lemma split_range (P N : ℕ) (f : ℕ → ℕ) :
    ∑ n ∈ range (P*N), f n = ∑ i ∈ range P, ∑ t ∈ range N, f (i+P*t) := by
  rw [sum_comm]
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ,sum_range_add,ih,sum_range_succ]
    simp only [Nat.add_comm (P*n)]

private lemma class_coprime {p P : ℕ} (hpP : p ∣ P) (i t e : ℕ) :
    (i+P*t).Coprime (P*p^e) ↔ i.Coprime P := by
  rw [Nat.coprime_mul_iff_right]
  constructor
  · exact fun h => (Nat.coprime_add_mul_left_left ..).mp h.1
  · intro h
    have hh := (Nat.coprime_add_mul_left_left i P t).mpr h
    exact ⟨hh,(hh.of_dvd_right hpP).pow_right e⟩

private lemma count_class (L B z : ℕ) (hL : 0 < L) :
    (∑ t ∈ range (L*B), if t ≡ z [MOD L] then 1 else 0) = B := by
  rw [sum_boole,← Nat.count_eq_card_filter_range,Nat.count_modEq_card _ hL]
  simp [Nat.mul_div_cancel_left _ hL]

/-- The reduced hit count is independent of b. Its ambient modulus grows
by p at every step. This holds at every prime, including 2, 5 and 11. -/
theorem stable_reduced_target_count (p : ℕ) [Fact p.Prime] (r d : ℕ) (hd : 0 < d) (y : ℤ) (b : ℕ) :
    (reducedTargetClasses p r d y b).card = targetMultiplicity p r d y := by
  let P := targetPeriod p y
  let K := targetDepth p y
  let h := testLevel p d y b
  have hp := targetPeriod_spec p y
  change ((range (P*p^(K+b))).filter (fun n => n.Coprime (P*p^(K+b)) ∧ Hit d r (p^h) y n)).card = _
  have count (S : Finset ℕ) (Q : ℕ → Prop) [DecidablePred Q] :
      (S.filter Q).card = ∑ i ∈ S, if Q i then 1 else 0 := by simp
  rw [count,split_range]
  unfold targetMultiplicity
  apply sum_congr rfl
  intro i hi
  change (∑ t ∈ range (p^(K+b)), if (i+P*t).Coprime (P*p^(K+b)) ∧ Hit d r (p^h) y (i+P*t)
    then 1 else 0) = (if i.Coprime P ∧ targetGood p r d y i then p^(companionOrder p (r+d*i)) else 0)
  have hpP : p ∣ P := hp.2
  simp_rw [class_coprime hpP]
  by_cases cop : i.Coprime P
  · simp_rw [and_iff_right cop]
    by_cases good : targetGood p r d y i
    · obtain ⟨hv,lift⟩ := (fixed_target_branch p r d hd y i).2 good
      obtain ⟨z,_,hh⟩ := lift b
      let v := companionOrder p (r+d*i)
      change (∑ t ∈ range (p^(K+b)), if Hit d r (p^h) y (i+P*t) then 1 else 0) = _
      have he (t : ℕ) : Hit d r (p^h) y (i+P*t) ↔ t ≡ z [MOD p^(K-v+b)] := hh t
      simp_rw [he]
      have split : p^(K+b) = p^(K-v+b)*p^v := by rw [←pow_add]; congr 1; change v<K at hv; omega
      rw [split,count_class _ _ _ (pow_pos (Fact.out : p.Prime).pos _)]
      simp [good,v]
    · have hn (t : ℕ) : ¬Hit d r (p^h) y (i+P*t) := (fixed_target_branch p r d hd y i).1 good b t
      simp [hn,good]
  · simp [cop]

#print axioms stable_reduced_target_count


theorem parameterModulus_pos (p : ℕ) [Fact p.Prime] (y : ℤ) (b : ℕ) :
    0 < parameterModulus p y b :=
  Nat.mul_pos (targetPeriod_spec p y).1 (pow_pos (Fact.out : p.Prime).pos _)

#print axioms parameterModulus_pos

/-- The modulus used for the stable count is a period of the full hit predicate. -/
theorem periodic_target_hits (p : ℕ) [Fact p.Prime] (r d : ℕ) (hd : 0<d) (y : ℤ) (b : ℕ) :
    Function.Periodic (Hit d r (p^(testLevel p d y b)) y) (parameterModulus p y b) := by
  let K := targetDepth p y
  let P := targetPeriod p y
  let H := Hit d r (p^(testLevel p d y b)) y
  intro n
  obtain ⟨i,t,hn⟩ : ∃ i t, n=i+P*t := ⟨n%P,n/P,(Nat.mod_add_div ..).symm⟩
  rw [hn]
  change H (i+P*t+P*p^(K+b)) = H (i+P*t)
  rw [show i+P*t+P*p^(K+b) = i+P*(t+p^(K+b)) by ring]
  apply propext
  by_cases good : targetGood p r d y i
  · obtain ⟨_,lift⟩ := (fixed_target_branch p r d hd y i).2 good
    obtain ⟨z,_,hc⟩ := lift b
    let v := companionOrder p (r+d*i)
    have hit (s : ℕ) : H (i+P*s) ↔ s ≡ z [MOD p^(K-v+b)] := hc s
    have eq : t+p^(K+b) ≡ t [MOD p^(K-v+b)] :=
      Nat.add_modEq_left_iff.mpr (pow_dvd_pow p (by omega))
    rw [hit,hit]
    exact ⟨eq.symm.trans,eq.trans⟩
  · have bad (s : ℕ) : ¬H (i+P*s) := (fixed_target_branch p r d hd y i).1 good b s
    exact iff_of_false (bad _) (bad _)

#print axioms periodic_target_hits

/-- One finite count decides whether all prime-power tests admit arbitrarily
large prime parameters, even when the prime or target divides the period. -/
theorem fixed_target_prime_test_iff (p : ℕ) [Fact p.Prime] (r d : ℕ) (hd : 0<d) (y : ℤ) :
    (∀ h B : ℕ, ∃ n>B, n.Prime ∧ Hit d r (p^h) y n) ↔ 0<targetMultiplicity p r d y := by
  constructor
  · intro hits
    let M := parameterModulus p y 0
    obtain ⟨n,hn,prime,hit⟩ := hits (testLevel p d y 0) M
    have cop : n.Coprime M := prime.coprime_iff_not_dvd.mpr
      (Nat.not_dvd_of_pos_of_lt (parameterModulus_pos p y 0) hn)
    rw [← stable_reduced_target_count p r d hd y 0,card_pos]
    refine ⟨n%M,mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt _ (parameterModulus_pos ..)),?_,?_⟩⟩
    · change (n%M).gcd M=1
      rw [← Nat.gcd_rec M n, Nat.gcd_comm]
      exact cop
    · exact ((periodic_target_hits p r d hd y 0).map_mod_nat n).symm ▸ hit
  · intro pos h B
    let M := parameterModulus p y h
    obtain ⟨i,hi⟩ := card_pos.mp ((stable_reduced_target_count p r d hd y h).symm ▸ pos)
    obtain ⟨lt,cop,hit⟩ := mem_filter.mp hi
    have ic : i.Coprime M := cop
    obtain ⟨n,hn,hpr,he⟩ := Nat.forall_exists_prime_gt_and_modEq B (parameterModulus_pos p y h).ne' ic
    have eq : n%M=i := (show n%M=i%M from he).trans (Nat.mod_eq_of_lt (mem_range.mp lt))
    have same := (periodic_target_hits p r d hd y h).map_mod_nat n
    change Hit d r _ y (n%M) = _ at same
    rw [eq] at same
    refine ⟨n,hn,hpr,?_⟩
    have lifted : Hit d r (p^(testLevel p d y h)) y n := same ▸ hit
    apply Int.ModEq.of_dvd _ lifted
    exact_mod_cast pow_dvd_pow p (show h≤testLevel p d y h by dsimp [testLevel]; omega)

#print axioms fixed_target_prime_test_iff

end Arxiv.«2211.10788».LocalPower
