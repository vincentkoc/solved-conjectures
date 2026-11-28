import Erdos478SexticCoordinateCounts
import Erdos478FactorialEndpointCounts
import Mathlib.Data.Nat.Prime.Factorial

/-!
# All primes and the positive factorial endpoints at separation six

The prime 17 gives a fixed reflection coordinate. At 719 the root 6
would have lower index zero. Each prime has a unique positive endpoint.
-/

namespace Erdos478.SexticGap
open Polynomial Finset SplittingDensity
noncomputable section

/-- A short falling factorial suffices to test equality of the two factorials. -/
theorem endpoints_eq_short_product {p : ℕ} (hp : p.Prime) (k : ℕ) :
    endpoints k p=(Ico (k+1) p).filter (fun j => j.descFactorial k % p=1) := by
  ext j
  simp only [endpoints,mem_filter]
  apply and_congr_right
  intro hj
  obtain ⟨hl,hu⟩ := mem_Ico.mp hj
  have hc := hp.coprime_factorial_of_lt (show j-k<p by omega)
  have hm : 1%p=1 := Nat.mod_eq_of_lt hp.one_lt
  rw [← Nat.factorial_mul_descFactorial (show k≤j by omega)]
  constructor
  · intro he
    have h : 1 ≡ j.descFactorial k [MOD p] := Nat.ModEq.cancel_left_of_coprime hc
      (by simpa only [Nat.ModEq,mul_one] using he)
    simpa only [Nat.ModEq,hm] using h.symm
  · intro he
    have h : 1 ≡ j.descFactorial k [MOD p] := by simpa only [Nat.ModEq,hm] using he.symm
    simpa only [Nat.ModEq,mul_one] using h.mul_left (j-k).factorial

private theorem cast_prime_ne_zero {p q : ℕ} [h : Fact p.Prime] (hq : q.Prime) (hpq : p≠q) :
    (q : ZMod p)≠0 := fun hz => hpq ((Nat.prime_dvd_prime_iff_eq h.out hq).mp
      ((CharP.cast_eq_zero_iff (ZMod p) p q).mp hz))

private theorem boundary {p : ℕ} (hp : p.Prime) (h : p≠719) : (6:ℕ).factorial%p≠1 := by
  intro he
  have hh : 1 ≡ 720 [MOD p] := by
    simpa only [Nat.ModEq,Nat.mod_eq_of_lt hp.one_lt,show (6:ℕ).factorial=720 by decide] using he.symm
  exact h ((Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 719)).mp
    ((Nat.modEq_iff_dvd' (by decide : 1≤720)).mp hh))

private theorem count_as_coordinates {p : ℕ} [hpr : Fact p.Prime]
    (h₂ : (2:ZMod p)≠0) (h719 : p≠719) :
    (endpoints 6 p).card=(univ.filter (fun s : ZMod p => (cub (ZMod p)).toPoly.eval (s^2)=0)).card := by
  classical
  let φ (x : ZMod p) := 2*x-5
  have h64 : (64:ZMod p)≠0 := by
    rw [show (64:ZMod p)=2^6 by norm_num]; exact pow_ne_zero _ h₂
  have hφ (j : ℕ) : (cub (ZMod p)).toPoly.eval ((φ (j:ZMod p))^2)=0 ↔ j.descFactorial 6%p=1 := by
    rw [gap_transform,descPochhammer_eval_eq_descFactorial,mul_eq_zero,or_iff_right h64,sub_eq_zero]
    have he := ZMod.natCast_eq_natCast_iff' (j.descFactorial 6) 1 p
    simpa only [Nat.cast_one,Nat.mod_eq_of_lt hpr.out.one_lt] using he
  apply Finset.card_bij (fun (j : ℕ) _ => φ (j:ZMod p))
  · intro j hj
    rw [endpoints_eq_short_product hpr.out] at hj
    exact mem_filter.mpr ⟨mem_univ _,(hφ j).mpr (mem_filter.mp hj).2⟩
  · intro i hi j hj he
    have hh : (i:ZMod p)=j := mul_left_cancel₀ h₂ (sub_left_inj.mp he)
    have hi' := (mem_Ico.mp (mem_filter.mp hi).1).2
    have hj' := (mem_Ico.mp (mem_filter.mp hj).1).2
    simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt hi',Nat.mod_eq_of_lt hj'] using congrArg ZMod.val hh
  · intro s hs
    let x := (s+5)/2
    have he : φ x=s := by dsimp [φ,x]; field_simp; ring
    have hy : (FallingGap.gap (ZMod p) 6).IsRoot x := by
      have ht := gap_transform x
      rw [show 2*x-5=s from he,(mem_filter.mp hs).2] at ht
      simpa [FallingGap.gap,IsRoot] using (mul_eq_zero.mp ht.symm).resolve_left h64
    obtain ⟨hle,hrep⟩ := FallingGap.endpoints_of_root hy
    have hlt : 6<x.val := by
      apply lt_of_le_of_ne hle
      rintro e
      rw [← e,Nat.sub_self,Nat.factorial_zero,Nat.mod_eq_of_lt hpr.out.one_lt] at hrep
      exact boundary hpr.out h719 hrep.symm
    exact ⟨x.val,mem_filter.mpr ⟨mem_Ico.mpr ⟨hlt,x.val_lt⟩,hrep⟩,by simpa using he⟩

set_option maxRecDepth 10000 in
private theorem special_endpoints :
    endpoints 6 2=∅ ∧ endpoints 6 17={11} ∧ endpoints 6 19={8,16} ∧
      endpoints 6 103={46,62} ∧ endpoints 6 719={718} := by
  rw [endpoints_eq_short_product (by decide : Nat.Prime 2),
    endpoints_eq_short_product (by decide : Nat.Prime 17),endpoints_eq_short_product (by decide : Nat.Prime 19),
    endpoints_eq_short_product (by decide : Nat.Prime 103),endpoints_eq_short_product (by norm_num : Nat.Prime 719)]
  decide

/-- The only exceptional positive endpoint counts occur at 17 and 719.
The listed endpoints use the actual interval `1 ≤ j-6 < j < p`. -/
theorem sextic_endpoints_all_primes {p : ℕ} (hp : p.Prime) :
    if p=17 then endpoints 6 p={11} else if p=719 then endpoints 6 p={718} else
      (endpoints 6 p).card=0 ∨ (endpoints 6 p).card=2 ∨ (endpoints 6 p).card=6 := by
  obtain ⟨h2,h17,h19,h103,h719⟩ := special_endpoints
  split_ifs with ha hb
  · simpa [ha] using h17
  · simpa [hb] using h719
  let : Fact p.Prime := ⟨hp⟩
  by_cases hc : p=2
  · simp [hc,h2]
  by_cases hd : p=19
  · simp [hd,h19]
  by_cases he : p=103
  · simp [he,h103]
  have hn : (2:ZMod p)≠0 := cast_prime_ne_zero Nat.prime_two hc
  rw [count_as_coordinates hn hb]
  apply coordinate_counts _ (fun x => by simp) hn (cast_prime_ne_zero (by decide : Nat.Prime 17) ha)
  rw [show (1957:ZMod p)=19*103 by norm_num]
  exact mul_ne_zero (cast_prime_ne_zero (by decide : Nat.Prime 19) hd)
    (cast_prime_ne_zero (by decide : Nat.Prime 103) he)

#print axioms endpoints_eq_short_product
#print axioms sextic_endpoints_all_primes
end
end Erdos478.SexticGap
