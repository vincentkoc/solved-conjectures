import HosoyaPrimePowerIndices
import LucasFibonacciPrimePowerLifts
import Mathlib.Data.Nat.Periodic

/-! Prime divisor frequencies on translated windows of a fixed Hosoya index progression. -/

namespace Arxiv.«2211.10788».DivisorWindows
open Finset IndexDivisors

/-- A prime actually dividing an upper value on the index progression r+dt. -/
def Hits (r d p : ℕ) : Prop := p.Prime ∧ ∃ t, p ∣ lucasFibonacciSum (r+d*t)

/-- Any divisor prime hits at least once in every block of p+1 parameters. -/
theorem hit_in_each_block {r d p : ℕ} (hp : Hits r d p) (a : ℕ) :
    ∃ j < p+1, p ∣ lucasFibonacciSum (r+d*(a+j)) := by
  obtain ⟨prime,t,hit⟩ := hp
  let : Fact p.Prime := ⟨prime⟩
  let R := fibonacciStepRank p d
  have hr : 0<R := (rank_properties p d).1
  let : NeZero R := ⟨hr.ne'⟩
  let f (i : ℕ) : Prop := p ∣ lucasFibonacciSum (r+d*i)
  have per : Function.Periodic f R := by
    intro i
    apply propext
    change p ∣ lucasFibonacciSum (r+d*(i+R)) ↔ _
    rw [Nat.mul_add,←Nat.add_assoc]
    exact lucasFibonacciSum_dvd_shift_iff (rank_properties p d).2
  let z := (t:ZMod R)-a
  have eq : (a+z.val)%R=t%R := (ZMod.natCast_eq_natCast_iff ..).mp (by simp [z])
  refine ⟨z.val,(ZMod.val_lt _).trans_le (rank_le_prime_add_one d),?_⟩
  change f (a+z.val)
  rw [←per.map_mod_nat (a+z.val),eq,per.map_mod_nat]
  exact hit

private lemma count_blocks (f : ℕ → Prop) [DecidablePred f] {B : ℕ}
    (h : ∀ a, ∃ j < B, f (a+j)) (a H : ℕ) :
    H/B ≤ ((range H).filter fun i => f (a+i)).card := by
  choose j hj hit using h
  let pick (k : ℕ) := B*k+j (a+B*k)
  have upper (k : ℕ) : pick k < B*(k+1) := by
    dsimp [pick]
    simpa only [Nat.mul_succ] using Nat.add_lt_add_left (hj (a+B*k)) (B*k)
  have strict : StrictMono pick := strictMono_nat_of_lt_succ fun k =>
    (upper k).trans_le (Nat.le_add_right _ _)
  have hh := card_le_card_of_injOn (s:=range (H/B)) (t:=(range H).filter fun i => f (a+i))
    pick (fun k hk => by
      have hk' := mem_range.mp hk
      refine mem_filter.mpr ⟨mem_range.mpr ((upper k).trans_le ?_),?_⟩
      · exact (Nat.mul_le_mul_left B hk').trans (Nat.mul_div_le H B)
      · simpa [pick,Nat.add_assoc] using hit (a+B*k)) strict.injective.injOn
  simpa using hh

/-- The sum of distinct prime-factor counts in every interval of H parameters
is at least the sum of floor(H/(p+1)) over any finite family of divisor primes. -/
theorem factor_incidences {r d : ℕ} (S : Finset ℕ) (hS : ∀ p ∈ S, Hits r d p) (a H : ℕ) :
    ∑ p ∈ S, H/(p+1) ≤
      ∑ i ∈ range H, (lucasFibonacciSum (r+d*(a+i))).primeFactors.card := by
  classical
  let U (i : ℕ) := lucasFibonacciSum (r+d*(a+i))
  have pos (i : ℕ) : 0<U i := by
    dsimp [U,lucasFibonacciSum]
    have h := Nat.fib_pos.mpr (by omega : 0<r+d*(a+i)+2)
    omega
  calc
    _ ≤ ∑ p ∈ S, ((range H).filter fun i => p ∣ U i).card := by
      apply sum_le_sum
      intro p hp
      exact count_blocks (fun j => p ∣ lucasFibonacciSum (r+d*j)) (hit_in_each_block (hS p hp)) a H
    _ = ∑ i ∈ range H, (S.filter fun p => p ∣ U i).card := by
      simp only [card_filter]
      exact sum_comm
    _ ≤ _ := by
      apply sum_le_sum
      intro i _
      apply card_le_card
      intro p hp
      obtain ⟨hs,hd⟩ := mem_filter.mp hp
      exact Nat.mem_primeFactors.mpr ⟨(hS p hs).1,hd,(pos i).ne'⟩

#print axioms hit_in_each_block
#print axioms factor_incidences

end Arxiv.«2211.10788».DivisorWindows
