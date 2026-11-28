import HosoyaRepeatedClassBound
import LucasFibonacciIsolatedDivisors

/-! Logarithmically many terms can occupy one prescribed power class in any interval. -/

namespace Arxiv.«2211.10788».PowerGaps
open Finset
open scoped Classical

private lemma positive (s : HosoyaNeighbor) (i : ℕ) : 0<s.value i := by
  have low := s.supportBounds.lower i
  by_contra! h
  rw [Nat.eq_zero_of_le_zero h] at low
  simp at low

/-- Two members of a common kth-power class with indices congruent modulo
2k must be separated by at least a quarter of the later index, up to 8. -/
theorem class_spacing (s : HosoyaNeighbor) {i j k d : ℕ} (lt : i<j) (hk : 2≤k)
    (modEq : i ≡ j [MOD 2*k]) (hi : ∃ y, s.value i=d*y^k) (hj : ∃ z, s.value j=d*z^k) :
    j≤4*(j-i)+8 := by
  obtain ⟨y,yi⟩ := hi
  obtain ⟨z,zj⟩ := hj
  obtain ⟨h,he⟩ := (Nat.modEq_iff_dvd' lt.le).mp modEq
  have hp : 0<h := by by_contra! zero;rw [Nat.eq_zero_of_le_zero zero,mul_zero] at he;omega
  have dp : 0<d := by
    have := positive s i
    by_contra! hd;rw [Nat.eq_zero_of_le_zero hd,zero_mul] at yi;omega
  have base {x n : ℕ} (eq : s.value n=d*x^k) : 0<x := by
    have := positive s n
    by_contra! hx
    rw [Nat.eq_zero_of_le_zero hx,zero_pow (by omega : k≠0),mul_zero] at eq
    omega
  obtain ⟨t,kt⟩ := Nat.exists_eq_add_of_le hk
  have ex : t+2=k := by omega
  have dg : 2*h*(t+2)=j-i := by rw [ex,he];ring
  have endpt : i+2*h*(t+2)=j := by omega
  have bound := repeated_class_bound s.value s.value_step dp (base yi) (base zj) hp t
    (by simpa [ex] using yi) (by rw [endpt,ex];exact zj)
  rw [endpt,dg] at bound
  have norm : |(s.value 1:ℝ)^2 - s.value 1*s.value 0 - (s.value 0:ℝ)^2|=11 := by
    cases s <;> norm_num [HosoyaNeighbor.value,lowerNeighborAtAddTwo,lucasFibonacciSum]
  rw [norm] at bound
  have sz : s.value j ≤ Nat.fib (j-i)^2*11 := by exact_mod_cast bound
  have top : s.value j ≤ 2^(2*(j-i)+4) := by
    calc
      _ ≤ Nat.fib (j-i)^2*11 := sz
      _ ≤ (2^(j-i))^2*2^4 := Nat.mul_le_mul (Nat.pow_le_pow_left (fib_le_two_pow _) _) (by decide)
      _ = _ := by rw [←pow_mul,←pow_add];congr 1;omega
  have lower := s.supportBounds.lower j
  have out := lower.trans (Nat.pow_le_pow_left top 2)
  rw [←pow_mul] at out
  have := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp out
  omega

private noncomputable def hits (s : HosoyaNeighbor) (d k a L : ℕ) : Finset ℕ :=
  (Ico a (a+L)).filter fun n => ∃ y, s.value n=d*y^k

private theorem short_block (s : HosoyaNeighbor) (d : ℕ) {k L a : ℕ} (hk : 2≤k) (lp : 0<L)
    (far : 16*L≤a) : (hits s d k a L).card ≤ 2*k := by
  have inj : Set.InjOn (fun n : ℕ => n%(2*k)) (hits s d k a L) := by
    have no {i j : ℕ} (hi : i∈hits s d k a L) (hj : j∈hits s d k a L)
        (lt : i<j) (eq : i%(2*k)=j%(2*k)) : False := by
      obtain ⟨a1,p1⟩ := mem_filter.mp hi
      obtain ⟨a2,p2⟩ := mem_filter.mp hj
      have b1 := mem_Ico.mp a1
      have b2 := mem_Ico.mp a2
      have := class_spacing s lt hk eq p1 p2
      omega
    intro i hi j hj eq
    rcases lt_trichotomy i j with lt|eq'|gt
    · exact (no hi hj lt eq).elim
    · exact eq'
    · exact (no hj hi gt eq.symm).elim
  have card := card_le_card_of_injOn (t:=range (2*k)) (fun n : ℕ => n%(2*k))
    (fun i _ => mem_range.mpr (Nat.mod_lt _ (by omega))) inj
  simpa using card

private theorem split (s : HosoyaNeighbor) (d k a L R : ℕ) :
    (hits s d k a (L+R)).card ≤ (hits s d k a L).card+(hits s d k (a+L) R).card := by
  unfold hits
  rw [←Nat.add_assoc a L R,←Ico_union_Ico_eq_Ico (a:=a) (b:=a+L) (c:=a+L+R) (by omega) (by omega),
    filter_union]
  exact card_union_le ..

private theorem blocks (s : HosoyaNeighbor) (d : ℕ) {k L a : ℕ} (hk : 2≤k) (lp : 0<L)
    (far : 16*L≤a) (m : ℕ) : (hits s d k a (m*L)).card ≤ m*(2*k) := by
  induction m with
  | zero => simp [hits]
  | succ m ih =>
    rw [Nat.succ_mul,Nat.succ_mul]
    refine (split s d k a (m*L) L).trans (Nat.add_le_add ih ?_)
    exact short_block s d hk lp (by omega)

/-- Uniform over the multiplier, interval location and choice of diagonal. -/
theorem power_class_block_bound (s : HosoyaNeighbor) (d a r : ℕ) {k : ℕ} (hk : 2≤k) :
    ((Ico a (a+16*2^r)).filter fun n => ∃ y, s.value n=d*y^k).card ≤ 16+32*k*r := by
  change (hits s d k a (16*2^r)).card≤_
  induction r with
  | zero =>
    have le := card_le_card (filter_subset (fun n => ∃ y, s.value n=d*y^k) (Ico a (a+16*2^0)))
    simpa [hits] using le
  | succ r ih =>
    have ex : 16*2^(r+1)=16*2^r+16*2^r := by rw [pow_succ];ring
    rw [ex,Nat.mul_succ]
    have second := blocks s d hk (show 0<2^r by positivity) (a:=a+16*2^r) (by omega) 16
    have sum := (split s d k a (16*2^r) (16*2^r)).trans (Nat.add_le_add ih second)
    omega

#print axioms class_spacing
#print axioms power_class_block_bound
end Arxiv.«2211.10788».PowerGaps
