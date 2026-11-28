import HosoyaPowerClassFactors

/-! Count the windows where a private prime fails to detect a prescribed exponent. -/

namespace Arxiv.«2211.10788».PowerGaps

open Finset HosoyaNeighbor
open scoped Classical

/-- Removing these primes leaves only divisors unique within H steps on both diagonals. -/
def excluded (S : Finset ℕ) (H : ℕ) := S ∪ (shiftDetProduct H).primeFactors

def detected (S : Finset ℕ) (H k : ℕ) (s : HosoyaNeighbor) (n : ℕ) : Prop :=
  ∃ q∈(s.value n).primeFactors, q∉excluded S H ∧ ¬k ∣ (s.value n).factorization q

/-- Every modulus between two and K is detected at each site in the window. -/
def goodWindow (S : Finset ℕ) (H K n : ℕ) : Prop :=
  ∀ s : HosoyaNeighbor, ∀ j≤H, ∀ k : ℕ, 2≤k → k≤K → detected S H k s (n+j)

private theorem translated (S : Finset ℕ) (H a r j : ℕ) (s : HosoyaNeighbor) {k : ℕ} (hk : 2≤k) :
    ((Ico a (a+16*2^r)).filter (fun n => ¬detected S H k s (n+j))).card ≤
      k^(excluded S H).card*(16+32*k*r) := by
  let E := excluded S H
  let P (i : ℕ) := ∀ p∈(s.value i).primeFactors, p∉E → k∣(s.value i).factorization p
  apply le_trans _ (exceptional_factor_orders s E (a+j) r hk)
  apply card_le_card_of_injOn (fun n : ℕ => n+j) (t:=(Ico (a+j) (a+j+16*2^r)).filter P)
  · intro n hn
    obtain ⟨inRange,bad⟩ := mem_filter.mp hn
    obtain ⟨lo,hi⟩ := mem_Ico.mp inRange
    change n+j ∈ (Ico (a+j) (a+j+16*2^r)).filter P
    exact mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega,by omega⟩,fun p hp out =>
      by_contra fun miss => bad ⟨p,hp,out,miss⟩⟩
  · intro i _ j _ eq;simpa using eq

/-- A uniform upper bound for all translated sampling intervals. For fixed H,
K and excluded primes the exceptional count grows at most logarithmically. -/
theorem window_exception_bound (S : Finset ℕ) (a r H K : ℕ) :
    ((Ico a (a+16*2^r)).filter (fun n => ¬goodWindow S H K n)).card ≤
      (H+1)*K*(2*(K^(excluded S H).card*(16+32*K*r))) := by
  let I := Ico a (a+16*2^r)
  let R := Ico 2 (K+1)
  let E (s : HosoyaNeighbor) (j k : ℕ) := I.filter (fun n => ¬detected S H k s (n+j))
  let C := K^(excluded S H).card*(16+32*K*r)
  have each (s : HosoyaNeighbor) (j k : ℕ) (hk : k∈R) : (E s j k).card ≤ C := by
    have kk := mem_Ico.mp hk
    refine (translated S H a r j s kk.1).trans ?_
    dsimp [C]
    have le : k≤K := by omega
    gcongr
  let A (j k : ℕ) := E .upper j k ∪ E .lower j k
  let B (j : ℕ) := R.biUnion (A j)
  have bk (j : ℕ) : (B j).card ≤ K*(2*C) := by
    calc
      _ ≤ ∑ k∈R,(A j k).card := card_biUnion_le
      _ ≤ ∑ _∈R, 2*C := by
        apply sum_le_sum
        intro k hk
        exact (card_union_le ..).trans (by have := each .upper j k hk;have := each .lower j k hk;omega)
      _ ≤ _ := by simp [R];gcongr;omega
  have sub : I.filter (fun n => ¬goodWindow S H K n) ⊆ (range (H+1)).biUnion B := by
    intro n hn
    obtain ⟨mem,bad⟩ := mem_filter.mp hn
    unfold goodWindow at bad
    push Not at bad
    obtain ⟨s,j,jle,k,kl,kr,fail⟩ := bad
    refine mem_biUnion.mpr ⟨j,mem_range.mpr (by omega),mem_biUnion.mpr ⟨k,mem_Ico.mpr ⟨kl,by omega⟩,?_⟩⟩
    cases s with
    | upper => exact mem_union_left _ (mem_filter.mpr ⟨mem,fail⟩)
    | lower => exact mem_union_right _ (mem_filter.mpr ⟨mem,fail⟩)
  calc
    _ ≤ _ := card_le_card sub
    _ ≤ ∑ j∈range (H+1), (B j).card := card_biUnion_le
    _ ≤ ∑ _∈range (H+1), K*(2*C) := sum_le_sum fun j _ => bk j
    _ = _ := by simp [C,Nat.mul_assoc]

#print axioms window_exception_bound
end Arxiv.«2211.10788».PowerGaps
