import Erdos478WindowCollisionEnergy

/-! # Occupancy counts and the collision energy of a factorial window -/

namespace Erdos478.WindowAverage
open Finset LocalSpacing
open scoped Classical
noncomputable section

def prefixMultiplicity (f : ℕ → ℕ) (n y : ℕ) := ((range n).filter fun r => f r=y).card

private theorem count_succ (f : ℕ → ℕ) (n y : ℕ) :
    prefixMultiplicity f (n+1) y=prefixMultiplicity f n y+(if f n=y then 1 else 0) := by
  simp only [prefixMultiplicity,card_filter, sum_range_succ]

private theorem fibre_pairs (f : ℕ → ℕ) (n y : ℕ) :
    (prefixMultiplicity f n y).choose 2=∑ s ∈ range n,if f s=y then prefixMultiplicity f s y else 0 := by
  induction n with
  | zero => simp [prefixMultiplicity]
  | succ n ih =>
    rw [count_succ,sum_range_succ]
    by_cases h : f n=y
    · rw [if_pos h,Nat.choose_succ_succ _ 1,Nat.choose_one_right,← ih,if_pos h]
      ac_rfl
    · simp only [if_neg h,add_zero,ih]

private theorem cost_ineq (m v : ℕ) : m*v≤(m+1).choose 2+v.choose 2 := by
  have square (k : ℕ) : 2*k.choose 2+k=k*k := by
    induction k with
    | zero => decide
    | succ k ih =>
      rw [Nat.choose_succ_succ k 1,Nat.choose_one_right]
      nlinarith
  have a := square (m+1)
  have b := square v
  by_cases h : v≤m
  · nlinarith [Nat.zero_le ((m-v)*(m-v+1)),Nat.sub_add_cancel h]
  · have hv : m+1≤v := by omega
    obtain ⟨r,hr⟩ := Nat.exists_eq_add_of_le hv
    subst v
    nlinarith [Nat.zero_le (r*r)]

/-- Each occupied residue of multiplicity v pays binom(v,2) unordered pairs. -/
theorem occupancy_energy (p a H : ℕ) :
    pairEnergy p a H=∑ y ∈ windowValues p a H,(prefixMultiplicity (fun i => (a+i).factorial%p) (H+1) y).choose 2 := by
  let f (i : ℕ) := (a+i).factorial%p
  have inside {s : ℕ} (hs : s∈range (H+1)) : f s∈windowValues p a H :=
    mem_image.mpr ⟨a+s,mem_Icc.mpr ⟨by omega,by have := mem_range.mp hs; omega⟩,rfl⟩
  change (∑ s ∈ range (H+1),∑ r ∈ range s,if f r=f s then 1 else 0)=_
  simp_rw [fibre_pairs]
  rw [sum_comm (s:=windowValues p a H)]
  apply sum_congr rfl
  intro s hs
  symm
  rw [sum_eq_single (f s)]
  · simp only [prefixMultiplicity,card_filter,f,ite_true]
  · intro y _ ne
    exact if_neg (Ne.symm ne)
  · exact fun no => (no (inside hs)).elim

/-- Every multiplicity gives a linear lower bound for the window image.
The slope parameter can be chosen after the window length is fixed. -/
theorem multiplicity_bound (p a H m : ℕ) :
    m*(H+1)≤(m+1).choose 2*(windowValues p a H).card+pairEnergy p a H := by
  let f (i : ℕ) := (a+i).factorial%p
  have count : H+1=∑ y ∈ windowValues p a H,prefixMultiplicity f (H+1) y := by
    conv_lhs => rw [← card_range (H+1)]
    unfold prefixMultiplicity
    apply card_eq_sum_card_fiberwise (f:=f)
    intro i hi
    exact mem_image.mpr ⟨a+i,mem_Icc.mpr ⟨by omega,by have := mem_range.mp hi; omega⟩,rfl⟩
  calc
    m*(H+1) = ∑ y ∈ windowValues p a H,m*prefixMultiplicity f (H+1) y := by
      conv_lhs => rw [count]
      rw [mul_sum]
    _ ≤ ∑ y ∈ windowValues p a H,((m+1).choose 2+(prefixMultiplicity f (H+1) y).choose 2) :=
      sum_le_sum fun y _ => cost_ineq m _
    _ = _ := by rw [sum_add_distrib,occupancy_energy]; simp [f,Nat.mul_comm]

#print axioms prefixMultiplicity
#print axioms occupancy_energy
#print axioms multiplicity_bound
end
end Erdos478.WindowAverage
