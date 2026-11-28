import LucasFibonacciCoprimeProgressionTests

/-! Bounded bilateral parameters and lifting in a prescribed parameter class. -/

namespace Arxiv.«2211.10788».AlmostPrimeClosure
open CongruenceClosure ProgressionClosure

/-- The index bound uses strict growth on both halves of the bilateral orbit. -/
theorem signed_index_bound (z : ℤ) : z.natAbs≤(signed z).natAbs+2 := by
  have U : StrictMono lucasFibonacciSum := fun _ _ h =>
    Nat.add_lt_add_of_le_of_lt (Nat.mul_le_mul_left 2 (Nat.fib_mono h.le)) (Nat.fib_add_two_strictMono h)
  have V : StrictMono lowerNeighborAtAddTwo := fun _ _ h =>
    Nat.add_lt_add_of_lt_of_le (Nat.mul_lt_mul_of_pos_left (Nat.fib_add_two_strictMono h) (by decide))
      (Nat.fib_mono h.le)
  obtain ⟨m,rfl|rfl⟩ := z.eq_nat_or_neg
  · rw [signed_nat]
    simpa using (U.id_le m).trans (Nat.le_add_right _ 2)
  · rcases m with _|_|m
    · decide
    · decide
    · rw [signed_lower]
      change (-((m+2:ℕ):ℤ)).natAbs≤((-1:ℤ)^(m+1)*(lowerNeighborAtAddTwo m:ℤ)).natAbs+2
      simp only [Int.natAbs_neg,Int.natAbs_natCast,Int.natAbs_mul,Int.natAbs_pow,Int.natAbs_one,one_pow,one_mul]
      exact Nat.add_le_add_right (V.id_le m) 2

theorem parameter_bound (r : ℕ) {d : ℕ} (hd : 0<d) (w : ℤ) :
    w.natAbs≤(signed (r+d*w)).natAbs+r+2 := by
  have bd := signed_index_bound ((r:ℤ)+d*w)
  have triangle := Int.natAbs_add_le ((r:ℤ)+d*w) (-(r:ℤ))
  rw [show ((r:ℤ)+d*w)+(-r)=(d:ℤ)*w by ring,Int.natAbs_mul] at triangle
  simp only [Int.natAbs_natCast,Int.natAbs_neg] at triangle
  have := Nat.le_mul_of_pos_left w.natAbs hd
  omega

/-- At each member of the coprime detector family, a modular hit at
parameter t lifts to an integral parameter in the same class modulo D. -/
theorem recover_parameter {d D : ℕ} (hd : 0<d) (hD : 0<D) (r t e : ℕ) (y : ℤ)
    (hit : Hit d r (detector (d*D) y e) y t) :
    ∃ w : ℤ, (t:ℤ) ≡ w [ZMOD D] ∧ signed (r+d*w)=y ∧ w.natAbs≤y.natAbs+r+2 := by
  let a := r+d*t
  have atZero : Hit (d*D) a (detector (d*D) y e) y 0 := by simpa only [Hit,Nat.mul_zero,Nat.add_zero,a] using hit
  obtain ⟨z,cl,_,val⟩ := detector_lifts (Nat.mul_pos hd hD) e atZero
  obtain ⟨v,eq⟩ := cl.dvd
  let w := (t:ℤ)-(D:ℤ)*v
  have same : (t:ℤ) ≡ w [ZMOD D] := Int.modEq_iff_dvd.mpr ⟨-v,by dsimp [w]; ring⟩
  have id : z = r+d*w := by
    change (a:ℤ)-z = (↑(d*D:ℕ):ℤ)*v at eq
    dsimp [a] at eq
    dsimp [w]
    linarith only [eq]
  rw [id] at val
  refine ⟨w,same,val,?_⟩
  simpa only [val] using parameter_bound r hd w

#print axioms signed_index_bound
#print axioms recover_parameter

end Arxiv.«2211.10788».AlmostPrimeClosure
