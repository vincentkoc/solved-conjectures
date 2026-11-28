import Erdos722CyclotomicIncidences

/-!
# Shifts with too few differences in a given class

Every slope stabilizing a difference class contributes the same incidence
count for each shift. Restricting the second moment to those slopes bounds
the number of shifts that see less than half the mean.
-/

namespace Erdos722.Cyclotomy
open Finset
open scoped Classical
variable {F : Type*} [Field F] [Fintype F]

noncomputable def neighbors (D S : Finset F) (b : F) : Finset F :=
  S.filter fun y => y-b ∈ D

omit [Fintype F] in
theorem hits_one (D S : Finset F) (b : F) :
    hits D S 1 b = (neighbors D S b).card := by
  classical
  unfold hits neighbors
  apply Finset.card_bij (fun z _ => z+b)
  · intro z hz
    apply mem_filter.mpr
    exact ⟨by simpa using (mem_filter.mp hz).2,by simpa using (mem_filter.mp hz).1⟩
  · intro x _ y _ h
    exact add_right_cancel h
  · intro y hy
    obtain ⟨hy,hz⟩ := mem_filter.mp hy
    exact ⟨y-b,mem_filter.mpr ⟨hz,by simpa⟩,by simp⟩

theorem sparse_shifts (D S U B : Finset F) (hU : U.card = D.card)
    (stable : ∀ a ∈ U, ∀ b, hits D S a b = hits D S 1 b)
    (small : ∀ b ∈ B, 2*Fintype.card F*(neighbors D S b).card ≤ D.card*S.card) :
    B.card*D.card^2*S.card ≤ 4*(Fintype.card F)^3 := by
  let q : ℝ := Fintype.card F
  let s : ℝ := S.card
  let d : ℝ := D.card
  let E (t : F × F) := (q*hits D S t.1 t.2-d*s)^2
  have total : ∑ t, E t = d*q^2*s*(q-s) := incidence_second_moment D S
  by_cases hd : D.card=0
  · simp [hd]
  by_cases hs : S.card=0
  · simp [hs]
  have hd' : 0<d := by dsimp [d]; exact_mod_cast Nat.pos_of_ne_zero hd
  have hs' : 0<s := by dsimp [s]; exact_mod_cast Nat.pos_of_ne_zero hs
  have bound (t : F × F) (ht : t ∈ U ×ˢ B) : (d*s)^2 ≤ 4*E t := by
    obtain ⟨ha,hb⟩ := mem_product.mp ht
    have h : 2*q*hits D S t.1 t.2 ≤ d*s := by
      rw [stable _ ha, hits_one]
      dsimp [q,d,s]
      exact_mod_cast small _ hb
    have ht' : d*s ≤ 2*(d*s-q*hits D S t.1 t.2) := by linarith
    have hl := pow_le_pow_left₀ (mul_nonneg hd'.le hs'.le) ht' 2
    dsimp [E]
    nlinarith only [hl]
  have hh : (B.card:ℝ)*d*(d*s)^2 ≤ 4*(d*q^2*s*(q-s)) := calc
    _ = ∑ _t ∈ U ×ˢ B, (d*s)^2 := by
      rw [sum_const,card_product,hU,nsmul_eq_mul,Nat.cast_mul]
      dsimp [d]; ring
    _ ≤ ∑ t ∈ U ×ˢ B, 4*E t := sum_le_sum bound
    _ ≤ ∑ t, 4*E t := sum_le_sum_of_subset_of_nonneg (subset_univ _) (by
      intro t _ _; exact mul_nonneg (by norm_num) (sq_nonneg _))
    _ = _ := by rw [← Finset.mul_sum,total]
  have endBound : (B.card:ℝ)*d^2*s ≤ 4*q^3 := by
    apply le_of_mul_le_mul_right (a := d*s) _ (mul_pos hd' hs')
    calc
      _ = (B.card:ℝ)*d*(d*s)^2 := by ring
      _ ≤ _ := hh
      _ ≤ 4*q^3*(d*s) := by
        have := mul_nonneg (show 0 ≤ d*q^2 by positivity) (sq_nonneg s)
        nlinarith only [this]
  dsimp [d,s,q] at endBound
  exact_mod_cast endBound

#print axioms hits_one
#print axioms sparse_shifts

end Erdos722.Cyclotomy
