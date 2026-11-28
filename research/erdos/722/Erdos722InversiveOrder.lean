import Erdos722ProjectiveDeletion

/-!
# Divisibility at the inversive-plane order

At rank three the square boundary passes all the binomial tests, even if
the plane forced by the ordinary design does not exist.
-/

namespace Erdos722.InversiveOrder
open Finset IntegralDesign MinimumOrder

private theorem choose_factor {u v a d : ℕ} (h : u.descFactorial a=v.descFactorial a*d) :
    u.choose a=v.choose a*d := by
  apply Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos a)
  simpa only [Nat.descFactorial_eq_factorial_mul_choose,Nat.mul_assoc] using h

/-- The three replication numbers are q(q²+1), q(q+1) and q+1. -/
theorem square_tests {q : ℕ} (hq : 2≤q) :
    ∀ i<3, (q+1-i).choose (3-i) ∣ (q^2+1-i).choose (3-i) := by
  obtain ⟨b,rfl⟩ := Nat.exists_eq_add_of_le hq
  let q := 2+b
  have hq₂ : q+1-2=b+1 := by dsimp [q]; omega
  have hv₂ : q^2+1-2=(b+1)*(b+3) := by
    have : q^2=(b+1)*(b+3)+1 := by dsimp [q]; ring
    omega
  intro i hi
  change (q+1-i).choose (3-i) ∣ (q^2+1-i).choose (3-i)
  interval_cases i
  · refine ⟨q*(q^2+1),choose_factor ?_⟩
    simp only [Nat.sub_zero,Nat.descFactorial_succ,Nat.descFactorial_zero,mul_one,hq₂,hv₂,
      Nat.add_sub_cancel]
    dsimp [q]
    ring
  · refine ⟨q*(q+1),choose_factor ?_⟩
    norm_num only [show 3-1=2 by decide,Nat.descFactorial_succ,Nat.descFactorial_zero,mul_one,
      Nat.sub_zero,Nat.sub_sub]
    rw [hv₂,hq₂,Nat.add_sub_cancel,Nat.add_sub_cancel]
    dsimp [q]
    ring
  · refine ⟨q+1,?_⟩
    norm_num [hv₂,hq₂,q]
    omega

theorem square_signed_separation {q : ℕ} (hq : 2≤q) (hn : ¬PlaneOfOrder q) :
    (∃ w, Represents (univ : Finset (Fin (q^2+1))) 3 (q+1) (fun _ => 1) w) ∧
      ¬∃ H : Finset (Finset (Fin (q^2+1))), H.IsBlockDesign 3 (q+1) := by
  refine ⟨(signed_steiner_iff _ _ _ (by omega) (by nlinarith [Nat.mul_self_le_mul_self hq])).mpr
    (square_tests hq),?_⟩
  rintro ⟨H,hH⟩
  exact hn (plane_of_square_design hq 1 hH)

theorem square_cutoff_of_no_plane {q N : ℕ} (hq : 2≤q) (hn : ¬PlaneOfOrder q)
    (h : ∀ n≥N, (∀ i<3, (q+1-i).choose (3-i) ∣ (n-i).choose (3-i)) →
      ∃ H : Finset (Finset (Fin n)), H.IsBlockDesign 3 (q+1)) : q^2+1<N := by
  by_contra! he
  exact (square_signed_separation hq hn).2 (h _ he (square_tests hq))

theorem mod_nine_obstruction {q : ℕ} (h : q%9=3 ∨ q%9=6) : ¬ ∃ a b : ℕ, q=a^2+b^2 := by
  have sq (x : ℕ) : x^2%9=0 ∨ x^2%9=1 ∨ x^2%9=4 ∨ x^2%9=7 := by
    rw [Nat.pow_mod]
    have hlt := Nat.mod_lt x (by decide : 0<9)
    interval_cases x%9 <;> decide
  rintro ⟨a,b,rfl⟩
  simp only [Nat.add_mod (a^2) (b^2)] at h
  rcases sq a with ha|ha|ha|ha <;> rcases sq b with hb|hb|hb|hb <;> omega

private theorem admissible_before_77 :
    ∀ v : Fin 77, 37<v.val → ¬ ∀ i : Fin 3, (7-i.val).choose (3-i.val) ∣
      (v.val-i.val).choose (3-i.val) := by decide

theorem seven_lower_of_no_six (hn : ¬PlaneOfOrder 6) {v : ℕ} (hv : 7<v)
    {H : Finset (Finset (Fin v))} (hH : H.IsBlockDesign 3 7) : 77≤v := by
  have h := triple_square_lower (by decide : 3<7) hv (by decide) (by decide) (by decide) hH
  have hne : v≠37 := by
    rintro rfl
    exact hn (plane_of_square_design (q:=6) (by decide) 1 hH)
  by_contra! hlt
  apply admissible_before_77 ⟨v,hlt⟩ (by norm_num at h; simpa using (show 37<v by omega))
  intro i
  exact ((signed_steiner_iff v 3 7 (by decide) hv.le).mp ⟨_,design_weights hH⟩) i.val i.isLt

#print axioms square_tests
#print axioms square_signed_separation
#print axioms square_cutoff_of_no_plane
#print axioms mod_nine_obstruction
#print axioms seven_lower_of_no_six
end Erdos722.InversiveOrder
