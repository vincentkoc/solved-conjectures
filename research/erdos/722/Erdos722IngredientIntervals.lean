import Erdos722AffineIngredients
import Mathlib.Algebra.Order.Ring.Int

/-!
# Finite intervals of group counts

Two independent choices between adjacent heights translate every initial
design by a rectangular family of displacements. Dividing by the block
size leaves two coprime generators for a numerical semigroup.
-/

namespace Erdos722.PairDesign
open Erdos722.Quartet

private theorem fan {k s : ℕ} (hpp : IsPrimePow k) (hk : 2≤k)
    (hs : Adjacent k s) (hpos : 0<s) (hd : k ∣ s) (B n : ℕ) :
    ∃ C, k ∣ C ∧ ∀ i ≤ n, ∀ x ≤ B, Local k x → Local k (C+s*i+x) := by
  induction n with
  | zero => exact ⟨0,dvd_zero _,by simp_all⟩
  | succ n ih =>
    obtain ⟨C,hC,h⟩ := ih
    obtain ⟨T,hT,hA,D₀,D₁⟩ := adjacent_heights hpp hk s (C+s*n+B) hpos
    refine ⟨s*T+C,dvd_add (dvd_mul_of_dvd_left hd _) hC,?_⟩
    intro i hi x hx hL
    by_cases hin : i ≤ n
    · have hr : C+s*i+x ≤ T := le_trans (by gcongr) hT
      have hg := grow hk D₀ hs hr (show 0≤1 by decide)
        (by simpa using hA.1) (by simpa using h i hin x hx hL)
      simpa only [Nat.add_zero,Nat.add_assoc] using hg
    · have hi' : i=n+1 := by omega
      subst i
      have hr : C+s*n+x ≤ T+1 := by omega
      have hg := grow hk D₁ hs hr (show 0≤1 by decide)
        (by simpa using hA.2) (by simpa using h n le_rfl x hx hL)
      convert hg using 1
      ring

private theorem initial {k z : ℕ} (hk : 2≤k) (hz : z≤1) : Local k z := by
  rcases (by omega : z=0 ∨ z=1) with rfl | rfl
  · change Has (· = k) ((k-1)*0+1)
    simp only [Nat.mul_zero,Nat.zero_add]
    exact ⟨Cover.empty (fun x y hxy _ => hxy (Subsingleton.elim x y))⟩
  · exact Has.single (by omega)

theorem seed_interval {k m g : ℕ} (hpp : IsPrimePow k) (hk : 2≤k)
    (hm : 0<m) (hg : 0<g) (hcop : m.Coprime g)
    (h₁ : Adjacent k (k*m)) (h₂ : Adjacent k (k*g)) (W : ℕ) :
    ∃ L ≥ W, ∀ u, L ≤ u → u ≤ L+W → u%k ≤ 1 → Local k u := by
  let P := m*g+W
  let n := P+W
  obtain ⟨C,hC,f⟩ := fan hpp hk h₁ (by positivity) (dvd_mul_right ..) 1 n
  obtain ⟨E,hE,h⟩ := fan hpp hk h₂ (by positivity) (dvd_mul_right ..) (C+(k*m)*n+1) n
  have hk' : 0<k := by omega
  have hP : W ≤ k*P := calc
    W ≤ P := Nat.le_add_left ..
    _ ≤ k*P := by simpa using Nat.mul_le_mul_right P (by omega : 1 ≤ k)
  refine ⟨E+C+k*P,by omega,?_⟩
  intro u hlu hhu ha
  let v := u-(E+C)
  have he : E+C+v=u := by dsimp [v]; omega
  let q := v/k
  let z := v%k
  have hz : z≤1 := by
    rw [← he,Nat.add_mod,Nat.mod_eq_zero_of_dvd (dvd_add hE hC),Nat.zero_add,Nat.mod_mod] at ha
    exact ha
  have hq : P ≤ q := (Nat.le_div_iff_mul_le hk').mpr (by rw [Nat.mul_comm]; omega)
  have hqn : q ≤ n := by
    apply Nat.le_of_lt_succ
    apply (Nat.div_lt_iff_lt_mul hk').mpr
    have hW : W ≤ W*k := Nat.le_mul_of_pos_right _ hk'
    dsimp [n]
    nlinarith only [hhu,he,hW,hk']
  have hpred : m.pred*g.pred ≤ q :=
    (Nat.mul_le_mul (Nat.pred_le _) (Nat.pred_le _)).trans ((Nat.le_add_right ..).trans hq)
  obtain ⟨i,j,eq⟩ := Nat.exists_add_mul_eq_of_gcd_dvd_of_mul_pred_le m g q
    (by rw [hcop.gcd_eq_one]; exact one_dvd _) hpred
  have hi : i≤n := by have := Nat.le_mul_of_pos_right i hm; omega
  have hj : j≤n := by have := Nat.le_mul_of_pos_right j hg; omega
  have hx : C+(k*m)*i+z≤C+(k*m)*n+1 := by gcongr
  have H := h j hj _ hx (f i hi z hz (initial hk hz))
  have hdiv : z+k*q=v := Nat.mod_add_div _ _
  convert H using 1
  nlinarith only [he,hdiv,congrArg (k*·) eq]

#print axioms seed_interval
end Erdos722.PairDesign
