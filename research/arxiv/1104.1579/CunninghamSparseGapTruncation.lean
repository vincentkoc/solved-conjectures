import CunninghamCoefficientEnergy
import Mathlib.RingTheory.PowerSeries.Trunc

/-! A bounded coefficient weight forces a dyadic gap in two polynomial truncations. -/

namespace CunninghamChain.LargeGap
open Polynomial CoefficientEnergy Finset

lemma energy_nonneg (P : ℤ[X]) (m : ℕ) : 0 ≤ energy P m :=
  sum_nonneg (fun i _ => sq_nonneg (P.coeff i))

lemma energy_mono (P : ℤ[X]) {m n : ℕ} (h : m ≤ n) : energy P m ≤ energy P n :=
  sum_le_sum_of_subset_of_nonneg (range_mono h) (fun i _ _ => sq_nonneg (P.coeff i))

lemma weight_of_extra (P : ℤ[X]) {m n i : ℕ} (lo : m ≤ i) (hi : i < n) :
    energy P m+(P.coeff i)^2 ≤ energy P n := by
  have ni : i ∉ range m := by simpa using lo
  rw [add_comm,energy,←sum_insert (f:=fun j => (P.coeff j)^2) ni]
  exact sum_le_sum_of_subset_of_nonneg (insert_subset (mem_range.mpr hi) (range_mono (by omega)))
    (fun j _ _ => sq_nonneg (P.coeff j))

/-- Some annulus [m,2m) between b and b·2^(w+1) is empty in both polynomials
when their total coefficient weight up to the last endpoint is at most w. -/
theorem common_dyadic_gap (P Q : ℤ[X]) (b w : ℕ)
    (bound : energy P (b*2^(w+1))+energy Q (b*2^(w+1)) ≤ w) :
    ∃ m, b ≤ m ∧ 2*m ≤ b*2^(w+1) ∧ ∀ i, m ≤ i → i < 2*m → P.coeff i=0 ∧ Q.coeff i=0 := by
  let M (j : ℕ) := b*2^j
  let E (j : ℕ) := energy P (M j)+energy Q (M j)
  have double (j : ℕ) : M (j+1)=2*M j := by dsimp [M]; rw [pow_succ]; ring
  have mono : Monotone M := fun _ _ h => Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) h)
  have equal : ∃ j ≤ w, E j=E (j+1) := by
    by_contra! no
    have grow (j : ℕ) (hj : j ≤ w+1) : (j:ℤ) ≤ E j := by
      induction j with
      | zero => simp only [Nat.cast_zero,E]; exact add_nonneg (energy_nonneg ..) (energy_nonneg ..)
      | succ j ih =>
        have up : E j ≤ E (j+1) := add_le_add (energy_mono P (mono (by omega))) (energy_mono Q (mono (by omega)))
        have ne := no j (by omega)
        have := ih (by omega)
        push_cast
        omega
    have bad := grow (w+1) le_rfl
    change E (w+1) ≤ (w:ℤ) at bound
    omega
  obtain ⟨j,hj,he⟩ := equal
  refine ⟨M j,(show b=M 0 by simp [M]) ▸ mono (Nat.zero_le j),
    (double j).symm ▸ mono (by omega : j+1 ≤ w+1),?_⟩
  intro i lo hi
  rw [←double] at hi
  have p := weight_of_extra P lo hi
  have q := weight_of_extra Q lo hi
  dsimp only [E] at he
  have he' : (P.coeff i)^2+(Q.coeff i)^2 ≤ 0 := by linarith
  constructor <;> nlinarith only [he',sq_nonneg (P.coeff i),sq_nonneg (Q.coeff i)]

noncomputable abbrev cut (P : ℤ[X]) (m : ℕ) := PowerSeries.trunc m (P:PowerSeries ℤ)

lemma cut_coeff (P : ℤ[X]) (m i : ℕ) :
    (cut P m).coeff i=if i < m then P.coeff i else 0 := by
  simp only [cut,PowerSeries.coeff_trunc,Polynomial.coeff_coe]

lemma cut_double (P : ℤ[X]) {m : ℕ} (gap : ∀ i, m ≤ i → i < 2*m → P.coeff i=0) :
    cut P (2*m)=cut P m := by
  ext i
  rw [cut_coeff,cut_coeff]
  split_ifs <;> first | rfl | exact gap i (by omega) (by omega) | omega

/-- The product of the two low pieces equals the entire small endpoint
polynomial once the two empty annuli separate it from the high terms. -/
theorem exact_low_product (P Q c : ℤ[X]) {m : ℕ} (hm : 0 < m) (dc : c.natDegree < 2*m)
    (hp : ∀ i, m ≤ i → i < 2*m → P.coeff i=0) (hq : ∀ i, m ≤ i → i < 2*m → Q.coeff i=0)
    (low : ∀ i < 2*m, (P*Q).coeff i=c.coeff i) : cut P m*cut Q m=c := by
  have deg (A : ℤ[X]) : (cut A m).natDegree < m := by
    obtain ⟨s,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
    exact PowerSeries.natDegree_trunc_lt _ _
  have dprod : (cut P m*cut Q m).natDegree < 2*m :=
    (natDegree_mul_le ..).trans_lt (by have := deg P; have := deg Q; omega)
  have ht : cut (P*Q) (2*m)=c := by
    ext i
    rw [cut_coeff]
    split_ifs with h
    · exact low i h
    · exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm
  calc _ = cut (cut P m*cut Q m) (2*m) := (PowerSeries.trunc_coe_eq_self dprod).symm
       _ = cut (P*Q) (2*m) := by
         rw [←cut_double P hp,←cut_double Q hq]
         simp only [cut,Polynomial.coe_mul,PowerSeries.trunc_trunc_mul_trunc]
       _ = _ := ht

#print axioms common_dyadic_gap
#print axioms exact_low_product

end CunninghamChain.LargeGap
