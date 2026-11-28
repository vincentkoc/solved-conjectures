import ThetaProgressionIncidence

/-! Simultaneous occupancy bounds for all selected residue classes on an interval. -/
namespace Arxiv.«2501.03234».ThetaProgressionOccupancy
open Finset Real ThetaProgressionIncidence
noncomputable section

def weight (u : ℕ) (a : ℕ → ℕ) (q j : ℕ) : ℝ := if (u+j)%q=a q then 1 else 0
def visits (u Q : ℕ) (a : ℕ → ℕ) (j : ℕ) := ∑ q∈Icc 1 Q,weight u a q j

theorem energy (u H Q : ℕ) (a : ℕ → ℕ) :
    ∑ j∈range (H+1),(visits u Q a j)^2 ≤ H*(harmonicSum Q)^3+(Q:ℝ)^2 := by
  let I := Icc 1 Q
  let J := range (H+1)
  have hpair (q d : ℕ) : ∑ j∈J,weight u a q j*weight u a d j = ((pair u H q d (a q) (a d)).card:ℝ) := by
    rw [←mul_one (((pair u H q d (a q) (a d)).card):ℝ),←nsmul_eq_mul,←sum_const,pair,sum_filter]
    apply sum_congr rfl;intro j _
    simp only [weight];split_ifs <;> simp_all
  have he : ∑ j∈J,(visits u Q a j)^2 = ∑ q∈I,∑ d∈I,((pair u H q d (a q) (a d)).card:ℝ) := by
    simp only [visits,sq,sum_mul,mul_sum,I]
    rw [sum_comm];apply sum_congr rfl;intro q _
    rw [sum_comm];exact sum_congr rfl (fun d _ => by simpa only [mul_comm] using hpair q d)
  rw [he]
  calc _ ≤ ∑ q∈I,∑ d∈I,((H:ℝ)/(q.lcm d)+1) := sum_le_sum (fun q hq =>
            sum_le_sum (fun d hd => pair_count u H q d _ _ (mem_Icc.mp hq).1 (mem_Icc.mp hd).1))
       _ = H*(∑ q∈I,∑ d∈I,((q.lcm d:ℕ):ℝ)⁻¹)+(Q:ℝ)^2 := by
           simp [sum_add_distrib,div_eq_mul_inv,mul_sum,I,sq]
       _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (lcm_sum Q) (Nat.cast_nonneg H)) le_rfl

def occupancy (E : Finset ℕ) (u Q : ℕ) (a : ℕ → ℕ) :=
  ∑ q∈Icc 1 Q,((E.filter (fun j => (u+j)%q=a q)).card:ℝ)

theorem bound {E : Finset ℕ} {u H Q : ℕ} (hE : E ⊆ range (H+1)) (a : ℕ → ℕ) :
    (occupancy E u Q a)^2 ≤ E.card*(H*(harmonicSum Q)^3+(Q:ℝ)^2) := by
  have he : occupancy E u Q a = ∑ j∈E,visits u Q a j := by
    unfold occupancy visits
    rw [sum_comm];apply sum_congr rfl;intro q _
    simp [weight,sum_boole]
  have hcs := sum_mul_sq_le_sq_mul_sq E (fun _ => (1:ℝ)) (visits u Q a)
  simp only [one_mul,one_pow,sum_const,nsmul_eq_mul,mul_one] at hcs
  rw [he]
  exact hcs.trans (mul_le_mul_of_nonneg_left
    ((sum_le_sum_of_subset_of_nonneg hE (fun j _ _ => sq_nonneg _)).trans (energy u H Q a)) (Nat.cast_nonneg _))

#print axioms energy
#print axioms bound
end
end Arxiv.«2501.03234».ThetaProgressionOccupancy
