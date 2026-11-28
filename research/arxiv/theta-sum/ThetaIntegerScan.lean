import ThetaHorizontalScan

/-! Integer comparisons with a uniform error allowance for the horizontal phase table. -/
namespace Arxiv.«2501.03234».ThetaIntegerScan
open Finset Filter Real Complex ThetaAdditiveReciprocity ThetaReciprocalMesh ThetaHorizontalTable
open ThetaHorizontalScan ThetaBourgainGaraev ThetaSquareRootWindow
noncomputable section

abbrev Table := ℕ → ℕ → ℤ×ℤ

def scaled (p d j : ℕ) : ℂ := ((2*(resolution p:ℝ):ℝ):ℂ)*row p d (j:ℤ)

def valid (p : ℕ) (α : ℝ) (T : Table) : Prop := ∀ t∈phases (radius p α),
  |(scaled p t.1 t.2).re-((T t.1 t.2).1:ℝ)|≤1 ∧
  |(scaled p t.1 t.2).im-((T t.1 t.2).2:ℝ)|≤1

def rounded (p : ℕ) : Table := fun d j => (⌊(scaled p d j).re⌋,⌊(scaled p d j).im⌋)

theorem valid_rounded (p : ℕ) (α : ℝ) : valid p α (rounded p) := by
  have hf (s : ℝ) : |s-(⌊s⌋:ℝ)|≤1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr (Int.floor_le s))]
    linarith only [Int.lt_floor_add_one s]
  exact fun t _ => ⟨hf _,hf _⟩

private theorem scale_norm (p d j : ℕ) : ‖scaled p d j‖=2*(resolution p:ℝ) := by
  simp [scaled,row]

/-- Each signed integer coordinate of a valid input has magnitude at most 2M+1. -/
theorem entry_bound {p : ℕ} {α : ℝ} {T : Table} (hT : valid p α T)
    {d j : ℕ} (h : (d,j)∈phases (radius p α)) :
    |((T d j).1:ℝ)|≤2*(resolution p:ℝ)+1 ∧ |((T d j).2:ℝ)|≤2*(resolution p:ℝ)+1 := by
  obtain ⟨hr,hi⟩ := hT (d,j) h
  have h₁ := abs_le.mp ((abs_re_le_norm _).trans_eq (scale_norm p d j))
  have h₂ := abs_le.mp ((abs_im_le_norm _).trans_eq (scale_norm p d j))
  obtain ⟨hr₁,hr₂⟩ := abs_le.mp hr
  obtain ⟨hi₁,hi₂⟩ := abs_le.mp hi
  change -(1:ℝ)≤(scaled p d j).re-((T d j).1:ℝ) at hr₁
  change (scaled p d j).re-((T d j).1:ℝ)≤1 at hr₂
  change -(1:ℝ)≤(scaled p d j).im-((T d j).2:ℝ) at hi₁
  change (scaled p d j).im-((T d j).2:ℝ)≤1 at hi₂
  constructor <;> rw [abs_le] <;> constructor <;> linarith only [h₁.1,h₁.2,h₂.1,h₂.2,hr₁,hr₂,hi₁,hi₂]

/-- The test after tabulation uses only two integer prefix sums and their squares. -/
def crossing (T : Table) (n j : ℕ) : Prop :=
  (2*(n:ℤ))^2 < (∑ d∈range n,(T d j).1)^2+(∑ d∈range n,(T d j).2)^2

theorem stable {p n j : ℕ} {α : ℝ} {T : Table} (hT : valid p α T)
    (hm : (n,j)∈checks p α) (hA : alert p n j) : crossing T n j := by
  classical
  obtain ⟨hn,hj⟩ := mem_product.mp hm
  have hn' := (mem_filter.mp hn).2
  let g (d : ℕ) : ℂ := ⟨((T d j).1:ℝ),((T d j).2:ℝ)⟩
  let V := ∑ d∈range n,g d
  let c : ℝ := 2*(resolution p:ℝ)
  have hc : 0≤c := by dsimp [c];positivity
  have hrow (d) (hd : d∈range n) : ‖scaled p d j-g d‖≤2 := by
    obtain ⟨hr,hi⟩ := hT (d,j) (mem_product.mpr ⟨mem_range.mpr ((mem_range.mp hd).trans_le hn'),hj⟩)
    apply (norm_le_abs_re_add_abs_im _).trans
    change |(scaled p d j).re-((T d j).1:ℝ)|+|(scaled p d j).im-((T d j).2:ℝ)|≤2
    linarith only [hr,hi]
  have hE := (norm_sum_le (range n) (fun d => scaled p d j-g d)).trans (sum_le_sum hrow)
  rw [sum_sub_distrib] at hE
  simp only [scaled,←mul_sum,sum_const,card_range,nsmul_eq_mul] at hE
  change ‖(c:ℂ)*horizontal p n (j:ℤ)-V‖≤(n:ℝ)*2 at hE
  have ht := norm_le_norm_add_norm_sub' ((c:ℂ)*horizontal p n (j:ℤ)) V
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hc] at ht
  change 2*(n:ℝ)<(resolution p:ℝ)*‖horizontal p n (j:ℤ)‖ at hA
  have hv : 2*(n:ℝ)<‖V‖ := by dsimp only [c] at ht; linarith only [ht,hA,hE]
  let A := ∑ d∈range n,(T d j).1
  let B := ∑ d∈range n,(T d j).2
  have hR : V.re=(A:ℝ) := by simp only [V,A,g,Complex.re_sum,Int.cast_sum]
  have hI : V.im=(B:ℝ) := by simp only [V,B,g,Complex.im_sum,Int.cast_sum]
  have hnorm := Complex.sq_norm_sub_sq_re V
  rw [hR,hI] at hnorm
  have hs : (2*(n:ℝ))^2<(A:ℝ)^2+(B:ℝ)^2 := by
    have hpos : 0<‖V‖+2*(n:ℝ) := by linarith only [hv,Nat.cast_nonneg (α:=ℝ) n]
    nlinarith only [mul_pos (sub_pos.mpr hv) hpos,hnorm]
  change (2*(n:ℤ))^2<A^2+B^2
  exact_mod_cast hs

/-- Many different prefix lengths cross the integer threshold in every valid table,
including any choice of admissible rounded coordinates on a boundary. -/
theorem witnesses (estimate : InitialSumEstimate) : ∃ b : ℝ, 0<b ∧
    ∀ α : ℝ, 0<α → α<1/3 → ∀ᶠ p : ℕ in atTop, ∀ hp : p.Prime, _root_.Odd p →
      letI : Fact p.Prime := ⟨hp⟩
      CompleteEstimate p → (S p:ℝ)≤(p:ℝ)*Real.log p/100 →
        ∃ G : Finset ℕ, b*ThetaInteriorResonance.weight (Real.log p)≤G.card ∧
          (∀ n∈G, ∃ j : ℕ, (n,j)∈checks p α ∧ ∀ T : Table, valid p α T → crossing T n j) ∧
          ∀ n m : ℕ, n∈G → m∈G → n < m → 3*n≤2*m := by
  obtain ⟨b,hb,H⟩ := ThetaHorizontalScan.many estimate
  refine ⟨b,hb,?_⟩
  intro α ha ha'
  filter_upwards [H α ha ha'] with p hh
  intro hp ho
  let : Fact p.Prime := ⟨hp⟩
  intro hW hS
  obtain ⟨G,hsize,hG,hsep⟩ := hh hp ho hW hS
  refine ⟨G,hsize,?_,hsep⟩
  intro n hn
  obtain ⟨j,hj,hA⟩ := hG n hn
  exact ⟨j,hj,fun T hT => stable hT hj hA⟩

theorem growth (estimate : InitialSumEstimate) (weil : ∀ (p : ℕ) [Fact p.Prime],CompleteEstimate p)
    {α : ℝ} (ha : 0<α) (ha' : α<1/3) (T : ℕ → Table)
    (quiet : ∀ᶠ p : ℕ in atTop, p.Prime → _root_.Odd p →
      valid p α (T p) ∧ ∀ v∈checks p α, ¬crossing (T p) v.1 v.2)
    (n : ℕ) : type_of% (conjecture_4_4 n) := by
  apply ThetaHorizontalScan.growth estimate weil ha ha' _ n
  filter_upwards [quiet] with p h
  intro hp ho v hv hA
  obtain ⟨hT,hq⟩ := h hp ho
  exact hq v hv (stable hT hv hA)

#print axioms witnesses
#print axioms growth

#print axioms valid_rounded
#print axioms entry_bound
#print axioms stable
end
end Arxiv.«2501.03234».ThetaIntegerScan
