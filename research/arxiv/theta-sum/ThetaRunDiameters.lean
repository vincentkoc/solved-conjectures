import ThetaPrimeRuns

/-! Total diameters of runs of consecutive elements of an ordered finite set. -/
namespace Arxiv.«2501.03234».ThetaRunDiameters
open Finset ThetaPrimeRuns
noncomputable section
local instance (P : Prop) : Decidable P := Classical.propDecidable _

/-- Position relative to X of the i-th element in increasing order, using H
past the end of a set in [X,X+H]. -/
def offset (A : Finset ℕ) (X H i : ℕ) :=
  if hi : i<A.card then A.orderEmbOfFin rfl ⟨i,hi⟩-X else H

def span (A : Finset ℕ) (X H L i : ℕ) := offset A X H (i+(L-1))-offset A X H i

def boundedStarts (A : Finset ℕ) (X H L : ℕ) (bad : ℕ → Prop) (D : ℝ) :=
  (starts A L bad).filter (fun i => (span A X H L i:ℝ)≤D)

theorem actual {A : Finset ℕ} {X H L i : ℕ} {bad : ℕ → Prop} (hL : 1≤L)
    (hA : ∀ p∈A,X≤p) (hi : i∈starts A L bad) :
    ∃ (f l : Fin A.card), (f:ℕ)=i ∧ (l:ℕ)=i+(L-1) ∧
      span A X H L i = A.orderEmbOfFin rfl l-A.orderEmbOfFin rfl f := by
  have hr := mem_range.mp (mem_filter.mp hi).1
  have hf : i<A.card := by omega
  have hl : i+(L-1)<A.card := by omega
  refine ⟨⟨_,hf⟩,⟨_,hl⟩,rfl,rfl,?_⟩
  simp only [span,offset,dif_pos hf,dif_pos hl]
  have h := hA _ (orderEmbOfFin_mem A rfl ⟨i,hf⟩)
  omega

theorem sum_span (A : Finset ℕ) (X H L : ℕ) (hA : ∀ p∈A,p≤X+H) :
    (∑ i∈range A.card,span A X H L i)≤(L-1)*H := by
  let f := offset A X H
  have hb (i : ℕ) : f i≤H := by
    dsimp only [f,offset]
    split_ifs with hi
    · have h := hA _ (orderEmbOfFin_mem A rfl ⟨i,hi⟩);omega
    · exact le_rfl
  have hm : Monotone f := by
    intro i j hij
    by_cases hj : j<A.card
    · have hi : i<A.card := hij.trans_lt hj
      dsimp only [f,offset]
      rw [dif_pos hi,dif_pos hj]
      exact Nat.sub_le_sub_right ((A.orderEmbOfFin rfl).monotone (show (⟨i,hi⟩:Fin A.card)≤⟨j,hj⟩ from hij)) _
    · change f i≤offset A X H j
      simpa only [offset,dif_neg hj] using hb i
  let l := L-1
  have ht := sum_range_add f A.card l
  have hu := sum_range_add f l A.card
  rw [Nat.add_comm l A.card] at hu
  have hh : (∑ i∈range l,f (A.card+i))≤l*H := by simpa using
    (sum_le_sum (s:=range l) fun i _ => hb (A.card+i))
  have he : (∑ i∈range A.card,span A X H L i)+(∑ i∈range A.card,f i)=∑ i∈range A.card,f (l+i) := by
    rw [←sum_add_distrib]
    apply sum_congr rfl
    intro i _
    change f (i+l)-f i+f i=f (l+i)
    rw [Nat.sub_add_cancel (hm (Nat.le_add_right i l)),Nat.add_comm]
  change _≤l*H
  omega

/-- At most (L-1)H/D starts in an interval of length H have diameter above D.
The estimate applies after restriction to uninterrupted good runs. -/
theorem lost (A : Finset ℕ) (X H L : ℕ) (bad : ℕ → Prop) {D : ℝ}
    (hL : 1≤L) (hA : ∀ p∈A,p≤X+H) :
    D*((starts A L bad).card-(boundedStarts A X H L bad D).card:ℝ)≤(L:ℝ)*H := by
  classical
  let S := starts A L bad
  let C := boundedStarts A X H L bad D
  let E := S \ C
  have hC : C⊆S := filter_subset ..
  have he : (E.card:ℝ)=(S.card:ℝ)-C.card := by
    rw [show E.card=S.card-C.card from card_sdiff_of_subset hC,Nat.cast_sub (card_le_card hC)]
  have hE : E⊆range A.card := by
    intro i hi
    have h := mem_range.mp (mem_filter.mp (mem_sdiff.mp hi).1).1
    exact mem_range.mpr (by omega)
  have h := sum_le_sum (s:=E) (fun i hi => (show D≤(span A X H L i:ℝ) by
    obtain ⟨hs,hc⟩ := mem_sdiff.mp hi
    exact le_of_lt (lt_of_not_ge (fun hh => hc (mem_filter.mpr ⟨hs,hh⟩)))))
  rw [sum_const,nsmul_eq_mul] at h
  change D*((S.card:ℝ)-C.card)≤_
  rw [←he,mul_comm D]
  apply h.trans
  apply (sum_le_sum_of_subset_of_nonneg hE (fun i _ _ => Nat.cast_nonneg (span A X H L i))).trans
  exact_mod_cast (sum_span A X H L hA).trans (Nat.mul_le_mul_right H (Nat.sub_le L 1))

#print axioms actual
#print axioms lost
end
end Arxiv.«2501.03234».ThetaRunDiameters
