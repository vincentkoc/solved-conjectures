import Erdos478ConsecutiveReturnPairs
import Erdos478ReturnCapacitySums
import Erdos478QuotientCubicPacking
import Erdos478PrescribedQuotientRoots

/-! # The quotient values between successive selected factorials -/

namespace Erdos478.QuotientSpacing
open Finset ReturnConcentration
open scoped Classical
noncomputable section

/-- Count every consecutive pair, even when its two factorial residues differ. -/
def adjacentQuotients (p : ℕ) (A : Finset ℕ) :=
  (links A).image fun e => quotient p e.1 e.2

theorem link_capacity {p : ℕ} (hp : p.Prime) (A : Finset ℕ) (fits : A ⊆ Ico 1 p)
    (k : ℕ) (hk : 0<k) :
    ((links A).filter (fun e => e.2-e.1=k)).card ≤ (adjacentQuotients p A).card*k := by
  apply le_trans _ (quotient_capacity hp hk (adjacentQuotients p A))
  apply card_le_card_of_injOn Prod.fst
  · intro e he
    obtain ⟨link,gap⟩ := mem_filter.mp he
    obtain ⟨left,right,lt⟩ := links_mem link
    have eq : e.1+k=e.2 := by omega
    have hw := mem_Ico.mp (fits right)
    exact mem_filter.mpr ⟨mem_Ico.mpr ⟨(mem_Ico.mp (fits left)).1,by omega⟩,
      eq ▸ mem_image_of_mem _ link⟩
  · rintro ⟨i,j⟩ he ⟨a,b⟩ hf eq
    have g := (mem_filter.mp he).2
    have h := (mem_filter.mp hf).2
    have u := (links_mem (mem_filter.mp he).1).2.2
    have v := (links_mem (mem_filter.mp hf).1).2.2
    change i=a at eq
    change j-i=k at g
    change b-a=k at h
    exact Prod.ext eq (by change i<j at u; change a<b at v; omega)

/-- Replicating each return m times charges integral degree capacities even
when the effective capacity per gap is a half-integer. -/
theorem packing {α : Type*} (s : Finset α) (g : α → ℕ) (C m : ℕ)
    (hC : 0<C) (hm : 0<m) (positive : ∀ e∈s,0<g e)
    (bounds : ∀ k, m*(s.filter (fun e => g e=k)).card ≤ C*k) :
    8*m*s.card^3≤9*C*(∑ e ∈ s,g e)^2 := by
  classical
  let copies := s ×ˢ (univ : Finset (Fin m))
  have count (k : ℕ) : (copies.filter (fun e => g e.1=k)).card=m*(s.filter (fun e => g e=k)).card := by
    have eq : copies.filter (fun e => g e.1=k)=(s.filter (fun e => g e=k)) ×ˢ (univ : Finset (Fin m)) := by
      ext e
      simp [copies]
    rw [eq,card_product,card_univ,Fintype.card_fin,mul_comm]
  have length : s.card≤∑ e ∈ s,g e := by
    calc
      _ = ∑ _ ∈ s,(1:ℕ) := by simp
      _ ≤ _ := sum_le_sum positive
  apply weighted_capacity_bound _ _ _ _ hC hm length
  intro h hh
  have b := cutoff copies (fun e => g e.1) (fun k => C*k) (fun k => (count k) ▸ bounds k) h
  have mass : (∑ e ∈ copies,g e.1)=m*∑ e ∈ s,g e := by simp [copies,sum_product,mul_sum]
  rw [mass,show copies.card=s.card*m by simp [copies]] at b
  have short : (∑ k ∈ range h,(h-k)*(C*k))=C*∑ k ∈ range h,(h-k)*k := by
    rw [mul_sum]
    exact sum_congr rfl fun k _ => by ring
  rw [short] at b
  have eq := degree_cost h
  nlinarith [Nat.mul_le_mul_left 6 b,congrArg (fun z : ℕ => C*z) eq]

theorem adjacent_quotient_bound {p : ℕ} (hp : p.Prime) (A : Finset ℕ) (fits : A⊆Ico 1 p) :
    8*(A.card-1)^3≤9*(adjacentQuotients p A).card*(width A)^2 := by
  by_cases h : (links A).Nonempty
  · have nonempty : (adjacentQuotients p A).Nonempty := h.image _
    have cap (k : ℕ) : 1*((links A).filter (fun e => e.2-e.1=k)).card≤(adjacentQuotients p A).card*k := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · have empty : (links A).filter (fun e => e.2-e.1=0)=∅ := by
          apply eq_empty_iff_forall_notMem.mpr
          intro e he
          obtain ⟨he,eq⟩ := mem_filter.mp he
          have lt := (links_mem he).2.2
          omega
        simp [empty]
      · simpa only [one_mul] using link_capacity hp A fits k hk
    simpa only [mul_one,links_card,links_sum] using
      packing (links A) (fun e => e.2-e.1) _ 1 (card_pos.mpr nonempty) (by decide)
        (fun e he => Nat.sub_pos_of_lt (links_mem he).2.2) cap
  · have z := (links_card A).symm.trans (card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp h))
    simp [z]

#print axioms adjacentQuotients
#print axioms link_capacity
#print axioms packing
#print axioms adjacent_quotient_bound
end
end Erdos478.QuotientSpacing
