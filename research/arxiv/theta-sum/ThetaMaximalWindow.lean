import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

/-! A finite one-sided maximal inequality for variable-length integer windows. -/
namespace Arxiv.«2501.03234».ThetaMaximalWindow
open Finset
noncomputable section

/-- Each exceptional starting integer can choose its own positive window length.
Scanning from the left gives the weak-type bound with constant one. -/
theorem count (f : ℕ → ℝ) (hf : ∀ p, 0≤f p) {c : ℝ} (hc : 0≤c)
    {s : Finset ℕ} {L U : ℕ} (hL : ∀ n∈s, L≤n)
    (h : ∀ n∈s, ∃ H : ℕ, 0<H ∧ n+H≤U ∧ c*H≤∑ p∈Ioc n (n+H), f p) :
    c*s.card≤∑ p∈Ioc L U, f p := by
  classical
  induction s using Finset.strongInductionOn generalizing L with | _ s ih =>
  by_cases hs : s.Nonempty
  · let n := s.min' hs
    have hn : n∈s := s.min'_mem _
    obtain ⟨H,hH,hU,hcost⟩ := h n hn
    let t := s.filter (fun j => n+H≤j)
    have ht : t⊂s := (ssubset_iff_of_subset (filter_subset ..)).mpr
      ⟨n,hn,fun hh => by have := (mem_filter.mp hh).2; omega⟩
    have hrest := ih t ht (L:=n+H) (fun j hj => (mem_filter.mp hj).2)
      (fun j hj => h j (mem_filter.mp hj).1)
    have hb : s.filter (fun j => ¬n+H≤j) ⊆ Ico n (n+H) := by
      intro j hj
      obtain ⟨hj,hj'⟩ := mem_filter.mp hj
      exact mem_Ico.mpr ⟨s.min'_le _ hj,lt_of_not_ge hj'⟩
    have hb' := card_le_card hb
    simp only [Nat.card_Ico,Nat.add_sub_cancel_left] at hb'
    have hpartition := card_filter_add_card_filter_not (s:=s) (fun j => n+H≤j)
    have hcard : s.card≤H+t.card := by change _≤H+(s.filter _).card; omega
    have hd : Disjoint (Ioc n (n+H)) (Ioc (n+H) U) := disjoint_left.mpr (by
      intro j h1 h2; exact (not_lt_of_ge (mem_Ioc.mp h1).2) (mem_Ioc.mp h2).1)
    have hu : Ioc n (n+H) ∪ Ioc (n+H) U ⊆ Ioc L U := by
      intro j hj
      rcases mem_union.mp hj with h1|h2
      · exact mem_Ioc.mpr ⟨(hL n hn).trans_lt (mem_Ioc.mp h1).1,(mem_Ioc.mp h1).2.trans hU⟩
      · exact mem_Ioc.mpr ⟨((hL n hn).trans (Nat.le_add_right ..)).trans_lt (mem_Ioc.mp h2).1,(mem_Ioc.mp h2).2⟩
    calc
      c*s.card ≤ c*(H+t.card:ℕ) := mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) hc
      _ = c*H+c*t.card := by push_cast;ring
      _ ≤ _ := (add_le_add hcost hrest).trans (by
        rw [←sum_union hd]; exact sum_le_sum_of_subset_of_nonneg hu (fun p _ _ => hf p))
  · rw [not_nonempty_iff_eq_empty.mp hs]
    simpa using sum_nonneg (s:=Ioc L U) (fun p _ => hf p)

#print axioms count

end
end Arxiv.«2501.03234».ThetaMaximalWindow
