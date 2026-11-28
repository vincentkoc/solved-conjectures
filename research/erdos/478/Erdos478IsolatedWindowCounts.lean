import Erdos478WindowImageLoss

/-! # Counting the exceptional starts exactly when repeated pairs are isolated -/

namespace Erdos478.WindowAverage
open Finset LocalSpacing
open scoped Classical
noncomputable section

private theorem offsets_pair {p a H r s : ℕ} (hr : r∈range s) (hs : s∈range (H+1))
    (he : (a+r).factorial%p=(a+s).factorial%p) : Repetition p a H (a+r) (a+s) := by
  have := mem_range.mp hr
  have := mem_range.mp hs
  exact ⟨by omega,by omega,by omega,he⟩

theorem isolated_energy {p a H : ℕ} (hp : p.Prime) (inside : a+H<p)
    (cut : (H+2)^(H^2)<p) : pairEnergy p a H=if _ : hasRepetition p a H then 1 else 0 := by
  unfold pairEnergy
  by_cases hit : hasRepetition p a H
  · rw [dif_pos hit]
    obtain ⟨i,j,w⟩ := hit
    obtain ⟨ai,ij,jH,he⟩ := w
    have same {r s : ℕ} (hr : r∈range s) (hs : s∈range (H+1))
        (h : (a+r).factorial%p=(a+s).factorial%p) : r=i-a ∧ s=j-a := by
      have eq := unique_repetition hp inside cut (offsets_pair hr hs h) ⟨ai,ij,jH,he⟩
      obtain ⟨e1,e2⟩ := Prod.mk.inj eq
      omega
    have mj : j-a∈range (H+1) := mem_range.mpr (by omega)
    have mi : i-a∈range (j-a) := mem_range.mpr (by omega)
    rw [sum_eq_single (j-a)]
    · rw [sum_eq_single (i-a)]
      · rw [show a+(i-a)=i by omega,show a+(j-a)=j by omega,if_pos he]
      · intro r hr ne
        exact if_neg (fun eq => ne (same hr mj eq).1)
      · exact fun no => (no mi).elim
    · intro s hs ne
      exact sum_eq_zero fun r hr => if_neg (fun eq => ne (same hr hs eq).2)
    · exact fun no => (no mj).elim
  · rw [dif_neg hit]
    exact sum_eq_zero fun s hs => sum_eq_zero fun r hr => if_neg (fun eq => hit ⟨_,_,offsets_pair hr hs eq⟩)

/-- For a fixed span and a sufficiently large prime, the number of windows with
any loss equals the total number of unordered pair incidences over those windows. -/
theorem isolated_count {p H : ℕ} (hp : p.Prime) (cut : (H+2)^(H^2)<p) :
    (exceptionalStarts p H 1).card=∑ a ∈ starts p H,pairEnergy p a H := by
  rw [exceptionalStarts,card_filter]
  apply sum_congr rfl
  intro a ha
  have h := (mem_starts.mp ha).2
  rw [isolated_energy hp h cut,loss,window_card_exact hp h cut]
  split <;> simp

/-- An explicit finite condition guarantees at least one positive interval
with all H+1 factorial residues distinct. -/
theorem exists_injective_window {p H : ℕ} (hp : p.Prime) (fits : H+1<p)
    (budget : (H+2).choose 3<p-1) :
    ∃ a∈starts p H, (windowValues p a H).card=H+1 := by
  have h := exceptional_starts_bound hp H 1
  have lt : (exceptionalStarts p H 1).card<(starts p H).card := by rw [starts_card]; omega
  obtain ⟨a,ha,miss⟩ := exists_mem_notMem_of_card_lt_card lt
  have zero : loss p a H=0 := by
    by_contra! pos
    exact miss (mem_filter.mpr ⟨ha,by omega⟩)
  have hi : (windowValues p a H).card≤H+1 := by
    apply card_image_le.trans
    rw [Nat.card_Icc]
    omega
  exact ⟨a,ha,by unfold loss at zero; omega⟩

#print axioms isolated_energy
#print axioms isolated_count
#print axioms exists_injective_window
end
end Erdos478.WindowAverage
