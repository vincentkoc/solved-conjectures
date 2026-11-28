import Erdos722IntegralDesignCriterion

/-!
# The signed index spectrum in every rank

A constant integer incidence vector has exactly the binomial divisibility
conditions of the Steiner problem when the index is one. The index of the
complete design is a period of the admissible indices.
-/

namespace Erdos722.IntegralDesign
open Finset
variable {α : Type*} [DecidableEq α]

def Conditions (v r k l : ℕ) : Prop :=
  ∀ i<r, (k-i).choose (r-i) ∣ l*(v-i).choose (r-i)

def Multiplicities (V : Finset α) (r k l : ℕ) : Prop :=
  ∃ w : Finset α → ℕ, ∀ A∈V.powersetCard r, (∑ B∈(V.powersetCard k).filter (A⊆·), w B)=l

theorem constant_incidence (V I : Finset α) (r : ℕ) (l : ℤ) (hI : I⊆V) (hi : I.card≤r) :
    incidence V r (fun _ => l) I = (((V.card-I.card).choose (r-I.card) : ℕ) : ℤ)*l := by
  rw [incidence,sum_const,nsmul_eq_mul,card_filter_powersetCard_subset _ _ _ hI hi]

theorem admissible_constant (V : Finset α) {r k l : ℕ} (hr : r≤V.card) :
    Admissible V r k (fun _ => (l:ℤ)) ↔ Conditions V.card r k l := by
  constructor
  · intro H i hi
    obtain ⟨I,hI,hc⟩ := exists_subset_card_eq (s:=V) (n:=i) (by omega)
    have h := H I hI (by omega)
    rw [constant_incidence _ _ _ _ hI (by omega),hc,mul_comm] at h
    exact_mod_cast h
  · intro H I hI hi
    rw [constant_incidence _ _ _ _ hI hi,mul_comm]
    by_cases h : I.card=r
    · simp [h]
    · exact_mod_cast H I.card (by omega)

theorem signed_index_iff (V : Finset α) {r k : ℕ} (hrk : r≤k) (hv : k+r≤V.card) (l : ℕ) :
    (∃ w, Represents V r k (fun _ => (l:ℤ)) w) ↔ Conditions V.card r k l :=
  (signed_criterion V r k hrk hv _).trans (admissible_constant V (by omega))

theorem conditions_of_multiplicities {V : Finset α} {r k l : ℕ} (hr : r≤V.card)
    (h : Multiplicities V r k l) : Conditions V.card r k l := by
  obtain ⟨w,hw⟩ := h
  apply (admissible_constant V hr).mp
  apply admissible_of_represents (w:=fun B => (w B:ℤ))
  intro A hA
  change (∑ B∈(V.powersetCard k).filter (A⊆·), (w B:ℤ))=(l:ℤ)
  rw [← Nat.cast_sum,hw A hA]

theorem complete_conditions (V : Finset α) {r k : ℕ} (hrk : r≤k) (hr : r≤V.card) :
    Conditions V.card r k ((V.card-r).choose (k-r)) := by
  apply conditions_of_multiplicities hr
  refine ⟨fun _ => 1,fun A hA => ?_⟩
  obtain ⟨hV,hc⟩ := mem_powersetCard.mp hA
  simp [card_filter_powersetCard_subset _ _ _ hV (hc ▸ hrk),hc]

theorem conditions_mod {v r k C l : ℕ} (hC : Conditions v r k C) (hl : Conditions v r k l) :
    Conditions v r k (l%C) := by
  intro i hi
  let N := (v-i).choose (r-i)
  let K := (k-i).choose (r-i)
  have hd : K ∣ (C*N)*(l/C) := dvd_mul_of_dvd_left (hC i hi) _
  have he : l*N=(l%C)*N+(C*N)*(l/C) := by
    calc
      _ = ((l%C)+C*(l/C))*N := by rw [Nat.mod_add_div]
      _ = _ := by ring
  exact (Nat.dvd_add_left hd).mp (he ▸ hl i hi)

#print axioms signed_index_iff
#print axioms conditions_of_multiplicities
#print axioms conditions_mod
end Erdos722.IntegralDesign
