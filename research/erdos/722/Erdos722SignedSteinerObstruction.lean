import Erdos722SteinerWeights

/-!
# A signed Steiner system with no nonnegative realization

Fix an s-subset of a block and an exterior point. Each of the remaining
block vertices gives a distinct block through that stem and the point.
Counting such blocks gives an obstruction beyond divisibility at index one.
-/

namespace Erdos722.IntegralDesign
open Finset

private theorem flag_count {n r k : ℕ} {H : Finset (Finset (Fin n))} (hH : H.IsBlockDesign r k)
    (I : Finset (Fin n)) (hi : I.card≤r) :
    (k-I.card).choose (r-I.card)*(H.filter (I⊆·)).card=(n-I.card).choose (r-I.card) := by
  classical
  let V := (univ : Finset (Fin n))
  let w (B : Finset (Fin n)) : ℤ := if B∈H then 1 else 0
  have he : ((V.powersetCard k).filter (I⊆·)).filter (·∈H)=H.filter (I⊆·) := by
    ext B
    simp only [V,mem_filter,mem_powersetCard,subset_univ,true_and]
    exact ⟨fun h => ⟨h.2,h.1.2⟩,fun h => ⟨⟨hH.1 B h.1,h.2⟩,h.1⟩⟩
  have h : incidence V k w I=((H.filter (I⊆·)).card:ℤ) := by
    simp only [incidence,w,← sum_filter,he,sum_const,nsmul_eq_mul,mul_one]
  have D := incidence_incidence (k:=k) V I hi w
  rw [incidence_congr (design_weights hH),constant_incidence V I r 1 (subset_univ I) hi,h,mul_one] at D
  have hv : V.card=n := by simp [V]
  rw [hv] at D
  exact_mod_cast D.symm

/-- For rank s+2, deletion of an s-point stem leaves the elementary
exterior-point bound for a pair design. -/
theorem exterior_point_bound {n s k : ℕ} (hsk : s+2≤k) (hkn : k<n)
    {H : Finset (Finset (Fin n))} (hH : H.IsBlockDesign (s+2) k) :
    (k-(s+1))*(k-s) ≤ n-(s+1) := by
  classical
  obtain ⟨A,_,hAr⟩ := exists_subset_card_eq (s:=(univ : Finset (Fin n))) (n:=s+2) (by simp; omega)
  obtain ⟨B,⟨hB,_⟩,_⟩ := hH.2 A hAr
  have hBk := hH.1 B hB
  obtain ⟨X,hXB,hX⟩ := exists_subset_card_eq (s:=B) (n:=s) (by omega)
  have hne : (univ\B).Nonempty := card_pos.mp (by rw [card_sdiff_of_subset (subset_univ B),card_univ,Fintype.card_fin]; omega)
  obtain ⟨o,ho'⟩ := hne
  have ho := (mem_sdiff.mp ho').2
  have hoX : o∉X := fun h => ho (hXB h)
  let J := insert o X
  have hJ : J.card=s+1 := by rw [show J=insert o X from rfl,card_insert_of_notMem hoX,hX]
  let L := B\X
  let P := H.filter (J⊆·)
  have triple (j : L) : (insert j.val J).card=s+2 := by
    have h : j.val∉J := by
      rw [show J=insert o X from rfl,mem_insert]
      exact not_or.mpr ⟨fun he => ho (he ▸ (mem_sdiff.mp j.property).1),(mem_sdiff.mp j.property).2⟩
    rw [card_insert_of_notMem h,hJ]
  choose f hf using fun j : L => (hH.2 (insert j.val J) (triple j)).exists
  have hP (j : L) : f j∈P := mem_filter.mpr ⟨(hf j).1,(subset_insert ..).trans (hf j).2⟩
  have hinj : Function.Injective f := by
    intro i j he
    by_contra hij
    have hv : i.val≠j.val := fun h => hij (Subtype.ext h)
    have hi := mem_sdiff.mp i.property
    have hj := mem_sdiff.mp j.property
    let T := insert i.val (insert j.val X)
    have hT : T.card=s+2 := by simp [T,card_insert_of_notMem,hv,hi.2,hj.2,hX]
    have hB' : T⊆B := insert_subset hi.1 (insert_subset hj.1 hXB)
    have iF : i.val∈f i := (hf i).2 (mem_insert_self ..)
    have jF : j.val∈f i := he ▸ (hf j).2 (mem_insert_self ..)
    have hXF : X⊆f i := (subset_insert o X).trans (mem_filter.mp (hP i)).2
    have hF : T⊆f i := insert_subset iF (insert_subset jF hXF)
    have eq := (hH.2 T hT).unique ⟨(hf i).1,hF⟩ ⟨hB,hB'⟩
    exact ho (eq ▸ (mem_filter.mp (hP i)).2 (mem_insert_self ..))
  have hle := Fintype.card_le_of_injective (fun j : L => (⟨f j,hP j⟩ : P))
    (fun i j h => hinj (congrArg Subtype.val h))
  rw [Fintype.card_coe,Fintype.card_coe,show L=B\X from rfl,card_sdiff_of_subset hXB,hX,hBk] at hle
  have ht := flag_count hH J (by omega)
  rw [hJ,show s+2-(s+1)=1 by omega,Nat.choose_one_right,Nat.choose_one_right] at ht
  exact (Nat.mul_le_mul_left (k-(s+1)) hle).trans_eq ht

/-- The binomial tests for S(3,7,22) have an integral solution. Its
nonnegative analogue would require six distinct blocks where there are four. -/
theorem signed_separation :
    (∃ w, Represents (univ : Finset (Fin 22)) 3 7 (fun _ => 1) w) ∧
    ¬∃ H : Finset (Finset (Fin 22)), H.IsBlockDesign 3 7 := by
  constructor
  · apply (signed_steiner_iff 22 3 7 (by decide) (by decide)).mpr
    intro i hi
    interval_cases i <;> decide
  · rintro ⟨H,hH⟩
    have h := exterior_point_bound (s:=1) (by decide : 1+2≤7) (by decide : 7<22) hH
    omega

#print axioms exterior_point_bound
#print axioms signed_separation
end Erdos722.IntegralDesign
