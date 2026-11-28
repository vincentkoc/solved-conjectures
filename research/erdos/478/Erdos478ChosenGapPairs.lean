import Erdos478EvenGapReflection

/-!
# Choosing representatives of the reflected even-gap roots

The reflection on a separable even gap has no fixed root in odd
characteristic. Its roots can be indexed in pairs with the two entries
related by the original affine reflection.
-/

namespace Erdos478.EffectiveResolvent
open Polynomial Finset

private theorem pair_indices {r : ℕ} (σ : Fin (2*r) → Fin (2*r))
    (hinv : Function.Involutive σ) (hfree : ∀ i, i ≠ σ i) :
    ∃ v : Fin r × Bool ↪ Fin (2*r), ∀ i, v (i,true) = σ (v (i,false)) := by
  classical
  let L := univ.filter fun i => i < σ i
  let e : Fin (2*r) ↪ Fin (2*r) := ⟨σ,hinv.injective⟩
  have disj : Disjoint L (L.map e) := by
    apply disjoint_left.mpr
    intro i hi hi'
    obtain ⟨j,hj,rfl⟩ := mem_map.mp hi'
    have hl := (mem_filter.mp hj).2
    have hr := (mem_filter.mp hi).2
    change σ j < σ (σ j) at hr
    rw [hinv] at hr
    exact (not_lt_of_gt hl) hr
  have cover : L ∪ L.map e = univ := by
    apply eq_univ_of_forall
    intro i
    rcases lt_or_gt_of_ne (hfree i) with h|h
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _,h⟩)
    · exact mem_union_right _ (mem_map.mpr ⟨σ i,mem_filter.mpr ⟨mem_univ _,by simpa only [hinv i] using h⟩,hinv i⟩)
  have hcard : L.card = r := by
    have hh := congrArg Finset.card cover
    rw [card_union_of_disjoint disj,card_map,card_univ,Fintype.card_fin] at hh
    omega
  let u := (Fintype.equivFinOfCardEq (show Fintype.card ↥L = r by simpa using hcard)).symm
  let v (x : Fin r × Bool) : Fin (2*r) := if x.2 then σ (u x.1) else u x.1
  have hne (i j : Fin r) : (u i).val ≠ σ (u j) := fun he =>
    (disjoint_left.mp disj) (u i).property (mem_map.mpr ⟨_,(u j).property,he.symm⟩)
  have hinj : Function.Injective v := by
    rintro ⟨i,b⟩ ⟨j,c⟩ h
    cases b <;> cases c <;> simp only [v,Bool.false_eq_true,if_false,if_true] at h ⊢
    · exact congrArg (fun k => (k,false)) (u.injective (Subtype.ext h))
    · exact (hne i j h).elim
    · exact (hne j i h.symm).elim
    · exact congrArg (fun k => (k,true)) (u.injective (Subtype.ext (hinv.injective h)))
  exact ⟨⟨v,hinj⟩,fun _ => rfl⟩

/-- Choose an enumeration in reflection pairs from any simple factorization
of the even falling-factorial gap polynomial. -/
theorem paired_even_gap_indices {K : Type*} [Field K] (r : ℕ) (h₂ : (2:K) ≠ 0)
    (a : Fin (2*r) ↪ K) (hf : descPochhammer K (2*r)-1 = ∏ i, (X-C (a i))) :
    ∃ v : Fin r × Bool ≃ Fin (2*r), ∀ i,
      a (v (i,true)) = ((2*r:ℕ):K)-1-a (v (i,false)) := by
  classical
  let f := descPochhammer K (2*r)-1
  have hs : f.Separable := by rw [show f = _ from hf]; exact separable_prod_X_sub_C_iff.mpr a.injective
  have root (x : K) : f.IsRoot x ↔ ∃ i, x = a i := by
    change (descPochhammer K (2*r)-1).IsRoot x ↔ _
    rw [hf]
    simp [IsRoot.def,eval_prod,Finset.prod_eq_zero_iff,sub_eq_zero]
  have pair (i) := two_even_roots h₂ r hs ((root _).mpr ⟨i,rfl⟩)
  choose σ hσ using fun i => (root _).mp (pair i).2
  obtain ⟨v,hv⟩ := pair_indices σ (fun i => a.injective (by
    rw [← hσ,← hσ]; ring)) (fun i h => (pair i).1 ((congrArg a h).trans (hσ i).symm))
  have hbij := (Fintype.bijective_iff_injective_and_card v).mpr
    ⟨v.injective,by simp [mul_comm]⟩
  exact ⟨Equiv.ofBijective v hbij,fun i => (congrArg a (hv i)).trans (hσ _).symm⟩

#print axioms paired_even_gap_indices

end Erdos478.EffectiveResolvent
