import CunninghamGapAverage

/-! The canonical Bateman–Horn polynomials for a positive separation of at least two. -/

namespace CunninghamChain.GapMean

open Finset Polynomial BatemanHornConjecture Filter
open scoped Topology

/-- The second-kind site at depth j evaluated at a seed h+2 above the first seed. -/
noncomputable def shifted (h j : ℕ) : ℤ[X] :=
  C ((2:ℤ)^j)*X + C ((2:ℤ)^j*(h+1)+1)

noncomputable def pairedForms (k l h : ℕ) : Finset ℤ[X] := chainForms 1 k ∪ (range l).image (shifted h)

private lemma lc (h i : ℕ) : (shifted h i).leadingCoeff=(2:ℤ)^i := leadingCoeff_linear (by positivity)

private lemma apart (h k l : ℕ) : Disjoint (chainForms 1 k) ((range l).image (shifted h)) := by
  rw [Finset.disjoint_left]
  intro f hf hg
  change f∈(range k).image (form 1) at hf
  obtain ⟨i,_,rfl⟩ := mem_image.mp hf
  obtain ⟨j,_,eq⟩ := mem_image.mp hg
  have e := congrArg leadingCoeff eq
  rw [lc,show (form 1 i).leadingCoeff=(2:ℤ)^i from leadingCoeff_linear (by positivity)] at e
  obtain rfl := (pow_right_injective₀ (by norm_num : (0:ℤ)<2) (by norm_num)) e
  have z := congrArg (fun f : ℤ[X] => f.eval 0) eq
  simp only [shifted,form,eval_add,eval_C,eval_mul,eval_X,mul_zero,zero_add,one_mul] at z
  nlinarith [mul_nonneg (show 0≤(2:ℤ)^j by positivity) (show 0≤(h:ℤ) by positivity)]

theorem pairedForms_card (k l h : ℕ) : (pairedForms k l h).card=k+l := by
  have inj : Function.Injective (shifted h) := by
    intro i j eq
    have hh := congrArg leadingCoeff eq
    rw [lc,lc] at hh
    exact (pow_right_injective₀ (by norm_num : (0:ℤ)<2) (by norm_num)) hh
  simp only [pairedForms,card_union_of_disjoint (apart h k l),chainForms_count,card_image_of_injective _ inj,card_range]

private lemma shift_eval (q h j : ℕ) (z : ZMod q) :
    ((shifted h j).map (Int.castRingHom (ZMod q))).eval z =
      ((form (-1) j).map (Int.castRingHom (ZMod q))).eval (z+(h+2:ℕ)) := by
  simp [shifted,form]
  ring

/-- The paired local product uses the pinned polynomial root count, including
the zero local factors on nonadmissible gaps. -/
theorem canonical_pair_product (k l h Y : ℕ) :
    BatemanHornPartialProduct (pairedForms k l h) Y = pairProduct k l Y (h+2) := by
  classical
  unfold BatemanHornPartialProduct pairProduct
  rw [pairedForms_card]
  apply prod_congr rfl
  intro q hq
  have hp := Nat.prime_of_mem_primesBelow hq
  let : Fact q.Prime := ⟨hp⟩
  let A := (accepted 1 k q).filter fun (x : ZMod q) => x+((h+2:ℕ):ZMod q)∈accepted (-1) l q
  have roots : {z : ZMod q | ∃ f∈pairedForms k l h, (f.map (Int.castRingHom (ZMod q))).eval z=0} =
      ↑(Aᶜ : Finset (ZMod q)) := by
    ext z
    have criterion : z∈A ↔ ∀ f∈pairedForms k l h, (f.map (Int.castRingHom (ZMod q))).eval z≠0 := by
      simp only [A,accepted,mem_filter,mem_univ,true_and,pairedForms,forall_mem_union]
      change (_ ∧ ∀ f∈(range l).image (form (-1)), _) ↔ _
      simp only [Finset.forall_mem_image,shift_eval]
    simp only [Set.mem_ofPred_eq,mem_coe,mem_compl,criterion]
    push Not
    rfl
  have count : A.card+OmegaP (pairedForms k l h) q=q := by
    rw [OmegaP,roots,Set.ncard_coe_finset]
    exact (card_add_card_compl A).trans (ZMod.card q)
  have cr : (A.card:ℝ)+(OmegaP (pairedForms k l h) q:ℝ)=q := by exact_mod_cast count
  have qr : (q:ℝ)≠0 := by exact_mod_cast hp.ne_zero
  simp only [factor,dif_pos hp,pairFactor]
  congr 1
  change 1-_/q=(A.card:ℝ)/q
  field_simp; linarith

theorem canonical_series_limit {k l : ℕ} (p : 0<k+l) (h : ℕ) :
    Tendsto (BatemanHornPartialProduct (pairedForms k l h)) atTop (𝓝 (series k l h)) := by
  simpa only [funext (canonical_pair_product k l h)] using series_limit p h

private lemma form_eval (n i : ℕ) : (form 1 i).eval (n:ℤ) = firstKindTerm n i := by
  induction i with
  | zero => simp [form,firstKindTerm]
  | succ i ih =>
    simp only [form,eval_add,eval_mul,eval_C,eval_X,one_mul] at ih ⊢
    rw [firstKindTerm,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,pow_succ]
    linear_combination 2*ih

private lemma shifted_eval (n h j : ℕ) : (shifted h j).eval (n:ℤ)=secondKindTerm (n+(h+2)) j := by
  have pos (t : ℕ) : 0<secondKindTerm (n+(h+2)) t := by
    induction t with
    | zero => simp [secondKindTerm]
    | succ t ih => rw [secondKindTerm]; omega
  induction j with
  | zero => simp [shifted,secondKindTerm]; ring
  | succ j ih =>
    simp only [shifted,eval_add,eval_mul,eval_C,eval_X] at ih ⊢
    rw [secondKindTerm,Nat.cast_sub (by have := pos j; omega : 1≤2*secondKindTerm (n+(h+2)) j),
      Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,pow_succ]
    linear_combination 2*ih

def Prefix (k l h n : ℕ) : Prop :=
  (∀ i<k, (firstKindTerm n i).Prime) ∧ (∀ j<l, (secondKindTerm (n+(h+2)) j).Prime)

/-- The simultaneous-prime event counts the two canonical prefixes at every natural seed. -/
theorem canonical_prefix (k l h n : ℕ) :
    (∀ f∈pairedForms k l h, (f.eval (n:ℤ)).natAbs.Prime) ↔ Prefix k l h n := by
  classical
  unfold pairedForms Prefix
  change (∀ f∈(range k).image (form 1) ∪ (range l).image (shifted h), _) ↔ _
  simp only [forall_mem_union,forall_mem_image,mem_range,form_eval,shifted_eval,Int.natAbs_natCast]

theorem family_bunyakovsky (k l h : ℕ) {f} (hf : f∈pairedForms k l h) :
    BunyakovskyCondition f ∧ f.natDegree=1 := by
  have lin (a b : ℤ) (pa : 0<a) (cop : IsCoprime a b) :
      BunyakovskyCondition (C a*X+C b) ∧ (C a*X+C b).natDegree=1 :=
    ⟨⟨(degree_linear pa.ne').ge,irreducible_C_mul_X_add_C pa.ne' cop.isRelPrime,
      by rw [leadingCoeff_linear pa.ne']; exact pa⟩,natDegree_linear pa.ne'⟩
  change f∈(range k).image (form 1) ∪ (range l).image (shifted h) at hf
  rcases mem_union.mp hf with hf|hf
  · obtain ⟨i,_,rfl⟩ := mem_image.mp hf
    exact lin _ _ (by positivity : 0<(2:ℤ)^i) ⟨1,-1,by ring⟩
  · obtain ⟨j,_,rfl⟩ := mem_image.mp hf
    exact lin _ _ (by positivity : 0<(2:ℤ)^j) ⟨-(h+1:ℤ),1,by ring⟩

#print axioms pairedForms_card
#print axioms canonical_pair_product
#print axioms canonical_series_limit
#print axioms canonical_prefix
#print axioms family_bunyakovsky

end CunninghamChain.GapMean
