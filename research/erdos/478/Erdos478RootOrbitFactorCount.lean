import Erdos478SeparableRootMean

/-! # Counting irreducible factors by a complete set of labels on the roots -/

namespace Erdos478.CollisionLaw
open Polynomial Finset UniqueFactorizationMonoid Function
noncomputable section

/-- A label for each root, onto the listed labels, gives the factor count
if equality of labels agrees with equality of minimal polynomials. -/
theorem factor_count_by_labels {F K L : Type*} [Field F] [DecidableEq F] [Field K] [Algebra F K]
    [Fintype L] {f : F[X]} (hm : f.Monic) (hs : f.Separable)
    (split : (f.map (algebraMap F K)).Splits) (tag : f.rootSet K → L)
    (onto : Surjective tag) (same : ∀ x y, tag x=tag y ↔ minpoly F (x:K)=minpoly F (y:K)) :
    (normalizedFactors f).card = Fintype.card L := by
  classical
  choose v hv using onto
  let q (t : L) := minpoly F (v t : K)
  have inj : Injective q := by
    intro i j he
    simpa only [hv] using (same _ _).mpr he
  have eq : (normalizedFactors f).toFinset=univ.image q := by
    ext g
    simp only [Multiset.mem_toFinset,mem_image,mem_univ,true_and,
      Polynomial.mem_normalizedFactors_iff hm.ne_zero]
    constructor
    · rintro ⟨hi,hg,hd⟩
      have sp := split.of_dvd (hm.map _).ne_zero (Polynomial.map_dvd (algebraMap F K) hd)
      obtain ⟨x,hx⟩ := sp.exists_eval_eq_zero (degree_ne_of_natDegree_ne (by
        rw [hg.natDegree_map]; exact hi.natDegree_pos.ne'))
      have root : aeval x g=0 := by simpa only [eval_map_algebraMap] using hx
      let y : f.rootSet K := ⟨x,hm.mem_rootSet.mpr (aeval_eq_zero_of_dvd_aeval_eq_zero hd root)⟩
      have hy := (same (v (tag y)) y).mp (hv _)
      exact ⟨tag y,hy.trans (minpoly.eq_of_irreducible_of_monic hi root hg).symm⟩
    · rintro ⟨i,rfl⟩
      have x := hm.mem_rootSet.mp (v i).prop
      have hi : IsIntegral F (v i : K) := ⟨f,hm,x⟩
      exact ⟨minpoly.irreducible hi,minpoly.monic hi,minpoly.dvd F _ x⟩
  have nd := (squarefree_iff_nodup_normalizedFactors hm.ne_zero).mp hs.squarefree
  rw [← Multiset.toFinset_card_of_nodup nd,eq,card_image_of_injective _ inj,card_univ]

#print axioms factor_count_by_labels
end
end Erdos478.CollisionLaw
