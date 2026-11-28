import Erdos722AffineLatinFillings
import Erdos722LatinCosetClassCount

/-! # Exact number of asymmetric classes outside the normalized coefficient family -/

namespace Erdos722.LatinFillings
open Finset QuadCompletion FourPoint QuadSwitch Equiv
open scoped Classical
noncomputable section
attribute [local instance] cubeOrder cubeDec

private theorem old_inside (d : ℕ) (hd : 6≤d) (a : CosetParameters d) (i j k : Base d)
    (on : baseQuad (cubeRule (d+2)) i j k∈region d) (f : Base d → Fibre)
    (accepted : (laws d (affineParameters d hd a).1 ⟨_,on⟩).accepts f) :
    (cosetRule d hd a.1 a.2).complete (i,f i) (j,f j) (k,f k)=
      ((cubeRule (d+2)).complete i j k,f ((cubeRule (d+2)).complete i j k)) := by
  let Q := cubeRule (d+2)
  let B : Q.blocks := ⟨_,region_sub d on⟩
  let D := linearCoordinates (cosetColours d hd a.1)
  let v (l : Base d) := D B l (f l)
  have size : (insert (Q.complete i j k) {i,j,k} : Finset (Base d)).card=4 := region_size d _ on
  have bound := card_insert_le (Q.complete i j k) ({i,j,k} : Finset (Base d))
  obtain ⟨ij,ik,jk⟩ := card_triple_eq_three_iff.mp (show ({i,j,k} : Finset (Base d)).card=3 by
    have h := @card_le_three (Base d) _ i j k
    omega)
  have sum := (affine_accepts d hd a ⟨_,on⟩ f).mp accepted
  change ∑ l ∈ insert (Q.complete i j k) {i,j,k}, v l=a.2 B at sum
  rw [sum_insert (Q.fresh ij ik jk),sum_insert (by simp [ij,ik]),sum_insert (by simpa using jk),
    sum_singleton] at sum
  apply Prod.ext
  · rfl
  apply (D B (Q.complete i j k)).injective
  rw [show D B (Q.complete i j k) ((cosetRule d hd a.1 a.2).complete (i,f i) (j,f j) (k,f k)).2 =
    v i+v j+v k+a.2 B from blockwise_transversal Q (matching d hd) a.2 D ij ik jk ..]
  change v i+v j+v k+a.2 B=v _
  rw [← sum]
  exact (show ∀ a b c h : Fibre, a+b+c+(h+(a+(b+c)))=h by decide +kernel) _ _ _ _

private theorem old_outside (d : ℕ) (hd : 6≤d) (a : CosetParameters d) (x y z : Base d × Fibre)
    (off : baseQuad (cubeRule (d+2)) x.1 y.1 z.1∉region d) :
    (baseline d hd (affineParameters d hd a).2).complete x y z=(cosetRule d hd a.1 a.2).complete x y z := by
  obtain ⟨i,x⟩ := x
  obtain ⟨j,y⟩ := y
  obtain ⟨k,z⟩ := z
  let Q := cubeRule (d+2)
  let S := baseQuad Q i j k
  let u := extendOffset d (affineParameters d hd a).2
  let C := cosetColours d hd a.1
  have clear : S∉region d := off
  have chart : blockChart Q (linearCoordinates (colours d hd)) S=blockChart Q (linearCoordinates C) S := by
    by_cases h : S∈Q.blocks
    · have outside : (⟨S,h⟩ : Q.blocks)∉cosetBlocks d := fun e => clear ((region_mem d _).mpr e)
      simp only [blockChart,dif_pos h]
      funext l
      change colourPermutation _=colourPermutation (cosetColours d hd a.1 ⟨S,h⟩ l)
      rw [cosetColours,dif_neg outside]
    · simp only [blockChart,dif_neg h]
  have offset : transversalOffset Q u i j k=transversalOffset Q a.2 i j k := by
    change offsetAt Q u S=offsetAt Q a.2 S
    by_cases h : S∈Q.blocks
    · have outer : S∈outsideBlocks d := mem_sdiff.mpr ⟨h,clear⟩
      simp only [offsetAt,dif_pos h,u,extendOffset,dif_pos outer,affineParameters]
    · simp only [offsetAt,dif_neg h]
  have eq := coloured_completion (matching d hd) (colours d hd) u i j k x y z
  dsimp only at eq
  change blockChart Q (linearCoordinates (colours d hd)) S (Q.complete i j k) _ =
    fourth (matching d hd) i j k (blockChart Q (linearCoordinates (colours d hd)) S i x)
      (blockChart Q (linearCoordinates (colours d hd)) S j y)
      (blockChart Q (linearCoordinates (colours d hd)) S k z)+transversalOffset Q u i j k at eq
  rw [chart,offset] at eq
  exact Prod.ext rfl ((blockChart Q (linearCoordinates C) S _).injective
    (eq.trans (coloured_completion (matching d hd) C a.2 i j k x y z).symm))

/-- Every labelled design from the earlier affine equations is an actual
member of the Latin family, with the same labels. -/
theorem affine_realization (d : ℕ) (hd : 6≤d) (a : CosetParameters d) :
    latinDesign d hd (affineParameters d hd a)=cosetDesign d hd a.1 a.2 := by
  let p := affineParameters d hd a
  have same : (latinRule d hd p).complete=(cosetRule d hd a.1 a.2).complete := by
    funext x y z
    exact patch_agrees _ _ _ (laws d p.1) (region_size d) (baseline_compatible d hd p.2).project
      (old_inside d hd a) (old_outside d hd a) x y z
  have eq : latinRule d hd p=cosetRule d hd a.1 a.2 := by
    cases h : latinRule d hd p
    cases h' : cosetRule d hd a.1 a.2
    rw [h,h'] at same
    cases same
    rfl
  exact congrArg (labelledBlocks (d+2)) eq

theorem affine_classes_subset (d : ℕ) (hd : 6≤d) : cosetClasses d hd ⊆ latinClasses d hd := by
  intro y hy
  obtain ⟨a,_,rfl⟩ := mem_image.mp hy
  exact mem_image.mpr ⟨affineParameters d hd a,mem_univ _,congrArg classOf (affine_realization d hd a)⟩

/-- Difference under unrestricted point isomorphism, with the affine classes removed. -/
theorem class_difference (d : ℕ) (hd : 6≤d) :
    (latinClasses d hd \ cosetClasses d hd).card =
      (64^blockNumber (2^d)-1)*(cosetClasses d hd).card := by
  rw [card_sdiff_of_subset (affine_classes_subset d hd),latin_class_count,coset_class_count,
    show 13824=64*216 by decide,mul_pow,mul_assoc,Nat.sub_mul,one_mul]

#print axioms affine_realization
#print axioms affine_classes_subset
#print axioms class_difference
end
end Erdos722.LatinFillings
