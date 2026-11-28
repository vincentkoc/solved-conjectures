import Green28UnpairedSites
import Green28FiveSiteCertificate

/-! Counting singleton and multiply represented totals of a uniform integer sum. -/

namespace Green28OutputCardinality

open Finset Green28 Green28UniformSums Green28UnpairedSites

/-- An aligned pair of deficient sites supplies a full translated row and
one further total for every other maximal row. These totals are disjoint
from all sums of pairs of maximal sites. -/
theorem count_aligned_rows {A B S H K : Finset ℤ}
    (hA : H ⊆ A) (hB : K ⊆ B) (cover : ∀ x ∈ A, ∀ y ∈ B, x+y ∈ S)
    (unique : ∀ x ∈ H, ∀ y ∈ K, ∀ u ∈ A, ∀ v ∈ B, x+y = u+v → x = u ∧ y = v)
    {a b p q : ℤ} (ah : a ∈ H) (bh : b ∈ K) (pa : p ∈ A) (qb : q ∈ B)
    (pl : p ∉ H) (ql : q ∉ K) (aligned : p-a = q-b) :
    H.card*K.card+B.card+(H.card-1) ≤ S.card := by
  classical
  let high := (H ×ˢ K).image (fun z => z.1+z.2)
  let row := B.image (fun y => p+y)
  let extra := (H.erase a).image (fun x => x+q)
  have hcard : high.card = H.card*K.card := by
    rw [←Finset.card_product]
    apply card_image_of_injOn
    rintro ⟨x,y⟩ xy ⟨u,v⟩ uv eq
    obtain ⟨xh,yk⟩ := mem_product.mp xy
    obtain ⟨uh,vk⟩ := mem_product.mp uv
    exact Prod.ext (unique x xh y yk u (hA uh) v (hB vk) eq).1
      (unique x xh y yk u (hA uh) v (hB vk) eq).2
  have rcard : row.card = B.card := card_image_of_injective _ (fun _ _ e => add_left_cancel e)
  have ecard : extra.card = H.card-1 := by
    rw [←card_erase_of_mem ah]
    exact card_image_of_injective _ (fun _ _ e => add_right_cancel e)
  have hr : Disjoint high row := by
    apply disjoint_left.mpr
    intro z hz rz
    obtain ⟨⟨x,y⟩,xy,rfl⟩ := mem_image.mp hz
    obtain ⟨v,vb,e⟩ := mem_image.mp rz
    obtain ⟨xh,yk⟩ := mem_product.mp xy
    exact pl ((unique x xh y yk p pa v vb e.symm).1 ▸ xh)
  have he : Disjoint high extra := by
    apply disjoint_left.mpr
    intro z hz ez
    obtain ⟨⟨x,y⟩,xy,rfl⟩ := mem_image.mp hz
    obtain ⟨u,uh,e⟩ := mem_image.mp ez
    obtain ⟨xh,yk⟩ := mem_product.mp xy
    exact ql ((unique x xh y yk u (hA (mem_erase.mp uh).2) q qb e.symm).2 ▸ yk)
  have re : Disjoint row extra := by
    apply disjoint_left.mpr
    intro z rz ez
    obtain ⟨v,vb,rfl⟩ := mem_image.mp rz
    obtain ⟨u,uh,e⟩ := mem_image.mp ez
    obtain ⟨ne,live⟩ := mem_erase.mp uh
    exact ne (unique u live b bh a (hA ah) v vb (by omega)).1
  have sub : high ∪ row ∪ extra ⊆ S := by
    intro z hz
    rw [mem_union,mem_union] at hz
    rcases hz with (h|h)|h
    · obtain ⟨⟨x,y⟩,xy,rfl⟩ := mem_image.mp h
      exact cover x (hA (mem_product.mp xy).1) y (hB (mem_product.mp xy).2)
    · obtain ⟨y,yb,rfl⟩ := mem_image.mp h
      exact cover p pa y yb
    · obtain ⟨x,xh,rfl⟩ := mem_image.mp h
      exact cover x (hA (mem_erase.mp xh).2) q qb
  have h := card_le_card sub
  rwa [card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨he,re⟩),
    card_union_of_disjoint hr,hcard,rcard,ecard] at h

/-- The sites of the original law with the same mass as the indicated endpoint. -/
def endpointSites (P : PMF ℤ) (a : ℤ) : Set ℤ :=
  {x | x ∈ P.support ∧ (P x).toReal = (P a).toReal}

private theorem two_endpoints {P : PMF ℤ} (E : Extremes P.support)
    (L : Extremes (lowerSites P E.lo)) (pf : P.support.Finite) (top : (P E.hi).toReal = (P E.lo).toReal) :
    2 ≤ (endpointSites P E.lo).ncard := by
  have ne : E.lo ≠ E.hi := by
    intro eq
    have low := E.least.2 L.least.1.1
    have high := E.greatest.2 L.least.1.1
    have same : L.lo = E.lo := by omega
    exact L.least.1.2 (by rw [same])
  have sub : ({E.lo,E.hi} : Set ℤ) ⊆ endpointSites P E.lo := by
    rintro x (rfl|hx)
    · exact ⟨E.least.1,rfl⟩
    · obtain rfl := Set.mem_singleton_iff.mp hx
      exact ⟨E.greatest.1,top⟩
  have fin : (endpointSites P E.lo).Finite := pf.subset (fun _ h => h.1)
  exact (by simpa [Set.ncard_pair ne] using Set.ncard_le_ncard sub fin)

/-- In a putative counterexample, maximal-mass pairs give singleton values
and aligned deficient atoms give disjoint families of multiply represented values. -/
theorem aligned_output_count {P Q : PMF ℤ} {S : Finset ℤ} (ne : S.Nonempty)
    (sum : indepSum P Q = PMF.uniformOfFinset S ne) (L : Alignment P Q) :
    let h := (endpointSites P L.left.lo).ncard
    let k := (endpointSites Q L.right.lo).ncard
    2 ≤ h ∧ 2 ≤ k ∧ h*k + max (Q.support.ncard+(h-1)) (P.support.ncard+(k-1)) ≤ S.card := by
  classical
  have flat : IsUniformOnSupport (indepSum P Q) := ⟨S,ne,sum⟩
  obtain ⟨pf,qf⟩ := finite_of_uniform_sum flat
  let a := L.left.lo
  let b := L.right.lo
  let p := L.leftLow.lo
  let q := L.rightLow.lo
  let A := pf.toFinset
  let B := qf.toFinset
  have hf : (endpointSites P a).Finite := pf.subset (fun _ h => h.1)
  have kf : (endpointSites Q b).Finite := qf.subset (fun _ h => h.1)
  let H := hf.toFinset
  let K := kf.toFinset
  obtain ⟨topP,topQ,rect⟩ := maximal_rectangle flat L.left L.right
  refine ⟨two_endpoints L.left L.leftLow pf topP,two_endpoints L.right L.rightLow qf topQ,?_⟩
  have hA : H ⊆ A := fun _ h => pf.mem_toFinset.mpr (hf.mem_toFinset.mp h).1
  have hB : K ⊆ B := fun _ h => qf.mem_toFinset.mpr (kf.mem_toFinset.mp h).1
  have cover (x : ℤ) (hx : x ∈ A) (y : ℤ) (hy : y ∈ B) : x+y ∈ S := by
    have mem : x+y ∈ (indepSum P Q).support := (PMF.mem_support_bind_iff _ _ _).mpr ⟨x,pf.mem_toFinset.mp hx,
      (PMF.mem_support_bind_iff _ _ _).mpr ⟨y,qf.mem_toFinset.mp hy,(PMF.mem_support_pure_iff _ _).mpr rfl⟩⟩
    rwa [sum,PMF.support_uniformOfFinset] at mem
  have unique (x : ℤ) (hx : x ∈ H) (y : ℤ) (hy : y ∈ K) (u : ℤ) (hu : u ∈ A) (v : ℤ) (hv : v ∈ B)
      (e : x+y = u+v) : x = u ∧ y = v := by
    have h := hf.mem_toFinset.mp hx
    have k := kf.mem_toFinset.mp hy
    exact ((rect x h.1 y k.1).mpr ⟨h.2,k.2⟩) u (pf.mem_toFinset.mp hu) v (qf.mem_toFinset.mp hv) e
  have ah : a ∈ H := hf.mem_toFinset.mpr ⟨L.left.least.1,rfl⟩
  have bh : b ∈ K := kf.mem_toFinset.mpr ⟨L.right.least.1,rfl⟩
  have pa : p ∈ A := pf.mem_toFinset.mpr L.leftLow.least.1.1
  have qb : q ∈ B := qf.mem_toFinset.mpr L.rightLow.least.1.1
  have pl : p ∉ H := fun h => L.leftLow.least.1.2 (hf.mem_toFinset.mp h).2
  have ql : q ∉ K := fun h => L.rightLow.least.1.2 (kf.mem_toFinset.mp h).2
  have left := count_aligned_rows hA hB cover unique ah bh pa qb pl ql L.lower_eq
  have right := count_aligned_rows hB hA (fun y hy x hx => add_comm x y ▸ cover x hx y hy)
    (fun y hy x hx v hv u hu e => (unique x hx y hy u hu v hv (by omega)).symm)
    bh ah qb pa ql pl L.lower_eq.symm
  rw [Nat.mul_comm K.card H.card] at right
  rw [Set.ncard_eq_toFinset_card _ pf,Set.ncard_eq_toFinset_card _ qf,
    Set.ncard_eq_toFinset_card (endpointSites P L.left.lo) hf,Set.ncard_eq_toFinset_card (endpointSites Q L.right.lo) kf]
  change H.card*K.card+max (B.card+(H.card-1)) (A.card+(K.card-1)) ≤ S.card
  omega

/-- Every failure of Green 28 has at least five more output values than
the number of atoms in its larger marginal. -/
theorem uniform_or_five_more {P Q : PMF ℤ} {S : Finset ℤ} (ne : S.Nonempty)
    (sum : indepSum P Q = PMF.uniformOfFinset S ne) :
    (IsUniformOnSupport P ∧ IsUniformOnSupport Q) ∨
      max P.support.ncard Q.support.ncard+5 ≤ S.card := by
  have flat : IsUniformOnSupport (indepSum P Q) := ⟨S,ne,sum⟩
  rcases alignment_alternative flat with fair|w
  · exact Or.inl fair
  · right
    obtain ⟨L⟩ := w
    obtain ⟨h,k,c⟩ := aligned_output_count ne sum L
    have four := Nat.mul_le_mul h k
    omega

/-- Any uniform sum supported on at most ten integers has uniform marginals.
The positions of the ten sites and the input probability values are arbitrary. -/
theorem uniform_of_ten_outputs {P Q : PMF ℤ} {S : Finset ℤ} (ne : S.Nonempty)
    (sum : indepSum P Q = PMF.uniformOfFinset S ne) (size : S.card ≤ 10) :
    IsUniformOnSupport P ∧ IsUniformOnSupport Q := by
  rcases uniform_or_five_more ne sum with fair|bound
  · exact fair
  · exact Green28FiveSiteCertificate.uniform_of_at_most_five_atoms ⟨S,ne,sum⟩ (by omega) (by omega)

#print axioms count_aligned_rows
#print axioms aligned_output_count
#print axioms uniform_or_five_more
#print axioms uniform_of_ten_outputs
end Green28OutputCardinality
