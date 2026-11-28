import Green51LinearStructures

/-! # Largest-flat counts from the dimension of the constant-derivative space -/

open Finset Green50Downsets Green51QuadraticFlats Green51WitnessIncidence
open scoped Classical Pointwise
namespace Green51PermutedPairs
local notation "F" => ZMod 2
variable {n:ℕ}

theorem affineModulo_iff_defect (f:Cube n→Cube n) {t:Cube n} (c:constantAlong f t) :
    affineModulo f t ↔ ∀x y,defect f x y=0 ∨ defect f x y=f 0+f t := by
  have eq (x y:Cube n) : defect f x y=f 0+f t ↔ f x+f y+f 0=f (x+y+t) := by
    rw [defect,←eq_sub_iff_add_eq,ZModModule.sub_eq_add,add_comm (f 0+f t),
      ←(constant_iff_shift f t).mp c (x+y)]
  simp only [affineModulo,defect_zero_iff,eq]

theorem at_most_one_extra (f:Cube n ≃ Cube n) {x y:Cube n} (h:defect f x y≠0) :
    (extraDirections f).card≤1 := by
  apply Finset.card_le_one.mpr
  intro s hs t ht
  have value {u:Cube n} (hu:u∈extraDirections f) : defect f x y=f 0+f u := by
    obtain ⟨d,m⟩:=mem_filter.mp hu
    exact ((affineModulo_iff_defect f (mem_filter.mp d).2).mp m x y).resolve_left h
  exact f.injective (add_left_cancel ((value hs).symm.trans (value ht)))

theorem one_extra_of_four_cosets (f:Cube n ≃ Cube n) {x y:Cube n} (h:defect f x y≠0)
    (dim:Nat.card (Cube n ⧸ structures f)=4) : (extraDirections f).card=1 := by
  apply Nat.le_antisymm (at_most_one_extra f h)
  apply (Finset.card_pos.mpr ?_)
  let w:=defect f x y
  let t:=f.symm (f 0+w)
  have et : f 0+f t=w := by
    change f 0+f (f.symm (f 0+w))=w
    rw [f.apply_symm_apply,←add_assoc,ZModModule.add_self,zero_add]
  have tn : t≠0 := by
    intro e;apply h
    change w=0
    rw [←et,e,ZModModule.add_self]
  have c:constantAlong f t := by
    apply (constant_iff_defect ..).mpr
    intro a
    rcases common_defect f dim h a t with z|z
    · exact z
    exfalso
    apply tn
    have sum : f a+f (a+t)=0 := by
      have e : defect f a t=(f 0+f t)+(f a+f (a+t)) := by unfold defect;ac_rfl
      change defect f a t=w at z
      rw [e,←et] at z
      exact add_left_cancel (z.trans (add_zero _).symm)
    rw [←ZModModule.sub_eq_add,sub_eq_zero] at sum
    have e:=f.injective sum
    exact add_left_cancel (e.symm.trans (add_zero _).symm)
  refine ⟨t,mem_filter.mpr ⟨mem_filter.mpr ⟨mem_erase.mpr ⟨tn,mem_univ _⟩,c⟩,?_⟩⟩
  apply (affineModulo_iff_defect _ c).mpr
  rw [et]
  exact common_defect f dim h

theorem card_structures (f:Cube n→Cube n) :
    1+(directions f).card = 2^(Module.finrank F (structures f)) := by
  classical
  let H:=structures f
  have eq : directions f=((univ:Finset (Cube n)).filter (·∈H)).erase 0 := by
    have mem (t:Cube n) : t∈H ↔ constantAlong f t := Iff.rfl
    ext t;simp [directions,mem]
  have zero:(0:Cube n)∈(univ.filter (·∈H)):=by simp
  rw [eq,Nat.add_comm,Finset.card_erase_add_one zero,←Fintype.card_subtype (fun z:Cube n=>z∈H),
    ←Nat.card_eq_fintype_card,Module.natCard_eq_pow_finrank (K:=F)]
  simp [H]

private theorem quotient_size (f:Cube n→Cube n) :
    Nat.card (Cube n ⧸ structures f) = 2^Module.finrank F (Cube n ⧸ structures f) := by
  rw [Module.natCard_eq_pow_finrank (K:=F)]
  simp

theorem flat_count_if_affine (large:4≤n) (f:Cube n ≃ Cube n)
    (aff:∀x y,defect f x y=0) :
    (familyAt n (labels f 0)).ncard=2^(n+1)-1 := by
  classical
  have c (t:Cube n):constantAlong f t:=(constant_iff_defect ..).mpr (fun x=>aff x t)
  have top : structures f=⊤ := top_unique (fun t _=>c t)
  have both:extraDirections f=directions f := by
    ext t
    simp only [extraDirections,mem_filter,and_iff_left_iff_imp]
    intro _
    exact (affineModulo_iff_defect _ (c t)).mpr (fun x y=>Or.inl (aff x y))
  have count:=card_structures f
  rw [top,finrank_top] at count
  rw [show Module.finrank F (Cube n)=n by simp [Cube]] at count
  rw [count_formula large,both,pow_succ]
  omega


/-- Away from affine permutations, there is at most one extra odd sheet. At codimension
two there is always exactly one. -/
theorem nonaffine_count (large:4≤n) (f:Cube n ≃ Cube n) {x y:Cube n} (bad:defect f x y≠0) :
    let s:=Module.finrank F (structures f)
    let m:=(familyAt n (labels f 0)).ncard
    s+2≤n ∧ (m=2^s ∨ m=2^s+1) ∧ (s+2=n → m=2^s+1) := by
  dsimp only
  let r:=Module.finrank F (Cube n ⧸ structures f)
  let s:=Module.finrank F (structures f)
  have dim:r+s=n := by simpa [r,s,Cube] using (structures f).finrank_quotient_add_finrank
  have q:Nat.card (Cube n ⧸ structures f)=2^r:=quotient_size f
  have four:=four_cosets_of_nonaffine f bad
  rw [q] at four
  have hr:2≤r := by
    by_contra! hr
    interval_cases r <;> simp_all
  have cap:=at_most_one_extra f bad
  rw [count_formula large,card_structures]
  change s+2≤n ∧ _ ∧ _
  refine ⟨by omega,by omega,?_⟩
  intro eq
  have : r=2:=by omega
  rw [one_extra_of_four_cosets f bad (by rw [q,this];decide)]

theorem four_dimensional_counts (f:Cube 4 ≃ Cube 4) :
    (familyAt 4 (labels f 0)).ncard∈([1,2,3,5,31]:List ℕ) := by
  classical
  by_cases aff:∀x y,defect f x y=0
  · rw [flat_count_if_affine (by decide) f aff]
    decide
  push Not at aff
  obtain ⟨x,y,bad⟩:=aff
  let s:=Module.finrank F (structures f)
  let k:=(familyAt 4 (labels f 0)).ncard
  have h:s+2≤4 ∧ (k=2^s ∨ k=2^s+1) ∧ (s+2=4 → k=2^s+1) :=
    nonaffine_count (by decide) f bad
  obtain ⟨dim,choices,edge⟩:=h
  change k∈([1,2,3,5,31]:List ℕ)
  simp only [List.mem_cons]
  have small:s≤2:=by omega
  interval_cases s <;> norm_num at choices edge <;> omega

end Green51PermutedPairs

#print axioms Green51PermutedPairs.at_most_one_extra
#print axioms Green51PermutedPairs.one_extra_of_four_cosets
#print axioms Green51PermutedPairs.card_structures
#print axioms Green51PermutedPairs.flat_count_if_affine
#print axioms Green51PermutedPairs.nonaffine_count
#print axioms Green51PermutedPairs.four_dimensional_counts
