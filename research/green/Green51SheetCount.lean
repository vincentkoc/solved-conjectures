import Green51SheetClosure

/-! # All largest flats of the paired construction with zero offsets -/

open Finset Green50Downsets Green51QuadraticFlats Green51WitnessIncidence
open scoped Classical Pointwise
namespace Green51PermutedPairs
local notation "F" => ZMod 2
variable {n:ℕ}

/-- Each largest flat is the vertical one or a full even or odd sheet over a unique chord direction. -/
theorem all_top_flats (large:4≤n) (f:Cube n ≃ Cube n) (D:Set (E n)) :
    D∈familyAt n (labels f 0) ↔ D=distinguished n ∨
    ∃ t:Cube n,t≠0 ∧ constantAlong f t ∧ (D=evenSheet f t ∨ D=oddSheet f t ∧ affineModulo f t) := by
  constructor
  · intro mem
    obtain ⟨P,W,dim,rfl,inside⟩:=mem
    rcases top_flat_alternative large f 0 P W dim inside with eq|⟨t,tn,proj,constant⟩
    · exact Or.inl eq
    refine Or.inr ⟨t,tn,constant,?_⟩
    rcases sheet_classification f tn constant (by omega) P W dim inside proj with eq|eq
    · exact Or.inl eq
    · exact Or.inr ⟨eq,(oddSheet_mem_iff f tn).mp (eq ▸ (show P +ᵥ (W:Set (E n))∈familyAt n (labels f 0) from ⟨P,W,dim,rfl,inside⟩))⟩
  · rintro (rfl|⟨t,tn,constant,h⟩)
    · exact distinguished_mem _ _
    rcases h with rfl|⟨rfl,good⟩
    · exact evenSheet_mem f tn constant
    · exact (oddSheet_mem_iff f tn).mpr good

private theorem even_marker (f:Cube n→Cube n) {t:Cube n} {z:E n} (hz:z∈evenSheet f t) :
    horizontal n z.1=t ∧ z.2.1=0 := by
  refine ⟨((fiber_iff _ _).mp hz.1).2,?_⟩
  rcases hz.2 with h|h <;> exact congrArg Prod.fst h

private theorem odd_marker (f:Cube n→Cube n) {t:Cube n} {z:E n} (hz:z∈oddSheet f t) :
    horizontal n z.1=t ∧ z.2.1=1 := by
  obtain ⟨x,rfl⟩:=hz
  exact ⟨((fiber_iff _ _).mp ((fiber_chord _ _).mpr ⟨x,rfl⟩)).2,rfl⟩

private theorem even_base (f:Cube n→Cube n) (t:Cube n) : ((chord t 0,0):E n)∈evenSheet f t :=
  ⟨(fiber_chord _ _).mpr ⟨0,rfl⟩,Or.inl rfl⟩

private theorem evenSheet_inj (f:Cube n→Cube n) : Function.Injective (evenSheet f) := by
  intro s t eq
  exact (even_marker f (even_base f s)).1.symm.trans (even_marker f (eq ▸ even_base f s)).1
private theorem oddSheet_inj (f:Cube n→Cube n) : Function.Injective (oddSheet f) := by
  intro s t eq
  have h:oddPoint f s 0∈oddSheet f s:=⟨0,rfl⟩
  exact (odd_marker f h).1.symm.trans (odd_marker f (eq ▸ h)).1
private theorem opposite_tags (f:Cube n→Cube n) (s t:Cube n) : evenSheet f s≠oddSheet f t := by
  intro eq
  have h:=even_base f s
  exact zero_ne_one ((even_marker f h).2.symm.trans (odd_marker f (eq ▸ h)).2)
private theorem nonvertical_even (f:Cube n→Cube n) (t:Cube n) : evenSheet f t≠distinguished n := by
  intro eq
  have h:=even_base f t
  have bad:=(eq ▸ h : (chord t 0,(0:V n))∈distinguished n)
  exact zero_ne_one (show (0:F)=1 from bad.2)
private theorem nonvertical_odd (f:Cube n→Cube n) {t:Cube n} (tn:t≠0) : oddSheet f t≠distinguished n := by
  intro eq
  have h:oddPoint f t 0∈oddSheet f t:=⟨0,rfl⟩
  have bad:=eq ▸ h
  apply tn
  rw [←(odd_marker f h).1,show (oddPoint f t 0).1=0 from bad.1,map_zero]

instance (f:Cube n→Cube n) (t:Cube n) : Decidable (constantAlong f t) :=
  inferInstanceAs (Decidable (∀x:Cube n,f x+f (x+t)=f 0+f t))
instance (f:Cube n→Cube n) (t:Cube n) : Decidable (affineModulo f t) :=
  inferInstanceAs (Decidable (∀x y:Cube n,f x+f y+f 0=f (x+y) ∨ f x+f y+f 0=f (x+y+t)))
def directions (f:Cube n→Cube n) : Finset (Cube n) := (univ.erase 0).filter (constantAlong f)
def extraDirections (f:Cube n→Cube n) : Finset (Cube n) := (directions f).filter (affineModulo f)

/-- Each nonzero constant derivative contributes one sheet, and a second when the quotient map is affine. -/
theorem count_formula (large:4≤n) (f:Cube n ≃ Cube n) :
    (familyAt n (labels f 0)).ncard=1+(directions f).card+(extraDirections f).card := by
  classical
  let E':=(directions f).image (evenSheet f)
  let O':=(extraDirections f).image (oddSheet f)
  let D:=distinguished n
  have eq:familyAt n (labels f 0)=↑(insert D (E'∪O')) := by
    ext A
    simp only [SetLike.mem_coe,mem_insert,mem_union,E',O',mem_image,directions,extraDirections,mem_filter,mem_erase,mem_univ,and_true,D]
    rw [all_top_flats large]
    constructor
    · rintro (rfl|⟨t,tn,c,rfl|⟨rfl,m⟩⟩)
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨t,⟨tn,c⟩,rfl⟩)
      · exact Or.inr (Or.inr ⟨t,⟨⟨tn,c⟩,m⟩,rfl⟩)
    · rintro (rfl|⟨t,⟨tn,c⟩,rfl⟩|⟨t,⟨⟨tn,c⟩,m⟩,rfl⟩)
      · exact Or.inl rfl
      · exact Or.inr ⟨t,tn,c,Or.inl rfl⟩
      · exact Or.inr ⟨t,tn,c,Or.inr ⟨rfl,m⟩⟩
  have dis:Disjoint E' O' := by
    apply disjoint_left.mpr
    rintro _ h j
    obtain ⟨s,_,rfl⟩:=mem_image.mp h
    obtain ⟨t,_,eq⟩:=mem_image.mp j
    exact opposite_tags f s t eq.symm
  have dn:D∉E'∪O' := by
    intro j
    rcases mem_union.mp j with j|j
    · obtain ⟨s,_,eq⟩:=mem_image.mp j
      exact nonvertical_even f s eq
    · obtain ⟨s,hs,eq⟩:=mem_image.mp j
      exact nonvertical_odd f (mem_erase.mp (mem_filter.mp (mem_filter.mp hs).1).1).1 eq
  rw [eq,Set.ncard_coe_finset,card_insert_of_notMem dn,card_union_of_disjoint dis,
    card_image_of_injective _ (evenSheet_inj _),card_image_of_injective _ (oddSheet_inj _)]
  omega

end Green51PermutedPairs

#print axioms Green51PermutedPairs.all_top_flats
#print axioms Green51PermutedPairs.count_formula
