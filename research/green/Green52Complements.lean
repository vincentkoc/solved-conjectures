import Green50Graphs

/-! # Exact subgroup complements in binary spaces -/

open Finset
open scoped Pointwise
namespace Green52Complements
local notation "K" => ZMod 2
variable {G : Type*} [AddCommGroup G] [Module K G] [Fintype G] [DecidableEq G]

/-- For a prescribed covering subspace, choose a representative in the set
above each point of a complementary input space. -/
theorem graph_of_subspace_cover (A : Set G) (U V : Submodule K G)
    (h : A + (V : Set G) = Set.univ) :
    ∃ f : U → V, (Green50Graphs.graph U V f : Set G) ⊆ A := by
  classical
  have hits (u : U) : ∃ v : V, (u:G) + (v:G) ∈ A := by
    have hz : (u:G) ∈ A + (V:Set G) := h ▸ Set.mem_univ _
    obtain ⟨a,ha,v,hv,he⟩ := hz
    exact ⟨⟨-v,V.neg_mem hv⟩,by change (u:G) + -v ∈ A; simpa [←he] using ha⟩
  choose f hf using hits
  refine ⟨f,?_⟩
  intro z hz
  obtain ⟨u,_,rfl⟩ := mem_image.mp hz
  exact hf u

/-- A set covered by translations along a finite complement contains a full graph
whose output dimension is at most the size of that complement minus one. -/
theorem graph_of_cover (A : Set G) (S : Finset G)
    (h : A + (S : Set G) = Set.univ) :
    ∃ (U V : Submodule K G), IsCompl U V ∧ Module.finrank K V ≤ S.card - 1 ∧
      ∃ f : U → V, (Green50Graphs.graph U V f : Set G) ⊆ A := by
  classical
  have hn : S.Nonempty := by
    by_contra! he
    have hz : (0:G) ∈ A + (S:Set G) := h ▸ Set.mem_univ _
    obtain ⟨_,_,s,hs,_⟩ := hz
    simp [he] at hs
  obtain ⟨s₀,hs₀⟩ := hn
  let D := (S.erase s₀).image (fun s => s - s₀)
  let V := Submodule.span K (D : Set G)
  have step (s) (hs : s ∈ S) : s - s₀ ∈ V := by
    by_cases hss : s = s₀
    · simp [hss]
    · exact Submodule.subset_span (mem_image_of_mem _ (mem_erase.mpr ⟨hss,hs⟩))
  have dim : Module.finrank K V ≤ S.card - 1 := calc
    _ ≤ D.card := by simpa [V] using (finrank_span_le_card (R := K) (D : Set G))
    _ ≤ (S.erase s₀).card := card_image_le
    _ = _ := card_erase_of_mem hs₀
  have covers : A + (V : Set G) = Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    have hz : x + s₀ ∈ A + (S:Set G) := h ▸ Set.mem_univ _
    obtain ⟨a,ha,s,hs,he⟩ := hz
    change a + s = x + s₀ at he
    refine ⟨a,ha,s-s₀,step s hs,?_⟩
    calc
      a + (s-s₀) = (a+s)-s₀ := by abel
      _ = x := by rw [he,add_sub_cancel_right]
  obtain ⟨U,hVU⟩ := V.exists_isCompl
  obtain ⟨f,hf⟩ := graph_of_subspace_cover A U V covers
  exact ⟨U,V,hVU.symm,dim,f,hf⟩

omit [Fintype G] [DecidableEq G] in
/-- The graph and its vertical complement represent every point in exactly one way. -/
theorem graph_tiles (U V : Submodule K G) (h : IsCompl U V) (f : U → V) (x : G) :
    ∃! p : U × V, (p.1:G) + (f p.1:G) + (p.2:G) = x := by
  let e := ((Equiv.refl U).prodShear fun u => Equiv.addLeft (f u)).trans
    (U.prodEquivOfIsCompl V h).toEquiv
  have he (p : U × V) : e p = (p.1:G) + (f p.1:G) + (p.2:G) := by
    change (p.1:G) + ((f p.1:G) + (p.2:G)) = _
    rw [add_assoc]
  simpa only [he] using e.bijective.existsUnique x

abbrev Cube (n : ℕ) := Fin n → K

/-- The requested affine subspace for a given summand set and codimension. -/
def Flat (n d : ℕ) (A : Set (Cube n)) : Prop :=
  ∃ W : AffineSubspace K (Cube n), (W : Set (Cube n)) ⊆ A + A ∧
    n ≤ Module.finrank K W.direction + d

/-- Green 52 at the exact quantifiers of its pinned statement. -/
def CoverStatement : Prop :=
  ∃ c : ℕ → ℕ, ∀ (n k : ℕ) (A : Set (Cube n)) (S : Finset (Cube n)),
    S.card = k → A + (S : Set (Cube n)) = Set.univ → Flat n (c k) A

/-- It suffices to treat full function graphs, measured only by their output dimension. -/
def GraphStatement : Prop :=
  ∃ b : ℕ → ℕ, ∀ n (U V : Submodule K (Cube n)), IsCompl U V → ∀ f : U → V,
    Flat n (b (Module.finrank K V)) (Green50Graphs.graph U V f : Set (Cube n))

/-- Arbitrary additive complements and exact graph tilings give equivalent problems. -/
theorem cover_iff_graph : CoverStatement ↔ GraphStatement := by
  classical
  constructor
  · rintro ⟨c,hc⟩
    refine ⟨fun d => c (2^d),?_⟩
    intro n U V h f
    let S := (V : Set (Cube n)).toFinset
    have hcard : S.card = 2^(Module.finrank K V) := by
      rw [show S.card = Fintype.card V from Set.toFinset_card _]
      simpa using (Module.card_eq_pow_finrank : Fintype.card V = Fintype.card K ^ Module.finrank K V)
    apply hc n _ _ S hcard
    refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨⟨u,v⟩,hx,_⟩ := graph_tiles U V h f x
    exact ⟨_,mem_image_of_mem _ (mem_univ u),v.val,by simp [S],hx⟩
  · rintro ⟨b,hb⟩
    refine ⟨fun k => (range (k+1)).sup b,?_⟩
    rintro n k A S rfl hcover
    obtain ⟨U,V,hu,hd,f,hf⟩ := graph_of_cover A S hcover
    obtain ⟨W,hw,hr⟩ := hb n U V hu f
    have hle : b (Module.finrank K V) ≤ (range (S.card+1)).sup b :=
      le_sup (f := b) (mem_range.mpr (by omega))
    exact ⟨W,hw.trans (Set.add_subset_add hf hf),hr.trans (Nat.add_le_add_left hle _)⟩

omit [Fintype G] [DecidableEq G] in
/-- Refining a cover by translates gives exactly as many colour classes.
The twofold sumset of every class lies in the same original sumset. -/
theorem partition_of_cover (A : Set G) (S : Finset G)
    (h : A + (S : Set G) = Set.univ) :
    ∃ P : Fin S.card → Set G, (⋃ i, P i) = Set.univ ∧
      Pairwise (fun i j => Disjoint (P i) (P j)) ∧ ∀ i, P i + P i ⊆ A + A := by
  classical
  let colour : Fin S.card → G := fun i => (S.equivFin.symm i).val
  have assign (x : G) : ∃ i, x - colour i ∈ A := by
    have hz : x ∈ A + (S : Set G) := h ▸ Set.mem_univ _
    obtain ⟨a,ha,s,hs,rfl⟩ := hz
    refine ⟨S.equivFin ⟨s,hs⟩,?_⟩
    simpa [colour] using ha
  choose I hI using assign
  refine ⟨fun i => {x | I x = i},Set.eq_univ_of_forall (fun x => Set.mem_iUnion.mpr ⟨I x,rfl⟩),?_,?_⟩
  · intro i j hij
    exact Set.disjoint_left.mpr fun _ hx hy => hij (hx.symm.trans hy)
  · intro i z hz
    obtain ⟨x,hx,y,hy,rfl⟩ := hz
    change I x = i at hx
    change I y = i at hy
    refine ⟨x-colour i,hx ▸ hI x,y-colour i,hy ▸ hI y,?_⟩
    have ht : colour i + colour i = 0 := by
      rw [← two_smul K,show (2:K)=0 by decide,zero_smul]
    calc
      x - colour i + (y - colour i) = x + y - (colour i + colour i) := by abel
      _ = _ := by rw [ht,sub_zero]

/-- Green's partition problem implies the additive-complement problem with the same bound. -/
theorem partition_implies_cover (c : ℕ → ℕ)
    (hp : ∀ (n k : ℕ) (P : Fin k → Set (Cube n)), (⋃ i, P i) = Set.univ →
      Pairwise (fun i j => Disjoint (P i) (P j)) → ∃ i, Flat n (c k) (P i)) :
    ∀ (n k : ℕ) (A : Set (Cube n)) (S : Finset (Cube n)), S.card = k →
      A + (S : Set (Cube n)) = Set.univ → Flat n (c k) A := by
  rintro n k A S rfl hc
  obtain ⟨P,hall,hdis,hsum⟩ := partition_of_cover A S hc
  obtain ⟨i,W,hw,hr⟩ := hp n S.card P hall hdis
  exact ⟨W,hw.trans (hsum i),hr⟩

end Green52Complements

#print axioms Green52Complements.graph_of_subspace_cover
#print axioms Green52Complements.graph_of_cover
#print axioms Green52Complements.graph_tiles
#print axioms Green52Complements.cover_iff_graph
#print axioms Green52Complements.partition_of_cover
#print axioms Green52Complements.partition_implies_cover
