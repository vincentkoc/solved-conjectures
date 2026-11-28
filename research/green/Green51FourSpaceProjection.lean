import Green51QuadraticFlats

/-! # Quotient sums of the pairs representing a binary flat -/

open Finset Green50Downsets
open scoped Classical Pointwise symmDiff
namespace Green51FourSpace
local notation "F" => ZMod 2

variable {I G : Type*} [DecidableEq I] [AddCommGroup G] [Module F G]

/-- In characteristic two symmetric difference adds the two subset sums. -/
theorem subset_sum_add (a : I → G) (U V : Finset I) :
    (∑ i ∈ (U ∆ V), a i) = (∑ i ∈ U, a i) + ∑ i ∈ V, a i := by
  classical
  have h1 := sum_inter_add_sum_sdiff U V a
  have h2 := sum_inter_add_sum_sdiff V U a
  have dis : Disjoint (U \ V) (V \ U) := by
    rw [disjoint_left];intro i hi hj
    exact (mem_sdiff.mp hi).2 (mem_sdiff.mp hj).1
  rw [inter_comm V U] at h2
  rw [Finset.symmDiff_def, sum_union dis,←h1,←h2,add_add_add_comm,ZModModule.add_self,zero_add]

/-- A switch of endpoints realizes every element of the span of their differences. -/
theorem span_iff_subset_sum (a : I → G) (S : Finset I) (v : G) :
    v ∈ Submodule.span F (a '' (S : Set I)) ↔
      ∃ T ⊆ S, (∑ i ∈ T, a i) = v := by
  constructor
  · intro h
    induction h using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨i,hi,rfl⟩ := hv
      exact ⟨{i},singleton_subset_iff.mpr hi,by simp⟩
    | zero => exact ⟨∅,empty_subset _,sum_empty⟩
    | add x y hx hy ix iy =>
      obtain ⟨U,hu,rfl⟩ := ix
      obtain ⟨V,hv,rfl⟩ := iy
      refine ⟨U ∆ V,?_,subset_sum_add a U V⟩
      intro i hi
      rcases Finset.mem_symmDiff.mp hi with hi|hi
      · exact hu hi.1
      · exact hv hi.1
    | smul c x hx ih =>
      rcases (show ∀ b:F,b=0 ∨ b=1 from by decide) c with rfl|rfl
      · exact ⟨∅,empty_subset _,by simp⟩
      · simpa using ih
  · rintro ⟨T,hT,rfl⟩
    exact Submodule.sum_mem _ fun i hi => Submodule.subset_span ⟨i,hT hi,rfl⟩


def endpoint (a δ : I → G) (s : I × F) : G := a s.1 + s.2 • δ s.1

private theorem endpoint_sum (a δ : I → G) (S T : Finset I) (sub:T⊆S) :
    (∑ i ∈ S, endpoint a δ (i, if i∈T then 1 else 0)) =
      (∑ i ∈ S,a i) + ∑ i ∈ T,δ i := by
  simp only [endpoint,sum_add_distrib,ite_smul,one_smul,zero_smul,sum_ite_mem,inter_eq_right.mpr sub]

/-- A nonempty selection of one endpoint per pair cannot vanish at weights
two, four or six when distinct endpoints have no short even relation. -/
theorem no_short_switch (a δ : I → G)
    (short : ∀ B : Finset (I × F), B.card=2 ∨ B.card=4 ∨ B.card=6 →
      (∑ s∈B,endpoint a δ s)≠0)
    (S : Finset I) (size : S.card=2 ∨ S.card=4 ∨ S.card=6) :
    (∑ i∈S,a i) ∉ Submodule.span F (δ '' (S : Set I)) := by
  intro inside
  obtain ⟨T,sub,eq⟩ := (span_iff_subset_sum δ S _).mp inside
  let f (i:I) : I × F := (i,if i∈T then 1 else 0)
  have inj : Function.Injective f := fun _ _ e => congrArg Prod.fst e
  apply short (S.image f) (by rwa [card_image_of_injective _ inj])
  rw [sum_image inj.injOn]
  exact (endpoint_sum a δ S T sub).trans (by rw [eq,ZModModule.add_self])

/-- An additional pair realizes any omitted direction once, so short projected
relations are impossible even when the switch uses a pair outside the support. -/
theorem no_extra_pair (a δ : I → G)
    (short : ∀ B : Finset (I × F), B.card=2 ∨ B.card=4 ∨ B.card=6 →
      (∑ s∈B,endpoint a δ s)≠0)
    (S : Finset I) (size : S.card=2 ∨ S.card=4) (j:I) (outside:j∉S) :
    (∑ i∈S,a i)+δ j ∉ Submodule.span F (δ '' (S : Set I)) := by
  intro inside
  obtain ⟨T,sub,eq⟩ := (span_iff_subset_sum δ S _).mp inside
  let f (i:I) : I × F := (i,if i∈T then 1 else 0)
  have inj : Function.Injective f := fun _ _ e => congrArg Prod.fst e
  have pairNe : (j,(0:F))≠(j,1) := by simp
  have off (b:F) : (j,b)∉S.image f := by
    rintro h
    obtain ⟨i,hi,e⟩ := mem_image.mp h
    have same : i=j := congrArg Prod.fst e
    exact outside (same ▸ hi)
  let B := insert (j,(0:F)) (insert (j,1) (S.image f))
  have h0 : (j,(0:F))∉insert (j,1) (S.image f) := by simp [pairNe,off]
  have hs : B.card=4 ∨ B.card=6 := by
    simp only [B,card_insert_of_notMem h0,card_insert_of_notMem (off 1),card_image_of_injective _ inj]
    omega
  apply short B (Or.inr hs)
  rw [show B=insert (j,0) (insert (j,1) (S.image f)) from rfl,
    sum_insert h0,sum_insert (off 1),sum_image inj.injOn]
  have calcSum := endpoint_sum a δ S T sub
  change (∑ i∈S,endpoint a δ (f i))=_ at calcSum
  rw [calcSum,eq]
  simp only [endpoint,zero_smul,one_smul,add_zero]
  calc
    _ = (a j+a j)+((∑ i∈S,a i)+(∑ i∈S,a i))+(δ j+δ j) := by abel
    _ = 0 := by simp [ZModModule.add_self]

variable {d:ℕ}

/-- The vertical quotient of a represented flat has no two- or four-site
relation. A six-site relation has deficient affine span amongst the indices. -/
theorem projected_support (a:Cube d → G) (e:(F × Cube d) →ₗ[F] G)
    (short : ∀ B : Finset (Cube d × F), B.card=2 ∨ B.card=4 ∨ B.card=6 →
      (∑ s∈B,endpoint a (fun z=>e (1,z)) s)≠0)
    (S:Finset (Cube d)) (rel:(∑ i∈S,a i)∈e.range) :
    S.card≠2 ∧ S.card≠4 ∧ (S.card=6 →
      Submodule.span F ((fun z:Cube d => ((1:F),z)) '' (S:Set (Cube d))) ≠ ⊤) := by
  let δ (i:Cube d) := e (1,i)
  let U := Submodule.span F (δ '' (S:Set (Cube d)))
  have memδ (i:Cube d) (hi:i∈S) : δ i∈U := Submodule.subset_span ⟨i,hi,rfl⟩
  obtain ⟨⟨b,z⟩,hz⟩ := rel
  have exclude (size:S.card=2 ∨ S.card=4) : False := by
    obtain ⟨i,hi⟩ := card_pos.mp (show 0<S.card by omega)
    have avail : ∃ j:Cube d,(∑ k∈S,a k)+δ j ∈ U := by
      rcases (show ∀ x:F,x=0 ∨ x=1 from by decide) b with rfl|rfl
      · refine ⟨z+i,?_⟩
        rw [←hz]
        change e ((0:F),z)+e (1,z+i) ∈ U
        rw [←map_add,show (((0:F),z)+(1,z+i))=(1,i) by ext <;> simp [←add_assoc,ZModModule.add_self]]
        exact memδ i hi
      · exact ⟨z,by rw [←hz];change e ((1:F),z)+e (1,z)∈U;rw [ZModModule.add_self];exact U.zero_mem⟩
    obtain ⟨j,hj⟩ := avail
    by_cases inside : j∈S
    · have h := U.add_mem hj (memδ j inside)
      rw [add_assoc,ZModModule.add_self,add_zero] at h
      exact no_short_switch a δ short S (size.imp_right Or.inl) h
    · exact no_extra_pair a δ short S size j inside hj
  refine ⟨fun h => exclude (Or.inl h),fun h => exclude (Or.inr h),?_⟩
  intro size full
  apply no_short_switch a δ short S (Or.inr (Or.inr size))
  have v : (b,z) ∈ Submodule.span F ((fun i:Cube d => ((1:F),i)) '' (S:Set (Cube d))) := by rw [full];trivial
  rw [←hz]
  have h := Submodule.mem_map_of_mem (f:=e) v
  rwa [Submodule.map_span,Set.image_image] at h

end Green51FourSpace

#print axioms Green51FourSpace.subset_sum_add
#print axioms Green51FourSpace.span_iff_subset_sum
#print axioms Green51FourSpace.projected_support
