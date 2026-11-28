import Green51FourSpaceCoordinates
import Green51FourSpaceCode

/-! # Projected affine supports in the sixteen standard coordinates -/
open Finset Green50Downsets Green50Sharp
open scoped Classical
namespace Green51FourSpace
local notation "F" => ZMod 2

private def level (a:F) (r:Fin 16) : Finset (Fin 16) :=
  univ.filter fun i=>a+(∑ j:Fin 4,decode 4 i.val j * decode 4 r.val j)=0

private theorem levels : ∀a:F,∀r:Fin 16,level a r=univ ∨
    ∃ p∈Certificate.planes,level a r⊆positions p := by decide +kernel

/-- Enumerate the labels of the affine four-space by their four-bit indices. -/
private noncomputable def listLabels : (Cube 4 → F) ≃ₗ[F] Cube 16 :=
  LinearEquiv.piCongrLeft' F (fun _:Cube 4=>F) (maskEquiv 4).symm

private theorem label_support (w:Cube 4→F) :
    (wordSupport w).image (maskEquiv 4).symm=supp (listLabels w) := by
  ext i
  simp only [mem_image]
  constructor
  · rintro ⟨z,hz,rfl⟩
    apply mem_filter.mpr
    refine ⟨mem_univ _,?_⟩
    change w ((maskEquiv 4) ((maskEquiv 4).symm z))≠0
    simpa using (mem_filter.mp hz).2
  · intro hi
    refine ⟨(maskEquiv 4) i,?_,(maskEquiv 4).symm_apply_apply _⟩
    exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hi).2⟩

theorem code_in_coordinates (K:Submodule F (Cube 4→F))
    (hw:∀w∈K,2∣(wordSupport w).card ∧ (wordSupport w).card≠2 ∧ (wordSupport w).card≠4 ∧
      ((wordSupport w).card=6 → Submodule.span F ((fun z:Cube 4 => ((1:F),z)) ''
        (wordSupport w:Set (Cube 4)))≠⊤)) :
    ∃ C:Submodule F (Cube 16),Module.finrank F C=Module.finrank F K ∧ validCode C := by
  classical
  refine ⟨K.map listLabels.toLinearMap,listLabels.finrank_map_eq K,?_⟩
  rintro v ⟨w,mem,rfl⟩
  obtain ⟨even,two,four,flat⟩:=hw w mem
  change 2∣(supp (listLabels w)).card ∧ _
  have size : (supp (listLabels w)).card=(wordSupport w).card := by
    rw [←label_support,card_image_of_injective _ (maskEquiv 4).symm.injective]
  refine ⟨size ▸ even,size ▸ two,size ▸ four,fun h=>?_⟩
  have ns:=flat (size ▸ h)
  let U:=Submodule.span F ((fun z:Cube 4 => ((1:F),z)) '' (wordSupport w:Set (Cube 4)))
  obtain ⟨D,ne,vanish⟩:=U.exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr ns)
  let l:=D.comp (LinearMap.inr F F (Cube 4))
  let a:=D (1,0)
  let r:=encode (fun j:Fin 4=>l (Pi.single j 1))
  let ix:Fin 16:=⟨r,encode_lt _⟩
  have evalD (i:Fin 16) : D (1,decode 4 i.val)=a+∑j:Fin 4,decode 4 i.val j*decode 4 ix.val j := by
    rw [show (1,decode 4 i.val)=((1,0)+(0,decode 4 i.val):F×Cube 4) by simp,map_add]
    change a + l (decode 4 i.val) = _
    rw [check_dot]
    have e : decode 4 ix.val=(fun j:Fin 4=>l (Pi.single j 1)) := decode_encode _
    rw [e]
  have some : level a ix≠univ := by
    intro eq
    have all (z:Cube 4) : D (1,z)=0 := by
      let i:Fin 16:=⟨encode z,encode_lt z⟩
      have hi : i∈level a ix := eq ▸ mem_univ _
      have h0 := (mem_filter.mp hi).2
      rw [←evalD] at h0
      simpa only [i,decode_encode] using h0
    apply ne
    apply LinearMap.ext
    rintro ⟨b,z⟩
    rcases (by decide : ∀b:F,b=0 ∨ b=1) b with rfl|rfl
    · rw [show ((0,z):F×Cube 4)=(1,0)+(1,z) by simp [Prod.mk_add_mk,ZModModule.add_self],map_add,all,all,add_zero]
      rfl
    · exact all _
  obtain ⟨p,hp,cover⟩:=(levels a ix).resolve_left some
  refine ⟨p,hp,fun i hi=>cover ?_⟩
  change i∈supp (listLabels w) at hi
  rw [←label_support] at hi
  obtain ⟨z,hz,hzi⟩:=mem_image.mp hi
  have az:((1:F),z)∈U:=Submodule.subset_span ⟨z,hz,rfl⟩
  have zero:D (1,z)=0 := vanish az
  have ez:decode 4 i.val=z := by
    subst i
    exact (maskEquiv 4).apply_symm_apply _
  exact mem_filter.mpr ⟨mem_univ _,(evalD i).symm.trans (ez ▸ zero)⟩
end Green51FourSpace
#print axioms Green51FourSpace.code_in_coordinates
