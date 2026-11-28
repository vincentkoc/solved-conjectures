import Green51SmallResidual
import Green51SeventeenSection
import Green51SectionCoordinates

/-! # Seventeen coplanar labels among twenty-one in twelve dimensions -/

open Finset Green50Downsets Green50Sharp Green51TenDimensions
open Green51SimplexSection Green51SimplexFibres Green51SectionCoordinates
open scoped Classical Pointwise
namespace Green51TwentyOneSection
local notation "F" => ZMod 2
local notation "V" => Cube 12

theorem coplanar (A:Finset V) (size:A.card=21) :
    ∃(T:Finset V) (K:V→ₗ[F] F) (a:V), T⊆A ∧ T.card=17 ∧ K≠0 ∧ ∀x∈T,K x=K a := by
  classical
  let e : Fin 21 ≃ ↥A := (finCongr size.symm).trans A.equivFin.symm
  let pick : Fin 21 ↪ V := e.toEmbedding.trans (Function.Embedding.subtype _)
  let E : Module.Dual F (F×V) →ₗ[F] Cube 21 :=
    { toFun := fun l i => l (1,pick i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have light : ∃l:Module.Dual F (F×V), l≠0 ∧ (supp (E l)).card≤4 := by
    by_contra! all
    have inj : Function.Injective E := by
      intro u v eq
      apply sub_eq_zero.mp
      by_contra ne
      have h := all (u-v) ne
      rw [map_sub,eq,sub_self] at h
      simp [supp] at h
    have high : 13≤Module.finrank F E.range := by
      rw [E.finrank_range_of_inj inj];simp [Module.finrank_prod,Cube]
    obtain ⟨u,nu,small⟩ := Green51SmallResidual.twenty_one E.range high
    obtain ⟨l,hl⟩ := u.property
    have nl : l≠0 := by rintro rfl; exact nu (Subtype.ext (hl.symm.trans (map_zero E)))
    have h := all l nl
    rw [hl] at h; omega
  obtain ⟨l,non,small⟩ := light
  let Z := (supp (E l))ᶜ.map pick
  have enough : 17≤Z.card := by
    change 17≤((supp (E l))ᶜ.map pick).card
    rw [card_map,card_compl,Fintype.card_fin];omega
  obtain ⟨T,sub,pts⟩ := exists_subset_card_eq enough
  have zero (x) (hx:x∈T) : l (1,x)=0 := by
    obtain ⟨i,hi,rfl⟩ := mem_map.mp (sub hx)
    simpa [supp,E] using mem_compl.mp hi
  obtain ⟨a,ha⟩ := card_pos.mp (show 0<T.card by omega)
  let K := l.comp (LinearMap.inr F F V)
  have split (x:V) : l (1,x)=l (1,0)+K x :=
    by simpa only [Prod.mk_add_mk,add_zero,zero_add,K,LinearMap.comp_apply,LinearMap.inr_apply] using
         map_add l ((1:F),(0:V)) (0,x)
  refine ⟨T,K,a,?_,pts,?_,fun x hx =>
    add_left_cancel ((split x).symm.trans ((zero _ hx).trans ((zero _ ha).symm.trans (split a))))⟩
  · intro x hx
    obtain ⟨i,_,rfl⟩ := mem_map.mp (sub hx)
    exact (e i).property
  · intro off
    apply non
    have base := zero _ ha
    rw [split,off,LinearMap.zero_apply,add_zero] at base
    apply LinearMap.ext
    rintro ⟨c,x⟩
    rcases (show ∀b:F,b=0 ∨ b=1 from by decide) c with rfl|rfl
    · exact LinearMap.congr_fun off x
    · change l (1,x)=0
      rw [split,off,LinearMap.zero_apply,base,add_zero]

theorem has_core (A:Finset V) (size:A.card=21) (avoid:¬∃p,FlatAt A p) :
    ∃(L:Cube 10 →ₗ[F] V) (t:V), Function.Injective L ∧ core L t⊆A := by
  classical
  obtain ⟨T,K,a,sub,sz,nz,level⟩ := coplanar A size
  obtain ⟨f,U,inj,_,repr⟩ := chart K nz a T level
  have iu : Function.Injective (fun x=>f x+a) := fun _ _ h=>inj (add_right_cancel h)
  have pts : U.card=17 := by rwa [←repr,card_image_of_injective _ iu] at sz
  have inc (x) (hx:x∈U) : f x+a∈A := sub (repr ▸ mem_image_of_mem _ hx)
  have free : ¬∃p,FlatAt U p := fun ⟨p,h⟩ => avoid ⟨_,transfer f inj a inc h⟩
  obtain ⟨D,c,dnz,fifteen⟩ := Green51SeventeenSection.hyperplane U pts free
  let B := U.filter (fun x => D x=c)
  have szB:B.card=15 := fifteen
  obtain ⟨b,hb⟩ := card_pos.mp (show 0<B.card by omega)
  have eb : D b=c := (mem_filter.mp hb).2
  obtain ⟨j,S,ji,_,rep⟩ := chart D dnz b B (fun x hx => (mem_filter.mp hx).2.trans eb.symm)
  have iS : Function.Injective (fun x=>j x+b) := fun _ _ h=>ji (add_right_cancel h)
  have ps : S.card=15 := by rwa [←rep,card_image_of_injective _ iS] at szB
  have ins (x) (hx:x∈S) : j x+b∈U := (mem_filter.mp (show j x+b∈B from rep ▸ mem_image_of_mem _ hx)).1
  have no : ¬FlatAt S 0 := fun h=>free ⟨_,transfer j ji b ins h⟩
  obtain ⟨L,t,Li,_,modelEq⟩ := position (f.comp j) (inj.comp ji) (f b+a) S ps no
  refine ⟨L,t,Li,?_⟩
  rw [modelEq]
  intro x hx
  obtain ⟨y,hy,rfl⟩ := mem_image.mp hx
  simpa only [LinearMap.comp_apply,map_add,add_assoc] using inc _ (ins _ hy)

end Green51TwentyOneSection
#print axioms Green51TwentyOneSection.coplanar
#print axioms Green51TwentyOneSection.has_core
