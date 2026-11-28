import Green51EmbeddedEighteen
import Green51ExteriorPair
import Green51AffineEvaluation

/-! # Twenty-four points force an affine three-space in dimension twelve -/

open Finset Green50Downsets Green50Sharp Green51TenDimensions Green51SectionCoordinates
open scoped Classical Pointwise
namespace Green51TwelveSections
local notation "F" => ZMod 2
local notation "V" => Cube 12

/-- Any twenty-three labels with eighteen on one affine hyperplane already
force an affine three-space in their double. -/
theorem eighteen_on_hyperplane (A T : Finset V) (size : 23≤A.card) (sub : T⊆A)
    (large : 18≤T.card) (K : V →ₗ[F] F) (non : K≠0) (a : V)
    (level : ∀x∈T,K x=K a) : ∃p,FlatAt A p := by
  classical
  by_contra avoid
  obtain ⟨B,inc,count⟩ := exists_subset_card_eq large
  obtain ⟨f,U,inj,_,repr⟩ := chart K non a B (fun x hx => level _ (inc hx))
  have affineInj : Function.Injective (fun x => f x+a) := fun _ _ eq => inj (add_right_cancel eq)
  have pts : U.card=18 := by rwa [←repr,card_image_of_injective _ affineInj] at count
  obtain ⟨L,t,C,Li,coreSub,inC,three,outC,cDiff⟩ :=
    Green51EighteenSection.embedded f inj a avoid U pts
      (fun x hx => sub (inc (repr ▸ mem_image_of_mem _ hx)))
  exact avoid (exterior_pair L Li t coreSub size inC three outC cDiff)

/-- On a flat-free set, eighteen zeros of an affine functional force that
functional to vanish identically. -/
private theorem annihilator (A T : Finset V) (size : 23≤A.card) (sub : T⊆A)
    (large : 18≤T.card) (l : Module.Dual F (F×V)) (zero : ∀x∈T,l (1,x)=0)
    (avoid : ¬∃p,FlatAt A p) : l=0 := by
  obtain ⟨a,ha⟩ := card_pos.mp (show 0<T.card by omega)
  let K := l.comp (LinearMap.inr F F V)
  have split (x:V) : l (1,x)=l (1,0)+K x :=
    by simpa only [Prod.mk_add_mk,add_zero,zero_add,K,LinearMap.comp_apply,LinearMap.inr_apply] using
         map_add l ((1:F),(0:V)) (0,x)
  have off : K=0 := by
    by_contra non
    exact avoid (eighteen_on_hyperplane A T size sub large K non a (fun x hx =>
      add_left_cancel ((split x).symm.trans ((zero _ hx).trans ((zero _ ha).symm.trans (split a))))))
  have base := zero _ ha
  rw [split,off,LinearMap.zero_apply,add_zero] at base
  apply LinearMap.ext
  rintro ⟨c,x⟩
  rcases (show ∀b:F,b=0 ∨ b=1 from by decide) c with rfl|rfl
  · exact LinearMap.congr_fun off x
  · change l (1,x)=0
    rw [split,off,LinearMap.zero_apply,base,add_zero]

/-- Every twenty-four points of the twelve-dimensional binary cube have an
affine three-space in their pairwise sumset. -/
theorem twenty_four (A : Finset V) (size : A.card=24) : ∃p,FlatAt A p := by
  classical
  by_contra avoid
  let e : Fin 24 ≃ ↥A := (finCongr size.symm).trans A.equivFin.symm
  let pick : Fin 24 ↪ V := e.toEmbedding.trans (Function.Embedding.subtype _)
  let column : Fin 25 → V := Fin.cases (pick 0) pick
  let E : Module.Dual F (F × V) →ₗ[F] Cube 25 :=
    { toFun := fun l i => l (1,column i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have vanishes (l : Module.Dual F (F × V)) (few : (supp (E l)).card≤6) : l=0 := by
    let v : Cube 24 := fun i => l (1,pick i)
    have short : (supp v).card ≤ (supp (E l)).card := by
      rw [←card_map (f:=Fin.succEmb _) (s:=supp v)]
      apply card_le_card
      intro k hk
      obtain ⟨i,hi,rfl⟩ := mem_map.mp hk
      simpa [supp,E,column,Fin.succEmb,v] using hi
    let T := (supp v)ᶜ.map pick
    apply annihilator A T (by omega) ?_ ?_ l ?_ avoid
    · intro x hx
      obtain ⟨i,_,rfl⟩ := mem_map.mp hx
      exact (e i).property
    · change 18≤((supp v)ᶜ.map pick).card
      rw [card_map,card_compl,Fintype.card_fin];omega
    · intro x hx
      obtain ⟨i,hi,rfl⟩ := mem_map.mp hx
      simpa [supp,v] using mem_compl.mp hi
  have inj : Function.Injective E := by
    intro l m eq
    apply sub_eq_zero.mp
    apply vanishes
    rw [map_sub,eq,sub_self]
    simp [supp]
  have rank := Green51AffineEvaluation.rank_of_seven E.range (by
    intro z nz
    obtain ⟨l,hl⟩ := z.property
    by_contra! small
    have zl := vanishes l (by rw [hl]; omega)
    apply nz
    apply Subtype.ext
    rw [←hl,zl,map_zero]
    rfl)
  rw [E.finrank_range_of_inj inj] at rank
  simp [Module.finrank_prod,Cube] at rank

end Green51TwelveSections
#print axioms Green51TwelveSections.eighteen_on_hyperplane
#print axioms Green51TwelveSections.twenty_four
