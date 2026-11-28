import Green51ShortenedColumns

/-! # Fibres of the augmented check map that admit a new label -/

open Finset Green50Downsets Green50Sharp Green51TenDimensions Green51PerfectColumns
open Green51WeightTransform Green51ShortenedColumns
open scoped Classical Pointwise
namespace Green51ExtensionFibres
local notation "F" => ZMod 2
local notation "V" => Cube 11

/-- All possible one-label extensions in the original ambient space. -/
noncomputable def holes (A:Finset V) : Finset V :=
  univ.filter fun v=>v∉A ∧ ¬FlatAt (insert v A) 0

private theorem hole_iff {A:Finset V} (high:18≤A.card) (avoid:¬FlatAt A 0) (v:V) :
    v∈holes A ↔ ∀T⊆A,T.card=1 ∨ T.card=3 ∨ T.card=5 → syndrome T≠v := by
  classical
  simp only [holes,mem_filter,mem_univ,true_and]
  constructor
  · rintro ⟨fresh,good⟩ T sub sz eq
    have vt:v∉T:=fun h=>fresh (sub h)
    rcases sz with one|odd
    · obtain ⟨a,rfl⟩:=card_eq_one.mp one
      exact vt (show v∈({a}:Finset V) by simpa [syndrome] using eq.symm)
    · apply good
      apply (flat_zero _).mpr
      have count:=card_insert_of_notMem fresh
      apply (Green51SparseDimensions.linear_three_iff (insert v A) (by omega)).mpr
      refine ⟨insert v T,insert_subset_insert v sub,?_,?_⟩
      · rw [card_insert_of_notMem vt];omega
      · change (∑ x∈insert v T,x)=0
        rw [sum_insert vt];exact (congrArg (v+·) eq).trans (ZModModule.add_self v)
  · intro missing
    have fresh:v∉A := fun h=>missing {v} (singleton_subset_iff.mpr h) (by simp) (by simp [syndrome])
    refine ⟨fresh,?_⟩
    intro bad
    have full:=card_insert_of_notMem fresh
    obtain ⟨T,sub,sz,zero⟩:=(Green51SparseDimensions.linear_three_iff (insert v A) (by omega)).mp
      ((flat_zero _).mp bad)
    by_cases hit:v∈T
    · have ta:T.erase v⊆A := by
        intro x hx
        exact (mem_insert.mp (sub (mem_erase.mp hx).2)).resolve_left (mem_erase.mp hx).1
      have cs:=card_erase_add_one hit
      have sum:=T.add_sum_erase id hit
      exact missing (T.erase v) ta (by omega)
        (add_left_cancel (sum.trans (zero.trans (ZModModule.add_self v).symm)))
    · have ta:T⊆A := fun x hx =>(mem_insert.mp (sub hx)).resolve_left fun e=>hit (e ▸ hx)
      exact avoid ((flat_zero _).mpr ((Green51SparseDimensions.linear_three_iff A (by omega)).mpr ⟨T,ta,sz,zero⟩))

noncomputable def pool {n:ℕ} (C:Submodule F (Cube n)) : Finset (Cube n) :=
  (dualWords C).filter fun z=>(supp z).card%4=3

noncomputable def triples {n:ℕ} (C:Submodule F (Cube n)) : Finset (Cube n) :=
  (dualWords C).filter fun z=>(supp z).card=3

private theorem uniform {A:Finset V} (D:Presentation A) (z:Cube A.card) :
    z∈pool D.P.ker ↔ ∀y,D.P y=D.P z → (supp y).card%4=3 := by
  have four (c:D.P.ker) : 4∣(supp c.val).card := by
    have h:=D.allowed c;simp only [mem_insert,mem_singleton] at h;omega
  change z∈(dualWords D.P.ker).filter _ ↔ _
  rw [mem_filter]
  constructor
  · rintro ⟨orth,w⟩ y eq
    let c:D.P.ker := ⟨z+y,by change D.P (z+y)=0;rw [map_add,eq,ZModModule.add_self]⟩
    have q:=(weight_mod_four z c.val (four c)).mpr ((mem_filter.mp orth).2 c)
    have back:z+c.val=y:=by dsimp [c];rw [←add_assoc,ZModModule.add_self,zero_add]
    rwa [back,w] at q
  · intro all
    have w:=all z rfl
    refine ⟨mem_filter.mpr ⟨mem_univ _,?_⟩,w⟩
    intro c
    apply (weight_mod_four z c.val (four c)).mp
    rw [w,all _ (by rw [map_add,show D.P c.val=0 from c.property,add_zero])]

private theorem same_pool {A:Finset V} (D:Presentation A) {z y:Cube A.card} (h:z∈pool D.P.ker)
    (eq:D.P y=D.P z) : y∈pool D.P.ker :=
  (uniform D y).mpr fun t ht=>(uniform D z).mp h t (ht.trans eq)

private theorem fst_one {A:Finset V} (D:Presentation A) {z:Cube A.card} (odd:(supp z).card%2=1) :
    (D.P z).1=1 := by
  rw [D.eval]
  change ((supp z).card:F)=1
  rw [←ZMod.natCast_mod _ 2,odd];rfl

private theorem hole_fibre {A:Finset V} (lo:18≤A.card) (avoid:¬FlatAt A 0) (D:Presentation A)
    (v:V) : v∈holes A ↔ (1,v)∈((pool D.P.ker).image D.P)\((triples D.P.ker).image D.P) := by
  classical
  constructor
  · intro hv
    obtain ⟨fresh,good⟩:=(mem_filter.mp hv).2
    have full:=card_insert_of_notMem fresh
    have all (y:Cube A.card) (eq:D.P y=(1,v)) : (supp y).card%4=3 := by
      have par:=congrArg Prod.fst ((D.eval y).symm.trans eq)
      have val:=congrArg ZMod.val par
      change ((supp y).card:F).val=1 at val
      rw [ZMod.val_natCast] at val
      have sy:syndrome (selected A y)=v:=congrArg Prod.snd ((D.eval y).symm.trans eq)
      have outside:v∉selected A y:=fun h=>fresh (selected_sub _ _ h)
      have sz:(insert v (selected A y)).card=(supp y).card+1:=by rw [card_insert_of_notMem outside,selected_card]
      have zero:syndrome (insert v (selected A y))=0:=by
        change (∑ x∈insert v (selected A y),x)=0
        rw [sum_insert outside];exact (congrArg (v+·) sy).trans (ZModModule.add_self v)
      have four:=Green51ResidualPacking.four_divisibility (by omega : 18≤(insert v A).card) good
        (insert_subset_insert v (selected_sub _ _)) (by rw [sz];omega) zero
      rw [sz] at four;omega
    obtain ⟨z,eq⟩:=D.onto (1,v)
    refine mem_sdiff.mpr ⟨mem_image.mpr ⟨z,(uniform D z).mpr (fun y h=>all y (h.trans eq)),eq⟩,?_⟩
    intro hit
    obtain ⟨u,hu,uv⟩:=mem_image.mp hit
    apply (hole_iff lo avoid v).mp hv (selected A u) (selected_sub ..) (Or.inr (Or.inl
      ((selected_card ..).trans (mem_filter.mp hu).2)))
    exact congrArg Prod.snd ((D.eval u).symm.trans uv)
  · intro h
    obtain ⟨pos,neg⟩:=mem_sdiff.mp h
    obtain ⟨z,hz,zv⟩:=mem_image.mp pos
    apply (hole_iff lo avoid v).mpr
    intro T sub sz sy
    obtain ⟨u,hu⟩:=selected_onto A sub
    have wt: (supp u).card=T.card:=(selected_card A u).symm.trans (congrArg card hu)
    have uv:D.P u=(1,v) := Prod.ext (fst_one D (by omega)) (by rw [D.eval];change syndrome (selected A u)=v;rw [hu,sy])
    have ok:=same_pool D hz (uv.trans zv.symm)
    have cs:=(mem_filter.mp ok).2
    exact neg (mem_image.mpr ⟨u,mem_filter.mpr ⟨(mem_filter.mp ok).1,by omega⟩,uv⟩)

/-- Each eligible syndrome represents one full kernel coset. Triple words
give distinct forbidden syndromes since the code has minimum distance eight. -/
theorem hole_count {A:Finset V} (lo:18≤A.card) (avoid:¬FlatAt A 0) (D:Presentation A) :
    ((holes A).card+(triples D.P.ker).card)*Fintype.card D.P.ker=(pool D.P.ker).card := by
  classical
  let U:=pool D.P.ker
  let T:=triples D.P.ker
  let H:=U.image D.P
  let B:=T.image D.P
  have fibers (s) (hs:s∈H) : (U.filter fun z=>D.P z=s).card=Fintype.card D.P.ker := by
    obtain ⟨u,hu,us⟩:=mem_image.mp hs
    have eq:(U.filter fun z=>D.P z=s)=univ.filter (fun z=>D.P z=s) := by
      ext y;simp only [mem_filter,mem_univ,true_and,and_iff_right_iff_imp]
      exact fun hy=>same_pool D hu (hy.trans us.symm)
    let e : {z:Cube A.card // D.P z=s} ≃ D.P.ker :=
      AddMonoidHom.fiberEquivKerOfSurjective (f:=D.P.toAddMonoidHom) D.onto s
    rw [eq,←Fintype.card_subtype]
    exact Fintype.card_congr e
  have ucount:U.card=H.card*Fintype.card D.P.ker := by
    calc
      _ = ∑ s∈H,(U.filter fun z=>D.P z=s).card := card_eq_sum_card_image D.P U
      _ = ∑ _s∈H,Fintype.card D.P.ker := sum_congr rfl fibers
      _ = _ := by simp
  have sub:T⊆U := by
    intro t ht;obtain ⟨o,w⟩:=mem_filter.mp ht
    exact mem_filter.mpr ⟨o,by rw [w]⟩
  have inj:Set.InjOn D.P (T:Set (Cube A.card)) := by
    intro x hx y hy eq
    let c:D.P.ker:=⟨x+y,by change D.P (x+y)=0;rw [map_add,eq,ZModModule.add_self]⟩
    have h:=D.allowed c
    simp only [mem_insert,mem_singleton] at h
    have wx: (supp x).card=3:=(mem_filter.mp hx).2
    have wy: (supp y).card=3:=(mem_filter.mp hy).2
    have w:=Green51AffineMatchings.weight_sum x y
    change (supp (x+y)).card=0 ∨ _ at h
    have empty:supp (x+y)=∅ := card_eq_zero.mp (by dsimp only [c] at h;omega)
    have zero:x+y=0:=by
      funext i;by_contra! non
      have hit:i∈supp (x+y):=mem_filter.mpr ⟨mem_univ _,non⟩
      rw [empty] at hit;exact notMem_empty i hit
    exact add_right_cancel (zero.trans (ZModModule.add_self y).symm)
  have bc:B.card=T.card:=card_image_of_injOn inj
  let label : V ↪ F×V:=⟨fun x=>(1,x),fun x y h=>congrArg Prod.snd h⟩
  have diff:(holes A).map label=H\B := by
    ext p
    constructor
    · intro h
      obtain ⟨v,hv,rfl⟩:=mem_map.mp h
      exact (hole_fibre lo avoid D v).mp hv
    · intro h
      obtain ⟨z,hz,zp⟩:=mem_image.mp (mem_sdiff.mp h).1
      have wt:=(mem_filter.mp hz).2
      have ep:(D.P z).1=1:=fst_one D (by omega)
      have pe:label p.2=p:=Prod.ext ((congrArg Prod.fst zp).symm.trans ep).symm rfl
      refine mem_map.mpr ⟨p.2,(hole_fibre lo avoid D p.2).mpr ?_,pe⟩
      change label p.2∈H\B; rwa [pe]
  have count:=congrArg card diff
  rw [card_map,card_sdiff_of_subset (image_subset_image sub)] at count
  change (holes A).card=H.card-B.card at count
  have le:B.card≤H.card:=card_le_card (image_subset_image sub)
  change ((holes A).card+T.card)*Fintype.card D.P.ker=U.card
  rw [show (holes A).card+T.card=H.card by omega,ucount]

end Green51ExtensionFibres
#print axioms Green51ExtensionFibres.hole_count
