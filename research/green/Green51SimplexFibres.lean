import Green51SimplexExtension

/-! # Extending a fifteen-point simplex section inside an ambient binary cube -/

open Finset Green50Downsets Green51TenDimensions Green51SimplexExtension
open Green51SystematicChecks Green51SimplexSection Green51SimplexDirections Green51FourSpace
open scoped Pointwise
namespace Green51SimplexFibres
local notation "F" => ZMod 2
local notation "V" => Cube 10
variable {G : Type*} [AddCommGroup G] [Module F G] [DecidableEq G]

private theorem conflict {A : Finset G} (size : 5≤A.card) (avoid : ¬∃ p, FlatAt A p)
    {a b c d : G} (ha : a∈A) (hb : b∈A) (hc : c∈A) (hd : d∈A)
    (ab : a≠b) (cd : c≠d) (ac : a≠c) (ad : a≠d) (bc : b≠c) (bd : b≠d) :
    a+b≠c+d := by
  intro eq
  have sub : ({a,b,c,d}:Finset G)⊆A := by
    intro x hx
    simp only [mem_insert,mem_singleton] at hx
    rcases hx with rfl|rfl|rfl|rfl <;> assumption
  apply avoid
  refine ⟨0,(flat_zero A).mpr ((Green51SparseDimensions.linear_three_iff A size).mpr
    ⟨{a,b,c,d},sub,Or.inl ?_,?_⟩)⟩
  · simp [ab,ac,ad,bc,bd,cd]
  · simp only [sum_insert,mem_insert,mem_singleton,ab,ac,ad,bc,bd,cd,or_self,
      not_false_eq_true,Finset.sum_singleton]
    calc
      a+(b+(c+d)) = (a+b)+(c+d) := by abel
      _ = 0 := by rw [eq,ZModModule.add_self]

private theorem transfer_frame (L : V →ₗ[F] G) (inj : Function.Injective L)
    (A : Finset G) (S : Finset V) (hs : ∀ x∈S,L x∈A+A)
    (frame : HasFrame S) : ∃ p, FlatAt A p := by
  obtain ⟨p,J,j,all⟩ := frame
  let K := L.comp J
  refine ⟨L p,K.range,?_,?_⟩
  · simpa [Cube,K] using K.finrank_range_of_inj (inj.comp j)
  · rintro _ ⟨_,⟨v,rfl⟩,rfl⟩
    change L p+L (J v)∈A+A
    rw [←map_add]
    exact hs _ (all v)

def core (L : V →ₗ[F] G) (t : G) := model.image (fun x => L x+t)

private theorem old_double {L : V →ₗ[F] G} {t : G} {A : Finset G}
    (inc : core L t⊆A) {z : V} (hz : z∈model+model) : L z∈A+A := by
  obtain ⟨x,hx,y,hy,rfl⟩ := mem_add.mp hz
  exact mem_add.mpr ⟨_,inc (mem_image_of_mem _ hx),_,inc (mem_image_of_mem _ hy),
    by rw [map_add,add_add_add_comm (L x) t (L y) t,ZModModule.add_self,add_zero]⟩

/-- A pair outside the core and inside one of its parallel ten-flats has a
difference in the explicit set of twenty-eight directions. -/
theorem pair_direction {L : V →ₗ[F] G} (inj : Function.Injective L) {t : G} {A : Finset G}
    (size : 5≤A.card) (avoid : ¬∃ p, FlatAt A p) (inc : core L t⊆A)
    {a b : G} (ha : a∈A) (hb : b∈A) (na : a∉core L t) (nb : b∉core L t)
    (ab : a≠b) {x : V} (rep : L x=a+b) : encode x ∈ directions := by
  have pt : point 10 (encode x)=x := decode_encode x
  have non : a+b≠0 := fun z => ab (add_right_cancel (z.trans (ZModModule.add_self b).symm))
  have pos : encode x≠0 := by
    intro e
    have zx : x=0 := by simpa only [e,show point 10 0=0 from decode_zero 10] using pt.symm
    exact non (rep.symm.trans (zx ▸ map_zero L))
  by_contra absent
  rcases single_obstruction pos (encode_lt x) absent with old|frame
  · rw [pt] at old
    obtain ⟨u,hu,v,hv,sum⟩ := mem_add.mp old
    have cu : L u+t∈core L t := mem_image_of_mem _ hu
    have cv : L v+t∈core L t := mem_image_of_mem _ hv
    have eq : a+b=(L u+t)+(L v+t) := by
      rw [←rep,←sum,map_add,add_add_add_comm (L u) t (L v) t,ZModModule.add_self,add_zero]
    have diff : L u+t≠L v+t := fun h => non (eq.trans (h ▸ ZModModule.add_self (L v+t)))
    exact conflict size avoid ha hb (inc cu) (inc cv) ab diff
      (fun h => na (h ▸ cu)) (fun h => na (h ▸ cv))
      (fun h => nb (h ▸ cu)) (fun h => nb (h ▸ cv)) eq
  · apply avoid (transfer_frame L inj A _ ?_ frame)
    intro z hz
    rcases mem_insert.mp hz with rfl|h
    · rw [pt,rep]; exact add_mem_add ha hb
    · exact old_double inc h

/-- If two distinct listed differences already lie in the ambient double,
their binary sum must also be listed. -/
theorem pair_compatible {L : V →ₗ[F] G} (inj : Function.Injective L) {t : G} {A : Finset G}
    (avoid : ¬∃ p, FlatAt A p) (inc : core L t⊆A) {u w : ℕ}
    (hu : u∈directions) (hw : w∈directions) (ne : u≠w)
    (inU : L (point 10 u)∈A+A) (inW : L (point 10 w)∈A+A) : u ^^^ w∈directions := by
  by_contra absent
  apply avoid (transfer_frame L inj A _ ?_ (pair_obstruction hu hw ne absent))
  intro z hz
  rcases mem_insert.mp hz with rfl|h
  · exact inU
  rcases mem_insert.mp h with rfl|h
  exacts [inW,old_double inc h]

/-- Three differences forming a binary plane leave no additional compatible
listed direction in the same ambient double. -/
theorem plane_maximal {L : V →ₗ[F] G} (inj : Function.Injective L) {t : G} {A : Finset G}
    (avoid : ¬∃ p, FlatAt A p) (inc : core L t⊆A) {u v w : ℕ}
    (hu : u∈directions) (hv : v∈directions) (huv : u ^^^ v∈directions) (hw : w∈directions)
    (iu : L (point 10 u)∈A+A) (iv : L (point 10 v)∈A+A)
    (iuv : L (point 10 (u ^^^ v))∈A+A) (iw : L (point 10 w)∈A+A) :
    u=w ∨ v=w ∨ u ^^^ v=w := by
  by_contra! ne
  have uw := pair_compatible inj avoid inc hu hw ne.1 iu iw
  have vw := pair_compatible inj avoid inc hv hw ne.2.1 iv iw
  exact no_three_space hu hv hw huv uw vw
    (pair_compatible inj avoid inc huv hw ne.2.2 iuv iw)

/-- A pair sum in a flat-free configuration determines its unordered pair. -/
theorem pair_equal {A:Finset G} (size:5≤A.card) (avoid:¬∃p,FlatAt A p)
    {a b c d:G} (ha:a∈A) (hb:b∈A) (hc:c∈A) (hd:d∈A) (ab:a≠b) (cd:c≠d)
    (eq:a+b=c+d) : c∈({a,b}:Finset G) ∧ d∈({a,b}:Finset G) := by
  by_cases ac:a=c
  · subst c;have bd := add_left_cancel eq;subst d;simp
  by_cases ad:a=d
  · subst d;rw [add_comm c a] at eq;have bc := add_left_cancel eq;subst c;simp
  by_cases bc:b=c
  · subst c;rw [add_comm b d] at eq;have ad := add_right_cancel eq;subst d;simp
  by_cases bd:b=d
  · subst d;have ac := add_right_cancel eq;subst c;simp
  exact False.elim (conflict size avoid ha hb hc hd ab cd ac ad bc bd eq)

/-- Any exterior pair with direction in the core space must lie in a given
exterior three-point fibre, whenever the ambient double has no three-flat. -/
theorem triangle_controls {A B C:Finset G} (L:Cube 10→ₗ[F] G) (inj:Function.Injective L)
    (t:G) (inc:core L t⊆A) (size:5≤A.card) (avoid:¬∃p,FlatAt A p)
    (inB:B⊆A) (inC:C⊆A) (three:B.card=3) (two:C.card=2)
    (outB:Disjoint B (core L t)) (outC:Disjoint C (core L t))
    (bDiff:∀ x∈B,∀ y∈B,x+y∈L.range) (cDiff:∀ x∈C,∀ y∈C,x+y∈L.range) : C⊆B := by
  obtain ⟨a,b,c,ab,ac,bc,eqB⟩ := card_eq_three.mp three
  obtain ⟨d,e,de,eqC⟩ := card_eq_two.mp two
  have ha : a∈B := eqB ▸ (by simp)
  have hb : b∈B := eqB ▸ (by simp)
  have hc : c∈B := eqB ▸ (by simp)
  have hd : d∈C := eqC ▸ (by simp)
  have he : e∈C := eqC ▸ (by simp)
  obtain ⟨u,ru⟩ := bDiff _ ha _ hb
  obtain ⟨v,rv⟩ := bDiff _ ha _ hc
  obtain ⟨w,rw'⟩ := cDiff _ hd _ he
  have ruv : L (u+v)=b+c := by rw [map_add,ru,rv,add_add_add_comm,ZModModule.add_self,zero_add]
  have hB {x y : G} (hx : x∈B) (hy : y∈B) (ne : x≠y) {z : V} (rz : L z=x+y) :=
    pair_direction inj size avoid inc (inB hx) (inB hy) (disjoint_left.mp outB hx)
      (disjoint_left.mp outB hy) ne rz
  have hw := pair_direction inj size avoid inc (inC hd) (inC he) (disjoint_left.mp outC hd)
    (disjoint_left.mp outC he) de rw'
  have mem {x y : G} (hx : x∈A) (hy : y∈A) {z : V} (rz : L z=x+y) :
      L (point 10 (encode z))∈A+A := by
    change L (decode 10 (encode z))∈A+A
    rw [decode_encode,rz]; exact add_mem_add hx hy
  have huV := hB hb hc bc ruv
  have iuV := mem (inB hb) (inB hc) ruv
  rw [encode_add] at huV iuV
  have eq := plane_maximal inj avoid inc (hB ha hb ab ru) (hB ha hc ac rv) huV hw
    (mem (inB ha) (inB hb) ru) (mem (inB ha) (inB hc) rv) iuV (mem (inC hd) (inC he) rw')
  have both {x y:G} (hx:x∈B) (hy:y∈B) (xy:x≠y) {z:Cube 10} (rz:L z=x+y)
      (same:encode z=encode w) : C⊆B := by
    have zw:z=w := by simpa using congrArg (decode 10) same
    have equal := rz.symm.trans ((congrArg L zw).trans rw')
    have hit := pair_equal size avoid (inB hx) (inB hy) (inC hd) (inC he) xy de equal
    have sub : ({x,y}:Finset G)⊆B := by
      intro i hi;rcases mem_insert.mp hi with rfl|k;exact hx;simpa only [mem_singleton.mp k] using hy
    rw [eqC]
    exact insert_subset (sub hit.1) (singleton_subset_iff.mpr (sub hit.2))
  rw [←encode_add] at eq
  exact eq.elim (both ha hb ab ru) (fun h=>h.elim (both ha hc ac rv) (both hb hc bc ruv))

/-- Fifteen simplex labels in one ten-flat, three in a parallel flat and two
in another force an affine three-space in the double. The conclusion also
holds for any two disjoint exterior families with the same internal
difference conditions. -/
theorem three_and_two {A B C : Finset G} (L : V →ₗ[F] G) (inj : Function.Injective L)
    (t : G) (inc : core L t⊆A) (size : 5≤A.card) (inB : B⊆A) (inC : C⊆A)
    (three : B.card=3) (two : C.card=2) (sep : Disjoint B C)
    (outB : Disjoint B (core L t)) (outC : Disjoint C (core L t))
    (bDiff : ∀ x∈B,∀ y∈B,x+y∈L.range) (cDiff : ∀ x∈C,∀ y∈C,x+y∈L.range) :
    ∃ p, FlatAt A p := by
  by_contra avoid
  have sub := triangle_controls L inj t inc size avoid inB inC three two outB outC bDiff cDiff
  obtain ⟨x,hx⟩ := card_pos.mp (show 0<C.card by omega)
  exact disjoint_left.mp sep (sub hx) hx

end Green51SimplexFibres
#print axioms Green51SimplexFibres.pair_direction
#print axioms Green51SimplexFibres.pair_compatible

#print axioms Green51SimplexFibres.plane_maximal
#print axioms Green51SimplexFibres.three_and_two

#print axioms Green51SimplexFibres.pair_equal
#print axioms Green51SimplexFibres.triangle_controls
