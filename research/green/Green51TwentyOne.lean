import Green51ExteriorFibres
import Green51ParallelPairs
import Green51TwentyOneSection

/-! # The exact twenty-one-point forcing bound in twelve binary dimensions -/

open Finset Green50Downsets Green50Sharp Green51SimplexSection Green51SimplexDirections
open Green51FourSpace Green51SystematicChecks Green51SimplexFibres Green51TenDimensions
open Green51ExteriorSums Green51ExteriorFibres Green51ParallelPairs Green51SimplexGeometry
open scoped Classical Pointwise
namespace Green51TwentyOne
local notation "F" => ZMod 2
local notation "V" => Cube 12

private theorem fourth {Q:Type*} [AddCommGroup Q] [Module F Q] [Fintype Q] [DecidableEq Q]
    {q r s o:Q} (qr:q≠r) (qs:q≠s) (rs:r≠s) (tags:univ.erase o={q,r,s}) : q+r+s=o := by
  by_contra ne
  have hit : q+r+s∈({q,r,s}:Finset Q) := tags ▸ mem_erase.mpr ⟨ne,mem_univ _⟩
  have cancel {a b:Q} (h:a+b=0) : a=b := add_right_cancel (h.trans (ZModModule.add_self b).symm)
  simp only [mem_insert,mem_singleton] at hit
  rcases hit with h|h|h
  · exact rs (cancel (add_left_cancel (show q+(r+s)=q+0 by rwa [←add_assoc,add_zero])))
  · exact qs (cancel (add_right_cancel (show (q+s)+r=0+r by rwa [add_right_comm,zero_add])))
  · exact qr (cancel (add_right_cancel (show (q+r)+s=0+s by rwa [zero_add])))

private structure ExteriorPair (L:Cube 10→ₗ[F] V) (E:Finset V) (q:V ⧸ L.range) where
  a : V
  b : V
  ha : a∈E
  hb : b∈E
  ne : a≠b
  qa : L.range.mkQ a=q
  qb : L.range.mkQ b=q
  u : ℕ
  hu : u∈directions
  rep : L (point 10 u)=a+b

private theorem get_pair {A:Finset V} (L:Cube 10→ₗ[F] V) (inj:Function.Injective L)
    (t:V) (inc:core L t⊆A) (size:A.card=21) (avoid:¬∃p,FlatAt A p)
    (q:V ⧸ L.range) (non:q≠L.range.mkQ t) : Nonempty (ExteriorPair L (A\core L t) q) := by
  obtain ⟨a,b,ne,eq⟩ := card_eq_two.mp (fibre_counts L inj t inc size avoid q non)
  have ha := mem_filter.mp (eq ▸ (show a∈({a,b}:Finset V) by simp))
  have hb := mem_filter.mp (eq ▸ (show b∈({a,b}:Finset V) by simp))
  have inside : a+b∈L.range := by
    apply (Submodule.Quotient.mk_eq_zero L.range).mp
    change L.range.mkQ (a+b)=0
    rw [map_add,ha.2,hb.2,ZModModule.add_self]
  obtain ⟨c,rep⟩ := inside
  have u := pair_direction inj (by omega) avoid inc (mem_sdiff.mp ha.1).1 (mem_sdiff.mp hb.1).1
    (mem_sdiff.mp ha.1).2 (mem_sdiff.mp hb.1).2 ne rep
  exact ⟨⟨a,b,ha.1,hb.1,ne,ha.2,hb.2,encode c,u,(congrArg L (decode_encode c)).trans rep⟩⟩

private theorem sum_of_three {G:Type*} [AddCommGroup G] [Module F G]
    {a b c x y z:G} (h:(a+x)+(b+y)=c+z) : a+b+c=x+y+z := by
  calc
    a+b+c = (a+b+c)+((x+x)+(y+y)+(z+z)) := by simp only [ZModModule.add_self,add_zero]
    _ = ((a+x)+(b+y)+(c+z))+(x+y+z) := by abel
    _ = x+y+z := by rw [h,ZModModule.add_self,zero_add]

theorem twenty_one (A:Finset V) (size:A.card=21) : ∃p,FlatAt A p := by
  classical
  by_contra avoid
  obtain ⟨L,t,inj,inc⟩ := Green51TwentyOneSection.has_core A size avoid
  let Q := V ⧸ L.range
  let _ : Fintype Q := Fintype.ofFinite _
  let f := L.range.mkQ
  let E := A\core L t
  have big : 5≤A.card := by omega
  have inA : E⊆A := sdiff_subset
  have sep : Disjoint E (core L t) := disjoint_left.mpr fun _ hx=>(mem_sdiff.mp hx).2
  have four := quotient_card L inj
  have three : (univ.erase (f t)).card=3 := by rw [card_erase_of_mem (mem_univ _),card_univ,four]
  obtain ⟨q,r,s,qr,qs,rs,tags⟩ := card_eq_three.mp three
  have extag {j:Q} (h:j∈({q,r,s}:Finset Q)) : j≠f t := (mem_erase.mp (tags ▸ h)).1
  obtain ⟨X⟩ := get_pair L inj t inc size avoid q (extag (by simp))
  obtain ⟨Y⟩ := get_pair L inj t inc size avoid r (extag (by simp))
  obtain ⟨Z⟩ := get_pair L inj t inc size avoid s (extag (by simp))
  have rt : X.a+Y.a+Z.a+t∈L.range := by
    apply (Submodule.Quotient.mk_eq_zero L.range).mp
    change f (X.a+Y.a+Z.a+t)=0
    simp only [map_add,f,X.qa,Y.qa,Z.qa]
    rw [fourth qr qs rs tags,ZModModule.add_self]
  obtain ⟨T,hT⟩ := rt
  have comp {j k:Q} (P:ExteriorPair L E j) (R:ExteriorPair L E k) (jk:j≠k) :
      P.u ^^^ R.u∈directions := by
    have ne:P.u≠R.u := by
      intro eq
      have m := (pair_equal big avoid (inA P.ha) (inA P.hb) (inA R.ha) (inA R.hb) P.ne R.ne
        (P.rep.symm.trans ((congrArg (fun i=>L (point 10 i)) eq).trans R.rep))).1
      simp only [mem_insert,mem_singleton] at m
      exact jk (m.elim (fun h=>P.qa.symm.trans ((congrArg f h.symm).trans R.qa))
        (fun h=>P.qb.symm.trans ((congrArg f h.symm).trans R.qa)))
    exact pair_compatible inj avoid inc P.hu R.hu ne (P.rep ▸ add_mem_add (inA P.ha) (inA P.hb))
      (R.rep ▸ add_mem_add (inA R.ha) (inA R.hb))
  have sw {j:Q} (P:ExteriorPair L E j) : P.a+L (point 10 P.u)∈E := by
    rw [P.rep,←add_assoc,ZModModule.add_self,zero_add];exact P.hb
  by_cases plane:X.u ^^^ Y.u=Z.u
  · let B : Finset V := {X.a,Y.a,Z.a}
    let C : Finset V := {X.b,Y.b,Z.b}
    have sub {x y z:V} (hx:x∈E) (hy:y∈E) (hz:z∈E) : ({x,y,z}:Finset V)⊆A := by
      intro i hi;simp only [mem_insert,mem_singleton] at hi
      rcases hi with rfl|rfl|rfl <;> apply inA <;> assumption
    have dis : Disjoint B C := by
      refine disjoint_left.mpr ?_
      intro i hi hj
      simp only [B,C,mem_insert,mem_singleton] at hi hj
      have tagsA := And.intro X.qa (And.intro Y.qa Z.qa)
      have tagsB := And.intro X.qb (And.intro Y.qb Z.qb)
      rcases hi with h|h|h <;> rcases hj with k|k|k <;>
        first | exact X.ne (h.symm.trans k) | exact Y.ne (h.symm.trans k) | exact Z.ne (h.symm.trans k) |
                solve | have tmp := congrArg f (h.symm.trans k); dsimp [f] at tmp; grind only
    have bad := disjoint_odd big avoid (sub X.ha Y.ha Z.ha) (sub X.hb Y.hb Z.hb) dis
      (show X.a∈B by simp [B]) (show Y.a∈B by simp [B]) (show Z.a∈B by simp [B])
      (show X.b∈C by simp [C]) (show Y.b∈C by simp [C]) (show Z.b∈C by simp [C])
    apply bad
    apply sum_of_three
    rw [←X.rep,←Y.rep,←Z.rep,←map_add,←point_xor,plane]
  · exact avoid (rank_three L t inc big inA sep X.hu Y.hu Z.hu (comp X Y qr) (comp X Z qs)
      (comp Y Z rs) plane X.a Y.a Z.a T hT X.ha (sw X) Y.ha (sw Y) Z.ha (sw Z))

end Green51TwentyOne
#print axioms Green51TwentyOne.twenty_one
