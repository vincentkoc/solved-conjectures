import Green51ThreePairs
import Green51ExteriorSums
import Green51SimplexFibres

/-! # Three pairs over the three exterior classes of a simplex section -/

open Finset Green50Downsets Green50Sharp Green51SimplexSection Green51SimplexDirections
open Green51FourSpace Green51SystematicChecks Green51SimplexFibres Green51TenDimensions
open Green51SimplexGeometry Green51ExteriorSums Green51ThreePairs
open scoped Classical Pointwise
namespace Green51ParallelPairs
local notation "F" => ZMod 2
local notation "V" => Cube 10
variable {G:Type*} [AddCommGroup G] [Module F G] [DecidableEq G]

private theorem split {u v w d:ℕ} (hd:d∈choices u v w) :
    ∃i∈[0,u],∃j∈[0,v],∃k∈[0,w], (i ^^^ j) ^^^ k=d := by
  simp only [choices,List.mem_cons,List.not_mem_nil,or_false] at hd
  rcases hd with h|h|h|h|h|h|h|h <;> rw [h]
  · exact ⟨0,by simp,0,by simp,0,by simp,by simp⟩
  · exact ⟨u,by simp,0,by simp,0,by simp,by simp⟩
  · exact ⟨0,by simp,v,by simp,0,by simp,by simp⟩
  · exact ⟨0,by simp,0,by simp,w,by simp,by simp⟩
  · exact ⟨u,by simp,v,by simp,0,by simp,by simp⟩
  · exact ⟨u,by simp,0,by simp,w,by simp,by simp⟩
  · exact ⟨0,by simp,v,by simp,w,by simp,by simp⟩
  · exact ⟨u,by simp,v,by simp,w,by simp,rfl⟩

private theorem in_model {a:ℕ} (h:a∈units++extras) : point 10 a∈model := by
  rcases List.mem_append.mp h with h|h
  · exact mem_union_left _ ((mem_rows units).mpr ⟨_,h,rfl⟩)
  · exact mem_union_right _ ((mem_rows extras).mpr ⟨_,h,rfl⟩)

theorem rank_three {A B:Finset G} (L:V→ₗ[F] G) (t:G) (inc:core L t⊆A)
    (size:5≤A.card) (inB:B⊆A) (sep:Disjoint B (core L t)) {u v w:ℕ}
    (hu:u∈directions) (hv:v∈directions) (hw:w∈directions)
    (uv:u ^^^ v∈directions) (uw:u ^^^ w∈directions) (vw:v ^^^ w∈directions)
    (non:u ^^^ v≠w) (x y z:G) (r:V) (hr:L r=x+y+z+t)
    (hx:x∈B) (hx':x+L (point 10 u)∈B) (hy:y∈B) (hy':y+L (point 10 v)∈B)
    (hz:z∈B) (hz':z+L (point 10 w)∈B) : ∃p,FlatAt A p := by
  by_contra avoid
  obtain ⟨d,hd,a,ha,b,hb,c,hc,eq⟩ := all_orders hu hv hw uv uw vw non (encode_lt r)
  obtain ⟨i,hi,j,hj,k,hk,mix⟩ := split hd
  have sw {p:G} {q n:ℕ} (base:p∈B) (next:p+L (point 10 q)∈B) (hn:n∈[0,q]) :
      p+L (point 10 n)∈B := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
    rcases hn with rfl|rfl
    · simpa only [show point 10 0=0 from decode_zero 10,map_zero,add_zero] using base
    · exact next
  have addCore {a:ℕ} (h:a∈units++extras) : L (point 10 a)+t∈core L t :=
    mem_image_of_mem _ (in_model h)
  have bad := disjoint_odd size avoid inB inc sep (sw hx hx' hi) (sw hy hy' hj) (sw hz hz' hk)
    (addCore ha) (addCore hb) (addCore hc)
  have rel := congrArg (fun v => L (point 10 v)) eq
  change L (point 10 (((a ^^^ b) ^^^ c) ^^^ d))=L (point 10 (encode r)) at rel
  rw [show point 10 (encode r)=r from decode_encode r,hr] at rel
  simp only [point_xor,map_add] at rel
  let old := L (point 10 a)+L (point 10 b)+L (point 10 c)
  let extra := L (point 10 d)
  have rd : old+extra=x+y+z+t := rel
  have orig : old=x+y+z+t+extra := by rw [←rd,add_assoc,ZModModule.add_self,add_zero]
  have md : L (point 10 i)+L (point 10 j)+L (point 10 k)=extra := by
    dsimp [extra];rw [←mix,point_xor,point_xor,map_add,map_add]
  apply bad
  calc
    _ = (x+y+z)+(L (point 10 i)+L (point 10 j)+L (point 10 k)) := by abel
    _ = old+t := by
      rw [md,orig]
      calc
        _ = ((x+y+z)+extra)+(t+t) := by rw [ZModModule.add_self,add_zero]
        _ = _ := by abel
    _ = _ := by
      change (L (point 10 a)+L (point 10 b)+L (point 10 c))+t=_
      calc
        _ = (L (point 10 a)+L (point 10 b)+L (point 10 c))+(t+t+t) := by rw [ZModModule.add_self,zero_add]
        _ = _ := by abel

end Green51ParallelPairs
#print axioms Green51ParallelPairs.rank_three
