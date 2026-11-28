import Green51SixProfileNumbers

/-! # Enumerating affine classes from six integer frequencies -/

namespace Green51FrameIsomorphisms
open Finset Green53ParityThreshold Green51MissingMasks Green51Hyperplane

private def splits (a c d b : ℕ) : Finset Profile :=
  (range (b+1)).biUnion fun x =>
    (range (b-x+1)).image fun y => six a c d x y (b-x-y)

private theorem mem_splits {a c d b : ℕ} {p : Profile} : p∈splits a c d b ↔
    ∃ x y z, x+y+z=b ∧ six a c d x y z=p := by
  simp only [splits,mem_biUnion,mem_range,mem_image]
  constructor
  · rintro ⟨x,hx,y,hy,rfl⟩
    exact ⟨x,y,b-x-y,by omega,rfl⟩
  · rintro ⟨x,y,z,h,rfl⟩
    exact ⟨x,by omega,y,by omega,by rw [show b-x-y=z by omega]⟩

private def sectionOf (g k a b : ℕ) : Finset Profile :=
  let c := 4*g-k-(3*a+2*b)
  let d := g-(a+b+c)
  if a+c+d+b=g ∧ a+3*c+4*d+2*b=k then splits a c d b else ∅

private theorem mem_section {g k a b : ℕ} {p : Profile} : p∈sectionOf g k a b ↔
    ∃ c d x y z, x+y+z=b ∧ a+c+d+b=g ∧ a+3*c+4*d+2*b=k ∧ six a c d x y z=p := by
  unfold sectionOf
  dsimp only
  split_ifs with fits
  · rw [mem_splits]
    constructor
    · rintro ⟨x,y,z,h,eq⟩
      exact ⟨_,_,x,y,z,h,fits.1,fits.2,eq⟩
    · rintro ⟨c,d,x,y,z,bh,n,w,eq⟩
      exact ⟨x,y,z,bh,by rwa [show 4*g-k-(3*a+2*b)=c by omega,show g-(a+b+c)=d by omega]⟩
  · simp only [notMem_empty,false_iff]
    rintro ⟨c,d,x,y,z,_,n,w,_⟩
    exact fits (by rw [show 4*g-k-(3*a+2*b)=c by omega,show g-(a+b+c)=d by omega];exact ⟨n,w⟩)

/-- Enumerate the number of singleton rows and the total number of pairs. The two remaining
ordinary sizes follow from the number of rows and the total weight. -/
def profileTable (g k : ℕ) : Finset Profile :=
  (range (g+1)).biUnion fun a => (range (g-a+1)).biUnion fun b => sectionOf g k a b

theorem mem_profileTable {g k : ℕ} {p : Profile} : p ∈ profileTable g k ↔ Valid g k p := by
  rw [valid_six]
  simp only [profileTable,mem_biUnion,mem_range,mem_section]
  constructor
  · rintro ⟨a,_,b,_,c,d,x,y,z,rfl,n,w,eq⟩
    exact ⟨a,c,d,x,y,z,n,w,eq⟩
  · rintro ⟨a,c,d,x,y,z,n,w,eq⟩
    exact ⟨a,by omega,x+y+z,by omega,c,d,x,y,z,rfl,n,w,eq⟩

/-- A finite profile enumeration computes the actual number of affine equivalence classes. -/
theorem table_eq_classes {s k : ℕ} (hs : 5 ≤ s)
    (near : min (5*(2*s+3)+12) (4*(2*s+3)+20)*2^2 < 8*k) :
    Nat.card (Quotient (affineSetoid (countedDoubles (2*(s+1)+2) k (threshold (2*s))))) =
      (profileTable (2*s+3) k).card := by
  rw [count_profiles hs near]
  let e : {p : Profile // Valid (2*s+3) k p} ≃ ↥(profileTable (2*s+3) k) :=
    Equiv.subtypeEquivRight (fun _ => mem_profileTable.symm)
  simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using Nat.card_congr e

end Green51FrameIsomorphisms
#print axioms Green51FrameIsomorphisms.mem_profileTable
#print axioms Green51FrameIsomorphisms.table_eq_classes
