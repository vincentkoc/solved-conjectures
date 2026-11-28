import Green51AffineProfileTable

/-! # Stable profiles at bounded distance from the full four-point carrier -/

namespace Green51FrameIsomorphisms
open Finset Green53ParityThreshold Green51MissingMasks Green51Hyperplane

/-- Unlabelled pair multiplicities can always be listed in increasing order. -/
private theorem ordered (x y z : ℕ) : ∃ u v w : ℕ, u≤v ∧ v≤w ∧ u+v+w=x+y+z ∧
    ({u,v,w} : Multiset ℕ)={x,y,z} := by
  rcases le_total x y with h|h
  · rcases le_total y z with h'|h'
    · exact ⟨x,y,z,h,h',rfl,rfl⟩
    · rcases le_total x z with h''|h''
      · exact ⟨x,z,y,h'',h',by omega,by simp only [Multiset.insert_eq_cons,←Multiset.singleton_add]; ac_rfl⟩
      · exact ⟨z,x,y,h'',h,by omega,by simp only [Multiset.insert_eq_cons,←Multiset.singleton_add]; ac_rfl⟩
  · rcases le_total x z with h'|h'
    · exact ⟨y,x,z,h,h',by omega,by simp only [Multiset.insert_eq_cons,←Multiset.singleton_add]; ac_rfl⟩
    · rcases le_total y z with h''|h''
      · exact ⟨y,z,x,h'',h',by omega,by simp only [Multiset.insert_eq_cons,←Multiset.singleton_add]; ac_rfl⟩
      · exact ⟨z,y,x,h'',h,by omega,by simp only [Multiset.insert_eq_cons,←Multiset.singleton_add]; ac_rfl⟩

/-- Parameters encode multiplicities of parts of weights 3, 2, 4, and 6.
The unspent defect counts parts of weight one. -/
abbrev Parts := ℕ × ℕ × ℕ × ℕ

def weight (t : Parts) : ℕ := 3*t.1+2*t.2.1+4*t.2.2.1+6*t.2.2.2

def fromParts (g h : ℕ) (t : Parts) : Profile :=
  let a := t.1
  let x := t.2.2.2
  let y := x+t.2.2.1
  let z := y+t.2.1
  let c := h-weight t
  six a c (g-(a+c+x+y+z)) x y z

private theorem ordered_injective {x y z u v w : ℕ} (h : x≤y) (h' : y≤z)
    (j : u≤v) (j' : v≤w) (eq : ({x,y,z} : Multiset ℕ)={u,v,w}) : x=u ∧ y=v ∧ z=w := by
  have xu : x∈({u,v,w} : Multiset ℕ) := eq ▸ (by simp : x∈({x,y,z} : Multiset ℕ))
  have ux : u∈({x,y,z} : Multiset ℕ) := eq ▸ (by simp : u∈({u,v,w} : Multiset ℕ))
  simp only [Multiset.insert_eq_cons,Multiset.mem_cons,Multiset.mem_singleton] at xu ux
  obtain rfl : x=u := by omega
  have rest : ({y,z} : Multiset ℕ)={v,w} := (Multiset.cons_inj_right _).mp eq
  have yv : y∈({v,w} : Multiset ℕ) := rest ▸ (by simp : y∈({y,z} : Multiset ℕ))
  have vy : v∈({y,z} : Multiset ℕ) := rest ▸ (by simp : v∈({v,w} : Multiset ℕ))
  simp only [Multiset.insert_eq_cons,Multiset.mem_cons,Multiset.mem_singleton] at yv vy
  obtain rfl : y=v := by omega
  exact ⟨rfl,rfl,Multiset.singleton_inj.mp ((Multiset.cons_inj_right _).mp rest)⟩

theorem fromParts_injective (g h : ℕ) : Function.Injective (fromParts g h) := by
  rintro ⟨a,b,c,d⟩ ⟨i,j,k,l⟩ eq
  have one := congrArg (fun p : Profile => p.1 0) eq
  have dirs := congrArg Prod.snd eq
  change a=i at one
  change ({d,d+c,d+c+b} : Multiset ℕ)={l,l+k,l+k+j} at dirs
  obtain ⟨p,q,r⟩ := ordered_injective (by omega) (by omega) (by omega) (by omega) dirs
  congr <;> omega

/-- For defect at most the number of rows, the affine profiles correspond to partitions
of the defect into parts of sizes one, two, three, four, and six. -/
theorem stable_parts {g h : ℕ} (enough : h≤g) {p : Profile} :
    Valid g (4*g-h) p ↔ ∃ t : Parts, weight t≤h ∧ fromParts g h t=p := by
  rw [valid_six]
  constructor
  · rintro ⟨a,c,d,x,y,z,n,m,rfl⟩
    obtain ⟨x',y',z',xy,yz,total,eq⟩ := ordered x y z
    let t : Parts := ⟨a,z'-y',y'-x',x'⟩
    have weight_eq : weight t+c=h := by dsimp [t,weight];omega
    refine ⟨t,by omega,?_⟩
    dsimp [fromParts,t]
    rw [show h-weight (a,z'-y',y'-x',x')=c by change h-weight t=c;omega,
      show x'+(y'-x')=y' by omega, show y'+(z'-y')=z' by omega,
      show g-(a+c+x'+y'+z')=d by omega]
    exact Prod.ext rfl eq
  · rintro ⟨⟨a,b,c,d⟩,w,rfl⟩
    change 3*a+2*b+4*c+6*d≤h at w
    let j := h-(3*a+2*b+4*c+6*d)
    let k := g-(a+j+d+(d+c)+(d+c+b))
    exact ⟨a,j,k,d,d+c,d+c+b,by dsimp [j,k];omega,by dsimp [j,k];omega,rfl⟩

end Green51FrameIsomorphisms
#print axioms Green51FrameIsomorphisms.stable_parts
#print axioms Green51FrameIsomorphisms.fromParts_injective
