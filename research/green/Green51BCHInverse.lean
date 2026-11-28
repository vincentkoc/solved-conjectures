import Green51BCHDirections
import Green51QuadraticSubset

/-! # Pulling flats of a BCH double back to the input set -/

open scoped Pointwise
namespace Green51BCH
variable {K : Type*} [Field K] [CharP K 2] [Algebra (ZMod 2) K]

/-- The linear part of the change in the BCH column along a fixed input difference. -/
def polar (t : K) : K →ₗ[ZMod 2] Space K where
  toFun x := (0,t*x^2+t^2*x,t*x^4+t^4*x)
  map_add' x y := by
    ext <;> simp only [Prod.fst_add,Prod.snd_add,add_zero]
    · ring_nf
      reduce_mod_char!
    · ring_nf
      reduce_mod_char!
  map_smul' r x := by
    rcases (show ∀ z : ZMod 2, z=0 ∨ z=1 from by decide) r with rfl|rfl <;> simp

theorem derivative (x t : K) : curve x+curve (x+t)=curve t+polar t x := by
  ext <;> simp only [curve,polar,LinearMap.coe_mk,AddHom.coe_mk,Prod.fst_add,Prod.snd_add]
  all_goals ring_nf
  all_goals reduce_mod_char!

private theorem polar_zero {t : K} (nz:t≠0) (x : K) : polar t x=0 ↔ x=0 ∨ x=t := by
  constructor
  · intro h
    have z := congrArg (fun v : Space K => v.2.1) h
    change t*x^2+t^2*x=0 at z
    have rn : t*(x*(x+t))=0 := by linear_combination z
    exact (mul_eq_zero.mp ((mul_eq_zero.mp rn).resolve_left nz)).imp_right CharTwo.add_eq_zero.mp
  · rintro (rfl|rfl)
    · exact map_zero _
    · ext <;> simp [polar] <;> ring_nf <;> reduce_mod_char!

theorem polar_ker {t : K} (nz : t≠0) : (polar t).ker=Submodule.span (ZMod 2) {t} := by
  ext x
  rw [LinearMap.mem_ker,polar_zero nz,Submodule.mem_span_singleton]
  constructor
  · rintro (rfl|rfl)
    · exact ⟨0,zero_smul _ _⟩
    · exact ⟨1,one_smul _ _⟩
  · rintro ⟨s,hs⟩
    rcases (show ∀ z : ZMod 2, z=0 ∨ z=1 from by decide) s with rfl|rfl <;> aesop

/-- The first two coordinates recover the unordered pair of input labels. -/
theorem both_labels (S : Set K) (x t : K) (nz : t≠0) :
    curve x+curve (x+t)∈curve '' S+curve '' S ↔ x∈S ∧ x+t∈S := by
  constructor
  · rintro ⟨_,⟨a,ha,rfl⟩,_,⟨b,hb,rfl⟩,eq⟩
    have same := congrArg Prod.fst eq
    change a+b=x+(x+t) at same
    have partner : b=a+t := by
      have e : a+b=t := same.trans (by rw [←add_assoc,CharTwo.add_self_eq_zero,zero_add])
      calc b = a+(a+b) := by rw [←add_assoc,CharTwo.add_self_eq_zero,zero_add]
           _ = a+t := congrArg (a+·) e
    change curve a + curve b = curve x + curve (x+t) at eq
    rw [partner,derivative,derivative] at eq
    have diff : polar t (a+x)=0 := by rw [map_add,add_left_cancel eq,ZModModule.add_self]
    rcases (polar_zero nz _).mp diff with one|two
    · have ax := CharTwo.add_eq_zero.mp one
      exact ⟨ax ▸ ha,(ax ▸ partner) ▸ hb⟩
    · have ax : x+t=a := by rw [←two,add_left_comm,CharTwo.add_self_eq_zero,add_zero]
      have bx : b=x := by rw [partner,←two,←add_assoc,CharTwo.add_self_eq_zero,zero_add]
      exact ⟨bx ▸ hb,ax.symm ▸ ha⟩
  · rintro ⟨h,h'⟩
    exact Set.add_mem_add (Set.mem_image_of_mem _ h) (Set.mem_image_of_mem _ h')

private theorem representative {S : Set K} {t : K} {y : Space K}
    (first : y.1=t) (mem : y∈curve '' S+curve '' S) :
    ∃ x∈S, x+t∈S ∧ curve t+polar t x=y := by
  obtain ⟨_,⟨x,hx,rfl⟩,_,⟨z,hz,rfl⟩,rfl⟩ := mem
  change x+z=t at first
  have e : z=x+t := by rw [←first,←add_assoc,CharTwo.add_self_eq_zero,zero_add]
  exact ⟨x,hx,e ▸ hz,by rw [←derivative,←e]⟩

/-- A dimension-d flat in the double of any subset of the three-coordinate
BCH curve corresponds to a dimension-(d+1) flat in its input. -/
theorem subset_inverse [Finite K] {d : ℕ} (large : 3≤d) (S : Set K) :
    (∃ (p : Space K) (W : Submodule (ZMod 2) (Space K)),Module.finrank (ZMod 2) W=d ∧
      p +ᵥ (W:Set (Space K)) ⊆ curve '' S+curve '' S) ↔
    ∃ (x : K) (U : Submodule (ZMod 2) K),Module.finrank (ZMod 2) U=d+1 ∧
      x +ᵥ (U:Set K) ⊆ S := by
  constructor
  · rintro ⟨p,W,dim,within⟩
    have hit (w : W) : p+w.val ∈ curve '' S+curve '' S := within ⟨w.val,w.property,rfl⟩
    have fixed := horizontal_constant p W (fun w => by
      obtain ⟨_,⟨a,_,rfl⟩,_,⟨b,_,rfl⟩,eq⟩ := hit w
      exact ⟨a,b,eq.symm⟩) (dim ▸ large)
    let t := p.1
    have repr (w : W) := representative (show (p+w.val).1=t by rw [Prod.fst_add,fixed,add_zero]) (hit w)
    obtain ⟨x,_,_,base⟩ := repr 0
    rw [Submodule.coe_zero,add_zero] at base
    have range : W≤(polar t).range := by
      intro w hw
      obtain ⟨y,_,_,hy⟩ := repr ⟨w,hw⟩
      change curve t+polar t y = p+w at hy
      rw [←base,add_assoc] at hy
      have eq := add_left_cancel hy
      exact ⟨y+x,by rw [map_add,eq,add_right_comm,ZModModule.add_self,zero_add]⟩
    have non : t≠0 := by
      intro z
      have atZero : polar (0:K)=0 := by ext a <;> simp [polar]
      rw [z,atZero,LinearMap.range_zero,le_bot_iff] at range
      rw [range,finrank_bot] at dim
      omega
    let U := W.comap (polar t)
    have eq : U.map (polar t)=W := Submodule.map_comap_eq_self range
    have sub : (polar t).ker≤U := by
      intro y hy
      change polar t y∈W
      exact (show polar t y=0 from hy) ▸ W.zero_mem
    have rank := Green51QuadraticFlats.map_rank (polar t) U sub
    rw [eq,dim,polar_ker non,finrank_span_singleton non] at rank
    refine ⟨x,U,rank.symm,?_⟩
    rintro y ⟨u,hu,rfl⟩
    apply ((both_labels S (x+u) t non).mp ?_).1
    rw [derivative,map_add,←add_assoc,base]
    exact hit ⟨polar t u,hu⟩
  · rintro ⟨x,U,dim,within⟩
    obtain ⟨t,mem,non⟩ : ∃t∈U,t≠0 := by
      by_contra! h
      have z : U=⊥ := eq_bot_iff.mpr fun a ha => (Submodule.mem_bot _).mpr (h a ha)
      rw [z,finrank_bot] at dim
      omega
    have sub : (polar t).ker≤U := by
      rw [polar_ker non]
      exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr mem)
    have rank := Green51QuadraticFlats.map_rank (polar t) U sub
    rw [polar_ker non,finrank_span_singleton non,dim] at rank
    refine ⟨curve x+curve (x+t),U.map (polar t),by omega,?_⟩
    rintro z ⟨_,⟨u,hu,rfl⟩,rfl⟩
    have hx : x+u∈S := within ⟨u,hu,rfl⟩
    have ht : x+u+t∈S := within ⟨u+t,U.add_mem hu mem,(add_assoc _ _ _).symm⟩
    have yes := (both_labels S (x+u) t non).mpr ⟨hx,ht⟩
    rw [derivative,map_add,←add_assoc,←derivative] at yes
    exact yes

end Green51BCH

#print axioms Green51BCH.derivative
#print axioms Green51BCH.polar_ker
#print axioms Green51BCH.both_labels
#print axioms Green51BCH.subset_inverse
