import Green51MooreRank
import Green51BCHInverse

/-! # Removing two bits of the fourth BCH coordinate -/

open Green50Downsets Green51BCH
open scoped Pointwise
namespace Green51BCHCompression
local notation "F" => ZMod 2
variable {K : Type*} [Field K] [CharP K 2] [Algebra F K]
variable {H : Type*} [AddCommGroup H] [Module F H]

private theorem move {V : Type*} [AddCommGroup V] [Module F V] {a b : V} (ha : a≠0) (hb : b≠0) :
    ∃ f : V ≃ₗ[F] V, f a=b := by
  let A := LinearEquiv.toSpanNonzeroSingleton F V a ha
  let B := LinearEquiv.toSpanNonzeroSingleton F V b hb
  obtain ⟨f,hf⟩ := Submodule.exists_linearEquiv_restrict_eq (A.symm.trans B)
  have eq := hf (A 1)
  change (B (A.symm (A 1)):V)=f (A 1) at eq
  rw [A.symm_apply_apply] at eq
  refine ⟨f,?_⟩
  simpa [A,B] using eq.symm

/-- Three full BCH coordinates and a linear projection of the seventh power. -/
def lifted (L : K →ₗ[F] H) (x : K) : Space K × H := (curve x,L (x^7))

private theorem unique_tail (L : K →ₗ[F] H) {x y u v : K} (eq : curve x+curve y=curve u+curve v) :
    L (x^7)+L (y^7)=L (u^7)+L (v^7) := by
  let t := x+y
  have eqt : u+v=t := (congrArg (fun z : Space K => z.1) eq).symm
  have yp : y=x+t := by simp [t,←add_assoc,CharTwo.add_self_eq_zero]
  have vp : v=u+t := by rw [←eqt,←add_assoc,CharTwo.add_self_eq_zero,zero_add]
  by_cases hz : t=0
  · rw [yp,vp,hz,add_zero,add_zero,ZModModule.add_self,ZModModule.add_self]
  · have mem : curve x+curve (x+t)∈curve '' ({u,v}:Set K)+curve '' ({u,v}:Set K) := by
      rw [←yp,eq]
      exact Set.add_mem_add (Set.mem_image_of_mem _ (by simp)) (Set.mem_image_of_mem _ (by simp))
    rcases (both_labels _ _ _ hz).mp mem with ⟨yes,_⟩
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at yes
    rcases yes with h|h
    · rw [yp,h,←vp]
    · have yt : y=u := by rw [yp,h,vp,add_assoc,CharTwo.add_self_eq_zero,add_zero]
      rw [h,yt,add_comm]

private theorem same_lift (L : K →ₗ[F] H) {p q : Space K × H}
    (hp : p∈Set.range (lifted L)+Set.range (lifted L))
    (hq : q∈Set.range (lifted L)+Set.range (lifted L)) (first:p.1=q.1) : p=q := by
  obtain ⟨_,⟨x,rfl⟩,_,⟨y,rfl⟩,rfl⟩ := hp
  obtain ⟨_,⟨u,rfl⟩,_,⟨v,rfl⟩,rfl⟩ := hq
  exact Prod.ext first (unique_tail L first)

omit [CharP K 2] in
private theorem pin_direction [Finite K] (U : Submodule F K) (t : K) (ht : t∈U) (nz:t≠0)
    (rank : 4≤Module.finrank F U) :
    ∃ J : Cube 4 →ₗ[F] K, Function.Injective J ∧ J (Pi.single 0 1)=t ∧ ∀ s,J s∈U := by
  have room : Module.finrank F (Cube 4)≤Module.finrank F U := by simpa [Cube] using rank
  obtain ⟨i,hi⟩ := finrank_le_iff_exists_linearMap.mp room
  let s : Cube 4 := Pi.single 0 1
  have ns : s≠0 := by decide +kernel
  have ni : i s≠0 := fun h => ns (hi (h.trans i.map_zero.symm))
  obtain ⟨g,hg⟩ := move ni (show (⟨t,ht⟩:U)≠0 from fun eq => nz (congrArg Subtype.val eq))
  refine ⟨U.subtype.comp (g.toLinearMap.comp i),U.subtype_injective.comp (g.injective.comp hi),?_,fun v => (g (i v)).property⟩
  exact congrArg Subtype.val hg

private theorem horizontal [Finite K] (L : K →ₗ[F] H)
    (p : Space K × H) (W : Submodule F (Space K × H))
    (inside : p +ᵥ (W:Set (Space K × H)) ⊆ Set.range (lifted L)+Set.range (lifted L))
    (dim : 3≤Module.finrank F W) :
    (∀ w:W,w.val.1.1=0) ∧
      Module.finrank F (W.map (LinearMap.fst F (Space K) H))=Module.finrank F W := by
  let P := LinearMap.fst F (Space K) H
  have hit (w : W) : p+w.val∈Set.range (lifted L)+Set.range (lifted L) := inside ⟨w.val,w.property,rfl⟩
  have inj : Function.Injective (P.comp W.subtype) := by
    intro w v eq
    have same : p+w.val=p+v.val := same_lift L (hit w) (hit v) (by
      change p.1+w.val.1=p.1+v.val.1
      exact congrArg (p.1+·) eq)
    exact Subtype.ext (add_left_cancel same)
  have rank : Module.finrank F (W.map P) = Module.finrank F W := by
    rw [←show (P.comp W.subtype).range=W.map P by rw [LinearMap.range_comp,Submodule.range_subtype]]
    exact (P.comp W.subtype).finrank_range_of_inj inj
  refine ⟨?_,rank⟩
  have fixed := horizontal_constant p.1 (W.map P) (fun v => by
    obtain ⟨w,hw,eq⟩ := v.property
    obtain ⟨_,⟨x,rfl⟩,_,⟨y,rfl⟩,sum⟩ := hit ⟨w,hw⟩
    refine ⟨x,y,?_⟩
    rw [←eq]
    exact (congrArg Prod.fst sum).symm) (rank ▸ dim)
  intro w
  exact fixed ⟨P w.val,⟨w.val,w.property,rfl⟩⟩

/-- The change in the seventh power along an input difference. -/
def seventhDerivative (t x : K) : K := x^7+(x+t)^7
omit [Algebra F K] in
/-- A mixed second difference of the derivative is the Moore determinant. -/
theorem seventhDerivative_rect (t x b c : K) :
    seventhDerivative t x+seventhDerivative t (x+b)+seventhDerivative t (x+c)+seventhDerivative t (x+b+c)=moore t b c := by
  unfold moore seventhDerivative
  ring_nf
  reduce_mod_char!

private theorem projected_rect (L : K →ₗ[F] H) (t x : K) (p : Space K × H)
    (base : lifted L x+lifted L (x+t)=p) (W : Submodule F (Space K × H))
    (inside : p +ᵥ (W:Set (Space K × H)) ⊆ Set.range (lifted L)+Set.range (lifted L))
    (U : Submodule F K) (above : ∀ u∈U, ∃ w∈W,w.1=polar t u) :
    ∀ b∈U,∀ c∈U, L (moore t b c)=0 := by
  have origin : L (seventhDerivative t x)=p.2 := by
    simpa [seventhDerivative,lifted] using congrArg Prod.snd base
  have first : curve t+polar t x=p.1 := (derivative x t).symm.trans (congrArg Prod.fst base)
  have eval (u : K) (w : Space K × H) (hw : w∈W) (eq : w.1=polar t u) :
      L (seventhDerivative t (x+u))=p.2+w.2 := by
    have left : lifted L (x+u)+lifted L (x+u+t)∈Set.range (lifted L)+Set.range (lifted L) :=
      Set.add_mem_add ⟨_,rfl⟩ ⟨_,rfl⟩
    have right := inside (show p+w∈p +ᵥ (W:Set (Space K × H)) from ⟨w,hw,rfl⟩)
    have yes := same_lift L left right (by
      change curve (x+u)+curve (x+u+t)=p.1+w.1
      rw [derivative,map_add,←add_assoc,first,eq])
    simpa [seventhDerivative,lifted] using congrArg Prod.snd yes
  intro b hb c hc
  obtain ⟨u,hu,h⟩ := above b hb
  obtain ⟨v,hv,g⟩ := above c hc
  rw [←seventhDerivative_rect t x, map_add, map_add, map_add,origin,eval b u hu h,eval c v hv g,add_assoc x b c,
    eval (b+c) (u+v) (W.add_mem hu hv) (by rw [Prod.fst_add,h,g,map_add]),Prod.snd_add]
  calc _ = (p.2+p.2)+(p.2+p.2)+(u.2+u.2)+(v.2+v.2) := by abel
       _ = 0 := by simp [ZModModule.add_self]

/-- A three-flat in the projected double comes from one nonzero difference
and an input subspace of one higher dimension on which all projected pair minors vanish. -/
theorem input_of_flat [Finite K] (L : K →ₗ[F] H) (p : Space K × H)
    (W : Submodule F (Space K × H))
    (inside : p +ᵥ (W:Set (Space K × H)) ⊆ Set.range (lifted L)+Set.range (lifted L))
    (dim : 3≤Module.finrank F W) :
    ∃ (t : K) (U : Submodule F K), t≠0 ∧ t∈U ∧
      Module.finrank F U=Module.finrank F W+1 ∧ ∀ b∈U,∀ c∈U,L (moore t b c)=0 := by
  let P := LinearMap.fst F (Space K) H
  obtain ⟨fixed,count⟩ := horizontal L p W inside dim
  let V := W.map P
  have hit (w : W) : p+w.val∈Set.range (lifted L)+Set.range (lifted L) := inside ⟨w.val,w.property,rfl⟩
  have hp := hit 0
  rw [Submodule.coe_zero,add_zero] at hp
  obtain ⟨_,⟨x,rfl⟩,_,⟨y,rfl⟩,base'⟩ := hp
  let t := p.1.1
  have xt : x+y=t := congrArg (fun z : Space K × H => z.1.1) base'
  have partner {a b : K} (h:a+b=t) : b=a+t := by rw [←h,←add_assoc,CharTwo.add_self_eq_zero,zero_add]
  have base : lifted L x+lifted L (x+t)=p := by rwa [←partner xt]
  have fst : curve t+polar t x=p.1 := (derivative x t).symm.trans (congrArg Prod.fst base)
  have range : V ≤ (polar t).range := by
    rintro _ ⟨w,hw,rfl⟩
    obtain ⟨_,⟨a,rfl⟩,_,⟨b,rfl⟩,eq⟩ := hit ⟨w,hw⟩
    have sum := congrArg (fun z : Space K × H => z.1.1) eq
    change a+b=p.1.1+w.1.1 at sum
    rw [fixed ⟨w,hw⟩,add_zero] at sum
    rw [partner sum] at eq
    have e := congrArg Prod.fst eq
    change curve a+curve (a+t)=p.1+w.1 at e
    rw [derivative,←fst,add_assoc] at e
    have pe := add_left_cancel e
    refine ⟨a+x,?_⟩
    change polar t (a+x)=w.1
    rw [map_add,pe,add_right_comm,ZModModule.add_self,zero_add]
  have nt : t≠0 := by
    intro z
    have atZero : polar (0:K)=0 := by ext u <;> simp [polar]
    rw [z,atZero,LinearMap.range_zero,le_bot_iff] at range
    have eq : Module.finrank F V=Module.finrank F W := count
    rw [range,finrank_bot] at eq
    omega
  let U := V.comap (polar t)
  have ker : (polar t).ker≤U := by
    intro u hu
    change polar t u∈V
    exact (show polar t u=0 from hu) ▸ V.zero_mem
  have ht : t∈U := ker (by rw [polar_ker nt];exact Submodule.subset_span (by simp))
  have rank := Green51QuadraticFlats.map_rank (polar t) U ker
  have im : U.map (polar t)=V := Submodule.map_comap_eq_self range
  have eq : Module.finrank F V=Module.finrank F W := count
  rw [im,eq,polar_ker nt,finrank_span_singleton nt] at rank
  have kill := projected_rect L t x p base W inside U (fun u hu => by
    obtain ⟨w,hw,h⟩ := hu
    exact ⟨w,hw,h⟩)
  exact ⟨t,U,nt,ht,by omega,kill⟩

theorem input_four_of_flat [Finite K] (L : K →ₗ[F] H) (p : Space K × H)
    (W : Submodule F (Space K × H))
    (inside : p +ᵥ (W:Set (Space K × H)) ⊆ Set.range (lifted L)+Set.range (lifted L))
    (dim : 3≤Module.finrank F W) :
    ∃ (t : K) (U : Submodule F K), t≠0 ∧ t∈U ∧ Module.finrank F U=4 ∧
      ∀ b∈U,∀ c∈U,L (moore t b c)=0 := by
  obtain ⟨t,U,nt,ht,rank,kill⟩ := input_of_flat L p W inside dim
  obtain ⟨J,inj,at0,contained⟩ := pin_direction U t ht nt (by omega)
  refine ⟨t,J.range,nt,⟨_,at0⟩,by simpa [Cube] using J.finrank_range_of_inj inj,?_⟩
  rintro _ ⟨b,rfl⟩ _ ⟨c,rfl⟩
  exact kill _ (contained b) _ (contained c)

/-- Omitting a two-dimensional subspace of the seventh-power coordinate
still excludes binary affine three-spaces from the double. -/
theorem excludes_three [Finite K] (L : K →ₗ[F] H) (small : Module.finrank F L.ker≤2)
    (p : Space K × H) (W : Submodule F (Space K × H))
    (inside : p +ᵥ (W:Set (Space K × H)) ⊆ Set.range (lifted L)+Set.range (lifted L)) :
    Module.finrank F W ≤ 2 := by
  by_contra! dim
  obtain ⟨t,U,nt,ht,rank,kill⟩ := input_of_flat L p W inside dim
  obtain ⟨J,inj,at0,contained⟩ := pin_direction U t ht nt (by omega)
  have big := moore_rank L J inj (fun b c => by rw [at0];exact kill _ (contained b) _ (contained c))
  omega


end Green51BCHCompression
#print axioms Green51BCHCompression.input_of_flat
#print axioms Green51BCHCompression.input_four_of_flat
#print axioms Green51BCHCompression.excludes_three
#print axioms Green51BCHCompression.seventhDerivative_rect
