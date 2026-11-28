import Green50BCH
import Mathlib.Tactic.ReduceModChar
/-! # Affine subspaces of the double of the three-coordinate binary BCH curve -/

open Finset
namespace Green51BCH
variable {K : Type*} [Field K] [CharP K 2]
private theorem surface (x y : K) : (x+y)*(x^5+y^5) =
    (x+y)^6+(x+y)^3*(x^3+y^3)+(x^3+y^3)^2 := by
  ring_nf
  reduce_mod_char!

/-- The third additive difference in characteristic two. -/
def cubeSum {V : Type*} [AddCommGroup V] (f : V → K) (p a b c : V) : K :=
  f p + f (p+a) + f (p+b) + f (p+c) + f (p+a+b) + f (p+a+c) + f (p+b+c) + f (p+a+b+c)

set_option maxHeartbeats 500000 in
/-- The third difference of the seventh power is the binary Moore determinant. -/
theorem seventh (p a b c : K) :
    cubeSum (·^7) p a b c = a*b*c*(a+b)*(a+c)*(b+c)*(a+b+c) := by
  unfold cubeSum
  ring_nf
  reduce_mod_char!

private theorem polar_product (a b c d p q r s : K) :
    a*p+(a+b)*(p+q)+(a+c)*(p+r)+(a+d)*(p+s)+(a+b+c)*(p+q+r)+
      (a+b+d)*(p+q+s)+(a+c+d)*(p+r+s)+(a+b+c+d)*(p+q+r+s)=0 := by
  ring_nf
  reduce_mod_char!

/-- Three field coordinates, viewed as a binary vector space. -/
abbrev Space (K : Type*) := K × K × K
/-- The odd-power coordinates of the triple-error-correcting BCH code. -/
def curve (x : K) : Space K := (x,x^3,x^5)
/-- The sums of two BCH columns, including zero. -/
def IsSecant (z : Space K) : Prop := ∃ x y : K, z = curve x + curve y
/-- The equation satisfied by a pair of BCH columns with sum (a,b,c). -/
theorem secant_equation (z : Space K) (h:IsSecant z) :
    z.1*z.2.2=z.1^6+z.1^3*z.2.1+z.2.1^2 := by
  obtain ⟨x,y,rfl⟩:=h
  exact surface x y
/-- On the double, the seventh power of the first coordinate is quadratic over the binary field. -/
theorem secant_seventh (z : Space K) (h:IsSecant z) :
    z.1^7=z.1^2*z.2.2+z.1^4*z.2.1+z.1*z.2.1^2 := by
  linear_combination (norm := (ring_nf; reduce_mod_char!)) -z.1 * secant_equation z h

omit [CharP K 2] in
private theorem cubeSum_add {V : Type*} [AddCommGroup V] (f g : V → K) (p a b c : V) :
    cubeSum (fun v => f v + g v) p a b c = cubeSum f p a b c + cubeSum g p a b c := by
  simp only [cubeSum]
  ac_rfl

private theorem linearProduct {V : Type*} [AddCommGroup V] (f g : V →+ K) (p a b c : V) :
    cubeSum (fun v => f v*g v) p a b c = 0 := by
  simpa only [cubeSum,map_add] using polar_product (f p) (f a) (f b) (f c) (g p) (g a) (g b) (g c)

private def sqHom : K →+ K where
  toFun := (·^2)
  map_zero' := zero_pow (by decide)
  map_add' := CharTwo.add_sq

private theorem cube_obstruction [DecidableEq K] (p a b c : Space K)
    (h : ∀ z ∈ ({p,p+a,p+b,p+c,p+a+b,p+a+c,p+b+c,p+a+b+c}:Finset (Space K)), IsSecant z) :
    a.1*b.1*c.1*(a.1+b.1)*(a.1+c.1)*(b.1+c.1)*(a.1+b.1+c.1)=0 := by
  classical
  let i : Space K →+ K := AddMonoidHom.fst ..
  let j : Space K →+ K := (AddMonoidHom.fst ..).comp (AddMonoidHom.snd ..)
  let k : Space K →+ K := (AddMonoidHom.snd ..).comp (AddMonoidHom.snd ..)
  let P := fun z : Space K => ((sqHom.comp i) z)*(k z)
  let Q := fun z : Space K => ((sqHom.comp (sqHom.comp i)) z)*(j z)
  let R := fun z : Space K => i z*(sqHom.comp j) z
  have ident (z : Space K) (hz : IsSecant z) : z.1^7 = P z + Q z + R z := by
    change z.1^7 = z.1^2*z.2.2+(z.1^2)^2*z.2.1+z.1*z.2.1^2
    simpa only [←pow_mul] using secant_seventh z hz
  have f : cubeSum (fun z : Space K => z.1^7) p a b c =
      cubeSum (fun z => P z+Q z+R z) p a b c := by
    simp only [cubeSum]
    rw [ident p (h _ (by simp)),
      ident (p+a) (h _ (by simp)),
      ident (p+b) (h _ (by simp)),
      ident (p+c) (h _ (by simp)),
      ident (p+a+b) (h _ (by simp)),
      ident (p+a+c) (h _ (by simp)),
      ident (p+b+c) (h _ (by simp)),
      ident (p+a+b+c) (h _ (by simp))]
  rw [cubeSum_add,cubeSum_add,linearProduct,linearProduct,linearProduct,add_zero,add_zero] at f
  rw [←seventh p.1]
  exact f
/-- Two points of the secant surface with the same first coordinate. -/
private theorem vertical_eq (p v : Space K) (vert : v.1=0)
    (h1 : IsSecant p) (h2 : IsSecant (p+v)) :
    p.1*v.2.2 = p.1^3*v.2.1+v.2.1^2 := by
  have h := secant_equation (p+v) h2
  simp only [Prod.fst_add,Prod.snd_add,vert,add_zero,CharTwo.add_sq,mul_add] at h
  linear_combination h - secant_equation p h1

private theorem mixed_rectangle (p u v : Space K) (horiz : u.1≠0) (vert : v.1=0)
    (non : v≠0) (h0 : IsSecant p) (h1 : IsSecant (p+u))
    (h2 : IsSecant (p+v)) (h3 : IsSecant (p+u+v)) :
    v.2.1 = p.1*(p.1+u.1)*u.1 ∧
    v.2.2 = (p.1^2+p.1*u.1+u.1^2)*v.2.1 := by
  let t := p.1
  let a := u.1
  let b := v.2.1
  let c := v.2.2
  have r : t*c=t^3*b+b^2 := vertical_eq p v vert h0 h2
  have s : (t+a)*c=(t+a)^3*b+b^2 := vertical_eq (p+u) v vert h1 h3
  have ec : a*(c-(t^2+t*a+a^2)*b)=0 := by
    linear_combination (norm := (ring_nf; reduce_mod_char!)) s-r
  have ck := sub_eq_zero.mp ((mul_eq_zero.mp ec).resolve_left horiz)
  have bn : b≠0 := by
    intro bz
    have cz : c=0 := by rw [ck,bz,mul_zero]
    exact non (Prod.ext vert (Prod.ext bz cz))
  have ab : b*(b-t*(t+a)*a)=0 := by
    rw [ck] at r
    linear_combination (norm := ring) -r
  exact ⟨sub_eq_zero.mp ((mul_eq_zero.mp ab).resolve_left bn),ck⟩

variable [Algebra (ZMod 2) K]
private theorem four_when_mixed (p : Space K) (W : Submodule (ZMod 2) (Space K))
    (inside : ∀ w : W, IsSecant (p+w.val)) (u v : W) (nh : u.val.1 ≠ 0)
    (vert : v.val.1=0) (nz : v ≠ 0) :
    ∀ w : W, w=0 ∨ w=v ∨ w=u ∨ w=v+u := by
  have rect (w d : W) (hz : d.val.1=0) (dn : d≠0) :=
    mixed_rectangle (p+w.val) u.val d.val nh hz (fun e => dn (Subtype.ext e))
      (inside w) (by simpa only [Submodule.coe_add,add_assoc] using inside (w+u))
      (by simpa only [Submodule.coe_add,add_assoc] using inside (w+d))
      (by simpa only [Submodule.coe_add,add_assoc] using inside (w+u+d))
  have origin := rect 0 v vert nz
  simp only [Submodule.coe_zero,add_zero] at origin
  have only (d : W) (hz : d.val.1=0) : d=0 ∨ d=v := by
    by_cases zero : d=0
    · exact Or.inl zero
    have h := rect 0 d hz zero
    simp only [Submodule.coe_zero,add_zero] at h
    have equal := h.1.trans origin.1.symm
    exact Or.inr (Subtype.ext (Prod.ext (hz.trans vert.symm)
      (Prod.ext equal (h.2.trans ((congrArg (_*·) equal).trans origin.2.symm)))))
  intro w
  have h := (rect w v vert nz).1
  simp only [Prod.fst_add] at h
  have vanish : u.val.1 * (w.val.1*(w.val.1+u.val.1)) = 0 := by
    linear_combination (norm := (ring_nf; reduce_mod_char!)) origin.1-h
  rcases mul_eq_zero.mp ((mul_eq_zero.mp vanish).resolve_left nh) with zero|same
  · exact (only w zero).imp_right Or.inl
  · rcases only (w+u) same with eq|eq
    · exact Or.inr (Or.inr (Or.inl (add_right_cancel (eq.trans (ZModModule.add_self u).symm))))
    · exact Or.inr (Or.inr (Or.inr (by
        calc w = (w+u)+u := by rw [add_assoc,ZModModule.add_self,add_zero]
             _ = v+u := congrArg (·+u) eq)))

private theorem in_kernel [Finite K] (p : Space K) (W : Submodule (ZMod 2) (Space K))
    (inside : ∀ x : W,IsSecant (p+x.val)) (dim : 3 ≤ Module.finrank (ZMod 2) W) :
    ∃ v : W, v≠0 ∧ v.val.1=0 := by
  classical
  let B := Green50Downsets.Cube 3
  have rank : Module.finrank (ZMod 2) B ≤ Module.finrank (ZMod 2) W := by
    simpa only [B,Green50Downsets.Cube,Module.finrank_fin_fun] using dim
  obtain ⟨j,inj⟩ := finrank_le_iff_exists_linearMap.mp rank
  let f : B →+ K := (AddMonoidHom.fst ..).comp (W.subtype.comp j).toAddMonoidHom
  by_contra! none
  have nz (x : B) (hx : x≠0) : f x≠0 := none (j x) (fun e => hx (inj (e.trans j.map_zero.symm)))
  let e : Fin 3 → B := fun i => Pi.single i 1
  let u := j (e 0)
  let v := j (e 1)
  let w := j (e 2)
  have blocked := cube_obstruction p u.val v.val w.val (by
    intro z hz
    simp only [mem_insert,mem_singleton] at hz
    rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · simpa only [Submodule.coe_zero,add_zero,Submodule.coe_add,add_assoc] using inside (0)
    · simpa only [Submodule.coe_zero,add_zero,Submodule.coe_add,add_assoc] using inside (u)
    · simpa only [Submodule.coe_zero,add_zero,Submodule.coe_add,add_assoc] using inside (v)
    · simpa only [Submodule.coe_zero,add_zero,Submodule.coe_add,add_assoc] using inside (w)
    · simpa only [Submodule.coe_zero,add_zero,Submodule.coe_add,add_assoc] using inside (u+v)
    · simpa only [Submodule.coe_zero,add_zero,Submodule.coe_add,add_assoc] using inside (u+w)
    · simpa only [Submodule.coe_zero,add_zero,Submodule.coe_add,add_assoc] using inside (v+w)
    · simpa only [Submodule.coe_zero,add_zero,Submodule.coe_add,add_assoc] using inside (u+v+w))
  change f (e 0)*f (e 1)*f (e 2)*(f (e 0)+f (e 1))*(f (e 0)+f (e 2))*
    (f (e 1)+f (e 2))*(f (e 0)+f (e 1)+f (e 2))=0 at blocked
  simp only [←map_add,mul_eq_zero] at blocked
  rcases blocked with (((((h|h)|h)|h)|h)|h)|h <;> exact nz _ (by decide +kernel) h

/-- Every affine flat of dimension at least three in the double of the
three-coordinate BCH curve has constant first coordinate. -/
theorem horizontal_constant [Finite K] (p : Space K) (W : Submodule (ZMod 2) (Space K))
    (inside : ∀ x:W, IsSecant (p+x.val)) (dim : 3 ≤ Module.finrank (ZMod 2) W) :
    ∀ x:W,x.val.1=0 := by
  classical
  let _ := Fintype.ofFinite W
  intro u
  by_contra non
  obtain ⟨v,nz,vert⟩ := in_kernel p W inside dim
  have rest := four_when_mixed p W inside u v non vert nz
  have sub : (univ : Finset W) ⊆ {0,v,u,v+u} := by
    intro x _
    simpa only [mem_insert,mem_singleton] using rest x
  have n := (card_le_card sub).trans card_le_four
  rw [card_univ,Module.card_eq_pow_finrank (K:=ZMod 2),ZMod.card] at n
  have big := Nat.pow_le_pow_right (by decide : 0 < 2) dim
  omega

end Green51BCH
#print axioms Green51BCH.seventh
#print axioms Green51BCH.secant_equation
#print axioms Green51BCH.secant_seventh
#print axioms Green51BCH.horizontal_constant
