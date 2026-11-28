import Green52CubicRegularity
import Green52CubicFibres
import Green52CubicParameters
import Green52Complements

/-! # The polar form of an additively cubic map in characteristic two -/
namespace Green52CubicPolar
open Green52CubicRegularity
local notation "𝔽" => ZMod 2
variable {U V : Type*} [AddCommGroup U] [Module 𝔽 U] [AddCommGroup V] [Module 𝔽 V]

/-- A polynomial map of additive degree at most three. -/
def Cubic (f : U → V) : Prop :=
  ∀ a b c d x, fwdDiff d (fwdDiff c (fwdDiff b (fwdDiff a f))) x = 0

private def triple (f : U → 𝔽) (a b c : U) := fwdDiff c (fwdDiff b (fwdDiff a f)) 0

omit [Module 𝔽 U] in
private theorem exchange {E : Type*} [AddCommGroup E] (f : U → E) (a b : U) :
    fwdDiff b (fwdDiff a f) = fwdDiff a (fwdDiff b f) := by
  funext x
  simp only [fwdDiff]
  rw [add_right_comm x b a]
  abel

omit [Module 𝔽 U] in
private theorem first_swap (f : U → 𝔽) (a b c : U) : triple f a b c = triple f b a c := by
  unfold triple
  rw [exchange f a b]

omit [Module 𝔽 U] in
private theorem last_swap (f : U → 𝔽) (a b c : U) : triple f a b c = triple f a c b :=
  congrFun (exchange (fwdDiff a f) b c) 0

omit [Module 𝔽 U] in
private theorem constant (f : U → 𝔽) (h : Cubic f) (a b c x : U) :
    fwdDiff c (fwdDiff b (fwdDiff a f)) x = triple f a b c := by
  simpa only [fwdDiff,zero_add,triple] using sub_eq_zero.mp (h a b c x 0)

omit [Module 𝔽 U] in
private theorem last_add (f : U → 𝔽) (h : Cubic f) (a b c d : U) :
    triple f a b (c+d) = triple f a b c + triple f a b d := by
  rw [←constant f h a b d c]
  unfold triple
  simp only [fwdDiff,zero_add]
  abel

/-- Bundle an additive map between binary spaces without extra scalar hypotheses. -/
def linearize {X Y : Type*} [AddCommGroup X] [Module 𝔽 X] [AddCommGroup Y] [Module 𝔽 Y]
    (g : X → Y) (hg : ∀ x y, g (x+y)=g x+g y) : X →ₗ[𝔽] Y := (AddMonoidHom.mk' g hg).toZModLinearMap 2

/-- The third difference is a symmetric trilinear form. -/
def polar (f : U → 𝔽) (h : Cubic f) : Trilinear U :=
  linearize (fun a => linearize (fun b => linearize (triple f a b) (last_add f h a b)) (by
    intro b c
    ext x
    change triple f a (b+c) x = triple f a b x + triple f a c x
    rw [last_swap f a (b+c) x,last_add f h,last_swap f a x b,last_swap f a x c])) (by
    intro a b
    ext x y
    change triple f (a+b) x y = triple f a x y + triple f b x y
    rw [first_swap f (a+b) x y,last_swap f x (a+b) y,last_add f h]
    rw [last_swap f x y a,last_swap f x y b,first_swap f x a y,first_swap f x b y])

theorem symmetric_first (f : U → 𝔽) (h : Cubic f) (x y : U) :
    polar f h x y = polar f h y x := LinearMap.ext (first_swap f x y)
theorem symmetric_last (f : U → 𝔽) (h : Cubic f) (x y z : U) :
    polar f h x y z = polar f h x z y := last_swap f x y z

omit [Module 𝔽 U] in
theorem scalar_cubic (f : U → V) (h : Cubic f) (l : Module.Dual 𝔽 V) : Cubic (fun x => l (f x)) := by
  intro a b c d x
  simpa only [fwdDiff,map_sub,map_zero] using congrArg l (h a b c d x)

/-- Above input a, the Boolean derivative is quadratic with the contraction of
the cubic polar form as its bilinear form. -/
theorem derivative_quadratic (F : U → 𝔽) (h : Cubic F) (a b x : U) :
    (F x+F (x+a))+(F (b+x)+F ((b+x)+a)) =
      polar F h a b x + ((F 0+F (0+a))+(F b+F (b+a))) := by
  have hpol : polar F h a b x = triple F a b x := rfl
  rw [hpol]
  simp only [triple,fwdDiff,zero_add,add_comm x b]
  have all (u v w y j k l m : 𝔽) : (u+v)+(w+y) =
    (y-w-(v-u)-(m-l-(k-j)))+((j+k)+(l+m)) := by decide +revert
  exact all _ _ _ _ _ _ _ _

/-- A quadratic binary function with zero polar form is affine. -/
theorem affine_of_zero (g : U → 𝔽)
    (hg : ∀ a x, g x + g (a+x)=g 0+g a) :
    ∃ l : Module.Dual 𝔽 U, ∀ x, g x=l x+g 0 := by
  let L := linearize (fun a => g a - g 0) (by
    intro a b
    have h := hg a b
    exact (show ∀ u v w z : 𝔽, v+w=z+u → w-z=(u-z)+(v-z) from by decide) _ _ _ _ h)
  exact ⟨L,fun x => (sub_add_cancel (g x) (g 0)).symm⟩
end Green52CubicPolar
#print axioms Green52CubicPolar.polar
#print axioms Green52CubicPolar.derivative_quadratic
#print axioms Green52CubicPolar.scalar_cubic

open Finset
open scoped Pointwise Classical
namespace Green52CubicGraphs
open Green52CubicRegularity Green52CubicSelection Green52CubicMinors Green52CubicFibres Green52CubicBias Green52CubicPolar
local notation "𝔽" => ZMod 2
variable {U V : Type*} [AddCommGroup U] [Module 𝔽 U] [Fintype U]
  [AddCommGroup V] [Module 𝔽 V] [Fintype V]
abbrev DualV (V : Type*) [AddCommGroup V] [Module 𝔽 V] := Module.Dual 𝔽 V

private theorem regular_directions (f : U → V) (T : DualV V → Trilinear U)
    (quad : ∀ (l : DualV V) a b x, l (f x+f (x+a)) + l (f (b+x)+f (b+x+a)) =
      T l a b x + (l (f 0+f (0+a))+l (f b+f (b+a))))
    (N : ℕ) (hN : Fintype.card V = N)
    (reg : ∀ l, (∀ a b c : U, T l a b c=0) ∨
      2^(2*N)*Nat.card {a : U // Module.finrank 𝔽 (T l a).range ≤ 2*(N+1)} < Nat.card U) :
    ∃ (P : Submodule 𝔽 U) (a : U),
      Module.finrank 𝔽 U ≤ Module.finrank 𝔽 P + (N+N*(2*(N+1))^2) ∧
      ∀ h : P, ∃ x, f x+f (x+(a+h.val))=0 := by
  classical
  let _ : Fintype (DualV V) := Fintype.ofInjective (fun l : DualV V => (l : V → 𝔽)) DFunLike.coe_injective
  have cn : Fintype.card (DualV V)=N := calc
    _ = Fintype.card 𝔽 ^ Module.finrank 𝔽 (DualV V) := Module.card_eq_pow_finrank
    _ = Fintype.card V := by rw [Subspace.dual_finrank_eq]; exact Module.card_eq_pow_finrank.symm
    _ = N := hN
  let R := 2*(N+1)
  let low (l : DualV V) := ∀ a b c, T l a b c=0
  let bad (l : DualV V) : Finset U := if low l then ∅ else univ.filter (fun a => Module.finrank 𝔽 (T l a).range ≤ R)
  obtain ⟨H,hd,projections⟩ := horizontal_projections f
  have small (l : DualV V) : 2^(2*N)*(bad l).card ≤ Fintype.card U := by
    by_cases hl : low l
    · simp [bad,hl]
    · have s := ((reg l).resolve_left hl).le
      simpa only [bad,if_neg hl,R,Nat.card_eq_fintype_card,Fintype.card_subtype] using s
  obtain ⟨a,ha,avoids⟩ := avoid_sparse N cn.le H (by omega) bad small
  have parameters (l : DualV V) : ∃ J : Submodule 𝔽 U,
      Module.finrank 𝔽 U ≤ Module.finrank 𝔽 J+R^2 ∧
      ∀ h : J, low l ∨ R ≤ Module.finrank 𝔽 (T l (a+h.val)).range := by
    by_cases hl : low l
    · exact ⟨⊤,by simp,fun _ => Or.inl hl⟩
    · have h := avoids l
      simp only [bad,if_neg hl,mem_filter,mem_univ,true_and] at h
      obtain ⟨J,dim,fixrank⟩ := freeze_minor (T l) a R (by omega)
      exact ⟨J,dim,fun h => Or.inr (fixrank h)⟩
  choose J loss rank using parameters
  obtain ⟨L,sub,dim⟩ := common_subspace J (fun _ => R^2) loss
  let P := H ⊓ L
  refine ⟨P,a,?_,?_⟩
  · have eq := Submodule.finrank_sup_add_finrank_inf_eq H L
    have le := Submodule.finrank_le (H ⊔ L)
    change Module.finrank 𝔽 U ≤ Module.finrank 𝔽 ↥(H ⊓ L : Submodule 𝔽 U) + (N+N*R^2)
    have dL : Module.finrank 𝔽 U ≤ Module.finrank 𝔽 L + N*R^2 := by simpa [cn] using dim
    rw [hN] at hd
    omega
  · intro h
    let v := a+h.val
    have inH : v ∈ H := H.add_mem ha h.property.1
    apply exists_zero
    intro l
    let g (x : U) := l (f x+f (x+v))
    have qg (b x) : g x+g (b+x)=T l v b x+(g 0+g b) := quad l v b x
    rcases rank l ⟨h.val,sub l h.property.2⟩ with hl|hr
    · obtain ⟨m,hm⟩ := affine_of_zero g (fun b x => by simpa [hl v b x] using qg b x)
      exact Or.inl (affine_nonneg g m (g 0) hm (projections ⟨v,inH⟩ l))
    · right
      have est := quadratic_sum_rank g (T l v) qg (N+1) hr
      have hgt : (Fintype.card V:ℤ) < 2^(N+1) := by
        rw [hN]; exact_mod_cast (show N < 2^(N+1) from (Nat.lt_succ_self N).trans (Nat.lt_two_pow_self))
      change (Fintype.card V:ℤ)*|∑ x,parity (g x)| < Fintype.card U
      by_cases z : |∑ x,parity (g x)|=0
      · rw [z,mul_zero]; positivity
      · exact (mul_lt_mul_of_pos_right hgt (lt_of_le_of_ne (abs_nonneg _) (Ne.symm z))).trans_le est
/-- A uniform horizontal codimension bound in terms of the output cardinality. -/
def horizontalCost (N : ℕ) := N*cost (2*N) (2*(N+1)) + (N+N*(2*(N+1))^2)

/-- For every cubic map over F₂, the inputs where a derivative can vanish
contain an affine subspace of bounded codimension, independent of the input dimension. -/
theorem cubic_horizontal (f : U → V) (hc : Cubic f) :
    ∃ (P : Submodule 𝔽 U) (a : U), Module.finrank 𝔽 U ≤ Module.finrank 𝔽 P + horizontalCost (Fintype.card V) ∧
      ∀ h : P, ∃ x, f x+f (x+(a+h.val))=0 := by
  classical
  let _ : Fintype (DualV V) := Fintype.ofInjective (fun l : DualV V => (l : V → 𝔽)) DFunLike.coe_injective
  let N := Fintype.card V
  let T (l : DualV V) := polar (fun x => l (f x)) (scalar_cubic f hc l)
  have cn : Fintype.card (DualV V)=N := calc
    _ = Fintype.card 𝔽 ^ Module.finrank 𝔽 (DualV V) := Module.card_eq_pow_finrank
    _ = _ := by rw [Subspace.dual_finrank_eq]; exact Module.card_eq_pow_finrank.symm
  obtain ⟨H,dim,reg⟩ := simultaneous T (fun l => symmetric_first _ _) (fun l => symmetric_last _ _)
    (2*N) (2*(N+1))
  let fH (x : H) := f x.val
  let TH (l : DualV V) := restrictTri (T l) H
  have quad (l : DualV V) (a b x : H) :
      l (fH x+fH (x+a)) + l (fH (b+x)+fH (b+x+a)) =
      TH l a b x + (l (fH 0+fH (0+a))+l (fH b+fH (b+a))) := by
    simp only [map_add]
    exact derivative_quadratic (fun x => l (f x)) (scalar_cubic f hc l) a.val b.val x.val
  obtain ⟨J,a,costJ,dir⟩ := regular_directions fH TH quad N rfl reg
  let P := J.map H.subtype
  have de : Module.finrank 𝔽 J = Module.finrank 𝔽 P :=
    (Submodule.equivMapOfInjective H.subtype H.subtype_injective J).finrank_eq
  refine ⟨P,a.val,?_,?_⟩
  · rw [cn] at dim
    change _ ≤ Module.finrank 𝔽 P + horizontalCost N
    unfold horizontalCost
    omega
  · rintro ⟨_,j,hj,rfl⟩
    obtain ⟨x,hx⟩ := dir ⟨j,hj⟩
    exact ⟨x.val,hx⟩

private theorem binary_double {Y : Type*} [AddCommGroup Y] [Module 𝔽 Y] (y : Y) : y+y=0 := by
  rw [←two_smul 𝔽,show (2:𝔽)=0 by decide,zero_smul]

open Green52Complements in
private theorem flat_of_horizontal {n : ℕ} (A : Set (Cube n))
    (U V : Submodule 𝔽 (Cube n)) (comp : IsCompl U V) (f : U → V)
    {c : ℕ} (horizontal : ∃ (P : Submodule 𝔽 U) (a : U), Module.finrank 𝔽 U ≤ Module.finrank 𝔽 P + c ∧
      ∀ h : P, ∃ x, f x+f (x+(a+h.val))=0) (inside : (Green50Graphs.graph U V f : Set (Cube n)) ⊆ A) :
    Flat n (c+Module.finrank 𝔽 V) A := by
  classical
  obtain ⟨P,a,dim,dir⟩ := horizontal
  let S := P.map U.subtype
  have de : Module.finrank 𝔽 P = Module.finrank 𝔽 S :=
    (Submodule.equivMapOfInjective U.subtype U.subtype_injective P).finrank_eq
  refine ⟨AffineSubspace.mk' (a:Cube n) S,?_,?_⟩
  · intro z hz
    obtain ⟨h,hh,he⟩ := (AffineSubspace.mem_mk'.mp hz : z-(a:Cube n)∈S)
    have sum : z=(a:Cube n)+(h:Cube n) := by
      change (h:Cube n)=z-(a:Cube n) at he
      rw [he]; abel
    obtain ⟨x,hx⟩ := dir ⟨h,hh⟩
    let y := x+(a+h)
    have gx (u : U) : (u:Cube n)+(f u:Cube n) ∈ A :=
      inside (Finset.mem_image_of_mem _ (Finset.mem_univ u))
    refine ⟨_,gx x,_,gx y,?_⟩
    have v0 : (f x:Cube n)+(f y:Cube n)=0 := congrArg V.subtype hx
    have xx : (x:Cube n)+(x:Cube n)=0 := by rw [←two_smul 𝔽,show (2:𝔽)=0 by decide,zero_smul]
    change ((x:Cube n)+(f x:Cube n))+((y:Cube n)+(f y:Cube n))=z
    rw [add_add_add_comm,v0,add_zero,sum]
    change (x:Cube n)+((x:Cube n)+((a:Cube n)+(h:Cube n)))=_
    rw [←add_assoc,xx,zero_add]
  · have total : Module.finrank 𝔽 U + Module.finrank 𝔽 V = n := by
      simpa [Cube,Module.finrank_prod] using (U.prodEquivOfIsCompl V comp).finrank_eq
    rw [AffineSubspace.direction_mk']
    change n ≤ Module.finrank 𝔽 S + (c+Module.finrank 𝔽 V)
    rw [←de]
    omega

open Green52Complements

/-- Green 52 holds on every set containing a cubic transversal. -/
theorem cubic_transversal_green52 {n : ℕ} (A : Set (Cube n))
    (U V : Submodule 𝔽 (Cube n)) (comp : IsCompl U V) (f : U → V)
    (hc : Cubic f) (inside : (Green50Graphs.graph U V f : Set (Cube n)) ⊆ A) :
    Flat n (horizontalCost (Nat.card V)+Module.finrank 𝔽 V) A := by
  classical
  rw [Nat.card_eq_fintype_card]
  exact flat_of_horizontal A U V comp f (cubic_horizontal f hc) inside

/-- An arbitrary function of boundedly many cubic coordinates has the same
horizontal directions of agreement as the underlying cubic map guarantees. -/
theorem cubic_factor_green52 {n : ℕ} (A : Set (Cube n))
    (U V : Submodule 𝔽 (Cube n)) (comp : IsCompl U V)
    {E : Type*} [AddCommGroup E] [Module 𝔽 E] [Fintype E] (p : U → E)
    (hp : Cubic p) (g : E → V)
    (inside : (Green50Graphs.graph U V (g ∘ p) : Set (Cube n)) ⊆ A) :
    Flat n (horizontalCost (Fintype.card E)+Module.finrank 𝔽 V) A := by
  classical
  apply flat_of_horizontal A U V comp (g ∘ p) _ inside
  obtain ⟨P,a,dim,dir⟩ := cubic_horizontal p hp
  refine ⟨P,a,dim,fun h => ?_⟩
  obtain ⟨x,hx⟩ := dir h
  have agree : p x = p (x+(a+h.val)) := by
    calc
      _ = p x+(p (x+(a+h.val))+p (x+(a+h.val))) := by rw [binary_double,add_zero]
      _ = _ := by rw [←add_assoc,hx,zero_add]
  exact ⟨x,by simpa only [Function.comp_apply,agree] using binary_double (g (p (x+(a+h.val))))⟩

end Green52CubicGraphs

#print axioms Green52CubicGraphs.cubic_horizontal
#print axioms Green52CubicGraphs.cubic_transversal_green52
#print axioms Green52CubicGraphs.cubic_factor_green52

namespace Green52CubicGraphs
open Green52Complements Green52CubicPolar
local notation "𝔽" => ZMod 2
private theorem cost_mono : Monotone horizontalCost := by
  intro a b h
  unfold horizontalCost Green52CubicRegularity.cost
  dsimp only
  gcongr <;> decide

/-- A single function of the complement budget bounds the codimension for all
sets containing a cubic transversal with at most that many vertical shifts. -/
theorem cubic_complement_bound {n k : ℕ} (A : Set (Cube n))
    (U V : Submodule 𝔽 (Cube n)) (comp : IsCompl U V) (f : U → V)
    (h : Cubic f) (inside : (Green50Graphs.graph U V f : Set (Cube n)) ⊆ A)
    (budget : Nat.card V ≤ k) : Flat n (horizontalCost k+k) A := by
  classical
  obtain ⟨W,hw,dim⟩ := cubic_transversal_green52 A U V comp f h inside
  have card : 2^(Module.finrank 𝔽 V)=Nat.card V := by
    rw [Nat.card_eq_fintype_card,Module.card_eq_pow_finrank (K:=𝔽) (V:=V),ZMod.card]
  have rd : Module.finrank 𝔽 V ≤ Nat.card V := card ▸ (Nat.lt_two_pow_self.le : Module.finrank 𝔽 V ≤ 2^(Module.finrank 𝔽 V))
  exact ⟨W,hw,dim.trans (Nat.add_le_add_left (Nat.add_le_add (cost_mono budget) (rd.trans budget)) _)⟩
end Green52CubicGraphs
#print axioms Green52CubicGraphs.cubic_complement_bound
