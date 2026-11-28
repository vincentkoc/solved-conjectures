import Green33ReciprocalCharts
import Mathlib.GroupTheory.Index
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! Splitting of binary quadratic forms on reciprocal parameter lines. -/

open Finset Green33ReciprocalCharts
open scoped BigOperators

namespace Green33SplitPencils

variable {F : Type*} [Field F] [CharP F 2]

/-- The homogeneous binary form aX²+bXY+cY² factors over the base field. -/
def Splits (a b c : F) : Prop := ∃ r s t u : F, a=r*t ∧ b=r*u+s*t ∧ c=s*u

private def asMap : F →+ F where
  toFun x := x^2+x
  map_zero' := by simp
  map_add' x y := by ring_nf;reduce_mod_char!

/-- Artin–Schreier's criterion for a binary quadratic with nonzero middle coefficient. -/
theorem splits_iff {a b c : F} (hb : b≠0) :
    Splits a b c ↔ ∃ x : F, x^2+x=a*c/b^2 := by
  constructor
  · rintro ⟨r,s,t,u,ar,br,cr⟩
    refine ⟨r*u/b,?_⟩
    field_simp [hb]
    rw [ar,br,cr]
    ring_nf
    reduce_mod_char!
  · rintro ⟨x,root⟩
    by_cases ha : a=0
    · subst a;exact ⟨0,1,b,c,by simp,by simp,by simp⟩
    refine ⟨a,b*x,1,b*(1+x)/a,by simp,?_,?_⟩
    · field_simp [ha]
      ring_nf
      reduce_mod_char!
    · have h := (eq_div_iff (pow_ne_zero 2 hb)).mp root
      field_simp [ha]
      linear_combination -h

variable [Fintype F]

private theorem as_index : (asMap (F:=F)).range.index=2 := by
  rw [AddSubgroup.index_range,Nat.card_eq_two_iff' 0]
  let one : (asMap (F:=F)).ker := ⟨1,by change (1:F)^2+1=0;simp [CharTwo.add_self_eq_zero]⟩
  refine ⟨one,fun eq => one_ne_zero (congrArg Subtype.val eq),?_⟩
  intro y nz
  apply Subtype.ext
  have hy := y.property
  change (y:F)^2+(y:F)=0 at hy
  have factor : (y:F)*((y:F)+1)=0 := by linear_combination hy
  rcases mul_eq_zero.mp factor with h | h
  · exact False.elim (nz (Subtype.ext h))
  · change (y:F)=1
    have e := congrArg (·+(1:F)) h
    simpa only [CharTwo.add_cancel_right,zero_add] using e

/-- The unique nontrivial sign on the two cosets of the Artin–Schreier image. -/
noncomputable def splitChar : AddChar F ℝ := by
  classical
  let U := (asMap (F:=F)).range
  exact {
    toFun := fun x => if x∈U then 1 else -1
    map_zero_eq_one' := by simp
    map_add_eq_mul' := by
      intro x y
      have h : x+y∈U ↔ (x∈U ↔ y∈U) := AddSubgroup.add_mem_iff_of_index_two as_index
      by_cases hx : x∈U <;> by_cases hy : y∈U <;> simp [h,hx,hy] }

private theorem splitChar_nontrivial : splitChar (F:=F)≠0 := by
  classical
  have h : (asMap (F:=F)).range≠⊤ := by
    intro top
    have p := as_index (F:=F)
    rw [top] at p
    simp at p
  obtain ⟨x,hx⟩ : ∃ x : F, x∉(asMap (F:=F)).range := by
    by_contra! all
    exact h (eq_top_iff.mpr (fun x _ => all x))
  intro zero
  have atx := DFunLike.congr_fun zero x
  change (if x∈(asMap (F:=F)).range then (1:ℝ) else -1)=1 at atx
  rw [if_neg hx] at atx
  norm_num at atx

private theorem char_square (x : F) : splitChar (x^2)=splitChar x := by
  classical
  have p : x^2+x∈(asMap (F:=F)).range := ⟨x,rfl⟩
  have e := (AddSubgroup.add_mem_iff_of_index_two as_index).mp p
  simp only [splitChar,AddChar.coe_mk]
  simp only [e]

/-- Sign of the splitting predicate, with value +1 for split forms. -/
noncomputable def sign (a b c : F) : ℝ := by
  classical exact if Splits a b c then 1 else -1

/-- The splitting indicator as an additive character, including the leading-coefficient-zero case. -/
theorem split_sign {a b c : F} (hb : b≠0) :
    sign a b c=splitChar (a*c/b^2) := by
  classical
  have e : Splits a b c ↔ a*c/b^2∈(asMap (F:=F)).range := splits_iff hb
  simp only [sign,splitChar,AddChar.coe_mk,e]

#print axioms splits_iff
#print axioms split_sign

omit [Fintype F] in
private theorem bin_sq (a b : F) : (a+b)^2=a^2+b^2 := by ring_nf;reduce_mod_char!

private theorem square_surj : Function.Surjective (fun x : F => x^2) := by
  apply Finite.surjective_of_injective
  intro x y h
  change x^2=y^2 at h
  have add : (x+y)^2=0 := by rw [bin_sq,h,CharTwo.add_self_eq_zero]
  have z : x+y=0 := (pow_eq_zero_iff (by decide : 2≠0)).mp add
  have e := congrArg (·+y) z
  simpa only [CharTwo.add_cancel_right,zero_add] using e

omit [Fintype F] [CharP F 2] in
private theorem sign_abs (a b c : F) : |sign a b c|=1 := by
  classical
  by_cases h : Splits a b c <;> simp [sign,h]

private theorem affine_sign (u v w z x ρ : F) (sq : ρ^2=v*z) :
    sign (u+v*x) 1 (w+z*x)=splitChar (u*w+(u*z+v*w+ρ)*x) := by
  rw [split_sign one_ne_zero,one_pow,div_one]
  have eq : (u+v*x)*(w+z*x) = u*w+(u*z+v*w)*x+(ρ*x)^2 := by rw [mul_pow,sq];ring
  rw [eq,AddChar.map_add_eq_mul,char_square,← AddChar.map_add_eq_mul]
  congr 1
  ring

/-- A complete affine line of split-form comparisons. The first form has
constant middle coefficient one. The second has a quadratic middle coefficient
with no linear term. Its unique zero is included in the sum. -/
theorem line_bound [DecidableEq F] (u v w z A B C D E G M L : F)
    (good : (u*z+v*w)^2+v*z≠0) (degree : L≠0) :
    |∑ s : F, sign (u+v*s) 1 (w+z*s)*sign (quad A B C s) (M+L*s^2) (quad D E G s)| ≤
      radius (Fintype.card F)+2 := by
  classical
  obtain ⟨ρ,hρ⟩ := square_surj (v*z)
  change ρ^2=v*z at hρ
  obtain ⟨r,hr⟩ := square_surj (M/L)
  let α := u*z+v*w+ρ
  have nonzero : α≠0 := by
    intro e
    apply good
    have es := congrArg (·^2) e
    dsimp only [α] at es
    rwa [bin_sq,hρ,zero_pow (by decide : 2≠0)] at es
  have cancel : M+L*r^2=0 := by
    change r^2=M/L at hr
    have e := (eq_div_iff degree).mp hr
    rw [mul_comm L,e,CharTwo.add_self_eq_zero]
  let T (s : F) := sign (u+v*s) 1 (w+z*s)*sign (quad A B C s) (M+L*s^2) (quad D E G s)
  have translate (a b c x : F) : quad a b c (x+r)=quad (quad a b c r) b c x := by
    simp only [quad,bin_sq]
    ring
  have mid (x : F) : M+L*(x+r)^2=L*x^2 := by
    rw [bin_sq]
    linear_combination cancel
  have point (x : F) (hx : x≠0) : T (x+r)=
      splitChar ((u*w+α*r)+α*x+pole (quad A B C r) B C (quad D E G r) E G L x) := by
    dsimp only [T]
    rw [affine_sign u v w z _ ρ hρ,mid,split_sign (mul_ne_zero degree (pow_ne_zero 2 hx)),
      ← AddChar.map_add_eq_mul,translate,translate]
    congr 1
    change u*w+α*(x+r)+_=_
    unfold pole
    ring
  have short := punctured_chart splitChar splitChar_nontrivial nonzero
    (u*w+α*r) (quad A B C r) B C (quad D E G r) E G L degree
  have reindex : ∑ x, T (x+r)=∑ s, T s := Equiv.sum_comp (Equiv.addRight r) T
  have cut := sum_erase_add (s:=(univ:Finset F)) (f:=fun x => T (x+r)) (mem_univ (0:F))
  rw [reindex,zero_add] at cut
  have absval : |T r|=1 := by simp only [T,abs_mul,sign_abs,mul_one]
  have away := sum_congr (s₁:=univ.erase (0:F)) rfl (fun x hx => point x (mem_erase.mp hx).1)
  change |∑ s, T s|≤_
  rw [← cut]
  exact (abs_add_le ..).trans (by rw [away,absval];linarith)

#print axioms line_bound

/-- Coefficients of a quadratic polynomial on the affine plane.
The coordinate order is 1, x, y, x², xy, y². -/
structure PlaneQuad (F : Type*) where
  const : F
  x : F
  y : F
  xx : F
  xy : F
  yy : F

def PlaneQuad.eval (P : PlaneQuad F) (a b : F) :=
  P.const+P.x*a+P.y*b+P.xx*a^2+P.xy*a*b+P.yy*b^2

private def direction (P : PlaneQuad F) (v z : F) := P.xx*v^2+P.xy*v*z+P.yy*z^2

private def linear (P : PlaneQuad F) (u v w z : F) :=
  P.x*v+P.y*z+P.xy*(u*z+w*v)

omit [Fintype F] in
private theorem restrict_line (P : PlaneQuad F) (u v w z s : F) :
    P.eval (u+v*s) (w+z*s) =
      quad (P.eval u w) (linear P u v w z) (direction P v z) s := by
  unfold PlaneQuad.eval quad linear direction
  rw [bin_sq,bin_sq]
  ring

/-- Product of the two splitting signs at a point of the affine chart. -/
noncomputable def weight (P Q R : PlaneQuad F) (a b : F) : ℝ :=
  sign a 1 b * sign (P.eval a b) (Q.eval a b) (R.eval a b)

omit [Fintype F] [CharP F 2] in
private theorem weight_abs (P Q R : PlaneQuad F) (a b : F) : |weight P Q R a b|=1 := by
  simp only [weight,abs_mul,sign_abs,mul_one]

private theorem on_line [DecidableEq F] (P Q R : PlaneQuad F) (u v w z : F)
    (good : (u*z+v*w)^2+v*z≠0) (pole : linear Q u v w z=0) (degree : direction Q v z≠0) :
    |∑ s : F, weight P Q R (u+v*s) (w+z*s)|≤radius (Fintype.card F)+2 := by
  have h := line_bound u v w z (P.eval u w) (linear P u v w z) (direction P v z)
    (R.eval u w) (linear R u v w z) (direction R v z) (Q.eval u w) (direction Q v z) good degree
  simpa only [weight,restrict_line,pole,quad,zero_mul,add_zero] using h

private theorem quad_roots [DecidableEq F] (A B C : F) (nonzero : B≠0 ∨ C≠0) :
    (univ.filter fun k => quad A B C k=0).card ≤ 2 := by
  classical
  let S := univ.filter (fun k : F => quad A B C k=0)
  change S.card≤2
  by_cases exists_root : S.Nonempty
  · obtain ⟨r,hr⟩ := exists_root
    have root := (mem_filter.mp hr).2
    have sub : S⊆{r,r+B/C} := by
      intro k hk
      have atK := (mem_filter.mp hk).2
      have factor : (k+r)*(B+C*(k+r))=0 := by
        rw [mul_add,show (k+r)*(C*(k+r))=C*(k+r)^2 by ring,bin_sq]
        unfold quad at root atK
        linear_combination atK + root - (CharTwo.add_self_eq_zero A)
      rcases mul_eq_zero.mp factor with eq | eq
      · have z := congrArg (·+r) eq
        have kr : k=r := by simpa only [CharTwo.add_cancel_right,zero_add] using z
        simp [kr]
      · have hC : C≠0 := by
          intro z;rw [z,zero_mul,add_zero] at eq
          exact nonzero.elim (fun h => h eq) (fun h => h z)
        have e : k+r=B/C := by
          apply (eq_div_iff hC).mpr
          have t := congrArg (·+B) eq
          calc
            _ = B+C*(k+r)+B := by rw [add_comm B (C*_),CharTwo.add_cancel_right,mul_comm]
            _ = B := by rw [eq,zero_add]
        have kr : k=r+B/C := by rw [← e,add_left_comm,CharTwo.add_self_eq_zero,add_zero]
        simp [kr]
    exact (card_le_card sub).trans Finset.card_le_two
  · rw [not_nonempty_iff_eq_empty.mp exists_root,card_empty];omega

omit [CharP F 2] in
private theorem sum_exceptional [DecidableEq F] (L : F→ℝ) (B : Finset F) (n : ℕ) (hn : B.card≤n)
    (trivial : ∀ k, |L k|≤(Fintype.card F:ℝ))
    (good : ∀ k∉B, |L k|≤radius (Fintype.card F)+2) :
    |∑ k, L k|≤(Fintype.card F:ℝ)*(radius (Fintype.card F)+2+n) := by
  classical
  let q : ℝ := Fintype.card F
  have qp : 0≤q := Nat.cast_nonneg _
  have rp : 0≤radius q := Real.rpow_nonneg (by positivity) _
  have each (k : F) : |L k| ≤ radius q+2+(if k∈B then q else 0) := by
    by_cases h : k∈B
    · rw [if_pos h];linarith only [trivial k,rp,show (Fintype.card F:ℝ)=q by rfl]
    · rw [if_neg h,add_zero];exact good k h
  have sum : (∑ k : F, if k∈B then q else 0)=(B.card:ℝ)*q := by
    rw [← sum_filter];simp
  have h := sum_le_sum (s:=univ) (fun k _ => each k)
  rw [sum_add_distrib,sum_const,card_univ,nsmul_eq_mul,sum] at h
  exact (abs_sum_le_sum_abs ..).trans (h.trans (by
    change q*(radius q+2)+B.card*q≤q*(radius q+2+n)
    nlinarith only [mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hn : (B.card:ℝ)≤n) qp]))

omit [CharP F 2] [Field F] in
private theorem trivial_line (W : F→ℝ) (h : ∀ t, |W t|=1) : |∑ t, W t|≤(Fintype.card F:ℝ) := by
  calc
    _ ≤ ∑ t, |W t| := abs_sum_le_sum_abs ..
    _ = _ := by simp [h]

omit [CharP F 2] in
private theorem rays (W : F→F→ℝ) (one : ∀ a b, |W a b|=1) (u w : F) :
    |∑ a, ∑ b, W a b| ≤ |∑ k, ∑ s, W (u+s) (w+k*s)|+2*(Fintype.card F:ℝ) := by
  classical
  let L (s : F) := ∑ k, W (u+s) (w+k*s)
  let T (s : F) := ∑ b, W (u+s) b
  have shift : ∑ s, T s=∑ a, ∑ b, W a b := Equiv.sum_comp (Equiv.addLeft u) (fun a => ∑ b, W a b)
  have bij (s : F) (hs : s≠0) : L s=T s :=
    Equiv.sum_comp ((Equiv.mulRight₀ s hs).trans (Equiv.addLeft w)) (W (u+s))
  have matchSum : ∑ s ∈ univ.erase (0:F), L s=∑ s ∈ univ.erase (0:F), T s :=
    sum_congr rfl fun s hs => bij s (mem_erase.mp hs).1
  have cutL := sum_erase_add (s:=(univ:Finset F)) (f:=L) (mem_univ (0:F))
  have cutT := sum_erase_add (s:=(univ:Finset F)) (f:=T) (mem_univ (0:F))
  have swap : ∑ s, L s=∑ k, ∑ s, W (u+s) (w+k*s) := sum_comm
  have bal : (∑ a, ∑ b, W a b) = (∑ k, ∑ s, W (u+s) (w+k*s)) + (T 0-L 0) := by
    linarith only [shift,matchSum,cutL,cutT,swap]
  rw [bal]
  have left : |T 0|≤(Fintype.card F:ℝ) := trivial_line _ (one _)
  have right : |L 0|≤(Fintype.card F:ℝ) := trivial_line _ (fun k => one _ _)
  have delta := abs_sub (T 0) (L 0)
  exact (abs_add_le ..).trans (by linarith)

/-- A nonzero mixed coefficient gives a radial pencil. At most four slopes
fail the line estimate, and the vertical line and pencil vertex cost at most 2q. -/
theorem radial_bound [DecidableEq F] (P Q R : PlaneQuad F) (mixed : Q.xy≠0) :
    |∑ a, ∑ b, weight P Q R a b| ≤ (Fintype.card F:ℝ)*(radius (Fintype.card F)+8) := by
  classical
  let u := Q.y/Q.xy
  let w := Q.x/Q.xy
  let H := univ.filter (fun k : F => quad (w^2) 1 (u^2) k=0)
  let T := univ.filter (fun k : F => quad Q.xx Q.xy Q.yy k=0)
  let L (k : F) := ∑ s, weight P Q R (u+s) (w+k*s)
  have hH : H.card≤2 := quad_roots _ _ _ (Or.inl one_ne_zero)
  have hT : T.card≤2 := quad_roots _ _ _ (Or.inl mixed)
  have hB : (H∪T).card≤4 := (card_union_le ..).trans (by omega)
  have good (k : F) (hk : k∉H∪T) : |L k|≤radius (Fintype.card F)+2 := by
    have first : quad (w^2) 1 (u^2) k≠0 := fun eq => hk (mem_union_left _ (mem_filter.mpr ⟨mem_univ _,eq⟩))
    have second : quad Q.xx Q.xy Q.yy k≠0 := fun eq => hk (mem_union_right _ (mem_filter.mpr ⟨mem_univ _,eq⟩))
    have discr : (u*k+1*w)^2+1*k≠0 := by
      intro e;apply first
      simpa only [quad,one_mul,bin_sq,mul_pow,add_comm,add_left_comm,add_assoc] using e
    have lin : linear Q u 1 w k=0 := by
      dsimp [linear,u,w]
      field_simp [mixed]
      ring_nf
      reduce_mod_char!
    have deg : direction Q 1 k≠0 := by simpa only [direction,quad,one_pow,mul_one] using second
    simpa only [L,one_mul] using on_line P Q R u 1 w k discr lin deg
  have total := sum_exceptional L (H∪T) 4 hB (fun _ => trivial_line _ (fun _ => weight_abs ..)) good
  have bound := rays (weight P Q R) (weight_abs P Q R) u w
  change |∑ a, ∑ b, weight P Q R a b|≤|∑ k, L k|+2*(Fintype.card F:ℝ) at bound
  norm_num at total
  linarith

/-- A parallel pencil in slope k when the affine polar terms cancel. -/
private theorem parallel_bound [DecidableEq F] (P Q R : PlaneQuad F) (k : F)
    (zero : Q.xy=0) (tilt : Q.x+Q.y*k=0) (deg : direction Q 1 k≠0) :
    |∑ a, ∑ b, weight P Q R a b| ≤ (Fintype.card F:ℝ)*(radius (Fintype.card F)+4) := by
  classical
  let H := univ.filter fun m : F => quad k 0 1 m=0
  let L (m : F) := ∑ s, weight P Q R s (m+k*s)
  have card : H.card≤2 := quad_roots _ _ _ (Or.inr one_ne_zero)
  have good (m : F) (hm : m∉H) : |L m|≤radius (Fintype.card F)+2 := by
    have first : (0*k+1*m)^2+1*k≠0 := by
      intro h
      apply hm
      exact mem_filter.mpr ⟨mem_univ _,by simpa only [quad,zero_mul,add_zero,zero_add,one_mul,add_comm] using h⟩
    have lin : linear Q 0 1 m k=0 := by simpa only [linear,zero,zero_mul,add_zero,mul_one] using tilt
    simpa only [L,zero_add,one_mul] using on_line P Q R 0 1 m k first lin deg
  have total := sum_exceptional L H 2 card (fun _ => trivial_line _ (fun _ => weight_abs ..)) good
  have eq : ∑ m, L m=∑ s, ∑ b, weight P Q R s b := by
    dsimp only [L];rw [sum_comm]
    exact sum_congr rfl fun s _ => Equiv.sum_comp (Equiv.addRight (k*s)) (weight P Q R s)
  rw [← eq];norm_num at total;linarith

#print axioms radial_bound

private def PlaneQuad.swap (P : PlaneQuad F) : PlaneQuad F :=
  ⟨P.const,P.y,P.x,P.yy,P.xy,P.xx⟩

omit [Fintype F] [CharP F 2] in
private theorem eval_swap (P : PlaneQuad F) (x y : F) : P.swap.eval x y=P.eval y x := by
  simp only [PlaneQuad.swap,PlaneQuad.eval]
  ring

/-- The homogeneous ternary quadratic, on coordinates (x,1,y) in the affine chart. -/
def PlaneQuad.hom (Q : PlaneQuad F) (a b c : F) :=
  Q.const*b^2+Q.x*a*b+Q.y*b*c+Q.xx*a^2+Q.xy*a*c+Q.yy*c^2

/-- Evaluation on the radical vector of the polar form. A nonzero value is the
usual nonsingularity condition for a ternary quadratic in characteristic two. -/
def PlaneQuad.discriminant (Q : PlaneQuad F) := Q.hom Q.y Q.xy Q.x

/-- Uniform splitting-sign correlation for arbitrary quadratic output coordinates
with nonsingular middle conic. -/
theorem plane_bound [DecidableEq F] (P Q R : PlaneQuad F) (regular : Q.discriminant≠0) :
    |∑ a, ∑ b, weight P Q R a b| ≤ (Fintype.card F:ℝ)*(radius (Fintype.card F)+8) := by
  by_cases mix : Q.xy≠0
  · exact radial_bound P Q R mix
  push Not at mix
  have nonzero : Q.xx*Q.y^2+Q.yy*Q.x^2≠0 := by
    simpa [PlaneQuad.discriminant,PlaneQuad.hom,mix] using regular
  have short : |∑ a, ∑ b, weight P Q R a b| ≤ (Fintype.card F:ℝ)*(radius (Fintype.card F)+4) := by
    by_cases hy : Q.y≠0
    · let k := Q.x/Q.y
      have tilt : Q.x+Q.y*k=0 := by
        have e : Q.y*k=Q.x := by dsimp [k];field_simp
        rw [e,CharTwo.add_self_eq_zero]
      have degree : direction Q 1 k≠0 := by
        intro h
        apply nonzero
        dsimp [direction,k] at h
        simp only [one_pow,mul_one,mix,zero_mul,add_zero] at h
        field_simp [hy] at h
        linear_combination h
      exact parallel_bound P Q R k mix tilt degree
    · push Not at hy
      have yy : Q.yy≠0 := fun h => nonzero (by rw [hy,h];ring)
      have degree : direction Q.swap 1 0≠0 := by
        simpa [direction,PlaneQuad.swap] using yy
      have p := parallel_bound P.swap Q.swap R.swap 0 mix
        (show Q.swap.x+Q.swap.y*0=0 by simp [PlaneQuad.swap,hy]) degree
      have same (a b : F) : weight P.swap Q.swap R.swap a b = weight P Q R b a := by
        simp only [weight,eval_swap,split_sign one_ne_zero,one_pow,div_one,mul_comm a b]
      simp only [same] at p
      rwa [sum_comm] at p
  exact short.trans (mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _))

/-- Points whose image under the quadratic coordinate triple is a split form. -/
noncomputable def output (P Q R : PlaneQuad F) : Finset (F×F) := by
  classical exact univ.filter fun z => Splits (P.eval z.1 z.2) (Q.eval z.1 z.2) (R.eval z.1 z.2)

/-- Points at which both the original and transformed forms split. -/
noncomputable def common (P Q R : PlaneQuad F) : Finset (F×F) := by
  classical exact (output P Q R).filter fun z => Splits z.1 1 z.2

theorem source_total : ∑ a : F, ∑ b : F, sign a 1 b=(Fintype.card F:ℝ) := by
  classical
  have row (a : F) : ∑ b : F, sign a 1 b=if a=0 then (Fintype.card F:ℝ) else 0 := by
    simp only [split_sign one_ne_zero,one_pow,div_one]
    by_cases h : a=0
    · simp [h]
    · rw [if_neg h]
      exact (Equiv.sum_comp (Equiv.mulLeft₀ a h) (splitChar (F:=F))).trans
        (AddChar.sum_eq_zero_iff_ne_zero.mpr splitChar_nontrivial)
  simp only [row,sum_ite_eq',mem_univ,if_true]

/-- Finite incidence estimate. No marginal density assumption is needed for
the transformed split forms. -/
theorem split_incidence [DecidableEq F] (P Q R : PlaneQuad F) (regular : Q.discriminant≠0) :
    |4*((common P Q R).card:ℝ)-2*(output P Q R).card-Fintype.card F| ≤
      (Fintype.card F:ℝ)*(radius (Fintype.card F)+8) := by
  classical
  let U := common P Q R
  let V := output P Q R
  have pt (z : F×F) : 4*(if z∈U then (1:ℝ) else 0)-2*(if z∈V then 1 else 0) =
      sign z.1 1 z.2+weight P Q R z.1 z.2 := by
    by_cases h : Splits z.1 1 z.2 <;>
      by_cases k : Splits (P.eval z.1 z.2) (Q.eval z.1 z.2) (R.eval z.1 z.2) <;>
      norm_num [U,V,common,output,sign,weight,h,k]
  have marks (T : Finset (F×F)) : (∑ z : F×F, if z∈T then (1:ℝ) else 0)=T.card := by
    rw [← sum_filter];simp
  have total := sum_congr (s₁:=univ) rfl (fun z _ => pt z)
  simp only [sum_sub_distrib,← mul_sum,marks,sum_add_distrib,Fintype.sum_prod_type,source_total] at total
  have bal : 4*(U.card:ℝ)-2*V.card-Fintype.card F = ∑ a : F, ∑ b : F, weight P Q R a b := by linarith
  change |4*(U.card:ℝ)-2*V.card-Fintype.card F|≤_
  rw [bal]
  exact plane_bound P Q R regular

#print axioms plane_bound
#print axioms split_incidence

open Filter
open scoped Topology

theorem radius_ratio {q : ℕ→ℝ} (pos : ∀ i, 0<q i) (big : Tendsto q atTop atTop) :
    Tendsto (fun i => radius (q i)/q i) atTop (𝓝 0) := by
  have tiny := (tendsto_const_nhds (x:=(15:ℝ))).div_atTop big
  have root := tiny.rpow_const_nhds_zero (by norm_num : 0<(8:ℝ)⁻¹)
  apply root.congr
  intro i
  have hq := pos i
  have rad : 0≤15*(q i)^7 := by positivity
  have pw : (radius (q i)/q i)^8=15/q i := by
    rw [div_pow]
    unfold radius
    rw [show (8:ℝ)⁻¹=((8:ℕ):ℝ)⁻¹ by norm_num,
      Real.rpow_inv_natCast_pow rad (by decide : 8 ≠ 0)]
    field_simp [hq.ne']
  have nn : 0≤radius (q i)/q i := div_nonneg (Real.rpow_nonneg rad _) (pos i).le
  rw [← pw]
  exact Real.pow_rpow_inv_natCast nn (by decide : 8 ≠ 0)

/-- On fields of increasing order, half the transformed split-form count
is the simultaneous count, up to o(q²), uniformly in the three quadratics. -/
theorem incidence_limit {K : ℕ→Type*} [∀ i, Field (K i)] [∀ i, Fintype (K i)]
    [∀ i, CharP (K i) 2] [∀ i, DecidableEq (K i)] (P Q R : ∀ i, PlaneQuad (K i))
    (regular : ∀ i, (Q i).discriminant≠0)
    (big : Tendsto (fun i => Fintype.card (K i)) atTop atTop) :
    Tendsto (fun i => (4*((common (P i) (Q i) (R i)).card:ℝ)-2*(output (P i) (Q i) (R i)).card)/
      (Fintype.card (K i):ℝ)^2) atTop (𝓝 0) := by
  let q i : ℝ := Fintype.card (K i)
  have qp i : 0<q i := by dsimp [q];exact_mod_cast Fintype.card_pos
  have large : Tendsto q atTop atTop := tendsto_natCast_atTop_atTop.comp big
  have tiny := (tendsto_const_nhds (x:=(9:ℝ))).div_atTop large
  have lim := (radius_ratio qp large).add tiny
  rw [add_zero] at lim
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ lim
  filter_upwards with i
  let z : ℝ := 4*((common (P i) (Q i) (R i)).card:ℝ)-2*(output (P i) (Q i) (R i)).card
  have bound := split_incidence (P i) (Q i) (R i) (regular i)
  change |z-q i|≤q i*(radius (q i)+8) at bound
  have num : |z| ≤ q i*(radius (q i)+9) := by
    have h := abs_add_le (z-q i) (q i)
    rw [sub_add_cancel,abs_of_pos (qp i)] at h
    linarith
  change ‖z/q i^2‖ ≤ radius (q i)/q i+9/q i
  rw [Real.norm_eq_abs,abs_div,abs_of_nonneg (sq_nonneg (q i)),← add_div]
  apply (div_le_div_iff₀ (sq_pos_of_pos (qp i)) (qp i)).mpr
  nlinarith only [mul_le_mul_of_nonneg_right num (qp i).le]

#print axioms incidence_limit

end Green33SplitPencils
