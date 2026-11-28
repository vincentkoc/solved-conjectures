import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic
import Mathlib.Tactic.ReduceModChar

/-! Reciprocal character sums in the affine charts of binary cyclic seeds. -/

open Finset
open scoped BigOperators

namespace Green33ReciprocalCharts

variable {F : Type*} [Field F] [CharP F 2]

/-- The vanishing polynomial of the four shifts 0, a, b and a+b,
with their multiplicities when a and b are dependent. -/
def face (a b x : F) : F := x*(x+a)*(x+b)*(x+a+b)

private theorem face_add (a b x y : F) : face a b (x+y)=face a b x+face a b y := by
  unfold face
  ring_nf
  reduce_mod_char!

/-- The sum of reciprocals on the four-point affine face. -/
def invFace (a b x : F) : F := x⁻¹+(x+a)⁻¹+(x+b)⁻¹+(x+a+b)⁻¹

private theorem face_fraction {a b x : F} (hx : face a b x≠0) :
    invFace a b x=a*b*(a+b)/face a b x := by
  have nz : x≠0 ∧ x+a≠0 ∧ x+b≠0 ∧ x+a+b≠0 := by
    unfold face at hx
    simpa only [mul_ne_zero_iff, and_assoc] using hx
  unfold face invFace
  field_simp [nz.1,nz.2.1,nz.2.2.1,nz.2.2.2]
  ring_nf
  reduce_mod_char!

/-- The third additive difference of inversion at a cube that avoids zero. -/
theorem reciprocal_cube {a b c x : F} (hx : face a b x≠0) (hy : face a b (x+c)≠0) :
    invFace a b x+invFace a b (x+c)=
    a*b*(a+b)*face a b c/(face a b x*face a b (x+c)) := by
  rw [face_fraction hx,face_fraction hy]
  have shift := face_add a b x c
  field_simp [hx,hy]
  rw [shift]
  ring_nf
  reduce_mod_char!

#print axioms reciprocal_cube

variable [DecidableEq F]

private def zeroMark (y : F) : ℝ := if y=0 then 1 else 0

omit [CharP F 2] in
private theorem mark_nonneg (y : F) : 0≤zeroMark y := by by_cases h : y=0 <;> simp [zeroMark,h]
omit [CharP F 2] in
private theorem mark_le_one (y : F) : zeroMark y≤1 := by by_cases h : y=0 <;> simp [zeroMark,h]

omit [CharP F 2] in
private theorem mark_mul (y z : F) : zeroMark (y*z)≤zeroMark y+zeroMark z := by
  by_cases h : y=0 <;> by_cases k : z=0 <;> simp [zeroMark,h,k]

omit [CharP F 2] in
private theorem face_mark (a b x : F) :
    zeroMark (face a b x)≤zeroMark x+zeroMark (x+a)+zeroMark (x+b)+zeroMark (x+(a+b)) := by
  have one := mark_mul x (x+a)
  have two := mark_mul (x*(x+a)) (x+b)
  have three := mark_mul (x*(x+a)*(x+b)) (x+a+b)
  unfold face
  rw [← add_assoc x a b]
  linarith

variable [Fintype F]

omit [CharP F 2] in
private theorem shift_mark (c : F) : ∑ x : F, zeroMark (x+c)=1 := by
  have move : ∑ x : F, zeroMark (x+c)= ∑ x : F, zeroMark x := Equiv.sum_comp (Equiv.addRight c) zeroMark
  rw [move];simp [zeroMark]

omit [CharP F 2] in
private theorem face_count (a b c : F) : ∑ x : F, zeroMark (face a b (x+c))≤4 := by
  calc
    _ = ∑ x : F, zeroMark (face a b x) := Equiv.sum_comp (Equiv.addRight c) (fun x => zeroMark (face a b x))
    _ ≤ ∑ x : F, (zeroMark x+zeroMark (x+a)+zeroMark (x+b)+zeroMark (x+(a+b))) :=
      sum_le_sum fun x _ => face_mark a b x
    _ = 4 := by
      have z : ∑ x : F, zeroMark x=1 := by simp [zeroMark]
      simp only [sum_add_distrib,shift_mark,z]
      norm_num

omit [Fintype F] in
private theorem cube_mark (a b c x : F) :
    zeroMark (invFace a b x+invFace a b (x+c)) ≤
      zeroMark (a*b*(a+b)*face a b c) + zeroMark (face a b x)+zeroMark (face a b (x+c)) := by
  by_cases hx : face a b x=0
  · have h : zeroMark (face a b x)=1 := by simp [zeroMark,hx]
    linarith only [h,mark_nonneg (a*b*(a+b)*face a b c),mark_nonneg (face a b (x+c)),mark_le_one (invFace a b x+invFace a b (x+c))]
  by_cases hy : face a b (x+c)=0
  · have h : zeroMark (face a b (x+c))=1 := by simp [zeroMark,hy]
    linarith only [h,mark_nonneg (a*b*(a+b)*face a b c),mark_nonneg (face a b x),mark_le_one (invFace a b x+invFace a b (x+c))]
  rw [reciprocal_cube hx hy]
  simp [zeroMark,hx,hy,div_eq_zero_iff]

omit [CharP F 2] in
private theorem bad_directions (a b : F) : ∑ c : F, zeroMark (a*b*(a+b)*face a b c) ≤
    (Fintype.card F:ℝ)*zeroMark (a*b*(a+b))+4 := by
  have h := sum_le_sum (s:=univ) (fun c _ => mark_mul (a*b*(a+b)) (face a b c))
  have f : ∑ c : F, zeroMark (face a b c)≤4 := by simpa only [add_zero] using face_count a b 0
  simp only [sum_add_distrib,sum_const,card_univ,nsmul_eq_mul] at h
  linarith

omit [CharP F 2] in
private theorem bad_pairs : ∑ a : F, ∑ b : F, zeroMark (a*b*(a+b)) ≤ 3*(Fintype.card F:ℝ) := by
  have one (a b : F) : zeroMark (a*b*(a+b))≤zeroMark a+zeroMark b+zeroMark (b+a) := by
    rw [add_comm b a]
    linarith only [mark_mul a b,mark_mul (a*b) (a+b)]
  have z : ∑ x : F, zeroMark x=1 := by simp [zeroMark]
  calc
    _ ≤ ∑ a : F, ∑ b : F, (zeroMark a+zeroMark b+zeroMark (b+a)) :=
      sum_le_sum fun a _ => sum_le_sum fun b _ => one a b
    _ = _ := by
      simp only [sum_add_distrib,shift_mark,z,sum_const,nsmul_eq_mul,card_univ,← mul_sum,mul_one]
      ring

/-- At most 15 q³ additive cubes have zero third difference of inversion,
counting the base point and the ordered directions in a field of order q. -/
theorem zero_cubes :
    (∑ a : F, ∑ b : F, ∑ c : F, ∑ x : F,
      if invFace a b x+invFace a b (x+c)=0 then (1:ℝ) else 0) ≤ 15*(Fintype.card F:ℝ)^3 := by
  let q : ℝ := Fintype.card F
  have qp : 0≤q := Nat.cast_nonneg _
  have point (a b c : F) : ∑ x : F, zeroMark (invFace a b x+invFace a b (x+c)) ≤
      q*zeroMark (a*b*(a+b)*face a b c)+8 := by
    have h := sum_le_sum (s:=univ) (fun x _ => cube_mark a b c x)
    simp only [sum_add_distrib,sum_const,card_univ,nsmul_eq_mul] at h
    have first : ∑ x : F, zeroMark (face a b x)≤4 := by simpa only [add_zero] using face_count a b 0
    change _ ≤ (Fintype.card F:ℝ)*_+8
    linarith only [h,first,face_count a b c]
  have span (a b : F) : (∑ c : F, ∑ x : F, zeroMark (invFace a b x+invFace a b (x+c))) ≤
      q^2*zeroMark (a*b*(a+b))+12*q := by
    have h := sum_le_sum (s:=univ) (fun c _ => point a b c)
    simp only [sum_add_distrib,← mul_sum,sum_const,card_univ,nsmul_eq_mul] at h
    have p := mul_le_mul_of_nonneg_left (bad_directions a b) qp
    dsimp only [q] at *
    nlinarith only [h,p]
  have h := sum_le_sum (s:=univ) (fun a _ => sum_le_sum (s:=univ) (fun b _ => span a b))
  simp only [sum_add_distrib,← mul_sum,sum_const,card_univ,nsmul_eq_mul] at h
  have p := mul_le_mul_of_nonneg_left (bad_pairs (F:=F)) (sq_nonneg q)
  change (∑ a : F, ∑ b : F, ∑ c : F, ∑ x : F, zeroMark (invFace a b x+invFace a b (x+c))) ≤ 15*q^3
  dsimp only [q] at *
  nlinarith only [h,p]

#print axioms zero_cubes

private abbrev Cube (F : Type*) := F × F × F × F

private def thirdInv (p : Cube F) : F :=
  invFace p.1 p.2.1 p.2.2.2+invFace p.1 p.2.1 (p.2.2.2+p.2.2.1)

omit [Fintype F] [DecidableEq F] [CharP F 2] in
private theorem face_scale (k a b x : F) :
    invFace (k*a) (k*b) (k*x)=k⁻¹*invFace a b x := by
  simp only [invFace,← mul_add,mul_inv_rev]
  ring

omit [CharP F 2] [DecidableEq F] in
private theorem scale_sum (ψ : AddChar F ℝ) {k : F} (hk : k≠0) :
    ∑ p : Cube F, ψ (k*thirdInv p) = ∑ p : Cube F, ψ (thirdInv p) := by
  let u := Equiv.mulLeft₀ k hk
  let e : Cube F ≃ Cube F := u.prodCongr (u.prodCongr (u.prodCongr u))
  calc
    _ = ∑ p : Cube F, ψ (k*thirdInv (e p)) := (Equiv.sum_comp e (fun p => ψ (k*thirdInv p))).symm
    _ = _ := by
      apply sum_congr rfl
      rintro ⟨a,b,c,x⟩ _
      change ψ (k*(invFace (k*a) (k*b) (k*x)+invFace (k*a) (k*b) (k*x+k*c))) =
        ψ (invFace a b x+invFace a b (x+c))
      rw [← mul_add k x c,face_scale,face_scale,← mul_add,← mul_assoc,mul_inv_cancel₀ hk,one_mul]

omit [CharP F 2] in
private theorem character_orthogonal (ψ : AddChar F ℝ) (nontrivial : ψ≠0) (z : F) :
    ∑ k ∈ (univ.erase (0:F)), ψ (k*z) ≤ ((univ.erase (0:F)).card:ℝ)*zeroMark z := by
  classical
  by_cases hz : z=0
  · subst z;simp [zeroMark]
  · have total : ∑ k : F, ψ (k*z) = 0 := by
      have shift := Equiv.sum_comp (Equiv.mulRight₀ z hz) ψ
      exact shift.trans (AddChar.sum_eq_zero_iff_ne_zero.mpr nontrivial)
    have split := sum_erase_add (s:=(univ:Finset F)) (f:=fun k => ψ (k*z)) (mem_univ (0:F))
    rw [total,zero_mul,ψ.map_zero_eq_one] at split
    simp only [zeroMark,if_neg hz,mul_zero]
    linarith

/-- Scalar dilation and additive character orthogonality convert the zero-cube
count into a bound for the complete reciprocal cube sum. -/
theorem character_cubes (ψ : AddChar F ℝ) (nontrivial : ψ≠0) {α : F} (ha : α≠0) :
    (∑ a : F, ∑ b : F, ∑ c : F, ∑ x : F, ψ (α*(invFace a b x+invFace a b (x+c)))) ≤
      15*(Fintype.card F:ℝ)^3 := by
  classical
  let U := univ.erase (0:F)
  have nz : 0<(U.card:ℝ) := by
    exact_mod_cast card_pos.mpr (show U.Nonempty from ⟨1,mem_erase.mpr ⟨one_ne_zero,mem_univ _⟩⟩)
  have h : (U.card:ℝ)*(∑ p : Cube F, ψ (thirdInv p)) ≤ (U.card:ℝ)* ∑ p : Cube F, zeroMark (thirdInv p) := by
    calc
      _ = ∑ _k ∈ U, ∑ p : Cube F, ψ (thirdInv p) := by simp
      _ = ∑ k ∈ U, ∑ p : Cube F, ψ (k*thirdInv p) := by
        apply sum_congr rfl
        intro k hk
        exact (scale_sum ψ (mem_erase.mp hk).1).symm
      _ = ∑ p : Cube F, ∑ k ∈ U, ψ (k*thirdInv p) := sum_comm
      _ ≤ ∑ p : Cube F, (U.card:ℝ)*zeroMark (thirdInv p) :=
        sum_le_sum fun p _ => character_orthogonal ψ nontrivial (thirdInv p)
      _ = _ := (mul_sum ..).symm
  have bound := le_of_mul_le_mul_left h nz
  have scaled := scale_sum ψ ha
  simp only [Fintype.sum_prod_type,thirdInv] at bound scaled
  exact scaled.le.trans (bound.trans (zero_cubes (F:=F)))

#print axioms character_cubes

section CubeBound

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- Multiplicative first difference for real-valued signs. -/
def edge (f : G → ℝ) (a x : G) := f x*f (x+a)

private theorem square_sum (f : G → ℝ) :
    (∑ x, f x)^2=∑ a, ∑ x, edge f a x := by
  rw [sum_comm,sq,sum_mul]
  apply sum_congr rfl
  intro x _
  unfold edge
  rw [← mul_sum]
  exact congrArg (f x*·) (Equiv.sum_comp (Equiv.addLeft x) f).symm

/-- Three Cauchy–Schwarz steps with the unnormalized counting convention. -/
theorem cube_bound (f : G → ℝ) :
    (∑ x, f x)^8 ≤ (Fintype.card G:ℝ)^4 * ∑ a, ∑ b, ∑ c, ∑ x, edge (edge (edge f a) b) c x := by
  let q : ℝ := Fintype.card G
  let S := ∑ x, f x
  let H (a : G) := ∑ x, edge f a x
  let J (a b : G) := ∑ x, edge (edge f a) b x
  have one : S^2=∑ a, H a := square_sum f
  have two a : H a^2=∑ b, J a b := square_sum (edge f a)
  have three a b : J a b^2=∑ c, ∑ x, edge (edge (edge f a) b) c x := square_sum (edge (edge f a) b)
  have cs := sq_sum_le_card_mul_sum_sq (s:=(univ:Finset G)) (f:=H)
  rw [← one] at cs
  simp only [two,card_univ] at cs
  have first : S^4 ≤ q*∑ a, ∑ b, J a b := by simpa only [← pow_mul] using cs
  have pairs := sq_sum_le_card_mul_sum_sq (s:=(univ:Finset (G×G))) (f:=fun z => J z.1 z.2)
  simp only [Fintype.sum_prod_type,card_univ,Fintype.card_prod,Nat.cast_mul,three] at pairs
  calc
    _ = (S^4)^2 := by ring
    _ ≤ (q*∑ a, ∑ b, J a b)^2 := pow_le_pow_left₀ (by positivity) first 2
    _ = q^2*(∑ a, ∑ b, J a b)^2 := mul_pow ..
    _ ≤ q^2*((q*q)*∑ a, ∑ b, ∑ c, ∑ x, edge (edge (edge f a) b) c x) :=
      mul_le_mul_of_nonneg_left pairs (sq_nonneg _)
    _ = _ := by dsimp only [q];ring

end CubeBound

#print axioms cube_bound

/-- Complete correlation bound against any real phase with trivial third
multiplicative differences. The inverse at zero has its field value zero. -/
theorem reciprocal_correlation (ψ : AddChar F ℝ) (nontrivial : ψ≠0) {α : F} (ha : α≠0)
    (Q : F → ℝ) (quad : ∀ a b c x, edge (edge (edge Q a) b) c x=1) :
    (∑ x, ψ (α*x⁻¹)*Q x)^8 ≤ 15*(Fintype.card F:ℝ)^7 := by
  let f (x : F) := ψ (α*x⁻¹)
  have alone (a b c x : F) : edge (edge (edge f a) b) c x =
      ψ (α*(invFace a b x+invFace a b (x+c))) := by
    unfold edge f invFace
    simp only [mul_add,AddChar.map_add_eq_mul]
    simp only [add_comm,add_left_comm,mul_comm,mul_left_comm]
  have product (a b c x : F) :
      edge (edge (edge (fun y => f y*Q y) a) b) c x =
        edge (edge (edge f a) b) c x*edge (edge (edge Q a) b) c x := by
    simp only [edge]
    ring
  have bound := cube_bound (fun y => f y*Q y)
  simp only [product,quad,mul_one,alone] at bound
  have result := mul_le_mul_of_nonneg_left (character_cubes ψ nontrivial ha)
      (by positivity : 0≤(Fintype.card F:ℝ)^4)
  exact bound.trans (result.trans_eq (by ring))

omit [Fintype F] [DecidableEq F] in
/-- Quartics over a field of characteristic two give phases of Boolean degree at most two. -/
private theorem quartic_phase (ψ : AddChar F ℝ) (A B C D E a b c x : F) :
    let Q (y : F) := ψ (A+B*y+C*y^2+D*y^3+E*y^4)
    edge (edge (edge Q a) b) c x=1 := by
  dsimp only
  simp only [edge,← AddChar.map_add_eq_mul]
  rw [← ψ.map_zero_eq_one]
  apply congrArg ψ
  ring_nf
  reduce_mod_char!

/-- The complete sum on a good reciprocal chart with arbitrary quartic
coefficients. The exponent on the left allows the estimate to stay algebraic. -/
theorem reciprocal_quartic (ψ : AddChar F ℝ) (nontrivial : ψ≠0) {α : F} (ha : α≠0)
    (A B C D E : F) :
    (∑ x, ψ (α*x⁻¹+(A+B*x+C*x^2+D*x^3+E*x^4)))^8 ≤ 15*(Fintype.card F:ℝ)^7 := by
  simpa only [AddChar.map_add_eq_mul] using
    reciprocal_correlation ψ nontrivial ha _ (quartic_phase ψ A B C D E)

#print axioms reciprocal_correlation
#print axioms reciprocal_quartic

/-- A real upper bound for the complete sum in a field of order q. -/
noncomputable def radius (q : ℝ) : ℝ := (15*q^7)^((8:ℝ)⁻¹)

omit [Fintype F] [DecidableEq F] in
private theorem char_abs (ψ : AddChar F ℝ) (x : F) : |ψ x|=1 := by
  have p : ψ x^2=1 := by rw [sq,← ψ.map_add_eq_mul,CharTwo.add_self_eq_zero,ψ.map_zero_eq_one]
  rcases sq_eq_one_iff.mp p with p | p <;> simp [p]

omit [Field F] [CharP F 2] [DecidableEq F] in
private theorem sum_radius {S : ℝ} (h : S^8 ≤ 15*(Fintype.card F:ℝ)^7) :
    |S| ≤ radius (Fintype.card F) := by
  have p := Real.rpow_le_rpow (abs_nonneg (S^8)) (show |S^8| ≤ 15*(Fintype.card F:ℝ)^7 by
    rwa [abs_of_nonneg (by positivity : 0≤S^8)]) (by norm_num : 0 ≤ (8:ℝ)⁻¹)
  unfold radius
  rw [← pow_abs] at p
  simpa only [show (8:ℝ)⁻¹=((8:ℕ):ℝ)⁻¹ by norm_num,
    Real.pow_rpow_inv_natCast (abs_nonneg S) (by decide : 8 ≠ 0)] using p

/-- A quadratic polynomial, with coefficients in ascending order. -/
def quad (A B C x : F) := A+B*x+C*x^2

/-- A product of two quadratic numerators divided by the square of a quadratic
with a double root at zero. The chart sum omits that point. -/
def pole (A B C D E G L x : F) := quad A B C x*quad D E G x/(L*x^2)^2

/-- On the punctured parameter line, an affine phase and a split criterion
with a double pole have correlation at most (15q⁷)^(1/8)+1. -/
theorem punctured_chart (ψ : AddChar F ℝ) (nt : ψ≠0) {α : F} (ha : α≠0)
    (k A B C D E G L : F) (nonzero : L≠0) :
    |∑ x ∈ univ.erase (0:F), ψ (k+α*x+pole A B C D E G L x)| ≤ radius (Fintype.card F)+1 := by
  let P (y : F) := k+quad C B A y*quad G E D y/L^2
  let H (y : F) := ψ (α*y⁻¹+P y)
  have expand (y : F) : P y =
      (k+C*G/L^2)+(B*G+C*E)/L^2*y+(A*G+B*E+C*D)/L^2*y^2+
      (A*E+B*D)/L^2*y^3+A*D/L^2*y^4 := by dsimp [P,quad];ring
  have full : |∑ y, H y| ≤ radius (Fintype.card F) := by
    apply sum_radius
    simp only [H,expand]
    apply reciprocal_quartic ψ nt ha
  have point (x : F) (hx : x≠0) : H x⁻¹=ψ (k+α*x+pole A B C D E G L x) := by
    apply congrArg ψ
    change α*x⁻¹⁻¹+(k+quad C B A x⁻¹*quad G E D x⁻¹/L^2)=_
    simp only [inv_inv,quad,pole]
    field_simp [hx,nonzero]
    ring
  have move : ∑ x : F, H x⁻¹ = ∑ y, H y := Equiv.sum_comp (Equiv.inv F) H
  have bal := sum_erase_add (s:=(univ:Finset F)) (f:=fun x => H x⁻¹) (mem_univ (0:F))
  rw [move,inv_zero] at bal
  have erased : ∑ x ∈ univ.erase (0:F), ψ (k+α*x+pole A B C D E G L x) =
      (∑ y, H y)-H 0 := by
    rw [← eq_sub_of_add_eq bal]
    exact sum_congr rfl fun x hx => (point x (mem_erase.mp hx).1).symm
  rw [erased]
  have hzero : |H 0|=1 := char_abs ψ _
  exact (abs_sub _ _).trans (add_le_add full hzero.le)

#print axioms punctured_chart

end Green33ReciprocalCharts
