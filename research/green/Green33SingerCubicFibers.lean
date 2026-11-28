import Green33PrimeQuarticCharacter

/-! Split cubics in a pencil through a fixed irreducible cubic. An odd-degree
extension containing its three roots gives a nonzero square value of the
discriminant of the residual quadratic. -/

open Finset Polynomial
open scoped BigOperators Polynomial

namespace Green33SingerCubicFibers

/-- Coefficients of a monic cubic and of a polynomial of degree at most two. -/
structure Pencil (F : Type*) where
  i : F
  j : F
  k : F
  a : F
  b : F
  c : F

namespace Pencil

variable {F E : Type*} [CommRing F] [CommRing E]

def map (P : Pencil F) (φ : F→+*E) : Pencil E := ⟨φ P.i,φ P.j,φ P.k,φ P.a,φ P.b,φ P.c⟩

def cubic (P : Pencil F) (x : F) := x^3+P.i*x^2+P.j*x+P.k
def quad (P : Pencil F) (x : F) := P.a*x^2+P.b*x+P.c
def middle (P : Pencil F) (x : F) := P.b*x^2+(P.i*P.b+P.c-P.a*P.j)*x+(P.i*P.c-P.a*P.k)
def last (P : Pencil F) (x : F) := P.c*x^2+(P.i*P.c-P.a*P.k)*x+(P.j*P.c-P.b*P.k)
def disc (P : Pencil F) (x : F) := (P.middle x)^2-4*P.quad x*P.last x

/-- Dividing the pencil member through the known root leaves a quadratic. -/
theorem residual (P : Pencil F) (x y : F) :
    P.quad x*P.cubic y-P.cubic x*P.quad y =
      (y-x)*(P.quad x*y^2+P.middle x*y+P.last x) := by
  unfold quad cubic middle last
  ring

/-- At any one of three distinct poles, the residual discriminant is a square. -/
theorem pole_value (P : Pencil F) {r s t : F} (one : r+s+t= -P.i)
    (two : r*s+r*t+s*t=P.j) (three : r*s*t= -P.k) :
    P.disc r=(P.quad r*(s-t))^2 := by
  have he : P.i= -(r+s+t) := by linear_combination one
  have hk : P.k= -(r*s*t) := by linear_combination three
  unfold disc quad middle last
  rw [he,←two,hk]
  ring

noncomputable def polynomial (P : Pencil F) : F[X] := (P.map C).disc X

theorem eval_polynomial (P : Pencil F) (φ : F→+*E) (x : E) :
    (P.polynomial.map φ).eval x=(P.map φ).disc x := by
  simp [polynomial,disc,middle,last,quad,map]

theorem polynomial_degree (P : Pencil F) : P.polynomial.natDegree≤4 := by
  unfold polynomial disc middle last quad map
  compute_degree

end Pencil

variable {p : ℕ} [Fact p.Prime]

private def rootsAt (P : Pencil (ZMod p)) (x : ZMod p) :=
  univ.filter fun y : ZMod p => P.quad x*y^2+P.middle x*y+P.last x=0

/-- The admissible roots of the residual quadratic at the given finite parameter. -/
def fiber (P : Pencil (ZMod p)) (x : ZMod p) : Finset (ZMod p) :=
  if P.quad x=0 then ∅ else rootsAt P x

theorem mem_fiber (P : Pencil (ZMod p)) (x y : ZMod p) :
    y∈fiber P x ↔ P.quad x≠0 ∧ P.quad x*y^2+P.middle x*y+P.last x=0 := by
  by_cases z : P.quad x=0 <;> simp [fiber,rootsAt,z]

private theorem fiber_size (P : Pencil (ZMod p)) (odd : ringChar (ZMod p)≠2)
    (x : ZMod p) (u : P.quad x≠0) :
    ((fiber P x).card:ℤ)=quadraticChar (ZMod p) (P.disc x)+1 := by
  classical
  have two : (2:ZMod p)≠0 := Ring.two_ne_zero odd
  have count := quadraticChar_card_sqrts odd (P.disc x)
  refine Eq.trans (congrArg (Nat.cast (R:=ℤ)) ?_) count
  apply card_nbij' (fun y => 2*P.quad x*y+P.middle x) (fun z => (z-P.middle x)/(2*P.quad x))
  · intro y hy
    have eq := (mem_fiber P x y).mp hy |>.2
    apply Set.mem_toFinset.mpr
    change (2*P.quad x*y+P.middle x)^2=P.disc x
    unfold Pencil.disc
    linear_combination (4*P.quad x)*eq
  · intro z hz
    have e := Set.mem_toFinset.mp hz
    change z^2=P.disc x at e
    apply (mem_fiber P x _).mpr
    refine ⟨u,?_⟩
    unfold Pencil.disc at e
    field_simp [two,u]
    linear_combination e
  · intro y _;field_simp [two,u];ring
  · intro z _;field_simp [two,u];ring

private theorem exceptional_points (P : Pencil (ZMod p)) {K : Type*} [Field K]
    (φ : ZMod p→+*K) (r : K) (nr : (P.map φ).quad r≠0) :
    (univ.filter (fun x : ZMod p => P.quad x=0)).card≤2 := by
  classical
  let Q := (P.map C).quad (X : (ZMod p)[X])
  have nv : Q≠0 := by
    intro zero
    have val : (Q.map φ).eval r=(P.map φ).quad r := by simp [Q,Pencil.quad,Pencil.map]
    exact nr (by rw [← val,zero];simp)
  have deg : Q.natDegree≤2 := by unfold Q Pencil.quad Pencil.map;compute_degree
  have sub : univ.filter (fun x : ZMod p => P.quad x=0) ⊆ Q.roots.toFinset := by
    intro x hx
    apply Multiset.mem_toFinset.mpr
    apply (mem_roots nv).mpr
    change Q.eval x=0
    simpa [Q,Pencil.map,Pencil.quad] using (mem_filter.mp hx).2
  exact (card_le_card sub).trans (Q.roots.toFinset_card_le.trans ((card_roots' Q).trans deg))

/-- A cubic pencil with three distinct poles in an odd-degree extension has
many ordered pairs whose residual quadratic splits. Repetitions are included. -/
theorem many_pairs {K : Type*} [Field K] [Algebra (ZMod p) K]
    [FiniteDimensional (ZMod p) K] (ext : Odd (Module.finrank (ZMod p) K))
    (P : Pencil (ZMod p)) (r s t : K)
    (one : r+s+t= -algebraMap (ZMod p) K P.i)
    (two : r*s+r*t+s*t=algebraMap (ZMod p) K P.j)
    (three : r*s*t= -algebraMap (ZMod p) K P.k) (st : s≠t)
    (nz : (P.map (algebraMap (ZMod p) K)).quad r≠0) (big : 400≤p) :
    p ≤ (∑ x : ZMod p, (fiber P x).card)+80*(p.sqrt+1)+8 := by
  classical
  let φ := algebraMap (ZMod p) K
  let W := (P.map φ).quad r*(s-t)
  have nw : W≠0 := mul_ne_zero nz (sub_ne_zero.mpr st)
  have val : (P.polynomial.map φ).eval r=W^2 :=
    (P.eval_polynomial φ r).trans ((P.map φ).pole_value one two three)
  have lower := Green33PrimeQuarticCharacter.quartic_lower ext P.polynomial P.polynomial_degree r W nw val big
  have eval (x : ZMod p) : P.polynomial.eval x=P.disc x := by
    simp [Pencil.polynomial,Pencil.disc,Pencil.middle,Pencil.last,Pencil.quad,Pencil.map]
  simp only [eval] at lower
  have fld : ringChar (ZMod p)≠2 := by rw [ringChar.eq (ZMod p) p];omega
  have cost (x : ZMod p) : quadraticChar (ZMod p) (P.disc x)+1 ≤
      ((fiber P x).card:ℤ)+2*(if P.quad x=0 then 1 else 0) := by
    by_cases u : P.quad x=0
    · simp only [fiber,u,if_pos,card_empty,Nat.cast_zero,mul_one,zero_add]
      by_cases d : P.disc x=0
      · simp [d]
      · rcases quadraticChar_dichotomy d with h|h <;> rw [h] <;> norm_num
    · rw [fiber_size P fld x u,if_neg u,mul_zero,add_zero]
  have charge := sum_le_sum (s:=univ) (fun x _ => cost x)
  simp only [sum_add_distrib,←mul_sum,sum_boole,sum_const,card_univ,ZMod.card,nsmul_eq_mul,mul_one,←Nat.cast_sum] at charge
  have cap := exceptional_points P φ r nz
  omega

#print axioms many_pairs

namespace Pencil

variable {F : Type*} [Field F]

/-- The other root of the residual quadratic with known root `y`. -/
def mate (P : Pencil F) (x y : F) := -(P.middle x)/(P.quad x)-y

theorem split_value (P : Pencil F) {x y r : F} (u : P.quad x≠0)
    (root : P.quad x*y^2+P.middle x*y+P.last x=0) (pole : P.cubic r=0) :
    (r-x)*(r-y)*(r-P.mate x y)= (-(P.cubic x)/(P.quad x))*P.quad r := by
  have det := P.residual x r
  rw [pole,mul_zero,zero_sub] at det
  have pair : P.quad x*(r-y)*(r-P.mate x y)=P.quad x*r^2+P.middle x*r+P.last x := by
    unfold mate
    field_simp [u]
    linear_combination -root
  field_simp [u]
  linear_combination (r-x)*pair-det

end Pencil

/-- Each root counted in the preceding bound gives an ordered triple with the
prescribed projective product. The scalar is nonzero when the cubic has no
base-field root. -/
theorem product_identity {K : Type*} [Field K] (φ : ZMod p→+*K)
    (P : Pencil (ZMod p)) {x y : ZMod p} (hy : y∈fiber P x) (r : K)
    (pole : (P.map φ).cubic r=0) :
    (r-φ x)*(r-φ y)*(r-φ (P.mate x y))=φ (-(P.cubic x)/(P.quad x))*(P.map φ).quad r := by
  obtain ⟨u,root⟩ := (mem_fiber P x y).mp hy
  have q : (P.map φ).quad (φ x)=φ (P.quad x) := by simp [Pencil.quad,Pencil.map]
  have m : (P.map φ).middle (φ x)=φ (P.middle x) := by simp [Pencil.middle,Pencil.map]
  have c : (P.map φ).last (φ x)=φ (P.last x) := by simp [Pencil.last,Pencil.map]
  have M : (P.map φ).cubic (φ x)=φ (P.cubic x) := by simp [Pencil.cubic,Pencil.map]
  have pair := (P.map φ).split_value (y:=φ y) (q ▸ (map_ne_zero φ).mpr u)
    (by rw [q,m,c];simpa only [map_add,map_mul,map_pow,map_zero] using congrArg φ root) pole
  simpa only [Pencil.mate,m,q,M,map_sub,map_div₀,map_neg] using pair

#print axioms product_identity

end Green33SingerCubicFibers
