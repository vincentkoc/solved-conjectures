import Mathlib.Tactic

/-! # Wilson's bijection for adjacent multiplicative cosets

The two ratios determine an ordered pair of distinct arguments. The inverse
calculation is Wilson's bijection in Betsumiya, Hirasaka, Komatsu and Munemasa,
*Upper bounds on cyclotomic numbers*, Lemma 2.1, with the arguments shifted by one.
-/

namespace Erdos478.CyclotomicProfiles
variable {F : Type*} [Field F]

def Regular (x : F) : Prop := x≠0 ∧ x+1≠0

def profileRatios (x y : F) : F × F := (x/y,(x+1)/(y+1))

theorem recover_argument {x y u v : F} (hy : Regular y)
    (hu : x/y=u) (hv : (x+1)/(y+1)=v) : (u-v)*y=v-1 := by
  have a := (div_eq_iff hy.1).mp hu
  have b := (div_eq_iff hy.2).mp hv
  linear_combination b-a

theorem regular_ratios {x y : F} (hx : Regular x) (hy : Regular y) (ne : x≠y) :
    let (u,v) := profileRatios x y
    (u≠0 ∧ u≠1) ∧ (v≠0 ∧ v≠1) ∧ u≠v := by
  refine ⟨⟨div_ne_zero hx.1 hy.1,fun eq => ne ((div_eq_one_iff_eq hy.1).mp eq)⟩,
    ⟨div_ne_zero hx.2 hy.2,fun eq => ne (add_right_cancel ((div_eq_one_iff_eq hy.2).mp eq))⟩,?_⟩
  intro eq
  have law := recover_argument hy (u:=x/y) rfl (v:=(x+1)/(y+1)) rfl
  have same : x/y=(x+1)/(y+1) := eq
  rw [← same,sub_self,zero_mul] at law
  exact ne ((div_eq_one_iff_eq hy.1).mp (sub_eq_zero.mp law.symm))

/-- The common ratios of two unequal field arguments and their successors determine both arguments. -/
theorem profile_injective {x y z w : F} (hx : Regular x) (hy : Regular y)
    (hw : Regular w) (ne : x≠y) (eq : profileRatios x y=profileRatios z w) : (x,y)=(z,w) := by
  let u := x/y
  let v := (x+1)/(y+1)
  have az : z/w=u := (congrArg Prod.fst eq).symm
  have bz : (z+1)/(w+1)=v := (congrArg Prod.snd eq).symm
  have a := recover_argument hy (u:=u) rfl (v:=v) rfl
  have b := recover_argument hw az bz
  have neq : u≠v := (regular_ratios hx hy ne).2.2
  have yw : y=w := mul_left_cancel₀ (sub_ne_zero.mpr neq) (a.trans b.symm)
  have xz : x=z := by
    have first : x=u*y := (div_eq_iff hy.1).mp rfl
    exact first.trans (yw ▸ ((div_eq_iff hw.1).mp az).symm)
  exact Prod.ext xz yw

/-- Wilson's inverse, valid for every pair of distinct nonzero ratios different from one. -/
theorem profile_surjective {u v : F} (u0 : u≠0) (u1 : u≠1) (v0 : v≠0) (v1 : v≠1) (ne : u≠v) :
    ∃ x y : F, Regular x ∧ Regular y ∧ x≠y ∧ profileRatios x y=(u,v) := by
  let y := (v-1)/(u-v)
  let x := u*y
  have den := sub_ne_zero.mpr ne
  have y0 : y≠0 := div_ne_zero (sub_ne_zero.mpr v1) den
  have ys : y+1=(u-1)/(u-v) := by dsimp [y]; field_simp; ring
  have y1 : y+1≠0 := ys ▸ div_ne_zero (sub_ne_zero.mpr u1) den
  have xs : x+1=v*(y+1) := by dsimp [x,y]; field_simp; ring
  refine ⟨x,y,⟨mul_ne_zero u0 y0,xs ▸ mul_ne_zero v0 y1⟩,⟨y0,y1⟩,?_,?_⟩
  · intro e
    exact u1 (mul_right_cancel₀ y0 (show u*y=1*y by simpa only [one_mul] using e))
  · exact Prod.ext ((div_eq_iff y0).mpr rfl) ((div_eq_iff y1).mpr xs)

#print axioms Regular
#print axioms profileRatios
#print axioms recover_argument
#print axioms regular_ratios
#print axioms profile_injective
#print axioms profile_surjective
end Erdos478.CyclotomicProfiles
