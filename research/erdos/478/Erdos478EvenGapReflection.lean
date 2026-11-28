import Erdos478JointRootBound

/-!
# Two distinct endpoints from one even-gap root

Reflection about the midpoint preserves an even falling factorial. A
separable gap polynomial in odd characteristic has no root fixed by
this reflection.
-/

namespace Erdos478.EffectiveResolvent
open Polynomial Finset

private theorem int_reflect (r : ℕ) :
    (descPochhammer ℤ (2*r)-1).comp (C ((2*r:ℕ):ℤ)-1-X) = descPochhammer ℤ (2*r)-1 := by
  apply Polynomial.funext
  intro z
  simp only [eval_comp,eval_sub,eval_C,eval_one,eval_X]
  rw [descPochhammer_eval_eq_ascPochhammer]
  rw [show ((2*r:ℕ):ℤ)-1-z-(2*r:ℕ)+1 = -z by ring,ascPochhammer_eval_neg_eq_descPochhammer]
  rw [pow_mul]
  norm_num

theorem reflect_even_gap {K : Type*} [Field K] (r : ℕ) :
    (descPochhammer K (2*r)-1).comp (C ((2*r:ℕ):K)-1-X) = descPochhammer K (2*r)-1 := by
  have hh := congrArg (Polynomial.map (Int.castRingHom K)) (int_reflect r)
  simpa [Polynomial.map_comp,Polynomial.map_sub,descPochhammer_map,show (C (2:K) : K[X]) = 2 from map_ofNat C 2] using hh

theorem two_even_roots {K : Type*} [Field K] (htwo : (2:K) ≠ 0) (r : ℕ)
    (hs : (descPochhammer K (2*r)-1).Separable) {x : K} (hx : (descPochhammer K (2*r)-1).IsRoot x) :
    let y := ((2*r:ℕ):K)-1-x
    x ≠ y ∧ (descPochhammer K (2*r)-1).IsRoot y := by
  let f := descPochhammer K (2*r)-1
  let g : K[X] := C ((2*r:ℕ):K)-1-X
  let y := ((2*r:ℕ):K)-1-x
  have hfg : f.comp g = f := reflect_even_gap r
  have hxy : f.eval x = 0 := hx
  have hg : g.eval x = y := by simp [g,y]
  refine ⟨?_,?_⟩
  · intro e
    change x=y at e
    have hh := congrArg (fun q : K[X] => q.derivative.eval x) hfg
    simp only [derivative_comp,eval_mul,eval_comp,hg,← e] at hh
    have hg' : g.derivative.eval x = -1 := by simp [g]
    rw [hg'] at hh
    have hz : f.derivative.eval x = 0 := (mul_eq_zero.mp
      (show (2:K) * f.derivative.eval x = 0 by linear_combination -hh)).resolve_left htwo
    obtain ⟨a,b,hab⟩ := hs
    have he := congrArg (Polynomial.eval x) hab
    change eval x (a*f+b*f.derivative) = eval x 1 at he
    simp [hxy,hz] at he
  · change f.eval y = 0
    rw [← hg,← eval_comp,hfg,hxy]

#print axioms two_even_roots

end Erdos478.EffectiveResolvent
