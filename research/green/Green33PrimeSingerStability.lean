import Mathlib.RingTheory.Polynomial.Wronskian
import Mathlib.FieldTheory.Finite.Polynomial
import Mathlib.Tactic

/-! The lacunary polynomial step in prime-order Singer layer stability.
The prime-plane argument follows Szőnyi and Weiner, *A stability theorem for
lines in Galois planes of prime order*, Theorem 2.4. -/

open Finset Polynomial
open scoped Polynomial

namespace Green33PrimeSingerStability

/-- A polynomial vanishing at every listed root supplies the factor lost by
differentiating their product, including when the list repeats roots. -/
private theorem derivative_multiple {F I : Type*} [Field F] [DecidableEq I]
    (s : Finset I) (a : I→F) (T : F[X]) (vanish : ∀ i ∈ s, T.IsRoot (a i)) :
    (∏ i ∈ s, (X-C (a i))) ∣ T*derivative (∏ i ∈ s, (X-C (a i))) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    let R := ∏ j ∈ s, (X-C (a j))
    let L := X-C (a i)
    have one : L ∣ T := dvd_iff_isRoot.mpr (vanish i (mem_insert_self _ _))
    have rest := ih (fun j hj => vanish j (mem_insert_of_mem hj))
    rw [prod_insert hi]
    change L*R ∣ T*derivative (L*R)
    have e : derivative L=1 := by simp [L]
    rw [derivative_mul,e,one_mul]
    have h₁ : L*R ∣ T*R := mul_dvd_mul_right one R
    have h₂ : L*R ∣ L*(T*derivative R) := mul_dvd_mul_left _ rest
    convert dvd_add h₁ h₂ using 1
    ring

/-- The split factor of a low-degree perturbation of a Frobenius multiple
divides the product used in the prime-plane stability argument. -/
theorem lacunary_divisor {p : ℕ} [Fact p.Prime] {I : Type*} [DecidableEq I]
    (s : Finset I) (a : I→ZMod p) (f g A : (ZMod p)[X])
    (factorization : X^p*f+g=A*(∏ i ∈ s, (X-C (a i)))) :
    (∏ i ∈ s, (X-C (a i))) ∣ (X*f+g)*wronskian f g := by
  let R := ∏ i ∈ s, (X-C (a i))
  let T : (ZMod p)[X] := X^p-X
  let H := X^p*f+g
  have ht (i : I) : T.IsRoot (a i) := by simp [T,IsRoot,ZMod.pow_card]
  have dr : R∣T*derivative R := derivative_multiple s a T (fun i _ => ht i)
  have he : H=A*R := factorization
  have hh : R ∣ H := he ▸ dvd_mul_left _ _
  have hd : R ∣ T*derivative H := by
    rw [he,derivative_mul]
    convert dvd_add (dvd_mul_left R (T*derivative A)) (dr.mul_left A) using 1
    ring
  have w : wronskian f g=f*derivative H-derivative f*H := by
    simp [H,wronskian,derivative_X_pow]; ring
  have tw : R ∣ T*wronskian f g := by
    rw [w]
    convert dvd_sub (hd.mul_left f) (hh.mul_left (T*derivative f)) using 1
    ring
  change R ∣ (X*f+g)*wronskian f g
  convert dvd_sub (hh.mul_right (wronskian f g)) (tw.mul_left f) using 1
  dsimp [H,T];ring

#print axioms lacunary_divisor

/-- A split factor larger than three times the residual degree forces one
of the two degenerate cases of the lacunary identity. -/
theorem degree_alternative {p : ℕ} [Fact p.Prime] {I : Type*} [DecidableEq I]
    (s : Finset I) (a : I→ZMod p) (f g A : (ZMod p)[X])
    (factorization : X^p*f+g=A*(∏ i ∈ s, (X-C (a i)))) {d : ℕ}
    (df : f.natDegree≤d) (dg : g.natDegree≤d) (large : 3*d<s.card) :
    X*f+g=0 ∨ wronskian f g=0 := by
  by_contra! nonzero
  have divides := lacunary_divisor s a f g A factorization
  have order := natDegree_le_of_dvd divides (mul_ne_zero nonzero.1 nonzero.2)
  have roots : (∏ i ∈ s, (X-C (a i))).natDegree=s.card := by
    rw [natDegree_prod_of_monic (h:=fun i _ => monic_X_sub_C (a i))]
    simp
  rw [roots] at order
  have w := natDegree_wronskian_lt_add nonzero.2
  have x : (X*f).natDegree ≤ (X:(ZMod p)[X]).natDegree+f.natDegree := natDegree_mul_le
  rw [natDegree_X] at x
  have add := natDegree_add_le (X*f) g
  have prod : ((X*f+g)*wronskian f g).natDegree ≤ (X*f+g).natDegree+(wronskian f g).natDegree := natDegree_mul_le
  omega

#print axioms degree_alternative

private theorem constant_of_derivative {p : ℕ} [Fact p.Prime] (f : (ZMod p)[X])
    (small : f.natDegree<p) (zero : derivative f=0) : f=C (f.coeff 0) := by
  ext n
  cases n with
  | zero => simp
  | succ n =>
    rw [coeff_C_succ]
    by_cases h : n+1≤f.natDegree
    · have nz : ((n+1:ℕ):ZMod p)≠0 := by
        rw [ne_eq,ZMod.natCast_eq_zero_iff]
        exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
      have deriv := congrArg (fun P : (ZMod p)[X] => P.coeff n) zero
      simp only [coeff_derivative,coeff_zero] at deriv
      exact (mul_eq_zero.mp deriv).resolve_right (by exact_mod_cast nz)
    · exact coeff_eq_zero_of_natDegree_lt (by omega)

/-- In degrees below the prime, a vanishing Wronskian forces proportionality. -/
theorem proportional {p : ℕ} [Fact p.Prime] (f g : (ZMod p)[X]) (nf : f≠0)
    (df : f.natDegree<p) (dg : g.natDegree<p) (zero : wronskian f g=0) :
    ∃ c : ZMod p, g=C c*f := by
  by_cases ng : g=0
  · exact ⟨0,by simp [ng]⟩
  let t := GCDMonoid.gcd f g
  let u := f/t
  let v := g/t
  have nt : t≠0 := gcd_ne_zero_of_right ng
  have hu : t*u=f := EuclideanDomain.mul_div_cancel' nt (gcd_dvd_left f g)
  have hv : t*v=g := EuclideanDomain.mul_div_cancel' nt (gcd_dvd_right f g)
  have cop : IsCoprime u v := isCoprime_div_gcd_div_gcd ng
  have w : t^2*wronskian u v=0 := by
    rw [←hu,←hv] at zero
    calc _ = wronskian (t*u) (t*v) := by simp only [wronskian,derivative_mul];ring
         _ = 0 := zero
  have deriv := cop.wronskian_eq_zero_iff.mp ((mul_eq_zero.mp w).resolve_left (pow_ne_zero _ nt))
  have cu := constant_of_derivative u ((natDegree_le_of_dvd ⟨t,hu.symm.trans (mul_comm _ _)⟩ nf).trans_lt df) deriv.1
  have cv := constant_of_derivative v ((natDegree_le_of_dvd ⟨t,hv.symm.trans (mul_comm _ _)⟩ ng).trans_lt dg) deriv.2
  have cne : u.coeff 0 ≠0 := by
    intro he
    apply nf
    rw [← hu,cu,he,map_zero,mul_zero]
  refine ⟨v.coeff 0 / u.coeff 0,?_⟩
  calc
    g = t*C (v.coeff 0) := by simpa only [←cv] using hv.symm
    _ = C (v.coeff 0/u.coeff 0)*(t*C (u.coeff 0)) := by
      rw [mul_left_comm,←C_mul,div_mul_cancel₀ _ cne]
    _ = _ := by rw [←cu,hu]

#print axioms proportional

private theorem multiplicity_product {F I : Type*} [Field F] [DecidableEq F] [DecidableEq I]
    (s : Finset I) (a : I→F) (c : F) :
    (∏ i ∈ s, (X-C (a i))).rootMultiplicity c=(s.filter (fun i => a i=c)).card := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [prod_insert hi,rootMultiplicity_mul (mul_ne_zero (X_sub_C_ne_zero _)
      (Finset.prod_ne_zero_iff.mpr (fun j _ => X_sub_C_ne_zero _))),rootMultiplicity_X_sub_C,ih]
    by_cases h : a i=c
    · simp [h,Finset.filter_insert,hi,Nat.add_comm]
    · simp [h,Ne.symm h,Finset.filter_insert]

/-- On a chart with p points, either almost all coordinates occur or a single
coordinate occurs at least p minus the degree of the auxiliary polynomial. -/
theorem coordinate_alternative {p : ℕ} [Fact p.Prime] {I : Type*} [DecidableEq I]
    (s : Finset I) (a : I→ZMod p) (f g A : (ZMod p)[X]) (size : s.card=p) (nA : A≠0)
    (factorization : X^p*f+g=A*(∏ i ∈ s, (X-C (a i)))) {d : ℕ}
    (df : f.natDegree≤d) (dg : g.natDegree≤d) (small : 3*d<p) :
    p≤(s.image a).card+A.natDegree ∨ ∃ c : ZMod p, p≤(s.filter (fun i => a i=c)).card+A.natDegree := by
  classical
  let R := ∏ i ∈ s, (X-C (a i))
  have nR : R≠0 := Finset.prod_ne_zero_iff.mpr (fun _ _ => X_sub_C_ne_zero _)
  have degreeR : R.natDegree=p := by
    dsimp only [R];rw [natDegree_prod_of_monic (h:=fun i _ => monic_X_sub_C (a i))];simp [size]
  have nf : f≠0 := by
    intro z
    rw [z,mul_zero,zero_add] at factorization
    change g=A*R at factorization
    rw [factorization,natDegree_mul nA nR,degreeR] at dg
    omega
  rcases degree_alternative s a f g A factorization df dg (by omega) with first|second
  · left
    have sub : (univ:Finset (ZMod p))⊆s.image a ∪ A.roots.toFinset := by
      intro z _
      have top := congrArg (eval z) factorization
      have vanish := congrArg (eval z) first
      simp only [eval_add,eval_mul,eval_pow,eval_X,ZMod.pow_card,eval_zero] at top vanish
      rw [vanish] at top
      rcases mul_eq_zero.mp top.symm with za|zr
      · exact mem_union_right _ (by simpa [mem_roots nA,IsRoot] using za)
      · rw [eval_prod,Finset.prod_eq_zero_iff] at zr
        obtain ⟨i,hi,eq⟩ := zr
        exact mem_union_left _ (mem_image.mpr ⟨i,hi,(sub_eq_zero.mp (by simpa using eq)).symm⟩)
    have bound := (card_le_card sub).trans (card_union_le _ _)
    rw [card_univ,ZMod.card] at bound
    exact bound.trans (Nat.add_le_add_left (A.roots.toFinset_card_le.trans A.card_roots') _)
  · obtain ⟨c,eq⟩ := proportional f g nf (by omega) (by omega) second
    refine Or.inr ⟨-c,?_⟩
    have frob : (X-C (-c))^p = (X^p+C c : (ZMod p)[X]) := by
      rw [map_neg,sub_neg_eq_add,add_pow_char,← C_pow,ZMod.pow_card]
    have dvd : (X-C (-c))^p∣A*R := by
      rw [frob];refine ⟨f,?_⟩
      change A*(∏ i ∈ s, (X-C (a i)))=_
      rw [←factorization,eq,add_mul]
    have m := (le_rootMultiplicity_iff (mul_ne_zero nA nR)).mpr dvd
    rw [rootMultiplicity_mul (mul_ne_zero nA nR)] at m
    change p≤A.rootMultiplicity (-c)+(∏ i ∈ s, (X-C (a i))).rootMultiplicity (-c) at m
    rw [multiplicity_product] at m
    have cap : A.rootMultiplicity (-c)≤A.natDegree := by
      rw [←count_roots]
      exact (Multiset.count_le_card ..).trans A.card_roots'
    omega

#print axioms coordinate_alternative

end Green33PrimeSingerStability
