import Green33PrimeSingerStability
import Mathlib.Algebra.Polynomial.OfFn

/-! Recovering the lacunary identity from the missing slopes of an affine
prime-field point set. The vertical direction is kept for specialization. -/

open Finset Polynomial
open scoped Polynomial

namespace Green33PrimeAffineSlopes

variable {F : Type*} [Field F]

private abbrev Bi (F : Type*) [Field F] := Polynomial (Polynomial F)

/-- A coefficient in bidegree (i,j) vanishes above the stated total degree. -/
private def Bounded (H : Bi F) (n : ℕ) : Prop :=
  ∀ (i j : ℕ), (n < i + j) → (H.coeff i).coeff j = 0

private theorem outer_bound {H : Bi F} {n : ℕ} (h : Bounded H n) : H.natDegree≤n := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  ext j
  simpa only [coeff_zero] using h i j (by omega)

private theorem inner_bound {H : Bi F} {n : ℕ} (h : Bounded H n) (i : ℕ) :
    (H.coeff i).natDegree≤n-i := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  exact h i j (by omega)

private theorem bounded_linear {H : Bi F} {n : ℕ} (h : Bounded H n) (a b : F) :
    Bounded ((X-C (C a+X*C b))*H) (n+1) := by
  intro i j high
  rw [sub_mul,coeff_sub,coeff_sub,coeff_C_mul,add_mul,coeff_add,coeff_C_mul]
  have lo : (H.coeff i).coeff j=0 := h i j (by omega)
  have x_term : ((X*H).coeff i).coeff j=0 := by
    cases i with
    | zero => simp
    | succ i => rw [coeff_X_mul];exact h i j (by omega)
  have y_term : ((X*C b)*H.coeff i).coeff j=0 := by
    rw [mul_assoc]
    cases j with
    | zero => simp
    | succ j => rw [coeff_X_mul,coeff_C_mul,h i j (by omega),mul_zero]
  rw [lo,x_term,y_term]; ring

private theorem bounded_product {I : Type*} [DecidableEq I] (s : Finset I)
    (a b : I→F) {A : Bi F} {d : ℕ} (hA : Bounded A d) :
    Bounded ((∏ i ∈ s, (X-C (C (a i)+X*C (b i))))*A) (s.card+d) := by
  induction s using Finset.induction_on with
  | empty => simpa using hA
  | @insert i s hi ih =>
    rw [prod_insert hi,card_insert_of_notMem hi,mul_assoc]
    convert bounded_linear ih (a i) (b i) using 1
    omega

private noncomputable def specialize (H : Bi F) (s : F) : F[X] := H.map (evalRingHom s)

private theorem specialize_bound {H : Bi F} {n : ℕ} (h : Bounded H n) (s : F) :
    (specialize H s).natDegree≤n := (natDegree_map_le).trans (outer_bound h)

private theorem specialize_coeff (H : Bi F) (s : F) (i : ℕ) :
    (specialize H s).coeff i = (H.coeff i).eval s := by simp [specialize]

private theorem grid_divisor {p : ℕ} [Fact p.Prime] (P : (ZMod p)[X]) (h : ∀ x, P.eval x=0) :
    (X^p-X : (ZMod p)[X])∣P := by
  have hp : 1<p := Fact.out (p:=p.Prime) |>.one_lt
  let T := (X^p-X : (ZMod p)[X])
  have mon : T.Monic := (monic_X_pow p).sub_of_left (by simpa using hp)
  have deg : T.natDegree=p := by
    dsimp [T]; rw [natDegree_sub_eq_left_of_natDegree_lt (by simpa using hp),natDegree_X_pow]
  have no : T≠1 := by intro eq; rw [eq,natDegree_one] at deg;omega
  apply (modByMonic_eq_zero_iff_dvd mon).mp
  apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero (P %ₘ T) (f:=id) Function.injective_id
  · intro x
    have eq := congrArg (eval x) (modByMonic_add_div P T)
    simpa [T,ZMod.pow_card,h] using eq
  · simpa [ZMod.card,←deg] using natDegree_modByMonic_lt P mon no

private theorem middle_coeff {p d : ℕ} [Fact p.Prime] (P : (ZMod p)[X])
    (small : P.natDegree≤p+d) (h : ∀ x, P.eval x=0) {i : ℕ} (below : i<p) (above : d + 1 < i) :
    P.coeff i=0 := by
  by_cases zero : P=0
  · simp [zero]
  have hp := Fact.out (p:=p.Prime) |>.one_lt
  obtain ⟨Q,eq⟩ := grid_divisor P h
  have nz : (X^p-X : (ZMod p)[X])≠0 ∧ Q≠0 := mul_ne_zero_iff.mp (eq ▸ zero)
  have deg : (X^p-X : (ZMod p)[X]).natDegree=p := by
    rw [natDegree_sub_eq_left_of_natDegree_lt (by simpa using hp),natDegree_X_pow]
  rw [eq,natDegree_mul nz.1 nz.2,deg] at small
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show i≠0 by omega)
  rw [eq,sub_mul,coeff_sub,coeff_X_pow_mul',if_neg (by omega),coeff_X_mul,coeff_eq_zero_of_natDegree_lt (by omega),sub_zero]

/-- The coefficients in the middle vanish identically in the slope parameter,
because their degrees are smaller than the number of nonzero slopes. -/
private theorem zero_slope_gap {p d : ℕ} [Fact p.Prime] (H : Bi (ZMod p))
    (h : Bounded H (p+d)) (cover : ∀ s : ZMod p, s≠0 → ∀ x, (specialize H s).eval x=0)
    {i : ℕ} (below : i<p) (above : d + 1 < i) : (specialize H 0).coeff i=0 := by
  have vanish : H.coeff i=0 := by
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero (H.coeff i) (f:=(fun u : (ZMod p)ˣ => (u:ZMod p))) Units.val_injective
    · intro u
      rw [← specialize_coeff]
      exact middle_coeff _ (specialize_bound h u) (cover u u.ne_zero) below above
    · have sz := inner_bound h i
      rw [Fintype.card_units,ZMod.card]
      omega
  simp [specialize_coeff,vanish]

/-- The vertical specialization of a grid-covering polynomial is lacunary. -/
private theorem grid_decompose {p d : ℕ} [Fact p.Prime] (H : Bi (ZMod p))
    (h : Bounded H (p+d)) (cover : ∀ s : ZMod p, s≠0 → ∀ x, (specialize H s).eval x=0) :
    ∃ f g : (ZMod p)[X], f.natDegree≤d+1 ∧ g.natDegree≤d+1 ∧
      X^p*f+g=specialize H 0 := by
  let P := specialize H 0
  let T := (X^p : (ZMod p)[X])
  let f := P /ₘ T
  let g := P %ₘ T
  have hb := specialize_bound h 0
  have df : f.natDegree≤d := by
    change (P /ₘ (X^p)).natDegree≤d
    rw [natDegree_divByMonic P (monic_X_pow _),natDegree_X_pow]
    change P.natDegree≤p+d at hb
    omega
  have eq : X^p*f+g=P := (add_comm ..).trans (modByMonic_add_div P T)
  have prime := Fact.out (p:=p.Prime) |>.pos
  have nt : T≠1 := by
    intro one
    have := congrArg natDegree one
    simp [T] at this
    omega
  have dg : g.natDegree<p := by simpa [g,T] using natDegree_modByMonic_lt P (monic_X_pow p) nt
  refine ⟨f,g,by omega,natDegree_le_iff_coeff_eq_zero.mpr ?_,eq⟩
  intro i hi
  by_cases below : i<p
  · have point := congrArg (fun Q : (ZMod p)[X] => Q.coeff i) eq
    simp only [coeff_add,coeff_X_pow_mul',if_neg (show ¬ p ≤ i by omega),zero_add] at point
    exact point.trans (zero_slope_gap H h cover below hi)
  · exact coeff_eq_zero_of_natDegree_lt (by omega)

private abbrev Triangle (d : ℕ) := Σ i : Fin (d+1), Fin (d+1-i.val)

private theorem triangle_count (d : ℕ) : 2*Fintype.card (Triangle d)=(d+1)*(d+2) := by
  change 2*Fintype.card (Σ i : Fin (d+1), Fin (d+1-i.val))=_
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  have eqn : (∑ i : Fin (d+1), (d+1-i.val))+(∑ i : Fin (d+1), i.val)=(d+1)*(d+1) := by
    rw [←sum_add_distrib]
    have term (i : Fin (d+1)) : d+1-i.val+i.val=d+1 := Nat.sub_add_cancel i.isLt.le
    simp [term]
  have twice : (∑ i : Fin (d+1), i.val)*2=(d+1)*d := by
    rw [show (∑ i : Fin (d+1), i.val)=∑ i ∈ range (d+1), i from Fin.sum_univ_eq_sum_range (fun x => x) _]
    simpa using sum_range_id_mul_two (d+1)
  nlinarith only [eqn,twice]

private noncomputable def encode {d : ℕ} (w : Triangle d→F) : Bi F := by
  classical
  exact ofFn (d+1) (fun i => ofFn (d+1-i.val) (fun j => w ⟨i,j⟩))

private theorem bounded_encode {d : ℕ} (w : Triangle d→F) : Bounded (encode w) d := by
  classical
  intro i j high
  dsimp only [encode]
  by_cases hi : i<d+1
  · rw [ofFn_coeff_eq_val_of_lt _ hi,ofFn_coeff_eq_zero_of_ge _ (by simpa using (show d+1-i≤j by omega))]
  · simp [ofFn_coeff_eq_zero_of_ge _ (le_of_not_gt hi)]

private theorem encode_injective (d : ℕ) : Function.Injective (encode (F:=F) (d:=d)) := by
  classical
  intro w z h
  funext ⟨i,j⟩
  have e := congrArg (fun P : Bi F => (P.coeff i.val).coeff j.val) h
  simpa [encode,ofFn_coeff_eq_val_of_lt _ i.isLt,ofFn_coeff_eq_val_of_lt _ j.isLt] using e

private theorem interpolate {p d : ℕ} [Fact p.Prime] (E : Finset ((ZMod p)×(ZMod p)))
    (few : 2*E.card<(d+1)*(d+2)) (nonzero : ∀ z ∈ E, z.2≠0) :
    ∃ A : Bi (ZMod p), Bounded A d ∧ specialize A 0≠0 ∧
      ∀ z ∈ E, (specialize A z.2).eval z.1=0 := by
  classical
  let Test (n : ℕ) := ∃ A : Bi (ZMod p), A≠0 ∧ Bounded A n ∧ ∀ z ∈ E, (specialize A z.2).eval z.1=0
  have has : Test d := by
    let values (w : Triangle d→ZMod p) (z : E) := (specialize (encode w) z.val.2).eval z.val.1
    have fail : ¬ Function.Injective values := by
      intro inj
      have h := Fintype.card_le_of_injective _ inj
      simp only [Fintype.card_fun,Fintype.card_coe,ZMod.card] at h
      have more : E.card<Fintype.card (Triangle d) := by have := triangle_count d;omega
      exact (Nat.pow_lt_pow_right (Fact.out (p:=p.Prime)).one_lt more).not_ge h
    obtain ⟨u,v,eq,ne⟩ := Function.not_injective_iff.mp fail
    refine ⟨encode u-encode v,sub_ne_zero.mpr (fun e => ne (encode_injective d e)),?_,?_⟩
    · intro i j above
      simp only [coeff_sub,bounded_encode u i j above,bounded_encode v i j above,sub_self]
    · intro z hz
      have e := congrFun eq ⟨z,hz⟩
      change (specialize (encode u) z.2).eval z.1=(specialize (encode v) z.2).eval z.1 at e
      simpa [specialize,sub_eq_zero] using e
  have existsDegree : ∃ n, Test n := ⟨d,has⟩
  let k := Nat.find existsDegree
  obtain ⟨A,nA,bd,van⟩ := Nat.find_spec existsDegree
  have kd : k≤d := Nat.find_min' existsDegree has
  refine ⟨A,fun i j above => bd i j (show k < i+j by omega),?_,van⟩
  intro atzero
  have div : (C (X:(ZMod p)[X])) ∣ A := by
    apply (C_dvd_iff_dvd_coeff _ _).mpr
    intro i
    rw [X_dvd_iff]
    have e := congrArg (fun P : (ZMod p)[X] => P.coeff i) atzero
    rw [coeff_zero_eq_eval_zero];simpa [specialize] using e
  obtain ⟨V,eq⟩ := div
  have nv : V≠0 := by intro hv;apply nA;rw [eq,hv,mul_zero]
  have vanish (i j : ℕ) (above : k < i+j+1) : (V.coeff i).coeff j=0 := by
    have e := bd i (j+1) (show k < i+(j+1) by omega)
    simpa [eq,coeff_C_mul,coeff_X_mul] using e
  have kp : 0<k := by
    by_contra! hk
    apply nv
    ext i j
    simpa only [coeff_zero] using vanish i j (by omega)
  apply Nat.find_min existsDegree (show k-1<k by omega)
  refine ⟨V,nv,fun i j above => vanish i j (by omega),?_⟩
  intro z hz
  have e := van z hz
  rw [eq] at e
  simpa [specialize,nonzero z hz] using e

/-- Missing affine lines encoded by their intercept and nonzero slope parameter. -/
def missed {p : ℕ} [Fact p.Prime] {I : Type*} (s : Finset I) (a b : I→ZMod p) :
    Finset (ZMod p×ZMod p) :=
  univ.filter (fun z => z.2≠0 ∧ ∀ i∈s, a i+z.2*b i≠z.1)

theorem mem_missed {p : ℕ} [Fact p.Prime] {I : Type*} (s : Finset I) (a b : I→ZMod p)
    (z : ZMod p×ZMod p) :
    z∈missed s a b ↔ z.2≠0 ∧ ∀ i∈s, a i+z.2*b i≠z.1 := by simp [missed]

/-- With few missing nonzero slopes, a set of p affine points either uses
nearly every vertical coordinate or occupies one vertical line heavily.
The index set may have repeated projections in both coordinates. -/
theorem slope_stability {p d : ℕ} [Fact p.Prime] {I : Type*} [DecidableEq I]
    (s : Finset I) (a b : I→ZMod p) (size : s.card=p)
    (few : 2*(missed s a b).card<(d+1)*(d+2)) (small : 3*(d+1)<p) :
    p≤(s.image a).card+d ∨ ∃ c : ZMod p, p≤(s.filter (fun i => a i=c)).card+d := by
  obtain ⟨A,bd,nA,van⟩ := interpolate (missed s a b) few (fun z hz => (mem_filter.mp hz).2.1)
  let H := (∏ i ∈ s, (X-C (C (a i)+X*C (b i))))*A
  have prod (t : ZMod p) : specialize H t =
      (∏ i ∈ s, (X-C (a i+t*b i)))*specialize A t := by
    simp [H,specialize,Polynomial.map_prod]
    left
    apply prod_congr rfl
    intro i _
    rw [mul_comm (C (b i)) (C t)]
  have bound := bounded_product s a b bd
  rw [size] at bound
  have covers (t : ZMod p) (nt : t≠0) (x : ZMod p) : (specialize H t).eval x=0 := by
    rw [prod,eval_mul]
    by_cases hit : ∃ i∈s, a i+t*b i=x
    · obtain ⟨i,hi,e⟩ := hit
      rw [eval_prod,Finset.prod_eq_zero hi (by simp [e]),zero_mul]
    · have miss : (x,t)∈missed s a b := by
        apply mem_filter.mpr
        refine ⟨mem_univ _,nt,fun i hi bad => hit ⟨i,hi,bad⟩⟩
      rw [van _ miss,mul_zero]
  obtain ⟨f,g,df,dg,eq⟩ := grid_decompose H bound covers
  have iden : X^p*f+g=specialize A 0*(∏ i ∈ s, (X-C (a i))) := by
    rw [eq,prod];simp [mul_comm]
  have aux := specialize_bound bd 0
  rcases Green33PrimeSingerStability.coordinate_alternative s a f g (specialize A 0)
    size nA iden df dg small with first|⟨c,hc⟩
  · exact Or.inl (by omega)
  · exact Or.inr ⟨c,by omega⟩

#print axioms slope_stability

end Green33PrimeAffineSlopes
