import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.Norm.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Tactic

/-! The elementary Stepanov auxiliary polynomial for quadratic characters in prime fields.
The two coefficient blocks use disjoint orders of vanishing at an odd-order root. -/

open Finset Polynomial
open scoped BigOperators Polynomial

namespace Green33PrimeQuarticCharacter

variable {K : Type*} [Field K]

private abbrev Indices (I J : ℕ) := Fin J × Fin I
private def exponent {I J : ℕ} (p : ℕ) (t : Indices I J) := t.1.val*p+t.2.val

private theorem residue {I J p : ℕ} (width : I≤p) (z : Indices I J) :
    exponent p z%p=z.2.val := by
  simp [exponent,Nat.add_mod,Nat.mod_eq_of_lt (z.2.isLt.trans_le width)]

private theorem exponent_injective {I J p : ℕ} (width : I≤p) (pos : 0<p) :
    Function.Injective (exponent (I:=I) (J:=J) p) := by
  intro a b eq
  have same := congrArg (·%p) eq
  rw [residue width,residue width] at same
  have first : a.1.val*p=b.1.val*p := by
    unfold exponent at eq
    omega
  exact Prod.ext (Fin.ext (Nat.eq_of_mul_eq_mul_right pos first)) (Fin.ext same)

private noncomputable def block {I J : ℕ} (p : ℕ) (w : Indices I J→K) : K[X] :=
  ∑ t, monomial (exponent p t) (w t)

private theorem block_coeff {I J p : ℕ} (width : I≤p) (pos : 0<p) (w : Indices I J→K)
    (t : Indices I J) : (block p w).coeff (exponent p t)=w t := by
  classical
  simp only [block,finsetSum_coeff,coeff_monomial,(exponent_injective width pos).eq_iff]
  simp

private theorem block_trailing {I J p : ℕ} (width : I≤p) (w : Indices I J→K)
    (nw : block p w≠0) : (block p w).natTrailingDegree%p<I := by
  classical
  let e := (block p w).natTrailingDegree
  have nz := coeff_natTrailingDegree_ne_zero.mpr nw
  by_contra! bad
  apply nz
  change (block p w).coeff e=0
  simp only [block,finsetSum_coeff,coeff_monomial]
  apply sum_eq_zero
  intro t _
  rw [if_neg]
  intro eq
  have r := residue width t
  rw [eq] at r
  change I≤e%p at bad
  omega

private theorem order_power (f : K[X]) (nz : f≠0) (n : ℕ) :
    (f^n).natTrailingDegree=n*f.natTrailingDegree := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ,natTrailingDegree_mul (pow_ne_zero n nz) nz,ih,Nat.succ_mul]

/-- If the orders of the two blocks are separated modulo the characteristic,
their combination can vanish only when both coefficient tables vanish. -/
private theorem auxiliary_independent {I J p n : ℕ} (width : I≤p) (pos : 0<p)
    (f : K[X]) (nf : f≠0)
    (gap : I≤(n*f.natTrailingDegree)%p)
    (room : (n*f.natTrailingDegree)%p+I≤p) (u v : Indices I J→K)
    (eq : block p u+f^n*block p v=0) : u=0 ∧ v=0 := by
  classical
  have vanish : block p v=0 := by
    by_contra vn
    have nn := mul_ne_zero (pow_ne_zero n nf) vn
    have rel : block p u=-(f^n*block p v) := eq_neg_of_add_eq_zero_left eq
    have un : block p u≠0 := rel ▸ neg_ne_zero.mpr nn
    have a := block_trailing width u un
    have b := block_trailing width v vn
    rw [rel,natTrailingDegree_neg,natTrailingDegree_mul (pow_ne_zero n nf) vn,order_power f nf] at a
    rw [Nat.add_mod,Nat.mod_eq_of_lt (by omega)] at a
    omega
  have zero : block p u=0 := by simpa only [vanish,mul_zero,add_zero] using eq
  constructor
  · funext t
    rw [←block_coeff width pos u t,zero];rfl
  · funext t
    rw [←block_coeff width pos v t,vanish];rfl

private noncomputable def jet (f : K[X]) (n : ℕ) (g : K[X]) : ℕ→K[X]
  | 0 => g
  | k+1 => f*derivative (jet f n g k)+C ((n:K)-k)*derivative f*(jet f n g k)

private theorem differentiated_power (f : K[X]) (n : ℕ) :
    f*derivative (f^n)=C (n:K)*derivative f*f^n := by
  cases n with
  | zero => simp
  | succ n => rw [derivative_pow_succ,pow_succ];push_cast;ring

private theorem jet_formula (f g : K[X]) (n k : ℕ) :
    f^k*derivative^[k] (f^n*g)=f^n*jet f n g k := by
  induction k with
  | zero => simp [jet]
  | succ k ih =>
    have delta := congrArg (fun z : K[X] => derivative z) ih
    rw [derivative_mul,derivative_mul] at delta
    rw [Function.iterate_succ_apply',jet,pow_succ,C_sub]
    linear_combination f*delta - (derivative^[k] (f^n*g))*differentiated_power f k +
      (jet f n g k)*differentiated_power f n - C (k:K)*derivative f*ih

private theorem jet_degree (f g : K[X]) (n k : ℕ) :
    (jet f n g k).natDegree≤g.natDegree+k*f.natDegree := by
  induction k with
  | zero => simp [jet]
  | succ k ih =>
    rw [jet]
    apply natDegree_add_le_of_degree_le
    · have bound := natDegree_mul_le (p:=f) (q:=derivative (jet f n g k))
      have der := (natDegree_derivative_le (jet f n g k)).trans (Nat.sub_le _ _)
      nlinarith only [bound,der,ih]
    · have bound := natDegree_mul_le (p:=C ((n:K)-k)*derivative f) (q:=jet f n g k)
      have der := (natDegree_derivative_le f).trans (Nat.sub_le _ _)
      have cf := natDegree_C_mul_le ((n:K)-k) (derivative f)
      nlinarith only [bound,cf,der,ih]

private noncomputable def probe {I J : ℕ} (f : K[X]) (c : K) (n k : ℕ)
    (w : Indices I J→K) : K[X] :=
  ∑ t, C (w t)*(X+C c)^t.1.val*jet f n (X^t.2.val) k

private theorem probe_degree {I J : ℕ} (f : K[X]) (c : K) (n k : ℕ) (w : Indices I J→K) :
    (probe f c n k w).natDegree ≤ I+J+k*f.natDegree := by
  apply natDegree_sum_le_of_forall_le
  intro t _
  have h := natDegree_mul_le (p:=C (w t)*(X+C c)^t.1.val) (q:=jet f n (X^t.2.val) k)
  have cf := natDegree_C_mul_le (w t) ((X+C c)^t.1.val)
  have deg : ((X+C c)^t.1.val).natDegree≤t.1.val := by
    rw [natDegree_pow,natDegree_X_add_C,mul_one]
  have jet_bound := jet_degree f (X^t.2.val) n k
  rw [natDegree_X_pow] at jet_bound
  have i := t.2.isLt
  have j := t.1.isLt
  omega

private theorem inert {a : K[X]} (flat : derivative a=0) (b : K[X]) (k : ℕ) :
    derivative^[k] (a*b)=a*derivative^[k] b := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [Function.iterate_succ_apply',ih,derivative_mul,flat,zero_mul,zero_add]

private theorem block_eval {I J p : ℕ} [CharP K p] (f : K[X]) (c x : K) (fr : x^p=x+c)
    (n k : ℕ) (w : Indices I J→K) :
    f.eval x^k*(derivative^[k] (f^n*block p w)).eval x =
      f.eval x^n*(probe f c n k w).eval x := by
  classical
  have decomp : f^n*block p w =
      ∑ t, (C (w t)*X^(t.1.val*p))*(f^n*X^t.2.val) := by
    unfold block
    rw [mul_sum]
    apply sum_congr rfl
    intro t _
    rw [← C_mul_X_pow_eq_monomial,exponent,pow_add];ring
  rw [decomp,iterate_derivative_sum,eval_finsetSum,probe,eval_finsetSum,mul_sum,mul_sum]
  apply sum_congr rfl
  intro t _
  have flat : derivative (C (w t)*X^(t.1.val*p) : K[X])=0 := by
    simp [derivative_mul,derivative_X_pow]
  have v := congrArg (fun z : K[X] => z.eval x) (jet_formula f (X^t.2.val) n k)
  simp only [eval_mul,eval_pow] at v
  rw [inert flat]
  simp only [eval_mul,eval_C,eval_pow,eval_X,eval_add]
  rw [Nat.mul_comm t.1.val p,pow_mul,fr]
  linear_combination w t*(x+c)^t.1.val*v

private theorem probe_sub {I J : ℕ} (f : K[X]) (c : K) (n k : ℕ) (w z : Indices I J→K) :
    probe f c n k (w-z)=probe f c n k w-probe f c n k z := by
  simp only [probe,Pi.sub_apply,C_sub,sub_mul,sum_sub_distrib]

private theorem vanishing_tables [Fintype K] {I J r : ℕ} (f : K[X]) (c : K) (n : ℕ)
    (more : r*(I+J+r*f.natDegree+1)<2*(J*I)) :
    ∃ u v : Indices I J→K, (u≠0 ∨ v≠0) ∧
      ∀ k<r, probe f c 0 k u+probe f c n k v=0 := by
  classical
  let W := Indices I J→K
  let N := I+J+r*f.natDegree+1
  let values (w : W×W) (t : Fin r×Fin N) :=
    (probe f c 0 t.1.val w.1+probe f c n t.1.val w.2).coeff t.2.val
  have fail : ¬Function.Injective values := by
    intro inj
    have cap := Fintype.card_le_of_injective _ inj
    simp only [W,Indices,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,← Nat.pow_add] at cap
    have strict := Nat.pow_lt_pow_right (Fintype.one_lt_card (α:=K)) more
    dsimp only [N] at cap
    rw [two_mul] at strict
    exact strict.not_ge cap
  obtain ⟨a,b,eq,ne⟩ := Function.not_injective_iff.mp fail
  refine ⟨a.1-b.1,a.2-b.2,?_,?_⟩
  · by_contra! nn
    exact ne (Prod.ext (sub_eq_zero.mp nn.1) (sub_eq_zero.mp nn.2))
  · intro k kr
    rw [probe_sub,probe_sub]
    have same : probe f c 0 k a.1+probe f c n k a.2=probe f c 0 k b.1+probe f c n k b.2 := by
      ext i
      by_cases hi : i<N
      · exact congrFun eq (⟨k,kr⟩,⟨i,hi⟩)
      · have lim (w : W×W) : (probe f c 0 k w.1+probe f c n k w.2).natDegree < i := by
          apply lt_of_le_of_lt (natDegree_add_le_of_degree_le (probe_degree ..) (probe_degree ..))
          have grow := Nat.mul_le_mul_right f.natDegree kr.le
          dsimp [N] at hi
          omega
        rw [coeff_eq_zero_of_natDegree_lt (lim a),coeff_eq_zero_of_natDegree_lt (lim b)]
    linear_combination same

private theorem block_degree {I J p : ℕ} (w : Indices I J→K) :
    (block p w).natDegree≤J*p+I := by
  apply natDegree_sum_le_of_forall_le
  intro t _
  apply (natDegree_monomial_le _).trans
  exact Nat.add_le_add (Nat.mul_le_mul_right p t.1.isLt.le) t.2.isLt.le

/-- A Stepanov bound for a translated prime field. The input set consists of
points on which the Frobenius and power tests both have their prescribed values. -/
theorem stepanov_bound [Fintype K] {p : ℕ} [Fact p.Prime] [CharP K p]
    {I J r n : ℕ} (f : K[X]) (nf : f≠0) (c : K)
    (points : Finset K) (test : ∀ x∈points, x^p=x+c ∧ f.eval x≠0 ∧ f.eval x^n=1)
    (width : I≤p) (rpos : 0<r) (small : r≤p)
    (gap : I≤(n*f.natTrailingDegree)%p) (room : (n*f.natTrailingDegree)%p+I≤p)
    (more : r*(I+J+r*f.natDegree+1)<2*(J*I)) :
    r*points.card≤J*p+I+n*f.natDegree := by
  classical
  obtain ⟨u,v,nz,vanish⟩ := vanishing_tables f c n more
  let H := block p u+f^n*block p v
  have nonzero : H≠0 := by
    intro zero
    have both := auxiliary_independent width (Fact.out (p:=p.Prime)).pos f nf gap room u v zero
    exact nz.elim (· both.1) (· both.2)
  have degree : H.natDegree≤J*p+I+n*f.natDegree := by
    apply natDegree_add_le_of_degree_le ((block_degree u).trans (by omega))
    have mul := natDegree_mul_le (p:=f^n) (q:=block p v)
    have power := natDegree_pow_le (p:=f) (n:=n)
    have deg := block_degree (p:=p) v
    omega
  have many (x : K) (hx : x∈points) : r≤H.rootMultiplicity x := by
    obtain ⟨fr,fzero,good⟩ := test x hx
    have root (k : ℕ) (kr : k<r) : (derivative^[k] H).IsRoot x := by
      have ua := block_eval (p:=p) f c x fr 0 k u
      have vb := block_eval (p:=p) f c x fr n k v
      have eq := congrArg (fun P : K[X] => P.eval x) (vanish k kr)
      simp only [pow_zero,one_mul] at ua
      rw [good,one_mul] at vb
      simp only [eval_add,eval_zero] at eq
      change (derivative^[k] (block p u+f^n*block p v)).eval x=0
      rw [iterate_map_add derivative,eval_add]
      apply (mul_eq_zero.mp (show f.eval x^k*((derivative^[k] (block p u)).eval x+
        (derivative^[k] (f^n*block p v)).eval x)=0 by rw [mul_add,ua,vb,eq])).resolve_left (pow_ne_zero k fzero)
    have mult := lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivisors'
      (n:=r-1) nonzero (fun k hk => root k (by omega)) (fun k hk kn => by
        apply mem_nonZeroDivisors_iff_ne_zero.mpr
        exact fun z => (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero kn) (by omega : k<p))
          ((CharP.cast_eq_zero_iff K p k).mp z))
    omega
  calc r*points.card = ∑ _ ∈ points,r := by simp [Nat.mul_comm]
       _ ≤ ∑ x ∈ points,H.roots.count x := sum_le_sum fun x hx => by rw [count_roots];exact many x hx
       _ ≤ ∑ x : K,H.roots.count x := sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
       _ = H.roots.card := Multiset.sum_count_eq_card (fun _ _ => mem_univ _)
       _ ≤ _ := (card_roots' H).trans degree

#print axioms stepanov_bound

private theorem quartic_count [Fintype K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (f : K[X]) (nf : f≠0) (degree : f.natDegree≤4)
    (order : Odd f.natTrailingDegree) (big : 400≤p) (c : K)
    (points : Finset K) (card : points.card≤p)
    (test : ∀ x∈points, x^p=x+c ∧ f.eval x≠0 ∧ f.eval x^(p/2)=1) :
    2*points.card≤p+80*(p.sqrt+1) := by
  let j := p.sqrt/10
  let i := 20*j^2
  let r := 2*j-1
  let n := p/2
  have large : 20≤p.sqrt := Nat.le_sqrt.mpr big
  have jpos : 2≤j := by dsimp [j];omega
  have jp : 10*j≤p.sqrt := by dsimp [j];omega
  have bound : 100*j^2≤p := by nlinarith only [Nat.mul_le_mul jp jp,Nat.sqrt_le' p]
  have iw : 5*i≤p := by dsimp [i];omega
  have rrel : r+1=2*j := by dsimp [r];omega
  have rsmall : r≤p := by nlinarith only [bound,rrel,Nat.mul_le_mul_left j jpos]
  have two : 2*n+1=p := by
    have odd := (Fact.out (p:=p.Prime)).odd_of_ne_two (by omega)
    obtain ⟨k,hk⟩ := odd
    dsimp [n];omega
  have mt : f.natTrailingDegree≤4 := (natTrailingDegree_le_natDegree f).trans degree
  have classes : f.natTrailingDegree=1 ∨ f.natTrailingDegree=3 := by
    obtain ⟨a,ha⟩ := order
    omega
  have split : (n*f.natTrailingDegree)%p=n ∨ (n*f.natTrailingDegree)%p=n-1 := by
    rcases classes with e|e
    · left; rw [e,mul_one,Nat.mod_eq_of_lt (by omega)]
    · right
      rw [e,show n*3=p+(n-1) by omega,Nat.add_mod_left,Nat.mod_eq_of_lt (by omega)]
  have more : r*(i+j+r*f.natDegree+1)<2*(j*i) := by
    have rd := Nat.mul_le_mul (show r≤2*j by omega) degree
    have cross := Nat.mul_le_mul (show r≤2*j by omega) (show j+r*f.natDegree+1≤9*j+1 by omega)
    have cancel := congrArg (·*i) rrel
    have lower : j^2≥2*j := by simpa only [pow_two] using Nat.mul_le_mul_right j jpos
    change r*(20*j^2+j+r*f.natDegree+1)<2*(j*(20*j^2))
    dsimp [i] at cancel
    nlinarith only [cross,cancel,lower,jpos]
  have raw := stepanov_bound (n:=n) (I:=i) (J:=j) (r:=r) f nf c points test (by omega)
    (by omega) rsmall (by rcases split with a|a <;> omega)
    (by rcases split with a|a <;> omega) more
  have nd := Nat.mul_le_mul_left n degree
  have align := congrArg (·*points.card) rrel
  have upper : p.sqrt+1≤20*j := by dsimp [j];omega
  have close := Nat.mul_le_mul_right (p.sqrt+1) upper
  have sq := Nat.lt_succ_sqrt' p
  have final : j*(2*points.card)≤j*(p+80*(p.sqrt+1)) := by
    nlinarith only [raw,nd,align,card,iw,two,close,sq]
  exact Nat.le_of_mul_le_mul_left final (by omega)

section PrimeValues

variable {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [Fintype K]
variable [Algebra (ZMod p) K] [CharP K p]

private theorem positive_values (g : (ZMod p)[X]) (deg : g.natDegree≤4) (a : K)
    (odd : Odd ((g.map (algebraMap (ZMod p) K)).rootMultiplicity a)) (big : 400≤p) :
    2*(univ.filter (fun x : ZMod p => quadraticChar (ZMod p) (g.eval x)=1)).card≤
      p+80*(p.sqrt+1) := by
  classical
  let φ := algebraMap (ZMod p) K
  let f := (g.map φ).comp (X+C a)
  have mult : (g.map φ).rootMultiplicity a=f.natTrailingDegree := rootMultiplicity_eq_natTrailingDegree
  have order : Odd f.natTrailingDegree := mult ▸ odd
  have nf : f≠0 := by rintro e;rw [e,natTrailingDegree_zero] at order;exact Nat.not_odd_zero order
  have degree : f.natDegree≤4 := by
    have le := natDegree_comp_le (p:=g.map φ) (q:=X+C a)
    rw [natDegree_X_add_C,mul_one] at le
    exact le.trans (natDegree_map_le.trans deg)
  let S := univ.filter (fun x : ZMod p => quadraticChar (ZMod p) (g.eval x)=1)
  let P := S.image (fun x => φ x-a)
  have same : P.card=S.card := card_image_of_injective _ (fun _ _ e => φ.injective (sub_left_inj.mp e))
  have size : P.card≤p := same.trans_le ((card_le_univ S).trans_eq (ZMod.card p))
  have fld : ringChar (ZMod p)≠2 := by rw [ringChar.eq (ZMod p) p];omega
  have tests (y : K) (hy : y∈P) : y^p=y+(a-a^p) ∧ f.eval y≠0 ∧ f.eval y^(p/2)=1 := by
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hy
    have gp : quadraticChar (ZMod p) (g.eval x)=1 := (mem_filter.mp hx).2
    have eq : f.eval (φ x-a)=φ (g.eval x) := by simp [f,eval_comp]
    rw [eq]
    have nz : g.eval x≠0 := by intro zero;simp [zero] at gp
    have fr : x^p=x := by simp
    have square := (quadraticChar_one_iff_isSquare nz).mp gp
    have one := (FiniteField.isSquare_iff fld nz).mp square
    rw [ZMod.card] at one
    refine ⟨?_,(map_ne_zero φ).mpr nz,?_⟩
    · rw [sub_pow_char,←map_pow,fr];ring
    · rw [←map_pow,one,map_one]
  have h := quartic_count f nf degree order big (a-a^p) P size tests
  rwa [same] at h

/-- An elementary uniform square-root bound on complete quadratic character sums
of degree at most four. The odd-multiplicity zero may lie in any finite extension. -/
theorem quartic_character_sum (g : (ZMod p)[X]) (deg : g.natDegree≤4) (a : K)
    (odd : Odd ((g.map (algebraMap (ZMod p) K)).rootMultiplicity a)) (big : 400≤p) :
    |∑ x : ZMod p, quadraticChar (ZMod p) (g.eval x)|≤80*((p.sqrt:ℤ)+1)+4 := by
  classical
  let χ := quadraticChar (ZMod p)
  let P := univ.filter (fun x : ZMod p => χ (g.eval x)=1)
  let M := univ.filter (fun x : ZMod p => χ (g.eval x)= -1)
  let Z := univ.filter (fun x : ZMod p => g.eval x=0)
  have positive : 2*P.card≤p+80*(p.sqrt+1) := positive_values g deg a odd big
  have fld : ringChar (ZMod p)≠2 := by rw [ringChar.eq (ZMod p) p];omega
  obtain ⟨u,neg⟩ := quadraticChar_exists_neg_one' fld
  let t := C (u:ZMod p)*g
  have mt : ((t.map (algebraMap (ZMod p) K)).rootMultiplicity a)=
      ((g.map (algebraMap (ZMod p) K)).rootMultiplicity a) := by
    have nf : g.map (algebraMap (ZMod p) K) ≠ 0 := by
      intro e;rw [e,rootMultiplicity_zero] at odd;exact Nat.not_odd_zero odd
    simp only [t,Polynomial.map_mul,map_C]
    rw [rootMultiplicity_mul (mul_ne_zero (C_ne_zero.mpr ((map_ne_zero (algebraMap (ZMod p) K)).mpr u.ne_zero)) nf),rootMultiplicity_C,zero_add]
  have twist := positive_values t ((natDegree_C_mul_le ..).trans deg) a (mt.symm ▸ odd) big
  have sets : univ.filter (fun x : ZMod p => quadraticChar (ZMod p) (t.eval x)=1)=M := by
    ext x
    simp only [M,t,χ,mem_filter,mem_univ,true_and,eval_mul,eval_C,map_mul,neg,neg_one_mul]
    omega
  rw [sets] at twist
  have gn : g≠0 := by
    rintro rfl;simp at odd
  have zeros : Z.card≤4 := by
    have cap : Z⊆g.roots.toFinset := by
      intro x hx
      exact Multiset.mem_toFinset.mpr ((mem_roots gn).mpr (mem_filter.mp hx).2)
    exact (card_le_card cap).trans (g.roots.toFinset_card_le.trans ((card_roots' g).trans deg))
  have parts (x : ZMod p) :
      (if χ (g.eval x)=1 then (1:ℤ) else 0)+(if χ (g.eval x)= -1 then 1 else 0)+
      (if g.eval x=0 then 1 else 0)=1 ∧
      χ (g.eval x)=(if χ (g.eval x)=1 then 1 else 0)-(if χ (g.eval x)= -1 then 1 else 0) := by
    by_cases z : g.eval x=0
    · simp [z,χ]
    · rcases quadraticChar_dichotomy z with h|h <;> simp [χ,h,z]
  have mass := sum_congr (s₁:=univ) rfl (fun x _ => (parts x).1)
  have values := sum_congr (s₁:=univ) rfl (fun x _ => (parts x).2)
  simp only [sum_add_distrib,sum_sub_distrib,sum_boole,sum_const,card_univ,ZMod.card,nsmul_eq_mul,mul_one] at mass values
  change (P.card:ℤ)+M.card+Z.card=p at mass
  change (∑ x : ZMod p,χ (g.eval x))=(P.card:ℤ)-M.card at values
  change |∑ x : ZMod p, χ (g.eval x)|≤_
  rw [values,abs_le]
  omega

#print axioms quartic_character_sum
end PrimeValues

private theorem square_factor {F E : Type*} [Field F] [PerfectField F] [Field E]
    (φ : F→+*E) (f : F[X]) (nf : f≠0) (sp : (f.map φ).Splits)
    (even : ∀ a : E, Even ((f.map φ).rootMultiplicity a)) :
    ∃ c : F, ∃ q : F[X], f=C c*q^2 := by
  classical
  by_cases flat : f.natDegree=0
  · exact ⟨_,1,by simpa using eq_C_of_natDegree_eq_zero flat⟩
  by_cases sf : Squarefree f
  · obtain ⟨a,ha⟩ := sp.exists_eval_eq_zero (by
      rw [degree_eq_natDegree (Polynomial.map_ne_zero nf),natDegree_map];exact_mod_cast flat)
    have one : (f.map φ).rootMultiplicity a≤1 := rootMultiplicity_le_one_of_separable (PerfectField.separable_iff_squarefree.mpr sf).map a
    have pos := (rootMultiplicity_pos' (p:=f.map φ)).mpr ⟨Polynomial.map_ne_zero nf,ha⟩
    obtain ⟨k,hk⟩ := even a
    omega
  · change ¬∀ g : F[X], g*g∣f → IsUnit g at sf
    push Not at sf
    obtain ⟨g,⟨h,eq⟩,nonunit⟩ := sf
    have gg : g≠0 := by rintro rfl;simp [eq] at nf
    have hh : h≠0 := by rintro rfl;simp [eq] at nf
    have gd : 0<g.natDegree := by
      by_contra! z
      have cg := eq_C_of_natDegree_eq_zero (by omega : g.natDegree=0)
      have ng : g.coeff 0≠0 := by intro hz;rw [cg,hz,map_zero] at gg;exact gg rfl
      exact nonunit (cg ▸ isUnit_C.mpr ng.isUnit)
    have size : h.natDegree<f.natDegree := by
      rw [eq,natDegree_mul (mul_ne_zero gg gg) hh,natDegree_mul gg gg]
      omega
    have divides : h.map φ∣f.map φ := by rw [eq,Polynomial.map_mul];exact dvd_mul_left ..
    have eh (a : E) : Even ((h.map φ).rootMultiplicity a) := by
      obtain ⟨k,hk⟩ := even a
      have gmg := Polynomial.map_ne_zero (f:=φ) gg
      rw [eq,Polynomial.map_mul,Polynomial.map_mul,rootMultiplicity_mul
        (mul_ne_zero (mul_ne_zero gmg gmg) (Polynomial.map_ne_zero hh)),
        rootMultiplicity_mul (mul_ne_zero gmg gmg)] at hk
      exact ⟨k-(g.map φ).rootMultiplicity a,by omega⟩
    obtain ⟨c,q,fac⟩ := square_factor φ h hh (sp.of_dvd (Polynomial.map_ne_zero nf) divides) eh
    exact ⟨c,g*q,by rw [eq,fac];ring⟩
termination_by f.natDegree

/-- A nonzero square value in an odd-degree extension rules out a negative
constant twist even if all geometric roots of the quartic have even order. -/
theorem quartic_lower {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [Algebra (ZMod p) K]
    [FiniteDimensional (ZMod p) K] (ext : Odd (Module.finrank (ZMod p) K))
    (g : (ZMod p)[X]) (deg : g.natDegree≤4) (r b : K)
    (nz : b≠0) (witness : (g.map (algebraMap (ZMod p) K)).eval r=b^2)
    (big : 400≤p) :
    -(80*((p.sqrt:ℤ)+1)+4)≤∑ x : ZMod p, quadraticChar (ZMod p) (g.eval x) := by
  classical
  let E := g.SplittingField
  let _ : Fintype E := Fintype.ofFinite _
  let _ : CharP E p := charP_of_injective_ringHom (algebraMap (ZMod p) E).injective p
  let φ := algebraMap (ZMod p) E
  by_cases odd : ∃ a : E, Odd ((g.map φ).rootMultiplicity a)
  · obtain ⟨a,ha⟩ := odd
    exact (abs_le.mp (quartic_character_sum g deg a ha big)).1
  · have gn : g≠0 := by rintro rfl;simp at witness;exact (pow_ne_zero 2 nz) witness.symm
    have even (x : E) := Nat.not_odd_iff_even.mp (fun hx => odd ⟨x,hx⟩)
    obtain ⟨c,q,fac⟩ := square_factor φ g gn (Polynomial.SplittingField.splits g) even
    let π := algebraMap (ZMod p) K
    let t := (q.map π).eval r
    have cw : π c*t^2=b^2 := by simpa [fac,t,π,Polynomial.map_mul,Polynomial.map_pow] using witness
    have tn : t≠0 := by rintro z;rw [z,zero_pow (by decide : 2≠0),mul_zero] at cw;exact (pow_ne_zero 2 nz) cw.symm
    have cn : c≠0 := by intro hc;rw [hc,map_zero,zero_mul] at cw;exact (pow_ne_zero 2 nz) cw.symm
    have val : π c=(b/t)^2 := by field_simp [tn];exact cw
    have norm := congrArg (Algebra.norm (ZMod p)) val
    change Algebra.norm (ZMod p) (algebraMap (ZMod p) K c)=_ at norm
    rw [Algebra.norm_algebraMap,map_pow] at norm
    obtain ⟨k,hk⟩ := ext
    rw [hk,pow_add,pow_one,pow_mul] at norm
    have sq : IsSquare c := by
      refine ⟨Algebra.norm (ZMod p) (b/t)/c^k,?_⟩
      field_simp [cn]
      linear_combination norm
    apply le_trans (by omega : -(80*((p.sqrt:ℤ)+1)+4)≤0)
    apply sum_nonneg
    intro x _
    rw [fac,eval_mul,eval_C,eval_pow]
    by_cases z : c*(q.eval x)^2=0
    · simp [z]
    · rw [(quadraticChar_one_iff_isSquare z).mpr (sq.mul (IsSquare.sq _))]
      decide

#print axioms quartic_lower

/-- A large complete character sum forces a constant times a polynomial square. -/
theorem quartic_dichotomy {p : ℕ} [Fact p.Prime] (g : (ZMod p)[X]) (deg : g.natDegree≤4)
    (big : 400≤p) :
    |∑ x : ZMod p, quadraticChar (ZMod p) (g.eval x)|≤80*((p.sqrt:ℤ)+1)+4 ∨
      ∃ c : ZMod p, ∃ q : (ZMod p)[X], g=C c*q^2 := by
  classical
  let E:=g.SplittingField
  let _ : Fintype E:=Fintype.ofFinite _
  let _ : CharP E p:=charP_of_injective_ringHom (algebraMap (ZMod p) E).injective p
  let φ:=algebraMap (ZMod p) E
  by_cases odd : ∃ a : E, Odd ((g.map φ).rootMultiplicity a)
  · obtain ⟨a,ha⟩:=odd
    exact Or.inl (quartic_character_sum g deg a ha big)
  · right
    by_cases nf : g=0
    · exact ⟨0,0,by simp [nf]⟩
    · exact square_factor φ g nf (Polynomial.SplittingField.splits g) (fun a =>
        Nat.not_odd_iff_even.mp (fun h => odd ⟨a,h⟩))

#print axioms quartic_dichotomy

end Green33PrimeQuarticCharacter
