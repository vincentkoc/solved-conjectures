import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.Norm.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Data.Nat.Multiplicity
import Mathlib.Tactic

/-! The elementary Stepanov auxiliary polynomial for quadratic characters in finite fields.
The two coefficient blocks use disjoint orders of vanishing at an odd-order root.
Hasse derivatives detect multiplicity even when it exceeds the characteristic. -/

open Finset Polynomial
open scoped BigOperators Polynomial

namespace Green33FiniteQuarticCharacter

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

/-- If the orders of the two blocks are separated modulo the Frobenius exponent,
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

/-- Clearing one factor of the polynomial in each positive Hasse order keeps the
product formula polynomial, including in the characteristic of the field. -/
private noncomputable def numerator (f : K[X]) : ℕ → K[X]
  | 0 => 1
  | k+1 => f^k*hasseDeriv (k+1) f

private theorem numerator_identity (f : K[X]) (i : ℕ) :
    f^i*hasseDeriv i f=f*numerator f i := by
  cases i with
  | zero => simp [numerator]
  | succ i => rw [numerator,pow_succ];ring

/-- The coefficient left after factoring `f^n` out of the cleared Hasse derivative
of `f^n * g`. The recurrence is the Hasse product rule. -/
private noncomputable def jet (f : K[X]) : ℕ → K[X] → ℕ → K[X]
  | 0,g,k => f^k*hasseDeriv k g
  | n+1,g,k => ∑ u ∈ antidiagonal k, numerator f u.1*jet f n g u.2

private theorem jet_formula (f g : K[X]) (n k : ℕ) :
    f^k*hasseDeriv k (f^n*g)=f^n*jet f n g k := by
  induction n generalizing k with
  | zero => simp [jet]
  | succ n ih =>
    rw [pow_succ',mul_assoc,hasseDeriv_mul,jet,mul_sum,mul_sum]
    apply sum_congr rfl
    intro u hu
    have eq:=mem_antidiagonal.mp hu
    rw [←eq,pow_add]
    calc _ = (f^u.1*hasseDeriv u.1 f)*(f^u.2*hasseDeriv u.2 (f^n*g)) := by ring
         _ = _ := by rw [numerator_identity,ih];ring

private theorem jet_degree (f g : K[X]) (n k : ℕ) :
    (jet f n g k).natDegree≤g.natDegree+k*f.natDegree := by
  have d (m : ℕ) (P : K[X]) : (hasseDeriv m P).natDegree≤P.natDegree :=
    (natDegree_hasseDeriv_le P m).trans (Nat.sub_le _ _)
  have nd (i : ℕ) : (numerator f i).natDegree ≤ i*f.natDegree := by
    cases i with
    | zero => simp [numerator]
    | succ i =>
      rw [numerator,Nat.succ_mul]
      exact (natDegree_mul_le ..).trans (Nat.add_le_add (natDegree_pow_le ..) (d _ _))
  induction n generalizing k with
  | zero =>
    rw [jet,Nat.add_comm g.natDegree]
    exact (natDegree_mul_le ..).trans (Nat.add_le_add (natDegree_pow_le ..) (d _ _))
  | succ n ih =>
    rw [jet]
    apply natDegree_sum_le_of_forall_le
    intro u hu
    have eq := mem_antidiagonal.mp hu
    exact (natDegree_mul_le ..).trans ((Nat.add_le_add (nd _) (ih _)).trans
      (by rw [←eq,add_mul];omega))

private theorem mult_of_hasse {H : K[X]} (nz : H≠0) (x : K) (r : ℕ)
    (vanish : ∀ k<r, (hasseDeriv k H).eval x=0) : r≤H.rootMultiplicity x := by
  by_contra! low
  have van:=vanish _ low
  rw [←taylor_coeff] at van
  have nt : taylor x H≠0 := by simpa using nz
  exact (coeff_natTrailingDegree_ne_zero.mpr nt) (by
    simpa only [rootMultiplicity_eq_natTrailingDegree,taylor_apply] using van)
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

private theorem inert {a b : K[X]} {k : ℕ} (flat : ∀ i, 0 < i → i ≤ k → hasseDeriv i a=0) :
    hasseDeriv k (a*b)=a*hasseDeriv k b := by
  rw [hasseDeriv_mul,sum_eq_single (0,k)]
  · simp
  · intro u hu ne
    have eq:=mem_antidiagonal.mp hu
    have pos : 0<u.1 := by
      by_contra! zero
      exact ne (Prod.ext (by omega) (by omega))
    rw [flat _ pos (by omega),zero_mul]
  · simp

/-- The positive Hasse derivatives of a monomial of exponent divisible
by `p^e` vanish through order `p^e - 1`. -/
private theorem inert_power {p : ℕ} [Fact p.Prime] [CharP K p] (e j : ℕ) (w : K)
    {k : ℕ} (pos : 0<k) (small : k<p^e) :
    hasseDeriv k (C w*X^(j*p^e))=0 := by
  have base (i : ℕ) (ip : 0 < i) (sm : i<p^e) : hasseDeriv i ((X:K[X])^(p^e))=0 := by
    rw [←monomial_one_right_eq_X_pow,hasseDeriv_monomial]
    have cast : ((p^e).choose i:K)=0 := (CharP.cast_eq_zero_iff K p _).mpr
      ((Fact.out : Nat.Prime p).dvd_choose_pow (by omega) (by omega))
    simp [cast]
  induction j with
  | zero =>
    rw [Nat.zero_mul,pow_zero,mul_one]
    exact hasseDeriv_C k w pos
  | succ j ih =>
    rw [Nat.succ_mul,pow_add,←mul_assoc,mul_comm _ (X^_),inert (fun i a b => base i a (by omega)),ih,mul_zero]
private theorem block_eval {I J q p e : ℕ} [Fact p.Prime] [CharP K p] (power : q=p^e) (f : K[X]) (c x : K) (fr : x^q=x+c)
    (n k : ℕ) (small : k<q) (w : Indices I J→K) :
    f.eval x^k*(hasseDeriv k (f^n*block q w)).eval x =
      f.eval x^n*(probe f c n k w).eval x := by
  classical
  have decomp : f^n*block q w =
      ∑ t, (C (w t)*X^(t.1.val*q))*(f^n*X^t.2.val) := by
    unfold block
    rw [mul_sum]
    apply sum_congr rfl
    intro t _
    rw [← C_mul_X_pow_eq_monomial,exponent,pow_add];ring
  rw [decomp,map_sum,eval_finsetSum,probe,eval_finsetSum,mul_sum,mul_sum]
  apply sum_congr rfl
  intro t _
  have flat (i : ℕ) (pos : 0 < i) (le : i≤k) : hasseDeriv i (C (w t)*X^(t.1.val*q) : K[X])=0 := by
    subst q
    exact inert_power e t.1.val (w t) pos (by omega)
  have v := congrArg (fun z : K[X] => z.eval x) (jet_formula f (X^t.2.val) n k)
  simp only [eval_mul,eval_pow] at v
  rw [inert flat]
  simp only [eval_mul,eval_C,eval_pow,eval_X,eval_add]
  rw [Nat.mul_comm t.1.val q,pow_mul,fr]
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

/-- A Stepanov bound for a translated finite field. The input set consists of
points on which the Frobenius and power tests both have their prescribed values. -/
theorem stepanov_bound [Fintype K] {q p e : ℕ} [Fact p.Prime] [CharP K p] (power : q=p^e)
    {I J r n : ℕ} (f : K[X]) (nf : f≠0) (c : K)
    (points : Finset K) (test : ∀ x∈points, x^q=x+c ∧ f.eval x≠0 ∧ f.eval x^n=1)
    (width : I≤q) (small : r≤q)
    (gap : I≤(n*f.natTrailingDegree)%q) (room : (n*f.natTrailingDegree)%q+I≤q)
    (more : r*(I+J+r*f.natDegree+1)<2*(J*I)) :
    r*points.card≤J*q+I+n*f.natDegree := by
  classical
  obtain ⟨u,v,nz,vanish⟩ := vanishing_tables f c n more
  let H := block q u+f^n*block q v
  have nonzero : H≠0 := by
    intro zero
    have both := auxiliary_independent width (power ▸ pow_pos (Fact.out : p.Prime).pos e) f nf gap room u v zero
    exact nz.elim (· both.1) (· both.2)
  have degree : H.natDegree≤J*q+I+n*f.natDegree := by
    apply natDegree_add_le_of_degree_le ((block_degree u).trans (by omega))
    have mul := natDegree_mul_le (p:=f^n) (q:=block q v)
    have power := natDegree_pow_le (p:=f) (n:=n)
    have deg := block_degree (p:=q) v
    omega
  have many (x : K) (hx : x∈points) : r≤H.rootMultiplicity x := by
    obtain ⟨fr,fzero,good⟩ := test x hx
    have root (k : ℕ) (kr : k<r) : (hasseDeriv k H).IsRoot x := by
      have ua := block_eval power f c x fr 0 k (kr.trans_le small) u
      have vb := block_eval power f c x fr n k (kr.trans_le small) v
      have eq := congrArg (fun P : K[X] => P.eval x) (vanish k kr)
      simp only [pow_zero,one_mul] at ua
      rw [good,one_mul] at vb
      simp only [eval_add,eval_zero] at eq
      change (hasseDeriv k (block q u+f^n*block q v)).eval x=0
      rw [map_add,eval_add]
      apply (mul_eq_zero.mp (show f.eval x^k*((hasseDeriv k (block q u)).eval x+
        (hasseDeriv k (f^n*block q v)).eval x)=0 by rw [mul_add,ua,vb,eq])).resolve_left (pow_ne_zero k fzero)
    exact mult_of_hasse nonzero x r root
  calc r*points.card = ∑ _ ∈ points,r := by simp [Nat.mul_comm]
       _ ≤ ∑ x ∈ points,H.roots.count x := sum_le_sum fun x hx => by rw [count_roots];exact many x hx
       _ ≤ ∑ x : K,H.roots.count x := sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
       _ = H.roots.card := Multiset.sum_count_eq_card (fun _ _ => mem_univ _)
       _ ≤ _ := (card_roots' H).trans degree

#print axioms stepanov_bound

private theorem quartic_count [Fintype K] {q p e : ℕ} [Fact p.Prime] [CharP K p] (power : q=p^e) (parity : Odd q)
    (f : K[X]) (nf : f≠0) (degree : f.natDegree≤4)
    (order : Odd f.natTrailingDegree) (big : 400≤q) (c : K)
    (points : Finset K) (card : points.card≤q)
    (test : ∀ x∈points, x^q=x+c ∧ f.eval x≠0 ∧ f.eval x^(q/2)=1) :
    2*points.card≤q+80*(q.sqrt+1) := by
  let j := q.sqrt/10
  let i := 20*j^2
  let r := 2*j-1
  let n := q/2
  have large : 20≤q.sqrt := Nat.le_sqrt.mpr big
  have jpos : 2≤j := by dsimp [j];omega
  have jp : 10*j≤q.sqrt := by dsimp [j];omega
  have bound : 100*j^2≤q := by nlinarith only [Nat.mul_le_mul jp jp,Nat.sqrt_le' q]
  have iw : 5*i≤q := by dsimp [i];omega
  have rrel : r+1=2*j := by dsimp [r];omega
  have rsmall : r≤q := by nlinarith only [bound,rrel,Nat.mul_le_mul_left j jpos]
  have two : 2*n+1=q := by
    obtain ⟨k,hk⟩ := parity
    dsimp [n];omega
  have mt : f.natTrailingDegree≤4 := (natTrailingDegree_le_natDegree f).trans degree
  have classes : f.natTrailingDegree=1 ∨ f.natTrailingDegree=3 := by
    obtain ⟨a,ha⟩ := order
    omega
  have split : (n*f.natTrailingDegree)%q=n ∨ (n*f.natTrailingDegree)%q=n-1 := by
    rcases classes with e|e
    · left; rw [e,mul_one,Nat.mod_eq_of_lt (by omega)]
    · right
      rw [e,show n*3=q+(n-1) by omega,Nat.add_mod_left,Nat.mod_eq_of_lt (by omega)]
  have more : r*(i+j+r*f.natDegree+1)<2*(j*i) := by
    have rd := Nat.mul_le_mul (show r≤2*j by omega) degree
    have cross := Nat.mul_le_mul (show r≤2*j by omega) (show j+r*f.natDegree+1≤9*j+1 by omega)
    have cancel := congrArg (·*i) rrel
    have lower : j^2≥2*j := by simpa only [pow_two] using Nat.mul_le_mul_right j jpos
    change r*(20*j^2+j+r*f.natDegree+1)<2*(j*(20*j^2))
    dsimp [i] at cancel
    nlinarith only [cross,cancel,lower,jpos]
  have raw := stepanov_bound power (n:=n) (I:=i) (J:=j) (r:=r) f nf c points test (by omega)
    rsmall (by rcases split with a|a <;> omega)
    (by rcases split with a|a <;> omega) more
  have nd := Nat.mul_le_mul_left n degree
  have align := congrArg (·*points.card) rrel
  have upper : q.sqrt+1≤20*j := by dsimp [j];omega
  have close := Nat.mul_le_mul_right (q.sqrt+1) upper
  have sq := Nat.lt_succ_sqrt' q
  have final : j*(2*points.card)≤j*(q+80*(q.sqrt+1)) := by
    nlinarith only [raw,nd,align,card,iw,two,close,sq]
  exact Nat.le_of_mul_le_mul_left final (by omega)

section CharacterValues

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {K : Type*} [Field K] [Fintype K] [Algebra F K]
local notation "Q" => Fintype.card F

private theorem positive_values (fld : ringChar F≠2) (g : F[X]) (deg : g.natDegree≤4) (a : K)
    (odd : Odd ((g.map (algebraMap F K)).rootMultiplicity a)) (big : 400≤Q) :
    2*(univ.filter (fun x : F => quadraticChar F (g.eval x)=1)).card≤
      Q+80*((Fintype.card F).sqrt+1) := by
  classical
  let φ := algebraMap F K
  let f := (g.map φ).comp (X+C a)
  have mult : (g.map φ).rootMultiplicity a=f.natTrailingDegree := rootMultiplicity_eq_natTrailingDegree
  have order : Odd f.natTrailingDegree := mult ▸ odd
  have nf : f≠0 := by rintro e;rw [e,natTrailingDegree_zero] at order;exact Nat.not_odd_zero order
  have degree : f.natDegree≤4 := by
    have le := natDegree_comp_le (p:=g.map φ) (q:=X+C a)
    rw [natDegree_X_add_C,mul_one] at le
    exact le.trans (natDegree_map_le.trans deg)
  let S := univ.filter (fun x : F => quadraticChar F (g.eval x)=1)
  let P := S.image (fun x => φ x-a)
  have same : P.card=S.card := card_image_of_injective _ (fun _ _ e => φ.injective (sub_left_inj.mp e))
  have size : P.card≤Q := same.trans_le (card_le_univ S)
  obtain ⟨e,prime,power⟩ := FiniteField.card F (ringChar F)
  let _ : Fact (ringChar F).Prime := ⟨prime⟩
  let _ : CharP K (ringChar F) := charP_of_injective_ringHom (algebraMap F K).injective _
  have parity : Odd (Fintype.card F) := power ▸ (prime.odd_of_ne_two fld).pow
  have tests (y : K) (hy : y∈P) : y^Q=y+(a-a^Q) ∧ f.eval y≠0 ∧ f.eval y^(Q/2)=1 := by
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hy
    have gp : quadraticChar F (g.eval x)=1 := (mem_filter.mp hx).2
    have eq : f.eval (φ x-a)=φ (g.eval x) := by simp [f,eval_comp]
    rw [eq]
    have nz : g.eval x≠0 := by intro zero;simp [zero] at gp
    have fr : x^Q=x := FiniteField.pow_card x
    have square := (quadraticChar_one_iff_isSquare nz).mp gp
    have one := (FiniteField.isSquare_iff fld nz).mp square
    refine ⟨?_,(map_ne_zero φ).mpr nz,?_⟩
    · rw [power,sub_pow_char_pow,←power,←map_pow,fr];ring
    · rw [←map_pow,one,map_one]
  have h := quartic_count power parity f nf degree order big (a-a^Q) P size tests
  rwa [same] at h

/-- An elementary uniform square-root bound on complete quadratic character sums
of degree at most four. The odd-multiplicity zero may lie in any finite extension. -/
theorem quartic_character_sum (fld : ringChar F≠2) (g : F[X]) (deg : g.natDegree≤4) (a : K)
    (odd : Odd ((g.map (algebraMap F K)).rootMultiplicity a)) :
    |∑ x : F, quadraticChar F (g.eval x)|≤80*(((Fintype.card F).sqrt:ℤ)+1)+4 := by
  classical
  by_cases big : 400≤Q
  swap
  · have bound (x : F) : |quadraticChar F (g.eval x)|≤1 := by
      by_cases z : g.eval x=0
      · simp [z]
      · rcases quadraticChar_dichotomy z with h|h <;> simp [h]
    have h := (Finset.abs_sum_le_sum_abs (fun x : F => quadraticChar F (g.eval x)) univ).trans
      (sum_le_sum (fun x _ => bound x))
    simp only [sum_const,card_univ,nsmul_eq_mul,mul_one] at h
    have rt := Nat.lt_succ_sqrt' Q
    have lim : (Fintype.card F).sqrt<20 := Nat.sqrt_lt'.mpr (by omega)
    have linear := Nat.mul_le_mul_left ((Fintype.card F).sqrt+1) (show (Fintype.card F).sqrt+1≤20 by omega)
    have small : Q≤80*((Fintype.card F).sqrt+1)+4 := by nlinarith
    exact h.trans (by exact_mod_cast small)
  let χ := quadraticChar F
  let P := univ.filter (fun x : F => χ (g.eval x)=1)
  let M := univ.filter (fun x : F => χ (g.eval x)= -1)
  let Z := univ.filter (fun x : F => g.eval x=0)
  have positive : 2*P.card≤Q+80*((Fintype.card F).sqrt+1) := positive_values fld g deg a odd big
  obtain ⟨u,neg⟩ := quadraticChar_exists_neg_one' fld
  let t := C (u:F)*g
  have mt : ((t.map (algebraMap F K)).rootMultiplicity a)=
      ((g.map (algebraMap F K)).rootMultiplicity a) := by
    have nf : g.map (algebraMap F K) ≠ 0 := by
      intro e;rw [e,rootMultiplicity_zero] at odd;exact Nat.not_odd_zero odd
    simp only [t,Polynomial.map_mul,map_C]
    rw [rootMultiplicity_mul (mul_ne_zero (C_ne_zero.mpr ((map_ne_zero (algebraMap F K)).mpr u.ne_zero)) nf),rootMultiplicity_C,zero_add]
  have twist := positive_values fld t ((natDegree_C_mul_le ..).trans deg) a (mt.symm ▸ odd) big
  have sets : univ.filter (fun x : F => quadraticChar F (t.eval x)=1)=M := by
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
  have parts (x : F) :
      (if χ (g.eval x)=1 then (1:ℤ) else 0)+(if χ (g.eval x)= -1 then 1 else 0)+
      (if g.eval x=0 then 1 else 0)=1 ∧
      χ (g.eval x)=(if χ (g.eval x)=1 then 1 else 0)-(if χ (g.eval x)= -1 then 1 else 0) := by
    by_cases z : g.eval x=0
    · simp [z,χ]
    · rcases quadraticChar_dichotomy z with h|h <;> simp [χ,h,z]
  have mass := sum_congr (s₁:=univ) rfl (fun x _ => (parts x).1)
  have values := sum_congr (s₁:=univ) rfl (fun x _ => (parts x).2)
  simp only [sum_add_distrib,sum_sub_distrib,sum_boole,sum_const,card_univ,nsmul_eq_mul,mul_one] at mass values
  change (P.card:ℤ)+M.card+Z.card=Q at mass
  change (∑ x : F,χ (g.eval x))=(P.card:ℤ)-M.card at values
  change |∑ x : F, χ (g.eval x)|≤_
  rw [values,abs_le]
  omega

#print axioms quartic_character_sum
end CharacterValues

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
theorem quartic_lower {F : Type*} [Field F] [Fintype F] [DecidableEq F] (fld : ringChar F≠2) {K : Type*} [Field K] [Algebra F K]
    [FiniteDimensional F K] (ext : Odd (Module.finrank F K))
    (g : F[X]) (deg : g.natDegree≤4) (r b : K)
    (nz : b≠0) (witness : (g.map (algebraMap F K)).eval r=b^2)
    :
    -(80*(((Fintype.card F).sqrt:ℤ)+1)+4)≤∑ x : F, quadraticChar F (g.eval x) := by
  classical
  let E := g.SplittingField
  let _ : Fintype E := Fintype.ofFinite _
  let φ := algebraMap F E
  by_cases odd : ∃ a : E, Odd ((g.map φ).rootMultiplicity a)
  · obtain ⟨a,ha⟩ := odd
    exact (abs_le.mp (quartic_character_sum fld g deg a ha)).1
  · have gn : g≠0 := by rintro rfl;simp at witness;exact (pow_ne_zero 2 nz) witness.symm
    have even (x : E) := Nat.not_odd_iff_even.mp (fun hx => odd ⟨x,hx⟩)
    obtain ⟨c,q,fac⟩ := square_factor φ g gn (Polynomial.SplittingField.splits g) even
    let π := algebraMap F K
    let t := (q.map π).eval r
    have cw : π c*t^2=b^2 := by simpa [fac,t,π,Polynomial.map_mul,Polynomial.map_pow] using witness
    have tn : t≠0 := by rintro z;rw [z,zero_pow (by decide : 2≠0),mul_zero] at cw;exact (pow_ne_zero 2 nz) cw.symm
    have cn : c≠0 := by intro hc;rw [hc,map_zero,zero_mul] at cw;exact (pow_ne_zero 2 nz) cw.symm
    have val : π c=(b/t)^2 := by field_simp [tn];exact cw
    have norm := congrArg (Algebra.norm F) val
    change Algebra.norm F (algebraMap F K c)=_ at norm
    rw [Algebra.norm_algebraMap,map_pow] at norm
    obtain ⟨k,hk⟩ := ext
    rw [hk,pow_add,pow_one,pow_mul] at norm
    have sq : IsSquare c := by
      refine ⟨Algebra.norm F (b/t)/c^k,?_⟩
      field_simp [cn]
      linear_combination norm
    apply le_trans (by omega : -(80*(((Fintype.card F).sqrt:ℤ)+1)+4)≤0)
    apply sum_nonneg
    intro x _
    rw [fac,eval_mul,eval_C,eval_pow]
    by_cases z : c*(q.eval x)^2=0
    · simp [z]
    · rw [(quadraticChar_one_iff_isSquare z).mpr (sq.mul (IsSquare.sq _))]
      decide

#print axioms quartic_lower

/-- A large complete character sum forces a constant times a polynomial square. -/
theorem quartic_dichotomy {F : Type*} [Field F] [Fintype F] [DecidableEq F] (fld : ringChar F≠2) (g : F[X]) (deg : g.natDegree≤4)
    :
    |∑ x : F, quadraticChar F (g.eval x)|≤80*(((Fintype.card F).sqrt:ℤ)+1)+4 ∨
      ∃ c : F, ∃ q : F[X], g=C c*q^2 := by
  classical
  let E:=g.SplittingField
  let _ : Fintype E:=Fintype.ofFinite _
  let φ:=algebraMap F E
  by_cases odd : ∃ a : E, Odd ((g.map φ).rootMultiplicity a)
  · obtain ⟨a,ha⟩:=odd
    exact Or.inl (quartic_character_sum fld g deg a ha)
  · right
    by_cases nf : g=0
    · exact ⟨0,0,by simp [nf]⟩
    · exact square_factor φ g nf (Polynomial.SplittingField.splits g) (fun a =>
        Nat.not_odd_iff_even.mp (fun h => odd ⟨a,h⟩))

#print axioms quartic_dichotomy

end Green33FiniteQuarticCharacter
