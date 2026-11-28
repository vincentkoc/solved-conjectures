import Mathlib
import research.arxiv.«1104.1579».CunninghamJonesLinearFactors

/-!
# Large degrees in Jones’s polynomial reducibility question

An explicit cutoff reduces each fixed-parameter instance of Jones’s
Conjecture 4.1 to a finite interval of degrees. The proof uses a lift of the
sparse polynomial obtained by multiplying the Jones sum by X − 1.
-/

section

open Finset

/-- Compress a finite set of exponents while preserving all equalities between
two-term sums, fixing zero and collapsing one but keeping N nonzero. -/
private theorem compress_support (N : ℕ) (S : Finset ℕ) (hN : 4^S.card < N) :
    ∃ h : ℕ, 0 < h ∧ ∃ v : ℕ → ℕ, v 0 = 0 ∧ v 1 = 0 ∧ v N = h ∧
      (∀ x ≤ N, v x ≤ h) ∧
      ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, ∀ w ∈ S, x+y=z+w → v x+v y=v z+v w := by
  classical
  have hN0 : 0 < N := (Nat.zero_le _).trans_lt hN
  let color (a : Fin (4^S.card+1)) (x : S) : Fin 4 :=
    ⟨4*((a.val*x.val)%N)/N,(Nat.div_lt_iff_lt_mul hN0).mpr (by
      have := Nat.mod_lt (a.val*x.val) hN0; omega)⟩
  obtain ⟨a,b,hab,hc⟩ := Fintype.exists_ne_map_eq_of_card_lt color (by simp)
  wlog hlt : a < b generalizing a b
  · exact this b a hab.symm hc.symm (lt_of_le_of_ne (le_of_not_gt hlt) hab.symm)
  have hab' : a.val < b.val := hlt
  let h := b.val-a.val
  let v (x : ℕ) := b.val*x/N-a.val*x/N
  have hbN : b.val < N := by have := b.isLt; omega
  have haN : a.val < N := by omega
  refine ⟨h,by dsimp [h]; omega,v,by simp [v],by simp [v,Nat.div_eq_of_lt hbN,Nat.div_eq_of_lt haN],
    by simp [v,h,hN0.ne'],?_,?_⟩
  · intro x hx
    have hb : b.val*x ≤ a.val*x+h*N := by
      have hba : b.val = a.val+h := by dsimp [h]; omega
      calc b.val*x = a.val*x+h*x := by rw [hba,add_mul]
           _ ≤ _ := Nat.add_le_add_left (Nat.mul_le_mul_left _ hx) _
    have hh := Nat.div_le_div_right hb (c := N)
    rw [Nat.add_mul_div_right _ _ hN0] at hh
    dsimp [v]
    omega
  · let err (x : ℕ) : ℤ := h*x-(N:ℤ)*v x
    have herr (x : ℕ) (hx : x ∈ S) : -(N:ℤ) < 4*err x ∧ 4*err x < N := by
      have he := congrArg Fin.val (congrFun hc ⟨x,hx⟩)
      change 4*((a.val*x)%N)/N = 4*((b.val*x)%N)/N at he
      have h₁ := Nat.mod_add_div (4*((a.val*x)%N)) N
      have h₂ := Nat.mod_add_div (4*((b.val*x)%N)) N
      rw [he] at h₁
      have h₃ := Nat.mod_lt (4*((a.val*x)%N)) hN0
      have h₄ := Nat.mod_lt (4*((b.val*x)%N)) hN0
      have heval : err x = (((b.val*x)%N : ℕ):ℤ)-(((a.val*x)%N : ℕ):ℤ) := by
        have ha := Nat.mod_add_div (a.val*x) N
        have hb := Nat.mod_add_div (b.val*x) N
        have hd := Nat.div_le_div_right (Nat.mul_le_mul_right x hab'.le) (c := N)
        dsimp only [err,h,v]
        push_cast [hab'.le,hd]
        zify at ha hb
        linear_combination ha - hb
      rw [heval]
      omega
    intro x hx y hy z hz w hw heq
    have hX := herr x hx
    have hY := herr y hy
    have hZ := herr z hz
    have hW := herr w hw
    have hz' : (x:ℤ)+y = z+w := by exact_mod_cast heq
    have hid : err x+err y-err z-err w = (N:ℤ)*((v z:ℤ)+v w-v x-v y) := by
      dsimp only [err]
      linear_combination (h:ℤ)*hz'
    have hbnd : -(N:ℤ) < (N:ℤ)*((v z:ℤ)+v w-v x-v y) ∧
        (N:ℤ)*((v z:ℤ)+v w-v x-v y) < N := by constructor <;> linarith
    have hn : 0 < (N:ℤ) := by exact_mod_cast hN0
    by_contra hne
    rcases lt_or_gt_of_ne hne with hl|hl
    · have h1 : (1:ℤ) ≤ (v z:ℤ)+v w-v x-v y := by omega
      linarith [mul_le_mul_of_nonneg_left h1 hn.le]
    · have h1 : (v z:ℤ)+v w-v x-v y ≤ -1 := by omega
      linarith [mul_le_mul_of_nonneg_left h1 hn.le]


end

section

open Polynomial
open scoped Polynomial

private theorem primitive_binomial {R : Type*} [CommRing R] [IsDomain R]
    {a l : R} (hl : Prime l) (ha : ¬l ∣ a) {d : ℕ} (hd : 0 < d) :
    Irreducible (C a*X^d+C l) := by
  let f : R[X] := C a*X^d+C l
  have ha0 : a ≠ 0 := fun e => ha (e ▸ dvd_zero _)
  have hlt : degree (C l) < degree (C a*X^d) := by
    rw [degree_C hl.ne_zero,degree_C_mul_X_pow _ ha0]
    exact_mod_cast hd
  have hdeg : f.degree = d := (degree_add_eq_left_of_degree_lt hlt).trans (degree_C_mul_X_pow _ ha0)
  have hlc : f.leadingCoeff = a :=
    (leadingCoeff_add_of_degree_lt' hlt).trans (leadingCoeff_C_mul_X_pow ..)
  have hc0 : f.coeff 0 = l := by simp [f,hd.ne',eq_comm]
  have hu : f.IsPrimitive := by
    intro r hr
    have hcoeff := (C_dvd_iff_dvd_coeff r f).mp hr
    have hrl : r ∣ l := hc0 ▸ hcoeff 0
    rcases hl.irreducible.dvd_iff.mp hrl with hunit|hassoc
    · exact hunit
    · exact (ha (hassoc.dvd.trans (hlc ▸ hcoeff f.natDegree))).elim
  change Irreducible f
  apply irreducible_of_eisenstein_criterion (P := Ideal.span {l}) ((Ideal.span_singleton_prime hl.ne_zero).mpr hl)
  · simpa only [hlc, Ideal.mem_span_singleton] using ha
  · intro n hn
    have hnd : n ≠ d := by rw [hdeg] at hn; exact (WithBot.coe_lt_coe.mp hn).ne
    by_cases hz : n = 0
    · rw [hz,hc0,Ideal.mem_span_singleton]
    · simp [f,hnd,hz,coeff_C]
  · rw [hdeg]; exact_mod_cast hd
  · rw [Ideal.span_singleton_pow,Ideal.mem_span_singleton,hc0]
    intro h
    obtain ⟨r,hr⟩ := h
    apply hl.not_isUnit
    have he : l*1 = l*(l*r) := by simpa [pow_two,mul_assoc] using hr
    exact IsUnit.of_mul_eq_one _ (mul_left_cancel₀ hl.ne_zero he).symm
  · exact hu

private theorem lifted_trinomial_prime (m N d : ℕ) (hm : 2 ≤ m) (hd : 0 < d) :
    Prime (C ((X:ℚ[X])^N) * X^d + C (C ((m:ℚ)-1)*X + C (-(m:ℚ)))) := by
  let b : ℚ := (m:ℚ)-1
  let l : ℚ[X] := C b*X+C (-(m:ℚ))
  have hb : b ≠ 0 := by
    have h : (2:ℚ) ≤ m := by exact_mod_cast hm
    dsimp [b]
    linarith
  have hm0 : (m:ℚ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hprime : Prime l := (irreducible_of_degree_eq_one (degree_linear hb)).prime
  apply (primitive_binomial hprime ?_ hd).prime
  let t : ℚ := m/b
  have hroot : l.eval t = 0 := by simp [l,t]; field_simp; ring
  have ht : t ≠ 0 := div_ne_zero hm0 hb
  rintro ⟨g,hg⟩
  have h := congrArg (eval t) hg
  simp [hroot,ht] at h


end

section

open Polynomial
open scoped Polynomial
variable {R : Type*} [CommSemiring R]

private noncomputable def liftAxes (x y : ℕ → ℕ) : R[X] →+ R[X][X] where
  toFun p := p.sum fun n a => monomial (y n) (monomial (x n) a)
  map_zero' := by simp
  map_add' p q := Polynomial.sum_add_index p q _ (by simp) (by simp)

private theorem liftAxes_monomial (x y : ℕ → ℕ) (n : ℕ) (a : R) :
    liftAxes x y (monomial n a) = monomial (y n) (monomial (x n) a) := by
  exact Polynomial.sum_monomial_index a (fun k c => monomial (y k) (monomial (x k) c)) (by simp)

private theorem reflect_expansion (N : ℕ) (p : R[X]) (hp : ∀ i ∈ p.support, i ≤ N) :
    reflect N p = ∑ i ∈ p.support, monomial (N-i) (p.coeff i) := by
  let f : R[X] →+ R[X] := ⟨⟨reflect N,reflect_zero⟩,fun p q => reflect_add p q N⟩
  have e : p = ∑ i ∈ p.support, monomial i (p.coeff i) := (sum_monomial_eq p).symm
  calc
    reflect N p = f (∑ i ∈ p.support, monomial i (p.coeff i)) := congrArg f e
    _ = _ := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      change reflect N (monomial i (p.coeff i)) = monomial (N-i) (p.coeff i)
      simp only [← C_mul_X_pow_eq_monomial, reflect_C_mul_X_pow, revAt_le (hp i hi)]

private theorem liftAxes_autocorrelation (S : Finset ℕ) (N d : ℕ) (v : ℕ → ℕ)
    (hN : ∀ x ∈ S, x ≤ N) (hd : ∀ x ∈ S, v x ≤ d)
    (hs : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, ∀ w ∈ S, x+y=z+w → v x+v y=v z+v w) :
    ∃ u : ℕ → ℕ, ∀ p : R[X], p.support ⊆ S →
      liftAxes id u (p * reflect N p) =
        liftAxes id v p * liftAxes (N-·) (fun i => d-v i) p := by
  classical
  have hfiber (k : ℕ) : ∃ t : ℕ, ∀ i ∈ S, ∀ j ∈ S, i+(N-j)=k → v i+(d-v j)=t := by
    by_cases h : ∃ i ∈ S, ∃ j ∈ S, i+(N-j)=k
    · obtain ⟨a,ha,b,hb,he⟩ := h
      refine ⟨v a+(d-v b),fun i hi j hj hh => ?_⟩
      have hn₁ := hN b hb
      have hn₂ := hN j hj
      have hs' := hs i hi b hb a ha j hj (by omega)
      have hd₁ := hd j hj
      have hd₂ := hd b hb
      omega
    · exact ⟨0,fun i hi j hj hh => (h ⟨i,hi,j,hj,hh⟩).elim⟩
  choose u hu using hfiber
  refine ⟨u,fun p hp => ?_⟩
  have forward : p = ∑ i ∈ p.support, monomial i (p.coeff i) := (sum_monomial_eq p).symm
  have backward := reflect_expansion N p fun i hi => hN i (hp hi)
  have both := congrArg₂ (· * ·) forward backward
  rw [both]
  change _ = (∑ i ∈ p.support, _) * (∑ j ∈ p.support, _)
  simp only [Finset.sum_mul,Finset.mul_sum,map_sum,monomial_mul_monomial,liftAxes_monomial,id_eq]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [← hu _ j (hp hj) i (hp hi) rfl]


end

section
open Polynomial
open scoped Polynomial
variable {R : Type*} [CommSemiring R]
private theorem eval_one_liftAxes (x y : ℕ → ℕ) (p : R[X]) :
    (liftAxes x y p).eval 1 = ∑ i ∈ p.support, monomial (x i) (p.coeff i) := by
  change (∑ i ∈ p.support, monomial (y i) (monomial (x i) (p.coeff i))).eval 1 = _
  simp [eval_finsetSum, eval_monomial]

private theorem specialization_of_prime_lift
    (S : Finset ℕ) (N d : ℕ) (v : ℕ → ℕ) (p g : R[X])
    (hN : ∀ x ∈ S, x ≤ N) (hd : ∀ x ∈ S, v x ≤ d)
    (hs : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, ∀ w ∈ S, x+y=z+w → v x+v y=v z+v w)
    (hp : p.support ⊆ S) (hg : g.support ⊆ S)
    (heq : p * reflect N p = g * reflect N g) (hprime : Prime (liftAxes id v p)) :
    p ∣ g ∨ p ∣ reflect N g := by
  obtain ⟨u,hu⟩ := liftAxes_autocorrelation (R := R) S N d v hN hd hs
  have he := congrArg (liftAxes id u) heq
  rw [hu p hp,hu g hg] at he
  have eval_forward (q : R[X]) : (liftAxes id v q).eval 1 = q := by
    rw [eval_one_liftAxes]
    exact sum_monomial_eq q
  have eval_backward : (liftAxes (N-·) (fun i => d-v i) g).eval 1 = reflect N g :=
    (eval_one_liftAxes ..).trans (reflect_expansion N g (fun i hi => hN i (hg hi))).symm
  rcases hprime.dvd_or_dvd (he ▸ dvd_mul_right _ _) with h|h
  · left
    simpa only [coe_evalRingHom,eval_forward] using _root_.map_dvd (evalRingHom 1) h
  · right
    simpa only [coe_evalRingHom,eval_forward,eval_backward] using _root_.map_dvd (evalRingHom 1) h


end

section

open Polynomial
open scoped Polynomial

private theorem middleCoeff_energy {R : Type*} [CommSemiring R] (p : R[X]) (N : ℕ)
    (hp : p.natDegree ≤ N) :
    (p*reflect N p).coeff N = ∑ i ∈ p.support, p.coeff i ^ 2 := by
  have h : p = ∑ i ∈ p.support, monomial i (p.coeff i) := (sum_monomial_eq p).symm
  conv_lhs => lhs; lhs; rw [h]
  rw [Finset.sum_mul, finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := (le_natDegree_of_mem_supp i hi).trans hp
  have e := coeff_monomial_mul (reflect N p) i (N-i) (p.coeff i)
  rw [Nat.sub_add_cancel hi',coeff_reflect,revAt_le (Nat.sub_le ..),Nat.sub_sub_self hi'] at e
  simpa only [pow_two] using e

private theorem support_card_le_middleCoeff (p : ℤ[X]) (N : ℕ) (hp : p.natDegree ≤ N) :
    (p.support.card : ℤ) ≤ (p*reflect N p).coeff N := by
  rw [middleCoeff_energy p N hp]
  calc
    (p.support.card : ℤ) = ∑ _i ∈ p.support, (1:ℤ) := by simp
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i hi
      have he := mem_support_iff.mp hi
      have := sq_pos_of_ne_zero he
      omega


end

section

open Polynomial
open scoped Polynomial

private noncomputable def tri {R : Type*} [CommRing R] (m : R) (N : ℕ) : R[X] :=
  monomial N 1 + monomial 1 (m-1) + monomial 0 (-m)

private theorem tri_reflect {R : Type*} [CommRing R] (m : R) (N : ℕ) (h : 1 ≤ N) :
    reflect N (tri m N) = 1 + C (m-1)*X^(N-1) + C (-m)*X^N := by
  simp only [tri, ← C_mul_X_pow_eq_monomial, reflect_add, reflect_C_mul_X_pow]
  simp [revAt_le h,revAt_le le_rfl]

private theorem tri_bezout {R : Type*} [CommRing R] (m : R) (N : ℕ) (h : 1 ≤ N) :
    X * reflect N (tri m N) - (C (m-1) - C m*X)*tri m N = C ((m-1)*m)*(X-1)^2 := by
  rw [tri_reflect m N h]
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  simp only [tri, ← C_mul_X_pow_eq_monomial, Nat.succ_sub_one, pow_succ, pow_zero,
    C_1, one_mul, mul_one,map_sub,map_mul,map_neg]
  ring

private theorem unit_of_common_factor (m : ℚ) (N : ℕ) (h : 1 ≤ N)
    (hm : m ≠ 0) (hb : m-1 ≠ 0) (p q : ℚ[X]) (hp : p.eval 1 ≠ 0)
    (hq : q ∣ p) (h₁ : q ∣ tri m N) (h₂ : q ∣ reflect N (tri m N)) : IsUnit q := by
  have hd := dvd_sub (h₂.trans (dvd_mul_left _ X)) (h₁.trans (dvd_mul_left _ (C (m-1)-C m*X)))
  rw [tri_bezout m N h] at hd
  have hc := (irreducible_X_sub_C (1:ℚ)).coprime_iff_not_dvd.mpr
    (show ¬ X-C 1 ∣ q from fun e => hp (dvd_iff_isRoot.mp (e.trans hq)))
  have hc' : IsCoprime q ((X-1)^2) := by simpa using hc.symm.pow_right (n := 2)
  exact isUnit_of_dvd_unit (hc'.dvd_of_dvd_mul_right hd) ((mul_ne_zero hb hm).isUnit.map C)

private theorem swap_autocorrelation {R : Type*} [CommRing R] (a b : R[X]) (u w : ℕ)
    (ha : a.natDegree ≤ u) (hb : b.natDegree ≤ w) :
    (a*b)*reflect (u+w) (a*b) = (a*reflect w b)*reflect (u+w) (a*reflect w b) := by
  have hr : (reflect w b).natDegree ≤ w := natDegree_reflect_le.trans (max_le le_rfl hb)
  rw [reflect_mul a b ha hb,reflect_mul a (reflect w b) ha hr, reflect_reflect]
  ring

private theorem swap_alternative {R : Type*} [CommRing R] [IsDomain R]
    (a b : R[X]) (u w : ℕ) (ha : a.natDegree ≤ u) (hb : b.natDegree ≤ w)
    (ha₀ : a ≠ 0) (hb₀ : b ≠ 0)
    (halt : a*b ∣ a*reflect w b ∨ a*b ∣ reflect (u+w) (a*reflect w b)) :
    b ∣ reflect (u+w) (a*b) ∨ a ∣ reflect (u+w) (a*b) := by
  have hr : (reflect w b).natDegree ≤ w := natDegree_reflect_le.trans (max_le le_rfl hb)
  rw [reflect_mul a (reflect w b) ha hr, reflect_reflect] at halt
  rw [reflect_mul a b ha hb]
  rcases halt with he|he
  · exact Or.inl (((mul_dvd_mul_iff_left ha₀).mp he).trans (dvd_mul_left ..))
  · exact Or.inr (((mul_dvd_mul_iff_right hb₀).mp he).trans (dvd_mul_right ..))


end

section
open Polynomial
open scoped Polynomial
private theorem tri_support {R : Type*} [CommRing R] (m : R) (N : ℕ) :
    (tri m N).support ⊆ {0,1,N} := by
  intro i hi
  contrapose! hi
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
  simp only [mem_support_iff,not_ne_iff,tri,coeff_add,coeff_monomial]
  simp [Ne.symm hi.1,Ne.symm hi.2.1,Ne.symm hi.2.2]

private theorem tri_middle (m : ℤ) (N : ℕ) (hn : 1 < N) :
    (tri m N * reflect N (tri m N)).coeff N = 1 + (m-1)^2 + m^2 := by
  have bounds (i : ℕ) (hi : i ∈ (tri m N).support) : i ≤ N := by
    have hm := tri_support m N hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hm
    omega
  have ht : (tri m N).natDegree ≤ N := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    by_contra he
    exact (not_le_of_gt hi) (bounds i (mem_support_iff.mpr he))
  rw [middleCoeff_energy _ _ ht]
  calc
    _ = ∑ i ∈ ({0,1,N} : Finset ℕ), (tri m N).coeff i ^ 2 := by
      apply Finset.sum_subset (tri_support m N)
      intro i _ he
      simp [notMem_support_iff.mp he]
    _ = _ := by
      have h0 : N ≠ 0 := by omega
      have h1 : N ≠ 1 := by omega
      simp only [tri,coeff_add,coeff_monomial]
      simp [h0,h1,Ne.symm h0,Ne.symm h1]
      ring

private theorem map_reflect_int (p : ℤ[X]) (N : ℕ) :
    (reflect N p).map (Int.castRingHom ℚ) = reflect N (p.map (Int.castRingHom ℚ)) := by
  ext i
  simp [coeff_reflect]

private theorem tri_map_int (m : ℕ) (N : ℕ) :
    (tri (m:ℤ) N).map (Int.castRingHom ℚ) = tri (m:ℚ) N := by
  simp [tri]


end

section
open Polynomial
open scoped Polynomial

private theorem sparse_factor_alternative (m N : ℕ) (hm : 2 ≤ m)
    (hN : 4^(4 + (m-1)^2 + m^2) < N)
    (g : ℤ[X]) (hg : g.natDegree ≤ N)
    (he : tri (m:ℤ) N * reflect N (tri (m:ℤ) N) = g * reflect N g) :
    tri (m:ℚ) N ∣ g.map (Int.castRingHom ℚ) ∨
      tri (m:ℚ) N ∣ reflect N (g.map (Int.castRingHom ℚ)) := by
  classical
  have hn : 1 < N := lt_of_le_of_lt (Nat.one_le_pow _ _ (by decide)) hN
  let S := insert 0 (insert 1 (insert N g.support))
  have hsub : g.support ⊆ S := by intro i hi; simp [S,hi]
  have hsN : ∀ i ∈ S, i ≤ N := by
    intro i hi
    simp only [S,Finset.mem_insert] at hi
    rcases hi with rfl|rfl|rfl|hi
    · omega
    · omega
    · rfl
    · exact (le_natDegree_of_mem_supp i hi).trans hg
  have hcard : g.support.card ≤ 1 + (m-1)^2 + m^2 := by
    have hb := support_card_le_middleCoeff g N hg
    rw [← he,tri_middle _ _ hn] at hb
    exact_mod_cast (show (g.support.card:ℤ) ≤ ((1 + (m-1)^2 + m^2 : ℕ):ℤ) by
      simpa [Nat.cast_sub (show 1 ≤ m by omega)] using hb)
  have hS : S.card ≤ 4+(m-1)^2+m^2 := by
    have ha := Finset.card_insert_le 0 (insert 1 (insert N g.support))
    have hb := Finset.card_insert_le 1 (insert N g.support)
    have hc := Finset.card_insert_le N g.support
    dsimp only [S]
    omega
  obtain ⟨d,hd,v,h0,h1,hvn,hbound,hadd⟩ :=
    compress_support N S ((Nat.pow_le_pow_right (by decide : 0 < 4) hS).trans_lt hN)
  let φ := Int.castRingHom ℚ
  have hprime : Prime (liftAxes id v (tri (m:ℚ) N)) := by
    simp only [tri,map_add,liftAxes_monomial,id_eq,h0,h1,hvn]
    simpa only [← C_mul_X_pow_eq_monomial,C_1,one_mul,pow_zero,mul_one,pow_one,map_add,
      add_assoc] using lifted_trinomial_prime m N d hm hd
  apply specialization_of_prime_lift S N d v _ _ hsN (fun i hi => hbound i (hsN i hi)) hadd _ _ _ hprime
  · intro i hi
    have hb := tri_support (m:ℚ) N hi
    simpa only [S,Finset.mem_insert] using
      (show i=0 ∨ i=1 ∨ i=N ∨ i∈g.support by
        simp only [Finset.mem_insert,Finset.mem_singleton] at hb
        tauto)
  · exact (support_map_subset φ g).trans hsub
  · have h := congrArg (Polynomial.map φ) he
    simpa only [φ,Polynomial.map_mul,tri_map_int,map_reflect_int] using h


end

open Polynomial
open scoped Polynomial
namespace CunninghamChain

private theorem jones_trinomial (m j : ℕ) :
    (X-1)*jonesSumPolynomial m j = tri (m:ℤ) (j+1) := by
  induction j with
  | zero => simp [jonesSumPolynomial,tri,← C_mul_X_pow_eq_monomial]; ring
  | succ j ih =>
    rw [jonesSumPolynomial_succ,mul_add,ih]
    simp only [tri,← C_mul_X_pow_eq_monomial, pow_succ X (j+1),C_1,one_mul]
    ring

/-- Jones's polynomial of degree j is irreducible over the rationals above an
explicit cutoff depending only on its constant term. -/
theorem jones_irreducible_of_large_degree (m j : ℕ) (hm : 2 ≤ m)
    (hgap : 4^(4+(m-1)^2+m^2) < j+1) :
    Irreducible ((jonesSumPolynomial m j).map (Int.castRingHom ℚ)) := by
  have hj : 0 < j := by
    have := Nat.one_le_pow (4+(m-1)^2+m^2) 4 (by decide)
    omega
  obtain ⟨hdeg,hmon⟩ := jonesSumPolynomial_shape m j
  have hmon := hmon hj
  apply (IsPrimitive.Int.irreducible_iff_irreducible_map_cast hmon.isPrimitive).mp
  apply hmon.irreducible_iff_natDegree.mpr
  refine ⟨fun he => by rw [he,natDegree_one] at hdeg; omega,?_⟩
  intro a b ha hb hab
  let u := 1 + a.natDegree
  let w := b.natDegree
  let A := (X-1)*a
  let N := j+1
  have hx : (X-1 : ℤ[X]) ≠ 0 := by simpa using X_sub_C_ne_zero (1:ℤ)
  have hs : u+w=N := by
    rw [← hab,natDegree_mul ha.ne_zero hb.ne_zero] at hdeg
    dsimp only [u,w,N]
    omega
  have hA : A.natDegree = u := by
    rw [show A = (X-C 1)*a by simp [A],natDegree_mul (X_sub_C_ne_zero _) ha.ne_zero,natDegree_X_sub_C]
  have ht : tri (m:ℤ) N = A*b := by rw [← jones_trinomial,← hab]; exact (mul_assoc ..).symm
  let G := A*reflect w b
  have hg : G.natDegree ≤ N := by
    rw [← hs]
    apply natDegree_mul_le.trans (Nat.add_le_add hA.le _)
    exact natDegree_reflect_le.trans (max_le le_rfl le_rfl)
  have hc : tri (m:ℤ) N * reflect N (tri (m:ℤ) N) = G * reflect N G := by
    rw [ht,←hs]
    exact swap_autocorrelation A b u w hA.le le_rfl
  have halt := sparse_factor_alternative m N hm hgap G hg hc
  let φ := Int.castRingHom ℚ
  have ht' : tri (m:ℚ) N = A.map φ*b.map φ := by
    simpa only [φ,tri_map_int,Polynomial.map_mul] using congrArg (Polynomial.map φ) ht
  have hswap : b.map φ ∣ reflect N (tri (m:ℚ) N) ∨ A.map φ ∣ reflect N (tri (m:ℚ) N) := by
    rw [ht',←hs]
    apply swap_alternative
    · exact natDegree_map_le.trans hA.le
    · exact natDegree_map_le
    · exact (Polynomial.map_ne_zero_iff (f := φ) Int.cast_injective).mpr (mul_ne_zero hx ha.ne_zero)
    · exact (hb.map φ).ne_zero
    · simpa only [φ,ht',G,Polynomial.map_mul,map_reflect_int,hs] using halt
  have hp : ((jonesSumPolynomial m j).map φ).eval 1 ≠ 0 := by
    simp [jonesSumPolynomial,Polynomial.map_sum,φ,eval_finsetSum]
    positivity
  have hm₀ : (m:ℚ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hm₁ : (m:ℚ)-1 ≠ 0 := by
    have : (2:ℚ) ≤ m := by exact_mod_cast hm
    linarith
  have aux (c : ℤ[X]) (hcf : c ∣ jonesSumPolynomial m j) (hct : c ∣ A*b)
      (hcr : c.map φ ∣ reflect N (tri (m:ℚ) N)) : c.natDegree = 0 := by
    have hu := unit_of_common_factor (m:ℚ) N (by dsimp [N]; omega) hm₀ hm₁ _ _ hp
      (Polynomial.map_dvd φ hcf) (ht' ▸ (by simpa only [Polynomial.map_mul] using Polynomial.map_dvd φ hct)) hcr
    rw [← natDegree_map_eq_of_injective (f := φ) Int.cast_injective]
    exact natDegree_eq_zero_of_isUnit hu
  rcases hswap with h|h
  · exact Or.inr (aux b (hab ▸ dvd_mul_left ..) (dvd_mul_left ..) h)
  · have haA : a ∣ A := dvd_mul_left ..
    exact Or.inl (aux a (hab ▸ dvd_mul_right ..) (haA.trans (dvd_mul_right ..))
      ((Polynomial.map_dvd φ haA).trans h))

#print axioms jones_irreducible_of_large_degree
private theorem jones_parameter_bound (t : ℕ) (ht : 3 ≤ t) :
    2 ≤ jonesConstant t ∧ t < 4^(4+(jonesConstant t-1)^2+(jonesConstant t)^2) := by
  have pow_lower (n : ℕ) : 2*(n+1) ≤ 2^(n+1) := by
    induction n with
    | zero => decide
    | succ n ih => rw [pow_succ (2:ℕ) (n+1)]; omega
  have h : 2*t ≤ 2^t := by
    obtain ⟨u,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
    exact pow_lower u
  have htm : t ≤ jonesConstant t := by unfold jonesConstant; omega
  have he : t ≤ 4+(jonesConstant t-1)^2+(jonesConstant t)^2 := by
    exact htm.trans ((Nat.le_self_pow (by decide : 2 ≠ 0) _).trans (Nat.le_add_left ..))
  have hu : t < 2^t := Nat.lt_two_pow_self
  exact ⟨by omega, hu.trans_le ((Nat.pow_le_pow_left (by decide : 2 ≤ 4) t).trans
    (Nat.pow_le_pow_right (by decide : 0 < 4) he))⟩

/-- At each Jones parameter every degree still requiring verification lies in
the displayed finite interval, for any prescribed initial degree. -/
theorem jones_irreducibility_iff_finite_check (t L : ℕ) (ht : 3 ≤ t) :
    (∀ j ≥ L, Irreducible ((jonesSumPolynomial (jonesConstant t) j).map (Int.castRingHom ℚ)) ↔ j ≠ t)
      ↔ ∀ j ∈ Finset.Ico L (4^(4+(jonesConstant t-1)^2+(jonesConstant t)^2)),
        (Irreducible ((jonesSumPolynomial (jonesConstant t) j).map (Int.castRingHom ℚ)) ↔ j ≠ t) := by
  obtain ⟨hm,htc⟩ := jones_parameter_bound t ht
  constructor
  · intro h j hj
    exact h j (Finset.mem_Ico.mp hj).1
  · intro h j hj
    by_cases he : j < 4^(4+(jonesConstant t-1)^2+(jonesConstant t)^2)
    · exact h j (Finset.mem_Ico.mpr ⟨hj,he⟩)
    · exact iff_of_true (jones_irreducible_of_large_degree _ _ hm (by omega)) (by omega)

#print axioms jones_irreducibility_iff_finite_check
private lemma all_roots_outside (m j : ℕ) (hm : 2 ≤ m) {z : ℂ}
    (hz : ((jonesSumPolynomial m j).map (Int.castRingHom ℂ)).IsRoot z) : 1 < ‖z‖ := by
  by_contra! hle
  let φ := Int.castRingHom ℂ
  have he := congrArg (fun p : ℤ[X] => (p.map φ).eval z) (jones_trinomial m j)
  change ((jonesSumPolynomial m j).map φ).eval z = 0 at hz
  have hid : 0 = z^(j+1) + ((m:ℂ)-1)*z - m := by
    simpa [φ,tri,← C_mul_X_pow_eq_monomial,Polynomial.map_sub,Polynomial.map_neg,hz,sub_eq_add_neg,
      add_mul] using he
  have hr := congrArg Complex.re hid
  simp at hr
  have hzn : (z^(j+1)).re ≤ 1 := (Complex.re_le_norm _).trans
    (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hle)
  have hzr : z.re ≤ 1 := (Complex.re_le_norm _).trans hle
  have hm' : (2:ℝ) ≤ m := by exact_mod_cast hm
  have hre : z.re = 1 := by nlinarith [mul_nonneg (show 0 ≤ (m:ℝ)-2 by linarith) (sub_nonneg.mpr hzr)]
  have him : z.im = 0 := by
    have hs := Complex.sq_norm_sub_sq_re z
    rw [hre] at hs
    nlinarith [sq_nonneg z.im,norm_nonneg z]
  have hz1 : z = 1 := Complex.ext (by simpa using hre) (by simpa using him)
  subst z
  have hn : ((m:ℂ) + j) ≠ 0 := by
    exact_mod_cast (show m+j ≠ 0 by omega)
  apply hn
  simpa [φ,jonesSumPolynomial,Polynomial.map_sum,eval_finsetSum] using hz

/-- Every positive-degree monic integral factor has constant coefficient of absolute value greater than one. -/
theorem jones_factor_constant_gt_one {m j : ℕ} (hm : 2 ≤ m) {g : ℤ[X]} (hg : g.Monic)
    (hdiv : g ∣ jonesSumPolynomial m j) (hdeg : 0 < g.natDegree) : 1 < (g.coeff 0).natAbs := by
  let G := g.map (Int.castRingHom ℂ)
  have hmon : G.Monic := hg.map _
  have hroots : G.roots ≠ 0 := by
    have hd : G.natDegree = g.natDegree := natDegree_map_eq_of_injective Int.cast_injective _
    have hs := (IsAlgClosed.splits G).natDegree_eq_card_roots
    intro h
    rw [h,Multiset.card_zero] at hs
    omega
  have hsep (z : ℂ) (hz : z ∈ G.roots) : 1 < ‖z‖ :=
    all_roots_outside m j hm ((isRoot_of_mem_roots hz).dvd (Polynomial.map_dvd _ hdiv))
  have prod_gt (s : Multiset ℂ) (hne : s ≠ 0) (h : ∀ z ∈ s, 1 < ‖z‖) : 1 < ‖s.prod‖ := by
    induction s using Multiset.induction_on with
    | empty => contradiction
    | cons z s ih =>
      have hz := h z (Multiset.mem_cons_self ..)
      have hs : 1 ≤ ‖s.prod‖ := by
        by_cases he : s=0
        · simp [he]
        · exact (ih he (fun w hw => h w (Multiset.mem_cons_of_mem hw))).le
      rw [Multiset.prod_cons,norm_mul]
      exact hz.trans_le (le_mul_of_one_le_right (norm_nonneg _) hs)
  have hnorm := congrArg norm (IsAlgClosed.splits G).coeff_zero_eq_leadingCoeff_mul_prod_roots
  simp only [hmon.leadingCoeff,norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul] at hnorm
  have hc : 1 < ‖G.coeff 0‖ := hnorm ▸ prod_gt _ hroots hsep
  change 1 < ‖(g.map _).coeff 0‖ at hc
  rw [coeff_map] at hc
  change 1 < ‖(g.coeff 0 : ℂ)‖ at hc
  rw [Complex.norm_intCast,← Int.cast_abs,← Int.natCast_natAbs] at hc
  exact_mod_cast hc

#print axioms jones_factor_constant_gt_one

private theorem six_normalized_swap (j : ℕ) (a b : ℤ[X]) (ha : a.Monic) (hb : b.Monic)
    (hab : a*b = jonesSumPolynomial 6 j) (ha₂ : (a.coeff 0).natAbs = 2) :
    ∃ g : ℤ[X], g.natDegree ≤ j+1 ∧ g.coeff 0 = 2 ∧ g.coeff (j+1) = -3 ∧
      g.eval 1 = 0 ∧ g*reflect (j+1) g = tri (6:ℤ) (j+1)*reflect (j+1) (tri (6:ℤ) (j+1)) := by
  let A := (X-1)*a
  let u := A.natDegree
  let w := b.natDegree
  let g := A*reflect w b
  have hA : A.Monic := by simpa [A] using (monic_X_sub_C (1:ℤ)).mul ha
  have hs : u+w = j+1 := by
    have h1 := (jonesSumPolynomial_shape 6 j).1
    rw [← hab,natDegree_mul ha.ne_zero hb.ne_zero] at h1
    have h2 : u = 1+a.natDegree := by
      simp only [u,A,show (X-1 : ℤ[X]) = X-C 1 by simp,
        natDegree_mul (X_sub_C_ne_zero _) ha.ne_zero,natDegree_X_sub_C]
    omega
  have ht : tri (6:ℤ) (j+1) = A*b := by
    have h : tri (6:ℤ) (j+1) = (X-1)*jonesSumPolynomial 6 j := by
      simpa using (jones_trinomial 6 j).symm
    rw [h,←hab]
    exact (mul_assoc ..).symm
  have hr : (reflect w b).natDegree ≤ w := natDegree_reflect_le.trans (max_le le_rfl le_rfl)
  have hg : g.natDegree ≤ j+1 := hs ▸ (natDegree_mul_le.trans (Nat.add_le_add_left hr u))
  have hc : g*reflect (j+1) g = tri (6:ℤ) (j+1)*reflect (j+1) (tri (6:ℤ) (j+1)) := by
    rw [ht,←hs]; exact (swap_autocorrelation A b u w le_rfl le_rfl).symm
  have hbl : b.coeff b.natDegree = 1 := hb
  have hal : A.coeff A.natDegree = 1 := hA
  have h₀ : g.coeff 0 = -a.coeff 0 := by
    simp [g,A,w,coeff_reflect,hbl]
  have hN : g.coeff (j+1) = b.coeff 0 := by
    have h := congrArg (fun p : ℤ[X] => p.coeff 0)
      (reflect_mul A (reflect w b) (F := u) (G := w) le_rfl hr)
    simpa only [hs,← show A * reflect w b = g from rfl,coeff_reflect,revAt_zero,
      reflect_reflect,mul_coeff_zero,u,hal,one_mul] using h
  have hval : g.eval 1 = 0 := by simp [g,A]
  have hab0 : a.coeff 0*b.coeff 0 = 6 := by
    have h := congrArg (fun p : ℤ[X] => p.coeff 0) hab
    simpa [jonesSumPolynomial,finsetSum_coeff,coeff_X_pow] using h
  have ha' : a.coeff 0 = 2 ∨ a.coeff 0 = -2 :=
    Int.natAbs_eq_natAbs_iff.mp (show (a.coeff 0).natAbs = (2:ℤ).natAbs from ha₂)
  rcases ha' with h|h
  · rw [h] at hab0
    refine ⟨-g,by simpa using hg,by simp [h₀,h],by simp [hN]; omega,by simp [hval],?_⟩
    simpa using hc
  · rw [h] at hab0
    exact ⟨g,hg,by simp [h₀,h],by omega,hval,hc⟩

private theorem six_irred_of_no_swap (j : ℕ) (hj : 0 < j)
    (hex : ¬∃ g : ℤ[X], g.natDegree ≤ j+1 ∧ g.coeff 0 = 2 ∧ g.coeff (j+1) = -3 ∧
      g.eval 1 = 0 ∧ g*reflect (j+1) g = tri (6:ℤ) (j+1)*reflect (j+1) (tri (6:ℤ) (j+1))) :
    Irreducible ((jonesSumPolynomial 6 j).map (Int.castRingHom ℚ)) := by
  obtain ⟨hd,hm⟩ := jonesSumPolynomial_shape 6 j
  have hmon := hm hj
  apply (IsPrimitive.Int.irreducible_iff_irreducible_map_cast hmon.isPrimitive).mp
  apply hmon.irreducible_iff_natDegree.mpr
  refine ⟨fun he => by rw [he,natDegree_one] at hd; omega,?_⟩
  intro a b ha hb hab
  by_contra! h
  have h₁ := jones_factor_constant_gt_one (by decide : 2 ≤ 6) ha (hab ▸ dvd_mul_right ..) (Nat.pos_of_ne_zero h.1)
  have h₂ := jones_factor_constant_gt_one (by decide : 2 ≤ 6) hb (hab ▸ dvd_mul_left ..) (Nat.pos_of_ne_zero h.2)
  have hab0 : a.coeff 0*b.coeff 0 = 6 := by
    have h := congrArg (fun p : ℤ[X] => p.coeff 0) hab
    simpa [jonesSumPolynomial,finsetSum_coeff,coeff_X_pow] using h
  have hc := congrArg Int.natAbs hab0
  rw [Int.natAbs_mul] at hc
  change (a.coeff 0).natAbs*(b.coeff 0).natAbs = 6 at hc
  by_cases h₃ : (a.coeff 0).natAbs = 2
  · exact hex (six_normalized_swap j a b ha hb hab h₃)
  · have h₄ : (b.coeff 0).natAbs = 2 := by
      by_contra hh
      have := Nat.mul_le_mul (by omega : 3 ≤ (a.coeff 0).natAbs) (by omega : 3 ≤ (b.coeff 0).natAbs)
      omega
    exact hex (six_normalized_swap j b a hb ha ((mul_comm ..).trans hab) h₄)

/-- A reducible Jones polynomial with constant six produces a polynomial
with normalized endpoint coefficients and the same product with its reflection
as the sparse trinomial. -/
theorem jones_six_factor_witness (j : ℕ) (hj : 0 < j)
    (hred : ¬Irreducible ((jonesSumPolynomial 6 j).map (Int.castRingHom ℚ))) :
    ∃ g : ℤ[X], g.natDegree ≤ j+1 ∧ g.coeff 0 = 2 ∧ g.coeff (j+1) = -3 ∧
      g.eval 1 = 0 ∧
      let T : ℤ[X] := X^(j+1)+5*X-6
      g*reflect (j+1) g = T*reflect (j+1) T := by
  by_contra h
  apply hred (six_irred_of_no_swap j hj ?_)
  rintro ⟨g,hd,h₀,hN,he,hg⟩
  apply h
  refine ⟨g,hd,h₀,hN,he,?_⟩
  have ht : tri (6:ℤ) (j+1) = X^(j+1)+5*X-6 := by
    norm_num [tri,← C_mul_X_pow_eq_monomial]
    ring
  simpa only [ht] using hg

#print axioms jones_six_factor_witness

end CunninghamChain
