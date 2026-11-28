import CunninghamJonesEndpointSearch
import research.arxiv.«1104.1579».CunninghamJonesComplementaryOrders

/-! Reflection of either monic factor gives a degree-independent energy identity
for Jones polynomials of arbitrary constant term. -/

namespace CunninghamChain.JonesReflection
open Polynomial
open scoped Polynomial

/-- Reverse the second factor. The resulting polynomial retains the coefficient
autocorrelations and evaluation at one, and exposes both factor constants as endpoints. -/
theorem reflected_witness {m j : ℕ} {a b : ℤ[X]} (ha : a.Monic) (hb : b.Monic)
    (hab : a*b = jonesSumPolynomial m j) :
    ∃ g : ℤ[X], g.natDegree ≤ j ∧ g.coeff 0 = a.coeff 0 ∧ g.coeff j = b.coeff 0 ∧
      g.eval 1 = (m : ℤ) + j ∧
      g * reflect j g = jonesSumPolynomial m j * reflect j (jonesSumPolynomial m j) := by
  let u := a.natDegree
  let w := b.natDegree
  let g := a * reflect w b
  have hs : u+w = j := by
    have h := (jonesSumPolynomial_shape m j).1
    rw [← hab, natDegree_mul ha.ne_zero hb.ne_zero] at h
    exact h
  have hr : (reflect w b).natDegree ≤ w := natDegree_reflect_le.trans (max_le le_rfl le_rfl)
  have hbl : b.coeff w = 1 := hb
  have hal : a.coeff u = 1 := ha
  have htop := congrArg (fun p : ℤ[X] => p.coeff 0)
    (reflect_mul a (reflect w b) (F := u) (G := w) le_rfl hr)
  have hone : (reflect w b).eval 1 = b.eval 1 := by
    let := invertibleOne (α := ℤ)
    simpa [eval₂_id] using eval₂_reflect_mul_pow (RingHom.id ℤ) (1 : ℤ) w b le_rfl
  refine ⟨g, hs ▸ natDegree_mul_le.trans (Nat.add_le_add_left hr u), ?_, ?_, ?_, ?_⟩
  · simp [g, coeff_reflect, hbl]
  · simpa only [hs, ← show a * reflect w b = g from rfl, coeff_reflect, revAt_zero,
      reflect_reflect, mul_coeff_zero, hal, one_mul] using htop
  · rw [show g.eval 1 = (a*b).eval 1 by simp [g, hone], hab]
    simp [jonesSumPolynomial, eval_finsetSum]
  · rw [← hab, ← hs, reflect_mul a b (F := u) (G := w) le_rfl le_rfl,
      show g = a * reflect w b from rfl, reflect_mul a (reflect w b) le_rfl hr, reflect_reflect]
    ring

private theorem sum_coeff_pos (m j i : ℕ) (hi : i < j) :
    (jonesSumPolynomial m j).coeff (i+1) = 1 := by
  simp [jonesSumPolynomial, finsetSum_coeff, coeff_X_pow, Finset.mem_range, hi]

private theorem corr_sum (g : ℤ[X]) (j n : ℕ) (hn : n ≤ j) :
    (g * reflect j g).coeff n =
      ∑ i ∈ Finset.range (n+1), g.coeff i * g.coeff (j-(n-i)) := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i k => g.coeff i * (reflect j g).coeff k)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [coeff_reflect, revAt_le (by omega : n-i≤j)]

theorem correlation (m j n : ℕ) (hn : n < j) :
    let p := jonesSumPolynomial m j
    (p * reflect j p).coeff n = (m : ℤ) + (n : ℤ) := by
  dsimp only
  rw [corr_sum _ _ _ hn.le]
  have top (i : ℕ) : (jonesSumPolynomial m j).coeff (j-(n-i)) = 1 := by
    obtain ⟨k,hk⟩ : ∃ k, j-(n-i)=k+1 := ⟨j-(n-i)-1, by omega⟩
    rw [hk]
    apply sum_coeff_pos
    omega
  simp_rw [top, mul_one]
  rw [Finset.sum_range_succ']
  have hu (i : ℕ) (hi : i ∈ Finset.range n) := sum_coeff_pos m j i ((Finset.mem_range.mp hi).trans hn)
  rw [Finset.sum_congr rfl hu]
  simp [jonesSumPolynomial, finsetSum_coeff, coeff_X_pow]
  ring

theorem centered_energy (m j : ℕ) (g : ℤ[X]) (hg : g.natDegree ≤ j)
    (hs : g.eval 1 = (m : ℤ) + (j : ℤ)) (hc : g * reflect j g =
      jonesSumPolynomial m j * reflect j (jonesSumPolynomial m j)) :
    ∑ i ∈ Finset.range (j+1), (g.coeff i - 1)^2 = ((m : ℤ)-1)^2 := by
  have mid (p : ℤ[X]) : (p * reflect j p).coeff j = ∑ i ∈ Finset.range (j+1), p.coeff i ^ 2 := by
    rw [corr_sum _ _ _ le_rfl]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Nat.sub_sub_self (Nat.le_of_lt_succ (Finset.mem_range.mp hi)), pow_two]
  have he := congrArg (fun p : ℤ[X] => p.coeff j) hc
  change (g*reflect j g).coeff j = _ at he
  rw [mid,mid,Finset.sum_range_succ' (f := fun i => (jonesSumPolynomial m j).coeff i ^ 2)] at he
  have hones (i : ℕ) (hi : i ∈ Finset.range j) :
      (jonesSumPolynomial m j).coeff (i+1)^2 = 1 := by rw [sum_coeff_pos _ _ _ (Finset.mem_range.mp hi)]; norm_num
  rw [Finset.sum_congr rfl hones] at he
  simp [jonesSumPolynomial, finsetSum_coeff, coeff_X_pow] at he
  rw [eval_eq_sum_range' (by omega : g.natDegree < j+1)] at hs
  simp only [one_pow, mul_one] at hs
  simp_rw [show ∀ x : ℤ, (x-1)^2=x^2-2*x+1 by intro x; ring]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, he, hs]
  simp
  ring

#print axioms reflected_witness
#print axioms correlation
#print axioms centered_energy

open JonesEndpointSearch

private theorem child_mem (p : Parameters) (hu : 0 < p.left) (hv : 0 < p.right)
    {a b : List ℤ} {budget : ℕ} {x y : ℤ}
    (hcost : (x-1).natAbs^2 + (y-1).natAbs^2 ≤ budget)
    (hxy : (p.right : ℤ)*x + p.left*y =
      (p.left : ℤ)*p.right + a.length - dot a b.reverse.tail) :
    (x::a, y::b, budget-((x-1).natAbs^2 + (y-1).natAbs^2)) ∈ children p (a,b,budget) := by
  let t : ℤ := (p.left : ℤ)*p.right + a.length - dot a b.reverse.tail
  let u : ℤ := p.left
  let v : ℤ := p.right
  let r : ℤ := budget.sqrt
  let lo := (t-u*(1+r))/v
  let hi := (t-u*(1-r))/v
  have hu' : 0 < u := by dsimp [u]; exact_mod_cast hu
  have hv' : 0 < v := by dsimp [v]; exact_mod_cast hv
  have habs : (y-1).natAbs ≤ budget.sqrt := Nat.le_sqrt'.2 (by omega)
  have hy : 1-r ≤ y ∧ y ≤ 1+r := by dsimp [r]; omega
  change v*x + u*y = t at hxy
  have hlo : lo ≤ x := by
    have h := Int.ediv_le_ediv hv' (show t-u*(1+r) ≤ v*x by nlinarith [mul_le_mul_of_nonneg_left hy.2 hu'.le])
    simpa [lo, Int.mul_ediv_cancel_left _ hv'.ne'] using h
  have hhi : x ≤ hi := by
    have h := Int.ediv_le_ediv hv' (show v*x ≤ t-u*(1-r) by nlinarith [mul_le_mul_of_nonneg_left hy.1 hu'.le])
    simpa [hi, Int.mul_ediv_cancel_left _ hv'.ne'] using h
  apply List.mem_filterMap.mpr
  refine ⟨(x-lo).toNat, List.mem_range.mpr (show (x-lo).toNat < (hi-lo+1).toNat by omega), ?_⟩
  have hnew : (t-v*x)/u = y := by rw [show t-v*x=u*y by linarith, Int.mul_ediv_cancel_left _ hu'.ne']
  change (let x' := lo + ((x-lo).toNat : ℤ)
          let y' := (t-v*x')/u
          if v*x'+u*y'=t ∧ (x'-1).natAbs^2 + (y'-1).natAbs^2 ≤ budget then
            some (x'::a,y'::b,budget-((x'-1).natAbs^2 + (y'-1).natAbs^2)) else none) = _
  simp only [show lo + ((x-lo).toNat : ℤ) = x by omega, hnew, hxy, hcost, and_self, if_true]

private def edge (v : ℕ → ℤ) (n : ℕ) : List ℤ := ((List.range n).map v).reverse

private theorem edge_step (v : ℕ → ℤ) (n : ℕ) : edge v (n+1) = v n :: edge v n := by
  simp [edge, List.range_succ]

private theorem edge_sum (v : ℕ → ℤ) (n : ℕ) : (edge v n).sum = ∑ i ∈ Finset.range n, v i := by
  induction n with
  | zero => simp [edge]
  | succ n ih => rw [edge_step, List.sum_cons, ih, Finset.sum_range_succ, add_comm]

private theorem boundary_dot {u v : ℤ} (g : ℤ[X]) (j n : ℕ) (hn : 0 < n) (hnj : n < j)
    (h₀ : g.coeff 0 = u) (h₁ : g.coeff j = v) :
    (g * reflect j g).coeff n =
      v * g.coeff n + u * g.coeff (j-n) +
      dot (edge g.coeff n) (edge (fun i => g.coeff (j-i)) n).reverse.tail := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  let coeff := g.coeff
  have hzip : (List.zipWith (·*·) (edge coeff (k+1))
      (edge (fun i => coeff (j-i)) (k+1)).reverse.tail) =
      (List.range k).map (fun i => coeff (k-i) * coeff (j-(i+1))) := by
    apply List.ext_getElem
    · simp [edge]
    · intro i hi hj
      simp [edge, List.getElem_reverse]
  have hdot : dot (edge coeff (k+1)) (edge (fun i => coeff (j-i)) (k+1)).reverse.tail =
      ∑ i ∈ Finset.range k, coeff (k-i) * coeff (j-(i+1)) := by
    rw [dot, hzip, ← edge_sum]
    simp [edge]
  rw [mul_comm,coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i l => (reflect j g).coeff i * g.coeff l)]
  have ht (i : ℕ) (hi : i ∈ Finset.range (k+1+1)) :
      (reflect j g).coeff i * g.coeff (k+1-i) = coeff (k+1-i)*coeff (j-i) := by
    rw [coeff_reflect,revAt_le (by have := Finset.mem_range.mp hi; omega : i ≤ j),mul_comm]
  rw [Finset.sum_congr rfl ht,Finset.sum_range_succ,Finset.sum_range_succ']
  change coeff 0 = u at h₀
  change coeff j = v at h₁
  change _ = v*coeff (k+1) + u*coeff (j-(k+1)) + _
  rw [hdot]
  simp only [Nat.sub_self, Nat.sub_zero, h₀, h₁, Nat.succ_sub_succ_eq_sub]
  ring

private def middleBudget (v : ℕ → ℤ) (j n : ℕ) :=
  ∑ i ∈ Finset.Ico n (j+1-n), (v i-1).natAbs^2

private theorem budget_step (v : ℕ → ℤ) {j n : ℕ} (h : 2*n+2 ≤ j+1) :
    middleBudget v j n = (v n-1).natAbs^2 + middleBudget v j (n+1) + (v (j-n)-1).natAbs^2 := by
  unfold middleBudget
  rw [show j+1-n = (j-n)+1 by omega, Finset.sum_Ico_succ_top (by omega : n ≤ j-n),
    Finset.sum_eq_sum_Ico_succ_bot (by omega : n < j-n)]
  simp

/-- The remaining squared deviations after the two endpoints have been read. -/
def initialBudget (p : Parameters) : ℕ :=
  ((p.left * p.right : ℕ)-1 : ℤ).natAbs^2 -
    ((p.left : ℤ)-1).natAbs^2 - ((p.right : ℤ)-1).natAbs^2

/-- An excluded root rules out every reflected factorization in the chosen odd
degree class except the designated degree. The two endpoint constants can be arbitrary
positive integers. The search has no presumed upper bound on polynomial degree. -/
theorem no_reflected_witness (p : Parameters) (hu : 0 < p.left) (hv : 0 < p.right)
    (cert : Excluded p ([p.left], [p.right], initialBudget p)) {j : ℕ}
    (ho : Odd j) (hm : (j+1) % p.period = p.residue) (hne : j ≠ p.exception)
    (g : ℤ[X]) (hd : g.natDegree ≤ j) (h₀ : g.coeff 0 = p.left) (h₁ : g.coeff j = p.right)
    (he : g.eval 1 = ((p.left*p.right : ℕ) : ℤ) + j) (hc : g * reflect j g =
      jonesSumPolynomial (p.left*p.right) j * reflect j (jonesSumPolynomial (p.left*p.right) j)) :
    False := by
  obtain ⟨k, hk⟩ := ho
  let m := p.left * p.right
  let v := g.coeff
  let w := fun i => v (j-i)
  let st (n : ℕ) : State := (edge v n, edge w n, middleBudget v j n)
  let Live (s : State) := ∃ n > 0, 2*n ≤ j+1 ∧ s = st n
  have advance (s : State) (hs : Live s) :
      terminal p s = true ∨ ∃ c ∈ children p s, Live c := by
    obtain ⟨n,hn,hlen,rfl⟩ := hs
    have ha : (edge v n).length = n := by simp [edge]
    by_cases hfull : 2*n = j+1
    · left
      have hrem : middleBudget v j n = 0 := by simp [middleBudget, show j+1-n=n by omega]
      have hrev : ∑ i ∈ Finset.range n, w i = ∑ i ∈ Finset.range n, v (n+i) := by
        rw [← Finset.sum_range_reflect (fun i => v (n+i)) n]
        apply Finset.sum_congr rfl
        intro i hi
        dsimp [w]
        congr 1
        have := Finset.mem_range.mp hi
        omega
      have hsum : (edge v n).sum + (edge w n).sum = ((2*n : ℕ) : ℤ) + (p.left : ℤ)*p.right-1 := by
        rw [edge_sum, edge_sum, hrev, ← Finset.sum_range_add]
        have e := he
        rw [eval_eq_sum_range' (by omega : g.natDegree < j+1)] at e
        simp only [one_pow, mul_one] at e
        rw [show n+n=j+1 by omega]
        change ∑ i ∈ Finset.range (j+1), g.coeff i = _
        rw [e, hfull]
        push_cast
        ring
      simp [st, terminal, ha, hrem, hsum, hfull, hm, hne]
    · have hg : 2*n+2 ≤ j+1 := by omega
      have hparts := budget_step v hg
      have hconv := boundary_dot g j n hn (by omega) h₀ h₁
      rw [hc,correlation _ j n (by omega)] at hconv
      have hrel : (p.right : ℤ)*v n + p.left*w n =
          (p.left : ℤ)*p.right + ((edge v n).length : ℤ) - dot (edge v n) (edge w n).reverse.tail := by
        rw [ha]
        change ((p.left*p.right : ℕ) : ℤ) + n = (p.right : ℤ)*v n + p.left*w n + _ at hconv
        push_cast at hconv
        linarith
      change middleBudget v j n = (v n-1).natAbs^2 + middleBudget v j (n+1) +
        (w n-1).natAbs^2 at hparts
      have hmemb := child_mem p hu hv (x := v n) (y := w n)
        (budget := middleBudget v j n) (by omega) hrel
      right
      refine ⟨_,hmemb,n+1,by omega,by omega,?_⟩
      simp only [st,edge_step,Prod.mk.injEq,true_and]
      omega
  have sound (s : State) (hx : Excluded p s) : ¬Live s := by
    induction hx with
    | step nt _ ih =>
      intro hl
      rcases advance _ hl with ht | ⟨c,hmemb,hl'⟩
      · simp [nt] at ht
      · exact ih c hmemb hl'
  have hE := centered_energy m j g hd he hc
  have hFull : middleBudget v j 0 = ((m : ℤ)-1).natAbs^2 := by
    unfold middleBudget
    simp only [Nat.sub_zero, Nat.Ico_zero_eq_range]
    exact_mod_cast (by simpa only [Nat.cast_sum, Nat.cast_pow, Int.natCast_natAbs, sq_abs]
      using hE : (∑ i ∈ Finset.range (j+1), ((v i-1).natAbs : ℤ)^2) = ((((m : ℤ)-1).natAbs : ℤ)^2))
  have hfirst := budget_step v (j := j) (n := 0) (by omega)
  rw [hFull] at hfirst
  simp only [Nat.zero_add, Nat.sub_zero] at hfirst
  change v 0 = p.left at h₀
  change v j = p.right at h₁
  rw [h₀,h₁] at hfirst
  have hroot : middleBudget v j 1 = initialBudget p := by
    change _ = ((m : ℤ)-1).natAbs^2 - _ - _
    rw [hfirst]
    omega
  apply sound _ cert
  refine ⟨1, by decide, by omega, ?_⟩
  simp [st,edge,List.range_succ,w,h₀,h₁,hroot]

#print axioms no_reflected_witness

end CunninghamChain.JonesReflection
