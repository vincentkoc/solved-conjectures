import research.arxiv.«1104.1579».CunninghamJonesComplementaryOrders
import research.arxiv.«1104.1579».CunninghamJonesTwentyTwoCertificate

/-! Jones's second polynomial parameter, with constant term 22. -/

namespace CunninghamChain
open Polynomial
open scoped Polynomial

private theorem reflected_witness {j : ℕ} (hj : 0 < j)
    (hred : ¬Irreducible ((jonesSumPolynomial 22 j).map (Int.castRingHom ℚ))) :
    ∃ g : ℤ[X], g.natDegree ≤ j ∧ g.coeff 0 = 2 ∧ g.coeff j = 11 ∧
      g.eval 1 = 22 + (j : ℤ) ∧
      g * reflect j g = jonesSumPolynomial 22 j * reflect j (jonesSumPolynomial 22 j) := by
  have h11 : IsPrimePow (11 : ℕ) := (by decide : Nat.Prime 11).isPrimePow
  obtain ⟨a,b,ha,hb,hab,_,ha₀,hb₀⟩ := jones_factor_two_of_prime_power h11 hj hred
  let u := a.natDegree
  let w := b.natDegree
  let g := a * reflect w b
  have hs : u+w = j := by
    have h := (jonesSumPolynomial_shape 22 j).1
    rw [← hab, natDegree_mul ha.ne_zero hb.ne_zero] at h
    exact h
  have hr : (reflect w b).natDegree ≤ w := natDegree_reflect_le.trans (max_le le_rfl le_rfl)
  norm_num at hb₀
  have hbl : b.coeff w = 1 := hb
  have hal : a.coeff u = 1 := ha
  have htop := congrArg (fun p : ℤ[X] => p.coeff 0)
    (reflect_mul a (reflect w b) (F := u) (G := w) le_rfl hr)
  have hone : (reflect w b).eval 1 = b.eval 1 := by
    let := invertibleOne (α := ℤ)
    simpa [eval₂_id] using eval₂_reflect_mul_pow (RingHom.id ℤ) (1 : ℤ) w b le_rfl
  refine ⟨g, hs ▸ natDegree_mul_le.trans (Nat.add_le_add_left hr u), ?_, ?_, ?_, ?_⟩
  · simp [g, coeff_reflect, hbl, ha₀]
  · simpa only [hs, ← show a * reflect w b = g from rfl, coeff_reflect, revAt_zero,
      reflect_reflect, mul_coeff_zero, hal, hb₀, one_mul] using htop
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

private theorem jones_corr (j n : ℕ) (hn : n < j) :
    let p := jonesSumPolynomial 22 j
    (p * reflect j p).coeff n = 22 + (n : ℤ) := by
  dsimp only
  rw [corr_sum _ _ _ hn.le]
  have top (i : ℕ) : (jonesSumPolynomial 22 j).coeff (j-(n-i)) = 1 := by
    obtain ⟨k,hk⟩ : ∃ k, j-(n-i)=k+1 := ⟨j-(n-i)-1, by omega⟩
    rw [hk]
    apply sum_coeff_pos
    omega
  simp_rw [top, mul_one]
  rw [Finset.sum_range_succ']
  have hu (i : ℕ) (hi : i ∈ Finset.range n) := sum_coeff_pos 22 j i ((Finset.mem_range.mp hi).trans hn)
  rw [Finset.sum_congr rfl hu]
  simp [jonesSumPolynomial, finsetSum_coeff, coeff_X_pow]
  ring

private theorem centered_energy (j : ℕ) (g : ℤ[X]) (hg : g.natDegree ≤ j)
    (hs : g.eval 1 = 22 + (j : ℤ)) (hc : g * reflect j g =
      jonesSumPolynomial 22 j * reflect j (jonesSumPolynomial 22 j)) :
    ∑ i ∈ Finset.range (j+1), (g.coeff i - 1)^2 = 441 := by
  have mid (p : ℤ[X]) : (p * reflect j p).coeff j = ∑ i ∈ Finset.range (j+1), p.coeff i ^ 2 := by
    rw [corr_sum _ _ _ le_rfl]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Nat.sub_sub_self (Nat.le_of_lt_succ (Finset.mem_range.mp hi)), pow_two]
  have he := congrArg (fun p : ℤ[X] => p.coeff j) hc
  change (g*reflect j g).coeff j = _ at he
  rw [mid,mid,Finset.sum_range_succ' (f := fun i => (jonesSumPolynomial 22 j).coeff i ^ 2)] at he
  have hones (i : ℕ) (hi : i ∈ Finset.range j) :
      (jonesSumPolynomial 22 j).coeff (i+1)^2 = 1 := by rw [sum_coeff_pos _ _ _ (Finset.mem_range.mp hi)]; norm_num
  rw [Finset.sum_congr rfl hones] at he
  simp [jonesSumPolynomial, finsetSum_coeff, coeff_X_pow] at he
  rw [eval_eq_sum_range' (by omega : g.natDegree < j+1)] at hs
  simp only [one_pow, mul_one] at hs
  simp_rw [show ∀ x : ℤ, (x-1)^2=x^2-2*x+1 by intro x; ring]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, he, hs]
  simp
  ring

private theorem twentyTwo_child {a b : List ℤ} {budget : ℕ} {x y : ℤ}
    (hbudget : budget ≤ 340)
    (hcost : (x-1).natAbs^2 + (y-1).natAbs^2 ≤ budget)
    (hxy : 11*x + 2*y = 22 + (a.length : ℤ) - JonesTwentyTwo.dot a b.reverse.tail) :
    (x::a, y::b, budget - ((x-1).natAbs^2 + (y-1).natAbs^2)) ∈
      JonesTwentyTwo.children (a,b,budget) := by
  let t : ℤ := 22 + (a.length : ℤ) - JonesTwentyTwo.dot a b.reverse.tail
  let l : ℤ := (t - 38) / 11
  have hyAbs : (y-1).natAbs ≤ 18 := by
    by_contra! hy
    have : 19^2 ≤ (y-1).natAbs^2 := Nat.pow_le_pow_left (by omega) 2
    omega
  have hy : -17 ≤ y ∧ y ≤ 19 := by omega
  change 11*x + 2*y = t at hxy
  have hr : 0 ≤ x-l ∧ x-l < 8 := by dsimp [l]; omega
  unfold JonesTwentyTwo.children
  apply List.mem_filterMap.mpr
  refine ⟨(x-l).toNat, List.mem_range.mpr (by omega), ?_⟩
  change (let x' := l + ((x-l).toNat : ℤ)
          let y' := (t-11*x')/2
          if 11*x'+2*y'=t ∧ (x'-1).natAbs^2 + (y'-1).natAbs^2 ≤ budget then
            some (x'::a,y'::b,budget-((x'-1).natAbs^2 + (y'-1).natAbs^2)) else none) = _
  simp only [show l + ((x-l).toNat : ℤ) = x by omega, show (t-11*x)/2 = y by omega,
    hxy,hcost, and_self, if_true]

private def edge (v : ℕ → ℤ) (n : ℕ) : List ℤ := ((List.range n).map v).reverse

private theorem edge_step (v : ℕ → ℤ) (n : ℕ) : edge v (n+1) = v n :: edge v n := by
  simp [edge, List.range_succ]

private theorem edge_sum (v : ℕ → ℤ) (n : ℕ) : (edge v n).sum = ∑ i ∈ Finset.range n, v i := by
  induction n with
  | zero => simp [edge]
  | succ n ih => rw [edge_step, List.sum_cons, ih, Finset.sum_range_succ, add_comm]

private theorem boundary_dot (g : ℤ[X]) (j n : ℕ) (hn : 0 < n) (hnj : n < j)
    (h₀ : g.coeff 0 = 2) (h₁ : g.coeff j = 11) :
    (g * reflect j g).coeff n =
      11 * g.coeff n + 2 * g.coeff (j-n) +
      JonesTwentyTwo.dot (edge g.coeff n) (edge (fun i => g.coeff (j-i)) n).reverse.tail := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  let v := g.coeff
  have hzip : (List.zipWith (·*·) (edge v (k+1))
      (edge (fun i => v (j-i)) (k+1)).reverse.tail) =
      (List.range k).map (fun i => v (k-i) * v (j-(i+1))) := by
    apply List.ext_getElem
    · simp [edge]
    · intro i hi hj
      simp [edge, List.getElem_reverse]
  have hdot : JonesTwentyTwo.dot (edge v (k+1)) (edge (fun i => v (j-i)) (k+1)).reverse.tail =
      ∑ i ∈ Finset.range k, v (k-i) * v (j-(i+1)) := by
    rw [JonesTwentyTwo.dot, hzip, ← edge_sum]
    simp [edge]
  rw [mul_comm,coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i l => (reflect j g).coeff i * g.coeff l)]
  have ht (i : ℕ) (hi : i ∈ Finset.range (k+1+1)) :
      (reflect j g).coeff i * g.coeff (k+1-i) = v (k+1-i)*v (j-i) := by
    rw [coeff_reflect,revAt_le (by have := Finset.mem_range.mp hi; omega : i ≤ j),mul_comm]
  rw [Finset.sum_congr rfl ht,Finset.sum_range_succ,Finset.sum_range_succ']
  change v 0 = 2 at h₀
  change v j = 11 at h₁
  change _ = 11*v (k+1) + 2*v (j-(k+1)) + _
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

private theorem no_twenty_two_witness (j : ℕ) (hj : j % 30 = 5) (hne : j ≠ 5)
    (g : ℤ[X]) (hd : g.natDegree ≤ j) (h₀ : g.coeff 0 = 2) (h₁ : g.coeff j = 11)
    (he : g.eval 1 = 22 + (j : ℤ)) (hc : g * reflect j g =
      jonesSumPolynomial 22 j * reflect j (jonesSumPolynomial 22 j)) : False := by
  let v := g.coeff
  let w := fun i => v (j-i)
  let st (n : ℕ) : JonesTwentyTwo.State :=
    (edge v n, edge w n, middleBudget v j n)
  let Live (s : JonesTwentyTwo.State) := ∃ n > 0, 2*n ≤ j+1 ∧ middleBudget v j n ≤ 340 ∧ s = st n
  have advance (s : JonesTwentyTwo.State) (hs : Live s) :
      JonesTwentyTwo.terminal s = true ∨ ∃ c ∈ JonesTwentyTwo.children s, Live c := by
    obtain ⟨n,hn,hlen,hb,rfl⟩ := hs
    have ha : (edge v n).length = n := by simp [edge]
    by_cases hfull : 2*n = j+1
    · left
      have hrem : middleBudget v j n = 0 := by
        simp [middleBudget, show j+1-n=n by omega]
      have hrev : ∑ i ∈ Finset.range n, w i = ∑ i ∈ Finset.range n, v (n+i) := by
        rw [← Finset.sum_range_reflect (fun i => v (n+i)) n]
        apply Finset.sum_congr rfl
        intro i hi
        dsimp [w]
        congr 1
        have := Finset.mem_range.mp hi
        omega
      have hsum : (edge v n).sum + (edge w n).sum = 2*(n : ℤ)+21 := by
        rw [edge_sum, edge_sum, hrev, ← Finset.sum_range_add]
        have e := he
        rw [eval_eq_sum_range' (by omega : g.natDegree < j+1)] at e
        simp only [one_pow, mul_one] at e
        rw [show n+n=j+1 by omega]
        change ∑ i ∈ Finset.range (j+1), g.coeff i = _
        rw [e]
        omega
      simp [st, JonesTwentyTwo.terminal, ha, hrem, hsum, show 3<n by omega,
        show (2*n)%30=6 by omega]
    · have hg : 2*n+2 ≤ j+1 := by omega
      have hparts := budget_step v hg
      have hconv := boundary_dot g j n hn (by omega) h₀ h₁
      rw [hc,jones_corr j n (by omega)] at hconv
      have hrel : 11*v n + 2*w n =
          22 + ((edge v n).length : ℤ) - JonesTwentyTwo.dot (edge v n) (edge w n).reverse.tail := by
        rw [ha]
        change 22 + (n : ℤ) = 11*v n + 2*w n + _ at hconv
        linarith
      change middleBudget v j n = (v n-1).natAbs^2 + middleBudget v j (n+1) +
        (w n-1).natAbs^2 at hparts
      have hm := twentyTwo_child hb (x := v n) (y := w n) (by omega) hrel
      right
      refine ⟨_,hm,n+1,by omega,by omega,by omega,?_⟩
      simp only [st,edge_step,Prod.mk.injEq,true_and]
      omega
  have sound (s : JonesTwentyTwo.State) (hx : JonesTwentyTwo.Excluded s) : ¬Live s := by
    induction hx with
    | step nt children ih =>
      intro hl
      rcases advance _ hl with ht | ⟨c,hm,hl'⟩
      · simp [nt] at ht
      · exact ih c hm hl'
  have hE := centered_energy j g hd he hc
  have hFull : middleBudget v j 0 = 441 := by
    unfold middleBudget
    simp only [Nat.sub_zero, Nat.Ico_zero_eq_range]
    exact_mod_cast (by simpa only [Nat.cast_sum, Nat.cast_pow, Int.natCast_natAbs, sq_abs]
      using hE : (∑ i ∈ Finset.range (j+1), ((v i-1).natAbs : ℤ)^2) = 441)
  have hfirst := budget_step v (j := j) (n := 0) (by omega)
  rw [hFull] at hfirst
  simp only [Nat.zero_add, Nat.sub_zero] at hfirst
  change v 0 = 2 at h₀
  change v j = 11 at h₁
  rw [h₀,h₁] at hfirst
  norm_num at hfirst
  have h340 : middleBudget v j 1 = 340 := by omega
  apply sound _ JonesTwentyTwo.twenty_two_certificate
  refine ⟨1,by decide,by omega,h340.le,?_⟩
  simp [st,edge,List.range_succ,w,h₀,h₁,h340]

/-- At Jones's second parameter (covering k = 2 and 3), the polynomial with constant
term 22 is reducible exactly in degree five, for all positive degrees. -/
theorem jones_second_parameter_irreducible_iff (j : ℕ) (hj : 0 < j) :
    Irreducible ((jonesSumPolynomial 22 j).map (Int.castRingHom ℚ)) ↔ j ≠ 5 := by
  have ho : Odd (5 : ℕ) := by decide
  have hp : IsPrimePow ((2^5+1)/3 : ℕ) := (by decide : Nat.Prime 11).isPrimePow
  constructor
  · rintro hi rfl
    exact ((jones_prime_power_part_range 5 5 (by decide) ho hp (by decide)
      (Or.inl (by decide))).mp hi) rfl
  · intro hne
    by_contra hred
    have hm := jones_prime_power_part_degree_class (by decide : 5≤5) ho hp hj hred
    obtain ⟨g,hd,h₀,h₁,he,hc⟩ := reflected_witness hj hred
    exact no_twenty_two_witness j (by simpa [Nat.ModEq] using hm) hne g hd h₀ h₁ he hc

#print axioms jones_second_parameter_irreducible_iff

end CunninghamChain
