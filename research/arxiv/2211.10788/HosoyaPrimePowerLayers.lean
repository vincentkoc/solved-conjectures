import LucasFibonacciIsolatedDivisors

/-! Counting prime powers by their first hit removes the square on the
Fibonacci product in the interval lcm bound. -/

namespace Arxiv.«2211.10788».FactorMass

open Finset

private lemma levels (M v : ℕ) : (∑ e∈range M, if e<v then 1 else 0) = min M v := by
  rw [←card_filter]
  have eq : (range M).filter (·<v) = range (min M v) := by ext i; simp
  rw [eq,card_range]

/-- Each level is charged once to a first hit. Every other occurrence at that
level charges a distinct positive gap from that first hit. -/
theorem layer_bound (T : Finset ℕ) (w F : ℕ → ℕ) {a L M : ℕ}
    (inside : T⊆Ico a (a+L)) (cap : ∀ t∈T, w t≤M)
    (gap : ∀ i∈T, ∀ j∈T, i<j → min (w i) (w j)≤F (j-i)) :
    ∑ t∈T, w t ≤ M + ∑ j∈Ico 1 L, F j := by
  classical
  let A (e : ℕ) := T.filter (fun t => e<w t)
  let J (e : ℕ) := (Ico 1 L).filter (fun j => e<F j)
  have per (e : ℕ) : (A e).card ≤ 1+(J e).card := by
    rcases (A e).eq_empty_or_nonempty with eq|ne
    · simp [eq]
    let t := (A e).min' ne
    have hit : t∈A e := min'_mem ..
    have h₀ := mem_filter.mp hit
    have card : ((A e).erase t).card ≤ (J e).card := by
      apply card_le_card_of_injOn (fun i => i-t)
      · intro i hi
        obtain ⟨different,hi'⟩ := mem_erase.mp hi
        have lb := (A e).min'_le i hi'
        change t ≤ i at lb
        have lt : t < i := by omega
        obtain ⟨mem,deep⟩ := mem_filter.mp hi'
        change i-t∈J e
        apply mem_filter.mpr
        have ti := mem_Ico.mp (inside h₀.1)
        have ii := mem_Ico.mp (inside mem)
        change a≤t ∧ t<a+L at ti
        exact ⟨mem_Ico.mpr ⟨by omega,by omega⟩,(lt_min h₀.2 deep).trans_le (gap t h₀.1 i mem lt)⟩
      · intro i hi j hj eq
        have li := (A e).min'_le i (mem_of_mem_erase hi)
        have lj := (A e).min'_le j (mem_of_mem_erase hj)
        change t ≤ i at li
        change t ≤ j at lj
        dsimp at eq;omega
    have := card_erase_add_one hit
    omega
  have lhs : ∑ e∈range M, (A e).card = ∑ t∈T, w t := by
    simp only [A,card_filter]
    rw [sum_comm]
    exact sum_congr rfl fun t ht => (levels M (w t)).trans (min_eq_right (cap t ht))
  have rhs : ∑ e∈range M, (J e).card ≤ ∑ j∈Ico 1 L, F j := by
    simp only [J,card_filter]
    rw [sum_comm]
    exact sum_le_sum fun j _ => (levels M (F j)).le.trans (min_le_right ..)
  have all := sum_le_sum (s:=range M) (fun e _ => per e)
  rw [lhs,sum_add_distrib] at all
  simpa only [sum_const,card_range,nsmul_eq_mul,mul_one,Nat.cast_id] using all.trans (Nat.add_le_add_left rhs _)

private theorem value_ne {f : ℕ → ℕ} (bnd : FibonacciSupportBounds f) (n : ℕ) : f n≠0 := by
  intro z
  have h := bnd.lower n
  rw [z] at h
  simp at h

private theorem gap_exponent {f : ℕ → ℕ} (bnd : FibonacciSupportBounds f) {r d i j p : ℕ}
    (hd : 0<d) (pr : p.Prime) (lt : i<j) :
    min ((f (r+d*i)).factorization p) ((f (r+d*j)).factorization p) ≤ (Nat.fib (d*(j-i))).factorization p := by
  let u (t) := f (r+d*t)
  let e := min ((u i).factorization p) ((u j).factorization p)
  let : NeZero (p^e) := ⟨pow_ne_zero _ pr.ne_zero⟩
  have di : p^e∣u i := (pow_dvd_pow p (min_le_left ..)).trans (Nat.ordProj_dvd ..)
  have dj : p^e∣u j := (pow_dvd_pow p (min_le_right ..)).trans (Nat.ordProj_dvd ..)
  have eq : (r+d*i)+d*(j-i)=r+d*j := by rw [Nat.add_assoc,←Nat.mul_add,show i+(j-i)=j by omega]
  exact (pr.pow_dvd_iff_le_factorization (Nat.fib_pos.mpr (Nat.mul_pos hd (Nat.sub_pos_of_lt lt))).ne').mp
    (bnd.common di (by simpa [eq,u] using dj))

/-- The sum of the p-adic orders in a window is bounded by any upper bound
on their maximum plus the total p-adic order of the Fibonacci gap factors. -/
theorem window_orders {f : ℕ → ℕ} (bnd : FibonacciSupportBounds f)
    (T : Finset ℕ) {r d a L M p : ℕ} (hd : 0<d) (inside : T⊆Ico a (a+L))
    (cap : ∀ t∈T, (f (r+d*t)).factorization p≤M) :
    ∑ t∈T, (f (r+d*t)).factorization p ≤ M + ∑ j∈Ico 1 L, (Nat.fib (d*j)).factorization p := by
  by_cases pr : p.Prime
  · exact layer_bound T _ _ inside cap (fun _ _ _ _ lt => gap_exponent bnd hd pr lt)
  · simp [Nat.factorization_eq_zero_of_not_prime _ pr]

/-- For any sites from a single interval, one copy of each Fibonacci gap
factor suffices alongside the lcm. This also applies to either Hosoya diagonal. -/
theorem interval_product_dvd {f : ℕ → ℕ} (bnd : FibonacciSupportBounds f)
    (T : Finset ℕ) {r d a L : ℕ} (hd : 0<d) (inside : T⊆Ico a (a+L)) :
    (∏ t∈T, f (r+d*t)) ∣ T.lcm (fun t => f (r+d*t)) * ∏ j∈Ico 1 L, Nat.fib (d*j) := by
  classical
  let u (t) := f (r+d*t)
  let g (j) := Nat.fib (d*j)
  have nz (t) : u t≠0 := value_ne bnd _
  have gnz (j) (mem : j∈Ico 1 L) : g j≠0 := (Nat.fib_pos.mpr (Nat.mul_pos hd (mem_Ico.mp mem).1)).ne'
  have lnz : T.lcm u≠0 := lcm_ne_zero_iff.mpr fun t _ => nz t
  change T.prod u ∣ T.lcm u * (Ico 1 L).prod g
  apply (Nat.factorization_le_iff_dvd (prod_ne_zero_iff.mpr fun t _ => nz t)
    (mul_ne_zero lnz (prod_ne_zero_iff.mpr gnz))).mp
  intro p
  change (T.prod u).factorization p≤(T.lcm u*(Ico 1 L).prod g).factorization p
  rw [Nat.factorization_prod_apply (fun t _ => nz t),Nat.factorization_mul lnz (prod_ne_zero_iff.mpr gnz),
    Finsupp.add_apply,Nat.factorization_prod_apply gnz]
  exact window_orders bnd T hd inside fun t mem => (Nat.factorization_le_iff_dvd (nz _) lnz).mpr (dvd_lcm mem) p

#print axioms window_orders
#print axioms layer_bound
#print axioms interval_product_dvd

end Arxiv.«2211.10788».FactorMass
