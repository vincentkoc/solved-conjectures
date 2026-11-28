import Green33WeightedPeaks
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! Uniform cyclic convolution with a rational marginal at a prime-power modulus. -/

open Finset Polynomial
open scoped Classical

namespace Green33PrimePowerBudget

private theorem separate {V : Type*} [AddCommGroup V] [Module ℚ V] (T : Module.End ℚ V)
    (D C F : ℚ[X]) (ir : Irreducible C) (ann : aeval T (D*C) = 0)
    (w : V) (flat : aeval T (D*F) w = 0) :
    aeval T (D*F) = 0 ∨ aeval T D w = 0 := by
  by_cases h : C ∣ F
  · obtain ⟨L, rfl⟩ := h
    exact Or.inl (by rw [← mul_assoc, map_mul, ann, zero_mul])
  · right
    obtain ⟨U,V',eq⟩ := (ir.isCoprime_or_dvd F).resolve_right h
    have repr : D = U*(D*C)+V'*(D*F) := by linear_combination -D*eq
    rw [repr, map_add, map_mul _ U _, map_mul _ V' _, ann, mul_zero, zero_add, Module.End.mul_apply, flat, map_zero]

private def shift (n : ℕ) : Module.End ℚ (ZMod n → ℝ) where
  toFun f z := f (z - 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem shift_pow (n j : ℕ) (f : ZMod n → ℝ) (z : ZMod n) :
    (shift n ^ j) f z = f (z - (j : ZMod n)) := by
  induction j generalizing z with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply]
    change (shift n ^ j) f (z-1) = _
    rw [ih, Nat.cast_succ]
    congr 1
    abel

private noncomputable def mask {n : ℕ} [NeZero n] (f : ZMod n → ℚ) : ℚ[X] :=
  ∑ x, monomial x.val (f x)

private theorem mask_apply {n : ℕ} [NeZero n] (f : ZMod n → ℚ) (w : ZMod n → ℝ) (z : ZMod n) :
    aeval (shift n) (mask f) w z = ∑ i, (f i : ℝ) * w (z-i) := by
  simp only [mask, map_sum, aeval_monomial, LinearMap.sum_apply, Finset.sum_apply, Module.End.mul_apply]
  apply sum_congr rfl
  intro i _
  change (f i) • ((shift n ^ i.val) w z) = _
  rw [shift_pow, ZMod.natCast_zmod_val]
  exact Rat.smul_def ..

private theorem diff_apply (n j : ℕ) (w : ZMod n → ℝ) (z : ZMod n) :
    aeval (shift n) ((X : ℚ[X]) ^ j - 1) w z = w (z-(j : ZMod n)) - w z := by
  simp [shift_pow]

/-- At the top digit of a prime power, an exactly constant convolution with one
rational marginal forces one input to be constant along every top-digit fibre. -/
theorem periodic_input {p : ℕ} [hp : Fact p.Prime] (d : ℕ)
    (f : ZMod (p^(d+1)) → ℚ) (g : ZMod (p^(d+1)) → ℝ) (c : ℝ)
    (flat : ∀ z, ∑ i, (f i : ℝ) * g (z-i) = c) :
    (∀ z, f (z - (p^d : ℕ)) = f z) ∨ (∀ z, g (z - (p^d : ℕ)) = g z) := by
  classical
  let n := p^(d+1)
  let T := shift n
  let D := (X : ℚ[X])^(p^d)-1
  let C := cyclotomic n ℚ
  have ir : Irreducible C := cyclotomic.irreducible_rat (pow_pos hp.out.pos _)
  have whole : D*C = (X : ℚ[X])^n-1 := by
    dsimp [D,C,n]
    rw [cyclotomic_prime_pow_eq_geom_sum hp.out, mul_comm, geom_sum_mul, ← pow_mul, ← pow_succ]
  have van : aeval T (D*C) = 0 := by
    rw [whole]
    apply LinearMap.ext
    intro w
    funext z
    simp only [T, diff_apply, ZMod.natCast_self, sub_zero, sub_self, LinearMap.zero_apply, Pi.zero_apply]
  have rel : aeval T (D*mask f) g = 0 := by
    rw [map_mul, Module.End.mul_apply]
    ext z
    simp only [T, D, diff_apply, mask_apply, Pi.zero_apply]
    exact sub_eq_zero.mpr ((flat _).trans (flat _).symm)
  rcases separate T D C (mask f) ir van g rel with hf | hg
  · left
    let point (x : ZMod n) : ℝ := if x = 0 then 1 else 0
    have recover (z : ZMod n) : aeval T (mask f) point z = (f z : ℝ) := by
      rw [mask_apply, sum_eq_single z]
      · simp [point]
      · intro i _ hi
        simp [point, sub_ne_zero.mpr (Ne.symm hi)]
      · simp
    intro z
    have h := congrArg (fun L : Module.End ℚ (ZMod n → ℝ) => L point z) hf
    rw [map_mul, Module.End.mul_apply, diff_apply, recover, recover] at h
    exact_mod_cast sub_eq_zero.mp h
  · right
    intro z
    have h := congrFun hg z
    simpa only [T, D, diff_apply, Pi.zero_apply, sub_eq_zero] using h

private noncomputable def push {G H K : Type*} [Fintype G] [AddCommMonoid K]
    (π : G → H) (f : G → K) (y : H) : K :=
  ∑ x, if π x = y then f x else 0

private theorem push_apply {G H K : Type*} [Fintype G] [Fintype H] [Field K]
    (π : G → H) (f : G → K) (w : H → K) :
    ∑ y, push π f y * w y = ∑ x, f x * w (π x) := by
  classical
  simp only [push, sum_mul, ite_mul, zero_mul]
  rw [sum_comm]
  simp

private theorem push_flat {G H : Type*} [Fintype G] [Fintype H] [AddCommGroup G]
    [AddCommGroup H] (π : G →+ H) (onto : Function.Surjective π)
    (f : G → ℚ) (g : G → ℝ) (c : ℝ) (flat : ∀ z, ∑ i, (f i : ℝ)*g (z-i) = c) :
    ∃ b : ℝ, ∀ z, ∑ i, ((push π f i : ℚ) : ℝ) * push π g (z-i) = b := by
  classical
  have cast (x : H) : ((push π f x : ℚ) : ℝ) = push π (fun i => (f i : ℝ)) x := by
    simp [push, Rat.cast_sum, apply_ite Rat.cast]
  have e (z : H) : ∑ i, ((push π f i : ℚ) : ℝ) * push π g (z-i) =
      ∑ t : G, if π t = z then c else 0 := by
    simp_rw [cast]
    rw [push_apply]
    conv_rhs => arg 2; ext t; rw [← flat t]
    have e (t : G) : (if π t = z then ∑ i, (f i:ℝ) * g (t-i) else 0) =
        ∑ i, if π t = z then (f i:ℝ) * g (t-i) else 0 := by
      by_cases h : π t = z <;> simp [h]
    simp_rw [e]
    rw [sum_comm (s := (univ : Finset G)) (t := (univ : Finset G)) (f := fun t i => if π t = z then (f i:ℝ)*g (t-i) else 0)]
    apply sum_congr rfl
    intro i _
    simp only [push, mul_sum, mul_ite, mul_zero]
    apply Fintype.sum_equiv (Equiv.addRight i)
    intro t
    simp only [Equiv.coe_addRight, add_sub_cancel_right, map_add]
    rw [eq_sub_iff_add_eq]
  refine ⟨∑ t : G, if π t = 0 then c else 0, fun z => (e z).trans ?_⟩
  obtain ⟨a, ha⟩ := onto z
  apply Fintype.sum_equiv (Equiv.subRight a)
  intro t
  simp only [Equiv.subRight_apply, map_sub, ha, sub_eq_zero]

/-- Every fibre of a surjective homomorphism between cyclic groups has the quotient of their orders as its size. -/
theorem fiber_count (N t p : ℕ) [NeZero N] [NeZero t] (size : N = t*p)
    (π : ZMod N →+ ZMod t) (onto : Function.Surjective π) (y : ZMod t) :
    (univ.filter fun z => π z = y).card = p := by
  classical
  have eq (z : ZMod t) : (univ.filter fun i => π i = z).card = (univ.filter fun i => π i = y).card :=
    AddMonoidHom.card_fiber_eq_of_mem_range π (onto z) (onto y)
  have s := card_eq_sum_card_fiberwise (f := π) (s := univ) (t := univ) (fun _ _ => mem_univ _)
  simp only [card_univ, ZMod.card, eq, sum_const, nsmul_eq_mul] at s
  exact Nat.eq_of_mul_eq_mul_left (NeZero.pos t) (s.symm.trans size)

/-- A weight invariant under subtraction of the smaller modulus descends to its residue classes. -/
theorem lift_equal {t N : ℕ} [NeZero t] [NeZero N] (h : t ∣ N)
    {K : Type*} (w : ZMod N → K) (period : ∀ z, w (z - (t : ZMod N)) = w z)
    {x y : ZMod N} (same : ZMod.castHom h (ZMod t) x = ZMod.castHom h (ZMod t) y) : w x = w y := by
  have eq (a : ℕ) (z : ZMod N) : w (z + (a*t : ℕ)) = w z := by
    induction a with
    | zero => simp
    | succ a ih =>
      rw [Nat.succ_mul, Nat.cast_add, ← add_assoc, ← ih]
      simpa using (period (z + (a*t : ℕ) + (t : ZMod N))).symm
  have modrep (z : ZMod N) : w z = w ((z.val % t : ℕ) : ZMod N) := by
    have e := eq (z.val / t) ((z.val % t : ℕ) : ZMod N)
    rwa [← Nat.cast_add, Nat.mul_comm _ t, Nat.mod_add_div, ZMod.natCast_zmod_val] at e
  rw [modrep x, modrep y]
  have proj (z : ZMod N) : (ZMod.castHom h (ZMod t) z).val = z.val % t := by
    conv_lhs => rw [← z.natCast_zmod_val]
    rw [map_natCast, ZMod.val_natCast]
  rw [← proj x, ← proj y, same]

private theorem push_nonneg {G H K : Type*} [Fintype G] [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (π : G → H) (w : G → K) (hw : ∀ i, 0 ≤ w i) (y : H) : 0 ≤ push π w y :=
  sum_nonneg fun i _ => ite_nonneg (hw i) le_rfl

private theorem le_push {G H K : Type*} [Fintype G] [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (π : G → H) (w : G → K) (hw : ∀ i, 0 ≤ w i) (i : G) : w i ≤ push π w (π i) := by
  classical
  simpa [push] using single_le_sum
    (f := fun j => if π j = π i then w j else 0)
    (fun j _ => ite_nonneg (hw j) le_rfl) (mem_univ i)

private theorem push_sum {G H K : Type*} [Fintype G] [Fintype H] [Field K]
    (π : G → H) (w : G → K) : ∑ i, push π w i = ∑ i, w i := by
  simpa only [mul_one] using push_apply π w (fun _ => 1)

private theorem periodic_push {N t p : ℕ} [NeZero N] [NeZero t] (size : N = t*p) (h : t ∣ N)
    {K : Type*} [Field K] (w : ZMod N → K) (period : ∀ z, w (z - (t : ZMod N)) = w z)
    (z : ZMod N) :
    push (ZMod.castHom h (ZMod t)) w (ZMod.castHom h (ZMod t) z) = (p:K)*w z := by
  classical
  let π := ZMod.castHom h (ZMod t)
  change push π w (π z) = _
  unfold push
  calc
    _ = ∑ x ∈ univ.filter (fun x => π x = π z), w x := by
      simp only [sum_filter]
      exact sum_congr rfl fun x _ => by by_cases e : π x = π z <;> simp [e]
    _ = ∑ _x ∈ univ.filter (fun x => π x = π z), w z :=
      sum_congr rfl fun x hx => lift_equal h w period (mem_filter.mp hx).2
    _ = _ := by
      rw [sum_const, nsmul_eq_mul]
      exact congrArg (fun a : ℕ => (a:K)*w z)
        (fiber_count N t p size π.toAddMonoidHom (ZMod.castHom_surjective h) (π z))

/-- The digit levels can be divided between the marginals so that every atom
is capped by the corresponding negative power of the prime. -/
theorem digit_caps {p : ℕ} [hp : Fact p.Prime] (e : ℕ)
    (f : ZMod (p^e) → ℚ) (g : ZMod (p^e) → ℝ)
    (hf : ∀ z, 0 ≤ f z) (hg : ∀ z, 0 ≤ g z)
    (c : ℝ) (flat : ∀ z, ∑ i, (f i : ℝ) * g (z-i) = c) :
    ∃ r s : ℕ, r+s=e ∧ (∀ i, (p:ℚ)^r * f i ≤ ∑ z, f z) ∧
      (∀ i, (p:ℝ)^s * g i ≤ ∑ z, g z) := by
  classical
  induction e generalizing c with
  | zero =>
    exact ⟨0, 0, rfl, fun i => by simpa using single_le_sum (fun j _ => hf j) (mem_univ i),
      fun i => by simpa using single_le_sum (fun j _ => hg j) (mem_univ i)⟩
  | succ e ih =>
    let h : p^e ∣ p^(e+1) := ⟨p, pow_succ ..⟩
    let π := ZMod.castHom h (ZMod (p^e))
    let F := push π f
    let G := push π g
    obtain ⟨b, hb⟩ := push_flat π.toAddMonoidHom (ZMod.castHom_surjective h) f g c flat
    obtain ⟨r,s,hrs,hf',hg'⟩ := ih F G (push_nonneg π f hf) (push_nonneg π g hg) b hb
    change ∀ i, (p:ℚ)^r * push π f i ≤ ∑ z, push π f z at hf'
    change ∀ i, (p:ℝ)^s * push π g i ≤ ∑ z, push π g z at hg'
    simp only [push_sum] at hf' hg'
    have leftCap (i) := (mul_le_mul_of_nonneg_left (le_push π f hf i) (by positivity : 0 ≤ (p:ℚ)^r)).trans (hf' _)
    have rightCap (i) := (mul_le_mul_of_nonneg_left (le_push π g hg i) (by positivity : 0 ≤ (p:ℝ)^s)).trans (hg' _)
    rcases periodic_input e f g c flat with hF | hG
    · refine ⟨r+1,s,by omega,?_,rightCap⟩
      intro i
      rw [pow_succ, mul_assoc, ← periodic_push (pow_succ p e) h f hF i]
      exact hf' _
    · refine ⟨r,s+1,by omega,leftCap,?_⟩
      intro i
      rw [pow_succ, mul_assoc, ← periodic_push (pow_succ p e) h g hG i]
      exact hg' _

open Green33WeightedStability Green33WeightedPeaks

private theorem total {ι : Type*} [Fintype ι] (u : PMF ι) : ∑ i, (u i).toReal = 1 := by
  have h := congrArg ENNReal.toReal u.tsum_coe
  rwa [tsum_fintype, ENNReal.toReal_sum (fun i _ => u.apply_ne_top i), ENNReal.toReal_one] at h

private theorem atom {ι G : Type*} [Fintype ι] [DecidableEq G] (u v : PMF ι)
    (obs : ι → ι → G) (z : G) : ((law u v obs) z).toReal =
      ∑ i, ∑ j, if obs i j = z then (u i).toReal * (v j).toReal else 0 := by
  classical
  have h := (observed_eq_mass u v obs {z}).symm
  simp only [mass, sum_singleton] at h
  rw [h]
  change (∑ i, ∑ j, if obs i j ∈ ({z}:Finset G) then _ else _) = _
  simp only [mem_singleton]

private theorem balanced (p : ℕ) (hp : 0 < p) (r s : ℕ) :
    p^((r+s)/2)+p^((r+s+1)/2) ≤ p^r+p^s := by
  have aux (a d : ℕ) : p^((a+(a+d))/2)+p^((a+(a+d)+1)/2) ≤ p^a+p^(a+d) := by
    have prod (i j : ℕ) (hi : 0 < i) (hj : 0 < j) : i+j ≤ 1+i*j := by
      obtain ⟨u, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi.ne'
      obtain ⟨v, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
      nlinarith
    have h := prod (p^(d/2)) (p^((d+1)/2)) (pow_pos hp _) (pow_pos hp _)
    rw [← pow_add, show d/2+(d+1)/2=d by omega] at h
    rw [show (a+(a+d))/2=a+d/2 by omega,show (a+(a+d)+1)/2=a+(d+1)/2 by omega]
    simpa only [pow_add, mul_add, mul_one] using Nat.mul_le_mul_left (p^a) h
  rcases le_total r s with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    exact aux r d
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    simpa only [add_comm (s+d) s, add_comm (p^(s+d)) (p^s)] using aux s d

/-- The minimum common label budget is bounded below by the two balanced
prime-power factors minus one, even if just the first law is rational. -/
theorem prime_power_budget {p : ℕ} [hp : Fact p.Prime] (e : ℕ)
    {ι : Type*} [Fintype ι] (l : ι → ZMod (p^e)) (P Q : PMF ι)
    (a : ι → ℚ) (rational : ∀ i, (a i : ℝ) = (P i).toReal)
    (flat : ∀ z, ((law P Q (fun i j => l i+l j)) z).toReal = ((p:ℝ)^e)⁻¹) :
    p^(e/2)+p^((e+1)/2) ≤ Fintype.card ι+1 := by
  classical
  let q (i : ι) := (Q i).toReal
  have aq (i) : 0 ≤ a i := by
    exact_mod_cast (show 0 ≤ (a i : ℝ) by rw [rational]; exact ENNReal.toReal_nonneg)
  have qpos (i) : 0 ≤ q i := ENNReal.toReal_nonneg
  have asum : ∑ i, a i = 1 := by
    exact_mod_cast (show (↑(∑ i, a i):ℝ) = 1 by push_cast; simp_rw [rational]; exact total P)
  have cast (z) : ((push l a z : ℚ):ℝ) = push l (fun i => (P i).toReal) z := by
    simp [push, Rat.cast_sum, apply_ite Rat.cast, rational]
  have prod (z) : ∑ i, ((push l a i : ℚ):ℝ)*push l q (z-i) = ((p:ℝ)^e)⁻¹ := by
    simp_rw [cast]
    rw [push_apply, ← flat z, atom]
    apply sum_congr rfl
    intro i _
    simp only [push, q, mul_sum, mul_ite, mul_zero, eq_sub_iff_add_eq, add_comm (l i)]
  obtain ⟨r,s,hrs,capA,capB⟩ := digit_caps e (push l a) (push l q)
    (push_nonneg l a aq) (push_nonneg l q qpos) _ prod
  simp only [push_sum, asum] at capA
  simp only [push_sum, q, total] at capB
  have pc (i) : (p:ℝ)^r*(P i).toReal ≤ 1 := by
    rw [←rational]
    exact_mod_cast ((mul_le_mul_of_nonneg_left (le_push l a aq i) (by positivity : 0 ≤ (p:ℚ)^r)).trans (capA _))
  have qc (i) : (p:ℝ)^s*(Q i).toReal ≤ 1 :=
    (mul_le_mul_of_nonneg_left (le_push l q qpos i) (by positivity)).trans (capB _)
  have diffuse : Diffuse P Q (fun i j => l i+l j) (Fintype.card (ZMod (p^e))) 0 := by
    intro E
    rw [observed_eq_mass, mass]
    simp only [flat, ZMod.card, Nat.cast_pow, sum_const, nsmul_eq_mul, add_zero, div_eq_mul_inv]
    exact le_rfl
  have diff := difference_atom_bound P Q l diffuse (fun z => (flat z).le) 0
  rw [ZMod.card, Nat.cast_pow, zero_mul] at diff
  have dot : ∑ i, (P i).toReal*(Q i).toReal ≤ ((p:ℝ)^e)⁻¹ := by
    have est : (∑ i, (P i).toReal*(Q i).toReal) ≤ ((law P Q (fun i j => l i-l j)) 0).toReal := by
      rw [atom]
      apply sum_le_sum
      intro i _
      simpa only [sub_self, if_true] using single_le_sum
        (f:=fun j => if l i-l j=0 then (P i).toReal*(Q j).toReal else 0)
        (fun _ _ => by positivity) (mem_univ i)
    exact est.trans (by nlinarith [sq_nonneg (((law P Q (fun i j => l i-l j)) 0).toReal-((p:ℝ)^e)⁻¹)])
  have count := sum_nonneg (s:=univ) (fun i _ => mul_nonneg (sub_nonneg.mpr (pc i)) (sub_nonneg.mpr (qc i)))
  have term (i) : (1-(p:ℝ)^r*(P i).toReal)*(1-(p:ℝ)^s*(Q i).toReal) =
      1-(p:ℝ)^r*(P i).toReal-(p:ℝ)^s*(Q i).toReal+(p:ℝ)^e*((P i).toReal*(Q i).toReal) := by
    rw [← hrs, pow_add]
    ring
  simp only [term, sum_add_distrib, sum_sub_distrib, ← mul_sum, total, mul_one,
    sum_const, card_univ, nsmul_eq_mul] at count
  have hp' : (p:ℝ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hdot := mul_le_mul_of_nonneg_left dot (by positivity : 0 ≤ (p:ℝ)^e)
  rw [mul_inv_cancel₀ (pow_ne_zero _ hp')] at hdot
  have hsum : p^r+p^s ≤ Fintype.card ι+1 := by
    exact_mod_cast (show (p:ℝ)^r+(p:ℝ)^s ≤ (Fintype.card ι:ℝ)+1 by linarith)
  exact (hrs ▸ balanced p hp.out.pos r s).trans hsum

/-- An exact weighted sum on this seed with a rational first marginal. -/
def ExactSeed (M : ℕ+) (A : Finset (ZMod M)) : Prop :=
  ∃ P Q : PMF A, (∃ a : A → ℚ, ∀ i, (a i : ℝ) = (P i).toReal) ∧
    ∀ z, ((law P Q (cyclicSum A)) z).toReal = (M.val:ℝ)⁻¹

/-- Complementary radix digits give an exact seed on any factored modulus. -/
theorem radix_exact (M : ℕ+) (t k : ℕ) (ht : 0 < t) (hk : 0 < k) (size : t*k=M.val) :
    ∃ A : Finset (ZMod M), A.card+1 ≤ t+k ∧ ExactSeed M A := by
  classical
  let _ : NeZero t := ⟨ht.ne'⟩
  let _ : NeZero k := ⟨hk.ne'⟩
  let hi (i : Fin t) : ZMod M := (k*i.val : ℕ)
  let lo (j : Fin k) : ZMod M := j.val
  let H := univ.image hi
  let L := univ.image lo
  let A := H∪L
  let h (i : Fin t) : A := ⟨hi i,mem_union_left _ (mem_image_of_mem _ (mem_univ _))⟩
  let l (j : Fin k) : A := ⟨lo j,mem_union_right _ (mem_image_of_mem _ (mem_univ _))⟩
  let U := PMF.uniformOfFintype (Fin t)
  let V := PMF.uniformOfFintype (Fin k)
  let P := U.map h
  let Q := V.map l
  let E (v : Fin t × Fin k) : ZMod M := (finProdFinEquiv v).val
  have eval (v) : (E v).val = (finProdFinEquiv v).val :=
    ZMod.val_natCast_of_lt (size ▸ (finProdFinEquiv v).isLt)
  have inj : Function.Injective E := fun x y eq =>
    finProdFinEquiv.injective (Fin.ext (by simpa only [eval] using congrArg ZMod.val eq))
  have digits (i j) : hi i + lo j = E (i,j) := by
    change ((k*i.val : ℕ):ZMod M)+(j.val:ZMod M)=((j.val+k*i.val : ℕ):ZMod M)
    push_cast
    rw [add_comm]
  have trans : law P Q (cyclicSum A) = U.bind (fun i => V.map (fun j => E (i,j))) := by
    simp only [P,Q,law,PMF.bind_map,PMF.map_comp,Function.comp_def]
    change U.bind (fun i => V.map (fun j => hi i+lo j)) = _
    simp_rw [digits]
  have flat (z) : ((law P Q (cyclicSum A)) z).toReal=(M.val:ℝ)⁻¹ := by
    rw [trans]
    have expr : (U.bind fun i => V.map (fun j => E (i,j))) z =
        ∑ v : Fin t × Fin k, if z = E v then U v.1 * V v.2 else 0 := by
      simp only [PMF.bind_apply, PMF.map_apply, tsum_fintype, mul_sum, mul_ite, mul_zero, Fintype.sum_prod_type]
    rw [expr]
    let v := finProdFinEquiv.symm (⟨z.val, size.symm ▸ z.val_lt⟩ : Fin (t*k))
    have ev : E v = z := by
      change ((finProdFinEquiv (finProdFinEquiv.symm _)).val:ZMod M) = z
      rw [Equiv.apply_symm_apply,ZMod.natCast_zmod_val]
    rw [sum_eq_single v]
    · simp [ev,U,V,PMF.uniformOfFintype_apply,ENNReal.toReal_mul,ENNReal.toReal_inv,←size,mul_comm]
    · intro w _ hw
      exact if_neg (fun e => hw (inj (e.symm.trans ev.symm)))
    · simp
  have rat (i : A) : ∃ a : ℚ, (a:ℝ) = (P i).toReal := by
    refine ⟨∑ j : Fin t, if i = h j then (t:ℚ)⁻¹ else 0,?_⟩
    change _ = ((U.map h) i).toReal
    rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum (fun j _ => by split <;> simp [U.apply_ne_top])]
    simp [U,PMF.uniformOfFintype_apply, Rat.cast_sum, apply_ite Rat.cast, apply_ite ENNReal.toReal]
  have hc : H.card ≤ t := by simpa [H] using card_image_le (f:=hi) (s:=univ)
  have lc : L.card ≤ k := by simpa [L] using card_image_le (f:=lo) (s:=univ)
  have both : (H ∩ L).Nonempty := by
    refine ⟨0,mem_inter.mpr ⟨mem_image.mpr ⟨0,mem_univ _,?_⟩,mem_image.mpr ⟨0,mem_univ _,?_⟩⟩⟩ <;> simp [hi,lo]
  have bal := card_union_add_card_inter H L
  have inter := card_pos.mpr both
  exact ⟨A, by change (H∪L).card+1 ≤ _; omega, P, Q, ⟨fun i => (rat i).choose, fun i => (rat i).choose_spec⟩, flat⟩

/-- The exact common-seed size threshold on every prime power with a rational
first marginal and an unrestricted second marginal. -/
theorem exact_budget_iff {p : ℕ} [hp : Fact p.Prime] (e b : ℕ) :
    (∃ A : Finset (ZMod (p^e)), A.card ≤ b ∧ ExactSeed ⟨p^e,pow_pos hp.out.pos e⟩ A) ↔
      p^(e/2)+p^((e+1)/2) ≤ b+1 := by
  constructor
  · rintro ⟨A,hab,P,Q,⟨a,ha⟩,flat⟩
    have flip (z) : ((law P Q (fun i j : A => i.val+j.val)) z).toReal = ((p:ℝ)^e)⁻¹ := by
      have hz := flat z
      change ((law P Q (fun i j : A => i.val+j.val)) z).toReal = ((↑(p^e : ℕ):ℝ))⁻¹ at hz
      rwa [Nat.cast_pow] at hz
    have le := prime_power_budget e (fun i : A => i.val) P Q a ha flip
    rw [Fintype.card_coe] at le
    omega
  · intro bound
    have eq : p^(e/2)*p^((e+1)/2) = p^e := by rw [← pow_add, show e/2+(e+1)/2=e by omega]
    obtain ⟨A,ha,hex⟩ := radix_exact ⟨p^e,pow_pos hp.out.pos _⟩ _ _
      (pow_pos hp.out.pos _) (pow_pos hp.out.pos _) eq
    exact ⟨A,Nat.le_of_succ_le_succ (ha.trans bound),hex⟩

/-- Arbitrary real weights on four common labels suffice at order five.
The rational-marginal threshold there is five. -/
theorem four_real_labels_mod_five : ∃ P Q : PMF (Fin 4), ∀ z : ZMod 5,
    ((law P Q (fun i j => (i.val+1 : ZMod 5)+(j.val+1 : ZMod 5))) z).toReal = 5⁻¹ := by
  classical
  let a := (5+Real.sqrt 5)/20
  let b := (5-Real.sqrt 5)/20
  have rt := Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num)
  have apos : 0 ≤ a := by dsimp [a]; positivity
  have bpos : 0 ≤ b := by dsimp [b]; nlinarith
  let F : Fin 4 → ℝ := ![a,b,b,a]
  let G : Fin 4 → ℝ := ![b,a,a,b]
  have hf (i) : 0 ≤ F i := by fin_cases i <;> first | exact apos | exact bpos
  have hg (i) : 0 ≤ G i := by fin_cases i <;> first | exact apos | exact bpos
  have sf : ∑ i, ENNReal.ofReal (F i) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hf i)]
    convert ENNReal.ofReal_one using 1
    congr 1
    simp [F,Fin.sum_univ_succ,a,b]
    ring
  have sg : ∑ i, ENNReal.ofReal (G i) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hg i)]
    convert ENNReal.ofReal_one using 1
    congr 1
    simp [G,Fin.sum_univ_succ,a,b]
    ring
  refine ⟨PMF.ofFintype _ sf, PMF.ofFintype _ sg, ?_⟩
  intro z
  rw [atom]
  simp only [PMF.ofFintype_apply, ENNReal.toReal_ofReal (hf _), ENNReal.toReal_ofReal (hg _)]
  have cells (i j : Fin 4) (y : ZMod 5) :
      (i.val+1 : ZMod 5)+(j.val+1 : ZMod 5) = y ↔ (i.val+1+j.val+1)%5 = y.val := by
    rw [← (ZMod.val_injective 5).eq_iff, ← Nat.cast_one (R := ZMod 5), ← Nat.cast_add,
      ← Nat.cast_add, ← Nat.cast_add, ZMod.val_natCast, Nat.add_assoc (i.val+1)]
  simp_rw [cells]
  fin_cases z <;> norm_num [Fin.sum_univ_succ,F,G,a,b,ZMod.val] <;> nlinarith

#print axioms periodic_input
#print axioms fiber_count
#print axioms lift_equal
#print axioms digit_caps
#print axioms prime_power_budget
#print axioms radix_exact
#print axioms exact_budget_iff
#print axioms four_real_labels_mod_five
end Green33PrimePowerBudget
