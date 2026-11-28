import HosoyaProjectivePowerFibers
import HosoyaProjectiveRoots

/-! Projective roots of the upper Hosoya index form at split ordinary primes. -/


namespace Arxiv.«2211.10788»

private def lineEval {K : Type*} [Field K] (a : K) : Option K → K
  | none => 1
  | some x => x+a

private lemma line_nonzero {K : Type*} [Field K] {a b : K} (hab : a≠b) {t : Kˣ}
    {z : Option K} {d : ℕ} (hd : 0<d)
    (hz : lineEval a z ^ d = (t:K) * lineEval b z ^ d) :
    lineEval a z ≠ 0 ∧ lineEval b z ≠ 0 := by
  cases z with
  | none => simp [lineEval]
  | some x =>
    simp only [lineEval] at hz ⊢
    have nn : ¬(x+a=0 ∧ x+b=0) := fun ⟨ha,hb⟩ => hab (add_left_cancel (ha.trans hb.symm))
    constructor
    · intro h
      rw [h,zero_pow hd.ne'] at hz
      exact nn ⟨h,(pow_eq_zero_iff hd.ne').mp ((mul_eq_zero.mp hz.symm).resolve_left t.ne_zero)⟩
    · intro h
      rw [h,zero_pow hd.ne',mul_zero] at hz
      exact nn ⟨(pow_eq_zero_iff hd.ne').mp hz,h⟩

private noncomputable def lineInverse {K : Type*} [Field K] (a b u : K) : Option K :=
  open Classical in if u=1 then none else some ((a-u*b)/(u-1))

private lemma line_inverse_ratio {K : Type*} [Field K] {a b : K} (hab : a≠b) (u : K) :
    lineEval b (lineInverse a b u) ≠ 0 ∧
      lineEval a (lineInverse a b u) / lineEval b (lineInverse a b u) = u := by
  classical
  by_cases h : u=1
  · simp [lineInverse,h,lineEval]
  · simp only [lineInverse,if_neg h,lineEval]
    have hd := sub_ne_zero.mpr h
    have he : (a-u*b)/(u-1)+b=(a-b)/(u-1) := by field_simp; ring
    rw [he]
    refine ⟨div_ne_zero (sub_ne_zero.mpr hab) hd,?_⟩
    field_simp [sub_ne_zero.mpr hab,hd]
    ring

private lemma line_ratio_inverse {K : Type*} [Field K] {a b : K} (hab : a≠b)
    (z : Option K) (hb : lineEval b z≠0) :
    lineInverse a b (lineEval a z / lineEval b z)=z := by
  classical
  cases z with
  | none => simp [lineEval,lineInverse]
  | some x =>
    change x+b≠0 at hb
    have hn : (x+a)/(x+b)≠1 := by
      intro h
      exact hab (add_left_cancel (by simpa using (div_eq_iff hb).mp h : x+a=x+b))
    have he (v : K) (hv : v≠1) : lineInverse a b v=some ((a-v*b)/(v-1)) := if_neg hv
    change lineInverse a b ((x+a)/(x+b))=some x
    rw [he _ hn,Option.some.injEq]
    apply (div_eq_iff (sub_ne_zero.mpr hn)).mpr
    field_simp
    ring

/-- The two distinct linear forms on the projective line turn the power
equation into a fiber of the power map on the multiplicative group. -/
private noncomputable def linePowerEquiv {K : Type*} [Field K] {a b : K} (hab : a≠b)
    (t : Kˣ) {d : ℕ} (hd : 0<d) :
    {z : Option K // lineEval a z ^ d=(t:K)*lineEval b z ^ d} ≃ {u : Kˣ // u^d=t} where
  toFun z := by
    have ha := (line_nonzero hab hd z.2).1
    have hb := (line_nonzero hab hd z.2).2
    refine ⟨Units.mk0 _ (div_ne_zero ha hb),Units.ext ?_⟩
    change (lineEval a z.val / lineEval b z.val)^d=(t:K)
    exact (div_pow ..).trans ((div_eq_iff (pow_ne_zero _ hb)).mpr z.2)
  invFun u := by
    have hb := (line_inverse_ratio hab (u.val:K)).1
    have hu := (line_inverse_ratio hab (u.val:K)).2
    refine ⟨lineInverse a b (u.val:K),?_⟩
    apply (div_eq_iff (pow_ne_zero d hb)).mp
    rw [← div_pow,hu]
    exact_mod_cast u.2
  left_inv z := by
    apply Subtype.ext
    exact line_ratio_inverse hab z.val (line_nonzero hab hd z.2).2
  right_inv u := by
    apply Subtype.ext
    apply Units.ext
    exact (line_inverse_ratio hab (u.val:K)).2

private theorem upper_conjugates {K : Type*} [Field K] {a b : K}
    (ha : a^2=a+1) (hb : b^2=b+1) (r : ℕ) :
    (a-b)*(lucasFibonacciSum r : K)=(3+a)*a^r-(3+b)*b^r := by
  induction r using Nat.twoStepInduction with
  | zero => simp [lucas_fibonacci_sum_zero]
  | one =>
    rw [lucas_fibonacci_sum_one]
    push_cast
    linear_combination -ha+hb
  | more r h₀ h₁ =>
    rw [lucas_fibonacci_sum_recurrence,Nat.cast_add,mul_add,h₁,h₀,pow_add a r 2,pow_add b r 2,ha,hb]
    rw [pow_succ,pow_succ]
    ring

/-- Evaluate the upper index form at the two Fibonacci characteristic roots. -/
theorem upper_form_conjugates {K : Type*} [Field K] {a b : K}
    (ha : a^2=a+1) (hb : b^2=b+1) (x y : K) (r d : ℕ) :
    (a-b)*upperIndexForm x y d r =
      ((3+a)*a^r)*(x+a*y)^d-((3+b)*b^r)*(x+b*y)^d := by
  induction d generalizing r with
  | zero => simpa only [upperIndexForm,pow_zero,mul_one] using upper_conjugates ha hb r
  | succ d ih =>
    rw [upperIndexForm,show (a-b)*(x*upperIndexForm x y d r+y*upperIndexForm x y d (r+1))=
        x*((a-b)*upperIndexForm x y d r)+y*((a-b)*upperIndexForm x y d (r+1)) by ring,ih,ih]
    rw [pow_succ a,pow_succ b,pow_succ (x+a*y),pow_succ (x+b*y)]
    ring

/-- For split ordinary primes the number of projective roots equals either zero
or the common divisor of the step and the split multiplicative group order. -/
theorem upperProjectiveRootCount_split {p : ℕ} [Fact p.Prime] (hp₅ : p≠5) (hp₁₁ : p≠11)
    {a : ZMod p} (ha : a^2=a+1) (r d : ℕ) (hd : 0<d) :
    let b := 1-a
    let g := (p-1).gcd d
    let e := (p-1)/g
    upperProjectiveRootCount p r d =
      if ((3+b)*b^r)^e=((3+a)*a^r)^e then g else 0 := by
  classical
  let b := 1-a
  let A := (3+a)*a^r
  let B := (3+b)*b^r
  let g := (p-1).gcd d
  let e := (p-1)/g
  change upperProjectiveRootCount p r d = if B^e=A^e then g else 0
  have nz (ℓ : ℕ) (hℓ : ℓ.Prime) (hne : p≠ℓ) : (ℓ:ZMod p)≠0 :=
    (ZMod.natCast_eq_zero_iff ..).not.mpr ((Nat.prime_dvd_prime_iff_eq Fact.out hℓ).not.mpr hne)
  have h5 : (5:ZMod p)≠0 := nz 5 (by decide) hp₅
  have h11 : (11:ZMod p)≠0 := nz 11 (by decide) hp₁₁
  have hb : b^2=b+1 := by dsimp [b]; linear_combination ha
  have h₁ : a*b=(-1) := by dsimp [b]; linear_combination -ha
  have h₂ : (3+a)*(3+b)=11 := by dsimp [b]; linear_combination -ha
  have hab : a≠b := by
    have he : (a-b)^2=5 := by dsimp [b]; linear_combination 4*ha
    intro h
    exact h5 (by simpa [h] using he.symm)
  have h₁' : a*b≠0 := by rw [h₁]; exact neg_ne_zero.mpr one_ne_zero
  have h₂' : (3+a)*(3+b)≠0 := h₂ ▸ h11
  have hA : A≠0 := mul_ne_zero (left_ne_zero_of_mul h₂') (pow_ne_zero _ (left_ne_zero_of_mul h₁'))
  have hB : B≠0 := mul_ne_zero (right_ne_zero_of_mul h₂') (pow_ne_zero _ (right_ne_zero_of_mul h₁'))
  let t : (ZMod p)ˣ := Units.mk0 (B/A) (div_ne_zero hB hA)
  have hit (z : Option (ZMod p)) :
      upperIndexForm (upperIndexChart z).1 (upperIndexChart z).2 d r=0 ↔
      lineEval a z ^ d = (t:ZMod p)*lineEval b z ^ d := by
    let x := (upperIndexChart z).1
    let y := (upperIndexChart z).2
    have line (s : ZMod p) : lineEval s z=x+s*y := by cases z <;> simp [x,y,upperIndexChart,lineEval]
    rw [line a,line b]
    change upperIndexForm x y d r=0 ↔ (x+a*y)^d=(B/A)*(x+b*y)^d
    rw [← mul_right_inj' (sub_ne_zero.mpr hab),mul_zero,upper_form_conjugates ha hb,sub_eq_zero]
    change A*(x+a*y)^d=B*(x+b*y)^d ↔ _
    field_simp
  have hc : Nat.card (ZMod p)ˣ=p-1 := by rw [Nat.card_units,Nat.card_zmod]
  have ht : t^e=1 ↔ B^e=A^e := by
    rw [← Units.val_inj]
    change (B/A)^e=1 ↔ _
    rw [div_pow,div_eq_iff (pow_ne_zero _ hA),one_mul]
  unfold upperProjectiveRootCount
  rw [←Fintype.card_subtype,←Nat.card_eq_fintype_card]
  rw [Nat.card_congr ((Equiv.subtypeEquivRight hit).trans (linePowerEquiv hab t hd)),cyclic_power_fiber_card,hc]
  have ht' : t^((p-1)/(p-1).gcd d)=1 ↔ B^e=A^e := ht
  simp only [ht']
  rfl

#print axioms upperProjectiveRootCount_split

end Arxiv.«2211.10788»
