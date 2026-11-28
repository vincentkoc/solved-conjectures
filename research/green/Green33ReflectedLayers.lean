import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic
import Green33SidonProfile
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Ring.AddAut

/-! Reflected pairs of cyclic Sidon layers in the Green 33 problem. -/

open Finset
open scoped Pointwise

namespace Green33ReflectedLayers

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- The translate sum, acting on real functions on the ambient group. -/
def walk (A : Finset G) (f : G → ℝ) (x : G) : ℝ := ∑ a ∈ A, f (x-a)

open Green33TailEnergy (diffReps)

private def corr (f : G → ℝ) (t : G) : ℝ := ∑ x, f x * f (x+t)

omit [DecidableEq G] in
private lemma sum_shift (f : G → ℝ) (t : G) : ∑ x, f (x+t) = ∑ x, f x :=
  Equiv.sum_comp (Equiv.addRight t) f

omit [DecidableEq G] in
private lemma sum_sub_shift (f : G → ℝ) (t : G) : ∑ x, f (x-t) = ∑ x, f x := by
  simpa only [sub_eq_add_neg] using sum_shift f (-t)

omit [DecidableEq G] in
private lemma corr_bound (f : G → ℝ) (t : G) : |corr f t| ≤ ∑ x, f x ^ 2 := by
  calc
    |corr f t| ≤ ∑ x, |f x * f (x+t)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, (f x ^ 2 + f (x+t) ^ 2)/2 := by
      apply sum_le_sum
      intro x _
      rw [abs_mul]
      have h := two_mul_le_add_sq |f x| |f (x+t)|
      rw [sq_abs,sq_abs] at h
      linarith
    _ = _ := by
      rw [← sum_div,sum_add_distrib,sum_shift (fun x => f x ^ 2) t]
      ring

omit [DecidableEq G] in
private lemma total_corr (f : G → ℝ) (hf : ∑ x, f x = 0) : ∑ t, corr f t = 0 := by
  unfold corr
  rw [sum_comm]
  apply sum_eq_zero
  intro x _
  rw [← mul_sum]
  have h := sum_shift f x
  simp only [add_comm x, h, hf, mul_zero]

private lemma fiber_sum (A : Finset G) (w : G → ℝ) :
    ∑ t, (diffReps A t : ℝ) * w t = ∑ a ∈ A, ∑ b ∈ A, w (a-b) := by
  classical
simp only [diffReps, card_eq_sum_ones, Nat.cast_sum, sum_mul, sum_filter]
  rw [sum_comm]
  simp [sum_product]

private lemma walk_energy (A : Finset G) (f : G → ℝ) :
    ∑ x, walk A f x ^ 2 = ∑ t, (diffReps A t : ℝ) * corr f t := by
  have pair (a b : G) : ∑ x, f (x-a)*f (x-b) = corr f (a-b) := by
    calc
      _ = ∑ x, (fun y => f y * f (y+(a-b))) (x-a) := by
        apply sum_congr rfl
        intro x _
        dsimp
        rw [show x-a+(a-b) = x-b by abel]
      _ = _ := sum_sub_shift (fun y => f y * f (y+(a-b))) a
  rw [fiber_sum]
  simp only [walk, sq, sum_mul, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  rw [sum_comm]
  exact sum_congr rfl (fun b _ => by simpa only [mul_comm] using pair a b)

/-- An elementary mean-zero translate bound from the deviation of the
difference counts from one. The group may have even order. -/
theorem walk_energy_bound (A : Finset G) (f : G → ℝ) (hf : ∑ x, f x=0) :
    ∑ x, walk A f x ^ 2 ≤ (∑ t, |(diffReps A t : ℝ)-1|) * ∑ x, f x ^ 2 := by
  rw [walk_energy]
  have h : ∑ t, ((diffReps A t : ℝ)-1)*corr f t = ∑ t, (diffReps A t : ℝ)*corr f t := by
    simp only [sub_mul,one_mul,sum_sub_distrib,total_corr f hf,sub_zero]
  rw [← h,sum_mul]
  apply sum_le_sum
  intro t _
  calc
    _ ≤ |((diffReps A t : ℝ)-1)*corr f t| := le_abs_self _
    _ ≤ _ := by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (corr_bound f t) (abs_nonneg _)

omit [DecidableEq G] in
private lemma total_walk (A : Finset G) (f : G → ℝ) : ∑ x, walk A f x = A.card * ∑ y, f y := by
  unfold walk
  rw [sum_comm]
  simp only [sum_sub_shift, sum_const, nsmul_eq_mul]

/-- Number of ordered r-term sums of elements of A with a given total. -/
noncomputable def paths (A : Finset G) : ℕ → G → ℝ
  | 0 => fun x => if x=0 then 1 else 0
  | r+1 => walk A (paths A r)

private lemma total_paths (A : Finset G) (r : ℕ) : ∑ x, paths A r x = (A.card : ℝ)^r := by
  induction r with
  | zero => simp [paths]
  | succ r ih => rw [paths,total_walk,ih,pow_succ,mul_comm]

private noncomputable def variance (A : Finset G) (r : ℕ) : ℝ :=
  ∑ x, (paths A r x - (A.card : ℝ)^r / Fintype.card G)^2

private lemma variance_step (A : Finset G) (r : ℕ) :
    variance A (r+1) ≤ (∑ t, |(diffReps A t : ℝ)-1|) * variance A r := by
  let k : ℝ := A.card
  let m : ℝ := Fintype.card G
  have hm : 0 < m := by dsimp [m]; exact_mod_cast Fintype.card_pos
  let g := fun x => paths A r x - k^r/m
  have hz : ∑ x, g x=0 := by
    simp only [g,sum_sub_distrib,total_paths,sum_const,nsmul_eq_mul]
    change k^r - m*(k^r/m)=0
    field_simp
    ring
  have step (x : G) : paths A (r+1) x - k^(r+1)/m = walk A g x := by
    simp only [paths,walk,g,sum_sub_distrib,sum_const,nsmul_eq_mul,pow_succ]
    change _ - k^r*k/m = _ - k*(k^r/m)
    ring
  change ∑ x, (paths A (r+1) x-k^(r+1)/m)^2 ≤ _
  simp only [step]
  exact walk_energy_bound A g hz

/-- The r-fold sum counts have variance controlled by the r-th power of
the total absolute discrepancy of the ordered difference counts from one. -/
theorem path_variance (A : Finset G) (r : ℕ) :
    ∑ x, (paths A r x - (A.card : ℝ)^r / Fintype.card G)^2 ≤
      (∑ t, |(diffReps A t : ℝ)-1|)^r := by
  let m : ℝ := Fintype.card G
  have hm : 0 < m := by dsimp [m]; exact_mod_cast Fintype.card_pos
  let k : ℝ := A.card
  let D := ∑ t, |(diffReps A t : ℝ)-1|
  change ∑ x, (paths A r x - k^r/m)^2 ≤ D^r
  induction r with
  | zero =>
    have pt (x : G) : (paths A 0 x-1/m)^2 = (if x=0 then 1-2/m else 0) + (1/m)^2 := by
      by_cases h : x=0
      · simp [paths,h]; ring
      · simp [paths,h]
    simp only [pow_zero,pt,sum_add_distrib,sum_ite_eq',mem_univ,if_true,sum_const,nsmul_eq_mul]
    change 1-2/m + m*(1/m)^2 ≤ 1
    field_simp
    nlinarith
  | succ r ih =>
    rw [pow_succ' D]
    exact (variance_step A r).trans (mul_le_mul_of_nonneg_left ih (sum_nonneg fun _ _ => abs_nonneg _))

omit [Fintype G] in
private lemma sidon_diff_le {A : Finset G} (hA : IsSidon (A : Set G)) {z : G} (hz : z ≠ 0) :
    diffReps A z ≤ 1 := by
  apply card_le_one.mpr
  rintro ⟨a,b⟩ hab ⟨u,v⟩ huv
  obtain ⟨⟨ha,hb⟩,hs⟩ := (mem_filter.trans (and_congr_left fun _ => mem_product)).mp hab
  obtain ⟨⟨hu,hv⟩,ht⟩ := (mem_filter.trans (and_congr_left fun _ => mem_product)).mp huv
  have h : a+v=u+b := sub_eq_sub_iff_add_eq_add.mp (hs.trans ht.symm)
  rcases hA a ha u hu v hv b hb h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · rfl
  · simp_all

omit [Fintype G] in
private lemma diff_zero (A : Finset G) : diffReps A 0 = A.card := by
  change ((A ×ˢ A).filter fun p => p.1-p.2=0).card = A.card
  rw [show ((A ×ˢ A).filter fun p => p.1-p.2=0) = A.diag by ext p; simp [Finset.mem_diag]; grind]
  simp

private lemma sidon_discrepancy {A : Finset G} (hA : IsSidon (A : Set G)) (hne : A.Nonempty) :
    ∑ t, |(diffReps A t : ℝ)-1| = Fintype.card G - (A.card : ℝ)^2 + 2*A.card - 2 := by
  have hzero := diff_zero A
  have each (t : G) : |(diffReps A t : ℝ)-1| =
      1 - diffReps A t + (if t=0 then 2*(A.card : ℝ)-2 else 0) := by
    by_cases h : t=0
    · subst t
      have hk : (1:ℝ) ≤ A.card := by exact_mod_cast hne.card_pos
      rw [hzero,abs_of_nonneg (by linarith),if_pos rfl]
      ring
    · have hd : (diffReps A t : ℝ) ≤ 1 := by exact_mod_cast sidon_diff_le hA h
      rw [abs_of_nonpos (by linarith),if_neg h]; ring
  have total := fiber_sum A (fun _ => 1)
  simp only [mul_one,sum_const,nsmul_eq_mul,mul_one] at total
  simp only [each,sum_add_distrib,sum_sub_distrib,sum_const,nsmul_eq_mul,mul_one,
    sum_ite_eq',mem_univ,if_true,total,sq,card_univ]
  ring

omit [Fintype G] in
private lemma paths_affine {H : Type*} [AddCommGroup H] [DecidableEq H]
    (A : Finset G) (e : G ≃+ H) (s : H) (r : ℕ) (x : G) :
    paths (A.image (fun a => e a+s)) r (e x+r • s) = paths A r x := by
  classical
  induction r generalizing x with
  | zero => simp [paths]
  | succ r ih =>
    rw [paths,paths,walk,walk,sum_image (by intro a _ b _ h; exact e.injective (add_right_cancel h))]
    apply sum_congr rfl
    intro a _
    rw [show e x+(r+1) • s-(e a+s)= e (x-a)+r • s by rw [map_sub,succ_nsmul]; abel]
    exact ih (x-a)

private def mark (A : Finset G) (x : G) : ℝ := if x∈A then 1 else 0

omit [AddCommGroup G] in
private lemma total_mark (A : Finset G) : ∑ x, mark A x = A.card := by
  classical
  simp [mark]

private def diagonals (A : Finset G) := A.image (fun a => a+a)

omit [Fintype G] in
private lemma pair_profile {A : Finset G} (hA : IsSidon (A : Set G)) (x : G) :
    (Green33Multiplicity.reps A x : ℝ) = 2*mark (A+A) x - mark (diagonals A) x := by
  classical
  by_cases hx : x∈A+A
  · obtain ⟨a,ha,b,hb,hs⟩ := mem_add.mp hx
    let P := ((A ×ˢ A).filter fun p => p.1+p.2=x)
    have hp : P = {(a,b),(b,a)} := by
      ext ⟨u,v⟩
      simp only [P,mem_filter,mem_product,mem_insert,mem_singleton,Prod.mk.injEq]
      constructor
      · rintro ⟨⟨hu,hv⟩,he⟩
        exact hA u hu a ha v hv b hb (he.trans hs.symm)
      · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
        · exact ⟨⟨ha,hb⟩,hs⟩
        · exact ⟨⟨hb,ha⟩,(add_comm _ _).trans hs⟩
    change (P.card : ℝ) = _
    rw [hp]
    by_cases h : a=b
    · subst b
      have hd : x∈diagonals A := mem_image.mpr ⟨a,ha,hs⟩
      norm_num [mark,hx,hd]
    · have hd : x∉diagonals A := by
        rintro hh
        obtain ⟨d,hd,he⟩ := mem_image.mp hh
        rcases hA a ha d hd b hb d hd (hs.trans he.symm) with hh | hh <;> exact h (hh.1.trans hh.2.symm)
      simp [mark,hx,hd,h]
  · have hd : x∉diagonals A := fun h => by
      obtain ⟨d,hd,rfl⟩ := mem_image.mp h
      exact hx (add_mem_add hd hd)
    have hp : ((A ×ˢ A).filter fun p => p.1+p.2=x) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      rintro ⟨a,b⟩ hh
      obtain ⟨⟨ha,hb⟩,he⟩ := (mem_filter.trans (and_congr_left fun _ => mem_product)).mp hh
      exact hx (he ▸ add_mem_add ha hb)
    simp [Green33Multiplicity.reps,hp,mark,hx,hd]

private lemma sum_fiber (A : Finset G) (w : G → ℝ) :
    ∑ x, (Green33Multiplicity.reps A x : ℝ)*w x = ∑ a ∈ A, ∑ b ∈ A, w (a+b) := by
  simp only [Green33Multiplicity.reps,card_eq_sum_ones,Nat.cast_sum,sum_mul,sum_filter]
  rw [sum_comm]; simp [sum_product]

private lemma two_walks (A : Finset G) (f : G → ℝ) (x : G) :
    walk A (walk A f) x = ∑ y, (Green33Multiplicity.reps A y : ℝ)*f (x-y) := by
  rw [sum_fiber]
  unfold walk
  exact sum_congr rfl (fun a _ => sum_congr rfl (fun b _ => congrArg f (by abel)))

private lemma paths_two (A : Finset G) (x : G) : paths A 2 x = Green33Multiplicity.reps A x := by
  change walk A (walk A (paths A 0)) x = _
  rw [two_walks]
  simp [paths,sub_eq_zero]

private lemma paths_four (A : Finset G) (x : G) : paths A 4 x =
    ∑ y, (Green33Multiplicity.reps A y : ℝ)*Green33Multiplicity.reps A (x-y) := by
  change walk A (walk A (paths A 2)) x = _
  rw [two_walks]
  simp only [paths_two]

private lemma sidon_sum_size {A : Finset G} (hA : IsSidon (A : Set G)) :
    2*(A+A).card = A.card^2+A.card := by
  have hdiag : (diagonals A).card = A.card := by
    apply card_image_of_injOn
    intro x hx y hy he
    rcases hA x hx y hy x hx y hy he with h | h <;> exact h.1
  have h := total_paths A 2
  simp only [paths_two,pair_profile hA,sum_sub_distrib,← mul_sum,total_mark,hdiag] at h
  exact_mod_cast (show 2*((A+A).card : ℝ)=(A.card : ℝ)^2+A.card by linarith)

private lemma two_walk_overlap {A : Finset G} (hA : IsSidon (A : Set G)) (z : G) :
    let S := A+A
    let I := S.filter (fun x => z-x∈S)
    paths A 4 z ≤ 4*I.card ∧ 4*(I.card : ℝ) ≤ paths A 4 z + 4*A.card := by
  classical
  let S := A+A
  let D := diagonals A
  let I := S.filter fun x => z-x∈S
  have hm (x : G) : mark S x*mark S (z-x) = mark I x := by
    by_cases h : x∈S <;> by_cases h' : z-x∈S <;> simp [mark,I,h,h']
  have bounds (E : Finset G) (x : G) : 0 ≤ mark E x ∧ mark E x ≤ 1 := by
    by_cases h : x∈E <;> simp [mark,h]
  have pt (x : G) : let f := fun w => (Green33Multiplicity.reps A w : ℝ)
      0 ≤ 4*mark I x - f x * f (z-x) ∧
      4*mark I x - f x * f (z-x) ≤ 2*(mark D x+mark D (z-x)) := by
    dsimp only
    have h₁ := pair_profile hA x
    have h₂ := pair_profile hA (z-x)
    change _ = 2*mark S x - mark D x at h₁
    change _ = 2*mark S (z-x) - mark D (z-x) at h₂
    rw [← hm,h₁,h₂]
    have n₁ : 0 ≤ 2*mark S x-mark D x := h₁ ▸ Nat.cast_nonneg _
    have n₂ : 0 ≤ 2*mark S (z-x)-mark D (z-x) := h₂ ▸ Nat.cast_nonneg _
    obtain ⟨d₁,_⟩ := bounds D x
    obtain ⟨d₂,_⟩ := bounds D (z-x)
    obtain ⟨s₁,u₁⟩ := bounds S x
    obtain ⟨s₂,u₂⟩ := bounds S (z-x)
    constructor
    · nlinarith only [mul_nonneg n₁ d₂,mul_nonneg d₁ s₂]
    · nlinarith only [mul_nonneg (sub_nonneg.mpr u₁) d₂,mul_nonneg (sub_nonneg.mpr u₂) d₁,mul_nonneg d₁ d₂]
  have sd : ∑ x, mark D (z-x) = D.card := by
    have h := Equiv.sum_comp (Equiv.subLeft z) (mark D)
    exact h.trans (total_mark D)
  have lo := sum_nonneg (s := (univ : Finset G)) (fun x _ => (pt x).1)
  have hi := sum_le_sum (s := (univ : Finset G)) (fun x _ => (pt x).2)
  simp only [sum_sub_distrib,← mul_sum,← paths_four,total_mark,sum_add_distrib,sd] at lo hi
  have hcard : (D.card : ℝ) ≤ A.card := by exact_mod_cast (card_image_le (f := fun x : G => x+x) (s := A))
  change paths A 4 z ≤ 4*(I.card : ℝ) ∧ 4*(I.card : ℝ) ≤ _
  exact ⟨by linarith,by linarith⟩

/-- A nonempty Sidon seed realizes each nonzero difference at most once. -/
theorem sidon_difference_size {A : Finset G} (hA : IsSidon (A : Set G)) (hne : A.Nonempty) :
    ((A-A).card : ℝ)=(A.card : ℝ)^2-A.card+1 := by
  classical
  have hzero := diff_zero A
  have zero_mem : (0:G)∈A-A := by obtain ⟨a,ha⟩ := hne; exact mem_sub.mpr ⟨a,ha,a,ha,sub_self _⟩
  have eqn (x : G) : (diffReps A x : ℝ) = mark (A-A) x + (if x=0 then (A.card : ℝ)-1 else 0) := by
    by_cases h : x=0
    · subst x; simp [hzero,mark,zero_mem]
    · have hpos : 0<diffReps A x ↔ x∈A-A := by
        change 0 < ((A ×ˢ A).filter fun p => p.1-p.2=x).card ↔ _
        rw [card_pos]
        constructor
        · rintro ⟨⟨a,b⟩,hh⟩
          obtain ⟨⟨ha,hb⟩,he⟩ := (mem_filter.trans (and_congr_left fun _ => mem_product)).mp hh
          exact mem_sub.mpr ⟨a,ha,b,hb,he⟩
        · rintro hx
          obtain ⟨a,ha,b,hb,he⟩ := mem_sub.mp hx
          exact ⟨(a,b),mem_filter.mpr ⟨mem_product.mpr ⟨ha,hb⟩,he⟩⟩
      have hle := sidon_diff_le hA h
      by_cases hh : x∈A-A
      · have hd := hpos.mpr hh
        simp [mark,h,hh,show diffReps A x=1 by omega]
      · have hd := mt hpos.mp hh
        simp [mark,h,hh,show diffReps A x=0 by omega]
  have total := fiber_sum A (fun _ => 1)
  simp only [mul_one,eqn,sum_add_distrib,total_mark,sum_ite_eq',mem_univ,if_true,
    sum_const,nsmul_eq_mul,mul_one] at total
  linarith [show (A.card : ℝ)^2=(A.card : ℝ)*A.card by ring]

/-- Same-parity overlap for a two-layer reflection with even target c. -/
def overlap (A : Finset G) (c : G) := ((A+A).filter (fun x => c-x∈A+A)).card

/-- A finite second-moment certificate for all reflection centers of a Sidon
seed. It controls the exceptional centers even in the absence of multipliers. -/
theorem reflection_variance {A : Finset G} (hA : IsSidon (A : Set G)) (hne : A.Nonempty) :
    let k : ℝ := A.card
    let m : ℝ := Fintype.card G
    ∑ c, (4*(overlap A c : ℝ)-k^4/m)^2 ≤
      4*k^2*(m-k^2+2*k-2)^2+32*m*k^2 := by
  let k : ℝ := A.card
  let m : ℝ := Fintype.card G
  let D := ∑ t, |(diffReps A t : ℝ)-1|
  have hD : 0 ≤ D := sum_nonneg fun _ _ => abs_nonneg _
  have hm : 0<m := by dsimp [m]; exact_mod_cast Fintype.card_pos
  let P := paths A 2
  have hcap (x : G) : P x ≤ 2 := by
    change paths A 2 x ≤ _
    rw [paths_two,pair_profile hA]
    unfold mark
    split_ifs <;> norm_num
  have hsq : ∑ x, (P x)^2 ≤ 2*k^2 := by
    have hu := total_paths A 2
    change ∑ x, P x=k^2 at hu
    rw [← hu,mul_sum]
    apply sum_le_sum
    intro x _
    have hp : 0≤P x := by change 0≤paths A 2 x; rw [paths_two]; positivity
    nlinarith only [mul_nonneg (sub_nonneg.mpr (hcap x)) hp]
  have hv : variance A 2 ≤ 2*k^2 := by
    let μ := k^2/m
    have each (x : G) : (P x-μ)^2 = (P x)^2 - 2*μ*(P x) + μ^2 := by ring
    change ∑ x, (P x-μ)^2 ≤ _
    simp only [each,sum_add_distrib,sum_sub_distrib,← mul_sum,sum_const,card_univ,nsmul_eq_mul]
    have hu : ∑ x, P x=k^2 := total_paths A 2
    rw [hu]
    have hμ : m*μ = k^2 := by dsimp [μ]; field_simp
    have h0 : 0 ≤ μ := div_nonneg (sq_nonneg _) hm.le
    change _ - _ + m*μ^2 ≤ _
    nlinarith only [hsq,congrArg (fun a => a*μ) hμ,mul_nonneg (sq_nonneg k) h0]
  have step₃ := variance_step A 2
  have step₄ := variance_step A 3
  change variance A 3 ≤ D*variance A 2 at step₃
  change variance A 4 ≤ D*variance A 3 at step₄
  have four : variance A 4 ≤ 2*k^2*D^2 := by
    calc
      _ ≤ D*(D*(2*k^2)) := step₄.trans (mul_le_mul_of_nonneg_left
        (step₃.trans (mul_le_mul_of_nonneg_left hv hD)) hD)
      _ = _ := by ring
  have each (c : G) : (4*(overlap A c : ℝ)-k^4/m)^2 ≤
      2*(paths A 4 c-k^4/m)^2+32*k^2 := by
    have ho := two_walk_overlap hA c
    change paths A 4 c ≤ 4*(overlap A c : ℝ) ∧ 4*(overlap A c : ℝ) ≤ paths A 4 c+4*k at ho
    let d := 4*(overlap A c : ℝ)-paths A 4 c
    have h₀ : 0≤d := sub_nonneg.mpr ho.1
    have h₁ : d≤4*k := by dsimp [d]; linarith [ho.2]
    have hsq' := pow_le_pow_left₀ h₀ h₁ 2
    have ht := sq_nonneg (d-(paths A 4 c-k^4/m))
    dsimp only [d] at hsq' ht
    nlinarith only [hsq',ht]
  have hs := sum_le_sum (s := (univ : Finset G)) (fun c _ => each c)
  simp only [sum_add_distrib,← mul_sum,sum_const,card_univ,nsmul_eq_mul] at hs
  change _ ≤ 2*variance A 4 + 32*(m*k^2) at hs
  have hd : D=m-k^2+2*k-2 := sidon_discrepancy hA hne
  change _ ≤ 4*k^2*(m-k^2+2*k-2)^2+32*m*k^2
  rw [← hd]
  nlinarith only [hs,four]

section Layers

variable {K : Type*} [AddCommGroup K] [DecidableEq K]

/-- Two copies of the seed in complementary cosets, reflected about j/2. -/
def layers (A : Finset G) (f : G →+ K) (j : K) := A.image f ∪ A.image (fun a => j-f a)

omit [Fintype G] [DecidableEq G] in
private lemma cosets_disjoint (f : G →+ K) {j : K} (hj : ∀ a, f a ≠ j) (A B : Finset G) :
    Disjoint (A.image f) (B.image (fun b => j+f b)) := by
  apply disjoint_left.mpr
  intro x hx hh
  obtain ⟨a,_,rfl⟩ := mem_image.mp hx
  obtain ⟨b,_,hb⟩ := mem_image.mp hh
  exact hj (a-b) (by rw [map_sub,← hb]; abel)

omit [Fintype G] [DecidableEq G] in
private lemma layer_size (A : Finset G) (f : G →+ K) (hf : Function.Injective f)
    {j : K} (hj : ∀ a, f a ≠ j) : (layers A f j).card=2*A.card := by
  have hd : Disjoint (A.image f) (A.image (fun a => j-f a)) := by
    apply disjoint_left.mpr
    intro x hx hh
    obtain ⟨a,_,rfl⟩ := mem_image.mp hx
    obtain ⟨b,_,hb⟩ := mem_image.mp hh
    exact hj (a+b) (by rw [map_add,← hb]; abel)
  rw [layers,card_union_of_disjoint hd,card_image_of_injective _ hf,
    card_image_of_injective _ (fun a b h => hf (sub_right_inj.mp h))]
  omega

omit [Fintype G] in
private lemma layer_sums (A : Finset G) (f : G →+ K) {j : K} {c : G} (hc : f c=j+j) :
    layers A f j + layers A f j =
      ((A+A) ∪ (A+A).image (fun x => c-x)).image f ∪
        (A-A).image (fun x => j+f x) := by
  ext y
  constructor
  · intro hy
    obtain ⟨u,hu,v,hv,rfl⟩ := mem_add.mp hy
    rcases mem_union.mp hu with hu | hu <;> obtain ⟨a,ha,rfl⟩ := mem_image.mp hu <;>
      rcases mem_union.mp hv with hv | hv <;> obtain ⟨b,hb,rfl⟩ := mem_image.mp hv
    · exact mem_union_left _ (mem_image.mpr ⟨_,mem_union_left _ (add_mem_add ha hb),map_add f a b⟩)
    · apply mem_union_right _ (mem_image.mpr ⟨a-b,sub_mem_sub ha hb,?_⟩)
      rw [map_sub]; abel
    · apply mem_union_right _ (mem_image.mpr ⟨b-a,sub_mem_sub hb ha,?_⟩)
      rw [map_sub]; abel
    · apply mem_union_left _ (mem_image.mpr ⟨c-(a+b),mem_union_right _ (mem_image_of_mem _ (add_mem_add ha hb)),?_⟩)
      rw [map_sub,hc,map_add]; abel
  · intro hy
    rcases mem_union.mp hy with hy | hy <;> obtain ⟨x,hx,rfl⟩ := mem_image.mp hy
    · rcases mem_union.mp hx with hx | hx
      · obtain ⟨a,ha,b,hb,rfl⟩ := mem_add.mp hx
        rw [map_add]
        exact add_mem_add (mem_union_left _ (mem_image_of_mem f ha)) (mem_union_left _ (mem_image_of_mem f hb))
      · obtain ⟨s,hs,rfl⟩ := mem_image.mp hx
        obtain ⟨a,ha,b,hb,rfl⟩ := mem_add.mp hs
        have h : f (c-(a+b))=(j-f a)+(j-f b) := by rw [map_sub,hc,map_add]; abel
        rw [h]
        exact add_mem_add (mem_union_right _ (mem_image_of_mem _ ha)) (mem_union_right _ (mem_image_of_mem _ hb))
    · obtain ⟨a,ha,b,hb,rfl⟩ := mem_sub.mp hx
      have h : j+f (a-b)=f a+(j-f b) := by rw [map_sub]; abel
      rw [h]
      exact add_mem_add (mem_union_left _ (mem_image_of_mem _ ha)) (mem_union_right _ (mem_image_of_mem _ hb))

/-- Exact sumset cardinality for a reflected pair of Sidon layers. -/
theorem layer_sumset_size {A : Finset G} (hA : IsSidon (A : Set G)) (hne : A.Nonempty)
    (f : G →+ K) (hf : Function.Injective f) {j : K} (hj : ∀ a, f a ≠ j)
    {c : G} (hc : f c=j+j) :
    ((layers A f j+layers A f j).card : ℝ) =
      2*(A.card : ℝ)^2+1-((A+A).filter (fun x => c-x∈A+A)).card := by
  let S := A+A
  let T := S.image (fun x => c-x)
  have hint : S ∩ T = S.filter (fun x => c-x∈S) := by
    ext x
    simp only [mem_inter,mem_filter,T,mem_image]
    constructor
    · rintro ⟨hx,y,hy,rfl⟩
      exact ⟨hx,by simpa using hy⟩
    · rintro ⟨hx,hy⟩
      exact ⟨hx,c-x,hy,sub_sub_cancel _ _⟩
  have hcT : T.card=S.card := card_image_of_injective _ (fun _ _ h => sub_right_inj.mp h)
  have hu := card_union_add_card_inter S T
  rw [hint,hcT] at hu
  have hu' : ((S∪T).card : ℝ) + (S.filter (fun x => c-x∈S)).card = S.card+S.card := by exact_mod_cast hu
  have hs : 2*(S.card : ℝ)=(A.card : ℝ)^2+A.card := by exact_mod_cast sidon_sum_size hA
  rw [layer_sums A f hc,card_union_of_disjoint (cosets_disjoint f hj _ _),card_image_of_injective _ hf,
    card_image_of_injective _ (fun a b h => hf (add_left_cancel h)),Nat.cast_add,sidon_difference_size hA hne]
  change ((S∪T).card : ℝ) + _ = _ - (S.filter (fun x => c-x∈S)).card
  linarith

end Layers

section Graph

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Multiplicative exponent coordinate and additive field coordinate. -/
abbrev Plane (F : Type*) [Field F] := Additive Fˣ × F

private def vertex (a : Fˣ) : Plane F := (Additive.ofMul a,(a : F))

/-- Ruzsa's graph in the product of the exponent and field coordinates. -/
def graph (F : Type*) [Field F] [Fintype F] [DecidableEq F] : Finset (Plane F) :=
  (univ : Finset Fˣ).image vertex

private lemma graph_size : (graph F).card = Fintype.card Fˣ := by
  rw [graph,card_image_of_injective _ (fun a b h => Units.ext (congrArg Prod.snd h)),card_univ]

private lemma graph_sidon : IsSidon ((graph F : Finset (Plane F)) : Set (Plane F)) :=
  Green33SidonProfile.graph_sidon F

private def dilate (u : Fˣ) : Plane F ≃+ Plane F :=
  (AddEquiv.refl _).prodCongr (DistribMulAction.toAddEquiv F u)

private def offset (u : Fˣ) : Plane F := (Additive.ofMul u,0)

private lemma invariant (u : Fˣ) : (graph F).image (fun a => dilate u a + offset u) = graph F := by
  have h (a : Fˣ) : dilate u (vertex a) + offset u = vertex (u*a) := by
    apply Prod.ext
    · change Additive.ofMul (a*u) = Additive.ofMul (u*a)
      rw [mul_comm]
    · change (u:F)*(a:F)+0=(↑(u*a):F)
      simp
  ext z
  simp only [graph,mem_image,mem_univ,true_and]
  constructor
  · rintro ⟨_,⟨a,rfl⟩,rfl⟩
    exact ⟨u*a,(h a).symm⟩
  · rintro ⟨a,rfl⟩
    refine ⟨vertex (u⁻¹*a),⟨_,rfl⟩,?_⟩
    rw [h]; simp

private lemma graph_paths_dilate (u : Fˣ) (z : Plane F) (r : ℕ) :
    paths (graph F) r (dilate u z+r • offset u) = paths (graph F) r z := by
  simpa only [invariant] using paths_affine (graph F) (dilate u) (offset u) r z

private lemma fiber_dilate (z w : Plane F) {r : ℕ} (hr : 0<r) :
    (univ.filter (fun u : Fˣ => dilate u z + r • offset u = w)).card ≤ r := by
  classical
  let S := univ.filter (fun u : Fˣ => dilate u z + r • offset u = w)
  let c : F := ((w.1-z.1).toMul : Fˣ)
  have sub : S.image (fun u : Fˣ => (u:F)) ⊆ (Polynomial.nthRoots r c).toFinset := by
    intro x hx
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hx
    have he := congrArg Prod.fst (mem_filter.mp hu).2
    change z.1 + r • Additive.ofMul u = w.1 at he
    have hp : r • Additive.ofMul u = w.1-z.1 := by abel_nf at he ⊢; grind
    have hu' := congrArg (fun v : Additive Fˣ => (v.toMul : F)) hp
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_nthRoots hr).mpr (by simpa [c] using hu'))
  calc
    S.card = (S.image (fun u : Fˣ => (u:F))).card := (card_image_of_injective _ Units.val_injective).symm
    _ ≤ _ := (card_le_card sub).trans (Multiset.toFinset_card_le _)
    _ ≤ r := Polynomial.card_nthRoots r c

private lemma plane_size : Fintype.card (Plane F) = Fintype.card Fˣ * (Fintype.card Fˣ + 1) := by
  rw [Fintype.card_prod,Fintype.card_additive,
    Fintype.card_units, Nat.sub_add_cancel Fintype.card_pos]

/-- Uniform finite estimate for ordered r-tuples of nonzero field elements
with prescribed product and sum, including additive coordinate zero. -/
theorem graph_moment (z : Plane F) {r : ℕ} (hr : 0<r) :
    let k : ℝ := Fintype.card Fˣ
    k * (paths (graph F) r z - k^r / (k*(k+1)))^2 ≤ r*(3*k-2)^r := by
  classical
  let A := graph F
  let k : ℝ := Fintype.card Fˣ
  let m : ℝ := Fintype.card (Plane F)
  have hm : m = k*(k+1) := by dsimp [m,k]; exact_mod_cast plane_size (F := F)
  have hne : A.Nonempty := ⟨vertex 1,mem_image.mpr ⟨1,mem_univ _,rfl⟩⟩
  have hD := sidon_discrepancy (A := A) graph_sidon hne
  change ∑ t, |(diffReps A t : ℝ)-1| = m - (A.card : ℝ)^2 + 2*A.card-2 at hD
  have hk : (A.card : ℝ) = k := by dsimp [A,k]; exact_mod_cast graph_size (F := F)
  rw [hm,hk,show k*(k+1)-k^2+2*k-2=3*k-2 by ring] at hD
  let V (w : Plane F) := (paths A r w-k^r/m)^2
  let T (u : Fˣ) := dilate u z+r • offset u
  have hV (u : Fˣ) : V (T u) = V z := by
    dsimp [V,T,A]; rw [graph_paths_dilate]
  have split : ∑ w, ((univ.filter (fun u : Fˣ => T u=w)).card : ℝ)*V w = ∑ u, V (T u) := by
    simp only [card_eq_sum_ones,Nat.cast_sum,sum_mul,sum_filter]
    rw [sum_comm]; simp
  have lower : k*V z ≤ (r:ℝ)*∑ w, V w := by
    calc
      k*V z = ∑ u : Fˣ, V (T u) := by simp [hV,k]
      _ = _ := split.symm
      _ ≤ ∑ w, (r:ℝ)*V w := by
        apply sum_le_sum
        intro w _
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast fiber_dilate z w hr) (sq_nonneg _)
      _ = _ := (mul_sum ..).symm
  have hu := path_variance A r
  rw [hD,hk] at hu
  have h := lower.trans (mul_le_mul_of_nonneg_left hu (Nat.cast_nonneg r))
  simpa only [V,hm] using h

end Graph

/-- Cyclic order of the Ruzsa graph before doubling. -/
def order (p : ℕ) [hp : Fact p.Prime] : ℕ+ := ⟨(p-1)*p,Nat.mul_pos (by have := hp.out.one_lt; omega) hp.out.pos⟩

private noncomputable def chart (p : ℕ) [hp : Fact p.Prime] :
    Plane (ZMod p) ≃+ ZMod (order p) := by
  let U := (ZMod p)ˣ
  have hcard : Nat.card (Additive U) = p-1 := by
    change Nat.card (ZMod p)ˣ = p-1
    rw [Nat.card_eq_fintype_card,ZMod.card_units]
  let f : ZMod (p-1) ≃+ Additive U := hcard ▸ zmodAddCyclicAddEquiv (inferInstance : IsAddCyclic (Additive U))
  let hc := (Nat.coprime_self_sub_left hp.out.one_le).mpr (by simp)
  exact ((ZMod.chineseRemainder hc).toAddEquiv.trans (f.prodCongr (AddEquiv.refl _))).symm

private def doubleHom (m : ℕ+) : ZMod m →+ ZMod (2*m.val) where
  toFun x := (2*x.val : ℕ)
  map_zero' := by simp
  map_add' x y := by
    change ((2*(x+y).val : ℕ): ZMod (2*m.val)) = ((2*x.val : ℕ):ZMod (2*m.val))+((2*y.val : ℕ):ZMod (2*m.val))
    rw [← Nat.cast_add,← Nat.mul_add,ZMod.val_add,ZMod.natCast_eq_natCast_iff]
    exact (Nat.mod_modEq _ _).mul_left' 2

private lemma double_injective (m : ℕ+) : Function.Injective (doubleHom m) := by
  intro a b hab
  have h := (ZMod.natCast_eq_natCast_iff _ _ _).mp hab
  have hm := Nat.ModEq.mul_left_cancel' (by decide : 2≠0) h
  exact ZMod.val_injective m (by simpa [Nat.ModEq,Nat.mod_eq_of_lt (ZMod.val_lt a),Nat.mod_eq_of_lt (ZMod.val_lt b)] using hm)

private lemma double_one (m : ℕ+) : doubleHom m 1=1+1 := by
  change ((2*(1 : ZMod m).val : ℕ):ZMod (2*m.val)) = 1+1
  have h := (Nat.mod_modEq 1 m.val).mul_left' 2
  have he := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h
  simpa only [← ZMod.val_natCast,Nat.cast_one,Nat.mul_one,Nat.cast_ofNat,one_add_one_eq_two] using he

private lemma even_ne_odd (m : ℕ+) (x t : ZMod m) : doubleHom m x ≠ 1+doubleHom m t := by
  let parity := ZMod.castHom (show 2 ∣ 2*m.val by simp) (ZMod 2)
  have h (a : ZMod m) : parity (doubleHom m a)=0 := by
    change parity ((2*a.val : ℕ):ZMod (2*m.val)) = 0
    rw [map_natCast,Nat.cast_mul,Nat.cast_ofNat,show (2 : ZMod 2)=0 by decide,zero_mul]
  intro he
  have h' := congrArg parity he
  rw [h,map_add,map_one,h,add_zero] at h'
  exact zero_ne_one h'

private noncomputable def primeEven (p : ℕ) [Fact p.Prime] : Plane (ZMod p) →+ ZMod (2*(order p).val) :=
  (doubleHom (order p)).comp (chart p).toAddMonoidHom

/-- Even copies of Ruzsa's graph and their reflections across an arbitrary
odd residue in the cyclic group of twice the original order. -/
noncomputable def primeLayers (p : ℕ) [Fact p.Prime] (t : ZMod (order p)) : Finset (ZMod (2*(order p).val)) :=
  layers (graph (ZMod p)) (primeEven p) (1+doubleHom (order p) t)

private lemma prime_even_data (p : ℕ) [Fact p.Prime] (t : ZMod (order p)) :
    Function.Injective (primeEven p) ∧ (∀ a, primeEven p a ≠ 1+doubleHom (order p) t) ∧
    primeEven p ((chart p).symm (1+t+t)) = (1+doubleHom (order p) t)+(1+doubleHom (order p) t) := by
  refine ⟨(double_injective _).comp (chart p).injective,fun a => even_ne_odd _ _ _,?_⟩
  simp only [primeEven,AddMonoidHom.comp_apply,AddEquiv.coe_toAddMonoidHom,AddEquiv.apply_symm_apply,map_add,double_one]
  abel

private lemma graph_four_error {F : Type*} [Field F] [Fintype F] [DecidableEq F] (z : Plane F) :
    let k : ℝ := Fintype.card Fˣ
    |paths (graph F) 4 z - k^4/(k*(k+1))| ≤ 18*k*Real.sqrt k := by
  let k : ℝ := Fintype.card Fˣ
  let v := paths (graph F) 4 z - k^4/(k*(k+1))
  change |v| ≤ 18*k*Real.sqrt k
  have hk : 1 ≤ k := by dsimp [k]; exact_mod_cast Fintype.card_pos
  have h := graph_moment z (r := 4) (by decide)
  change k*v^2 ≤ (4:ℝ)*(3*k-2)^4 at h
  have ht := pow_le_pow_left₀ (by linarith : 0≤3*k-2) (by linarith : 3*k-2≤3*k) 4
  have hs := Real.sq_sqrt (show 0≤k by linarith)
  have he : k*(18*k*Real.sqrt k)^2 = 4*(3*k)^4 := by rw [mul_pow,hs]; ring
  have hv : v^2 ≤ (18*k*Real.sqrt k)^2 := by
    apply le_of_mul_le_mul_left (a := k) _ (by linarith)
    rw [he]; linarith
  have hp : 0 ≤ 18*k*Real.sqrt k := by positivity
  nlinarith only [hv,sq_abs v,hp,abs_nonneg v,sq_nonneg (|v| - 18*k*Real.sqrt k)]

/-- Coordinates for the two layers, with the even embedding and its odd
reflection specified independently of the choice of primitive root. -/
theorem primeLayers_structure (p : ℕ) [Fact p.Prime] (t : ZMod (order p)) :
    ∃ (f : Plane (ZMod p) →+ ZMod (2*(order p).val)) (j : ZMod (2*(order p).val))
      (c : Plane (ZMod p)), Function.Injective f ∧ (∀ x, f x ≠ j) ∧
      f c=j+j ∧ primeLayers p t=layers (graph (ZMod p)) f j := by
  obtain ⟨hf,hj,hc⟩ := prime_even_data p t
  exact ⟨_,_,_,hf,hj,hc,rfl⟩

/-- For every odd reflection center, the doubled graph misses one eighth of
the ambient cyclic group up to an explicit sublinear error. -/
theorem prime_layer_bound (p : ℕ) [hp : Fact p.Prime] (t : ZMod (order p)) :
    let A := primeLayers p t
    let k : ℝ := (p-1 : ℕ)
    let m : ℝ := (order p).val
    A.card=2*(p-1) ∧ |4*(2*m-(A+A).card)-m| ≤ 18*k*Real.sqrt k + 12*k := by
  let B := graph (ZMod p)
  let A := primeLayers p t
  let k : ℝ := (p-1 : ℕ)
  let m : ℝ := (order p).val
  let z := (chart p).symm (1+t+t)
  have hd := prime_even_data p t
  have hkB : B.card=p-1 := (graph_size (F := ZMod p)).trans (ZMod.card_units p)
  have hBk : (B.card : ℝ)=k := by dsimp only [k]; exact_mod_cast hkB
  have hk : 1≤k := by dsimp [k]; exact_mod_cast (show 1≤p-1 by have := hp.out.one_lt; omega)
  have hm : m=k*(k+1) := by
    dsimp [m,k,order]
    push_cast [Nat.cast_sub hp.out.one_le]
    ring
  have hmpos : 0<m := by rw [hm]; positivity
  have hne : B.Nonempty := ⟨vertex 1,mem_image.mpr ⟨1,mem_univ _,rfl⟩⟩
  have hc := layer_sumset_size (A := B) graph_sidon hne (primeEven p) hd.1 hd.2.1 hd.2.2
  let I := ((B+B).filter (fun x => z-x∈B+B)).card
  change ((A+A).card : ℝ)=2*(B.card : ℝ)^2+1-I at hc
  rw [hBk] at hc
  have ho := two_walk_overlap (A := B) graph_sidon z
  change paths B 4 z ≤ 4*(I : ℝ) ∧ 4*(I : ℝ) ≤ paths B 4 z+4*B.card at ho
  rw [hBk] at ho
  have herr := graph_four_error z
  simp only [ZMod.card_units] at herr
  change |paths B 4 z-k^4/(k*(k+1))| ≤ 18*k*Real.sqrt k at herr
  rw [← hm,abs_le] at herr
  have hcenter : m-2*k ≤ k^4/m ∧ k^4/m ≤ m := by
    constructor
    · apply (le_div_iff₀ hmpos).mpr
      rw [hm]; nlinarith only [sq_nonneg k]
    · apply (div_le_iff₀ hmpos).mpr
      rw [hm]; nlinarith only [sq_nonneg k,mul_nonneg (sq_nonneg k) (show k≥0 by linarith)]
  refine ⟨(layer_size B _ hd.1 hd.2.1).trans (by rw [hkB]),?_⟩
  change |4*(2*m-(↑(A+A).card : ℝ))-m| ≤ _
  rw [abs_le]
  constructor <;> nlinarith only [hc,ho.1,ho.2,herr.1,herr.2,hcenter.1,hcenter.2,hm,hk]

open Filter
open scoped Topology

private lemma k_limit (p : ℕ → ℕ) (hp : Tendsto p atTop atTop) :
    Tendsto (fun i => ((p i-1 : ℕ) : ℝ)) atTop atTop := by
  apply tendsto_natCast_atTop_atTop.comp
  apply tendsto_atTop.mpr
  intro n
  filter_upwards [hp.eventually_ge_atTop (n+1)] with i hi
  omega

/-- Along every unbounded prime sequence, uniformly in the independently
chosen reflections, one eighth of the cyclic residues are missing. -/
theorem prime_hole_fraction (p : ℕ → ℕ) [h : ∀ i, Fact (p i).Prime]
    (t : ∀ i, ZMod (order (p i))) (hp : Tendsto p atTop atTop) :
    let A := fun i => primeLayers (p i) (t i)
    Tendsto (fun i => ((2*(order (p i)).val : ℕ) - ((A i+A i).card : ℝ)) /
      (2*(order (p i)).val : ℕ)) atTop (𝓝 (1/8)) := by
  let k (i : ℕ) : ℝ := (p i-1 : ℕ)
  let m (i : ℕ) : ℝ := (order (p i)).val
  let A := fun i => primeLayers (p i) (t i)
  let holes (i : ℕ) := 2*m i - (↑(A i+A i).card : ℝ)
  have hk (i : ℕ) : 0 < k i := by
    dsimp [k]; exact_mod_cast (show 0<p i-1 by have := (h i).out.one_lt; omega)
  have hm (i : ℕ) : m i = k i*(k i+1) := by
    dsimp [m,k,order]; push_cast [Nat.cast_sub (h i).out.one_le]; ring
  have hpos (i : ℕ) : 0<m i := by rw [hm]; exact mul_pos (hk i) (by linarith [hk i])
  have ht : Tendsto k atTop atTop := k_limit p hp
  have hd := ((tendsto_const_nhds (x := (18:ℝ))).div_atTop (Real.tendsto_sqrt_atTop.comp ht)).add
    ((tendsto_const_nhds (x := (12:ℝ))).div_atTop ht)
  rw [add_zero] at hd
  have hconv : Tendsto (fun i => |holes i/(2*m i)-1/8|) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => abs_nonneg _) _ hd
    intro i
    have hb := (prime_layer_bound (p i) (t i)).2
    change |4*holes i-m i| ≤ 18*k i*Real.sqrt (k i)+12*k i at hb
    have hs : 0 < Real.sqrt (k i) := Real.sqrt_pos.mpr (hk i)
    have hs₂ := Real.sq_sqrt (hk i).le
    have hden : k i*k i ≤ 8*m i := by rw [hm]; nlinarith [sq_nonneg (k i),hk i]
    have hscale : (18/Real.sqrt (k i)+12/k i)*(k i*k i) =
        18*k i*Real.sqrt (k i)+12*k i := by
      field_simp [hs.ne',(hk i).ne']
      nlinarith only [hs₂]
    have he : holes i/(2*m i)-1/8 = (4*holes i-m i)/(8*m i) := by field_simp [(hpos i).ne']; ring
    rw [he,abs_div,abs_of_pos (by linarith [hpos i] : 0<8*m i)]
    apply (div_le_iff₀ (by linarith [hpos i] : 0<8*m i)).mpr
    rw [← hscale] at hb
    exact hb.trans (mul_le_mul_of_nonneg_left hden (by positivity))
  have ht' := tendsto_iff_dist_tendsto_zero.mpr (show Tendsto (fun i =>
      dist (holes i/(2*m i)) (1/8)) atTop (𝓝 0) by simpa only [Real.dist_eq] using hconv)
  simpa only [Nat.cast_mul,Nat.cast_ofNat] using ht'

private lemma extension_cost {A B : Finset G} (hAB : A ⊆ B) (hb : B+B=univ) :
    2*((Fintype.card G : ℝ)-(A+A).card)+(A.card : ℝ)^2+A.card ≤ (B.card : ℝ)^2+B.card := by
  classical
  let s : Sym2 G → G := Sym2.lift ⟨(·+·),add_comm⟩
  have image_s (C : Finset G) : C.sym2.image s = C+C := by
    ext x
    constructor
    · rintro hx
      obtain ⟨⟨a,b⟩,hab,rfl⟩ := mem_image.mp hx
      obtain ⟨ha,hb⟩ := mk_mem_sym2_iff.mp hab
      exact add_mem_add ha hb
    · rintro hx
      obtain ⟨a,ha,b,hb,rfl⟩ := mem_add.mp hx
      exact mem_image.mpr ⟨Sym2.mk a b,mk_mem_sym2_iff.mpr ⟨ha,hb⟩,rfl⟩
  have sub : (B+B) \ (A+A) ⊆ (B.sym2 \ A.sym2).image s := by
    intro x hx
    obtain ⟨hi,ho⟩ := mem_sdiff.mp hx
    rw [← image_s] at hi ho
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hi
    exact mem_image.mpr ⟨p,mem_sdiff.mpr ⟨hp,fun h => ho (mem_image_of_mem s h)⟩,rfl⟩
  have hle : ((B+B) \ (A+A)).card ≤ (B.sym2 \ A.sym2).card := (card_le_card sub).trans card_image_le
  have hprev := card_sdiff_add_card_eq_card (add_subset_add hAB hAB)
  have hnew := card_sdiff_add_card_eq_card (sym2_mono hAB)
  rw [hb,card_univ] at hprev
  rw [hb] at hle
  have hh : Fintype.card G+A.sym2.card ≤ (A+A).card+B.sym2.card := by omega
  have hh' : (Fintype.card G : ℝ)+A.sym2.card ≤ (A+A).card+B.sym2.card := by exact_mod_cast hh
  simp only [card_sym2,Nat.cast_choose_two,Nat.cast_add_one] at hh'
  linarith

/-- Any cyclic two-basis containing a reflected prime graph has eventual
normalized size above every constant below 3/2. -/
theorem prime_extension_lower (p : ℕ → ℕ) [h : ∀ i, Fact (p i).Prime]
    (t : ∀ i, ZMod (order (p i))) (hp : Tendsto p atTop atTop)
    (B : (i : ℕ) → Finset (ZMod (2*(order (p i)).val)))
    (hsub : ∀ i, primeLayers (p i) (t i) ⊆ B i) (hb : ∀ i, B i+B i=univ)
    (c : ℝ) (hc : c<3/2) : ∀ᶠ i in atTop, c < ((B i).card : ℝ)/Real.sqrt (2*(order (p i)).val : ℕ) := by
  let A := fun i => primeLayers (p i) (t i)
  let k (i : ℕ) : ℝ := (p i-1 : ℕ)
  let N (i : ℕ) : ℝ := (2*(order (p i)).val : ℕ)
  let H (i : ℕ) := N i - (↑(A i+A i).card : ℝ)
  let a (i : ℕ) : ℝ := (A i).card
  let b (i : ℕ) : ℝ := (B i).card
  have hk (i : ℕ) : 0 < k i := by
    dsimp [k]; exact_mod_cast (show 0<p i-1 by have := (h i).out.one_lt; omega)
  have hN (i : ℕ) : N i=2*k i*(k i+1) := by
    dsimp [N,k,order]; push_cast [Nat.cast_sub (h i).out.one_le]; ring
  have hn (i : ℕ) : 0<N i := by rw [hN]; have := hk i; positivity
  have ht : Tendsto k atTop atTop := k_limit p hp
  have hnt : Tendsto N atTop atTop := tendsto_atTop_mono (fun i =>
    show k i ≤ N i by rw [hN]; nlinarith [hk i,sq_nonneg (k i)]) ht
  have ha (i : ℕ) : a i=2*k i := by
    dsimp [a,A,k]; exact_mod_cast (prime_layer_bound (p i) (t i)).1
  have hh : Tendsto (fun i => H i/N i) atTop (𝓝 (1/8)) := prime_hole_fraction p t hp
  have hk1 : Tendsto (fun i => k i+1) atTop atTop := ht.atTop_add (tendsto_const_nhds (x := (1:ℝ)))
  have ha₂ : Tendsto (fun i => (a i)^2/N i) atTop (𝓝 2) := by
    have hlim := (tendsto_const_nhds (x := (2:ℝ)) (f := atTop (α := ℕ))).sub
      ((tendsto_const_nhds (x := (2:ℝ))).div_atTop hk1)
    rw [sub_zero] at hlim
    apply hlim.congr
    intro i
    rw [ha,hN]
    field_simp [(hk i).ne',show k i+1≠0 by linarith [hk i]]; ring
  have he := (((tendsto_const_nhds (x := (2:ℝ))).mul hh).add ha₂).sqrt
  rw [show (2*(1/8)+2 : ℝ)=(3/2 : ℝ)^2 by norm_num,Real.sqrt_sq (by norm_num)] at he
  have herr := (tendsto_const_nhds (x := (1:ℝ))).div_atTop (Real.tendsto_sqrt_atTop.comp hnt)
  have hlim := he.sub herr
  rw [sub_zero] at hlim
  filter_upwards [hlim.eventually_const_lt hc] with i hi
  have hcost := extension_cost (hsub i) (hb i)
  rw [ZMod.card] at hcost
  change 2*H i+(a i)^2+a i ≤ (b i)^2+b i at hcost
  have hb₀ : 0≤b i := Nat.cast_nonneg _
  have ha₀ : 0≤a i := Nat.cast_nonneg _
  have hH : 0≤H i := by
    apply sub_nonneg.mpr
    have hle := (A i+A i).card_le_univ
    rw [ZMod.card] at hle
    dsimp only [N]
    exact_mod_cast hle
  have hs : Real.sqrt (2*H i+(a i)^2) ≤ b i+1 := (Real.sqrt_le_iff).mpr ⟨by linarith,by nlinarith⟩
  change c < Real.sqrt (2*(H i/N i)+(a i)^2/N i)-1/Real.sqrt (N i) at hi
  rw [← mul_div_assoc,← add_div,Real.sqrt_div (by positivity),← sub_div] at hi
  exact hi.trans_le (div_le_div_of_nonneg_right (by linarith) (Real.sqrt_nonneg _))

private lemma relative_overlap {m : ℕ → ℕ+} (A : (i : ℕ) → Finset (ZMod (m i)))
    (hA : ∀ i, IsSidon (A i : Set (ZMod (m i)))) (hne : ∀ i, (A i).Nonempty)
    (hm : Tendsto (fun i => (m i).val) atTop atTop)
    (hk : Tendsto (fun i => ((A i).card : ℝ)/Real.sqrt (m i).val) atTop (𝓝 1)) :
    Tendsto (fun i => (∑ c, (4*(overlap (A i) c : ℝ)-(m i).val)^2) / ((m i).val : ℝ)^3) atTop (𝓝 0) := by
  let n (i : ℕ) : ℝ := (m i).val
  let k (i : ℕ) : ℝ := (A i).card
  let s (i : ℕ) := (k i)^2/n i
  let D (i : ℕ) := n i-(k i)^2+2*k i-2
  have hp (i : ℕ) : 0<n i := by dsimp [n]; exact_mod_cast (m i).pos
  have ht : Tendsto n atTop atTop := tendsto_natCast_atTop_atTop.comp hm
  have hs₀ (i : ℕ) : (Real.sqrt (n i))^2 = n i := Real.sq_sqrt (hp i).le
  have hs : Tendsto s atTop (𝓝 1) := by
    have h := hk.pow 2
    rw [one_pow] at h
    apply h.congr (fun i => ?_)
    change (k i/Real.sqrt (n i))^2 = _
    rw [div_pow,hs₀]
  have hkn : Tendsto (fun i => k i/n i) atTop (𝓝 0) := by
    apply (hk.div_atTop (Real.tendsto_sqrt_atTop.comp ht)).congr (fun i => ?_)
    change (k i/Real.sqrt (n i))/Real.sqrt (n i)=_
    rw [div_div,← sq,hs₀]
  have hDn : Tendsto (fun i => D i/n i) atTop (𝓝 0) := by
    have h := (((tendsto_const_nhds (x := (1:ℝ))).sub hs).add
      ((tendsto_const_nhds (x := (2:ℝ))).mul hkn)).sub ((tendsto_const_nhds (x := (2:ℝ))).div_atTop ht)
    norm_num at h
    apply h.congr (fun i => ?_)
    change 1-s i+2*(k i/n i)-2/n i=D i/n i
    dsimp [s,D]; field_simp [(hp i).ne']
  have bound := (((tendsto_const_nhds (x := (4:ℝ))).mul hs).mul (hDn.pow 2)).add
    ((tendsto_const_nhds (x := (32:ℝ))).mul (hkn.pow 2))
  have all := ((tendsto_const_nhds (x := (2:ℝ))).mul bound).add
    ((tendsto_const_nhds (x := (2:ℝ))).mul (((hs.pow 2).sub (tendsto_const_nhds (x := (1:ℝ)))).pow 2))
  norm_num at all
  apply squeeze_zero (fun i => div_nonneg (sum_nonneg fun _ _ => sq_nonneg _) (by positivity)) _ all
  intro i
  have h := reflection_variance (hA i) (hne i)
  simp only [ZMod.card] at h
  let X (c : ZMod (m i)) : ℝ := 4*(overlap (A i) c : ℝ)
  let μ := (k i)^4/n i
  change ∑ c, (X c-μ)^2 ≤ 4*(k i)^2*(D i)^2+32*n i*(k i)^2 at h
  have each (c : ZMod (m i)) : (X c-n i)^2 ≤ 2*(X c-μ)^2+2*(μ-n i)^2 := by
    nlinarith only [sq_nonneg ((X c-μ)-(μ-n i))]
  have hsum := sum_le_sum (s := (univ : Finset (ZMod (m i)))) (fun c _ => each c)
  simp only [sum_add_distrib,← mul_sum,sum_const,card_univ,ZMod.card,nsmul_eq_mul] at hsum
  change _ ≤ 2*∑ c, (X c-μ)^2 + _ at hsum
  change (∑ c, (X c-n i)^2)/(n i)^3 ≤ 2*(4*s i*(D i/n i)^2+32*(k i/n i)^2)+2*((s i)^2-1)^2
  apply (div_le_iff₀ (pow_pos (hp i) 3)).mpr
  have he : (2*(4*s i*(D i/n i)^2+32*(k i/n i)^2)+2*((s i)^2-1)^2)*(n i)^3 =
      2*(4*(k i)^2*(D i)^2+32*n i*(k i)^2)+2*n i*(μ-n i)^2 := by
    dsimp only [μ,s]; field_simp [(hp i).ne']
  rw [he]
  change _ ≤ 2*∑ c, (X c-μ)^2 + 2*(n i*(μ-n i)^2) at hsum
  linarith

/-- For every dense cyclic Sidon family, the proportion of even-layer
reflection parameters with a fixed deviation from quarter overlap tends
to zero. No multiplier or algebraic construction is assumed. -/
theorem typical_centers {m : ℕ → ℕ+} (A : (i : ℕ) → Finset (ZMod (m i)))
    (hA : ∀ i, IsSidon (A i : Set (ZMod (m i)))) (hne : ∀ i, (A i).Nonempty)
    (hm : Tendsto (fun i => (m i).val) atTop atTop)
    (hk : Tendsto (fun i => ((A i).card : ℝ)/Real.sqrt (m i).val) atTop (𝓝 1))
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun i => (((univ.filter fun c => δ*(m i).val ≤
      |4*(overlap (A i) c : ℝ)-(m i).val|).card : ℝ)/(m i).val)) atTop (𝓝 0) := by
  let n (i : ℕ) : ℝ := (m i).val
  have hn (i : ℕ) : 0<n i := by dsimp [n]; exact_mod_cast (m i).pos
  have h := (relative_overlap A hA hne hm hk).div_const (δ^2)
  rw [zero_div] at h
  apply squeeze_zero (fun _ => by positivity) _ h
  intro i
  let f (c) := 4*(overlap (A i) c : ℝ)-n i
  let E := univ.filter (fun c => δ*n i ≤ |f c|)
  have ht : ∑ c ∈ E, (δ*n i)^2 ≤ ∑ c, (f c)^2 := by
    apply (sum_le_sum (g := fun c => (f c)^2) ?_).trans (sum_le_univ_sum_of_nonneg fun _ => sq_nonneg _)
    intro c hc
    simpa only [sq_abs] using pow_le_pow_left₀ (mul_nonneg hδ.le (hn i).le) (mem_filter.mp hc).2 2
  rw [sum_const,nsmul_eq_mul] at ht
  change (E.card : ℝ)/n i ≤ (∑ c, (f c)^2)/(n i)^3/δ^2
  apply (le_div_iff₀ (pow_pos hδ 2)).mpr
  apply (le_div_iff₀ (pow_pos (hn i) 3)).mpr
  calc
    _ = (E.card : ℝ)*(δ*n i)^2 := by field_simp [(hn i).ne']
    _ ≤ _ := ht

#print axioms walk_energy_bound
#print axioms path_variance
#print axioms sidon_difference_size
#print axioms reflection_variance
#print axioms layer_sumset_size
#print axioms graph_moment
#print axioms primeLayers_structure
#print axioms prime_layer_bound
#print axioms prime_hole_fraction
#print axioms prime_extension_lower
#print axioms typical_centers

end Green33ReflectedLayers
