import Green33TranslateOverlap

/-! Translation variation of the ordered sum representation function. Sárközy
studies its unit-step variation in finite cyclic groups. Here the estimates
are uniform in every nonzero shift, including shifts of nonmaximal order. -/

open Finset Filter Green33Multiplicity Green33TailEnergy Green33TranslateOverlap
open Green33ReflectionRigidity
open scoped Pointwise Topology

namespace Green33ShiftVariation

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

omit [AddCommGroup G] in
private lemma fiber_total {α : Type*} (B : Finset α) (f : α → G) :
    ∑ s, (B.filter fun x => f x = s).card = B.card := by
  simpa using sum_card_fiberwise_eq_card_filter B univ f

private lemma fiber_corr {α : Type*} [DecidableEq α] (B : Finset α) (f : α → G) (h : G) :
    ∑ s, (B.filter fun x => f x = s).card * (B.filter fun y => f y = s+h).card =
      ((B ×ˢ B).filter fun u => f u.2 = f u.1+h).card := by
  rw [← fiber_total ((B ×ˢ B).filter fun u => f u.2 = f u.1+h) (fun u => f u.1)]
  apply sum_congr rfl
  intro s _
  rw [← card_product]
  congr 1
  ext u
  simp only [mem_product, mem_filter]
  grind

/-- The ordered sum and difference counts have the same autocorrelation at
each shift. -/
theorem shifted_correlation (A : Finset G) (h : G) :
    ∑ z, reps A z * reps A (z+h) = ∑ z, diffReps A z * diffReps A (z+h) := by
  simp only [reps, diffReps, fiber_corr]
  let swap (u : (G×G)×(G×G)) := ((u.1.1,u.2.2),(u.2.1,u.1.2))
  let e : ((G×G)×(G×G)) ≃ ((G×G)×(G×G)) := ⟨swap,swap,fun _ => rfl,fun _ => rfl⟩
  apply card_equiv e
  rintro ⟨⟨a,b⟩,c,d⟩
  change ((a,b),(c,d)) ∈ _ ↔ ((a,d),(c,b)) ∈ _
  simp only [mem_filter, mem_product]
  have eq : c+d=a+b+h ↔ c-b=a-d+h := by
    constructor
    · intro H
      rw [← eq_sub_iff_add_eq] at H
      subst c
      abel
    · intro H
      rw [sub_eq_iff_eq_add] at H
      subst c
      abel
  tauto

/-- Sum of the squared changes along translation by `h`. -/
def jumpEnergy (f : G → ℝ) (h : G) : ℝ := ∑ z, (f (z+h)-f z)^2

omit [DecidableEq G] in
private lemma shift_sum (f : G → ℝ) (h : G) : ∑ z, f (z+h) = ∑ z, f z :=
  Fintype.sum_equiv (Equiv.addRight h) _ _ fun _ => rfl

omit [DecidableEq G] in
private lemma energy_expand (f : G → ℝ) (h : G) :
    jumpEnergy f h = 2 * (∑ z, f z ^ 2) - 2 * ∑ z, f z * f (z+h) := by
  have term (z) : (f (z+h)-f z)^2 = f (z+h)^2 + f z^2 - 2*(f z*f (z+h)) := by ring
  rw [jumpEnergy]
  simp only [term, sum_sub_distrib, sum_add_distrib, ← mul_sum, shift_sum (fun z => f z^2)]
  ring

theorem sum_difference_jumps (A : Finset G) (h : G) :
    jumpEnergy (fun z => reps A z) h = jumpEnergy (fun z => diffReps A z) h := by
  rw [energy_expand,energy_expand]
  have c (u : G) : ∑ z, (reps A z : ℝ) * reps A (z+u) =
      ∑ z, (diffReps A z : ℝ) * diffReps A (z+u) := by exact_mod_cast shifted_correlation A u
  have z := c 0
  simp only [add_zero, ← sq] at z
  rw [z,c]

omit [Fintype G] in
private theorem diff_neg (A : Finset G) (h : G) : diffReps A (-h) = diffReps A h := by
  apply card_equiv (Equiv.prodComm G G)
  rintro ⟨a,b⟩
  simp only [mem_filter, mem_product, Equiv.prodComm_apply]
  have eq : a-b = -h ↔ b-a = h := by
    constructor
    · intro H
      rw [sub_eq_iff_eq_add] at H
      subst a
      abel
    · intro H
      rw [sub_eq_iff_eq_add] at H
      subst b
      abel
  tauto

/-- The two positions zero and minus the shift in the difference profile give
a lower bound for variation of the sum profile. -/
theorem jump_lower (A : Finset G) {h : G} (hh : h ≠ 0) :
    2*((A.card : ℝ)-diffReps A h)^2 ≤ jumpEnergy (fun z => reps A z) h := by
  classical
  rw [sum_difference_jumps,jumpEnergy]
  have zero : diffReps A 0 = A.card := by simp only [diffReps,sub_eq_zero,← diag_eq_filter,diag_card]
  have neq : 0 ≠ -h := by simpa using hh
  calc
    _ = ∑ z ∈ ({0,-h}:Finset G), ((diffReps A (z+h):ℝ)-diffReps A z)^2 := by
      rw [sum_pair neq]
      simp only [zero_add,neg_add_cancel,zero,diff_neg]
      ring
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => sq_nonneg _)

/-- Total absolute deviation from two ordered representations per residue. -/
def deviation (A : Finset G) : ℝ := ∑ z, |(reps A z : ℝ)-2|

omit [Fintype G] in
private theorem covered (A : Finset G) {z : G} (hz : z ∈ A+A) : 2 ≤ reps A z + diagonalReps A z := by
  obtain ⟨a,ha,b,hb,e⟩ := mem_add.mp hz
  have h : (a,b) ∈ (A ×ˢ A).filter (fun u => u.1+u.2=z) := by simp [ha,hb,e]
  by_cases eq : a=b
  · subst b
    exact Nat.add_le_add (show 0 < reps A z from card_pos.mpr ⟨_,h⟩)
      (show 0 < diagonalReps A z from card_pos.mpr ⟨_,mem_filter.mpr ⟨ha,e⟩⟩)
  · have h' : (b,a) ∈ (A ×ˢ A).filter (fun u => u.1+u.2=z) := by simp [ha,hb,add_comm b a,e]
    have hr : 1 < reps A z := one_lt_card.mpr ⟨_,h,_,h',fun he => eq (congrArg Prod.fst he)⟩
    omega

/-- Missing sums and excess above the counting threshold bound the total
deviation. This also covers seeds whose sumset omits residues. -/
theorem deviation_upper (A : Finset G) : deviation A ≤
    (A.card:ℝ)^2 + 2*Fintype.card G - 4*(A+A).card + 2*A.card := by
  classical
  have one (z : G) : |(reps A z:ℝ)-2| ≤
      (reps A z:ℝ)+2-4*(if z ∈ A+A then (1:ℝ) else 0)+2*(diagonalReps A z:ℝ) := by
    by_cases h : z ∈ A+A
    · have hz : (2:ℝ) ≤ (reps A z:ℝ)+diagonalReps A z := by exact_mod_cast covered A h
      rw [if_pos h,abs_le]
      constructor <;> linarith [Nat.cast_nonneg (α:=ℝ) (diagonalReps A z)]
    · rw [if_neg h,abs_le]
      constructor <;> linarith [Nat.cast_nonneg (α:=ℝ) (reps A z),Nat.cast_nonneg (α:=ℝ) (diagonalReps A z)]
  have sumR : ∑ z, (reps A z:ℝ) = (A.card:ℝ)^2 := by
    exact_mod_cast (show ∑ z, reps A z = A.card^2 by simp only [reps,fiber_total,card_product,sq])
  have sumD : ∑ z, (diagonalReps A z:ℝ) = A.card := by exact_mod_cast fiber_total A (fun x => x+x)
  have inds : (∑ z, if z ∈ A+A then (1:ℝ) else 0) = (A+A).card := by simp
  have h := sum_le_sum (s:=univ) (fun z _ => one z)
  simpa only [deviation, sum_add_distrib, sum_sub_distrib, ← mul_sum, sumR, sumD, inds,
    sum_const, card_univ, nsmul_eq_mul, mul_comm (Fintype.card G:ℝ) 2] using h

/-- A bound on upward jumps alone bounds their total squared energy. -/
theorem one_sided_energy (A : Finset G) (h : G) (L : ℝ) (hL : 0 ≤ L)
    (cap : ∀ z, (reps A (z+h):ℝ)-reps A z ≤ L) :
    jumpEnergy (fun z => reps A z) h ≤ (2*L+8)*deviation A := by
  let r (z : G) := (reps A z:ℝ)
  let d (z : G) := r (z+h)-r z
  have steps : ∑ z, |d z| ≤ 2*deviation A := by
    have point (z) : |d z| ≤ |r (z+h)-2|+|r z-2| := by
      rw [show d z = (r (z+h)-2)-(r z-2) by dsimp [d]; ring]
      exact abs_sub _ _
    have hz := sum_le_sum (s:=univ) (fun z _ => point z)
    rw [sum_add_distrib, shift_sum (fun z => |r z-2|)] at hz
    simpa only [deviation,r,two_mul] using hz
  have term (z) : (r (z+h)-2)*d z ≤ L*|r (z+h)-2|+2*|d z| := by
    by_cases H : 0 ≤ r (z+h)-2
    · rw [abs_of_nonneg H]
      have bound := mul_le_mul_of_nonneg_left (cap z) H
      change (r (z+h)-2)*d z ≤ _ at bound
      linarith [abs_nonneg (d z)]
    · have lo : -(r (z+h)-2) ≤ 2 := by dsimp [r]; linarith [Nat.cast_nonneg (α:=ℝ) (reps A (z+h))]
      have absBound : |r (z+h)-2| ≤ 2 := by rwa [abs_of_neg (lt_of_not_ge H)]
      calc
        _ ≤ |r (z+h)-2| *|d z| := by rw [← abs_mul]; exact le_abs_self _
        _ ≤ 2*|d z| := mul_le_mul_of_nonneg_right absBound (abs_nonneg _)
        _ ≤ _ := le_add_of_nonneg_left (mul_nonneg hL (abs_nonneg _))
  have parts (z) : (d z)^2 = 2*((r (z+h)-2)*d z) - ((r (z+h)-2)^2-(r z-2)^2) := by
    dsimp [d]; ring
  have en : jumpEnergy r h = 2*∑ z, (r (z+h)-2)*d z := by
    change ∑ z, (d z)^2 = _
    simp only [parts, sum_sub_distrib, ← mul_sum, shift_sum (fun z => (r z-2)^2), sub_self, sub_zero]
  have up := sum_le_sum (s:=univ) (fun z _ => term z)
  rw [sum_add_distrib, ← mul_sum, ← mul_sum, shift_sum (fun z => |r z-2|)] at up
  change _ ≤ L*deviation A+2*∑ z, |d z| at up
  change jumpEnergy r h ≤ _
  rw [en]
  linarith

private theorem max_le_card (A : Finset G) : maxDifference A ≤ A.card := by
  apply Finset.sup_le
  intro h _
  apply card_le_card_of_injOn Prod.fst
  · intro u hu
    exact (mem_product.mp (mem_filter.mp hu).1).1
  · rintro ⟨a,b⟩ hab ⟨c,d⟩ hcd e
    change a = c at e
    subst c
    have b1 : a-b=h := (mem_filter.mp hab).2
    have b2 : a-d=h := (mem_filter.mp hcd).2
    exact Prod.ext rfl (sub_right_inj.mp (b1.trans b2.symm))

private theorem uniform_lower (A : Finset G) {h : G} (hh : h ≠ 0) :
    2*((A.card:ℝ)-maxDifference A)^2 ≤ jumpEnergy (fun z => reps A z) h := by
  have hd : diffReps A h ≤ maxDifference A :=
    Finset.le_sup (f := fun z => diffReps A z) (mem_erase.mpr ⟨hh,mem_univ _⟩)
  have h1 : 0 ≤ (A.card:ℝ)-maxDifference A := sub_nonneg.mpr (by exact_mod_cast max_le_card A)
  have h2 : (A.card:ℝ)-maxDifference A ≤ (A.card:ℝ)-diffReps A h :=
    sub_le_sub_left (by exact_mod_cast hd) _
  exact (mul_le_mul_of_nonneg_left ((sq_le_sq₀ h1 (h1.trans h2)).mpr h2) (by norm_num)).trans
    (jump_lower A hh)

section Limits

variable {ι : Type*} {l : Filter ι} (M : ι → ℕ+) (A : (i : ι) → Finset (ZMod (M i)))
    (big : Tendsto (fun i => (M i).val) l atTop)
    (size : Tendsto (fun i => ((A i).card:ℝ)/Real.sqrt (M i)) l (𝓝 (Real.sqrt 2)))
    (cover : Tendsto (fun i => (((A i)+(A i)).card:ℝ)/(M i:ℝ)) l (𝓝 1))

include big size cover in
private theorem deviation_vanish : Tendsto (fun i => deviation (A i)/(M i:ℝ)) l (𝓝 0) := by
  obtain ⟨hc,hc2⟩ := card_limits M (fun i => (A i).card) big size
  have h := (((hc2.add (tendsto_const_nhds (x:=(2:ℝ)))).sub (cover.const_mul 4)).add (hc.const_mul 2))
  norm_num at h
  apply squeeze_zero (fun i => div_nonneg (sum_nonneg fun _ _ => abs_nonneg _) (by positivity)) _ h
  intro i
  have hm : (0:ℝ) < M i := by exact_mod_cast (M i).pos
  have up := div_le_div_of_nonneg_right (deviation_upper (A i)) hm.le
  rw [ZMod.card] at up
  apply up.trans_eq
  field_simp

include big size cover in
/-- Every nonzero shift has mean squared change with lower limit at least four.
The quantifier over shifts is inside the eventual assertion. -/
theorem all_shift_energy {L : ℝ} (hL : L < 4) :
    ∀ᶠ i in l, ∀ h : ZMod (M i), h ≠ 0 →
      L < jumpEnergy (fun z => reps (A i) z) h/(M i:ℝ) := by
  have hD := vanishing_max_difference M A big size cover
  have h := ((size.sub hD).pow 2).const_mul 2
  simp only [sub_zero, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)] at h
  norm_num at h
  filter_upwards [h.eventually_const_lt hL] with i hi
  intro s hs
  have hfloor := div_le_div_of_nonneg_right (uniform_lower (A i) hs) (show 0 ≤ (M i:ℝ) by positivity)
  apply lt_of_lt_of_le _ hfloor
  simpa only [← sub_div,div_pow,Real.sq_sqrt (show 0 ≤ (M i:ℝ) by positivity),mul_div_assoc] using hi

include big size cover in
/-- Every nonzero shift has both an upward jump and a downward jump exceeding
any fixed threshold, uniformly over shifts, for density-one sum covers. -/
theorem all_shift_jumps (B : ℝ) : ∀ᶠ i in l, ∀ h : ZMod (M i), h ≠ 0 →
    (∃ z, B < (reps (A i) (z+h):ℝ)-reps (A i) z) ∧
    (∃ z, B < (reps (A i) z:ℝ)-reps (A i) (z+h)) := by
  let L := max B 0
  have small := (deviation_vanish M A big size cover).const_mul (2*L+8)
  simp only [mul_zero] at small
  filter_upwards [all_shift_energy M A big size cover (by norm_num : (1:ℝ)<4),
    small.eventually_lt_const (by norm_num : (0:ℝ)<1)] with i en err
  have up (h : ZMod (M i)) (hh : h ≠ 0) : ∃ z, B < (reps (A i) (z+h):ℝ)-reps (A i) z := by
    by_contra! bounded
    have bound := one_sided_energy (A i) h L (le_max_right _ _) (fun z => (bounded z).trans (le_max_left _ _))
    have hq := div_le_div_of_nonneg_right bound (show 0 ≤ (M i:ℝ) by positivity)
    rw [mul_div_assoc] at hq
    exact (en h hh).not_ge (hq.trans err.le)
  intro h hh
  obtain ⟨z,hz⟩ := up (-h) (neg_ne_zero.mpr hh)
  exact ⟨up h hh, z+(-h),by simpa using hz⟩

include big size in
/-- Specialization to the full cyclic two-bases in Green 33. -/
theorem green_shift_jumps (full : ∀ i, (A i)+(A i)=univ) (B : ℝ) :
    ∀ᶠ i in l, ∀ h : ZMod (M i), h ≠ 0 →
    (∃ z, B < (reps (A i) (z+h):ℝ)-reps (A i) z) ∧
    (∃ z, B < (reps (A i) z:ℝ)-reps (A i) (z+h)) := by
  apply all_shift_jumps M A big size _ B
  refine tendsto_const_nhds.congr (fun i => ?_)
  rw [full,card_univ,ZMod.card,div_self (by exact_mod_cast (M i).ne_zero)]

end Limits

omit [DecidableEq G] in
private theorem subgroup_energy (H : AddSubgroup G) [Fintype H] (e : G → ℝ) :
    ∑ h : H, jumpEnergy e (h:G) ≤ 2*(Fintype.card H:ℝ)*∑ z, e z^2 := by
  classical
  let u (z : G) := ∑ h : H, e (z+(h:G))
  have inv (z : G) (h : H) : u (z+(h:G)) = u z := by
    exact Fintype.sum_equiv (Equiv.addLeft h) _ _ (fun j => by simp [add_assoc])
  have id : (∑ z, u z^2) = (Fintype.card H:ℝ)*∑ z, e z*u z := by
    calc
      _ = ∑ z, ∑ h : H, e (z+(h:G))*u z := sum_congr rfl fun z _ => by rw [← sum_mul, sq]
      _ = ∑ h : H, ∑ z, e (z+(h:G))*u (z+(h:G)) := by rw [sum_comm]; simp only [inv]
      _ = _ := by simp only [shift_sum (fun z => e z*u z),sum_const,card_univ,nsmul_eq_mul]
  have nn : 0 ≤ ∑ z, e z*u z :=
    nonneg_of_mul_nonneg_right (id ▸ sum_nonneg fun z _ => sq_nonneg (u z)) (by positivity)
  have corr : (∑ h : H, ∑ z, e z*e (z+(h:G))) = ∑ z, e z*u z := by
    rw [sum_comm]
    simp only [u,mul_sum]
  simp only [energy_expand, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, ← mul_sum, corr]
  linarith

/-- Finite squared-error floor against any real profile that is constant on
cosets of a subgroup. The period and the profile may be chosen after the seed. -/
theorem periodic_residual (A : Finset G) (H : AddSubgroup G) [Fintype H]
    (f : G → ℝ) (period : ∀ z (h : H), f (z+(h:G)) = f z) :
    ((Fintype.card H:ℝ)-1)*((A.card:ℝ)-maxDifference A)^2 ≤
      (Fintype.card H:ℝ)*∑ z, ((reps A z:ℝ)-f z)^2 := by
  classical
  let e (z : G) := (reps A z:ℝ)-f z
  let k : ℝ := ((A.card:ℝ)-maxDifference A)^2
  have same (h : H) : jumpEnergy e (h:G) = jumpEnergy (fun z => reps A z) (h:G) := by
    unfold jumpEnergy
    apply sum_congr rfl
    intro z _
    simp only [e,period]
    ring
  have low (h : H) : 2*k-(if h=0 then 2*k else 0) ≤ jumpEnergy e (h:G) := by
    by_cases zero : h=0
    · subst h
      simp [jumpEnergy]
    · rw [if_neg zero, sub_zero,same]
      exact uniform_lower A (fun eq => zero (Subtype.ext eq))
  have h := (sum_le_sum (s:=univ) (fun h _ => low h)).trans (subgroup_energy H e)
  simp only [sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, sum_ite_eq', mem_univ, if_true] at h
  change ((Fintype.card H:ℝ)-1)*k ≤ (Fintype.card H:ℝ)*∑ z, e z^2
  linarith

/-- A coset-constant fit, with any subgroup and any fitted values, retains at
least the indicated mean squared residual in the density-one limit. -/
theorem all_periodic_errors {ι : Type*} {l : Filter ι} (M : ι → ℕ+)
    (A : (i : ι) → Finset (ZMod (M i))) (big : Tendsto (fun i => (M i).val) l atTop)
    (size : Tendsto (fun i => ((A i).card:ℝ)/Real.sqrt (M i)) l (𝓝 (Real.sqrt 2)))
    (cover : Tendsto (fun i => (((A i)+(A i)).card:ℝ)/(M i:ℝ)) l (𝓝 1))
    {B : ℝ} (hB : B < 2) : ∀ᶠ i in l, ∀ (H : AddSubgroup (ZMod (M i))) [Fintype H]
    (f : ZMod (M i) → ℝ), (∀ z (h:H), f (z+(h:ZMod (M i))) = f z) →
    B*(1-(Fintype.card H:ℝ)⁻¹) ≤ (∑ z, ((reps (A i) z:ℝ)-f z)^2)/(M i:ℝ) := by
  have diff := vanishing_max_difference M A big size cover
  have h := (size.sub diff).pow 2
  simp only [sub_zero,Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)] at h
  filter_upwards [h.eventually_const_lt hB] with i hi
  intro H _ f period
  let t : ℝ := Fintype.card H
  have ht : (1:ℝ) ≤ t := by
    dsimp [t]
    exact_mod_cast (show 1 ≤ Fintype.card H from Fintype.card_pos)
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hm : (0:ℝ) < M i := by exact_mod_cast (M i).pos
  have lo : B*(M i:ℝ) ≤ ((A i).card-maxDifference (A i):ℝ)^2 := by
    apply (le_div_iff₀ hm).mp
    simpa only [← sub_div,div_pow,Real.sq_sqrt hm.le] using hi.le
  have extra := mul_le_mul_of_nonneg_left lo (sub_nonneg.mpr ht)
  have bound := extra.trans (periodic_residual (A i) H f period)
  change B*(1-t⁻¹) ≤ _/(M i:ℝ)
  apply (le_div_iff₀ hm).mpr
  apply (mul_le_mul_iff_right₀ htpos).mp
  calc
    _ = (t-1)*(B*(M i:ℝ)) := by field_simp
    _ ≤ _ := bound

#print axioms shifted_correlation
#print axioms sum_difference_jumps
#print axioms jump_lower
#print axioms deviation_upper
#print axioms one_sided_energy
#print axioms all_shift_energy
#print axioms all_shift_jumps
#print axioms green_shift_jumps
#print axioms periodic_residual
#print axioms all_periodic_errors
end Green33ShiftVariation
