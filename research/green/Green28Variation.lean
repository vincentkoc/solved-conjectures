import Green28DigitTranspose

/-! Total variation from the uniform law on a finite support. -/

namespace Green28Variation

open Green28 Green28DigitTranspose Finset
open scoped ENNReal

/-- Bhattacharyya affinity with the uniform law on the given set. -/
noncomputable def affinity {α : Type*} (P : PMF α) (A : Finset α) : ℝ :=
  ∑ x ∈ A, Real.sqrt (P x).toReal * Real.sqrt (A.card:ℝ)⁻¹

/-- Half the finite ℓ¹ distance to the uniform law on the given support. -/
noncomputable def variation {α : Type*} (P : PMF α) (A : Finset α) : ℝ :=
  (∑ x ∈ A, |(P x).toReal-(A.card:ℝ)⁻¹|)/2

private theorem total {α : Type*} {P : PMF α} {A : Finset α} (supp : P.support=(A:Set α)) :
    ∑ x ∈ A, (P x).toReal = 1 := by
  have sum : ∑' x, P x = ∑ x ∈ A, P x :=
    tsum_eq_sum (fun x hx => (P.apply_eq_zero_iff x).mpr (supp ▸ hx))
  rw [←ENNReal.toReal_sum (fun x _ => P.apply_ne_top x),←sum,P.tsum_coe,ENNReal.toReal_one]

private theorem average_total {α : Type*} {P : PMF α} {A : Finset α} (supp : P.support=(A:Set α)) :
    ∑ x ∈ A, ((P x).toReal+(A.card:ℝ)⁻¹) = 2 := by
  have ne : A.Nonempty := by simpa only [←Finset.coe_nonempty,supp] using P.support_nonempty
  rw [sum_add_distrib,total supp]
  norm_num [ne.card_ne_zero]

private theorem affinity_nonneg {α : Type*} (P : PMF α) (A : Finset α) : 0≤affinity P A :=
  sum_nonneg (fun _ _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

private theorem term_bound {p u : ℝ} (hp : 0≤p) (hu : 0≤u) :
    2*(Real.sqrt p*Real.sqrt u)≤p+u ∧ (p≠u → 2*(Real.sqrt p*Real.sqrt u)<p+u) := by
  have ep := Real.sq_sqrt hp
  have eu := Real.sq_sqrt hu
  constructor
  · nlinarith [sq_nonneg (Real.sqrt p-Real.sqrt u)]
  · intro ne
    have d : Real.sqrt p-Real.sqrt u ≠ 0 := by
      intro he
      apply ne
      have h := sub_eq_zero.mp he
      nlinarith [congrArg (·^2) h]
    nlinarith [sq_pos_of_ne_zero d]

/-- Nonuniformity makes the affinity strictly smaller than one. -/
theorem affinity_lt_one {P : PMF ℤ} {A : Finset ℤ} (supp : P.support=(A:Set ℤ))
    (notflat : ¬IsUniformOnSupport P) : affinity P A<1 := by
  classical
  have ne : A.Nonempty := by simpa only [←Finset.coe_nonempty,supp] using P.support_nonempty
  have uneven : ∃ x∈A, (P x).toReal ≠ (A.card:ℝ)⁻¹ := by
    by_contra! same
    apply notflat
    refine ⟨A,ne,PMF.ext fun x => ?_⟩
    by_cases hx : x∈A
    · apply (ENNReal.toReal_eq_toReal_iff' (P.apply_ne_top _) ((PMF.uniformOfFinset A ne).apply_ne_top _)).mp
      simpa only [PMF.uniformOfFinset_apply_of_mem ne hx,ENNReal.toReal_inv,ENNReal.toReal_natCast] using same x hx
    · rw [PMF.uniformOfFinset_apply_of_notMem ne hx]
      exact (P.apply_eq_zero_iff x).mpr (supp ▸ hx)
  have b (x : ℤ) := term_bound (p := (P x).toReal) (u := (A.card:ℝ)⁻¹) ENNReal.toReal_nonneg (by positivity)
  obtain ⟨x,hx,e⟩ := uneven
  have h := Finset.sum_lt_sum (s := A) (fun z _ => (b z).1) ⟨x,hx,(b x).2 e⟩
  rw [←mul_sum,average_total supp] at h
  unfold affinity
  linarith

/-- Total variation dominates one minus the affinity on the same support. -/
theorem one_sub_affinity_le_variation {α : Type*} {P : PMF α} {A : Finset α}
    (supp : P.support=(A:Set α)) : 1-affinity P A ≤ variation P A := by
  have bound (p u : ℝ) (hp : 0≤p) (hu : 0≤u) : p+u-2*(Real.sqrt p*Real.sqrt u)≤|p-u| := by
    have ep := Real.sq_sqrt hp
    have eu := Real.sq_sqrt hu
    rcases le_total p u with h|h
    · rw [abs_of_nonpos (sub_nonpos.mpr h)]
      nlinarith [mul_nonneg (Real.sqrt_nonneg p) (sub_nonneg.mpr (Real.sqrt_le_sqrt h))]
    · rw [abs_of_nonneg (sub_nonneg.mpr h)]
      nlinarith [mul_nonneg (Real.sqrt_nonneg u) (sub_nonneg.mpr (Real.sqrt_le_sqrt h))]
  have h := Finset.sum_le_sum (s := A) (fun x _ => bound (P x).toReal (A.card:ℝ)⁻¹ ENNReal.toReal_nonneg (by positivity))
  rw [sum_sub_distrib,←mul_sum,average_total supp] at h
  unfold affinity variation
  linarith

private theorem mapped_values {α β : Type*} [DecidableEq β] {P : PMF α} {A : Finset α}
    (supp : P.support=(A:Set α)) {f : α → β} (inj : Set.InjOn f (A:Set α)) :
    (P.map f).support=(A.image f:Set β) ∧ ∀ x∈A, P.map f (f x)=P x := by
  classical
  constructor
  · rw [PMF.support_map,supp,Finset.coe_image]
  · intro x hx
    rw [PMF.map_apply,tsum_eq_single x]
    · simp
    · intro y ne
      by_cases hy : y∈A
      · simp [show f x ≠ f y from fun e => ne (inj hx hy e).symm]
      · simp [(P.apply_eq_zero_iff y).mpr (supp ▸ hy)]

private theorem map_scores {α β : Type*} [DecidableEq β] {P : PMF α} {A : Finset α}
    (supp : P.support=(A:Set α)) {f : α → β} (inj : Set.InjOn f (A:Set α)) :
    affinity (P.map f) (A.image f)=affinity P A ∧ variation (P.map f) (A.image f)=variation P A := by
  classical
  have val := (mapped_values supp inj).2
  constructor
  · unfold affinity
    rw [Finset.card_image_of_injOn inj,Finset.sum_image (fun x hx y hy e => inj hx hy e)]
    exact sum_congr rfl (fun x hx => by rw [val x hx])
  · unfold variation
    rw [Finset.card_image_of_injOn inj,Finset.sum_image (fun x hx y hy e => inj hx hy e)]
    congr 1
    exact sum_congr rfl (fun x hx => by rw [val x hx])

private theorem prod_support {P Q : PMF ℤ} {A B : Finset ℤ} (pa : P.support=(A:Set ℤ))
    (qb : Q.support=(B:Set ℤ)) : (pairLaw P Q).support=(A ×ˢ B : Finset (ℤ×ℤ)) := by
  ext ⟨x,y⟩
  simp only [PMF.mem_support_iff,pairLaw_apply,mul_ne_zero_iff,Finset.mem_coe,Finset.mem_product]
  simp only [←PMF.mem_support_iff,pa,qb,Finset.mem_coe]

private theorem prod_affinity (P Q : PMF ℤ) (A B : Finset ℤ) :
    affinity (pairLaw P Q) (A ×ˢ B) = affinity P A*affinity Q B := by
  unfold affinity
  rw [Finset.sum_product,Finset.sum_mul]
  apply sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro y _
  rw [pairLaw_apply,ENNReal.toReal_mul,Finset.card_product,Nat.cast_mul,mul_inv,
    Real.sqrt_mul ENNReal.toReal_nonneg,Real.sqrt_mul (by positivity)]
  ring

/-- A single law paired with its digit-transposed independent copy. -/
private structure Trial where
  law : PMF ℤ
  sites : Finset ℤ
  supp : law.support=(sites:Set ℤ)
  outcomes : Finset ℤ
  inhabited : outcomes.Nonempty
  sum_eq : indepSum law (law.map transpose)=PMF.uniformOfFinset outcomes inhabited

private theorem Trial.square (T : Trial) :
    ∃ U : Trial, affinity U.law U.sites = (affinity T.law T.sites)^2 := by
  classical
  let B := T.sites.image transpose
  have inj := transpose_involutive.injective.injOn (s := (T.sites:Set ℤ))
  have qb : (T.law.map transpose).support=(B:Set ℤ) := (mapped_values T.supp inj).1
  have same := (map_scores T.supp inj).1
  obtain ⟨L⟩ := exists_square_lift T.inhabited T.sum_eq
  have source := prod_support T.supp qb
  have i : Set.InjOn L.label ((T.sites ×ˢ B : Finset (ℤ×ℤ)):Set (ℤ×ℤ)) := source ▸ L.label_inj
  let C := (T.sites ×ˢ B).image L.label
  have supp : L.law.support=(C:Set ℤ) := L.law_eq ▸ (mapped_values source i).1
  refine ⟨⟨L.law,C,supp,L.outcomes,L.inhabited,L.sum_eq⟩,?_⟩
  change affinity L.law C=_
  rw [L.law_eq,(map_scores source i).1,prod_affinity,show affinity (T.law.map transpose) B=affinity T.law T.sites from same,pow_two]

private theorem Trial.powers (T : Trial) (n : ℕ) :
    ∃ U : Trial, affinity U.law U.sites=(affinity T.law T.sites)^(2^n) := by
  induction n with
  | zero => exact ⟨T,by simp⟩
  | succ n ih =>
    obtain ⟨U,hu⟩ := ih
    obtain ⟨V,hv⟩ := U.square
    exact ⟨V,by rw [hv,hu,←pow_mul,pow_succ]⟩

/-- Failure of Green 28 would force both marginals arbitrarily far in total
variation from the uniform laws on their own supports, even when one is a
fixed relabelling of an independent copy of the other. -/
theorem far_marginals_of_failure (fail : ¬(type_of% Green28.green_28)) (ε : ℝ) (pos : 0<ε) :
    ∃ (R : PMF ℤ) (A B : Finset ℤ), R.support=(A:Set ℤ) ∧ (R.map transpose).support=(B:Set ℤ) ∧
      IsUniformOnSupport (indepSum R (R.map transpose)) ∧
      1-ε < variation R A ∧ 1-ε < variation (R.map transpose) B := by
  classical
  change ¬(∀ P Q : PMF ℤ, _ → _) at fail
  push Not at fail
  obtain ⟨P,Q,⟨_,_,S,sne,eq⟩,bad⟩ := fail
  obtain ⟨L⟩ := exists_square_lift sne eq
  have nf : ¬IsUniformOnSupport L.law := fun h => bad (L.uniform_iff.mp h).1 (L.uniform_iff.mp h).2
  let A := L.finite.toFinset
  have supp : L.law.support=(A:Set ℤ) := by simp [A]
  let T : Trial := ⟨L.law,A,supp,L.outcomes,L.inhabited,L.sum_eq⟩
  have lt := affinity_lt_one supp nf
  obtain ⟨n,hn⟩ := exists_pow_lt_of_lt_one pos lt
  obtain ⟨U,hu⟩ := T.powers n
  have tiny : affinity U.law U.sites<ε := by
    rw [hu]
    exact (pow_le_pow_of_le_one (affinity_nonneg _ _) lt.le (Nat.lt_two_pow_self (n := n)).le).trans_lt hn
  let B := U.sites.image transpose
  have inj := transpose_involutive.injective.injOn (s := (U.sites:Set ℤ))
  have v := (map_scores U.supp inj).2
  have far := one_sub_affinity_le_variation U.supp
  refine ⟨U.law,U.sites,B,U.supp,(mapped_values U.supp inj).1,
    ⟨U.outcomes,U.inhabited,U.sum_eq⟩,by linarith,?_⟩
  rw [show variation (U.law.map transpose) B=variation U.law U.sites from v]
  linarith

private theorem variation_zero {P : PMF ℤ} {A : Finset ℤ} (supp : P.support=(A:Set ℤ))
    (flat : IsUniformOnSupport P) : variation P A=0 := by
  obtain ⟨S,ne,rfl⟩ := flat
  have e : S=A := by apply Finset.coe_injective; simpa only [PMF.support_uniformOfFinset] using supp
  subst A
  unfold variation
  have val (x : ℤ) (hx : x∈S) : ((PMF.uniformOfFinset S ne) x).toReal=(S.card:ℝ)⁻¹ := by
    rw [PMF.uniformOfFinset_apply_of_mem ne hx,ENNReal.toReal_inv,ENNReal.toReal_natCast]
  apply div_eq_zero_iff.mpr (Or.inl ?_)
  apply Finset.sum_eq_zero
  intro x hx
  rw [val _ hx,sub_self,abs_zero]

/-- It suffices to prove any positive uniform gap from total variation one
for at least one of the two input laws in each instance. -/
theorem green_28_iff_variation_gap :
    (type_of% Green28.green_28) ↔
    ∃ δ : ℝ, 0<δ ∧ ∀ (P Q : PMF ℤ) (A B : Finset ℤ), P.support=(A:Set ℤ) →
      Q.support=(B:Set ℤ) → IsUniformOnSupport (indepSum P Q) →
      variation P A≤1-δ ∨ variation Q B≤1-δ := by
  constructor
  · intro truth
    refine ⟨1,zero_lt_one,?_⟩
    intro P Q A B pa qb sum
    obtain ⟨pf,qf⟩ := Green28UniformSums.finite_of_uniform_sum sum
    have flat := (truth P Q ⟨pf,qf,sum⟩).1
    exact Or.inl (by rw [variation_zero pa flat]; norm_num)
  · rintro ⟨δ,pos,gap⟩
    by_contra fail
    obtain ⟨R,A,B,pa,qb,sum,far,far'⟩ := far_marginals_of_failure fail δ pos
    exact (gap _ _ _ _ pa qb sum).elim (not_le.mpr far) (not_le.mpr far')

#print axioms affinity_lt_one
#print axioms one_sub_affinity_le_variation
#print axioms far_marginals_of_failure
#print axioms green_28_iff_variation_gap

end Green28Variation
