import Green33ApproximateCovers
import FormalConjectures.ErdosProblems.«840»

/-! A transfer from cyclic Green bases to quasi-Sidon subsets of integer intervals. -/

open Finset Filter Asymptotics Green33MaximalOrders Green33StrictReduction Green33ApproximateCovers
open scoped Pointwise Topology

namespace Green33QuasiSidon

/-- Positive integer representatives of the cyclic basis points. -/
def intervalCopy {M : ℕ+} (A : Finset (ZMod M)) : Finset ℕ := A.image (fun x => x.val+1)

theorem intervalCopy_spec {M : ℕ+} (A : Finset (ZMod M)) (hA : StrictCover A) :
    intervalCopy A ⊆ Icc 1 M.val ∧ (intervalCopy A).card=A.card ∧
      M.val ≤ (intervalCopy A+intervalCopy A).card := by
  let f (x : ZMod M) := x.val+1
  let B := intervalCopy A
  have hi : Function.Injective f := fun x y h => ZMod.val_injective _ (Nat.succ.inj h)
  refine ⟨?_,card_image_of_injective _ hi,?_⟩
  · intro x hx
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hx
    exact mem_Icc.mpr ⟨Nat.succ_pos _,a.val_lt⟩
  · let g (v : ℕ) : ZMod M := (v : ZMod M)-2
    have hsur : (B+B).image g = univ := by
      apply eq_univ_of_forall
      intro x
      obtain ⟨a,ha,b,hb,_,rfl⟩ := hA x
      refine mem_image.mpr ⟨f a+f b,mem_add.mpr
        ⟨_,mem_image_of_mem _ ha,_,mem_image_of_mem _ hb,rfl⟩,?_⟩
      simp only [g,f,Nat.cast_add,Nat.cast_one,ZMod.natCast_zmod_val]
      ring
    have h := card_image_le (s := B+B) (f := g)
    simpa [hsur,ZMod.card] using h

theorem order_le_choose {M : ℕ+} {A : Finset (ZMod M)} (h : StrictCover A) :
    M.val ≤ A.card.choose 2 := by
  have hs : strictSums A = univ := eq_univ_of_forall (fun x => mem_strictSums.mpr (h x))
  have hc := card_image_le (s := A.powersetCard 2) (f := pairSum)
  change (strictSums A).card ≤ _ at hc
  simpa [hs,ZMod.card] using hc

/-- A finite interval can accommodate all the residues of a strict extremizer.
Padding the lifted representatives gives exactly the requested budget. -/
theorem finite_transfer {k N : ℕ} (hk : k ≤ N) (hcap : k.choose 2 ≤ N) :
    ∃ B : Finset ℕ, B ⊆ Icc 1 N ∧ B.card=k ∧ maxOrder true k ≤ (B+B).card := by
  classical
  have feasible : maxOrder true k = 0 ∨ ∃ M : ℕ+, M.val=maxOrder true k ∧
      ∃ A : Finset (ZMod M), A.card≤k ∧ Covers true A := by
    let F (n : ℕ) := n=0 ∨ ∃ M : ℕ+, M.val=n ∧ ∃ A : Finset (ZMod M), A.card≤k ∧ Covers true A
    let : DecidablePred F := fun n => Classical.propDecidable (F n)
    change F (Nat.findGreatest F (k^2))
    exact Nat.findGreatest_spec (Nat.zero_le _) (show F 0 from Or.inl rfl)
  rcases feasible with h | ⟨M,hm,A,ha,hA⟩
  · obtain ⟨B,_,hB,hBk⟩ := exists_subsuperset_card_eq (empty_subset (Icc 1 N))
      (by simp : (∅ : Finset ℕ).card ≤ k) (show k ≤ (Icc 1 N).card by simpa using hk)
    exact ⟨B,hB,hBk,by simp [h]⟩
  · have h := covers_true_iff.mp hA
    have hM := order_le_choose h
    let D := intervalCopy A
    obtain ⟨hD,hd,hord⟩ := intervalCopy_spec A h
    have hMN := hM.trans ((Nat.choose_le_choose 2 ha).trans hcap)
    obtain ⟨B,hDB,hB,hBk⟩ := exists_subsuperset_card_eq
      (hD.trans (Icc_subset_Icc le_rfl hMN)) (hd.trans_le ha)
      (show k ≤ (Icc 1 N).card by simpa using hk)
    exact ⟨B,hB,hBk,hm ▸ hord.trans (card_le_card (add_subset_add hDB hDB))⟩

/-- Size budget for the interval of length N. -/
def budget (N : ℕ) := Nat.sqrt (2*N)

theorem budget_fits (N : ℕ) : budget N ≤ N ∧ (budget N).choose 2 ≤ N := by
  have hk := Nat.sqrt_le' (2*N)
  change budget N ^ 2 ≤ 2*N at hk
  constructor
  · exact Nat.lt_succ_iff.mp (Nat.sqrt_lt'.mpr (by nlinarith : 2*N < (N+1)^2))
  · rw [Nat.choose_two_right]
    have h := Nat.mul_le_mul_left (budget N) (Nat.sub_le (budget N) 1)
    rw [← sq] at h
    omega

private lemma budget_floor (N : ℕ) : budget N = ⌊Real.sqrt 2*Real.sqrt N⌋₊ := by
  rw [← Real.sqrt_mul (by norm_num)]
  simpa [budget] using (Real.nat_floor_real_sqrt_eq_nat_sqrt (a := 2*N)).symm

theorem budget_scale :
    Tendsto budget atTop atTop ∧
    Tendsto (fun N => (budget N : ℝ)/Real.sqrt N) atTop (𝓝 (Real.sqrt 2)) := by
  have hroot := Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  constructor
  · rw [show budget = (fun n : ℕ => ⌊Real.sqrt 2*Real.sqrt n⌋₊) from funext budget_floor]
    simpa [Function.comp_def] using tendsto_nat_floor_atTop.comp
      (hroot.const_mul_atTop (Real.sqrt_pos_of_pos (by norm_num : (0:ℝ)<2)))
  · simpa [Function.comp_def,budget_floor] using
      (tendsto_nat_floor_mul_div_atTop (Real.sqrt_nonneg 2)).comp hroot

theorem sumset_upper (B : Finset ℕ) : (B+B).card ≤ (B.card+1).choose 2 := by
  rw [← card_sym2]
  have h : B+B ⊆ B.sym2.image ordinarySum := by
    intro x hx
    obtain ⟨a,ha,b,hb,rfl⟩ := mem_add.mp hx
    exact mem_image.mpr ⟨Sym2.mk a b,mk_mem_sym2_iff.mpr ⟨ha,hb⟩,rfl⟩
  exact (card_le_card h).trans card_image_le

/-- Both unordered-pair counts have the interval length as their scale along
any sequence of lengths tending to infinity at the critical size. -/
theorem pair_scales_along {N : ℕ → ℕ} (k : ℕ → ℕ)
    (big : Tendsto N atTop atTop)
    (size : Tendsto (fun i => (k i:ℝ)/Real.sqrt (N i)) atTop (𝓝 (Real.sqrt 2))) :
    Tendsto (fun i => ((k i).choose 2:ℝ)/(N i:ℝ)) atTop (𝓝 1) ∧
    Tendsto (fun i => ((k i+1).choose 2:ℝ)/(N i:ℝ)) atTop (𝓝 1) := by
  have quad : Tendsto (fun i => (k i:ℝ)^2/(N i:ℝ)) atTop (𝓝 2) := by
    simpa only [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ)≤2),Real.sq_sqrt (Nat.cast_nonneg _)] using size.pow 2
  have lin : Tendsto (fun i => (k i:ℝ)/(N i:ℝ)) atTop (𝓝 0) := by
    have h := size.div_atTop (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp big))
    apply h.congr
    intro i
    change (k i:ℝ)/Real.sqrt (N i)/Real.sqrt (N i)=_
    rw [div_div,← sq,Real.sq_sqrt (Nat.cast_nonneg _)]
  constructor
  · have h := (quad.sub lin).div_const 2
    norm_num at h
    apply h.congr
    intro i
    rw [Nat.cast_choose_two]
    ring
  · have h := (quad.add lin).div_const 2
    norm_num at h
    apply h.congr
    intro i
    rw [Nat.cast_choose_two]
    push_cast
    ring

/-- The unordered pair counts on either diagonal convention have the same scale. -/
theorem pair_scales_of_size {k : ℕ → ℕ}
    (h : Tendsto (fun N => (k N : ℝ)/Real.sqrt N) atTop (𝓝 (Real.sqrt 2))) :
    Tendsto (fun N => ((k N).choose 2 : ℝ)/(N : ℝ)) atTop (𝓝 1) ∧
    Tendsto (fun N => ((k N+1).choose 2 : ℝ)/(N : ℝ)) atTop (𝓝 1) :=
  pair_scales_along (N:=id) k tendsto_id h

/-- If Green 33 holds, the constant √2 is attained in the all-interval
quasi-Sidon problem of Erdős and Freud, in the pinned upstream definition. -/
theorem green_implies_erdos840 (hGreen : OrdinaryLimit) :
    Erdos840.IsQuasiSidonConstant (Real.sqrt 2) := by
  choose B hsub hcard hsum using
    (fun n : ℕ => finite_transfer (budget_fits n).1 (budget_fits n).2)
  refine ⟨B,hsub,?_,?_⟩
  · apply isEquivalent_of_tendsto_one
    have h := budget_scale.2.div_const (Real.sqrt 2)
    rw [div_self (Real.sqrt_pos_of_pos (by norm_num : (0:ℝ)<2)).ne'] at h
    exact h.congr (fun n => by simp [Pi.div_apply,hcard,div_div,mul_comm])
  · have hmax := (budget_limits true).comp budget_scale.1
    rw [green_iff_orderConstant.mp hGreen] at hmax
    have hlow : Tendsto (fun n => (maxOrder true (budget n) : ℝ)/(n : ℝ)) atTop (𝓝 1) := by
      have ht := hmax.mul (budget_scale.2.pow 2)
      norm_num [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)] at ht
      apply ht.congr'
      filter_upwards [budget_scale.1.eventually_gt_atTop 0] with n hn
      have hk : (budget n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      change _/(budget n : ℝ)^2*((budget n : ℝ)/Real.sqrt n)^2 = _
      rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
      field_simp
    have hden : Tendsto (fun n => ((B n+B n).card : ℝ)/(n : ℝ)) atTop (𝓝 1) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlow (pair_scales_of_size budget_scale.2).2
      · intro n
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
        exact Nat.cast_le.mpr (hsum n)
      · intro n
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
        exact Nat.cast_le.mpr (hcard n ▸ sumset_upper (B n))
    have he₁ : (fun n => ((B n+B n).card : ℝ)) ~[atTop] (fun n : ℕ => (n : ℝ)) :=
      isEquivalent_of_tendsto_one hden
    have he₂ : (fun n => ((B n).card.choose 2 : ℝ)) ~[atTop] (fun n : ℕ => (n : ℝ)) := by
      apply isEquivalent_of_tendsto_one
      change Tendsto (fun n => ((B n).card.choose 2 : ℝ)/(n : ℝ)) atTop (𝓝 1)
      simpa only [hcard] using (pair_scales_of_size budget_scale.2).1
    exact he₁.trans he₂.symm

#print axioms intervalCopy_spec
#print axioms order_le_choose
#print axioms budget_fits
#print axioms budget_scale
#print axioms sumset_upper
#print axioms pair_scales_along
#print axioms pair_scales_of_size
#print axioms finite_transfer
#print axioms green_implies_erdos840

end Green33QuasiSidon
