import ThetaPrimeClassBV

/-! Positive theta primes in every reduced residue class of almost all moduli. -/
namespace Arxiv.«2501.03234».ThetaPrimeClassCoverage
open Filter Real Finset ThetaPrimeClassBV
open scoped Classical
noncomputable section

/-- Except for O_A(Q/(log X)^A) moduli up to Q=floor(X^theta), every
reduced class contains at least half its ordinary expected number of primes
satisfying the original slope. The input is the ordinary BV statement. -/
theorem from_sparse (H : Ordinary) {θ A : ℝ} (hθ : θ<1/2) (hA : 0<A) {P : ℕ → Prop} (hP : Sparse P) :
    ∃ K : ℝ,0<K ∧ ∀ᶠ X : ℕ in atTop,
      let Q := ⌊(X:ℝ)^θ⌋₊
      ∃ D ⊆ Icc 1 Q,(D.card:ℝ) ≤ K*Q/(log X)^A ∧
      ∀ q∈Icc 1 Q,q∉D → ∀ a : (ZMod q)ˣ,
        (X.primeCounting:ℝ)/(2*q.totient) ≤ selectedCount P X q a := by
  classical
  obtain ⟨C,hC,h⟩ := ThetaPrimeClassBV.from_sparse H hθ (show 1≤A+1 by linarith) hP
  refine ⟨8*C,by positivity,?_⟩
  have hn := tendsto_natCast_atTop_atTop (R:=ℝ)
  have hl := tendsto_log_atTop.comp hn
  filter_upwards [h,ThetaPrimeDensity.prime_count_lower,hl.eventually_gt_atTop 0,eventually_ge_atTop 2]
    with X he hπ hL hX Q
  let M := (X.primeCounting:ℝ)
  let L := log (X:ℝ)
  let D := (Icc 1 Q).filter (fun q => ∃ a : (ZMod q)ˣ,(selectedCount P X q a:ℝ) < M/(2*q.totient))
  let E (q : ℕ) := error (selectedCount P) X q
  have hM : 0<M := by
    dsimp [M];rw [←Nat.primesLE_card_eq_primeCounting]
    exact_mod_cast card_pos.mpr ⟨2,Nat.mem_primesLE.mpr ⟨hX,Nat.prime_two⟩⟩
  change 0<L at hL
  have h₂ : (1:ℝ)/2≤log 2 := by have hh := one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2);norm_num at hh;linarith
  have hX' : (X:ℝ)≤4*M*L := by
    change log 2/2*(X:ℝ) ≤ M*L at hπ
    nlinarith only [hπ,mul_le_mul_of_nonneg_right h₂ (Nat.cast_nonneg (α:=ℝ) X)]
  have hterm {q : ℕ} (hq : q∈Icc 1 Q) (a : (ZMod q)ˣ) :
      |(selectedCount P X q a:ℝ)-M/q.totient| ≤ E q := by
    let : NeZero q := ⟨(show 0<q from (mem_Icc.mp hq).1).ne'⟩
    have h := le_ciSup (Finite.bddAbove_range (fun b : (ZMod q)ˣ =>
      |(selectedCount P X q b:ℝ)-(⌊(X:ℝ)⌋₊.primeCounting:ℝ)/q.totient|)) a
    simpa only [E,error,M,Nat.floor_natCast] using h
  have hnon (q : ℕ) (hq : q∈Icc 1 Q) : 0≤E q := (abs_nonneg _).trans (hterm hq 1)
  have hbad (q : ℕ) (hq : q∈D) : M≤2*(Q:ℝ)*E q := by
    obtain ⟨hqr,a,ha⟩ := mem_filter.mp hq
    have hf : 0<(q.totient:ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr (mem_Icc.mp hqr).1)
    have hh := (abs_le.mp (hterm hqr a)).1
    have hdiv : M/(2*q.totient) ≤ E q := by
      have ht : M/q.totient=2*(M/(2*q.totient)) := by ring
      rw [ht] at hh;linarith
    have hfQ : (q.totient:ℝ)≤Q := by exact_mod_cast (Nat.totient_le q).trans (mem_Icc.mp hqr).2
    have hb := (div_le_iff₀ (by positivity)).mp hdiv
    nlinarith only [hb,mul_le_mul_of_nonneg_right hfQ (hnon q hqr)]
  refine ⟨D,filter_subset _ _,?_,?_⟩
  · have hignore : (D.card:ℝ)*M ≤ (2*(Q:ℝ))*(C*X/L^(A+1)) := calc
      _ = ∑ _q∈D,M := by simp
      _ ≤ ∑ q∈D,2*Q*E q := sum_le_sum hbad
      _ ≤ ∑ q∈Icc 1 Q,2*Q*E q := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun q hq _ => by positivity [hnon q hq])
      _ ≤ _ := by rw [←mul_sum];exact mul_le_mul_of_nonneg_left he (by positivity)
    apply (mul_le_mul_iff_left₀ hM).mp
    calc _ ≤ _ := hignore
         _ ≤ (2*(Q:ℝ))*(C*(4*M*L)/L^(A+1)) := by gcongr
         _ = (8*C*(Q:ℝ)/L^A)*M := by rw [rpow_add_one hL.ne'];field_simp;ring
  · intro q hq hd a;by_contra! hbad
    exact hd (mem_filter.mpr ⟨hq,a,hbad⟩)

theorem slope (H : Ordinary) {θ A : ℝ} (hθ : θ<1/2) (hA : 0<A) (k : ℕ) :
    ∃ K : ℝ,0<K ∧ ∀ᶠ X : ℕ in atTop,
      let Q := ⌊(X:ℝ)^θ⌋₊
      ∃ D ⊆ Icc 1 Q,(D.card:ℝ) ≤ K*Q/(log X)^A ∧
      ∀ q∈Icc 1 Q,q∉D → ∀ a : (ZMod q)ˣ,
        (X.primeCounting:ℝ)/(2*q.totient) ≤ slopeCount k X q a := by
  simpa only [selected_slope] using from_sparse H hθ hA (ThetaWorstPrimeClasses.slope k)

#print axioms from_sparse
#print axioms slope
end
end Arxiv.«2501.03234».ThetaPrimeClassCoverage
