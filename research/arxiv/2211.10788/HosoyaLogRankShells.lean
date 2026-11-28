import HosoyaReciprocalRankTail

/-! A logarithm-weighted summable bound for the largest-prime decomposition. -/

namespace Arxiv.«2211.10788».IndexDivisors
open Finset Real

noncomputable def rootWeight (p : ℕ) : ℝ := √(rankWeight p)*√((p:ℝ)⁻¹)
noncomputable def logRootWeight (p : ℕ) : ℝ := log p*rootWeight p

lemma rootWeight_eq {p : ℕ} (hp : p.Prime) :
    rootWeight p=√(returnRank p)*rankWeight p := by
  have h : 0<(p:ℝ) := by exact_mod_cast hp.pos
  have r : 0<(returnRank p:ℝ) := by exact_mod_cast (returnRank_spec hp).1
  have w : 0 ≤ rankWeight p := by unfold rankWeight; positivity
  apply (sq_eq_sq₀ (by unfold rootWeight; positivity) (by positivity)).mp
  rw [rootWeight,mul_pow,mul_pow,Real.sq_sqrt w,Real.sq_sqrt (by positivity),Real.sq_sqrt r.le]
  unfold rankWeight
  field_simp

private lemma root_shell_bound {K : ℕ} (hk : 64≤K) (S : Finset ℕ)
    (hs : ∀ p∈S, p.Prime ∧ K^2≤p ∧ p<4*K^2) :
    ∑ p ∈ S, rootWeight p ≤ 2/√(K:ℝ) := by
  have kp : 0 < (K:ℝ) := by exact_mod_cast (by omega : 0<K)
  have a := rank_shell_bound hk S hs
  have card : S.card≤3*K^2 := by
    have sub : S ⊆ Ico (K^2) (4*K^2) := fun p hp => mem_Ico.mpr (hs p hp).2
    have H := card_le_card sub
    rw [Nat.card_Ico] at H
    omega
  have b : ∑ p ∈ S, (p:ℝ)⁻¹ ≤ 3 := by
    calc _ ≤ ∑ _p ∈ S, ((K:ℝ)^2)⁻¹ := sum_le_sum fun p hp =>
              inv_anti₀ (by positivity) (by exact_mod_cast (hs p hp).2.1)
         _ = (S.card:ℝ)/(K:ℝ)^2 := by simp [div_eq_mul_inv]
         _ ≤ 3 := (div_le_iff₀ (by positivity)).mpr (by exact_mod_cast card)
  have cs := Real.sum_sqrt_mul_sqrt_le S (f:=rankWeight) (g:=fun p : ℕ => (p:ℝ)⁻¹)
    (fun p => by unfold rankWeight; positivity) (fun p => by positivity)
  apply cs.trans
  calc √(∑ p ∈ S, rankWeight p)*√(∑ p ∈ S, (p:ℝ)⁻¹)
      ≤ √(13/(12*(K:ℝ)))*√3 := by gcongr
    _ = √(13/(12*(K:ℝ))*3) := (Real.sqrt_mul (by positivity) _).symm
    _ ≤ √(4/(K:ℝ)) := by
      apply Real.sqrt_le_sqrt
      field_simp
      linarith
    _ = 2/√(K:ℝ) := by rw [Real.sqrt_div (by norm_num)]; norm_num

private lemma log_shell_bound {K : ℕ} (hk : 64≤K) (S : Finset ℕ)
    (hs : ∀ p∈S, p.Prime ∧ K^2≤p ∧ p<4*K^2) :
    ∑ p ∈ S, logRootWeight p ≤ 4*log (2*(K:ℝ))/√(K:ℝ) := by
  have kp : 0 < (K:ℝ) := by exact_mod_cast (by omega : 0<K)
  have lg : 0≤log (2*(K:ℝ)) := Real.log_nonneg (by linarith [show 64≤(K:ℝ) by exact_mod_cast hk])
  calc _ ≤ ∑ p ∈ S, (2*log (2*(K:ℝ)))*rootWeight p := by
            apply sum_le_sum
            intro p hp
            apply mul_le_mul_of_nonneg_right _ (by unfold rootWeight; positivity)
            have b : (p:ℝ)≤(2*(K:ℝ))^2 := by
              have v : (p:ℝ)<4*(K:ℝ)^2 := by exact_mod_cast (hs p hp).2.2
              nlinarith
            calc log (p:ℝ) ≤ log ((2*(K:ℝ))^2) := Real.log_le_log (by exact_mod_cast (hs p hp).1.pos) b
                 _ = _ := by rw [Real.log_pow]; norm_num
       _ ≤ 2*log (2*(K:ℝ))*(2/√(K:ℝ)) := by
         rw [←mul_sum]
         exact mul_le_mul_of_nonneg_left (root_shell_bound hk S hs) (by positivity)
       _ = _ := by ring

private lemma log_tail_levels (j K : ℕ) (hk : 64≤K) (S : Finset ℕ)
    (hS : ∀ p∈S, p.Prime ∧ K^2≤p ∧ p<(2^j*K)^2) :
    ∑ p ∈ S, logRootWeight p ≤ 16*(log (2*(K:ℝ))+4)/√(K:ℝ) := by
  induction j generalizing K S with
  | zero =>
    have emp : S=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro p hp
      obtain ⟨_,a,b⟩ := hS p hp
      exact (not_lt_of_ge a) (by simpa using b)
    simp [emp]
    have high : 64≤(K:ℝ) := by exact_mod_cast hk
    have lg : 0≤log (2*(K:ℝ)) := Real.log_nonneg (by linarith)
    positivity
  | succ j ih =>
    let A := S.filter fun p => p < (2*K)^2
    let B := S.filter fun p => ¬p < (2*K)^2
    have a := log_shell_bound hk A (by
      intro p hp
      obtain ⟨mem,hi⟩ := mem_filter.mp hp
      exact ⟨(hS p mem).1,(hS p mem).2.1,by nlinarith⟩)
    have b := ih (2*K) (by omega) B (by
      intro p hp
      obtain ⟨mem,lo⟩ := mem_filter.mp hp
      obtain ⟨pr,_,hi⟩ := hS p mem
      refine ⟨pr,by omega,?_⟩
      simpa only [pow_succ _ j, mul_assoc] using hi)
    have split : (∑ p ∈ A, logRootWeight p)+(∑ p ∈ B, logRootWeight p)=∑ p ∈ S, logRootWeight p :=
      sum_filter_add_sum_filter_not ..
    rw [←split]
    apply (add_le_add a b).trans
    push_cast
    have kp : 0 < (K:ℝ) := by exact_mod_cast (by omega : 0 < K)
    have one : 1 ≤ (K:ℝ) := by exact_mod_cast (by omega : 1≤K)
    have s2 : 0 < √(2:ℝ) := by positivity
    have sk : 0 < √(K:ℝ) := by positivity
    have lg : 0≤log (2*(K:ℝ)) := Real.log_nonneg (by linarith)
    have recip : 16/√(2:ℝ) ≤ 12 := by
      apply (div_le_iff₀ s2).mpr
      nlinarith [Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)]
    have doubled : log (2*(2*(K:ℝ)))=log 2+log (2*(K:ℝ)) :=
      Real.log_mul (by norm_num) (by positivity)
    rw [doubled,Real.sqrt_mul (by norm_num : (0:ℝ)≤2)]
    let L := log (2*(K:ℝ))
    change 4*L/√(K:ℝ)+16*(log 2+L+4)/(√2*√(K:ℝ)) ≤ 16*(L+4)/√(K:ℝ)
    rw [show 16*(log 2+L+4)/(√2*√(K:ℝ))=(16/√2)*(log 2+L+4)/√(K:ℝ) by ring]
    rw [←add_div]
    apply div_le_div_of_nonneg_right _ sk.le
    have cmp := mul_le_mul_of_nonneg_right recip (show 0≤log 2+L+4 by dsimp [L]; positivity)
    linarith [Real.log_le_sub_one_of_pos (show (0:ℝ)<2 by norm_num)]

/-- The reciprocal square-root rank weight remains summable after a logarithmic factor. -/
theorem log_root_rank_tail {K : ℕ} (hk : 64≤K) (S : Finset ℕ)
    (hS : ∀ p∈S, p.Prime ∧ K^2≤p) :
    ∑ p ∈ S, logRootWeight p ≤ 16*(log (2*(K:ℝ))+4)/√(K:ℝ) := by
  let j := S.sup id
  apply log_tail_levels j K hk S
  intro p hp
  have le : p ≤ j := Finset.le_sup (f:=id) hp
  have a := j.lt_two_pow_self
  have b : 2^j ≤ 2^j*K := Nat.le_mul_of_pos_right _ (by omega)
  have c : 2^j*K ≤ (2^j*K)^2 := by
    rw [pow_two]
    exact Nat.le_mul_of_pos_right _ (by positivity)
  exact ⟨(hS p hp).1,(hS p hp).2,lt_of_le_of_lt le (a.trans_le (b.trans c))⟩

#print axioms log_root_rank_tail
#print axioms rootWeight_eq
#print axioms log_shell_bound

end Arxiv.«2211.10788».IndexDivisors
