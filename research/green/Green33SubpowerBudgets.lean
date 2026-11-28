import Green33QuadraticRadix
import Green33MaximalOrders
import Mathlib.Analysis.SpecificLimits.Basic

/-! Size budgets for cyclic two-bases with a bound on ordered sum counts. -/

open Finset Filter Green33StrictReduction Green33Multiplicity Green33MaximalOrders
open scoped Pointwise Topology

namespace Green33SubpowerBudgets

/-- Bracket every sufficiently large budget by adjacent grid values, with indices
tending to infinity. The grid need only dominate the identity. -/
private lemma bracket (g : ℕ → ℕ) (big : ∀ n, n ≤ g n) :
    ∃ j : ℕ → ℕ, Tendsto j atTop atTop ∧
      ∀ᶠ K in atTop, g (j K) ≤ K ∧ K < g (j K+1) := by
  let j (K : ℕ) := Nat.findGreatest (fun n => g n≤K) K
  refine ⟨j,tendsto_atTop.mpr (fun n => ?_),?_⟩
  · filter_upwards [eventually_ge_atTop (g n)] with K hK
    exact Nat.le_findGreatest ((big n).trans hK) hK
  · filter_upwards [eventually_ge_atTop (g 0)] with K hK
    refine ⟨Nat.findGreatest_spec (P := fun n => g n≤K) (Nat.zero_le K) hK,?_⟩
    by_contra! h
    have h' : j K+1≤j K := Nat.le_findGreatest ((big _).trans h) h
    omega

/-- For every size budget large enough, a fixed strict seed retains any
smaller normalized order density even under a prescribed multiplicity cap. -/
theorem seed_all_budgets {M : ℕ+} (A : Finset (ZMod M)) (hA : StrictCover A)
    (h : ℕ) {v : ℝ} (hv : v < (M:ℝ)/(A.card:ℝ)^2) :
    ∀ᶠ K : ℕ in atTop, ∃ N : ℕ+, ∃ B : Finset (ZMod N), StrictCover B ∧
      B.card ≤ K ∧ v < (N:ℝ)/(K:ℝ)^2 ∧ (maxReps B)^h ≤ N.val := by
  let k := A.card
  let s := k.factorial
  let d := h+1
  let q (n : ℕ) := s*n+1
  let g (n : ℕ) := k*(q n+s)^d
  let C := 2*k^2*(32*(4*k+7))^d
  have hk : 0<k := by
    obtain ⟨a,ha,_,_,_,_⟩ := hA 0
    exact card_pos.mpr ⟨a,ha⟩
  have hs : 0<s := Nat.factorial_pos _
  have hq (n) : n≤q n := (Nat.le_mul_of_pos_left n hs).trans (Nat.le_succ _)
  have hg (n) : n≤g n := (hq n).trans ((Nat.le_add_right _ _).trans
    ((Nat.le_self_pow (by dsimp [d]; omega) _).trans (Nat.le_mul_of_pos_left _ hk)))
  obtain ⟨j,hj,br⟩ := bracket g hg
  have qt : Tendsto q atTop atTop :=
    tendsto_atTop.mpr (fun n => (eventually_ge_atTop n).mono fun a ha => ha.trans (hq a))
  have lim : Tendsto (fun n : ℕ => (M:ℝ)/(k:ℝ)^2*
      ((q n:ℝ)/((q n:ℝ)+2*(s:ℝ)))^(2*d)) atTop (𝓝 ((M:ℝ)/(k:ℝ)^2)) := by
    simpa using (((tendsto_natCast_div_add_atTop (2*(s:ℝ))).comp qt).pow (2*d)).const_mul ((M:ℝ)/(k:ℝ)^2)
  filter_upwards [br,(lim.comp hj).eventually_const_lt hv,
    (qt.comp hj).eventually_ge_atTop (6+s+C^h),eventually_gt_atTop 0] with K bounds near large hK
  let n := j K
  let Q := q n
  have size : 6+s+C^h≤Q := large
  have hp : 0<Q := by omega
  let N : ℕ+ := ⟨M.val*(Q^2)^d,Nat.mul_pos M.pos (pow_pos (pow_pos hp _) _)⟩
  obtain ⟨B,hB,cB,peak⟩ := Green33QuadraticRadix.finite_lift_all_radices A hA Q n d
    (by omega) (by change s<Q; omega) rfl
  refine ⟨N,B,hB,cB.trans bounds.1,?_,?_⟩
  · change v < (M:ℝ)/(k:ℝ)^2*((Q:ℝ)/((Q:ℝ)+2*(s:ℝ)))^(2*d) at near
    apply near.trans_le
    have nxt : q (n+1)+s=Q+2*s := by dsimp [q,Q]; ring
    have hK' : K ≤ k*(Q+2*s)^d := by
      rw [←nxt]
      exact bounds.2.le
    have den : 0 < (K:ℝ)^2 := by positivity
    have bigden : (K:ℝ)^2 ≤ ((k:ℝ)*((Q:ℝ)+2*(s:ℝ))^d)^2 := by
      apply pow_le_pow_left₀ (Nat.cast_nonneg _) _ 2
      exact_mod_cast hK'
    have hk' : 0<(k:ℝ) := by exact_mod_cast hk
    have hQ : 0<(Q:ℝ) := by exact_mod_cast hp
    have nz : (Q:ℝ)+2*(s:ℝ) ≠ 0 := by positivity
    have eq : (M:ℝ)/(k:ℝ)^2*((Q:ℝ)/((Q:ℝ)+2*(s:ℝ)))^(2*d) =
        (N:ℝ)/((k:ℝ)*((Q:ℝ)+2*(s:ℝ))^d)^2 := by
      change _ = ((M.val*(Q^2)^d:ℕ):ℝ)/_
      push_cast
      rw [div_pow, pow_mul (Q:ℝ) 2 d, Nat.mul_comm 2 d, pow_mul, mul_pow]
      field_simp
    rw [eq]
    exact div_le_div_of_nonneg_left (by positivity) den bigden
  · have small : maxReps B ≤ C*Q := peak.trans (by
      change k^2*(32*(4*k+7))^d*(Q+s) ≤ C*Q
      dsimp only [C]
      calc
        _ ≤ k^2*(32*(4*k+7))^d*(2*Q) := Nat.mul_le_mul_left _ (by omega)
        _ = _ := by ring)
    calc
      _ ≤ (C*Q)^h := Nat.pow_le_pow_left small h
      _ = C^h*Q^h := Nat.mul_pow ..
      _ ≤ Q*Q^h := Nat.mul_le_mul_right _ (by omega)
      _ = Q^d := by simp [d,pow_succ,mul_comm]
      _ ≤ (Q^2)^d := Nat.pow_le_pow_left (Nat.le_self_pow (by decide) _) _
      _ ≤ N.val := Nat.le_mul_of_pos_left _ M.pos


private lemma strictDensities_nonempty : strictDensities.Nonempty := by
  let M : ℕ+ := 3
  let A : Finset (ZMod M) := univ
  refine ⟨_,M,A,?_,rfl⟩
  change ∀ z : ZMod 3, ∃ a ∈ (univ : Finset (ZMod 3)), ∃ b ∈ (univ : Finset (ZMod 3)),
    a ≠ b ∧ a+b=z
  decide +kernel

/-- One strict family, indexed by every size budget, reaches the unrestricted
Graham–Sloane limit and simultaneously satisfies every fixed power cap. -/
theorem all_budget_family :
    ∃ (N : ℕ → ℕ+) (B : (K : ℕ) → Finset (ZMod (N K))),
      (∀ᶠ K : ℕ in atTop, StrictCover (B K) ∧ (B K).card ≤ K) ∧
      Tendsto (fun K => (N K:ℝ)/(K:ℝ)^2) atTop (𝓝 orderConstant) ∧
      ∀ h : ℕ, ∀ᶠ K : ℕ in atTop, (maxReps (B K))^h ≤ (N K).val := by
  classical
  let good (t K : ℕ) (N : ℕ+) (B : Finset (ZMod N)) : Prop :=
    StrictCover B ∧ B.card≤K ∧ orderConstant-1/((t:ℝ)+1)<(N:ℝ)/(K:ℝ)^2 ∧ (maxReps B)^t≤N.val
  have eventual (t : ℕ) : ∀ᶠ K : ℕ in atTop, ∃ N B, good t K N B := by
    have ht : orderConstant-1/((t:ℝ)+1)<orderConstant := sub_lt_self _ (by positivity)
    obtain ⟨_,⟨M,A,hA,rfl⟩,hv⟩ := exists_lt_of_lt_csSup strictDensities_nonempty ht
    exact seed_all_budgets A hA t hv
  choose threshold ht using fun t => eventually_atTop.mp (eventual t)
  obtain ⟨j,hj,br⟩ := bracket (fun t => max t (threshold t)) (fun _ => le_max_left ..)
  have ex : ∀ᶠ K : ℕ in atTop, ∃ N B, good (j K) K N B :=
    br.mono fun K b => ht _ K ((le_max_right ..).trans b.1)
  have select (K : ℕ) : ∃ N B, (∃ N B, good (j K) K N B) → good (j K) K N B := by
    by_cases yes : ∃ N B, good (j K) K N B
    · obtain ⟨N,B,h⟩ := yes
      exact ⟨N,B,fun _ => h⟩
    · exact ⟨1,∅,fun h => (yes h).elim⟩
  choose N B spec using select
  have goodK := ex.mono (fun K e => spec K e)
  refine ⟨N,B,goodK.mono (fun K e => ⟨e.1,e.2.1⟩),?_,?_⟩
  · have small : Tendsto (fun K => 1/((j K:ℝ)+1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hj
    have lower : Tendsto (fun K => orderConstant-1/((j K:ℝ)+1)) atTop (𝓝 orderConstant) := by
      simpa using (tendsto_const_nhds (x := orderConstant)).sub small
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' lower (budget_limits true)
    · exact goodK.mono (fun _ e => e.2.2.1.le)
    · filter_upwards [goodK] with K e
      exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (le_maxOrder e.2.1 (covers_true_iff.mpr e.1))) (sq_nonneg _)
  · intro h
    filter_upwards [goodK,hj.eventually_ge_atTop h] with K e ht'
    by_cases zero : maxReps (B K)=0
    · cases h with
      | zero => rw [pow_zero]; have := (N K).pos; omega
      | succ h => simp [zero]
    · exact (Nat.pow_le_pow_right (Nat.pos_of_ne_zero zero) ht').trans e.2.2.2


/-- Largest cyclic order at budget K with the specified cap on all ordered
sum fibers. The value is zero when no positive order qualifies. -/
noncomputable def cappedOrder (strict : Bool) (h K : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (fun n => n=0 ∨ ∃ N : ℕ+, N.val=n ∧
    ∃ B : Finset (ZMod N), B.card≤K ∧ Covers strict B ∧ (maxReps B)^h≤n) (maxOrder strict K)

/-- Imposing any fixed power cap leaves both all-budget maximal-order limits unchanged. -/
theorem capped_order_limit (strict : Bool) (h : ℕ) :
    Tendsto (fun K : ℕ => (cappedOrder strict h K:ℝ)/(K:ℝ)^2) atTop (𝓝 orderConstant) := by
  classical
  obtain ⟨N,B,good,lim,cap⟩ := all_budget_family
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' lim (budget_limits strict)
  · filter_upwards [good,cap h] with K e peak
    have cover : Covers strict (B K) := by
      intro x
      obtain ⟨a,ha,b,hb,ne,eq⟩ := e.1 x
      exact ⟨a,ha,b,hb,fun _ => ne,eq⟩
    have le : (N K).val ≤ cappedOrder strict h K :=
      Nat.le_findGreatest (le_maxOrder e.2 cover) (Or.inr ⟨N K,rfl,B K,e.2,cover,peak⟩)
    exact div_le_div_of_nonneg_right (Nat.cast_le.mpr le) (sq_nonneg _)
  · apply Eventually.of_forall
    intro K
    have le : cappedOrder strict h K ≤ maxOrder strict K := Nat.findGreatest_le _
    exact div_le_div_of_nonneg_right (Nat.cast_le.mpr le) (sq_nonneg _)

#print axioms capped_order_limit

#print axioms all_budget_family

#print axioms seed_all_budgets

end Green33SubpowerBudgets
