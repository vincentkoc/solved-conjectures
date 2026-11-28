import HosoyaIndexGcdTail
import LucasFibonacciPrimePowerLifts

/-! Finite prime weights for the index and upper Hosoya value below 4096. -/

namespace Arxiv.«2211.10788».IndexDivisors
open Finset

def excludedBases : List ℕ := [5,11,13,17,29,41,47,61]

private lemma avoids_step (p R : ℕ) (hr : 0 < R) (hf : p ∣ Nat.fastFib (p*R))
    (hs : (List.range R).all (fun i => decide (¬p ∣ 2*Nat.fastFib (p*i)+Nat.fastFib (p*i+2)))=true)
    (t : ℕ) : ¬p ∣ lucasFibonacciSum (p*t) := by
  let f (j : ℕ) := p ∣ lucasFibonacciSum (p*j)
  have per : Function.Periodic f R := by
    intro j
    apply propext
    change p ∣ lucasFibonacciSum (p*(j+R)) ↔ _
    rw [Nat.mul_add]
    exact lucasFibonacciSum_dvd_shift_iff (by simpa [Nat.fastFib_eq] using hf)
  change ¬f t
  rw [← per.map_mod_nat t]
  have h := List.all_eq_true.mp hs (t%R) (List.mem_range.mpr (Nat.mod_lt _ hr))
  simpa [f,lucasFibonacciSum,Nat.fastFib_eq] using h

theorem no_common_excluded {p n : ℕ} (hp : p∈excludedBases) (hn : p ∣ n) :
    ¬p ∣ lucasFibonacciSum n := by
  obtain ⟨t,rfl⟩ := hn
  simp only [excludedBases,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact avoids_step 5 1 (by decide) (by decide +kernel) (by decide +kernel) t
  · exact avoids_step 11 10 (by decide) (by decide +kernel) (by decide +kernel) t
  · exact avoids_step 13 7 (by decide) (by decide +kernel) (by decide +kernel) t
  · exact avoids_step 17 9 (by decide) (by decide +kernel) (by decide +kernel) t
  · exact avoids_step 29 14 (by decide) (by decide +kernel) (by decide +kernel) t
  · exact avoids_step 41 20 (by decide) (by decide +kernel) (by decide +kernel) t
  · exact avoids_step 47 16 (by decide) (by decide +kernel) (by decide +kernel) t
  · exact avoids_step 61 15 (by decide) (by decide +kernel) (by decide +kernel) t

def limitedRank (p : ℕ) : ℕ → ℕ
  | 0 => 1
  | j+1 =>
    let r := limitedRank p j
    if r=j+1 ∧ ¬p ∣ Nat.fastFib (j+1) then j+2 else r

lemma limitedRank_bounds {p : ℕ} (hp : p.Prime) (j : ℕ) :
    0 < limitedRank p j ∧ limitedRank p j ≤ returnRank p := by
  obtain ⟨pos,dvd⟩ := returnRank_spec hp
  induction j with
  | zero => exact ⟨by change 0 < 1; decide,pos⟩
  | succ j ih =>
    rw [limitedRank]
    split_ifs with cond
    · refine ⟨by omega,?_⟩
      have miss : returnRank p≠j+1 := by
        intro eq
        exact cond.2 (by simpa [Nat.fastFib_eq,eq] using dvd)
      omega
    · exact ih

private def trialDivisors : List ℕ :=
  [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61]

private def passesTrial (p : ℕ) : Bool :=
  decide (2≤p) && trialDivisors.all fun q => p==q || p%q != 0

private lemma prime_passes {p : ℕ} (hp : p.Prime) : passesTrial p=true := by
  have pos : trialDivisors.all (fun q => decide (2≤q))=true := by decide
  simp only [passesTrial,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,
    Bool.or_eq_true,beq_iff_eq,bne_iff_ne]
  refine ⟨hp.two_le,?_⟩
  intro q hq
  by_cases eq : p=q
  · exact Or.inl eq
  · right
    intro zero
    have := (hp.eq_one_or_self_of_dvd q (Nat.dvd_of_mod_eq_zero zero)).resolve_right (Ne.symm eq)
    have := of_decide_eq_true (List.all_eq_true.mp pos q hq)
    omega

/-- Upward-rounded millionths for each prime outside the eight empty classes. -/
def smallScore (p : ℕ) : ℕ :=
  if passesTrial p=true ∧ p∉excludedBases then (1000000+p*limitedRank p 32-1)/(p*limitedRank p 32) else 0

theorem weight_le_smallScore {p : ℕ} (hp : p.Prime) (active : p∉excludedBases) :
    rankWeight p ≤ (smallScore p:ℝ)/1000000 := by
  obtain ⟨pos,le⟩ := limitedRank_bounds hp 32
  have bd : 1000000 ≤ (p*limitedRank p 32)*smallScore p := by
    rw [smallScore,if_pos ⟨prime_passes hp,active⟩,←Nat.ceilDiv_eq_add_pred_div]
    exact (ceilDiv_le_iff_le_mul (Nat.mul_pos hp.pos pos)).mp le_rfl
  have b := bd.trans (Nat.mul_le_mul_right (smallScore p) (Nat.mul_le_mul_left p le))
  have h : (1000000:ℝ) ≤ (p:ℝ)*returnRank p*smallScore p := by exact_mod_cast b
  unfold rankWeight
  have pp : (0:ℝ)<p := by exact_mod_cast hp.pos
  have rp : (0:ℝ)<returnRank p := by exact_mod_cast (returnRank_spec hp).1
  apply (div_le_div_iff₀ (mul_pos pp rp) (by norm_num)).mpr
  simpa only [one_mul,mul_comm (smallScore p:ℝ) _] using h

private def subtotal (a : ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => subtotal a n+smallScore (a+n)

private lemma subtotal_spec (a n : ℕ) : subtotal a n=∑ p ∈ range n, smallScore (a+p) := by
  induction n with
  | zero => simp [subtotal]
  | succ n ih => rw [subtotal,ih,sum_range_succ]

private lemma join_subtotals (a b c u v : ℕ) (h₁ : subtotal a b=u) (h₂ : subtotal (a+b) c=v) :
    subtotal a (b+c)=u+v := by
  subst u v
  induction c with
  | zero => simp [subtotal]
  | succ c ih =>
    change subtotal a (b+c)+smallScore (a+(b+c))=
      subtotal a b+(subtotal (a+b) c+smallScore ((a+b)+c))
    rw [ih,Nat.add_assoc,Nat.add_assoc a b c]

open Lean Meta in
/-- Each leaf reduces 32 candidate scores in the kernel. All internal nodes
apply the subtotal identity; numerical sums supplied by the generator are checked. -/
private partial def weightCertificate (a n : ℕ) : MetaM (ℕ × Expr) := do
  let term := mkApp2 (mkConst ``subtotal) (toExpr a) (toExpr n)
  if n≤32 then
    let v := subtotal a n
    let val := toExpr v
    let h ← mkAuxTheorem (←mkEq term val) (←mkEqRefl val) (kind? := `_rankWeightBlock)
    return (v,h)
  let b := n/2
  let c := n-b
  let (u,left) ← weightCertificate a b
  let (v,right) ← weightCertificate (a+b) c
  let h := mkAppN (mkConst ``join_subtotals) #[toExpr a,toExpr b,toExpr c,toExpr u,toExpr v,left,right]
  return (u+v,h)

open Lean Elab Tactic in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem small_scores_total : (∑ p ∈ range 4096, smallScore p)=298854 := by
  have result : subtotal 0 4096=298854 := by
    run_tac liftMetaTactic fun g => do
      let (_,proof) ← weightCertificate 0 4096
      g.assign proof
      return []
  simpa only [subtotal_spec,Nat.zero_add] using result

#print axioms no_common_excluded
#print axioms weight_le_smallScore
#print axioms small_scores_total

end Arxiv.«2211.10788».IndexDivisors
