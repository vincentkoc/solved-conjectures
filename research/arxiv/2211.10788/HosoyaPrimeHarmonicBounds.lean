import Mathlib

/-! Comparing reciprocal prime sums with counts and with the logarithm of the harmonic sum. -/

namespace Arxiv.«2211.10788».DivisorWindows
open Finset

/-- The Euler product over primes at most N dominates the ordinary harmonic sum up to N. -/
private lemma harmonic_le_product (N : ℕ) :
    (harmonic N : ℝ) ≤ ∏ p ∈ (N+1).primesBelow, (1-(p:ℝ)⁻¹)⁻¹ := by
  classical
  let f : ℕ →* ℝ := { toFun := fun n => (n:ℝ)⁻¹, map_one' := by simp, map_mul' := by intro x y; simp [mul_comm] }
  have small {p : ℕ} (hp : p.Prime) : ‖f p‖ < 1 := by
    change ‖(p:ℝ)⁻¹‖ < 1
    rw [Real.norm_of_nonneg (by positivity)]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  have hs := (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric small (N+1)).2
  let S := Icc 1 N
  let embed : S → (N+1).smoothNumbers := fun i => ⟨i.1,Nat.mem_smoothNumbers'.mpr <| by
    intro p _ hd
    have hi := mem_Icc.mp i.2
    exact (Nat.le_of_dvd hi.1 hd).trans_lt (by omega)⟩
  have inj : Function.Injective embed := by intro x y he; exact Subtype.ext (congrArg (fun i : (N+1).smoothNumbers => (i:ℕ)) he)
  have le := sum_le_hasSum (S.attach.image embed) (fun i _ => (show 0≤f i by dsimp [f]; positivity)) hs
  rw [sum_image (by exact inj.injOn)] at le
  change ∑ i ∈ S.attach, ((i.1:ℕ):ℝ)⁻¹ ≤ _ at le
  rw [sum_attach S (fun i : ℕ => (i:ℝ)⁻¹)] at le
  have hf (p : ℕ) : f p=(p:ℝ)⁻¹ := rfl
  simpa only [hf,harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,S] using le

private lemma gap_sum (N : ℕ) :
    (∑ j ∈ range N, ((1:ℝ)/(j+1)-1/(j+2))) = 1-1/(N+1) := by
  induction N with
  | zero => norm_num
  | succ N ih => rw [sum_range_succ,ih]; push_cast; ring

/-- An elementary one-sided Mertens estimate with p+1 in the denominator. -/
theorem log_log_le_prime_weight {N : ℕ} (hn : 1≤N) :
    Real.log (Real.log (N+1)) ≤ (∑ p ∈ (N+1).primesBelow, 1/((p:ℝ)+1))+2 := by
  classical
  let S := (N+1).primesBelow
  have hp {p} (h : p ∈ S) : 2≤p := (Nat.prime_of_mem_primesBelow h).two_le
  have nz {p} (h : p ∈ S) : 0<1-(p:ℝ)⁻¹ := by
    have : (1:ℝ)<p := by exact_mod_cast (hp h)
    exact sub_pos.mpr (inv_lt_one_of_one_lt₀ this)
  have bound := (log_add_one_le_harmonic N).trans (harmonic_le_product N)
  have logs := Real.log_le_log (Real.log_pos (by exact_mod_cast (by omega : 1<N+1))) bound
  rw [Real.log_prod (fun p h => (inv_ne_zero (nz h).ne'))] at logs
  have one {p : ℕ} (h : p∈S) :
      Real.log ((1-(p:ℝ)⁻¹)⁻¹) ≤ 1/((p:ℝ)+1) + (1/((p:ℝ)-1)-1/(p:ℝ)) * 2 := by
    have gt : (1:ℝ)<p := by exact_mod_cast (hp h)
    have le := Real.log_le_sub_one_of_pos (inv_pos.mpr (nz h))
    apply le.trans
    have hd : 0<(p:ℝ)-1 := sub_pos.mpr gt
    have hp0 : 0<(p:ℝ) := by linarith
    have hp1 : 0<(p:ℝ)+1 := by linarith
    have eq : (1-(p:ℝ)⁻¹)⁻¹-1=1/((p:ℝ)-1) := by
      field_simp [hd.ne',hp0.ne',(nz h).ne']; ring
    rw [eq]
    field_simp [hd,hp0,hp1]; nlinarith
  have residual : (∑ p ∈ S, (1/((p:ℝ)-1)-1/(p:ℝ))) ≤ 1 := by
    let G (p : ℕ) := if 2≤p then (1:ℝ)/((p:ℝ)-1)-1/p else 0
    have pos (p : ℕ) : 0≤G p := by
      dsimp [G]; split_ifs with h
      · have gt : 1<(p:ℝ) := by exact_mod_cast h
        exact sub_nonneg.mpr (one_div_le_one_div_of_le (by linarith) (by linarith))
      · rfl
    calc _ = ∑ p ∈ S, G p := sum_congr rfl fun p h => by simp [G,hp h]
         _ ≤ ∑ p ∈ range (N+2), G p := sum_le_sum_of_subset_of_nonneg
           (fun p h => mem_range.mpr ((Nat.lt_of_mem_primesBelow h).trans (by omega))) (fun p _ _ => pos p)
         _ = ∑ j ∈ range N, ((1:ℝ)/(j+1)-1/(j+2)) := by
           rw [show N+2=2+N by omega,sum_range_add]
           simp [G,sum_range_succ,show ∀ j : ℕ, 2≤2+j from fun _ => by omega]
           simp only [show ∀ x : ℝ, x+2-1=x+1 from fun x => by ring,add_comm (2:ℝ)]
         _ ≤ 1 := by rw [gap_sum]; exact sub_le_self _ (by positivity)
  have sumle := sum_le_sum (s:=S) (fun p h => one h)
  rw [sum_add_distrib,←sum_mul] at sumle
  change Real.log (Real.log (N+1)) ≤ _
  push_cast at logs
  linarith

#print axioms log_log_le_prime_weight

end Arxiv.«2211.10788».DivisorWindows
