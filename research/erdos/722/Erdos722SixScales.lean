import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# Nearby products of 31 and 40

Normalize powers of 40 by their leading base-31 power, then partition
the resulting interval into bins of width `1/L`. Equal bins give two
distinct products whose ratio is at most `(L+1)/L`.
-/

namespace Erdos722.Six
def Scale (n : ℕ) := ∃ i j : ℕ, n=31^i*40^j

theorem scale_mul {a b : ℕ} (ha : Scale a) (hb : Scale b) : Scale (a*b) := by
  obtain ⟨i,j,rfl⟩ := ha
  obtain ⟨k,l,rfl⟩ := hb
  exact ⟨i+k,j+l,by rw [pow_add,pow_add]; ring⟩

private def lead (n : ℕ) := 31 ^ Nat.log 31 n

private theorem lead_pos (n : ℕ) : 0 < lead n := by unfold lead; positivity

private theorem lead_le {n : ℕ} (hn : n ≠ 0) : lead n ≤ n := Nat.pow_log_le_self _ hn

private theorem bin_lt {L n : ℕ} (hL : 0<L) : L*n/lead n < 31*L := by
  apply (Nat.div_lt_iff_lt_mul (lead_pos _)).mpr
  have hn := Nat.lt_pow_succ_log_self (by decide : 1<31) n
  rw [pow_succ] at hn
  simpa only [lead,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using Nat.mul_lt_mul_of_pos_left hn hL

private theorem near {L x y : ℕ} (hx : x≠0) (he : L*y/lead y=L*x/lead x) :
    L*(y*lead x) ≤ (L+1)*(x*lead y) := by
  let b := L*x/lead x
  have hyb : L*y < (b+1)*lead y := by
    apply (Nat.div_lt_iff_lt_mul (lead_pos _)).mp
    change L*y/lead y < L*x/lead x+1
    omega
  have hxb : b*lead x ≤ L*x := Nat.div_mul_le_self ..
  have h₁ := Nat.mul_le_mul_right (lead x) hyb.le
  have h₂ := Nat.mul_le_mul_right (lead y) hxb
  have h₃ := Nat.mul_le_mul_right (lead y) (lead_le hx)
  nlinarith only [h₁,h₂,h₃]

private theorem distinct {i j : ℕ} (hne : i≠j) (a b : ℕ) : 40^i*31^a ≠ 40^j*31^b := by
  intro he
  have h := congrArg (fun n : ℕ => n.factorization 5) he
  have h₄₀ : (40 : ℕ).factorization 5 = 1 := by
    have iff' (k : ℕ) := (show Nat.Prime 5 by decide).pow_dvd_iff_le_factorization (k := k) (by decide : 40 ≠ 0)
    have lo := (iff' (k := 1)).mp (by decide)
    have hi := (iff' (k := 2)).not.mp (by decide)
    omega
  have h₃₁ : (31 : ℕ).factorization 5 = 0 := Nat.factorization_eq_zero_of_not_dvd (by decide)
  simp only [Nat.factorization_mul (by positivity : 40^_ ≠ 0) (by positivity : 31^_ ≠ 0),
    Nat.factorization_pow,Finsupp.add_apply,Finsupp.smul_apply,smul_eq_mul,h₄₀,h₃₁,
    Nat.mul_one,Nat.mul_zero,Nat.add_zero] at h
  exact hne h

theorem nearby_scales {L : ℕ} (hL : 0<L) :
    ∃ A B, Scale A ∧ Scale B ∧ 0<A ∧ A<B ∧ L*B≤(L+1)*A := by
  let f (i : Fin (31*L+1)) : Fin (31*L) := ⟨L*40^i.val/lead (40^i.val),bin_lt hL⟩
  obtain ⟨i,j,hij,hbin⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simp)
  let x := 40^i.val
  let y := 40^j.val
  have hx : 0<x := by dsimp [x]; positivity
  have hy : 0<y := by dsimp [y]; positivity
  have he : L*x/lead x=L*y/lead y := congrArg Fin.val hbin
  have hxy : x*lead y≠y*lead x := distinct (fun e => hij (Fin.ext e)) _ _
  have sA : Scale (x*lead y) := ⟨_,_,Nat.mul_comm ..⟩
  have sB : Scale (y*lead x) := ⟨_,_,Nat.mul_comm ..⟩
  rcases lt_or_gt_of_ne hxy with h | h
  · exact ⟨_,_,sA,sB,Nat.mul_pos hx (lead_pos _),h,near hx.ne' he.symm⟩
  · exact ⟨_,_,sB,sA,Nat.mul_pos hy (lead_pos _),h,near hy.ne' he⟩

#print axioms nearby_scales
end Erdos722.Six
