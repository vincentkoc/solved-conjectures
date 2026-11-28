import ThetaConductorMoment

/-! A lower bound for the first moment at one over the odd Dirichlet characters. -/
namespace Arxiv.«2501.03234».ThetaOddCharacterMean
open Finset Complex DirichletCharacter
noncomputable section
variable {q : ℕ} [NeZero q]

def oddChars (q : ℕ) : Finset (DirichletCharacter ℂ q) := by classical exact univ.filter (·.Odd)

omit [NeZero q] in
theorem mem_odd (χ : DirichletCharacter ℂ q) : χ∈oddChars q ↔ χ.Odd := by classical simp [oddChars]

omit [NeZero q] in
theorem ne_one {χ : DirichletCharacter ℂ q} (h : χ.Odd) : χ≠1 := by
  intro he
  have h₁ : (1:DirichletCharacter ℂ q).Even := MulChar.one_apply (isUnit_one.neg)
  subst χ
  exact DirichletCharacter.Odd.not_even _ h h₁

private theorem kernel (x : ZMod q) :
    2*(∑ χ∈oddChars q,χ x) =
      (if x=1 then (q.totient:ℂ) else 0)-(if x=(-1) then (q.totient:ℂ) else 0) := by
  classical
  have he (χ : DirichletCharacter ℂ q) : 2*(if χ.Odd then χ x else 0)=χ x-χ (-x) := by
    rcases χ.even_or_odd with h|h
    · rw [if_neg h.not_odd,h.eval_neg]; ring
    · rw [if_pos h,h.eval_neg]; ring
  simp only [oddChars,sum_filter,mul_sum,he,sum_sub_distrib,sum_characters_eq]
  simp only [neg_eq_iff_eq_neg]

private def block (χ : DirichletCharacter ℂ q) (k : ℕ) : ℂ :=
  ∑ i∈range q,χ (i:ZMod q)/((q*k+i:ℕ):ℂ)

private theorem block_sum (hq : 5≤q) (k : ℕ) :
    2*(∑ χ∈oddChars q,block χ k).re =
    q.totient*(1/((q*k:ℕ)+1:ℝ)-1/((q*k:ℕ)+(q-1:ℕ):ℝ)) := by
  classical
  have h1 : 1<q := by omega
  have hn (i : ℕ) (hi : i<q) : (i:ZMod q)=-1 ↔ i=q-1 := by
    have he : ((q-1:ℕ):ZMod q)=-1 := by rw [Nat.cast_sub (by omega),ZMod.natCast_self,Nat.cast_one]; simp
    rw [←he]
    constructor
    · intro h; simpa only [ZMod.val_natCast_of_lt hi,ZMod.val_natCast_of_lt (by omega : q-1<q)] using congrArg ZMod.val h
    · rintro rfl; rfl
  have hp (i : ℕ) (hi : i<q) : (i:ZMod q)=1 ↔ i=1 := by
    constructor
    · intro h; simpa only [ZMod.val_natCast_of_lt hi,ZMod.val_one'' (by omega : q≠1)] using congrArg ZMod.val h
    · rintro rfl; exact Nat.cast_one
  have hc : 2*(∑ χ∈oddChars q,block χ k) =
      (q.totient:ℂ)/((q*k:ℕ)+1:ℂ)-(q.totient:ℂ)/((q*k:ℕ)+(q-1:ℕ):ℂ) := by
    unfold block
    rw [sum_comm,mul_sum]
    have hterm (i : ℕ) (hi : i∈range q) : 2*∑ χ∈oddChars q,χ (i:ZMod q)/((q*k+i:ℕ):ℂ) =
        (if i=1 then (q.totient:ℂ)/((q*k+i:ℕ):ℂ) else 0) -
        (if i=q-1 then (q.totient:ℂ)/((q*k+i:ℕ):ℂ) else 0) := by
      rw [←sum_div,←mul_div_assoc,kernel]
      simp only [hp _ (mem_range.mp hi),hn _ (mem_range.mp hi),sub_div]
      simp only [ite_div,zero_div]
    rw [sum_congr rfl hterm,sum_sub_distrib,sum_ite_eq',sum_ite_eq',if_pos (mem_range.mpr h1),
      if_pos (mem_range.mpr (by omega : q-1<q))]
    push_cast; ring
  have h := congrArg Complex.re hc
  push_cast at h
  simp only [mul_re,re_ofNat,im_ofNat,zero_mul,sub_zero,sub_re,←ofReal_natCast,←ofReal_one,
    ←ofReal_add,←ofReal_mul,←ofReal_div,ofReal_re] at h
  push_cast
  linear_combination h

private theorem block_nonneg (hq : 5≤q) (k : ℕ) : 0≤(∑ χ∈oddChars q,block χ k).re := by
  have h := block_sum hq k
  have hle : 1/((q*k:ℕ)+(q-1:ℕ):ℝ) ≤ 1/((q*k:ℕ)+1:ℝ) :=
    one_div_le_one_div_of_le (by positivity) (by gcongr; exact_mod_cast (show 1≤q-1 by omega))
  linarith [mul_nonneg (Nat.cast_nonneg q.totient) (sub_nonneg.mpr hle)]

omit [NeZero q] in
private theorem full_blocks (χ : DirichletCharacter ℂ q) (K : ℕ) :
    ∑ i∈range (q*K),χ (i:ZMod q)/(i:ℂ)=∑ k∈range K,block χ k := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Nat.mul_succ,sum_range_add,ih,sum_range_succ]
    simp only [block,Nat.cast_add,Nat.cast_mul,ZMod.natCast_self,zero_mul,zero_add]

/-- The real sum over odd characters is at least a quarter of the full character count. -/
theorem lower (hq : 5≤q) : (q.totient:ℝ)/4 ≤ ∑ χ∈oddChars q,(LFunction χ 1).re := by
  have hfirst := block_sum hq 0
  simp only [Nat.mul_zero,Nat.cast_zero,zero_add,div_one] at hfirst
  have hq1 : (4:ℝ)≤(q-1:ℕ) := by exact_mod_cast (show 4≤q-1 by omega)
  have hi := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<4) hq1
  have hf : (q.totient:ℝ)*(3/8) ≤ (∑ χ∈oddChars q,block χ 0).re := by
    nlinarith only [hfirst,mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg q.totient)]
  have hsum := single_le_sum (f:=fun k => (∑ χ∈oddChars q,block χ k).re)
    (fun k _ => block_nonneg hq k) (by decide : 0∈range 8)
  have hχ (χ) (hχ : χ∈oddChars q) :
      (∑ k∈range 8,block χ k).re-(LFunction χ 1).re≤1/8 := by
    have h := ThetaCharacterHarmonicLimit.harmonic_error χ (ne_one ((mem_odd χ).mp hχ))
      (show 0<q*8 by have := NeZero.pos q; omega)
    rw [full_blocks,norm_sub_rev] at h
    have he : (q:ℝ)/(q*8:ℕ)=1/8 := by push_cast; field_simp [show (q:ℝ)≠0 by exact_mod_cast NeZero.ne q]
    exact (re_le_norm _).trans (h.trans_eq he)
  have H := sum_le_sum hχ
  simp only [sum_sub_distrib,sum_const,nsmul_eq_mul,re_sum] at H hsum hf
  rw [sum_comm (f:=fun χ k => (block χ k).re)] at H
  have hc : ((oddChars q).card:ℝ)≤q.totient := by
    have h := card_le_univ (oddChars q)
    rw [←Nat.card_eq_fintype_card,card_eq_totient_of_hasEnoughRootsOfUnity ℂ q] at h
    exact_mod_cast h
  linarith

#print axioms lower
end
end Arxiv.«2501.03234».ThetaOddCharacterMean
