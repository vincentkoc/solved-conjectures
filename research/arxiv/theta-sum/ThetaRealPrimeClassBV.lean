import ThetaPrimeClassBV

/-! Transfer with all real endpoints x ≥ 3 and the original source quantifiers. -/
namespace Arxiv.«2501.03234».ThetaRealPrimeClassBV
open Finset Filter Real ThetaPrimeClassBV ThetaWorstPrimeClasses ThetaOccupancyScales
noncomputable section

def Statement (F : ℝ → (q : ℕ) → ZMod q → ℕ) : Prop := ∀ θ < (1/2:ℝ),∀ A ≥ (1:ℝ),
  ∃ C > (0:ℝ),∀ x ≥ (3:ℝ),∑ q∈Icc 1 ⌊x^θ⌋₊,error F x q ≤ C*x/(log x)^A

private theorem floor_errors {x : ℝ} (hx : 0≤x) (P : ℕ → Prop) (q : ℕ) :
    error ordinaryCount x q=error ordinaryCount ⌊x⌋₊ q ∧
    error (selectedCount P) x q=error (selectedCount P) ⌊x⌋₊ q := by
  have h (p : ℕ) : ((p:ℝ)≤x) ↔ (p:ℝ)≤(⌊x⌋₊:ℕ) := by rw [Nat.cast_le];exact (Nat.le_floor_iff hx).symm
  have h₁ (a : ZMod q) : ordinaryCount x q a=ordinaryCount ⌊x⌋₊ q a := by
    unfold ordinaryCount;congr 1;ext p;simp only [Set.mem_ofPred_eq,h p]
  have h₂ (a : ZMod q) : selectedCount P x q a=selectedCount P ⌊x⌋₊ q a := by
    unfold selectedCount;congr 1;ext p;simp only [Set.mem_ofPred_eq,h p]
  constructor <;> unfold error <;> apply iSup_congr <;> intro a <;> simp only [h₁,h₂,Nat.floor_natCast]

private theorem bound {x : ℝ} (hx : 0≤x) (P : ℕ → Prop) (Q : ℕ) :
    ∑ q∈Icc 1 Q,error (selectedCount P) x q ≤
      (∑ q∈Icc 1 Q,error ordinaryCount x q)+total (ThetaPrimeDensity.primeSet P ⌊x⌋₊) Q := by
  rw [total,←sum_add_distrib]
  apply sum_le_sum;intro q hq
  rw [(floor_errors hx P q).1,(floor_errors hx P q).2]
  exact one_selected P ⌊x⌋₊ q (mem_Icc.mp hq).1

private theorem trivial (P : ℕ → Prop) (N Q : ℕ) :
    total (ThetaPrimeDensity.primeSet P N) Q ≤ (Q:ℝ)*N := by
  classical
  let E := ThetaPrimeDensity.primeSet P N
  have hsub : E⊆Icc 1 N := fun p hp =>
    let h := Nat.mem_primesLE.mp (mem_filter.mp hp).1
    mem_Icc.mpr ⟨h.2.pos,h.1⟩
  have hcard : E.card≤N := by simpa using card_le_card hsub
  have h (q : ℕ) : worst E q≤N := Finset.sup_le (fun a _ => (card_filter_le E _).trans hcard)
  apply (sum_le_sum (s:=Icc 1 Q) (fun q _ => Nat.cast_le (α:=ℝ).mpr (h q))).trans
  simp

/-- This uses the same real endpoints, unit supremum and inclusive modulus
floor as the ordinary source. Only the numerator of the prime count changes. -/
theorem transfer (H : Ordinary) {P : ℕ → Prop} (hP : Sparse P) : Statement (selectedCount P) := by
  intro θ hθ A hA
  obtain ⟨C,hC,hC'⟩ := H θ hθ A hA
  have ha : 0<A := by linarith
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp ((hP.and
    (ThetaPositivePrimeLevel.absorption ha)).and ThetaOccupancyScales.bounds)
  let B := (N₀:ℝ)+3
  let D := B^2*(log B)^A+2^A
  have hb : 1<B := by dsimp [B];linarith only [Nat.cast_nonneg (α:=ℝ) N₀]
  have hd : 0<D := by dsimp [D];positivity [log_pos hb]
  refine ⟨C+D,by positivity,?_⟩
  intro x hx
  let N := ⌊x⌋₊
  let Q := ⌊x^θ⌋₊
  let E := ThetaPrimeDensity.primeSet P N
  have hp : 0<x := by linarith
  have hxp : 0<log x := log_pos (by linarith)
  have hpow := Nat.floor_le (rpow_nonneg hp.le θ)
  have hqx : (Q:ℝ)^2≤x := by
    have hh := pow_le_pow_left₀ (Nat.cast_nonneg (α:=ℝ) Q) hpow 2
    rw [←rpow_mul_natCast hp.le] at hh
    exact (hh.trans (rpow_le_rpow_of_exponent_le (by linarith : 1≤x)
      (show θ*(2:ℕ)≤(1:ℝ) by norm_num;linarith))).trans_eq (rpow_one _)
  have hN : (N:ℝ)≤x := Nat.floor_le hp.le
  have hNhi : x<(N:ℝ)+1 := Nat.lt_floor_add_one x
  have hN3 : 3≤N := (Nat.le_floor_iff hp.le).mpr (by simpa using hx)
  have hN' : (3:ℝ)≤N := by exact_mod_cast hN3
  have hpos : 0<log (N:ℝ) := log_pos (by linarith)
  have hE : total E Q ≤ D*x/(log x)^A := by
    by_cases hlarge : N₀≤N
    · obtain ⟨⟨he,hs⟩,hr⟩ := hN₀ N hlarge
      have hfit : (Q:ℝ)^2≤N*exp (saving N) := by
        have h₂ := (add_one_le_exp (saving N))
        have hmul := mul_le_mul_of_nonneg_left (show (2:ℝ)≤exp (saving N) by linarith only [h₂,hr.2.2.1]) (Nat.cast_nonneg (α:=ℝ) N)
        linarith only [hqx,hNhi,hN',hmul]
      have hlow := (he Q hfit).trans hs
      have hlog : log x≤2*log (N:ℝ) := by
        have hxx : x≤(N:ℝ)^2 := by nlinarith only [hNhi,hN',mul_nonneg (show 0≤(N:ℝ)-3 by linarith) (Nat.cast_nonneg (α:=ℝ) N)]
        have h := log_le_log hp hxx;simpa only [log_pow,Nat.cast_ofNat] using h
      have hA' := rpow_le_rpow hxp.le hlog ha.le
      rw [mul_rpow (by norm_num : (0:ℝ)≤2) hpos.le] at hA'
      apply hlow.trans
      rw [div_le_div_iff₀ (rpow_pos_of_pos hpos A) (rpow_pos_of_pos hxp A)]
      have hD : (2:ℝ)^A≤D := by dsimp [D];exact le_add_of_nonneg_left (by positivity [log_pos hb])
      calc _ ≤ x*((2:ℝ)^A*(log (N:ℝ))^A) := mul_le_mul hN hA' (rpow_nonneg hxp.le _) hp.le
           _ ≤ (D*x)*(log (N:ℝ))^A := by
             rw [←mul_assoc,mul_comm x];exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hD hp.le) (rpow_nonneg hpos.le _)
    · have hxb : x≤B := by
        have hn : (N:ℝ)≤N₀ := Nat.cast_le.mpr (le_of_not_ge hlarge)
        dsimp [B];linarith only [hNhi,hn]
      have hQb : (Q:ℝ) ≤ B := by
        have hh : x≤B^2 := hxb.trans (le_self_pow₀ hb.le (by decide : (2:ℕ)≠0))
        exact le_of_pow_le_pow_left₀ (by decide : (2:ℕ)≠0) (by linarith) (hqx.trans hh)
      have he := (trivial P N Q).trans (mul_le_mul hQb (hN.trans hxb)
        (Nat.cast_nonneg _) (by linarith))
      apply he.trans
      rw [le_div_iff₀ (rpow_pos_of_pos hxp A)]
      have hh := rpow_le_rpow hxp.le (log_le_log hp hxb) ha.le
      have hD : B^2*(log B)^A ≤ D := by dsimp [D];linarith only [rpow_pos_of_pos (by norm_num : (0:ℝ)<2) A]
      calc _ ≤ B*B*(log B)^A := mul_le_mul_of_nonneg_left hh (by positivity)
           _ ≤ D := by simpa only [sq] using hD
           _ ≤ _ := le_mul_of_one_le_right hd.le (by linarith)
  apply (bound hp.le P Q).trans
  calc _ ≤ C*x/(log x)^A+D*x/(log x)^A := add_le_add (hC' x hx) hE
       _ = _ := by ring

theorem slope (H : Ordinary) (k : ℕ) : Statement (slopeCount k) := by
  simpa only [selected_slope] using transfer H (ThetaWorstPrimeClasses.slope k)

theorem centered (H : Ordinary) : ∃ A : ℝ,0<A ∧ Statement (selectedCount
    (fun p : ℕ => A*(1+log (log p))^2≤|(S p:ℝ)/p-log p/2|)) := by
  obtain ⟨A,hA,h⟩ := ThetaWorstPrimeClasses.centered
  exact ⟨A,hA,transfer H h⟩

#print axioms transfer
#print axioms centered
#print axioms slope
end
end Arxiv.«2501.03234».ThetaRealPrimeClassBV
