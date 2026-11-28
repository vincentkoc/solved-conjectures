import ThetaIntervalKernel

/-! The part of the smoothed interval kernel above a signed frequency cutoff. -/
namespace Arxiv.«2501.03234».ThetaShortFrequencies
open Finset ThetaFourier ThetaIntervalKernel
variable {p : ℕ} [NeZero p]

def near (T : ℕ) (t : ZMod p) : Prop := ∃ j : ℕ, j≤T ∧ (t=j ∨ t= - (j : ZMod p))

omit [NeZero p] in
lemma near_neg {T : ℕ} {t : ZMod p} : near T (-t) ↔ near T t := by
  constructor
  · rintro ⟨j,hj,h|h⟩
    · exact ⟨j,hj,Or.inr (neg_eq_iff_eq_neg.mp h)⟩
    · exact ⟨j,hj,Or.inl (neg_inj.mp h)⟩
  · rintro ⟨j,hj,h|h⟩
    · exact ⟨j,hj,Or.inr (congrArg Neg.neg h)⟩
    · exact ⟨j,hj,Or.inl (neg_eq_iff_eq_neg.mpr h)⟩

open Classical in
theorem tail_mass {L T : ℕ} (hp : p%2=1) (hT : 0<T) (hTm : T ≤ p/2) :
    ∑ t∈univ.erase (0 : ZMod p), (if near T t then 0 else profile L t) ≤ 2*(p:ℝ)^2/T := by
  classical
  let m := p/2
  let f (t : ZMod p) : ℝ := if near T t then 0 else profile L t
  have hsplit : p=2*m+1 := by dsimp [m];omega
  change (∑ t∈univ.erase (0 : ZMod p),f t) ≤ _
  rw [sum_nonzero]
  have href := sum_Ico_reflect (fun n => f (n : ZMod p)) 1 (m:=m+1) (n:=p) (by omega)
  rw [show p+1-(m+1)=m+1 by omega,Nat.add_sub_cancel] at href
  have refl (n : ℕ) (hn : n∈Ico 1 (m+1)) : f ((p-n:ℕ):ZMod p)=f (n:ZMod p) := by
    have h := (mem_Ico.mp hn).2
    simp [f,Nat.cast_sub (show n≤p by omega),near_neg,profile,weight_neg]
  rw [←sum_Ico_consecutive (fun n => f (n:ZMod p)) (m:=1) (n:=m+1) (k:=p)
    (by omega) (by omega),←href,sum_congr rfl refl,←two_mul]
  rw [←sum_Ico_consecutive (fun n => f (n:ZMod p)) (m:=1) (n:=T+1) (k:=m+1)
    (by omega) (by dsimp [m];omega)]
  have hz : ∑ n∈Ico 1 (T+1),f (n:ZMod p)=0 := by
    apply sum_eq_zero
    intro n hn
    have h := (mem_Ico.mp hn).2
    exact if_pos ⟨n,by omega,Or.inl rfl⟩
  rw [hz,zero_add,mul_div_assoc]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    _ ≤ ∑ n∈Ico (T+1) (m+1),(p:ℝ)^2*(n:ℝ)⁻¹^2 := by
      apply sum_le_sum
      intro n hn
      obtain ⟨hn₁,hn₂⟩ := mem_Ico.mp hn
      have h := weight_small (p:=p) (by omega : 0<n) (by dsimp [m] at hn₂;omega : n≤p/2)
      have hn₀ : 0<(n:ℝ) := by exact_mod_cast (show 0<n by omega)
      have hw : weight (n:ZMod p) ≤ (p:ℝ)*(n:ℝ)⁻¹ := by
        rw [←div_eq_mul_inv]
        apply h.trans
        gcongr
        linarith
      dsimp only [f]
      split_ifs
      · positivity
      · unfold profile
        calc
          _ ≤ ((p:ℝ)*(n:ℝ)⁻¹)*((p:ℝ)*(n:ℝ)⁻¹) := mul_le_mul hw ((min_le_right ..).trans hw)
            (le_min (by positivity) (by unfold weight;positivity)) (by positivity)
          _ = _ := by ring
    _ ≤ _ := by
      rw [←mul_sum,div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left (inv_square_sum hT hTm) (by positivity)

#print axioms tail_mass
end Arxiv.«2501.03234».ThetaShortFrequencies
