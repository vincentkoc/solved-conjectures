import ThetaCenteredMoment

/-! Logarithmic scales and moment orders for geometrically spaced log-denominator bands. -/
namespace Arxiv.«2501.03234».ThetaDenominatorBandScales
open Finset Filter Real ThetaTiltBudget
noncomputable section

def scale (h : ℕ) : ℕ := 2^h
def first (h : ℕ) := 65536*(h+1)^2
def size (q : ℕ) : ℕ := 2^(4*q)
def steps (h q : ℕ) := q/(1024*(h+1))
def expose (h q : ℕ) : ℕ := 2^(steps h q)
def order (h q : ℕ) := scale h/q
def saving (h : ℕ) := (scale h:ℝ)/(65536*(h+1:ℕ))

theorem quotient {a b : ℕ} (hb : 0 < b) (hab : b ≤ a) :
    b*(a/b) ≤ a ∧ a ≤ 2*(b*(a/b)) := by
  have h := Nat.lt_mul_div_succ a hb
  have h₁ : 1 ≤ a/b := (Nat.le_div_iff_mul_le hb).mpr (by simpa using hab)
  have hd := Nat.mul_le_mul_left b h₁
  rw [Nat.mul_add,Nat.mul_one] at h
  simp only [Nat.mul_one] at hd
  exact ⟨Nat.mul_div_le a b,by omega⟩

theorem ints {h q : ℕ} (hq : first h ≤ q) (ht : q ≤ scale h) :
    64*(h+1) ≤ steps h q ∧ 1 ≤ order h q ∧
    steps h q*(1024*(h+1)) ≤ q ∧ q ≤ 2*(steps h q*(1024*(h+1))) ∧
    order h q*q ≤ scale h ∧ scale h ≤ 2*(order h q*q) := by
  have H : 64*(h+1)*(1024*(h+1)) ≤ q := by simpa [first,show 64*(h+1)*(1024*(h+1))=65536*(h+1)^2 by ring] using hq
  have hs : 64*(h+1) ≤ steps h q := (Nat.le_div_iff_mul_le (by positivity)).mpr H
  have hb : 1024*(h+1) ≤ q := by
    apply le_trans _ H;calc 1024*(h+1) = 1*(1024*(h+1)) := by simp
                            _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
  have hp : 0 < q := by omega
  have h₀ := quotient (by positivity) hb
  have h₁ := quotient hp ht
  exact ⟨hs,(Nat.le_div_iff_mul_le hp).mpr (by simpa using ht),by simpa [steps,Nat.mul_comm] using h₀.1,
    by simpa [steps,Nat.mul_comm] using h₀.2,by simpa [order,Nat.mul_comm] using h₁.1,by simpa [order,Nat.mul_comm] using h₁.2⟩

theorem first_le : ∀ᶠ h : ℕ in atTop,first h ≤ scale h := by
  have hf := (tendsto_pow_const_div_const_pow_of_one_lt 2 (by norm_num : (1:ℝ)<2))
  filter_upwards [hf.eventually_le_const (by norm_num : (0:ℝ)<1/262144),eventually_ge_atTop 1] with h hh hp
  have hc : 1 ≤ (h:ℝ) := by exact_mod_cast hp
  change (h:ℝ)^2/(2:ℝ)^h ≤ _ at hh
  have hs := (div_le_iff₀ (by positivity)).mp hh
  have he : (h:ℝ)+1≤2*h := by linarith
  have := pow_le_pow_left₀ (by positivity : 0 ≤ (h:ℝ)+1) he 2
  change 65536*(h+1)^2 ≤ 2^h
  exact_mod_cast (show 65536*((h:ℝ)+1)^2 ≤ (2:ℝ)^h by nlinarith)

theorem log_expose (h q : ℕ) : log (expose h q:ℝ)=steps h q*log 2 := by simp [expose,log_pow]
theorem log_size (q : ℕ) : log (size q:ℝ)=4*q*log 2 := by simp [size,log_pow]
theorem log_scale (h : ℕ) : log (scale h:ℝ)=h*log 2 := by simp [scale,log_pow]

#print axioms ints
end
end Arxiv.«2501.03234».ThetaDenominatorBandScales
