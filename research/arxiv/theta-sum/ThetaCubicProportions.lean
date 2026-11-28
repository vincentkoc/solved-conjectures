import ThetaHalfFourthMoment

/-! Positive proportions of large positive and negative high-order cubic terms. -/
namespace Arxiv.«2501.03234».ThetaCubicProportions
open Finset Filter Real DirichletCharacter ThetaPointwiseCubic ThetaPointwiseCutoff ThetaRealCharacterMoment
open ThetaAbsoluteCubicMass ThetaSignedCubicMass ThetaHalfFourthMoment
noncomputable section
variable {p : ℕ} [Fact p.Prime]

def size (χ : DirichletCharacter ℂ p) : ℝ := ‖halfSum χ‖/Real.sqrt p
def value (χ : DirichletCharacter ℂ p) : ℝ := (cubic χ).re/((p:ℝ)*Real.sqrt p)

theorem normalized_fourth (hp : _root_.Odd p) :
    ∑ χ∈nonprincipal p,(size χ)^4 ≤ momentConstant*p := by
  have hx : 0<(p:ℝ) := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  simp only [size,div_pow,←sum_div]
  rw [div_le_iff₀ (pow_pos (Real.sqrt_pos.mpr hx) 4),
    show (Real.sqrt p)^4=((Real.sqrt p)^2)^2 by ring,Real.sq_sqrt hx.le]
  exact (fourth_bound hp).trans_eq (by ring)

theorem value_bound (χ : DirichletCharacter ℂ p) : |value χ| ≤ (size χ)^3 := by
  have hx : 0<(p:ℝ) := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  rw [value,size,cubic_real,abs_div,abs_mul,abs_of_nonneg (sq_nonneg _),
    abs_of_pos (mul_pos hx (Real.sqrt_pos.mpr hx)),div_pow,
    show (Real.sqrt p)^3=(p:ℝ)*Real.sqrt p by rw [pow_succ,Real.sq_sqrt hx.le]]
  exact div_le_div_of_nonneg_right (by
    calc _ ≤ ‖halfSum χ‖^2*‖halfSum χ‖ := mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (sq_nonneg _)
         _ = _ := by ring) (by positivity)

lemma card_le (D : Finset (DirichletCharacter ℂ p)) : (D.card:ℝ) ≤ p := by
  have hφ := DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ p
  rw [Nat.card_eq_fintype_card] at hφ
  exact_mod_cast (card_le_univ D).trans (hφ ▸ Nat.totient_le p)

lemma many {ι : Type*} (D : Finset ι) (x y : ι → ℝ) (P C : ℝ)
    (hC : 0<C) (hP : 0≤P) (hc : (D.card:ℝ) ≤ P) (hx : ∀ i,0≤x i)
    (hy : ∀ i,|y i| ≤ (x i)^3) (h4 : ∑ i∈D,(x i)^4 ≤ C*P)
    (h1 : P/2048 ≤ ∑ i∈D,max (y i) 0) :
    let K := 8192*(1+C)
    P/(8192*K^3) ≤ ((D.filter (fun i => 1/8192 ≤ y i)).card:ℝ) := by
  classical
  let K := 8192*(1+C)
  have hk : 0<K := by dsimp [K]; positivity
  have point (i) : max (y i) 0 ≤ 1/8192 + (if 1/8192≤y i then K^3 else 0) + (x i)^4/K := by
    have hy' : max (y i) 0 ≤ (x i)^3 := max_le ((le_abs_self _).trans (hy i)) (pow_nonneg (hx _) _)
    have ht : 0≤(if (1:ℝ)/8192≤y i then K^3 else 0) := by split_ifs <;> positivity
    have hn : 0≤(x i)^4/K := by positivity
    by_cases h : x i ≤ K
    · by_cases h' : 1/8192≤y i
      · rw [if_pos h']; linarith only [hy',pow_le_pow_left₀ (hx i) h 3,hn]
      · rw [if_neg h']; have H : max (y i) 0≤1/8192 := max_le (by linarith) (by norm_num)
        linarith only [H,hn]
    · have hh : (x i)^3 ≤ (x i)^4/K := (le_div_iff₀ hk).mpr (by
        nlinarith only [mul_le_mul_of_nonneg_right (le_of_not_ge h) (pow_nonneg (hx i) 3)])
      linarith only [hy',hh,ht]
  have H := h1.trans (sum_le_sum (fun i _ => point i))
  simp only [sum_add_distrib,←sum_filter,←sum_div,sum_const,nsmul_eq_mul] at H
  have ht : C*P/K≤P/8192 := by apply (div_le_iff₀ hk).mpr; dsimp [K]; nlinarith only [hP]
  have hu := (div_le_div_of_nonneg_right h4 hk.le).trans ht
  change P/(8192*K^3) ≤ _
  apply (div_le_iff₀ (by positivity)).mpr
  linarith

def positiveChars (p : ℕ) [Fact p.Prime] (ε : ℝ) := (large p ε).filter (fun χ => 1/8192≤value χ)
def negativeChars (p : ℕ) [Fact p.Prime] (ε : ℝ) := (large p ε).filter (fun χ => 1/8192≤ -value χ)

theorem proportions : ∃ δ : ℝ,0<δ ∧ ∀ ε : ℝ,0<ε →
    ∀ᶠ p : ℕ in atTop,∀ hp : p.Prime,_root_.Odd p →
      letI : Fact p.Prime := ⟨hp⟩
      δ*p ≤ (positiveChars p ε).card ∧ δ*p ≤ (negativeChars p ε).card := by
  let K := 8192*(1+momentConstant)
  have hk : 0<K := by dsimp [K]; positivity [constant_pos]
  refine ⟨1/(8192*K^3),by positivity,?_⟩
  intro ε he
  filter_upwards [both_unscaled he] with p H
  intro hp ho
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨hpos,hneg⟩ := H hp ho
  let D := large p ε
  let t := (p:ℝ)*Real.sqrt p
  have hx : 0<(p:ℝ) := Nat.cast_pos.mpr hp.pos
  have ht : 0<t := mul_pos hx (Real.sqrt_pos.mpr hx)
  have hs : scale p/2048/t=(p:ℝ)/2048 := by dsimp [scale,t]; field_simp
  have h4 : ∑ χ∈D,(size χ)^4 ≤ momentConstant*p := (sum_le_sum_of_subset_of_nonneg (filter_subset _ (nonprincipal p))
    (fun χ _ _ => pow_nonneg (by unfold size; positivity : 0≤ size χ) 4)).trans (normalized_fourth ho)
  have hp' : (p:ℝ)/2048≤∑ χ∈D,max (value χ) 0 := by
    rw [←hs]
    calc _ ≤ positive D/t := div_le_div_of_nonneg_right hpos ht.le
         _ = _ := by simp only [positive,sum_div,value,t,←max_div_div_right ht.le,zero_div]
  have hn' : (p:ℝ)/2048≤∑ χ∈D,max (-value χ) 0 := by
    rw [←hs]
    calc _ ≤ negative D/t := div_le_div_of_nonneg_right hneg ht.le
         _ = _ := by simp only [negative,sum_div,value,t,←neg_div,←max_div_div_right ht.le,zero_div]
  have hx' (χ : DirichletCharacter ℂ p) : 0≤ size χ := by unfold size; positivity
  have hpN := many D size value p momentConstant constant_pos hx.le (card_le D) hx' value_bound h4 hp'
  have hnN := many D size (fun χ => -value χ) p momentConstant constant_pos hx.le (card_le D) hx'
    (fun χ => by simpa only [abs_neg] using value_bound χ) h4 hn'
  change (1/(8192*K^3))*(p:ℝ) ≤ _ ∧ (1/(8192*K^3))*(p:ℝ) ≤ _
  rw [one_div_mul_eq_div]
  exact ⟨hpN,hnN⟩

/-- The full absolute mass, in the normalization of S(p), has the same
order of magnitude as the lower bounds for each of the two signs. -/
theorem absolute_upper (hp : _root_.Odd p) :
    (4/(p.totient:ℝ))*mass (nonprincipal p) ≤
      8*(1+momentConstant)*((p:ℝ)*Real.sqrt p) := by
  classical
  have hprime : p.Prime := Fact.out
  have hx : 0<(p:ℝ) := Nat.cast_pos.mpr hprime.pos
  let t := (p:ℝ)*Real.sqrt p
  have ht : 0<t := mul_pos hx (Real.sqrt_pos.mpr hx)
  have point (χ : DirichletCharacter ℂ p) : |value χ| ≤ 1+(size χ)^4 := by
    apply (value_bound χ).trans
    have hn : 0≤ size χ := by unfold size; positivity
    rcases le_total (size χ) 1 with h|h
    · have H := pow_le_pow_left₀ hn h 3
      simp only [one_pow] at H
      linarith only [H,pow_nonneg hn 4]
    · have H := mul_le_mul_of_nonneg_left h (pow_nonneg hn 3)
      nlinarith only [H]
  have H := sum_le_sum (s:=nonprincipal p) (fun χ _ => point χ)
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul,mul_one,value,abs_div] at H
  change (∑ χ∈nonprincipal p,|(cubic χ).re|/|t|)≤_ at H
  rw [←sum_div,abs_of_pos ht] at H
  have hs := le_trans H (add_le_add (card_le (nonprincipal p)) (normalized_fourth hp))
  change mass (nonprincipal p)/t ≤ _ at hs
  have hM := (div_le_iff₀ ht).mp hs
  have hφ : 0<(p.totient:ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hprime.pos)
  have hφp : (p:ℝ) ≤ 2*p.totient := by
    rw [Nat.totient_prime hprime,Nat.cast_sub hprime.one_le]; push_cast
    have h2 : (2:ℝ)≤p := by exact_mod_cast hprime.two_le
    linarith
  rw [div_mul_eq_mul_div,div_le_iff₀ hφ]
  change 4*mass (nonprincipal p) ≤ 8*(1+momentConstant)*t*p.totient
  nlinarith only [hM,mul_le_mul_of_nonneg_left hφp
    (mul_nonneg (by linarith only [constant_pos] : 0≤1+momentConstant) ht.le)]

#print axioms absolute_upper

#print axioms normalized_fourth
#print axioms proportions
end
end Arxiv.«2501.03234».ThetaCubicProportions
