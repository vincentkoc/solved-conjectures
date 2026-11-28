import ThetaDirectionalMass

/-! A positive proportion of high-order cubic coefficients in every oriented half-plane. -/
namespace Arxiv.«2501.03234».ThetaDirectionalProportions
open Finset Filter Real Complex DirichletCharacter ThetaPointwiseCubic ThetaPointwiseCutoff
open ThetaRealCharacterMoment ThetaAbsoluteCubicMass ThetaHalfFourthMoment ThetaDirectionalMass
open ThetaCubicProportions ThetaPointwiseOrders
noncomputable section
variable {p : ℕ} [Fact p.Prime]

def ordinate (z : ℂ) (χ : DirichletCharacter ℂ p) : ℝ := projection z χ/((p:ℝ)*Real.sqrt p)

def candidates (p : ℕ) [Fact p.Prime] (z : ℂ) :=
  (nonprincipal p).filter (fun χ => (1:ℝ)/8192≤ordinate z χ)

def high (p : ℕ) [Fact p.Prime] (ε : ℝ) (z : ℂ) :=
  (candidates p z).filter (fun χ => (p:ℝ)^(1-ε)<orderOf χ)

private lemma ordinate_bound {z : ℂ} (hz : ‖z‖=1) (χ : DirichletCharacter ℂ p) :
    |ordinate z χ| ≤ (size χ)^3 := by
  have hx : 0<(p:ℝ) := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  rw [ordinate,size,projection_eq,abs_div,abs_mul,abs_of_nonneg (sq_nonneg _),
    abs_of_pos (mul_pos hx (Real.sqrt_pos.mpr hx)),div_pow,
    show (Real.sqrt p)^3=(p:ℝ)*Real.sqrt p by rw [pow_succ,Real.sq_sqrt hx.le]]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hn : |(z*halfSum χ).re|≤‖halfSum χ‖ := (abs_re_le_norm _).trans_eq (by rw [norm_mul,hz,one_mul])
  nlinarith only [mul_le_mul_of_nonneg_left hn (sq_nonneg ‖halfSum χ‖)]

theorem sparse_orders {ε b : ℝ} (he : 0<ε) (hb : 0<b) :
    ∀ᶠ p : ℕ in atTop,∀ hp : p.Prime, _root_.Odd p →
      letI : Fact p.Prime := ⟨hp⟩
      ∀ D : Finset (DirichletCharacter ℂ p), (∀ χ∈D,(orderOf χ:ℝ)≤(p:ℝ)^(1-ε)) →
        (D.card:ℝ)≤b*p := by
  have hd : 0<ε/2 := half_pos he
  obtain ⟨C,hC,hdv⟩ := divisor_bound hd
  have ht := ((tendsto_rpow_neg_atTop hd).comp (tendsto_natCast_atTop_atTop (R:=ℝ))).const_mul C
  rw [mul_zero] at ht
  filter_upwards [ht.eventually_le_const hb,eventually_ge_atTop 2] with p hsmall hp2
  intro hp ho
  let : Fact p.Prime := ⟨hp⟩
  intro D hD
  have hx : 0<(p:ℝ) := Nat.cast_pos.mpr hp.pos
  have hdiv : ((p-1).divisors.card:ℝ)≤C*(p:ℝ)^(ε/2) :=
    (hdv (p-1) (by omega)).trans (mul_le_mul_of_nonneg_left
      (rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.mpr (Nat.sub_le p 1)) hd.le) hC.le)
  have hc := count_orders ho ((p:ℝ)^(1-ε)) (rpow_nonneg hx.le _) D hD
  change C*(p:ℝ)^(-(ε/2))≤b at hsmall
  calc (D.card:ℝ) ≤ (p:ℝ)^(1-ε)*(C*(p:ℝ)^(ε/2)) := hc.trans (mul_le_mul_of_nonneg_left hdiv (rpow_nonneg hx.le _))
       _ = (C*(p:ℝ)^(-(ε/2)))*p := by
         have H : (p:ℝ)^(1-ε)*(p:ℝ)^(ε/2)=(p:ℝ)^(-(ε/2))*(p:ℝ) := by
           calc _ = (p:ℝ)^(-(ε/2))*(p:ℝ)^(1:ℝ) := by
                  rw [←rpow_add hx,←rpow_add hx]
                  congr 1
                  ring
                _ = _ := by rw [rpow_one]
         linear_combination C*H
       _ ≤ b*p := mul_le_mul_of_nonneg_right hsmall hx.le

/-- The axis and the characters may vary with the prime. The constant is independent of ε and
the axis. Replacing the axis by its negative gives the same count on the opposite side. -/
theorem proportions : ∃ δ : ℝ, 0<δ ∧ ∀ ε : ℝ, 0<ε →
    ∀ᶠ p : ℕ in atTop,∀ hp : p.Prime, _root_.Odd p →
      letI : Fact p.Prime := ⟨hp⟩
      ∀ z : ℂ, ‖z‖=1 → δ*p ≤ ((high p ε z).card:ℝ) := by
  classical
  let K := 8192*(1+momentConstant)
  have hk : 0<K := by dsimp [K]; positivity [constant_pos]
  let δ : ℝ := 1/(2*8192*K^3)
  have hδ : 0<δ := by dsimp [δ]; positivity
  refine ⟨δ,hδ,?_⟩
  intro ε he
  filter_upwards [positive_lower,sparse_orders he hδ] with p hm hL
  intro hp ho
  let : Fact p.Prime := ⟨hp⟩
  intro z hz
  have hx : 0<(p:ℝ) := Nat.cast_pos.mpr hp.pos
  let t := (p:ℝ)*Real.sqrt p
  have ht : 0<t := mul_pos hx (Real.sqrt_pos.mpr hx)
  have hs : scale p/2048/t=(p:ℝ)/2048 := by dsimp [scale,t]; field_simp
  have hp' : (p:ℝ)/2048≤∑ χ∈nonprincipal p,max (ordinate z χ) 0 := by
    rw [←hs]
    calc _ ≤ (∑ χ∈nonprincipal p,max (projection z χ) 0)/t := div_le_div_of_nonneg_right (hm hp ho z hz) ht.le
         _ = _ := by simp only [sum_div,ordinate,t,←max_div_div_right ht.le,zero_div]
  have hx' (χ : DirichletCharacter ℂ p) : 0≤ size χ := by unfold size; positivity
  have hN := many (nonprincipal p) size (ordinate z) p momentConstant constant_pos hx.le
    (ThetaCubicProportions.card_le _) hx' (ordinate_bound hz) (normalized_fourth ho) hp'
  change (p:ℝ)/(8192*K^3)≤((candidates p z).card:ℝ) at hN
  let E := (candidates p z).filter (fun χ => ¬(p:ℝ)^(1-ε)<orderOf χ)
  have hE : (E.card:ℝ)≤δ*p := hL hp ho E (fun χ hχ => le_of_not_gt (mem_filter.mp hχ).2)
  have hsum : (high p ε z).card+E.card=(candidates p z).card :=
    card_filter_add_card_filter_not (s:=candidates p z) _
  have hsum' : ((high p ε z).card:ℝ)+E.card=(candidates p z).card := by exact_mod_cast hsum
  have htwice : 2*(δ*p)=(p:ℝ)/(8192*K^3) := by dsimp [δ]; ring
  linarith only [hN,hE,hsum',htwice]

#print axioms sparse_orders
#print axioms proportions
end
end Arxiv.«2501.03234».ThetaDirectionalProportions
