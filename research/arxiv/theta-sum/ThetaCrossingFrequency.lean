import ThetaConsecutiveCrossings

/-! Count distinct adjacent strict crossings of the original prime residual
in a dyadic interval. Each selected pair lies in a different short interval. -/
namespace Arxiv.«2501.03234».ThetaCrossingFrequency
open Real Finset Filter ThetaConsecutiveCrossings ThetaShortExcursionTails
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Left endpoints of edges whose two primes both lie in the dyadic interval. -/
def starts (X q r : ℕ) := (Ioc X (2*X)).filter (fun a => a.Prime ∧ a%q=r ∧
    ∃ b : ℕ, a<b ∧ b≤2*X ∧ b.Prime ∧ b%q=r ∧ deviation a*deviation b<0 ∧
    ∀ t : ℕ, a<t → t<b → t.Prime → t%q≠r)

private theorem pack {X K q r : ℕ} (win : ∀ j<X/K, Crossing (X+j*K) K q r) :
    X/K≤(starts X q r).card := by
  classical
  have choose : ∀ j, j<X/K → ∃ a∈starts X q r, X+j*K<a ∧ a≤X+(j+1)*K := by
    intro j hj
    obtain ⟨a,b,ha,hab,hb,ha',hb',har,hbr,hs,hgap⟩ := win j hj
    have hh := (Nat.mul_le_mul_right K (show j+1≤X/K by omega)).trans (Nat.div_mul_le_self X K)
    rw [Nat.add_mul,one_mul] at hh
    refine ⟨a,mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega,by omega⟩,ha',har,b,hab,by omega,hb',hbr,hs,hgap⟩,ha,?_⟩
    rw [Nat.add_mul,one_mul]; omega
  let f (j : ℕ) := if h : j<X/K then (choose j h).choose else 0
  have spec {j : ℕ} (hj : j<X/K) : f j∈starts X q r ∧ X+j*K<f j ∧ f j≤X+(j+1)*K := by
    simpa only [f,dif_pos hj] using (choose j hj).choose_spec
  have inc {i j : ℕ} (hij : i<j) (hj : j<X/K) : f i<f j :=
    (spec (hij.trans hj)).2.2.trans_lt (lt_of_le_of_lt (Nat.add_le_add_left
      (Nat.mul_le_mul_right K (show i+1≤j by omega)) X) (spec hj).2.1)
  have card := card_le_card_of_injOn (s:=range (X/K)) (t:=starts X q r) f
    (fun _ hj => (spec (mem_range.mp hj)).1) (by
      intro i hi j hj he
      rcases lt_trichotomy i j with h | h | h
      · exact ((inc h (mem_range.mp hj)).ne he).elim
      · exact h
      · exact ((inc h (mem_range.mp hi)).ne he.symm).elim)
  simpa only [card_range] using card

/-- The number of consecutive progression-prime sign changes in `(X,2X]`
is at least `X^(1-θ)/8`, uniformly over the indicated reduced classes. -/
theorem dyadic {θ : ℝ} (hθ : 0≤θ) (hθ' : θ<1) (he : Edge θ) :
    ∃ η b : ℝ, 0<η ∧ 0≤b ∧ ∀ᶠ X : ℕ in atTop, ∀ q r : ℕ, 0 < q → r < q →
    r.Coprime q → log q≤η*(log (log (log X))-b) →
    (X:ℝ)^(1-θ)/8≤((starts X q r).card:ℝ) := by
  obtain ⟨η,b,hη,hb,hwin⟩ := intervals he
  obtain ⟨X₀,hwin⟩ := eventually_atTop.mp hwin
  have hn := tendsto_natCast_atTop_atTop (R:=ℝ)
  have hlog := tendsto_log_atTop.comp hn
  have hp := (tendsto_rpow_atTop (sub_pos.mpr hθ')).comp hn
  refine ⟨η,b,hη,hb,?_⟩
  filter_upwards [eventually_ge_atTop X₀,eventually_ge_atTop (2:ℕ),hp.eventually_ge_atTop 8,
    (tendsto_log_atTop.comp hlog).eventually_gt_atTop 0] with X hx hx2 hlarge hlog₂
  intro q r hq hr hqr hqr'
  let K := ⌈(2*(X:ℝ))^θ⌉₊
  have hX : 1≤(X:ℝ) := by exact_mod_cast (show 1≤X by omega)
  have hx' : 0<(X:ℝ) := lt_of_lt_of_le (by norm_num) hX
  have hk : (2*(X:ℝ))^θ≤(K:ℝ) := Nat.le_ceil _
  have hk' : 0<K := by exact_mod_cast ((rpow_pos_of_pos (by positivity : 0<2*(X:ℝ)) θ).trans_le hk)
  apply le_trans _ (Nat.cast_le.mpr (pack (K:=K) (fun j hj => by
    let V := X+j*K
    have bound := (Nat.mul_le_mul_right K (show j+1≤X/K by omega)).trans (Nat.div_mul_le_self X K)
    rw [Nat.add_mul,one_mul] at bound
    have hXV : X≤V := Nat.le_add_right ..
    have hV : V≤2*X := by dsimp [V]; omega
    apply hwin V (hx.trans hXV) K (show K≤V from (by omega : K≤X).trans hXV)
    · exact (rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hV) hθ).trans hk
    · exact hq
    · exact hr
    · exact hqr
    · apply hqr'.trans (mul_le_mul_of_nonneg_left (sub_le_sub_right _ _) hη.le)
      exact log_le_log hlog₂ (log_le_log (log_pos (by exact_mod_cast (show 1<X by omega)))
        (log_le_log hx' (Nat.cast_le.mpr hXV))))))
  have hpow := one_le_rpow hX hθ
  have htwo : (2:ℝ)^θ≤2 := (rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) hθ'.le).trans_eq (rpow_one _)
  have hK : (K:ℝ)≤4*(X:ℝ)^θ := calc
    _ ≤ (2*(X:ℝ))^θ+1 := (Nat.ceil_lt_add_one (by positivity)).le
    _ ≤ _ := by rw [mul_rpow (by norm_num) hx'.le]; nlinarith only [mul_le_mul_of_nonneg_right htwo (rpow_nonneg hx'.le θ),hpow]
  have hdiv : X<(X/K+1)*K := (Nat.lt_mul_div_succ X hk').trans_le (Nat.mul_comm K (X/K+1)).le
  have hdiv' : (X:ℝ)<((X/K:ℕ)+1:ℝ)*(K:ℝ) := by exact_mod_cast hdiv
  have hprod : (X:ℝ)^(1-θ)*(X:ℝ)^θ=(X:ℝ) := by rw [←rpow_add hx',sub_add_cancel,rpow_one]
  have H : (X:ℝ)^(1-θ)<4*((X/K:ℕ)+1:ℝ) := by
    by_contra! h
    nlinarith only [hprod,hdiv',mul_le_mul_of_nonneg_right h (rpow_nonneg hx'.le θ),
      mul_le_mul_of_nonneg_left hK (show (0:ℝ)≤(X/K:ℕ)+1 by positivity)]
  change 8≤(X:ℝ)^(1-θ) at hlarge
  linarith only [H,hlarge]

#print axioms dyadic
end
end Arxiv.«2501.03234».ThetaCrossingFrequency
