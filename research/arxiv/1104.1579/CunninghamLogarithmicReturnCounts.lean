import CunninghamSparsePairScale
import CunninghamJointCoverBounds

/-! Choosing a progression in which early prime returns from both signs
occupy arbitrarily little prime mass. -/

namespace CunninghamChain.OrbitIsolation
open Finset Filter Real SquarefreeSeeds PrimePeriodSupply

def EarlyReturn (c : ℝ) (p : ℕ) : Prop :=
  ∃ (b : Bool) (i : ℕ), ((i+1:ℕ):ℝ)≤c*log p ∧ (SquarefreeSeeds.term b p (i+1)).Prime

noncomputable def returningParameters (c : ℝ) (A W X : ℕ) : Finset ℕ := by
  classical
  exact (range X).filter fun t => let p := A+W*t; p.Prime ∧ W<p ∧ EarlyReturn c p

private lemma covered_parameters {T c : ℝ} (hc : 0≤c) (S : PeriodSupply T) (A : ℕ)
    (cover : ∀ p : ℕ, S.seedModulus<p → p ≡ A [MOD S.seedModulus] → ∀ b : Bool, ∀ i : ℕ,
      (SquarefreeSeeds.term b p (i+1)).Prime → i.Coprime (S.periodProduct b)) {X : ℕ}
    (large : A+S.seedModulus+1≤X) :
    let W := S.seedModulus
    let H := ⌊2*c*log (X:ℝ)⌋₊
    let I (b : Bool) := (range H).filter (fun i => i.Coprime (S.periodProduct b))
    (returningParameters c A W X).card ≤
      (∑ i∈I true, (affinePairs true A W i X).card)+(∑ i∈I false, (affinePairs false A W i X).card) := by
  classical
  dsimp only
  let W := S.seedModulus
  let H := ⌊2*c*log (X:ℝ)⌋₊
  let I (b : Bool) := (range H).filter fun i => i.Coprime (S.periodProduct b)
  let P (b : Bool) := (I b).biUnion fun i => affinePairs b A W i X
  have inc : returningParameters c A W X ⊆ P true ∪ P false := by
    intro t ht
    obtain ⟨ht,prime,big,b,i,lo,ret⟩ := mem_filter.mp ht
    let p := A+W*t
    have sq : p≤X^2 := by
      have first := Nat.mul_le_mul_left W (mem_range.mp ht).le
      have one := Nat.le_mul_of_pos_right A (show 0<X by omega)
      have cmp := Nat.mul_le_mul_right X (show A+W≤X by dsimp [W]; omega)
      dsimp [p]
      nlinarith
    have lp : 0<(p:ℝ) := by exact_mod_cast prime.pos
    have logBound : log (p:ℝ)≤2*log (X:ℝ) := by
      calc _ ≤ log ((X:ℝ)^2) := Real.log_le_log lp (by exact_mod_cast sq)
           _ = _ := by rw [Real.log_pow]; norm_num
    have hi : i<H := by
      have v := mul_le_mul_of_nonneg_left logBound hc
      have r : ((i+1:ℕ):ℝ)≤2*c*log X := by
        change ((i+1:ℕ):ℝ)≤c*log p at lo
        linarith only [v,lo]
      exact Nat.lt_of_succ_le (Nat.le_floor r)
    have ap : p ≡ A [MOD W] := by simp [p,Nat.ModEq]
    have mem : t∈P b := mem_biUnion.mpr ⟨i,mem_filter.mpr ⟨mem_range.mpr hi,cover p big ap b i ret⟩,
      mem_filter.mpr ⟨ht,prime,ret⟩⟩
    cases b
    · exact mem_union_right _ mem
    · exact mem_union_left _ mem
  exact (card_le_card inc).trans ((card_union_le ..).trans
    (add_le_add (card_biUnion_le ..) (card_biUnion_le ..)))

/-- For any two prescribed constants, select a single reduced progression
on which the count of prime seeds returning within c log p in either sign,
per X progression parameters, is eventually at most δX/log X. -/
theorem sparse_returning_parameters {c δ : ℝ} (hc : 0≤c) (hd : 0<δ) :
    ∃ W A : ℕ, 0<W ∧ A<W ∧ A.Coprime W ∧ ∀ᶠ X : ℕ in atTop,
      ((returningParameters c A W X).card:ℝ)*log X≤δ*X := by
  let η := δ/(16*(c+1))
  have ηp : 0<η := by dsimp [η]; positivity
  obtain ⟨K,kp,scale⟩ := sparse_affine_pair_scale ηp
  let T := K/η+1
  have tp : 0<T := by dsimp [T]; positivity
  obtain ⟨S⟩ := period_supply_exists tp
  obtain ⟨R,unit,good⟩ := S.simultaneous_class
  let W := S.seedModulus
  let A := R%W
  have wp : 0<W := S.modulus_pos
  have cl : A ≡ R [MOD W] := Nat.mod_modEq R W
  have cover := fun (p : ℕ) (hp : W<p) (ap : p ≡ A [MOD W]) => good p hp (ap.trans cl)
  refine ⟨W,A,wp,Nat.mod_lt R wp,cl.gcd_eq.trans unit,?_⟩
  have ef : K*exp (-T)≤η := by
    rw [exp_neg,mul_inv_le_iff₀ (exp_pos _)]
    have bound := Real.add_one_le_exp T
    have id : η*T=K+η := by dsimp [T]; field_simp
    nlinarith [mul_le_mul_of_nonneg_left bound ηp.le]
  let B : ℝ := K*((S.periodProduct true:ℝ)+S.periodProduct false)
  have enough := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (2*B/δ+1)
  filter_upwards [scale,enough,eventually_ge_atTop (A+W+2)] with X sf high big
  let H := ⌊2*c*log (X:ℝ)⌋₊
  let I (b : Bool) := (range H).filter fun i => i.Coprime (S.periodProduct b)
  let total (b : Bool) := ∑ i∈I b, ((affinePairs b A W i X).card:ℝ)
  have pX : 1<(X:ℝ) := by exact_mod_cast (by omega : 1<X)
  have lX := Real.log_pos pX
  have cnt (b : Bool) : total b*(log X)^2≤X*(2*η*H+K*S.periodProduct b) := by
    have s := sf b A W H (I b) wp S.seed_euler_cost (filter_subset ..)
    have num := S.surviving_offset_count b H
    have h := mul_le_mul_of_nonneg_left num kp.le
    have ev := mul_le_mul_of_nonneg_right ef (Nat.cast_nonneg (α:=ℝ) H)
    apply s.trans
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg X)
    change K*((I b).card:ℝ)+η*H ≤ _
    change K*((I b).card:ℝ)≤K*(exp (-T)*H+(S.periodProduct b:ℝ)) at h
    linarith only [h,ev]
  have cb := covered_parameters hc S A cover (X:=X) (by change A+W+1≤X; omega)
  have bound : ((returningParameters c A W X).card:ℝ)≤total true+total false := by
    change (returningParameters c A W X).card ≤ (∑ i∈I true, (affinePairs true A W i X).card)+
      (∑ i∈I false, (affinePairs false A W i X).card) at cb
    dsimp only [total]
    exact_mod_cast cb
  have combined : ((returningParameters c A W X).card:ℝ)*(log X)^2≤X*(4*η*H+B) := by
    apply (mul_le_mul_of_nonneg_right bound (sq_nonneg _)).trans
    rw [add_mul]
    apply (add_le_add (cnt true) (cnt false)).trans_eq
    dsimp [B]; ring
  have hH : (H:ℝ)≤2*c*log X := Nat.floor_le (by positivity)
  have coeff : 8*η*c≤δ/2 := by
    have id : η*(16*(c+1))=δ := by dsimp [η]; field_simp
    linarith
  have const : B≤(δ/2)*log X := by
    change 2*B/δ+1≤log X at high
    have v := (div_le_iff₀ hd).mp (show 2*B/δ≤log X by linarith)
    linarith
  apply le_of_mul_le_mul_right (a:=log (X:ℝ)) _ lX
  calc _ = ((returningParameters c A W X).card:ℝ)*(log X)^2 := by ring
       _ ≤ X*(4*η*H+B) := combined
       _ ≤ X*((δ/2)*log X+(δ/2)*log X) := by
         apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg X)
         apply add_le_add _ const
         calc 4*η*H ≤ (8*η*c)*log X := by nlinarith only [mul_le_mul_of_nonneg_left hH (show 0≤4*η by positivity)]
              _ ≤ _ := mul_le_mul_of_nonneg_right coeff lX.le
       _ = _ := by ring

#print axioms sparse_returning_parameters

end CunninghamChain.OrbitIsolation
