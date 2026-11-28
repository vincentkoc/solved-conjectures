import ThetaMaynardClusters
import ThetaWeilShortIntervals

/-! Pulling a backward prime-tuple count through a fixed affine change of variables. -/
namespace Arxiv.«2501.03234».ThetaAffineSieveInterval
open Finset Filter Real
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

def Count (P : ℕ → Prop) (k : ℕ) (A : ℝ) := ∀ᶠ z : ℕ in atTop, ∀ h : ℕ,
    (z:ℝ)^(21/40:ℝ)≤h → h≤z → A*h/(1+log z)^k ≤ (((Icc (z-h) z).filter P).card:ℝ)

/-- Dilation retains A/(4L) in the lower bound, with room for the shift B and
the entire diameter D. The two endpoint losses are uniform in the interval length. -/
theorem dilate {P V : ℕ → Prop} {k L B D : ℕ} (hL : 8≤L) {A : ℝ} (hA : 0<A)
    (sieve : Count P k A) (maps : ∀ᶠ n : ℕ in atTop, P n → V (L*n+B)) :
    ∀ᶠ X : ℕ in atTop, ∀ H : ℕ, ((4*L:ℕ):ℝ)*(X:ℝ)^(21/40:ℝ)≤H → H≤X →
    A/((4*L:ℕ):ℝ)*H/(1+log X)^k≤(((Ioc X (X+(H-D))).filter V).card:ℝ) := by
  obtain ⟨z₀,hbase⟩ := eventually_atTop.mp sieve
  obtain ⟨n₀,hmap⟩ := eventually_atTop.mp maps
  have ht := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<21/40)).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [eventually_ge_atTop ((max z₀ n₀)*L+32),
    ht.eventually_ge_atTop ((2*(L+B+D)+4*L:ℕ):ℝ)] with X hX hwide
  intro H hlen htop
  let y := H/(2*L)
  let z := X/L+1+y
  have hL₀ : 0<L := by omega
  have hL' : 0<2*L := by omega
  have hL₄ : 0<((4*L:ℕ):ℝ) := by positivity
  have hlow := (Nat.le_div_iff_mul_le hL₀).mpr (show max z₀ n₀*L≤X by omega)
  have hstart := Nat.lt_mul_div_succ X hL₀
  have hxdiv : X/L≤X/8 := Nat.div_le_div_left hL (by decide)
  have hydiv : H/(2*L)≤H/16 := Nat.div_le_div_left (by omega) (by decide)
  have hzX : z≤X := by dsimp [z,y];omega
  have hz : 1≤z := (Nat.succ_le_succ (Nat.zero_le (X/L))).trans (Nat.le_add_right _ _)
  have hN : 1≤((4*L:ℕ):ℝ) := by exact_mod_cast (by omega : 1≤4*L)
  change ((2*(L+B+D)+4*L:ℕ):ℝ)≤(X:ℝ)^(21/40:ℝ) at hwide
  have hres : 2*(L+B+D)+4*L≤H := by
    exact_mod_cast hwide.trans ((le_mul_of_one_le_left (rpow_nonneg (Nat.cast_nonneg X) _) hN).trans hlen)
  have hpos : 1≤y := Nat.div_pos (by omega) hL'
  have hlen' := Nat.lt_mul_div_succ H hL'
  change H < 2*L*(y+1) at hlen'
  have hy' : 2*L≤(2*L)*y := Nat.le_mul_of_pos_right _ hpos
  have hbound : H≤(4*L)*y := by nlinarith only [hlen',hy']
  have hy : (z:ℝ)^(21/40:ℝ)≤y := by
    have hY : (H:ℝ)≤((4*L:ℕ):ℝ)*y := by exact_mod_cast hbound
    have hz' := rpow_le_rpow (Nat.cast_nonneg z) (show (z:ℝ)≤X by exact_mod_cast hzX)
      (by norm_num : (0:ℝ)≤21/40)
    apply hz'.trans
    exact le_of_mul_le_mul_left (hlen.trans hY) hL₄
  have hb := hbase z (by dsimp [z];omega) y hy (by dsimp [z];omega)
  let S := (Icc (z-y) z).filter P
  let T := (Ioc X (X+(H-D))).filter V
  have hcard : S.card≤T.card := by
    apply card_le_card_of_injOn (fun n => L*n+B)
    · intro n hn
      obtain ⟨hr,hp⟩ := mem_filter.mp hn
      obtain ⟨hl,hu⟩ := mem_Icc.mp hr
      have hl' : X/L+1≤n := by simpa only [z,Nat.add_sub_cancel] using hl
      apply mem_filter.mpr
      refine ⟨mem_Ioc.mpr ⟨?_,?_⟩,hmap n (by omega) hp⟩
      · change X<L*n+B
        exact (hstart.trans_le (Nat.mul_le_mul_left L hl')).trans_le (Nat.le_add_right _ _)
      · change L*n+B≤X+(H-D)
        have hh := Nat.mul_le_mul_left L hu
        have hx := Nat.mul_div_le X L
        have hy' : 2*(L*y)≤H := by simpa only [y,Nat.mul_assoc] using Nat.mul_div_le H (2*L)
        dsimp only [z] at hh
        rw [Nat.mul_add,Nat.mul_add,Nat.mul_one] at hh
        omega
    · intro i _ j _ h
      exact Nat.eq_of_mul_eq_mul_left hL₀ (Nat.add_right_cancel h)
  have hlogpos : 0<1+log (z:ℝ) := by linarith only [log_nonneg (by exact_mod_cast hz : 1≤(z:ℝ))]
  have hlog := log_le_log (by exact_mod_cast hz : 0<(z:ℝ)) (show (z:ℝ)≤X by exact_mod_cast hzX)
  apply le_trans _ (hb.trans (by exact_mod_cast hcard))
  apply div_le_div₀ (by positivity) _ (pow_pos hlogpos k) (pow_le_pow_left₀ hlogpos.le (by linarith) k)
  rw [div_mul_eq_mul_div,div_le_iff₀ hL₄]
  have hreal : (H:ℝ)≤((4*L:ℕ):ℝ)*y := by exact_mod_cast hbound
  nlinarith only [mul_le_mul_of_nonneg_left hreal hA.le]

#print axioms dilate
end
end Arxiv.«2501.03234».ThetaAffineSieveInterval
