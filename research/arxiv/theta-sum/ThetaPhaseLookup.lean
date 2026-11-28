import ThetaIntegerScan

/-! Shared angular samples for the integer theta scan. -/
namespace Arxiv.«2501.03234».ThetaPhaseLookup
open Real Filter ThetaIntegerScan ThetaAdditiveReciprocity ThetaReciprocalMesh
open ThetaHorizontalScan ThetaBourgainGaraev ThetaSquareRootWindow
noncomputable section

def width (M : ℕ) := 32*M+1

def residue (p d j : ℕ) : ZMod (4*(d+1)) :=
  -(j:ZMod (4*(d+1)))*(p:ZMod (4*(d+1)))⁻¹

/-- Integer address of the phase, shared by every prefix. -/
def address (p d j : ℕ) : Fin (width (resolution p)) :=
  let D := 4*(d+1)
  letI : NeZero D := ⟨by dsimp [D]; omega⟩
  let Q := width (resolution p)
  ⟨Q*(residue p d j).val/D, (Nat.div_lt_iff_lt_mul (by dsimp [D]; omega)).mpr
    (Nat.mul_lt_mul_of_pos_left (ZMod.val_lt (residue p d j)) (by dsimp [Q,width];omega))⟩

def angle (a D : ℕ) : ℝ := 2*π*((a:ℝ)/D)

private theorem angle_error (M a D : ℕ) (hD : 0<D) :
    (2*(M:ℝ))*|angle a D-angle (width M*a/D) (width M)| ≤ 2/5 := by
  let Q := width M
  let b := Q*a/D
  have hq : 0<(Q:ℝ) := by dsimp [Q,width]; positivity
  have hd : 0<(D:ℝ) := by exact_mod_cast hD
  have h₁ : b*D≤Q*a := Nat.div_mul_le_self ..
  have h₂ : Q*a<b*D+D := by
    have := Nat.mod_add_div (Q*a) D
    have := Nat.mod_lt (Q*a) hD
    dsimp [b]; rw [Nat.mul_comm (Q*a/D) D]; omega
  have hl : (b:ℝ)*D≤(Q:ℝ)*a := by exact_mod_cast h₁
  have hu : (Q:ℝ)*a<(b:ℝ)*D+D := by exact_mod_cast h₂
  have hfrac : (a:ℝ)/D-(b:ℝ)/Q=(Q*a-b*D)/((D:ℝ)*Q) := by field_simp
  change 2*(M:ℝ)*|2*π*((a:ℝ)/D)-2*π*((b:ℝ)/Q)|≤2/5
  rw [←mul_sub,hfrac,abs_of_nonneg (by positivity [sub_nonneg.mpr hl])]
  have hu' : (Q*a-b*D)/((D:ℝ)*Q) ≤ 1/(Q:ℝ) := by
    rw [div_le_div_iff₀ (mul_pos hd hq) hq]
    nlinarith only [mul_nonneg (sub_nonneg.mpr hu.le) hq.le]
  have hy := mul_le_mul_of_nonneg_left hu' (by positivity : 0≤2*π)
  apply (mul_le_mul_of_nonneg_left hy (by positivity : 0≤2*(M:ℝ))).trans
  rw [←mul_assoc,mul_one_div,div_le_iff₀ hq]
  dsimp [Q,width];push_cast
  nlinarith only [mul_nonneg (Nat.cast_nonneg (α:=ℝ) M) (sub_nonneg.mpr pi_lt_d2.le)]

def near (x : ℝ) : ℤ := ⌊x+1/2⌋

private theorem near_error (x : ℝ) : |x-(near x:ℝ)|≤1/2 := by
  dsimp [near];rw [abs_le]
  constructor <;> linarith only [Int.floor_le (x+1/2),Int.lt_floor_add_one (x+1/2)]

/-- The only trigonometric samples are these Q pairs. -/
def samples (M : ℕ) (k : Fin (width M)) : ℤ×ℤ :=
  let θ := angle k (width M)
  (near (2*(M:ℝ)*cos θ),near (2*(M:ℝ)*sin θ))

def lookup (p : ℕ) : Table := fun d j => samples (resolution p) (address p d j)

theorem sample_card (M : ℕ) : Fintype.card (Fin (width M)) = 32*M+1 := Fintype.card_fin _

/-- Calibration is required only at the Q sampled angles. An error of 1/10
before nearest-integer rounding is allowed in each scaled coordinate. -/
def calibrated (M : ℕ) (C : Fin (width M) → ℤ×ℤ) : Prop := ∀ k : Fin (width M),
  |2*(M:ℝ)*cos (angle k (width M))-((C k).1:ℝ)|≤3/5 ∧
  |2*(M:ℝ)*sin (angle k (width M))-((C k).2:ℝ)|≤3/5

theorem calibrate {x v : ℝ} (hv : |x-v|≤1/10) : |x-(near v:ℝ)|≤3/5 := by
  linarith only [hv,near_error v,abs_sub_le x v (near v:ℝ)]

theorem sampled (M : ℕ) : calibrated M (samples M) := by
  intro k
  exact ⟨calibrate (x:=2*(M:ℝ)*cos (angle k (width M))) (by norm_num),
         calibrate (x:=2*(M:ℝ)*sin (angle k (width M))) (by norm_num)⟩

theorem valid_of_calibrated (p : ℕ) (α : ℝ)
    (C : Fin (width (resolution p)) → ℤ×ℤ) (hC : calibrated (resolution p) C) :
    valid p α (fun d j => C (address p d j)) := by
  intro t _
  obtain ⟨d,j⟩ := t
  let D := 4*(d+1)
  let : NeZero D := ⟨by dsimp [D];omega⟩
  let M := resolution p
  let a := (residue p d j).val
  let b := width M*a/D
  let x := angle a D
  let y := angle b (width M)
  have step (f : ℝ → ℝ) (hf : |f x-f y|≤|x-y|) (v : ℤ) (hv : |2*(M:ℝ)*f y-(v:ℝ)|≤3/5) :
      |2*(M:ℝ)*f x-(v:ℝ)|≤1 := by
    have h₁ : |2*(M:ℝ)*f x-2*(M:ℝ)*f y|≤2/5 := by
      rw [←mul_sub,abs_mul,abs_of_nonneg (by positivity : 0≤2*(M:ℝ))]
      exact (mul_le_mul_of_nonneg_left hf (by positivity)).trans (angle_error M a D (by dsimp [D];omega))
    exact (abs_sub_le _ (2*(M:ℝ)*f y) _).trans (by linarith only [h₁,hv])
  have hr : row p d (j:ℤ)=Complex.exp ((x:ℂ)*Complex.I) := by
    unfold row
    rw [ZMod.stdAddChar_apply,ZMod.toCircle_eq_circleExp,Circle.coe_exp]
    rfl
  simp only [scaled,hr,Complex.re_ofReal_mul,Complex.im_ofReal_mul,
    Complex.exp_ofReal_mul_I_re,Complex.exp_ofReal_mul_I_im]
  obtain ⟨hc,hs⟩ := hC (address p d j)
  exact ⟨step cos (abs_cos_sub_cos_le x y) _ hc,step sin (abs_sin_sub_sin_le x y) _ hs⟩

theorem lookup_valid (p : ℕ) (α : ℝ) : valid p α (lookup p) :=
  valid_of_calibrated p α _ (sampled _)

theorem growth (estimate : InitialSumEstimate)
    (weil : ∀ (p : ℕ) [Fact p.Prime],CompleteEstimate p) {α : ℝ} (ha : 0<α) (hb : α<1/3)
    (quiet : ∀ᶠ p : ℕ in atTop, p.Prime → _root_.Odd p →
      ∀ v∈checks p α, ¬crossing (lookup p) v.1 v.2)
    (n : ℕ) : type_of% (conjecture_4_4 n) :=
  ThetaIntegerScan.growth estimate weil ha hb lookup
    (quiet.mono (fun p h hp ho => ⟨lookup_valid p α,h hp ho⟩)) n

#print axioms sample_card
#print axioms calibrate
#print axioms sampled
#print axioms valid_of_calibrated
#print axioms lookup_valid
#print axioms growth
end
end Arxiv.«2501.03234».ThetaPhaseLookup
