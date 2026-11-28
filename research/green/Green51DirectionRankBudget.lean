import Green51OmissionRowCharge

/-! # Loss away from the middle binary dimension -/
namespace Green51FrameIsomorphisms

private theorem far_rank_product {h d D : ℕ} (hd : d≤h) (far : 2*d+D≤h ∨ h+D≤2*d) :
    4*d*(h-d)+D^2≤h^2 := by
  have split := Nat.sub_add_cancel hd
  rcases far with lo|hi
  · have e : D≤(h-d)-d := by omega
    have order : d≤h-d := by omega
    have a := Nat.sub_add_cancel order
    have b := Nat.pow_le_pow_left e 2
    nlinarith only [split,a,b,sq_nonneg ((h-d)-d : ℕ)]
  · have e : D≤d-(h-d) := by omega
    have order : h-d≤d := by omega
    have a := Nat.sub_add_cancel order
    have b := Nat.pow_le_pow_left e 2
    nlinarith only [split,a,b,sq_nonneg (d-(h-d) : ℕ)]

private theorem far_rank_budget {h d D L : ℕ} (large : 10≤h) (hd : d≤h)
    (far : 2*d+D≤h ∨ h+D≤2*d) (gap : 64*h*(L+1)≤D^2) :
    2*L+D^2/8+(L*h+(d*(h-d)+h))+(L*h+(h+h/2))≤h*h/4 := by
  apply (Nat.le_div_iff_mul_le (by decide : 0<4)).mpr
  have prod := far_rank_product hd far
  have half : 2*(h/2)≤h := by omega
  have cut : 8*(D^2/8)≤D^2 := by omega
  have lh : L≤L*h := by simpa using Nat.mul_le_mul_left L (show 1≤h by omega)
  nlinarith only [prod,gap,half,cut,lh,Nat.zero_le (h*L),Nat.zero_le h]

theorem direction_rank_charge {h d D T : ℕ} (large : 10≤h) (hd : d≤h)
    (far : 2*d+D≤h ∨ h+D≤2*d) (gap : 64*h*(Nat.log 2 h+2)≤D^2)
    (bound : T≤h^h*2^(d*(h-d)+h)) :
    (h+1)^2*2^(D^2/8)*T≤universalDefectNumber h := by
  let L := Nat.log 2 h+1
  have top : h+1≤2^L := Nat.lt_pow_succ_log_self (by decide) h
  have power : h^h≤2^(L*h) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left ((Nat.le_succ h).trans top) _
  have budget := far_rank_budget large hd far (show 64*h*(L+1)≤D^2 from gap)
  let loss := h^h*2^(h+h/2)
  have pos : 0<loss := by dsimp [loss];positivity
  apply Nat.le_of_mul_le_mul_right _ pos
  have sq : (h+1)^2≤2^(2*L) := by
    rw [Nat.mul_comm 2 L,pow_mul]
    exact Nat.pow_le_pow_left top 2
  calc
    (h+1)^2*2^(D^2/8)*T*loss ≤
      2^(2*L)*2^(D^2/8)*(2^(L*h)*2^(d*(h-d)+h))*(2^(L*h)*2^(h+h/2)) := by
        apply Nat.mul_le_mul _ (Nat.mul_le_mul_right _ power)
        exact Nat.mul_le_mul (Nat.mul_le_mul_right _ sq) (bound.trans (Nat.mul_le_mul_right _ power))
    _ = 2^(2*L+D^2/8+(L*h+(d*(h-d)+h))+(L*h+(h+h/2))) := by simp only [pow_add]
    _ ≤ 2^(h*h/4) := Nat.pow_le_pow_right (by decide) budget
    _ ≤ universalDefectNumber h*loss := by simpa [loss,Nat.mul_assoc] using lower_growth large

end Green51FrameIsomorphisms
#print axioms Green51FrameIsomorphisms.direction_rank_charge
