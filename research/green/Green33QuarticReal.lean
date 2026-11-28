import Green33RealBudget
import Mathlib.NumberTheory.JacobiSum.Basic

/-! Uniform cyclic sums on zero and the nonzero quadratic residues. -/

open Finset Green33PrimeFlatness Green33RealBudget

namespace Green33QuarticReal

/-- The real weights needed by the quadratic-residue construction exist
exactly when the integral difference of the two signed row counts is at least
minus one. -/
theorem weight_criterion (p : ℝ) (K : ℤ) (hp : 0<p) (hK : (K:ℝ)^2<p) :
    (∃ r c : ℝ, 0<r ∧ r<1 ∧ 0<c ∧
      4*c=1+K*r^2 ∧ 8*c^2-4*c+(p+1)/2=p*r^2) ↔ -1 ≤ K := by
  constructor
  · rintro ⟨r,c,hr,hr1,hc,co,center⟩
    by_contra! bad
    have k : (K:ℝ) ≤ -2 := by exact_mod_cast (show K ≤ -2 by omega)
    have eq : (K:ℝ)^2 * (r^2)^2 + p = 2*p*r^2 := by
      linear_combination 2*center - (4*c+1+K*r^2-2)*co
    have y : 1 ≤ 2*r^2 := by
      by_contra! less
      nlinarith [mul_pos hp (sub_pos.mpr less),mul_nonneg (sq_nonneg (K:ℝ)) (sq_nonneg (r^2))]
    nlinarith [mul_le_mul_of_nonneg_right k (sq_nonneg r)]
  · intro k
    let d := Real.sqrt (1-(K:ℝ)^2/p)
    have inside : 0 < 1-(K:ℝ)^2/p := sub_pos.mpr ((div_lt_one hp).mpr hK)
    have hd : 0 < d := Real.sqrt_pos.mpr inside
    let y := 1/(1+d)
    have hy : 0 < y := one_div_pos.mpr (by linarith)
    have yl : y < 1 := (div_lt_one (by linarith : 0<1+d)).mpr (by linarith)
    have sqd : d^2=1-(K:ℝ)^2/p := Real.sq_sqrt inside.le
    have eq : (K:ℝ)^2*y^2+p=2*p*y := by
      have h : p*d^2=p-(K:ℝ)^2 := by rw [sqd]; field_simp
      dsimp [y]
      field_simp [show 1+d≠0 by linarith]
      nlinarith [h]
    let c := (1+K*y)/4
    have kl : (-1:ℝ) ≤ K := by exact_mod_cast k
    have hc : 0<c := by dsimp [c]; nlinarith [mul_le_mul_of_nonneg_right kl hy.le]
    refine ⟨Real.sqrt y,c,Real.sqrt_pos.mpr hy,?_,hc,?_,?_⟩
    · simpa using Real.sqrt_lt_sqrt hy.le yl
    · rw [Real.sq_sqrt hy.le]; dsimp [c]; ring
    · rw [Real.sq_sqrt hy.le]; dsimp [c]; nlinarith [eq]


section Convolution
variable {p : ℕ} [NeZero p]

private lemma conv_commute (f g : ZMod p → ℝ) (z : ZMod p) : conv f g z = conv g f z := by
  apply Fintype.sum_equiv (Equiv.subLeft z)
  intro i; simp [mul_comm]

private lemma expand (f d : ZMod p → ℝ) (z : ZMod p) :
    conv (fun x => f x+d x) (fun x => f x-d x) z = conv f f z-conv d d z := by
  have term (i) : (f i+d i)*(f (z-i)-d (z-i)) =
      f i*f (z-i)-d i*d (z-i)+(d i*f (z-i)-f i*d (z-i)) := by ring
  simp only [conv,term,sum_add_distrib,sum_sub_distrib]
  change _ + (conv d f z - conv f d z) = _
  rw [conv_commute d f,sub_self,add_zero]

private def delta (z : ZMod p) : ℝ := if z=0 then 1 else 0

private lemma conv_delta (f : ZMod p → ℝ) (z : ZMod p) : conv delta f z=f z := by
  simp [conv,delta,ite_mul]

private lemma centered (q : ZMod p → ℝ) (c : ℝ) (z : ZMod p) :
    let f x := c*delta x+q x/2
    conv f f z = c^2*delta z+c*q z+conv q q z/4 := by
  dsimp only
  have one (i) : (c*delta i+q i/2)*(c*delta (z-i)+q (z-i)/2) =
      c^2*(delta i*delta (z-i))+(c/2)*(delta i*q (z-i))+
      (c/2)*(q i*delta (z-i))+(q i*q (z-i))/4 := by ring
  simp only [conv,one,sum_add_distrib,← mul_sum,← sum_div]
  change c^2*conv delta delta z+(c/2)*conv delta q z+(c/2)*conv q delta z+_ = _
  rw [conv_commute q delta,conv_delta,conv_delta]
  ring

private lemma rows (q s : ZMod p → ℝ) (r c : ℝ) (z : ZMod p) :
    let u x := c*delta x+q x/2+r*s x/2
    let v x := c*delta x+q x/2-r*s x/2
    conv u v z = c^2*delta z+c*q z+(conv q q z-r^2*conv s s z)/4 := by
  dsimp only
  rw [expand,centered]
  have eq : conv (fun i => r*s i/2) (fun i => r*s i/2) z=r^2*conv s s z/4 := by
    simp only [conv,mul_sum,sum_div]
    apply sum_congr rfl;intro i _; ring
  rw [eq]; ring
end Convolution

/-- Indicator of the chosen nonzero labels, with integer values for finite
row certificates. -/
def mark {p : ℕ} (Q : Finset (ZMod p)) (x : ZMod p) : ℤ := if x ∈ Q then 1 else 0

/-- Signed count of ordered pairs of labels with prescribed sum. -/
def signedRow {p : ℕ} [NeZero p] (s : ZMod p → ℤ) (z : ZMod p) : ℤ :=
  ∑ x, s x*s (z-x)

/-- The three integer rows needed for a quadratically invariant construction.
At a nonzero residue its class is specified by membership in `Q`. -/
structure RowCounts (p : ℕ+) (Q : Finset (ZMod p)) (s : ZMod p → ℤ) (K : ℤ) : Prop where
  zero_out : 0 ∉ Q
  size : 2*Q.card+1=p.val
  bounded : ∀ x, |s x| ≤ mark Q x
  at_zero : 2*signedRow (mark Q) 0=(p.val:ℤ)-1 ∧ 2*signedRow s 0=(p.val:ℤ)-1
  off_zero : ∀ z, z ≠ 0 →
    4*signedRow (mark Q) z=(p.val:ℤ)-1-4*mark Q z ∧
    2*signedRow s z=K*(2*mark Q z-1)-1

private lemma row_cast {p : ℕ} [NeZero p] (s : ZMod p → ℤ) (z : ZMod p) :
    (signedRow s z:ℝ)=conv (fun t => (s t:ℝ)) (fun t => (s t:ℝ)) z := by
  simp [signedRow,conv,Int.cast_sum]

/-- The row counts certify that the absolute prime support lower bound is
attained on zero and `Q`. -/
theorem exact_of_rows (p : ℕ+) [Fact p.val.Prime] (Q : Finset (ZMod p)) (s : ZMod p → ℤ) (K : ℤ)
    (h : RowCounts p Q s K) (sizeK : (K:ℝ)^2<p) (signK : -1 ≤ K) :
    ExactSeed p (insert 0 Q) ∧ minimumBudget p=Q.card+1 := by
  classical
  have hp : (0:ℝ)<p := by exact_mod_cast p.pos
  obtain ⟨r,c,hr,h1,hc,mean,center⟩ := (weight_criterion p K hp sizeK).mpr signK
  let q (x : ZMod p) := (mark Q x:ℝ)
  let t (x : ZMod p) := (s x:ℝ)
  let A := insert 0 Q
  let w (x : ZMod p) := c*delta x+q x/2+r*t x/2
  let v (x : ZMod p) := c*delta x+q x/2-r*t x/2
  have cap (x : ZMod p) : -q x ≤ t x ∧ t x ≤ q x := by
    change -(mark Q x:ℝ) ≤ (s x:ℝ) ∧ (s x:ℝ) ≤ (mark Q x:ℝ)
    exact_mod_cast abs_le.mp (h.bounded x)
  have absent (x : ZMod p) (hx : x ∉ Q) : q x=0 ∧ t x=0 := by
    have qx : q x=0 := by simp [q,mark,hx]
    have H := cap x
    rw [qx] at H; exact ⟨qx,by linarith⟩
  have pos (x : ZMod p) (mem : x ∈ A) : 0<w x ∧ 0<v x := by
    rcases mem_insert.mp mem with at0|inside
    · subst x
      obtain ⟨qx,tx⟩ := absent _ h.zero_out
      simpa [w,v,delta,qx,tx] using hc
    · have nonzero : x ≠ 0 := fun e => h.zero_out (e ▸ inside)
      have qx : q x=1 := by simp [q,mark,inside]
      have H := cap x
      rw [qx] at H
      simp only [w,v,delta,if_neg nonzero,mul_zero,zero_add,qx]
      constructor <;> nlinarith [mul_le_mul_of_nonneg_left H.1 hr.le,mul_le_mul_of_nonneg_left H.2 hr.le]
  have outside (x : ZMod p) (hx : x ∉ A) : w x=0 ∧ v x=0 := by
    have ne : x≠0 := fun e => hx (mem_insert.mpr (Or.inl e))
    obtain ⟨qx,tx⟩ := absent _ (fun he => hx (mem_insert_of_mem he))
    simp [w,v,delta,ne,qx,tx]
  have flat (z : ZMod p) : conv w v z = ((p:ℝ)-1+2*r^2*(K+1))/16 := by
    change conv (fun x => c*delta x+q x/2+r*t x/2) (fun x => c*delta x+q x/2-r*t x/2) z=_
    rw [rows]
    have castQ : conv q q z = (signedRow (mark Q) z:ℝ) := (row_cast _ _).symm
    have castT : conv t t z = (signedRow s z:ℝ) := (row_cast _ _).symm
    rw [castQ,castT]
    by_cases eq : z=0
    · subst z
      have qx := (absent 0 h.zero_out).1
      rw [qx,delta,if_pos rfl]
      have Q0 : 2*(signedRow (mark Q) 0:ℝ)=(p:ℝ)-1 := by exact_mod_cast h.at_zero.1
      have S0 : 2*(signedRow s 0:ℝ)=(p:ℝ)-1 := by exact_mod_cast h.at_zero.2
      linear_combination center/8+mean/8 + Q0/8 - r^2*S0/8
    · obtain ⟨hq,hs⟩ := h.off_zero z eq
      have Qz : 4*(signedRow (mark Q) z:ℝ)=(p:ℝ)-1-4*q z := by dsimp only [q];exact_mod_cast hq
      have Sz : 2*(signedRow s z:ℝ)=(K:ℝ)*(2*q z-1)-1 := by dsimp only [q];exact_mod_cast hs
      rw [delta,if_neg eq]
      linear_combination q z*mean/4+Qz/16-r^2*Sz/8
  have restrict (z : ZMod p) : ∑ i : A, w i*v (z-i) = conv w v z := by
    rw [univ_eq_attach,sum_attach A (fun i => w i*v (z-i))]
    exact sum_subset (subset_univ _) fun i _ hi => by rw [(outside _ hi).1,zero_mul]
  let z₀ : A := ⟨0,mem_insert_self _ _⟩
  let : Nonempty A := ⟨z₀⟩
  have witness : ExactSeed p A := exact_of_constant_convolution A id (fun x => w x) v
    (fun i => (pos i i.property).1) (fun x => by
      by_cases hx : x ∈ A
      · exact (pos x hx).2.le
      · rw [(outside _ hx).2])
    (fun x hx => (pos x hx).2) (fun x hx => (outside x hx).2) (fun z => by
      change ∑ i : A, w i*v (z-i) = ∑ i : A, w i*v (0-i)
      rw [restrict,restrict,flat,flat])
  have sz : A.card=Q.card+1 := card_insert_of_notMem h.zero_out
  let B := {k : ℕ | ∃ T : Finset (ZMod p), T.card=k ∧ ExactSeed p T}
  have m : A.card ∈ B := ⟨A,rfl,witness⟩
  have lm : minimumBudget p ≤ A.card := Nat.sInf_le m
  have attained : minimumBudget p ∈ B := Nat.sInf_mem ⟨_,m⟩
  obtain ⟨T,e,u,v',law⟩ := attained
  have lb := prime_divisor_budget (dvd_refl p.val) T u v' law
  have hs := h.size
  exact ⟨witness,by omega⟩

/-- Unnormalized mass on the zero label and the two signed residue classes. -/
noncomputable def residueWeight {p : ℕ+} (Q : Finset (ZMod p)) (s : ZMod p → ℤ)
    (r c : ℝ) (x : ZMod p) : ℝ := c*delta x+(mark Q x:ℝ)/2+r*(s x:ℝ)/2

/-- Strictly positive opposite weights with constant convolution exist exactly
when the signed parameter is at least minus one. -/
theorem flat_weights_iff (p : ℕ+) [Fact p.val.Prime] (Q : Finset (ZMod p)) (s : ZMod p → ℤ)
    (K : ℤ) (h : RowCounts p Q s K) (sizeK : (K:ℝ)^2<p) (one_in : 1 ∈ Q) :
    (∃ r c : ℝ, 0<r ∧ r<1 ∧ 0<c ∧ ∀ z,
      conv (residueWeight Q s r c) (residueWeight Q s (-r) c) z =
        conv (residueWeight Q s r c) (residueWeight Q s (-r) c) 0) ↔ -1≤K := by
  classical
  let f r c := conv (residueWeight Q s r c) (residueWeight Q s (-r) c)
  have value (r c : ℝ) (z : ZMod p) :
      f r c z = c^2*delta z+c*(mark Q z:ℝ)+
        ((signedRow (mark Q) z:ℝ)-r^2*(signedRow s z:ℝ))/4 := by
    have e := rows (fun x => (mark Q x:ℝ)) (fun x => (s x:ℝ)) r c z
    change conv (fun x => c*delta x+(mark Q x:ℝ)/2+r*(s x:ℝ)/2)
      (fun x => c*delta x+(mark Q x:ℝ)/2+(-r)*(s x:ℝ)/2) z = _
    simpa only [neg_mul,neg_div,sub_eq_add_neg,← row_cast] using e
  have zero (r c : ℝ) : f r c 0=c^2+((p:ℝ)-1)*(1-r^2)/8 := by
    rw [value]
    have q : 2*(signedRow (mark Q) 0:ℝ)=(p:ℝ)-1 := by exact_mod_cast h.at_zero.1
    have m : 2*(signedRow s 0:ℝ)=(p:ℝ)-1 := by exact_mod_cast h.at_zero.2
    simp [delta,mark,h.zero_out]
    linear_combination q/8-r^2*m/8
  have off (r c : ℝ) (z : ZMod p) (nz : z≠0) :
      f r c z=((p:ℝ)-1+2*r^2*(K+1))/16+
        (mark Q z:ℝ)*(4*c-1-K*r^2)/4 := by
    rw [value]
    obtain ⟨q,m⟩ := h.off_zero z nz
    have q' : 4*(signedRow (mark Q) z:ℝ)=(p:ℝ)-1-4*(mark Q z:ℝ) := by exact_mod_cast q
    have m' : 2*(signedRow s z:ℝ)=(K:ℝ)*(2*(mark Q z:ℝ)-1)-1 := by exact_mod_cast m
    simp only [delta,if_neg nz,mul_zero,zero_add]
    linear_combination q'/16-r^2*m'/8
  have hp : (0:ℝ)<p := by exact_mod_cast p.pos
  rw [← weight_criterion p K hp sizeK]
  constructor
  · rintro ⟨r,c,hr,hr',hc,flat⟩
    have sz := h.size
    have ne : 0<Q.card := card_pos.mpr ⟨1,one_in⟩
    have lt : (insert 0 Q).card < (univ : Finset (ZMod p)).card := by
      rw [card_insert_of_notMem h.zero_out,card_univ,ZMod.card];omega
    obtain ⟨z,_,absent⟩ := exists_mem_notMem_of_card_lt_card lt
    obtain ⟨nz,notIn⟩ := not_or.mp (mt mem_insert.mpr absent)
    have once : f r c 1=f r c 0 := flat 1
    have other : f r c z=f r c 0 := flat z
    rw [off _ _ _ one_ne_zero,zero] at once
    rw [off _ _ _ nz,zero] at other
    simp only [mark,if_pos one_in,if_neg notIn,Int.cast_one,Int.cast_zero,one_mul,zero_mul] at once other
    refine ⟨r,c,hr,hr',hc,?_,?_⟩
    · linear_combination 4*once-4*other
    · linear_combination -4*once-4*other
  · rintro ⟨r,c,hr,hr',hc,w,t⟩
    refine ⟨r,c,hr,hr',hc,fun z => ?_⟩
    change f r c z=f r c 0
    by_cases nz : z=0
    · rw [nz]
    rw [off _ _ _ nz,zero]
    linear_combination ((mark Q z:ℝ)/4-1/8)*w-t/8

/-- Quadratic residues and their two quartic classes, encoded by Euler powers
for direct finite verification. -/
def squares (p : ℕ+) : Finset (ZMod p) :=
  univ.filter fun x => x^(p.val/2)=1

def signature (p : ℕ+) (x : ZMod p) : ℤ :=
  if x^(p.val/4)=1 then 1 else if x^(p.val/4)= -1 then -1 else 0

#print axioms weight_criterion
#print axioms exact_of_rows
#print axioms flat_weights_iff
end Green33QuarticReal
