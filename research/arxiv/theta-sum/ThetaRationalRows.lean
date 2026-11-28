import ThetaDiagonalModEight
import Mathlib.NumberTheory.PrimesCongruentOne
import Mathlib.NumberTheory.Harmonic.Bounds

/-! Signed contributions of coprime odd rational slopes to the canonical theta sum. -/

namespace Arxiv.«2501.03234».ThetaRationalRows

open Finset
open ThetaDiagonal (U oddReps sign rep)

variable {p : ℕ} [Fact p.Prime]

/-- Correlation between the parity of a unit and the parity after multiplication by a slope. -/
def row (a : U p) : ℤ := ∑ b : U p, sign b * sign (a*b)

private lemma parity_neg (hp : p % 2 = 1) (b : U p) :
    rep (-b) % 2 = 1 ↔ rep b % 2 ≠ 1 := by
  let : NeZero (b : ZMod p) := ⟨b.ne_zero⟩
  have hn : rep (-b) = p - rep b := ZMod.val_neg_of_ne_zero (b : ZMod p)
  have hlt : rep b < p := ZMod.val_lt _
  rw [hn]; omega

private lemma sign_neg (hp : p % 2 = 1) (b : U p) : sign (-b) = -sign b := by
  simp only [sign, parity_neg hp]
  split_ifs <;> simp_all

private lemma row_half (hp : p % 2 = 1) (a : U p) :
    row a = 2 * ∑ b ∈ oddReps p, sign (b*a) := by
  let f := fun b : U p => sign b * sign (a*b)
  have h : ∑ b : U p with ¬ rep b % 2 = 1, f b = ∑ b ∈ oddReps p, f b := by
    apply sum_nbij' (fun x => -x) (fun x => -x)
    · simp [oddReps, parity_neg hp]
    · simp [oddReps]
      intro b hb; have := parity_neg hp b; omega
    · simp
    · simp
    · simp [f, mul_neg, sign_neg hp]
  have hodd (b : U p) (hb : b ∈ oddReps p) : f b = sign (b*a) := by
    simp [f, sign, (mem_filter.mp hb).2, mul_comm a b]
  change ∑ b : U p, f b = _
  rw [← sum_filter_add_sum_filter_not univ (fun b : U p => rep b % 2 = 1), h]
  change (∑ b ∈ oddReps p, f b) + (∑ b ∈ oddReps p, f b) = _
  rw [sum_congr rfl hodd]; ring

/-- The selected rows here are actual summands of the pinned theta sum. -/
theorem S_eq_sum_rows (hp : p % 2 = 1) : S p = ∑ a ∈ oddReps p, row a := by
  simp_rw [row_half hp]
  rw [← mul_sum, ThetaDiagonal.S_eq_odd_square hp]

private lemma grid_floor {k a d : ℕ} (hd : 0 < d) (hk : k < a*d) :
    a*(k+1)/(a*d+1) = k/d := by
  have hq := (Nat.div_lt_iff_lt_mul hd).mpr hk
  apply Nat.div_eq_of_lt_le
  · nlinarith only [Nat.mul_le_mul_left a (Nat.mul_div_le k d), hq]
  · have hnext := Nat.succ_le_of_lt (Nat.lt_mul_div_succ k hd)
    nlinarith only [Nat.mul_le_mul_left a hnext, Nat.zero_le (k/d)]

private lemma alternating_sum {n : ℕ} (hn : n % 2 = 1) :
    (∑ x ∈ range n, (-1 : ℤ)^x) = 1 := by
  have h := geom_sum_mul (-1 : ℤ) n
  rw [neg_one_pow_eq_pow_mod_two, hn, pow_one] at h
  linarith

private lemma crt_parity {u v : ℕ} (hu : u % 2 = 1) (hv : v % 2 = 1) (hc : u.Coprime v) :
    (∑ t ∈ range (u*v), (-1 : ℤ)^(t%u) * (-1)^(t%v)) = 1 := by
  have hu0 : 0 < u := by omega
  have hv0 : 0 < v := by omega
  calc
    _ = ∑ ab ∈ range u ×ˢ range v, (-1 : ℤ)^ab.1 * (-1)^ab.2 := by
      apply sum_bij (fun t _ => (t%u,t%v))
      · intro t _; exact mem_product.mpr ⟨mem_range.mpr (Nat.mod_lt _ hu0),
          mem_range.mpr (Nat.mod_lt _ hv0)⟩
      · intro a ha b hb he
        have h := (Nat.modEq_and_modEq_iff_modEq_mul hc).mp
          ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩
        change a % (u*v) = b % (u*v) at h
        simpa [Nat.mod_eq_of_lt (mem_range.mp ha), Nat.mod_eq_of_lt (mem_range.mp hb)] using h
      · rintro ⟨a,b⟩ hab
        obtain ⟨ha,hb⟩ := mem_product.mp hab
        let x := Nat.chineseRemainder hc a b
        refine ⟨x.val, mem_range.mpr (Nat.chineseRemainder_lt_mul hc a b hu0.ne' hv0.ne'), ?_⟩
        exact Prod.ext (Eq.trans x.property.1 (Nat.mod_eq_of_lt (mem_range.mp ha)))
          (Eq.trans x.property.2 (Nat.mod_eq_of_lt (mem_range.mp hb)))
      · intros; rfl
    _ = _ := by simp [sum_product, ← mul_sum, alternating_sum hu, alternating_sum hv]

private lemma div_parity {t u v : ℕ} (hu : u % 2 = 1) (hv : v % 2 = 1) :
    (-1 : ℤ)^(t/u+t/v) = (-1)^(t%u) * (-1)^(t%v) := by
  rw [← pow_add]
  have h (a : ℕ) (ha : a % 2 = 1) :
      (t%a + t/a) % 2 = t % 2 := by
    have hh := congrArg (· % 2) (Nat.mod_add_div t a)
    change (t%a + a*(t/a))%2 = _ at hh
    simpa only [Nat.add_mod, Nat.mul_mod a, ha, one_mul, Nat.mod_mod] using hh
  rw [neg_one_pow_eq_pow_mod_two, neg_one_pow_eq_pow_mod_two (n := t%u+t%v)]
  congr 1; have := h u hu; have := h v hv; omega

private lemma sum_blocks {d n : ℕ} (hd : 0 < d) (f : ℕ → ℤ) :
    ∑ k ∈ range (n*d), f (k/d) = d * ∑ t ∈ range n, f t := by
  calc
    _ = ∑ ab ∈ range n ×ˢ range d, f ab.1 := by
      apply sum_bij (fun k _ => (k/d,k%d))
      · intro k hk; exact mem_product.mpr
          ⟨mem_range.mpr ((Nat.div_lt_iff_lt_mul hd).mpr (mem_range.mp hk)),
           mem_range.mpr (Nat.mod_lt _ hd)⟩
      · intro a _ b _ he; have hq := congrArg Prod.fst he; have hr := congrArg Prod.snd he
        change a / d = b / d at hq; change a % d = b % d at hr
        calc a = a%d + d*(a/d) := (Nat.mod_add_div a d).symm
             _ = b := by rw [hr, hq, Nat.mod_add_div]
      · rintro ⟨a,b⟩ hab
        obtain ⟨ha,hb⟩ := mem_product.mp hab
        have hb' := mem_range.mp hb
        refine ⟨b + d*a, mem_range.mpr ?_, ?_⟩
        · have ha' := mem_range.mp ha
          change a < n at ha'; change b < d at hb'
          nlinarith [Nat.mul_le_mul_left d (Nat.succ_le_of_lt ha')]
        · simp [Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt hb', Nat.mod_eq_of_lt hb']
      · intros; rfl
    _ = _ := by simp [sum_product, mul_sum]

private lemma grid_sum {u v d : ℕ} (hu : u%2=1) (hv : v%2=1) (hc : u.Coprime v)
    (hd : 0 < d) :
    (∑ k ∈ range (u*v*d), (-1 : ℤ)^(u*(k+1)/(u*v*d+1)+v*(k+1)/(u*v*d+1))) = d := by
  have hu0 : 0 < u := by omega
  have hv0 : 0 < v := by omega
  have hf (k : ℕ) (hk : k ∈ range (u*v*d)) :
      (-1 : ℤ)^(u*(k+1)/(u*v*d+1)+v*(k+1)/(u*v*d+1)) =
      (-1)^((k/d)%u) * (-1)^((k/d)%v) := by
    have h₁ := grid_floor (a := u) (d := d*v) (mul_pos hd hv0)
      (show k < u*(d*v) by simpa [Nat.mul_assoc, Nat.mul_comm d v] using mem_range.mp hk)
    have h₂ := grid_floor (a := v) (d := d*u) (mul_pos hd hu0)
      (show k < v*(d*u) by simpa [mul_comm, mul_left_comm, mul_assoc] using mem_range.mp hk)
    rw [show u*v*d=u*(d*v) by ring] at *
    rw [h₁, show u*(d*v)=v*(d*u) by ring, h₂, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul,
      add_comm]
    exact div_parity hu hv
  rw [sum_congr rfl hf, sum_blocks hd (fun t => (-1 : ℤ)^(t%u)*(-1)^(t%v)), crt_parity hu hv hc, mul_one]

private lemma sign_mul_nat {a : U p} {n : ℕ} (ha : (a : ZMod p) = n) (hn : n%2=1)
    (hp : p%2=1) (x : U p) :
    sign (a*x) = (-1 : ℤ)^(rep x+1+n*rep x/p) := by
  have hr : rep (a*x) = n * rep x % p := by
    change ((a : ZMod p) * (x : ZMod p)).val = _
    rw [ha, ← ZMod.natCast_zmod_val (x : ZMod p), ← Nat.cast_mul, ZMod.val_natCast]
    rfl
  have he := congrArg (·%2) (Nat.mod_add_div (n*rep x) p)
  change (n*rep x%p+p*(n*rep x/p))%2=(n*rep x)%2 at he
  rw [← hr, Nat.add_mod, Nat.mul_mod p, hp, one_mul, Nat.mul_mod n, hn, one_mul] at he
  simp only [sign, neg_one_pow_eq_ite, Nat.even_iff]
  split_ifs <;> omega

private lemma range_units (f : ℕ → ℤ) :
    ∑ x : U p, f (rep x) = ∑ k ∈ range (p-1), f (k+1) := by
  apply sum_bij (fun x _ => rep x-1)
  · intro x _
    have hlt : rep x < p := ZMod.val_lt _
    have hpos : rep x ≠ 0 := fun e => x.ne_zero ((ZMod.val_eq_zero _).mp e)
    exact mem_range.mpr (by omega)
  · intro a _ b _ h
    have ha : rep a ≠ 0 := fun e => a.ne_zero ((ZMod.val_eq_zero _).mp e)
    have hb : rep b ≠ 0 := fun e => b.ne_zero ((ZMod.val_eq_zero _).mp e)
    exact Units.ext (ZMod.val_injective p (by change rep a = rep b; omega))
  · intro k hk
    have hlt : k+1 < p := by have := mem_range.mp hk; omega
    have hn : ((k+1 : ℕ) : ZMod p) ≠ 0 := by
      intro he; have hh := congrArg ZMod.val he
      rw [ZMod.val_natCast_of_lt hlt, ZMod.val_zero] at hh; omega
    refine ⟨Units.mk0 _ hn, mem_univ _, ?_⟩
    change ((k+1 : ℕ) : ZMod p).val - 1 = k
    rw [ZMod.val_natCast_of_lt hlt]; omega
  · intro a _
    have ha : rep a ≠ 0 := fun e => a.ne_zero ((ZMod.val_eq_zero _).mp e)
    congr 1; omega

/-- The two parity waves have total one over a complete coprime odd grid. -/
theorem parity_grid_sum {u v : ℕ} (hu : u%2=1) (hv : v%2=1) (hc : u.Coprime v) :
    (∑ t ∈ range (u*v), (-1 : ℤ)^(t/v+t/u)) = 1 := by
  simp_rw [add_comm (_/v) (_/u), div_parity hu hv]
  exact crt_parity hu hv hc

/-- Rotate an odd rational slope into two floor functions evaluated on the same grid. -/
theorem row_ratio_floor_sum {u v : ℕ} (hu : u%2=1) (hv : v%2=1) (hp2 : p%2=1)
    (a b : U p) (ha : (a : ZMod p) = u) (hb : (b : ZMod p) = v) :
    row (a/b) = ∑ k ∈ range (p-1), (-1 : ℤ)^(u*(k+1)/p+v*(k+1)/p) := by
  have hrow : row (a/b) = ∑ x : U p, sign (b*x) * sign (a*x) := by
    unfold row
    apply Fintype.sum_equiv (Equiv.mulLeft b).symm
    intro x
    simp [div_eq_mul_inv, mul_assoc]
  have hpow (x : U p) : sign (b*x) * sign (a*x) =
      (-1 : ℤ)^(u*rep x/p+v*rep x/p) := by
    rw [sign_mul_nat hb hv hp2, sign_mul_nat ha hu hp2, ← pow_add]
    nth_rw 1 [neg_one_pow_eq_pow_mod_two]
    rw [neg_one_pow_eq_pow_mod_two (n := u*rep x/p+v*rep x/p)]
    congr 1; omega
  rw [hrow]
  simp_rw [hpow]
  exact range_units (p := p) (fun x => (-1 : ℤ)^(u*x/p+v*x/p))

/-- On a common grid, a reduced positive odd fraction has exactly the reciprocal-height row. -/
theorem row_ratio {u v d : ℕ} (hu : u%2=1) (hv : v%2=1) (hc : u.Coprime v)
    (hd : 0 < d) (hp : p = u*v*d+1) (hp2 : p%2=1)
    (a b : U p) (ha : (a : ZMod p) = u) (hb : (b : ZMod p) = v) :
    row (a/b) = d := by
  rw [row_ratio_floor_sum hu hv hp2 a b ha hb, hp, Nat.add_sub_cancel]
  exact grid_sum hu hv hc hd

/-- Use the unit represented by n for the slopes below, whose coordinates lie between 3 and p. -/
private def natUnit (p n : ℕ) [Fact p.Prime] : U p :=
  if h : (n : ZMod p) ≠ 0 then Units.mk0 _ h else 1

private lemma nat_nonzero {n : ℕ} (h : 0 < n) (hl : n < p) : (n : ZMod p) ≠ 0 := by
  intro he; have hh := congrArg ZMod.val he
  rw [ZMod.val_natCast_of_lt hl, ZMod.val_zero] at hh; omega

private lemma coe_natUnit {n : ℕ} (h : 0 < n) (hl : n < p) :
    (natUnit p n : ZMod p) = n := by simp [natUnit, nat_nonzero h hl]

private def oddLift (a : U p) : U p := if rep a % 2 = 1 then a else -a

private lemma lift_mem (hp : p%2=1) (a : U p) : oddLift a ∈ oddReps p := by
  apply mem_filter.mpr; refine ⟨mem_univ _, ?_⟩
  unfold oddLift; split_ifs with h
  · exact h
  · exact (parity_neg hp _).mpr h

/-- Negating a slope reverses its correlation. -/
theorem row_neg (hp : p%2=1) (a : U p) : row (-a) = -row a := by
  simp [row, neg_mul, sign_neg hp, sum_neg_distrib]

private def oriented (p u v : ℕ) [Fact p.Prime] : U p :=
  oddLift (natUnit p u / natUnit p v)

private lemma ratio_eq_rep {u v z : ℕ} (hu : 0 < u) (hv : 0 < v)
    (hup : u < p) (hvp : v < p) (hz : z < p)
    (he : (z : ZMod p) * v = u) :
    rep (natUnit p u / natUnit p v) = z := by
  have h : ((natUnit p u / natUnit p v : U p) : ZMod p) = z := by
    rw [Units.val_div_eq_div_val, coe_natUnit hu hup, coe_natUnit hv hvp]
    exact (div_eq_iff (nat_nonzero hv hvp)).mpr he.symm
  unfold rep; rw [h, ZMod.val_natCast_of_lt hz]

private lemma smaller_odd {u v d : ℕ} (hu : u%2=1) (hv : v%2=1) (huv : u < v)
    (hd : 0 < d) (hp : p=u*v*d+1) :
    rep (natUnit p u / natUnit p v) % 2 = 1 := by
  have hu0 : 0 < u := by omega
  have hv0 : 0 < v := by omega
  let m := u*d
  have hm : 0 < m := Nat.mul_pos hu0 hd
  have hpm : p = v*m+1 := by dsimp [m]; rw [hp]; ring
  let z := (v-u)*m+1
  have hz : z < p := by
    dsimp [z]; rw [hpm]; exact Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_right (by omega) hm) 1
  have hvp : v < p := by rw [hpm]; nlinarith [Nat.le_mul_of_pos_right v hm]
  have hvu : v-u+u=v := by omega
  have he : z*v+0 = (v-u)*p+u := by dsimp [z]; rw [hpm]; nlinarith only [hvu]
  have he' : (z : ZMod p) * v = u := by
    have hh := congrArg (fun n : ℕ => (n : ZMod p)) he
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_zero, add_zero, ZMod.natCast_self,
      mul_zero, zero_add] using hh
  rw [ratio_eq_rep hu0 hv0 (huv.trans hvp) hvp hz he']
  dsimp [z]; rw [Nat.add_mod, Nat.mul_mod, show (v-u)%2=0 by omega]; simp

private lemma larger_three_odd {j d : ℕ} (hd : 0 < d) (hp : p = 3*(6*j+1)*d+1) :
    rep (natUnit p (6*j+1) / natUnit p 3) % 2 = 1 := by
  let m := (6*j+1)*d
  have hpm : p=3*m+1 := by dsimp [m]; rw [hp]; ring
  have hm : 6*j+1 ≤ m := Nat.le_mul_of_pos_right _ hd
  let z := 2*m+(2*j+1)
  have hz : z < p := by dsimp [z]; omega
  have he : z*3 = 2*p+(6*j+1) := by dsimp [z]; rw [hpm]; ring
  have he' : (z : ZMod p) * (3 : ℕ) = (6*j+1 : ℕ) := by
    have hh := congrArg (fun n : ℕ => (n : ZMod p)) he
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
      ZMod.natCast_self, mul_zero, zero_add] using hh
  rw [ratio_eq_rep (by omega) (by decide : 0<3) (by omega) (by omega) hz he']
  dsimp [z]; omega

private lemma paired_score {u v d : ℕ} (hu : u%2=1) (hv : v%2=1) (hc : u.Coprime v)
    (huv : u < v) (hd : 0 < d) (hp : p=u*v*d+1) (hp2 : p%2=1) :
    0 ≤ row (oriented p u v) + row (oriented p v u) ∧
    (rep (natUnit p v / natUnit p u) % 2 = 1 →
      row (oriented p u v) + row (oriented p v u) = 2*d) := by
  have hu0 : 0 < u := by omega
  have hv0 : 0 < v := by omega
  have hvp : v < p := by
    have hm := Nat.mul_pos hu0 hd; rw [hp]
    nlinarith only [Nat.le_mul_of_pos_right v hm]
  have ha := coe_natUnit hu0 (huv.trans hvp)
  have hb := coe_natUnit hv0 hvp
  have h₁ := row_ratio hu hv hc hd hp hp2 _ _ ha hb
  have h₂ := row_ratio hv hu hc.symm hd (by rwa [mul_comm v u]) hp2 _ _ hb ha
  simp only [oriented, oddLift, if_pos (smaller_odd hu hv huv hd hp)]
  split_ifs with h <;> simp_all [row_neg hp2]
  ring

/-- Reduced directed fractions of height at most H, excluding numerator or denominator one. -/
def labels (H : ℕ) : Finset (ℕ × ℕ) :=
  (Icc 3 H ×ˢ Icc 3 H).filter fun e =>
    e.1 % 2 = 1 ∧ e.2 % 2 = 1 ∧ e.1.Coprime e.2 ∧ e.1 ≠ e.2

/-- The actual odd representatives of all the labelled slopes. -/
def rationalRows (p H : ℕ) [Fact p.Prime] : Finset (U p) :=
  (labels H).image fun e => oriented p e.1 e.2

private lemma label_spec {H u v : ℕ} :
    (u,v) ∈ labels H ↔ (3 ≤ u ∧ u ≤ H) ∧ (3 ≤ v ∧ v ≤ H) ∧
      u%2=1 ∧ v%2=1 ∧ u.Coprime v ∧ u≠v := by
  simp [labels, and_assoc]

private lemma label_swap {H u v : ℕ} (h : (u,v) ∈ labels H) : (v,u) ∈ labels H := by
  obtain ⟨hu,hv,huo,hvo,hc,hn⟩ := label_spec.mp h
  exact label_spec.mpr ⟨hv,hu,hvo,huo,hc.symm,hn.symm⟩

private lemma orient_eq {u v : ℕ} (hu : 0<u) (hv : 0<v) (hup : u<p) (hvp : v<p) :
    (oriented p u v : ZMod p) * v = u ∨ (oriented p u v : ZMod p) * v = -u := by
  unfold oriented oddLift
  split_ifs <;> simp [Units.val_div_eq_div_val, coe_natUnit hu hup, coe_natUnit hv hvp,
    nat_nonzero hv hvp]

private lemma label_injective {H : ℕ} (hp : 2*H^2 < p) :
    Set.InjOn (fun e : ℕ × ℕ => oriented p e.1 e.2) (labels H) := by
  rintro ⟨u,v⟩ hu ⟨w,z⟩ hw he
  obtain ⟨⟨hu3,huH⟩,⟨hv3,hvH⟩,_,_,hc,_⟩ := label_spec.mp hu
  obtain ⟨⟨hw3,hwH⟩,⟨hz3,hzH⟩,_,_,hc',_⟩ := label_spec.mp hw
  have hH : H<p := by nlinarith [Nat.le_mul_self H]
  have h₁ := orient_eq (by omega : 0<u) (by omega : 0<v) (by omega : u<p) (by omega : v<p)
  have h₂ := orient_eq (by omega : 0<w) (by omega : 0<z) (by omega : w<p) (by omega : z<p)
  change oriented p u v = oriented p w z at he
  rw [← he] at h₂
  have h₃ : (u : ZMod p)*z = w*v ∨ (u : ZMod p)*z + w*v = 0 := by
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
    · left; linear_combination (v : ZMod p)*h₂ - (z : ZMod p)*h₁
    · right; linear_combination (v : ZMod p)*h₂ - (z : ZMod p)*h₁
    · right; linear_combination (z : ZMod p)*h₁ - (v : ZMod p)*h₂
    · left; linear_combination (z : ZMod p)*h₁ - (v : ZMod p)*h₂
  have ha : u*z ≤ H^2 := by simpa [sq] using Nat.mul_le_mul huH hzH
  have hb : w*v ≤ H^2 := by simpa [sq] using Nat.mul_le_mul hwH hvH
  have he' : u*z=w*v := by
    rcases h₃ with h|h
    · rw [← Nat.cast_mul, ← Nat.cast_mul] at h
      have hh := congrArg ZMod.val h
      rwa [ZMod.val_natCast_of_lt (show u*z<p by omega),
        ZMod.val_natCast_of_lt (show w*v<p by omega)] at hh
    · rw [← Nat.cast_mul, ← Nat.cast_mul, ← Nat.cast_add] at h
      exact False.elim (nat_nonzero (by positivity : 0<u*z+w*v) (by omega : u*z+w*v<p) h)
  have huw : u ∣ w := hc.dvd_of_dvd_mul_right (he' ▸ dvd_mul_right u z)
  have hwu : w ∣ u := hc'.dvd_of_dvd_mul_right (he'.symm ▸ dvd_mul_right w v)
  obtain rfl := Nat.dvd_antisymm huw hwu
  exact Prod.ext rfl (Nat.eq_of_mul_eq_mul_left (by omega) he'.symm)

private lemma row_sum_labels {H : ℕ} (hp : 2*H^2 < p) :
    ∑ a ∈ rationalRows p H, row a = ∑ e ∈ labels H, row (oriented p e.1 e.2) := by
  exact sum_image (label_injective hp)

private def upper (H : ℕ) := (labels H).filter fun e => e.1 < e.2

private lemma row_sum_pairs {H : ℕ} (hp : 2*H^2 < p) :
    ∑ a ∈ rationalRows p H, row a =
    ∑ e ∈ upper H, (row (oriented p e.1 e.2) + row (oriented p e.2 e.1)) := by
  rw [row_sum_labels hp, sum_add_distrib]
  unfold upper
  rw [← sum_filter_add_sum_filter_not (labels H) (fun e => e.1<e.2)]
  congr 1
  apply sum_nbij' Prod.swap Prod.swap
  · rintro ⟨u,v⟩ h
    obtain ⟨hl,hn⟩ := mem_filter.mp h
    have := (label_spec.mp hl).2.2.2.2.2
    exact mem_filter.mpr ⟨label_swap hl, by change v<u; change ¬u<v at hn; omega⟩
  · rintro ⟨u,v⟩ h
    obtain ⟨hl,ht⟩ := mem_filter.mp h
    exact mem_filter.mpr ⟨label_swap hl, by change ¬v<u; change u<v at ht; omega⟩
  · intros; rfl
  · intros; rfl
  · intros; rfl

/-- Each row in the family is an odd-representative summand, beyond (p−H)/H. -/
theorem rationalRows_long {H : ℕ} (hp : 2*H^2 < p) (hp2 : p%2=1) {a : U p}
    (ha : a ∈ rationalRows p H) : a ∈ oddReps p ∧ p ≤ H*rep a+H := by
  obtain ⟨⟨u,v⟩,hl,rfl⟩ := mem_image.mp ha
  refine ⟨lift_mem hp2 _, ?_⟩
  obtain ⟨⟨hu3,huH⟩,⟨hv3,hvH⟩,_,_,hc,_⟩ := label_spec.mp hl
  have hH : H<p := by nlinarith [Nat.le_mul_self H]
  let x := rep (oriented p u v)
  change p ≤ H*x+H
  by_contra! hh
  have hx : (x : ZMod p) = (oriented p u v : ZMod p) := ZMod.natCast_zmod_val _
  have hvx : x*v ≤ H*x := by simpa [mul_comm] using Nat.mul_le_mul_left x hvH
  have h := orient_eq (by omega : 0<u) (by omega : 0<v) (by omega : u<p) (by omega : v<p)
  rw [← hx, ← Nat.cast_mul] at h
  rcases h with h|h
  · have he := congrArg ZMod.val h
    rw [ZMod.val_natCast_of_lt (by omega : x*v<p), ZMod.val_natCast_of_lt (by omega : u<p)] at he
    have hdiv : v ∣ u := he ▸ dvd_mul_left v x
    have hg : u.gcd v = v := Nat.gcd_eq_right hdiv
    rw [hc.gcd_eq_one] at hg
    omega
  · have hz : ((x*v+u : ℕ) : ZMod p) = 0 := by rw [Nat.cast_add,h,neg_add_cancel]
    exact nat_nonzero (by omega : 0<x*v+u) (by omega : x*v+u<p) hz

/-- Modulus giving a common grid for all the fractions of height at most H. -/
def gridModulus (H : ℕ) : ℕ := 8 * (Nat.factorial H)^2

omit [Fact p.Prime] in
private lemma modulus_odd {H : ℕ} (hg : p ≡ 1 [MOD gridModulus H]) : p%2=1 := by
  have h : 2 ∣ gridModulus H := by unfold gridModulus; exact dvd_mul_of_dvd_left (by decide) _
  exact hg.of_dvd h

private lemma grid_factor {H u v : ℕ} (hu : 0<u) (hv : 0<v) (huH : u≤H) (hvH : v≤H)
    (hg : p ≡ 1 [MOD gridModulus H]) : ∃ d, 0<d ∧ p=u*v*d+1 := by
  have hmul := Nat.mul_dvd_mul (Nat.dvd_factorial hu huH) (Nat.dvd_factorial hv hvH)
  have hm : u*v ∣ gridModulus H := by
    unfold gridModulus; rw [sq]; exact dvd_mul_of_dvd_right hmul _
  obtain ⟨d,he⟩ := hm.trans hg.symm.dvd'
  have hprime := (Fact.out : p.Prime).two_le
  refine ⟨d, ?_, by omega⟩
  by_contra! hd
  have : d=0 := by omega
  simp [this] at he; omega

private lemma score_nonneg {H : ℕ} (hg : p ≡ 1 [MOD gridModulus H])
    {e : ℕ × ℕ} (he : e ∈ upper H) :
    0 ≤ row (oriented p e.1 e.2) + row (oriented p e.2 e.1) := by
  rcases e with ⟨u,v⟩
  obtain ⟨hl,huv⟩ := mem_filter.mp he
  obtain ⟨⟨hu3,huH⟩,⟨hv3,hvH⟩,hu,hv,hc,_⟩ := label_spec.mp hl
  obtain ⟨d,hd,hp⟩ := grid_factor (by omega : 0<u) (by omega : 0<v) huH hvH hg
  exact (paired_score hu hv hc huv hd hp (modulus_odd hg)).1

private lemma anchor_label {H j : ℕ} (hj : 0<j) (hh : 6*j+1≤H) :
    (3,6*j+1) ∈ upper H := by
  refine mem_filter.mpr ⟨label_spec.mpr ⟨⟨by decide,by omega⟩,⟨by omega,hh⟩,by decide,
    by omega,?_,by omega⟩,by change 3<6*j+1; omega⟩
  rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_rec]
  simp [show (6*j+1)%3=1 by omega]

private lemma anchor_score {H j : ℕ} (hg : p ≡ 1 [MOD gridModulus H])
    (hj : 0<j) (hh : 6*j+1≤H) :
    (row (oriented p 3 (6*j+1)) + row (oriented p (6*j+1) 3) : ℝ) =
      2*((p:ℝ)-1)/(3*(6*j+1 : ℕ)) := by
  obtain ⟨hl,huv⟩ := mem_filter.mp (anchor_label hj hh)
  obtain ⟨⟨_,huH⟩,_,hu,hv,hc,_⟩ := label_spec.mp hl
  obtain ⟨d,hd,hp⟩ := grid_factor (by decide : 0<3) (by omega : 0<6*j+1) huH hh hg
  have he := (paired_score hu hv hc huv hd hp (modulus_odd hg)).2 (larger_three_odd hd hp)
  rw [← Int.cast_add, he]
  push_cast
  have he' : (p : ℝ)=3*(6*j+1)*d+1 := by exact_mod_cast hp
  rw [he']; field_simp; ring

private lemma reflected_floor {r j : ℕ} (hr : r<p) (hj : 0<j) (hjp : j<p) (hr0 : 0<r) :
    (p-r)*j/p + r*j/p + 1 = j := by
  have pp := (Fact.out : p.Prime)
  have hd : ¬ p ∣ r*j := fun h => (pp.dvd_mul.mp h).elim
    (fun h => hr.not_ge (Nat.le_of_dvd hr0 h)) (fun h => hjp.not_ge (Nat.le_of_dvd hj h))
  have hmod : r*j%p ≠ 0 := fun h => hd (Nat.dvd_of_mod_eq_zero h)
  have hh := Nat.div_add_mod (r*j) p
  have hh' := Nat.mod_lt (r*j) pp.pos
  let q := r*j/p
  have hq : q<j := (Nat.div_lt_iff_lt_mul pp.pos).mpr (by
    simpa [mul_comm] using Nat.mul_lt_mul_of_pos_right hr hj)
  let s := j-(q+1)
  have hs : s+q+1=j := by dsimp [s]; omega
  have hpq := congrArg (fun n : ℕ => n*p) hs
  have hpr : (p-r)*j+r*j=p*j := by rw [← Nat.add_mul, Nat.sub_add_cancel hr.le]
  have hd' : (p-r)*j/p = s := Nat.div_eq_of_lt_le (by dsimp [q] at hpq; nlinarith only [hpq,hpr,hh,hh'])
    (by dsimp [q] at hpq; nlinarith only [hpq,hpr,hh,show 0<r*j%p by omega])
  rw [hd']; exact hs

/-- Each odd-indexed correlation is the original paper's even-numerator Hardy row. -/
theorem row_eq_S' (hp : p%2=1) {a : U p} (ha : a ∈ oddReps p) : row a = S' (p-rep a) p := by
  have hr : rep a < p := ZMod.val_lt _
  have hr0 : rep a ≠ 0 := fun he => a.ne_zero ((ZMod.val_eq_zero _).mp he)
  have h (x : U p) : sign x * sign (a*x) = (-1 : ℤ)^(rep a*rep x/p) := by
    have hx := sign_mul_nat (a := (1 : U p)) (n := 1) (by simp) (by decide) hp x
    simp only [one_mul, Nat.div_eq_of_lt (show rep x < p from ZMod.val_lt _), add_zero] at hx
    rw [hx, sign_mul_nat (n := rep a) (ZMod.natCast_zmod_val _).symm (mem_filter.mp ha).2 hp, ← pow_add]
    nth_rw 1 [neg_one_pow_eq_pow_mod_two]
    rw [neg_one_pow_eq_pow_mod_two (n := rep a*rep x/p)]; congr 1; omega
  unfold row S'
  simp_rw [h, ← Nat.cast_mul, Nat.floor_div_eq_div]
  rw [range_units (fun j => (-1 : ℤ)^(rep a*j/p)), sum_Ico_eq_sum_range]
  apply sum_congr rfl; intro k hk; rw [Nat.add_comm 1 k]
  have hf := reflected_floor hr (show 0<k+1 by omega) (show k+1<p by have := mem_range.mp hk; omega)
    (show 0<rep a by omega)
  nth_rw 1 [neg_one_pow_eq_pow_mod_two]
  rw [neg_one_pow_eq_pow_mod_two (n := k+1+1+(p-rep a)*(k+1)/p)]; congr 1; omega

private lemma negative_anchor {H k : ℕ} (hg : p ≡ 1 [MOD gridModulus H]) (hh : 6*k+5≤H) :
    (3,6*k+5) ∈ upper H ∧
    (row (oriented p (6*k+5) 3) : ℝ) = -((p:ℝ)-1)/(3*(6*k+5 : ℕ)) := by
  have hc : (3 : ℕ).Coprime (6*k+5) := by
    rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_rec]
    simp [show (6*k+5)%3=2 by omega]
  refine ⟨mem_filter.mpr ⟨label_spec.mpr ⟨⟨by decide,by omega⟩,⟨by omega,hh⟩,by decide,
    by omega,hc,by omega⟩,by change 3<6*k+5; omega⟩,?_⟩
  obtain ⟨d,hd,hp⟩ := grid_factor (by decide : 0<3) (by omega : 0<6*k+5) (by omega : 3≤H) hh hg
  let m := (6*k+5)*d
  have hpm : p=3*m+1 := by dsimp [m]; rw [hp]; ring
  have hm : 6*k+5 ≤ m := Nat.le_mul_of_pos_right _ hd
  let z := m+2*k+2
  have hz : z < p := by dsimp [z]; omega
  have he : z*3=p+(6*k+5) := by dsimp [z]; rw [hpm]; ring
  have he' : (z : ZMod p)*(3 : ℕ) = (6*k+5 : ℕ) := by
    have hh := congrArg (fun n : ℕ => (n : ZMod p)) he
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,ZMod.natCast_self,zero_add] using hh
  have hp2 := modulus_odd hg
  have hrep := ratio_eq_rep (by omega : 0<6*k+5) (by decide : 0<3)
    (by omega : 6*k+5<p) (by omega : 3<p) hz he'
  have hz2 : z%2≠1 := by dsimp [z]; omega
  have hr := row_ratio (by omega : (6*k+5)%2=1) (by decide : 3%2=1) hc.symm hd
    (show p = (6*k+5)*3*d+1 by simpa [Nat.mul_comm 3] using hp) hp2
    (natUnit p (6*k+5)) (natUnit p 3)
    (coe_natUnit (by omega) (by omega)) (coe_natUnit (by decide) (by omega))
  simp only [oriented, oddLift, hrep, if_neg hz2, row_neg hp2, hr, Int.cast_neg, Int.cast_natCast]
  have he'' : (p : ℝ)=3*(6*k+5)*d+1 := by exact_mod_cast hp
  rw [he'']; push_cast; field_simp; ring

/-- Along the indicated progression, the full signed family contributes at least a harmonic
multiple of p−1. Both orientations of every reduced fraction in the height box are included. -/
theorem rationalRows_lower {L H : ℕ} (hL : 6*L+1 ≤ H) (hp : 2*H^2 < p)
    (hg : p ≡ 1 [MOD gridModulus H]) :
    2 * ((p:ℝ)-1) / 21 * (harmonic L : ℝ) ≤
      ((∑ a ∈ rationalRows p H, row a : ℤ) : ℝ) := by
  let e (k : ℕ) : ℕ × ℕ := (3,6*(k+1)+1)
  let f (z : ℕ × ℕ) : ℝ := (row (oriented p z.1 z.2) + row (oriented p z.2 z.1) : ℤ)
  have hs : (range L).image e ⊆ upper H := by
    intro a ha
    obtain ⟨k,hk,rfl⟩ := mem_image.mp ha
    exact anchor_label (by omega) (by have := mem_range.mp hk; omega)
  have hi : Set.InjOn e (range L) := by
    intro i _ j _ hij; have hh := congrArg Prod.snd hij
    change 6*(i+1)+1=6*(j+1)+1 at hh; omega
  have hf (k : ℕ) (hk : k ∈ range L) :
      (2*((p:ℝ)-1)/21) * ((k:ℝ)+1)⁻¹ ≤ f (e k) := by
    have ht := anchor_score (j := k+1) hg (by omega) (by have := mem_range.mp hk; omega)
    change _ ≤ ((row (oriented p 3 (6*(k+1)+1)) + row (oriented p (6*(k+1)+1) 3) : ℤ) : ℝ)
    rw [Int.cast_add, ht]
    push_cast
    have hp' : (1:ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_le
    have hk' : 0 ≤ (k:ℝ) := by positivity
    field_simp
    nlinarith [mul_nonneg (sub_nonneg.mpr hp') hk']
  calc
    _ = ∑ k ∈ range L, 2*((p:ℝ)-1)/21 * ((k:ℝ)+1)⁻¹ := by
      simp [harmonic, mul_sum]
    _ ≤ ∑ k ∈ range L, f (e k) := sum_le_sum hf
    _ = ∑ z ∈ (range L).image e, f z := (sum_image hi).symm
    _ ≤ ∑ z ∈ upper H, f z := sum_le_sum_of_subset_of_nonneg hs (fun z hz _ => by
      dsimp only [f]; exact_mod_cast score_nonneg hg hz)
    _ = _ := by rw [row_sum_pairs hp, Int.cast_sum]

/-- Total magnitude of negative contributions from these same long rows. -/
def negativeMass (p H : ℕ) [Fact p.Prime] : ℤ :=
  ∑ a ∈ rationalRows p H, max (-(row a)) 0

/-- Negative rows alone already have harmonic-size mass in the same family. -/
theorem negativeMass_lower {L H : ℕ} (hL : 6*L+1 ≤ H) (hp : 2*H^2 < p)
    (hg : p ≡ 1 [MOD gridModulus H]) :
    ((p:ℝ)-1)/18 * (harmonic L : ℝ) ≤ (negativeMass p H : ℝ) := by
  let e (k : ℕ) : ℕ × ℕ := (6*k+5,3)
  let f (z : ℕ × ℕ) : ℝ := (max (-row (oriented p z.1 z.2)) 0 : ℤ)
  have hs : (range L).image e ⊆ labels H := by
    intro a ha; obtain ⟨k,hk,rfl⟩ := mem_image.mp ha
    apply label_swap
    exact (mem_filter.mp (negative_anchor (k := k) hg (by have := mem_range.mp hk; omega)).1).1
  have hi : Set.InjOn e (range L) := by
    intro i _ j _ hij; have hh := congrArg Prod.fst hij
    change 6*i+5=6*j+5 at hh; omega
  have hf (k : ℕ) (hk : k ∈ range L) : ((p:ℝ)-1)/18 * ((k:ℝ)+1)⁻¹ ≤ f (e k) := by
    have hr := (negative_anchor (k := k) hg (by have := mem_range.mp hk; omega)).2
    change _ ≤ ((max (-(row (oriented p (6*k+5) 3))) 0 : ℤ) : ℝ)
    rw [Int.cast_max, Int.cast_neg, hr]
    apply le_trans _ (le_max_left _ _)
    push_cast
    have hp' : (1:ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_le
    field_simp
    linarith
  calc
    _ = ∑ k ∈ range L, ((p:ℝ)-1)/18 * ((k:ℝ)+1)⁻¹ := by simp [harmonic, mul_sum]
    _ ≤ ∑ k ∈ range L, f (e k) := sum_le_sum hf
    _ = ∑ z ∈ (range L).image e, f z := (sum_image hi).symm
    _ ≤ ∑ z ∈ labels H, f z := sum_le_sum_of_subset_of_nonneg hs (fun z _ _ => by
      dsimp only [f]; exact_mod_cast (le_max_right (-row (oriented p z.1 z.2)) 0))
    _ = _ := by rw [negativeMass,rationalRows,sum_image (label_injective hp),Int.cast_sum]

/-- Given any target multiple C, a fixed progression of primes has a signed long-row
subtotal exceeding Cp. A nonpositive full sum would force the complementary rows below −Cp. -/
theorem long_rows_arbitrarily_large (C : ℝ) : ∃ H : ℕ,
    (∀ N : ℕ, ∃ p : ℕ, p.Prime ∧ max N (2*H^2) < p ∧ p ≡ 1 [MOD gridModulus H]) ∧
    ∀ (p : ℕ) [Fact p.Prime], 2*H^2 < p → p ≡ 1 [MOD gridModulus H] →
      C*p < ((∑ a ∈ rationalRows p H, row a : ℤ) : ℝ) ∧
      C*p < (negativeMass p H : ℝ) ∧
      (S p ≤ 0 → ((∑ a ∈ oddReps p \ rationalRows p H, row a : ℤ) : ℝ) < -C*p) := by
  let B := max C 0 + 1
  have hB : 0 < B := by dsimp [B]; positivity
  obtain ⟨L,hL⟩ := exists_nat_gt (Real.exp (36*B))
  have hh : 36*B ≤ (harmonic L : ℝ) := by
    apply le_trans _ (log_add_one_le_harmonic L)
    rw [← Real.log_exp (36*B)]
    apply Real.log_le_log (Real.exp_pos _)
    push_cast; linarith
  let H := 6*L+1
  refine ⟨H, fun N => Nat.exists_prime_gt_modEq_one _ (by unfold gridModulus; positivity), ?_⟩
  intro p _ hp hg
  have hl := rationalRows_lower (show 6*L+1≤H from le_rfl) hp hg
  have hp' : (2:ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
  have hkp : C*p < B*p := mul_lt_mul_of_pos_right (show C<B by dsimp [B]; linarith [le_max_left C 0])
    (by linarith)
  have ha : C*p < ((∑ a ∈ rationalRows p H, row a : ℤ) : ℝ) := by
    apply lt_of_lt_of_le hkp
    apply le_trans _ hl
    have := mul_le_mul_of_nonneg_left hh (show 0 ≤ 2*((p:ℝ)-1)/21 by linarith)
    nlinarith [mul_nonneg (show 0≤(p:ℝ)-2 by linarith) hB.le]
  have hn := negativeMass_lower (show 6*L+1≤H from le_rfl) hp hg
  have hneg : C*p < (negativeMass p H : ℝ) := by
    apply lt_of_lt_of_le hkp
    apply le_trans _ hn
    have := mul_le_mul_of_nonneg_left hh (show 0 ≤ ((p:ℝ)-1)/18 by linarith)
    nlinarith [mul_nonneg (show 0≤(p:ℝ)-2 by linarith) hB.le]
  refine ⟨ha,hneg,fun hS => ?_⟩
  have hsub : rationalRows p H ⊆ oddReps p := fun _ hx => (rationalRows_long hp (modulus_odd hg) hx).1
  have hs := sum_sdiff hsub (f := row)
  rw [← S_eq_sum_rows (modulus_odd hg)] at hs
  have hs' := congrArg (fun x : ℤ => (x:ℝ)) hs
  simp only [Int.cast_add] at hs'
  have hS' : (S p : ℝ) ≤ 0 := by exact_mod_cast hS
  linarith

end Arxiv.«2501.03234».ThetaRationalRows

#print axioms Arxiv.«2501.03234».ThetaRationalRows.S_eq_sum_rows
#print axioms Arxiv.«2501.03234».ThetaRationalRows.row_ratio
#print axioms Arxiv.«2501.03234».ThetaRationalRows.row_eq_S'
#print axioms Arxiv.«2501.03234».ThetaRationalRows.negativeMass_lower
#print axioms Arxiv.«2501.03234».ThetaRationalRows.rationalRows_long
#print axioms Arxiv.«2501.03234».ThetaRationalRows.rationalRows_lower
#print axioms Arxiv.«2501.03234».ThetaRationalRows.long_rows_arbitrarily_large

#print axioms Arxiv.«2501.03234».ThetaRationalRows.parity_grid_sum
#print axioms Arxiv.«2501.03234».ThetaRationalRows.row_ratio_floor_sum
#print axioms Arxiv.«2501.03234».ThetaRationalRows.row_neg
