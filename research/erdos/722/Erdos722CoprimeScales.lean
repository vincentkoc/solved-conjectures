import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# Multiplicative translates of an interval

For any two coprime integer bases greater than one, products of their
powers dilate a nondegenerate positive interval to cover a tail. The
binning and overlap argument generalizes the six-block construction.
-/

namespace Erdos722.PairDesign
namespace Scales
variable {c d : ℕ}
def Scale (c d n : ℕ) := ∃ i j : ℕ, n=c^i*d^j

theorem scale_mul {a b : ℕ} (ha : Scale c d a) (hb : Scale c d b) : Scale c d (a*b) := by
  obtain ⟨i,j,rfl⟩ := ha
  obtain ⟨k,l,rfl⟩ := hb
  exact ⟨i+k,j+l,by rw [pow_add,pow_add]; ring⟩

private def lead (c n : ℕ) := c ^ Nat.log c n

private theorem lead_pos (hc : 0<c) (n : ℕ) : 0 < lead c n := by unfold lead; positivity

private theorem lead_le {n : ℕ} (hn : n ≠ 0) : lead c n ≤ n := Nat.pow_log_le_self _ hn

private theorem bin_lt (hc : 1<c) {L n : ℕ} (hL : 0<L) : L*n/lead c n < c*L := by
  apply (Nat.div_lt_iff_lt_mul (lead_pos (by omega : 0<c) _)).mpr
  have hn := Nat.lt_pow_succ_log_self hc n
  rw [pow_succ] at hn
  simpa only [lead,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using Nat.mul_lt_mul_of_pos_left hn hL

private theorem near (hc : 0<c) {L x y : ℕ} (hx : x≠0) (he : L*y/lead c y=L*x/lead c x) :
    L*(y*lead c x) ≤ (L+1)*(x*lead c y) := by
  let b := L*x/lead c x
  have hyb : L*y < (b+1)*lead c y := by
    apply (Nat.div_lt_iff_lt_mul (lead_pos hc _)).mp
    change L*y/lead c y < L*x/lead c x+1
    omega
  have hxb : b*lead c x ≤ L*x := Nat.div_mul_le_self ..
  have h₁ := Nat.mul_le_mul_right (lead c x) hyb.le
  have h₂ := Nat.mul_le_mul_right (lead c y) hxb
  have h₃ := Nat.mul_le_mul_right (lead c y) (lead_le (c:=c) hx)
  nlinarith only [h₁,h₂,h₃]

private theorem distinct (hc : 0<c) (hd : 1<d) (hcop : c.Coprime d) {i j : ℕ}
    (hne : i≠j) (a b : ℕ) : d^i*c^a ≠ d^j*c^b := by
  obtain ⟨p,hp,hpd⟩ := Nat.exists_prime_and_dvd (by omega : d≠1)
  have hpc : ¬p ∣ c := fun h => (Nat.Prime.not_coprime_iff_dvd.mpr ⟨p,hp,h,hpd⟩) hcop
  have hd' : 0<d := by omega
  have hpval := hp.factorization_pos_of_dvd hd'.ne' hpd
  intro he
  have hv := congrArg (fun n : ℕ => n.factorization p) he
  simp only [Nat.factorization_mul (pow_ne_zero _ hd'.ne') (pow_ne_zero _ hc.ne'),
    Nat.factorization_pow,Finsupp.add_apply,Finsupp.smul_apply,smul_eq_mul,
    Nat.factorization_eq_zero_of_not_dvd hpc,Nat.mul_zero,Nat.add_zero] at hv
  exact hne (Nat.eq_of_mul_eq_mul_right hpval hv)

private theorem nearby_scales (hc₁ : 1<c) (hd₁ : 1<d) (hcop : c.Coprime d) {L : ℕ} (hL : 0<L) :
    ∃ A B, Scale c d A ∧ Scale c d B ∧ 0<A ∧ A<B ∧ L*B≤(L+1)*A := by
  have hc : 0<c := by omega
  have hd : 0<d := by omega
  let f (i : Fin (c*L+1)) : Fin (c*L) := ⟨L*d^i.val/lead c (d^i.val),bin_lt hc₁ hL⟩
  obtain ⟨i,j,hij,hbin⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simp)
  let x := d^i.val
  let y := d^j.val
  have hx : 0<x := by dsimp [x]; positivity
  have hy : 0<y := by dsimp [y]; positivity
  have he : L*x/lead c x=L*y/lead c y := congrArg Fin.val hbin
  have hxy : x*lead c y≠y*lead c x := distinct hc hd₁ hcop (fun e => hij (Fin.ext e)) _ _
  have sA : Scale c d (x*lead c y) := ⟨_,_,Nat.mul_comm ..⟩
  have sB : Scale c d (y*lead c x) := ⟨_,_,Nat.mul_comm ..⟩
  rcases lt_or_gt_of_ne hxy with h | h
  · exact ⟨_,_,sA,sB,Nat.mul_pos hx (lead_pos hc _),h,near hc hx.ne' he.symm⟩
  · exact ⟨_,_,sB,sA,Nat.mul_pos hy (lead_pos hc _),h,near hc hy.ne' he⟩

private def Fits (c d l h u : ℕ) := ∃ z, Scale c d z ∧ l*z≤u ∧ u≤h*z

private theorem tower {l h A B : ℕ} (hA : Scale c d A) (hB : Scale c d B) (hab : A ≤ B)
    (hover : l*B ≤ h*A) (e : ℕ) :
    ∀ z, Scale c d z → ∀ u, l*z*A^e ≤ u → u ≤ h*z*B^e → Fits c d l h u := by
  induction e with
  | zero =>
    intro z hz u hl hu
    exact ⟨z,hz,by simpa using hl,by simpa using hu⟩
  | succ e ih =>
    intro z hz u hl hu
    have mid : l*(z*B)*A^e ≤ h*(z*A)*B^e := calc
      _ = (l*B)*z*A^e := by ring
      _ ≤ (h*A)*z*B^e := by gcongr
      _ = _ := by ring
    by_cases hc : u≤h*(z*A)*B^e
    · apply ih (z*A) (scale_mul hz hA) u _ hc
      simpa only [pow_succ,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using hl
    · apply ih (z*B) (scale_mul hz hB) u (by omega) _
      simpa only [pow_succ,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using hu

private theorem ratio_growth {A B : ℕ} (hab : A<B) (e : ℕ) :
    (A+e)*A^e ≤ A*B^e := by
  induction e with
  | zero => simp
  | succ e ih =>
    have hs := Nat.mul_le_mul_right B ih
    have ht := Nat.mul_le_mul_left ((A+e)*A^e) (show A+1≤B from hab)
    rw [pow_succ,pow_succ]
    nlinarith only [hs,ht,Nat.zero_le (e*A^e)]

theorem scale_cover (hc : 1<c) (hd : 1<d) (hcop : c.Coprime d) {l h : ℕ} (hl : 0<l) (hh : l<h) :
    ∃ N, ∀ u ≥ N, ∃ z, Scale c d z ∧ l*z ≤ u ∧ u ≤ h*z := by
  obtain ⟨A,B,hA,hB,hpos,hab,hnear⟩ := nearby_scales hc hd hcop hl
  have hover := hnear.trans (Nat.mul_le_mul_right A hh)
  let e := c*A
  have hwide : c*A^e ≤ B^e := by
    apply (mul_le_mul_iff_right₀ hpos).mp
    have he := ratio_growth hab e
    have hm : A*c≤A+e := by dsimp [e]; nlinarith
    exact (by simpa only [Nat.mul_assoc] using (Nat.mul_le_mul_right (A^e) hm).trans he)
  let L := l*A^e
  have hL : 0<L := Nat.mul_pos hl (pow_pos hpos _)
  refine ⟨L,?_⟩
  intro u hu
  have hq : 0<u/L := (Nat.div_pos hu hL)
  let v := Nat.log c (u/L)
  let z := c^v
  have hlow : z*L ≤ u := (Nat.le_div_iff_mul_le hL).mp (Nat.pow_log_le_self _ hq.ne')
  have hup : u < (c*z)*L := (Nat.div_lt_iff_lt_mul hL).mp (by
    simpa only [z,v,pow_succ',Nat.succ_eq_add_one] using Nat.lt_pow_succ_log_self hc (u/L))
  have hz : Scale c d z := ⟨v,0,by simp [z]⟩
  apply tower hA hB hab.le hover e z hz u
  · simpa only [L,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using hlow
  · exact hup.le.trans (calc
      (c*z)*L = l*z*(c*A^e) := by dsimp [L]; ring
      _ ≤ h*z*B^e := by gcongr)

#print axioms scale_cover
end Scales
end Erdos722.PairDesign
