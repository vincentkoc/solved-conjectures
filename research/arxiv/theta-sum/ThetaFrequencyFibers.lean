import ThetaOddSquare

/-! Singular and regular additive-frequency fibers over a cyclic residue ring. -/
namespace Arxiv.«2501.03234».ThetaFrequencyFibers
open Finset ThetaFourier ThetaOddSquare
variable {p : ℕ} [NeZero p]

private lemma sum_residues {M : Type*} [AddCommMonoid M] (f : ZMod p → M) :
    ∑ a, f a = ∑ j∈range p,f (j:ZMod p) := by
  apply sum_bij (fun (a : ZMod p) _ => a.val)
  · exact fun a _ => mem_range.mpr a.val_lt
  · exact fun _ _ _ _ h => ZMod.val_injective p h
  · intro j hj
    exact ⟨(j:ZMod p),mem_univ _,ZMod.val_natCast_of_lt (mem_range.mp hj)⟩
  · intro a _; rw [ZMod.natCast_zmod_val]

private lemma repeated {M : Type*} [AddCommMonoid M] {e : ℕ} [NeZero e]
    (f : ZMod e → M) (d : ℕ) :
    ∑ j∈range (d*e),f (j:ZMod e)=d • ∑ b,f b := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Nat.succ_mul,sum_range_add,ih,succ_nsmul]
    congr 1
    simpa only [Nat.cast_add,Nat.cast_mul,ZMod.natCast_self,mul_zero,zero_add] using (sum_residues f).symm

private lemma reduce_char {d e s : ℕ} [NeZero e] (hd : 0<d) (h : p=d*e) (j : ℕ) :
    ZMod.stdAddChar ((j*(d*s):ℕ):ZMod p)=ZMod.stdAddChar ((j*s:ℕ):ZMod e) := by
  simp only [ZMod.stdAddChar_apply,ZMod.toCircle_natCast]
  apply congrArg Complex.exp
  rw [h]
  push_cast
  have hn : (d:ℂ)≠0 := by exact_mod_cast hd.ne'
  field_simp [hn]

/-- The character t induces a uniform fiber of size gcd(t,p) over each character
value of the quotient of order p/gcd(t,p). The zero frequency is included. -/
theorem frequency_sum {M : Type*} [AddCommMonoid M] (F : ℂ → M) (t : ZMod p)
    {d e s : ℕ} [NeZero e] (hd : 0<d) (hp : p=d*e) (ht : t.val=d*s) (hs : s.Coprime e) :
    ∑ a : ZMod p,F (ZMod.stdAddChar (a*t))=d • ∑ b : ZMod e,F (ZMod.stdAddChar b) := by
  have ht' : t=((d*s:ℕ):ZMod p) := by rw [←ht,ZMod.natCast_zmod_val]
  have H := repeated (fun b : ZMod e => F (ZMod.stdAddChar (b*(s:ZMod e)))) d
  rw [sum_residues,ht']
  simp_rw [← Nat.cast_mul,reduce_char hd hp]
  rw [hp]
  simp only [Nat.cast_mul]
  rw [H]
  congr 1
  obtain ⟨v,hv⟩ := (ZMod.isUnit_iff_coprime s e).2 hs
  rw [←hv]
  exact (Equiv.sum_comp (Units.mulRight v) (fun b => F (ZMod.stdAddChar b)))

private theorem quotient_data (t : ZMod p) :
    ∃ d e s : ℕ, d=t.val.gcd p ∧ 0<d ∧ 0<e ∧ p=d*e ∧ t.val=d*s ∧ s.Coprime e := by
  let d := t.val.gcd p
  have hd : 0<d := Nat.gcd_pos_of_pos_right _ (NeZero.pos p)
  have h₁ := Nat.mul_div_cancel' (Nat.gcd_dvd_right t.val p)
  have h₂ := Nat.mul_div_cancel' (Nat.gcd_dvd_left t.val p)
  have he : 0<p/d := Nat.div_pos (Nat.le_of_dvd (NeZero.pos p) (Nat.gcd_dvd_right t.val p)) hd
  exact ⟨d,p/d,t.val/d,rfl,hd,he,h₁.symm,h₂.symm,Nat.coprime_div_gcd_div_gcd hd⟩

/-- Absolute regular Fourier mass on every multiplier slice, including nonunits. -/
theorem slice_weight (hp : p%2=1) (t : ZMod p) :
    ∑ a : ZMod p,weight (a*t) ≤ (p:ℝ)*harmonic (p/2) := by
  obtain ⟨d,e,s,_,hd,he,hp',ht,hs⟩ := quotient_data t
  let : NeZero e := ⟨he.ne'⟩
  have ho : e%2=1 := Nat.odd_iff.mp ((Nat.odd_iff.mpr hp).of_dvd_nat ⟨d,by rw [hp',mul_comm]⟩)
  have H := frequency_sum (fun z : ℂ => 2/‖z-1‖) t hd hp' ht hs
  change (∑ a : ZMod p,weight (a*t))=d • ∑ b : ZMod e,weight b at H
  rw [H,nsmul_eq_mul,←sum_erase_add _ _ (mem_univ (0:ZMod e))]
  simp only [weight,AddChar.map_zero_eq_one,sub_self,norm_zero,div_zero,add_zero]
  have hle : e≤p := Nat.le_of_dvd (NeZero.pos p) ⟨d,by rw [hp',mul_comm]⟩
  have hh : harmonic (e/2) ≤ harmonic (p/2) := by
    unfold harmonic
    exact sum_le_sum_of_subset_of_nonneg (range_mono (Nat.div_le_div_right hle)) (by intros; positivity)
  calc _ ≤ (d:ℝ)*((e:ℝ)*harmonic (e/2)) := mul_le_mul_of_nonneg_left (weight_mass ho) (Nat.cast_nonneg _)
       _ ≤ (p:ℝ)*harmonic (p/2) := by rw [←mul_assoc,←Nat.cast_mul,←hp']; gcongr

/-- The zero fiber of multiplication by t has exactly gcd(t,p) elements. -/
theorem zero_fiber (t : ZMod p) :
    (∑ a : ZMod p,if a*t=0 then 1 else 0 : ℕ)=t.val.gcd p := by
  classical
  obtain ⟨d,e,s,hg,hd,he,hp,ht,hs⟩ := quotient_data t
  let : NeZero e := ⟨he.ne'⟩
  have character_one {k : ℕ} [NeZero k] (x : ZMod k) : ZMod.stdAddChar x=1 ↔ x=0 := by
    rw [←(ZMod.stdAddChar (N:=k)).map_zero_eq_one]
    exact (ZMod.injective_stdAddChar (N:=k)).eq_iff
  have H := frequency_sum (fun z : ℂ => if z=1 then (1:ℕ) else 0) t hd hp ht hs
  simpa only [character_one,sum_ite_eq',mem_univ,if_true,nsmul_eq_mul,mul_one,Nat.cast_id,hg] using H

#print axioms frequency_sum
#print axioms slice_weight
#print axioms zero_fiber
end Arxiv.«2501.03234».ThetaFrequencyFibers
