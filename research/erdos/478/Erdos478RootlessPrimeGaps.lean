import Erdos478PrimeDerangements
import Erdos478ResidueFrobeniusAtTwo
import Erdos478CubicGapTransitivity

/-!
# Binary Frobenius and prime-length factorial gaps

A residue root in a fixed point of Frobenius would be zero or one.
Neither is a root of a factorial gap of length at least two. For the
two cubic-factor classes the residue degree is divisible by three,
so the lift cannot be a translation at prime degree greater than three.
-/

namespace Erdos478.BinaryGap
open Polynomial Ideal NumberField Function
open scoped Polynomial
noncomputable section

def broad (l : ℕ) := l%7=3 ∨ l%7=4

private theorem broad_form {l : ℕ} (hl : l.Prime) (h : broad l) :
    ∃ s : Bool, ∃ m : ℕ, l=2*(7*m+(if s then 5 else 1))+1 := by
  unfold broad at h
  have ho : l%2=1 := hl.eq_two_or_odd.resolve_left (by omega)
  rcases h with ha|ha
  · exact ⟨false,l/14,by simp; omega⟩
  · exact ⟨true,l/14,by simp; omega⟩

private theorem gap_value_map {A B : Type*} [CommRing A] [CommRing B] (j : A →+* B) (l : ℕ) (x : A) :
    j ((descPochhammer A l-1).eval x)=(descPochhammer B l-1).eval (j x) := by
  rw [← eval_map_apply,Polynomial.map_sub,descPochhammer_map,Polynomial.map_one]

private theorem fixes_no_gap_root {K : Type*} [Field K] [NumberField K] {l : ℕ} (hl : 2≤l)
    (J : Ideal (𝓞 K)) [J.IsPrime] (σ : K ≃ₐ[ℚ] K)
    (fixed : ∀ z : 𝓞 K, σ (z:K)=(z:K) → Ideal.Quotient.mk J z=0 ∨ Ideal.Quotient.mk J z=1)
    (x : (rationalGap l).rootSet K) : σ (x:K)≠(x:K) := by
  intro hx
  let f := descPochhammer ℤ l-1
  have mon (R : Type) [CommRing R] [IsDomain R] : (descPochhammer R l-1).Monic := by
    have hD : (descPochhammer R l).IsMonicOfDegree l := ⟨descPochhammer_natDegree R l,monic_descPochhammer R l⟩
    simpa only [sub_eq_add_neg] using (hD.add_right (q := -(1:R[X])) (by simpa using (show 0<l by omega))).monic
  have root : (descPochhammer K l-1).eval (x:K)=0 := by
    have h := (mon ℚ).mem_rootSet.mp x.prop
    simpa only [aeval_def,← eval_map,Polynomial.map_sub,descPochhammer_map,Polynomial.map_one] using h
  have integral : IsIntegral ℤ (x:K) := ⟨f,mon ℤ,by
    simpa only [f,aeval_def,← eval_map,Polynomial.map_sub,descPochhammer_map,Polynomial.map_one] using root⟩
  let z : 𝓞 K := ⟨x,integral⟩
  have hz : (descPochhammer (𝓞 K) l-1).eval z=0 := by
    apply FaithfulSMul.algebraMap_injective (𝓞 K) K
    rw [gap_value_map,map_zero]
    exact root
  let R := (𝓞 K) ⧸ J
  let y := Ideal.Quotient.mk J z
  have hy : (descPochhammer R l).eval y=1 := by
    have he := congrArg (Ideal.Quotient.mk J) hz
    rw [gap_value_map,map_zero,eval_sub,eval_one,sub_eq_zero] at he
    exact he
  have zero (j : ℕ) (hj : j<l) (he : y=(j:R)) : False := by
    rw [he,descPochhammer_eval_coe_nat_of_lt hj] at hy
    exact zero_ne_one hy
  rcases fixed z hx with h|h
  · exact zero 0 (by omega) (by simpa using h)
  · exact zero 1 (by omega) (by simpa using h)

attribute [local instance] Int.ideal_span_isMaximal_of_prime

/-- The root action is doubly transitive for both classes 3 and 4 modulo
seven, including the prime lengths congruent to one modulo three. -/
theorem broad_root_pair_conjugate {l : ℕ} (hl : l.Prime) (h : broad l) (hl3 : 3<l)
    {a b c d : (rationalGap l).rootSet (rationalGap l).SplittingField}
    (hab : a≠b) (hcd : c≠d) :
    ∃ σ : (rationalGap l).SplittingField ≃ₐ[ℚ] (rationalGap l).SplittingField,
      σ (a:_)=(c:_) ∧ σ (b:_)=(d:_) := by
  classical
  let : Fact l.Prime := ⟨hl⟩
  let F := rationalGap l
  let K := F.SplittingField
  let : NumberField K := ⟨⟩
  let : Normal ℚ K := SplittingField.instNormal F
  let : Fact ((F.map (algebraMap ℚ K)).Splits) := ⟨SplittingField.splits F⟩
  let : IsGalois ℚ K := { to_isSeparable := inferInstance, to_normal := SplittingField.instNormal F }
  let P : Ideal ℤ := span {(2:ℤ)}
  let : P.IsMaximal := Int.ideal_span_isMaximal_of_prime 2
  obtain ⟨J,hJ,hcomp⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S:=𝓞 K) P
    (by rw [(RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective ℤ (𝓞 K))]; exact bot_le)
  let : J.IsMaximal := hJ
  let : J.LiesOver P := ⟨hcomp.symm⟩
  obtain ⟨σ,hord,hfix⟩ := binary_frobenius_lift K J
  have h₃ : 3∣J.inertiaDeg ℤ := by
    obtain ⟨s,m,hm⟩ := broad_form hl h
    apply three_dvd_binary_inertia K s m J
    have hs : ((descPochhammer ℚ l-1).map (algebraMap ℚ K)).Splits := SplittingField.splits F
    rw [Polynomial.map_sub,descPochhammer_map,Polynomial.map_one] at hs
    simpa only [← hm] using hs
  have hp : σ^l≠1 := by
    intro hh
    rcases (Nat.dvd_prime hl).mp (h₃.trans (hord.trans (orderOf_dvd_of_pow_eq_one hh))) with he|he <;> omega
  have irr : Irreducible F := GapFamilies.irreducible_gap_rat hl.pos
  have hd : F.natDegree=l := by
    change (descPochhammer ℚ l-1).natDegree=l
    rw [natDegree_sub_eq_left_of_natDegree_lt (by simpa [descPochhammer_natDegree] using hl.pos),descPochhammer_natDegree]
  let ρ := (Gal.galActionHom F K).comp (Gal.restrict F K)
  have ri : Injective (Gal.restrict F K) := (Finite.injective_iff_surjective).mpr (Gal.restrict_surjective F K)
  have hf (x : F.rootSet K) : ρ σ x≠x := fun he =>
    fixes_no_gap_root (by omega) J σ hfix x ((Gal.galActionHom_restrict F K σ x).symm.trans (congrArg Subtype.val he))
  obtain ⟨τ,ha,hb⟩ := PrimeDifferences.two_transitive_of_derangement ρ ((Gal.galActionHom_injective F K).comp ri)
    ((card_rootSet_eq_natDegree irr.separable (SplittingField.splits F)).trans hd)
    (hd ▸ Gal.prime_degree_dvd_card irr (hd ▸ hl)) hf hp hab hcd
  exact ⟨τ,(Gal.galActionHom_restrict F K τ a).symm.trans (congrArg Subtype.val ha),
    (Gal.galActionHom_restrict F K τ b).symm.trans (congrArg Subtype.val hb)⟩

#print axioms broad
#print axioms broad_root_pair_conjugate
end
end Erdos478.BinaryGap
