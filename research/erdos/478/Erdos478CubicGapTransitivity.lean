import Erdos478PrimePairTransitivity
import Erdos478CubicSplittingDegree
import Erdos478DisjointGapFamilies
import Mathlib.FieldTheory.PolynomialGaloisGroup

/-!
# Doubly transitive Galois groups of prime-length factorial gaps

The binary cubic and prime-degree arguments apply together in the two
reduced residue classes 11 and 17 modulo 21.
-/

namespace Erdos478.BinaryGap
noncomputable section
open Polynomial
open scoped Polynomial

def selected (l : ℕ) := l%21=11 ∨ l%21=17

theorem selected_form {l : ℕ} (hl : l.Prime) (h : selected l) :
    ∃ s : Bool, ∃ m : ℕ, l=2*(7*m+(if s then 5 else 1))+1 := by
  have ho : l%2=1 := hl.eq_two_or_odd.resolve_left (by unfold selected at h; omega)
  obtain hl | hl := h
  · exact ⟨true,l/14,by simp; omega⟩
  · exact ⟨false,l/14,by simp; omega⟩

def rationalGap (l : ℕ) : ℚ[X] := descPochhammer ℚ l-1

theorem root_pair_conjugate {l : ℕ} (hl : l.Prime) (h : selected l)
    {a b c d : (rationalGap l).rootSet (rationalGap l).SplittingField}
    (hab : a≠b) (hcd : c≠d) :
    ∃ σ : (rationalGap l).SplittingField ≃ₐ[ℚ] (rationalGap l).SplittingField,
      σ (a:_)=(c:_) ∧ σ (b:_)=(d:_) := by
  let : Fact l.Prime := ⟨hl⟩
  let F := rationalGap l
  let K := F.SplittingField
  let : NumberField K := ⟨⟩
  let : Normal ℚ K := SplittingField.instNormal F
  let : Fact ((F.map (algebraMap ℚ K)).Splits) := ⟨SplittingField.splits F⟩
  have hi : Irreducible F := GapFamilies.irreducible_gap_rat hl.pos
  have hd : F.natDegree=l := by
    change (descPochhammer ℚ l-1).natDegree=l
    rw [natDegree_sub_eq_left_of_natDegree_lt (by simpa [descPochhammer_natDegree] using hl.pos),descPochhammer_natDegree]
  have hc := (card_rootSet_eq_natDegree hi.separable (SplittingField.splits F)).trans hd
  have hdiv : l∣Nat.card F.Gal := hd ▸ Gal.prime_degree_dvd_card hi (hd ▸ hl)
  have h₃ : 3∣Nat.card F.Gal := by
    rw [Gal.card_of_separable hi.separable]
    obtain ⟨s,m,hm⟩ := selected_form hl h
    apply three_dvd_number_field K s m
    have hs : ((descPochhammer ℚ l-1).map (algebraMap ℚ K)).Splits := SplittingField.splits F
    rw [Polynomial.map_sub,descPochhammer_map,Polynomial.map_one] at hs
    simpa only [← hm] using hs
  have hn : ¬Nat.card F.Gal∣l*(l-1) := by
    intro hh
    have ht := (Nat.prime_three.dvd_mul.mp (h₃.trans hh))
    unfold selected at h
    omega
  obtain ⟨σ,ha,hb⟩ := PrimeDifferences.two_transitive_of_order (Gal.galActionHom F K)
    (Gal.galActionHom_injective F K) hc hdiv hn hab hcd
  obtain ⟨τ,rfl⟩ := Gal.restrict_surjective F K σ
  exact ⟨τ,(Gal.galActionHom_restrict F K τ a).symm.trans (congrArg Subtype.val ha),
    (Gal.galActionHom_restrict F K τ b).symm.trans (congrArg Subtype.val hb)⟩

#print axioms selected_form
#print axioms root_pair_conjugate
end
end Erdos478.BinaryGap
