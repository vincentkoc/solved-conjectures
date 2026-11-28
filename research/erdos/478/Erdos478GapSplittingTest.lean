import Erdos478SplittingFieldFactor
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Complete factorial-gap splitting in a progression

The test polynomial contains the prescribed gap polynomials and a
cyclotomic polynomial. Using a finite set of factors keeps it separable
even if the same factor is specified twice.
-/

namespace Erdos478.SplittingDensity
open Polynomial Finset Filter Topology RootMoments
open scoped Classical

noncomputable def gapPoly (k : ℕ) : ℤ[X] := descPochhammer ℤ k-1

theorem gap_degree {k : ℕ} (hk : 0<k) : (gapPoly k).IsMonicOfDegree k := by
  have h : (descPochhammer ℤ k).IsMonicOfDegree k :=
    ⟨descPochhammer_natDegree ℤ k,monic_descPochhammer ℤ k⟩
  simpa only [gapPoly,sub_eq_add_neg] using h.add_right (q := -(1:ℤ[X])) (by simpa using hk)

noncomputable def factors (m : ℕ) (S : Finset ℕ) :=
  insert (cyclotomic m ℤ) (S.image gapPoly)

noncomputable def test (m : ℕ) (S : Finset ℕ) := ∏ f ∈ factors m S, f

private theorem ingredients {m : ℕ} (hm : 0<m) {S : Finset ℕ} (hS : ∀ k∈S, 0<k)
    {f : ℤ[X]} (hf : f∈factors m S) : f.Monic ∧ Irreducible (f.map (Int.castRingHom ℚ)) := by
  rcases mem_insert.mp hf with rfl | h
  · exact ⟨cyclotomic.monic _ _,by rw [map_cyclotomic]; exact cyclotomic.irreducible_rat hm⟩
  · obtain ⟨k,hk,rfl⟩ := mem_image.mp h
    refine ⟨(gap_degree (hS k hk)).monic,?_⟩
    simpa [gapPoly] using GapFamilies.irreducible_gap_rat (hS k hk)

theorem test_properties {m : ℕ} (hm : 0<m) {S : Finset ℕ} (hS : ∀ k∈S, 0<k) :
    (test m S).Monic ∧ 0<(test m S).natDegree ∧ ((test m S).map (Int.castRingHom ℚ)).Separable := by
  classical
  have hmon := fun f (h:f∈factors m S) => (ingredients hm hS h).1
  refine ⟨monic_prod_of_monic _ _ hmon,?_,?_⟩
  · have hd : cyclotomic m ℤ ∣ test m S := Finset.dvd_prod_of_mem _ (mem_insert_self ..)
    exact (natDegree_cyclotomic m ℤ ▸ Nat.totient_pos.mpr hm).trans_le
      (natDegree_le_of_dvd hd (monic_prod_of_monic _ _ hmon).ne_zero)
  · unfold test
    rw [Polynomial.map_prod]
    apply separable_prod'
    · intro f hf g hg hfg
      obtain ⟨fm,fi⟩ := ingredients hm hS hf
      obtain ⟨gm,gi⟩ := ingredients hm hS hg
      apply fi.coprime_iff_not_dvd.mpr
      intro hd
      have hass := (fi.associated_of_dvd gi hd)
      exact hfg (Polynomial.map_injective (Int.castRingHom ℚ) (by exact Int.cast_injective)
        (eq_of_monic_of_associated (fm.map _) (gm.map _) hass))
    · exact fun f hf => (ingredients hm hS hf).2.separable

private theorem cyclo_iff {m p : ℕ} (hm : 0<m) (hp : m<p) [hpr : Fact p.Prime] :
    ((cyclotomic m ℤ).map (Int.castRingHom (ZMod p))).Splits ↔ m ∣ p-1 := by
  let : NeZero (m : ZMod p) := ⟨fun h => Nat.not_dvd_of_pos_of_lt hm hp
    ((CharP.cast_eq_zero_iff (ZMod p) p m).mp h)⟩
  rw [map_cyclotomic]
  constructor
  · intro hs
    obtain ⟨z,hz⟩ := hs.exists_eval_eq_zero (degree_ne_of_natDegree_ne (by
      rw [natDegree_cyclotomic]; exact (Nat.totient_pos.mpr hm).ne'))
    have hroot := isRoot_cyclotomic_iff.mp (show (cyclotomic m (ZMod p)).IsRoot z from hz)
    have hne : z≠0 := by
      rintro rfl
      simpa [zero_pow hm.ne'] using hroot.pow_eq_one
    exact hroot.dvd_of_pow_eq_one _ (ZMod.pow_card_sub_one_eq_one hne)
  · intro hd
    have hpos := hpr.out.one_lt
    have hs := GaloisField.splits_zmod_X_pow_sub_X p
    have he : ((X: (ZMod p)[X])^(p-1)-1)*X=X^p-X := by
      rw [sub_mul,one_mul,← pow_succ,Nat.sub_add_cancel (by omega)]
    rw [← he] at hs
    have hn : ((X: (ZMod p)[X])^(p-1)-1)≠0 := (monic_X_pow_sub_C 1 (by omega : p-1≠0)).ne_zero
    have hdiv := (cyclotomic.dvd_X_pow_sub_one m (ZMod p)).trans (dvd_pow_sub_one_of_dvd hd)
    exact (hs.of_dvd (mul_ne_zero hn X_ne_zero) (dvd_mul_right ..)).of_dvd hn hdiv

def complete (m : ℕ) (S : Finset ℕ) (p : ℕ) : Prop :=
  m ∣ p-1 ∧ ∀ k∈S, ((gapPoly k).map (Int.castRingHom (ZMod p))).Splits

theorem test_iff {m p : ℕ} (hm : 0<m) (hp : m<p) [Fact p.Prime]
    {S : Finset ℕ} (hS : ∀ k∈S, 0<k) :
    ((test m S).map (Int.castRingHom (ZMod p))).Splits ↔ complete m S p := by
  classical
  unfold test complete
  rw [Polynomial.map_prod,splits_prod_iff (fun f hf => ((ingredients hm hS hf).1.map _).ne_zero)]
  simp only [factors,Finset.forall_mem_insert,Finset.forall_mem_image,cyclo_iff hm hp]

#print axioms test_properties
#print axioms test_iff
end Erdos478.SplittingDensity
