import Erdos478TranslatedGapRoots

/-! # An explicit nonzero resultant separating two short factorial collisions -/

namespace Erdos478.LocalSpacing
open Polynomial

noncomputable def gapResultant (r k s l : ℕ) : ℤ :=
  resultant (translatedGap ℤ r k) (translatedGap ℤ s l) k l

theorem map_translated (R : Type*) [CommRing R] (r k : ℕ) :
    (translatedGap ℤ r k).map (Int.castRingHom R)=translatedGap R r k := by
  simp [translatedGap]

theorem map_gapResultant (R : Type*) [CommRing R] (r k s l : ℕ) :
    (gapResultant r k s l:R)=resultant (translatedGap R r k) (translatedGap R s l) k l := by
  change Int.castRingHom R (resultant _ _ k l)=_
  rw [← resultant_map_map,map_translated,map_translated]

theorem gapResultant_ne {r k s l : ℕ} (hk : 0<k) (hl : 0<l) (h : (r,k)≠(s,l)) :
    gapResultant r k s l≠0 := by
  intro eq
  have z := map_gapResultant ℚ r k s l
  rw [eq,Int.cast_zero] at z
  apply resultant_ne_zero _ _ (translated_coprime hk hl h)
  simpa only [(translated_degree ℚ r hk).natDegree_eq,(translated_degree ℚ s hl).natDegree_eq] using z.symm

private theorem prod_norm_bound (m : Multiset ℂ) (B : ℝ) (hB : 0≤B) (h : ∀ x∈m,‖x‖≤B) :
    ‖m.prod‖≤B^m.card := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    rw [Multiset.prod_cons,norm_mul,Multiset.card_cons,pow_succ']
    exact mul_le_mul (h a (Multiset.mem_cons_self ..))
      (ih (fun x hx => h x (Multiset.mem_cons_of_mem hx))) (norm_nonneg _) hB

theorem gapResultant_bound {r k s l H : ℕ} (hk : 0<k) (hl : 0<l)
    (hkr : k≤r) (hls : l≤s) (hr : r≤H) (hs : s≤H) :
    (gapResultant r k s l).natAbs≤(H+2)^(k*l) := by
  let f := translatedGap ℂ r k
  let g := translatedGap ℂ s l
  have hf : f.IsMonicOfDegree k := translated_degree _ _ hk
  have hg : g.IsMonicOfDegree l := translated_degree _ _ hl
  have sf : f.Splits := IsAlgClosed.splits _
  have sg : g.Splits := IsAlgClosed.splits _
  let m := (f.roots ×ˢ g.roots).map (fun ij => ij.1-ij.2)
  have eqn : (gapResultant r k s l:ℂ)=m.prod := (map_gapResultant ..).trans (by
    simpa only [hf.natDegree_eq,hg.natDegree_eq] using resultant_eq_prod_roots_sub f g hf.monic hg.monic sf sg)
  have card : m.card=k*l := by
    rw [Multiset.card_map,Multiset.card_product,← sf.natDegree_eq_card_roots,
      ← sg.natDegree_eq_card_roots,hf.natDegree_eq,hg.natDegree_eq]
  have radius : ∀ x∈m,‖x‖≤(H:ℝ)+2 := by
    intro x hx
    obtain ⟨⟨z,w⟩,hz,rfl⟩ := Multiset.mem_map.mp hx
    obtain ⟨a,b⟩ := Multiset.mem_product.mp hz
    exact root_difference_bound hk hl hkr hls hr hs (isRoot_of_mem_roots a) (isRoot_of_mem_roots b)
  have bound := prod_norm_bound m _ (by positivity) radius
  rw [← eqn,Complex.norm_intCast,← Int.cast_abs,← Int.natCast_natAbs,card] at bound
  exact_mod_cast bound

theorem prime_dvd_resultant {p r k s l : ℕ} [Fact p.Prime] (hk : 0<k) (hl : 0<l)
    {x : ZMod p} (hf : (translatedGap (ZMod p) r k).IsRoot x)
    (hg : (translatedGap (ZMod p) s l).IsRoot x) : p ∣ (gapResultant r k s l).natAbs := by
  let f := translatedGap (ZMod p) r k
  let g := translatedGap (ZMod p) s l
  obtain ⟨u,v,_,_,hz⟩ := exists_mul_add_mul_eq_C_resultant f g
    (translated_degree _ _ hk).natDegree_eq.le (translated_degree _ _ hl).natDegree_eq.le (Or.inl hk.ne')
  have he := congrArg (eval x) hz
  change f.eval x=0 at hf
  change g.eval x=0 at hg
  simp only [eval_add,eval_mul,hf,hg,zero_mul,zero_add,eval_C] at he
  have z : (gapResultant r k s l:ZMod p)=0 := (map_gapResultant ..).trans he.symm
  exact Int.ofNat_dvd_left.mp ((CharP.intCast_eq_zero_iff _ p _).mp z)

#print axioms gapResultant
#print axioms map_translated
#print axioms map_gapResultant
#print axioms gapResultant_ne
#print axioms gapResultant_bound
#print axioms prime_dvd_resultant
end Erdos478.LocalSpacing
