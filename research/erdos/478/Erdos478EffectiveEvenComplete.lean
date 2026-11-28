import Erdos478PairedSplittingPrime
import Erdos478DisjointGapFamilies

/-!
# Effective complete splitting at every prescribed even length

For distinct lengths twice the positive integers in a finite list,
specializing one representative per reflected pair yields all the
collision endpoints. The prime selection can avoid any given integer.
-/

namespace Erdos478.EffectiveResolvent
open Polynomial Finset

noncomputable def evenGapProduct {I : Type*} [Fintype I] (R : Type*) [CommRing R] (r : I → ℕ) :
    R[X] := ∏ i, (descPochhammer R (2*r i)-1)

private theorem gap_degree (R : Type*) [CommRing R] [IsDomain R] {k : ℕ} (hk : 0<k) :
    (descPochhammer R k-1).IsMonicOfDegree k := by
  have h : (descPochhammer R k).IsMonicOfDegree k := ⟨descPochhammer_natDegree R k,monic_descPochhammer R k⟩
  simpa [sub_eq_add_neg] using h.add_right (q := -(1:R[X])) (by simpa using hk)

private theorem product_degree {I : Type*} [Fintype I] (r : I → ℕ) (hpos : ∀ i, 0<r i)
    (R : Type*) [CommRing R] [IsDomain R] : (evenGapProduct R r).IsMonicOfDegree (2*∑ i, r i) := by
  have hm (i) := gap_degree R (k := 2*r i) (by have := hpos i; omega)
  constructor
  · rw [evenGapProduct,natDegree_prod_of_monic _ _ (fun i _ => (hm i).monic),mul_sum]
    exact sum_congr rfl fun i _ => (hm i).natDegree_eq
  · exact monic_prod_of_monic _ _ (fun i _ => (hm i).monic)

private theorem product_map {I : Type*} [Fintype I] (r : I → ℕ) {R K : Type*}
    [CommRing R] [CommRing K] (j : R →+* K) :
    (evenGapProduct R r).map j = evenGapProduct K r := by
  simp [evenGapProduct,Polynomial.map_prod,Polynomial.map_sub,descPochhammer_map]

/-- All roots at the given lengths give distinct losses from the upstream
factorial image. The Schur degree is at most the product of the lengths,
each raised to half that length. -/
theorem effective_even_complete {I : Type} [Fintype I] [Nonempty I] (r : I ↪ ℕ)
    (hpos : ∀ i, 0<r i) (U C : ℕ) (hU : ∀ i, 2*r i+1 ≤ U) (hC : 0<C)
    (method : RootPrimeBound) :
    let N := ∑ i, r i
    let D := ∏ i, (2*r i)^(r i)
    let V := wordBound N D U
    ∃ e ≤ D, ∃ p ≤ method.bound e V ((C*(2*U)^((2*N)^2))*(2*V)^(D^2)),
      p.Prime ∧ ¬p ∣ C ∧ (evenGapProduct (ZMod p) r).Splits ∧ (evenGapProduct (ZMod p) r).Separable ∧
      ((Ico 1 p).image (fun i => i.factorial % p)).card + 2*N ≤ p-1 := by
  classical
  let N := ∑ i, r i
  let G := evenGapProduct ℤ r
  let f (i : I) := descPochhammer ℤ (2*r i)-1
  let k : I ↪ ℕ := ⟨fun i => 2*r i,fun i j h => r.injective (by dsimp at h; omega)⟩
  have hk (i : I) : 0<2*r i := by have := hpos i; omega
  have hN : 0<N := Finset.sum_pos (fun i _ => hpos i) univ_nonempty
  have hU' : 0<U := by have := hU (Classical.arbitrary I); omega
  have hs : (evenGapProduct ℂ r).Separable := by
    have h := GapFamilies.separable_gap_family (univ.map k) (by
      intro m hm
      obtain ⟨i,_,rfl⟩ := mem_map.mp hm
      exact hk i)
    have hh := h.map (f := algebraMap ℚ ℂ)
    simpa only [evenGapProduct,Finset.prod_map,show ∀ i, k i = 2*r i from fun _ => rfl,Polynomial.map_prod,
      Polynomial.map_sub,descPochhammer_map,Polynomial.map_one] using hh
  have hg := product_degree r hpos ℤ
  have hh : (G.map (Int.castRingHom ℂ)).Separable := (product_map r (Int.castRingHom ℂ)).symm ▸ hs
  obtain ⟨g,hg'⟩ := enumerate_roots _ (hg.monic.map _) (IsAlgClosed.splits _) hh
    ((hg.monic.natDegree_map _).trans hg.natDegree_eq)
  have norm_root (i : I) (x : ℂ) (h : (descPochhammer ℂ (2*r i)-1).IsRoot x) : ‖x‖ ≤ U :=
    (gap_root_norm (hk i) h).trans (by exact_mod_cast hU i)
  have gu (l) : ‖g l‖ ≤ U := by
    have hz : (G.map (Int.castRingHom ℂ)).IsRoot (g l) := by
      rw [hg']; simp only [IsRoot.def,eval_prod,eval_sub,eval_X,eval_C]
      exact prod_eq_zero (mem_univ l) (sub_self _)
    change ((evenGapProduct ℤ r).map _).eval (g l) = 0 at hz
    rw [product_map,evenGapProduct,eval_prod,Finset.prod_eq_zero_iff] at hz
    obtain ⟨i,_,hi⟩ := hz
    exact norm_root i _ hi
  obtain ⟨hb,hb'⟩ := bad_bound G g hg' U hU' gu
  have hsingle (i : I) := enumerate_roots (descPochhammer ℂ (2*r i)-1) (gap_degree ℂ (hk i)).monic
    (IsAlgClosed.splits _) (hs.of_dvd (Finset.dvd_prod_of_mem _ (mem_univ i))) (gap_degree ℂ (hk i)).natDegree_eq
  choose a ha using hsingle
  have hu (i l) : ‖a i l‖ ≤ U := by
    apply norm_root i
    rw [ha]; simp only [IsRoot.def,eval_prod,eval_sub,eval_X,eval_C]
    exact prod_eq_zero (mem_univ l) (sub_self _)
  choose v hv using fun i => paired_even_gap_indices (r i) (by norm_num : (2:ℂ)≠0) (a i) (ha i)
  have hf (i) : (f i).map (Int.castRingHom ℂ) = ∏ l, (X-Polynomial.C (a i l)) := by simpa [f] using ha i
  have hcard : Fintype.card (Σ i, Fin (r i)) = N := by simp [N,Fintype.card_sigma]
  obtain ⟨e,he,p,hp,hprime,havoid,hsplit⟩ := paired_splitting_prime r (hcard ▸ hN) f a hf v
    (fun i => (2*r i:ℕ)-1) (fun i l => by simpa using hv i l) method U (C*(bad G).natAbs) hU'
    (Nat.mul_pos hC hb) hu
  let : Fact p.Prime := ⟨hprime⟩
  have simple : (evenGapProduct (ZMod p) r).Separable := by
    rw [← product_map r (Int.castRingHom (ZMod p))]
    exact separable_at_good_prime G (by have := hg.natDegree_eq; change G.natDegree = 2*N at this; omega) p
      (fun h => havoid (dvd_mul_of_dvd_right h C))
  have split : (evenGapProduct (ZMod p) r).Splits := Splits.prod (fun i _ => by simpa [f] using hsplit i)
  have count : ((Ico 1 p).image (fun i => i.factorial % p)).card +
      (evenGapProduct (ZMod p) r).roots.toFinset.card ≤ p-1 := by
    apply FallingGap.card_add_gap_endpoints
    intro z hz
    have hh := isRoot_of_mem_roots (Multiset.mem_toFinset.mp hz)
    change (evenGapProduct (ZMod p) r).eval z = 0 at hh
    rw [evenGapProduct,eval_prod,Finset.prod_eq_zero_iff] at hh
    obtain ⟨i,_,hi⟩ := hh
    exact ⟨2*r i,by have := hpos i; omega,hi⟩
  rw [Multiset.toFinset_card_of_nodup (nodup_roots simple),← split.natDegree_eq_card_roots,
    (product_degree r hpos (ZMod p)).natDegree_eq] at count
  rw [hcard] at hp
  refine ⟨e,he,p,hp.trans (method.mono _ _ ?_),hprime,fun h => havoid (dvd_mul_of_dvd_left h _),split,simple,count⟩
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by simpa [N] using hb'))

#print axioms effective_even_complete

end Erdos478.EffectiveResolvent
