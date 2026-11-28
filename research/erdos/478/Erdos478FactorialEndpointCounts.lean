import Erdos478GapSplittingTest

/-!
# Counts of actual pairs of factorial indices

For a fixed separation, distinct modular roots coincide with the upper
indices of repeated factorial residues at that separation, away from a
finite initial segment. Both indices lie in the pinned interval.
-/

namespace Erdos478.SplittingDensity
open Polynomial Finset GapFamilies
open scoped Classical

def endpoints (k p : ℕ) : Finset ℕ :=
  (Ico (k+1) p).filter fun j => (j-k).factorial % p=j.factorial % p

private theorem root_of_endpoint {k p j : ℕ} [hpr : Fact p.Prime] (h : j∈endpoints k p) :
    ((gapPoly k).map (Int.castRingHom (ZMod p))).IsRoot (j:ZMod p) := by
  obtain ⟨hj,he⟩ := mem_filter.mp h
  obtain ⟨hl,hu⟩ := mem_Ico.mp hj
  have he' := (ZMod.natCast_eq_natCast_iff' _ _ _).mpr he
  have hn : ((j-k).factorial : ZMod p)≠0 := by
    rw [Ne,CharP.cast_eq_zero_iff (ZMod p) p]
    intro hd
    have := hpr.out.dvd_factorial.mp hd
    omega
  have hprod := congrArg (fun n : ℕ => (n:ZMod p)) (Nat.factorial_mul_descFactorial (by omega : k≤j))
  simp only [Nat.cast_mul] at hprod
  have hd : (j.descFactorial k : ZMod p)=1 := by
    apply mul_left_cancel₀ hn
    simpa only [mul_one] using hprod.trans he'.symm
  simpa [gapPoly,IsRoot,descPochhammer_eval_eq_descFactorial,sub_eq_zero] using hd

private theorem endpoint_of_root {k p : ℕ} [hpr : Fact p.Prime] (hk : 2≤k) (hp : k.factorial<p)
    {x : ZMod p} (hx : ((gapPoly k).map (Int.castRingHom (ZMod p))).IsRoot x) :
    x.val∈endpoints k p := by
  have hr : (FallingGap.gap (ZMod p) k).IsRoot x := by simpa [gapPoly,FallingGap.gap] using hx
  obtain ⟨hle,he⟩ := FallingGap.endpoints_of_root hr
  have hlt : k<x.val := by
    apply lt_of_le_of_ne hle
    rintro heq
    rw [← heq,Nat.sub_self,Nat.factorial_zero,Nat.mod_eq_of_lt hpr.out.one_lt,
      Nat.mod_eq_of_lt hp] at he
    exact (Nat.one_lt_factorial.mpr hk).ne he
  exact mem_filter.mpr ⟨mem_Ico.mpr ⟨hlt,x.val_lt⟩,he⟩

noncomputable def cutoff (k : ℕ) := max k.factorial ((gapPoly k).resultant (gapPoly k).derivative).natAbs

theorem endpoint_count {k p : ℕ} [Fact p.Prime] (hk : 2≤k) (hp : cutoff k<p) :
    (endpoints k p).card=((gapPoly k).map (Int.castRingHom (ZMod p))).roots.card := by
  classical
  let F := (gapPoly k).map (Int.castRingHom (ZMod p))
  have hm := gap_degree (by omega : 0<k)
  have hne : F≠0 := (hm.monic.map _).ne_zero
  have hsep : F.Separable := separable_mod_above_resultant (gapPoly k) (by rw [hm.natDegree_eq]; omega)
    (by simpa [gapPoly] using (irreducible_gap_rat (by omega : 0<k)).separable) ((le_max_right ..).trans_lt hp)
  let e : ZMod p ↪ ℕ := ⟨ZMod.val,ZMod.val_injective p⟩
  have he : F.roots.toFinset.map e=endpoints k p := by
    ext j
    constructor
    · rintro hj
      obtain ⟨x,hx,rfl⟩ := mem_map.mp hj
      exact endpoint_of_root hk ((le_max_left ..).trans_lt hp) ((mem_roots hne).mp (Multiset.mem_toFinset.mp hx))
    · intro hj
      have hj' := (mem_Ico.mp (mem_filter.mp hj).1).2
      exact mem_map.mpr ⟨(j:ZMod p),Multiset.mem_toFinset.mpr ((mem_roots hne).mpr (root_of_endpoint hj)),
        by change (j:ZMod p).val=j; rw [ZMod.val_natCast,Nat.mod_eq_of_lt hj']⟩
  change (endpoints k p).card=F.roots.card
  rw [← he,card_map,Multiset.toFinset_card_of_nodup (nodup_roots hsep)]

theorem saturated_iff {k p : ℕ} [Fact p.Prime] (hk : 2≤k) (hp : cutoff k<p) :
    ((gapPoly k).map (Int.castRingHom (ZMod p))).Splits ↔ (endpoints k p).card=k := by
  rw [endpoint_count hk hp,splits_iff_card_roots]
  have hm := gap_degree (by omega : 0<k)
  rw [hm.monic.natDegree_map,hm.natDegree_eq]

theorem endpoint_bound {k p : ℕ} [Fact p.Prime] (hk : 2≤k) (hp : cutoff k<p) :
    (endpoints k p).card≤k := by
  have hm := gap_degree (by omega : 0<k)
  rw [endpoint_count hk hp]
  exact (card_roots' _).trans_eq ((hm.monic.natDegree_map (Int.castRingHom (ZMod p))).trans hm.natDegree_eq)

#print axioms endpoint_count
#print axioms saturated_iff
end Erdos478.SplittingDensity
