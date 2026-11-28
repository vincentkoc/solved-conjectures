import Erdos478JointCountInterpolation
import Erdos478FactorialPatternLaw

/-!
# Exact densities for the factorial collision counts at prescribed gaps

For every finite list of requested gap counts in a prime progression, finite
root-count interpolation yields a rational density. The same event includes
the sum of these counts as a lower bound on the missing nonzero residues.
-/

namespace Erdos478.CollisionLaw
open Finset Polynomial Filter Topology SplittingDensity RootMoments GapDensity
open scoped Classical
noncomputable section

def requests (m : ℕ) (S : Finset ℕ) (c : ℕ → ℕ) : List Test :=
  ⟨cyclotomic m ℤ,m.totient⟩ :: (S.sort (· ≤ ·)).map fun k => ⟨gapPoly k,c k⟩

def exactEvent (m : ℕ) (S : Finset ℕ) (c : ℕ → ℕ) (p : ℕ) : Prop :=
  m ∣ p-1 ∧ (∀ k∈S, (endpoints k p).card=c k) ∧
    ((Ico 1 p).image (fun j => j.factorial % p)).card + ∑ k∈S, c k ≤ p-1

private theorem cyclo_good {m : ℕ} (hm : 0<m) : Good (cyclotomic m ℤ) :=
  ⟨cyclotomic.monic ..,natDegree_cyclotomic m ℤ ▸ Nat.totient_pos.mpr hm,
    by rw [map_cyclotomic]; exact (cyclotomic.irreducible_rat hm).separable⟩

private theorem gap_good {k : ℕ} (hk : 2≤k) : Good (gapPoly k) := by
  have h := gap_degree (by omega : 0<k)
  exact ⟨h.monic,by rw [h.natDegree_eq]; omega,by simpa [gapPoly] using
    (GapFamilies.irreducible_gap_rat (by omega : 0<k)).separable⟩

private theorem agree {m : ℕ} (hm : 0<m) (S : Finset ℕ) (hS : ∀ k∈S, 2≤k) (c : ℕ → ℕ) :
    ∃ B, ∀ p>B, p.Prime → (exactEvent m S c p ↔ hasCounts (requests m S c) p) := by
  let F := cyclotomic m ℤ
  let H := GapFamilies.family ℤ S
  let D := (F.resultant F.derivative).natAbs
  let E := (H.resultant H.derivative).natAbs
  refine ⟨max (max m D) (max (S.sup cutoff) E),?_⟩
  intro p hp hpr
  let : Fact p.Prime := ⟨hpr⟩
  have hmD : max m D<p := (le_max_left ..).trans_lt hp
  have hSE : max (S.sup cutoff) E<p := (le_max_right ..).trans_lt hp
  have hz := cyclo_good hm
  have sp := GapFamilies.separable_mod_above_resultant F hz.2.1.ne' hz.2.2 ((le_max_right ..).trans_lt hmD)
  let j := Int.castRingHom (ZMod p)
  have hc : RootMoments.roots F p=(m.totient : ℝ) ↔ m∣p-1 := by
    have ht := test_iff (S:=∅) hm ((le_max_left ..).trans_lt hmD) (by simp)
    have he : (F.map j).Splits ↔ m∣p-1 := by simpa [F,test,factors,complete,j] using ht
    have hd : (F.map j).natDegree=m.totient := ((cyclotomic.monic ..).natDegree_map j).trans (natDegree_cyclotomic m ℤ)
    rw [count_roots F hz.1 p sp,Nat.cast_inj,← hd,← splits_iff_card_roots]
    exact he
  have hk (k) (hk:k∈S) : cutoff k<p := (le_sup hk).trans_lt ((le_max_left ..).trans_lt hSE)
  have hgap (k) (hkS:k∈S) : RootMoments.roots (gapPoly k) p=((endpoints k p).card:ℝ) := by
    have hg := gap_good (hS k hkS)
    have hs := GapFamilies.separable_mod_above_resultant (gapPoly k) hg.2.1.ne' hg.2.2
      ((le_max_right ..).trans_lt (hk k hkS))
    rw [count_roots _ hg.1 p hs,endpoint_count (hS k hkS) (hk k hkS)]
  have hh : hasCounts (requests m S c) p ↔ m∣p-1 ∧ ∀ k∈S, (endpoints k p).card=c k := by
    simp only [hasCounts,requests,List.forall_mem_cons,List.forall_mem_map,Finset.mem_sort]
    apply and_congr hc
    constructor <;> intro h k hkS
    · exact_mod_cast (hgap k hkS).symm.trans (h k hkS)
    · rw [hgap k hkS,h k hkS]
  rw [hh]
  refine ⟨fun h => ⟨h.1,h.2.1⟩,?_⟩
  rintro ⟨hmod,h⟩
  refine ⟨hmod,h,?_⟩
  have u := GapFamilies.card_add_sum_gap_roots S hS (p:=p) ((le_max_right ..).trans_lt hSE)
  have he : (∑ k∈S, (descPochhammer (ZMod p) k-1).roots.card)=∑ k∈S, c k := by
    apply sum_congr rfl
    intro k hkS
    simpa [gapPoly] using (endpoint_count (hS k hkS) (hk k hkS)).symm.trans (h k hkS)
  rwa [he] at u

/-- The natural and prime-Mertens averaging laws have the same rational value. -/
theorem exact_count_mean (A : PrimeAverage) {m : ℕ} (hm : 0<m) (S : Finset ℕ)
    (hS : ∀ k∈S, 2≤k) (c : ℕ → ℕ) :
    Tendsto (fun X => A.avg X (event (exactEvent m S c))) atTop
      (𝓝 (jointDensity (requests m S c) : ℝ)) := by
  obtain ⟨B,hB⟩ := agree hm S hS c
  apply mean_of_change A B (b:=event (hasCounts (requests m S c)))
    (fun p hp hpr => by simp only [event,hB p hp hpr])
  apply joint_mean
  simp only [requests,List.forall_mem_cons,List.forall_mem_map,Finset.mem_sort]
  exact ⟨cyclo_good hm,fun k hk => gap_good (hS k hk)⟩

theorem exact_count_of_pit (pit : DegreeOnePrimeIdealTheorem) {m : ℕ} (hm : 0<m)
    (S : Finset ℕ) (hS : ∀ k∈S, 2≤k) (c : ℕ → ℕ) :
    Tendsto (fun X => (((Nat.primesLE X).filter (exactEvent m S c)).card : ℝ) /
      (Nat.primesLE X).card) atTop (𝓝 (jointDensity (requests m S c) : ℝ)) := by
  apply (exact_count_mean (countingAverage pit) hm S hS c).congr
  intro X
  change (Nat.primeCounting X : ℝ)⁻¹*(∑ p∈Nat.primesLE X, if exactEvent m S c p then 1 else 0)=_
  rw [← Nat.primesLE_card_eq_primeCounting,div_eq_inv_mul]
  congr 1
  rw [card_filter]
  push_cast
  rfl

#print axioms exact_count_mean
#print axioms exact_count_of_pit
end
end Erdos478.CollisionLaw
