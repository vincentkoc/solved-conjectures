import Erdos478MixedPolynomialMoments
import Erdos478GapPatternMeans

/-!
# Interpolation of joint polynomial root counts

For a list of tests, expand products of shifted counts in mixed moments.
All coefficients are integers until the final Lagrange normalization.
-/

namespace Erdos478.CollisionLaw
noncomputable section
open Filter Topology Polynomial RootMoments
open scoped Classical

def shifted (qs : List (ℤ[X] × ℕ)) (p : ℕ) : ℝ :=
  (qs.map fun q => RootMoments.roots q.1 p-q.2).prod

def shiftedMoment (fs : List ℤ[X]) : List (ℤ[X] × ℕ) → ℤ
  | [] => moment fs
  | (f,j)::qs => shiftedMoment (f::fs) qs - (j:ℤ)*shiftedMoment fs qs

private theorem shifted_mean (A : PrimeAverage) (qs : List (ℤ[X] × ℕ))
    (hg : ∀ q∈qs, Good q.1) (fs : List ℤ[X]) (hf : ∀ f∈fs, Good f) :
    Tendsto (fun X => A.avg X (fun p => productRoots fs p * shifted qs p)) atTop
      (𝓝 (shiftedMoment fs qs : ℝ)) := by
  induction qs generalizing fs with
  | nil => simpa [shifted,shiftedMoment] using mixed_root_mean A fs hf
  | cons q qs ih =>
    rcases q with ⟨f,j⟩
    have ht (q) (hq:q∈qs) := hg q (List.mem_cons_of_mem _ hq)
    have H := ih ht (f::fs) (by simpa using And.intro (hg _ List.mem_cons_self) hf)
    have I := (ih ht fs hf).const_mul (j:ℝ)
    have he : (fun p => productRoots fs p * shifted ((f,j)::qs) p) =
        (fun p => productRoots (f::fs) p * shifted qs p) -
        (j:ℝ) • (fun p => productRoots fs p * shifted qs p) := by
      funext p
      simp [productRoots,shifted]
      ring
    simpa only [he,map_sub,map_smul,smul_eq_mul,shiftedMoment,Int.cast_sub,Int.cast_mul,
      Int.cast_natCast] using H.sub I

structure Test where
  poly : ℤ[X]
  count : ℕ

def except (t : Test) := (List.range (t.poly.natDegree+1)).filter (· ≠ t.count)
def shifts (ts : List Test) := ts.flatMap fun t => (except t).map fun (j : ℕ) => (t.poly,j)
def denominator (ts : List Test) : ℤ :=
  (ts.map fun t => ((except t).map fun (j : ℕ) => (t.count:ℤ)-j).prod).prod

def jointDensity (ts : List Test) : ℚ := (shiftedMoment [] (shifts ts) : ℚ) / denominator ts

def hasCounts (ts : List Test) (p : ℕ) : Prop :=
  ∀ t∈ts, RootMoments.roots t.poly p=t.count

theorem denominator_ne_zero (ts : List Test) : denominator ts ≠ 0 := by
  classical
  apply List.prod_ne_zero
  simp only [List.mem_map,not_exists,not_and]
  intro t _
  apply List.prod_ne_zero
  simp only [List.mem_map,not_exists,not_and]
  intro j hj
  have h : j ≠ t.count := of_decide_eq_true (List.mem_filter.mp hj).2
  exact sub_ne_zero.mpr (by exact_mod_cast h.symm)

private theorem test_value (t : Test) (n : ℕ) (hn : n≤t.poly.natDegree) :
    ((except t).map fun (j : ℕ) => (n:ℝ)-j).prod =
      if n=t.count then ((((except t).map fun (j : ℕ) => (t.count:ℤ)-j).prod : ℤ) : ℝ) else 0 := by
  classical
  by_cases he : n=t.count
  · subst n
    simp [Int.cast_list_prod,Function.comp_def]
  · rw [if_neg he,List.prod_eq_zero_iff]
    exact List.mem_map.mpr ⟨n,List.mem_filter.mpr ⟨List.mem_range.mpr (show n<t.poly.natDegree+1 by omega),by simpa using he⟩,sub_self _⟩

/-- Lagrange interpolation on any vector of bounded integral counts. -/
theorem interpolation_at (value : ℤ[X] → ℝ) (ts : List Test)
    (bound : ∀ t∈ts, ∃ n≤t.poly.natDegree, value t.poly=(n : ℝ)) :
    ((shifts ts).map fun q => value q.1-q.2).prod =
      if ∀ t∈ts, value t.poly=(t.count : ℝ) then (denominator ts : ℝ) else 0 := by
  classical
  induction ts with
  | nil => simp [shifts,denominator]
  | cons t ts ih =>
    obtain ⟨n,hn,hv⟩ := bound t List.mem_cons_self
    have ht := ih (fun u hu => bound u (List.mem_cons_of_mem _ hu))
    have head := test_value t n hn
    rw [show shifts (t::ts)=((except t).map fun j => (t.poly,j))++shifts ts from rfl]
    simp only [List.map_append,List.prod_append,List.map_map,Function.comp_def,hv,ht,head,
      List.forall_mem_cons,Nat.cast_inj,denominator,List.map_cons,List.prod_cons,Int.cast_mul]
    by_cases h : n=t.count <;> by_cases hts : ∀ u∈ts, value u.poly=(u.count : ℝ) <;> simp [h,hts]

private theorem interpolation (ts : List Test) (p : ℕ)
    (bound : ∀ t∈ts, Nat.card (RootPairs.solutions t.poly (ZMod p))≤t.poly.natDegree) :
    shifted (shifts ts) p = if hasCounts ts p then (denominator ts : ℝ) else 0 := by
  have h := interpolation_at (fun f => RootMoments.roots f p) ts (fun t ht => ⟨_,bound t ht,rfl⟩)
  unfold shifted hasCounts
  rw [h]
  split_ifs <;> rfl

private theorem shifts_good (ts : List Test) (hg : ∀ t∈ts, Good t.poly) :
    ∀ q∈shifts ts, Good q.1 := by
  intro q h
  obtain ⟨t,ht,hs⟩ := List.mem_flatMap.mp h
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hs
  exact hg t ht

/-- Finite Lagrange interpolation gives the rational density for arbitrary
exact root counts. The list may prescribe zero roots or repeat a polynomial. -/
theorem joint_mean (A : PrimeAverage) (ts : List Test) (hg : ∀ t∈ts, Good t.poly) :
    Tendsto (fun X => A.avg X (SplittingDensity.event (hasCounts ts))) atTop
      (𝓝 (jointDensity ts : ℝ)) := by
  classical
  let D (t : Test) := (t.poly.resultant t.poly.derivative).natAbs
  let B := ts.toFinset.sup D
  have hd : (denominator ts : ℝ)≠0 := by exact_mod_cast denominator_ne_zero ts
  have hlim := (shifted_mean A (shifts ts) (shifts_good ts hg) [] (by simp)).const_mul (denominator ts : ℝ)⁻¹
  apply mean_of_change A (b:=(denominator ts : ℝ)⁻¹ • shifted (shifts ts)) B
  · intro p hp hpr
    let : Fact p.Prime := ⟨hpr⟩
    have bound (t) (ht:t∈ts) : Nat.card (RootPairs.solutions t.poly (ZMod p))≤t.poly.natDegree := by
      obtain ⟨hm,hn,hs⟩ := hg t ht
      have sp := GapFamilies.separable_mod_above_resultant t.poly hn.ne' hs
        (lt_of_le_of_lt (Finset.le_sup (f:=D) (List.mem_toFinset.mpr ht)) hp)
      have eq := count_roots t.poly hm p sp
      have h := (card_roots' (t.poly.map (Int.castRingHom (ZMod p)))).trans_eq (hm.natDegree_map _)
      apply (Nat.cast_le (α:=ℝ)).mp
      change RootMoments.roots t.poly p ≤ _
      rw [eq]
      exact_mod_cast h
    rw [Pi.smul_apply,smul_eq_mul,interpolation ts p bound]
    by_cases h : hasCounts ts p <;> simp [SplittingDensity.event,h,hd]
  · simpa [productRoots,map_smul,jointDensity,div_eq_inv_mul] using hlim

#print axioms interpolation_at
#print axioms denominator_ne_zero
#print axioms joint_mean
#print axioms shifted_mean
end
end Erdos478.CollisionLaw
