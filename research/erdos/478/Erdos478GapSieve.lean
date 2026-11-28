import Erdos478RootProduct
import Erdos478GapVariance

/-!
# A finite sieve for factorial collisions

At each prime p, retain a gap length ℓ with weight r_ℓ(p)/ℓ, where r_ℓ
counts roots of the falling-factorial polynomial. The mean of each atom
of this finite product distribution equals the corresponding independent
Bernoulli mass with parameters 1/ℓ.
-/

namespace Erdos478.GapSieve
noncomputable section
open Finset Filter Topology RootMoments GapVariance

def retain (i : Nat.Primes) : ℕ → ℝ := weight i • observation i

/-- Product weight for selecting all of s and omitting all of t. -/
def pattern {R : Type*} [CommRing R] (q : Nat.Primes → R) (s t : Finset Nat.Primes) : R :=
  (∏ i ∈ s, q i) * ∏ j ∈ t, (1-q j)

private theorem retain_range (i : Nat.Primes) {p : ℕ} (hp : p.Prime) :
    0 ≤ retain i p ∧ retain i p ≤ 1 := by
  change 0 ≤ (1/(i.val:ℝ))*observation i p ∧ (1/(i.val:ℝ))*observation i p ≤ 1
  rw [one_div,inv_mul_eq_div]
  have hi : (0:ℝ) < i.val := by exact_mod_cast i.property.pos
  exact ⟨div_nonneg (Nat.cast_nonneg _) hi.le,(div_le_one hi).mpr (bound i p hp)⟩

private theorem all_retained (A : PrimeAverage) (s : Finset Nat.Primes) :
    Tendsto (fun X => A.avg X (∏ i ∈ s, retain i)) atTop (𝓝 (∏ i ∈ s, weight i)) := by
  have h := RootProduct.mixed_mean A (fun i : Nat.Primes => gap i.val) s
    (fun i _ => (gap_degree i).monic) (fun i _ => gap_irr i) (fun i _ j _ hij => by
      rw [(gap_degree i).natDegree_eq,(gap_degree j).natDegree_eq]
      exact (Nat.coprime_primes i.property j.property).mpr (fun he => hij (Subtype.ext he)))
  have he : (∏ i ∈ s, retain i) = (∏ i ∈ s, weight i) • (∏ i ∈ s, observation i) := by
    ext p
    simp [retain,prod_apply,prod_mul_distrib]
  simp only [he,map_smul,smul_eq_mul]
  simpa [observation] using (tendsto_const_nhds (x := ∏ i ∈ s, weight i)).mul h

private theorem pattern_insert {R : Type*} [CommRing R] (q : Nat.Primes → R)
    (s t : Finset Nat.Primes) {j : Nat.Primes} (hs : j ∉ s) (ht : j ∉ t) :
    pattern q s (insert j t) = pattern q s t - pattern q (insert j s) t := by
  simp [pattern,prod_insert,hs,ht]
  ring

/-- Disjoint prescribed successes and failures for the auxiliary weights
have the exact product limit. -/
theorem pattern_mean (A : PrimeAverage) (s t : Finset Nat.Primes) (hst : Disjoint s t) :
    Tendsto (fun X => A.avg X (pattern retain s t)) atTop (𝓝 (pattern weight s t)) := by
  classical
  induction t using Finset.induction_on generalizing s with
  | empty => simpa [pattern] using all_retained A s
  | @insert j t hj ih =>
    have hs : j ∉ s := by
      intro hh
      exact disjoint_left.mp hst hh (mem_insert_self ..)
    have ht : Disjoint s t := hst.mono_right (subset_insert ..)
    have hst' : Disjoint (insert j s) t := disjoint_insert_left.mpr ⟨hj,ht⟩
    simp only [pattern_insert _ _ _ hs hj,map_sub]
    exact (ih s ht).sub (ih (insert j s) hst')

/-- A factorial repetition with both endpoints in the upstream interval. -/
def HasGap (p k : ℕ) : Prop :=
  ∃ j ∈ Ico 1 p, j+k ∈ Ico 1 p ∧ j.factorial % p = (j+k).factorial % p

/-- Gap lengths actually witnessed by two factorials. -/
def hits (s : Finset Nat.Primes) (p : ℕ) : Finset Nat.Primes := by
  classical exact s.filter (fun i => HasGap p i.val)

private theorem hasGap_of_retain {i : Nat.Primes} {p : ℕ} (hp : p.Prime)
    (hB : i.val.factorial < p) (h : retain i p ≠ 0) : HasGap p i.val := by
  let : Fact p.Prime := ⟨hp⟩
  have hc : Nat.card (RootPairs.solutions (gap i.val) (ZMod p)) ≠ 0 := by
    intro hz
    apply h
    change weight i * (Nat.card _ : ℝ) = 0
    rw [hz,Nat.cast_zero,mul_zero]
  obtain ⟨x,hx⟩ := (Nat.card_pos_iff.mp (Nat.pos_of_ne_zero hc)).1
  have hr : (FallingGap.gap (ZMod p) i.val).IsRoot x := by
    simpa [gap,FallingGap.gap,Polynomial.IsRoot.def,← Polynomial.eval_map] using hx
  obtain ⟨hle,he⟩ := FallingGap.endpoints_of_root hr
  have hxlt := x.val_lt
  have hlt : i.val < x.val := by
    apply lt_of_le_of_ne hle
    intro heq
    rw [← heq,Nat.sub_self,Nat.factorial_zero,Nat.mod_eq_of_lt hp.one_lt,
      Nat.mod_eq_of_lt hB] at he
    exact (Nat.one_lt_factorial.mpr i.property.one_lt).ne he
  refine ⟨x.val-i.val,mem_Ico.mpr ⟨by omega,by omega⟩,?_,?_⟩
  · rw [Nat.sub_add_cancel hle]
    exact mem_Ico.mpr ⟨by omega,hxlt⟩
  · rwa [Nat.sub_add_cancel hle]

/-- Sum of product weights over the subsets satisfying E. -/
def eventMass {R : Type*} [CommRing R] (q : Nat.Primes → R) (s : Finset Nat.Primes)
    (E : Finset Nat.Primes → Prop) : R := by
  classical exact ∑ t ∈ s.powerset.filter E, pattern q t (s \ t)

private theorem pattern_apply (s t : Finset Nat.Primes) (p : ℕ) :
    pattern retain s t p = pattern (fun i => retain i p) s t := by simp [pattern,prod_apply]

private theorem event_apply (s : Finset Nat.Primes) (E : Finset Nat.Primes → Prop) (p : ℕ) :
    eventMass retain s E p = eventMass (fun i => retain i p) s E := by
  classical simp [eventMass,Finset.sum_apply,pattern_apply]

private theorem full_mass (s : Finset Nat.Primes) (q : Nat.Primes → ℝ) :
    ∑ t ∈ s.powerset, pattern q t (s \ t) = 1 := by
  classical
  simpa [pattern] using (prod_add q (fun i => 1-q i) s).symm

theorem event_mean (A : PrimeAverage) (s : Finset Nat.Primes) (E : Finset Nat.Primes → Prop) :
    Tendsto (fun X => A.avg X (eventMass retain s E)) atTop (𝓝 (eventMass weight s E)) := by
  classical
  simp only [eventMass,map_sum]
  exact tendsto_finsetSum _ (fun t _ => pattern_mean A t (s \ t) Finset.disjoint_sdiff)

private theorem weight_nonneg (s t : Finset Nat.Primes) {p : ℕ} (hp : p.Prime) :
    0 ≤ pattern (fun i => retain i p) s t :=
  mul_nonneg (prod_nonneg (fun i _ => (retain_range i hp).1))
    (prod_nonneg (fun i _ => sub_nonneg.mpr (retain_range i hp).2))

def indicator (s : Finset Nat.Primes) (E : Finset Nat.Primes → Prop) (p : ℕ) : ℝ := by
  classical exact if E (hits s p) then 1 else 0

private theorem dominated (s : Finset Nat.Primes) {E : Finset Nat.Primes → Prop} (hE : Monotone E)
    {p : ℕ} (hp : p.Prime) (hB : s.sup (fun i => i.val.factorial) < p) :
    eventMass retain s E p ≤ indicator s E p := by
  classical
  rw [event_apply]
  by_cases hh : E (hits s p)
  · simp only [indicator,if_pos hh,eventMass]
    rw [← full_mass s (fun i => retain i p)]
    exact sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun t _ _ => weight_nonneg t _ hp)
  · simp only [indicator,if_neg hh,eventMass]
    apply le_of_eq
    apply sum_eq_zero
    intro t ht
    obtain ⟨hts,htE⟩ := mem_filter.mp ht
    have hsub := mem_powerset.mp hts
    have not_sub : ¬t ⊆ hits s p := fun hs => hh (hE hs htE)
    obtain ⟨i,hit,hi⟩ := not_subset.mp not_sub
    have hz : retain i p = 0 := by
      by_contra hn
      exact hi (mem_filter.mpr ⟨hsub hit,hasGap_of_retain hp
        ((le_sup (f := fun i : Nat.Primes => i.val.factorial) (hsub hit)).trans_lt hB) hn⟩)
    rw [pattern,prod_eq_zero (f := fun i => retain i p) hit hz,zero_mul]

/-- Every increasing event in the observed prime gap lengths has lower
prime density at least its Bernoulli product probability. -/
theorem event_lower (A : PrimeAverage) (s : Finset Nat.Primes) (E : Finset Nat.Primes → Prop)
    (hE : Monotone E) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X in atTop, eventMass weight s E - ε < A.avg X (indicator s E) := by
  classical
  let B := s.sup (fun i => i.val.factorial)
  let cut := fun p => if B < p then eventMass retain s E p else 0
  have hc := A.finite_change (a := cut) (b := eventMass retain s E) B (fun p hp _ => if_pos hp)
  have hl := hc.add (event_mean A s E)
  simp only [sub_add_cancel,zero_add] at hl
  filter_upwards [hl.eventually_const_lt (show eventMass weight s E - ε < _ by linarith)] with X hx
  apply hx.trans_le (A.mono X ?_)
  intro p hp
  by_cases hb : B < p
  · simpa only [cut,if_pos hb] using dominated s hE hp hb
  · simp only [cut,if_neg hb,indicator]
    split <;> norm_num

/-- A genuine repetition gives a root at its upper endpoint, since the
lower factorial is invertible modulo p. -/
private theorem root_of_hasGap {p k : ℕ} (hp : p.Prime) (hg : HasGap p k) :
    ∃ x : ZMod p, (FallingGap.gap (ZMod p) k).IsRoot x := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨j,hj,he,hh⟩ := hg
  have hj' := (mem_Ico.mp hj).2
  have hn : (j.factorial : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff,hp.dvd_factorial]
    omega
  have eqfac := (ZMod.natCast_eq_natCast_iff' _ _ _).mpr hh
  have hmul := congrArg (fun n : ℕ => (n : ZMod p)) (Nat.factorial_mul_descFactorial
    (show k ≤ j+k by omega))
  rw [Nat.add_sub_cancel,Nat.cast_mul,← eqfac] at hmul
  have hd : ((j+k).descFactorial k : ZMod p) = 1 := (mul_left_cancel₀ hn) (hmul.trans (mul_one _).symm)
  refine ⟨(j+k : ℕ),?_⟩
  rw [Polynomial.IsRoot.def,FallingGap.gap,Polynomial.eval_sub,Polynomial.eval_one,
    descPochhammer_eval_eq_descFactorial,hd,sub_self]

/-- Distinct witnessed lengths have distinct upper endpoints beyond the
finite resultant cutoff. Zero contributes one more missing residue. -/
theorem hits_le_deficit (s : Finset Nat.Primes) :
    ∃ B, ∀ p > B, p.Prime → (hits s p).card+1 ≤ MeanDeficit.deficit p := by
  classical
  let S := s.map (Function.Embedding.subtype Nat.Prime)
  let f := GapFamilies.family ℤ S
  refine ⟨(f.resultant f.derivative).natAbs,?_⟩
  intro p hp hpr
  let : Fact p.Prime := ⟨hpr⟩
  have hc := GapFamilies.card_add_sum_gap_roots S (fun k hk => by
    obtain ⟨i,_,rfl⟩ := mem_map.mp hk; exact i.property.two_le) hp
  have hbound : (hits s p).card ≤ ∑ k ∈ S, (descPochhammer (ZMod p) k - 1).roots.card := by
    have he : (∑ k ∈ S, (descPochhammer (ZMod p) k - 1).roots.card) =
        ∑ i ∈ s, (descPochhammer (ZMod p) i.val - 1).roots.card :=
      Finset.sum_map s (Function.Embedding.subtype Nat.Prime) (fun k => (descPochhammer (ZMod p) k-1).roots.card)
    rw [he]
    apply le_trans _ (sum_le_sum_of_subset (show hits s p ⊆ s from filter_subset ..))
    rw [card_eq_sum_ones]
    apply sum_le_sum
    intro i hi
    obtain ⟨x,hx⟩ := root_of_hasGap hpr ((mem_filter.mp hi).2)
    have hn : descPochhammer (ZMod p) i.val - 1 ≠ 0 := by
      have h := (gap_degree i).monic.map (Int.castRingHom (ZMod p))
      simpa [gap] using h.ne_zero
    exact Multiset.card_pos_iff_exists_mem.mpr ⟨x,(Polynomial.mem_roots hn).mpr hx⟩
  unfold MeanDeficit.deficit
  have := hpr.pos
  omega

/-- A fixed positive number of witnessed lengths forces a corresponding
deficit in the canonical image. -/
theorem deficit_lower (A : PrimeAverage) (s : Finset Nat.Primes) (D : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X in atTop, eventMass weight s (fun t => D ≤ t.card) - ε <
      A.avg X (fun p => if D+1 ≤ MeanDeficit.deficit p then 1 else 0) := by
  classical
  let E := fun t : Finset Nat.Primes => D ≤ t.card
  obtain ⟨B,hB⟩ := hits_le_deficit s
  let cut := fun p => if B < p then indicator s E p else 0
  have hc := A.finite_change (a := cut) (b := indicator s E) B (fun p hp _ => if_pos hp)
  have hl := event_lower A s E (fun _ _ hh hg => hg.trans (card_le_card hh)) (half_pos hε)
  filter_upwards [hl,hc.eventually_const_lt (show -(ε/2)<0 by linarith)] with X hx hcX
  have hm : A.avg X cut ≤ A.avg X (fun p => if D+1 ≤ MeanDeficit.deficit p then 1 else 0) := by
    apply A.mono
    intro p hp
    by_cases hb : B < p
    · simp only [cut,if_pos hb,indicator,E]
      have := hB p hb hp
      split <;> split <;> try norm_num <;> omega
    · simp only [cut,if_neg hb]
      split <;> norm_num
  dsimp only [E] at hx
  linarith

theorem complement_mass (s : Finset Nat.Primes) (E : Finset Nat.Primes → Prop) :
    eventMass weight s E + eventMass weight s (fun t => ¬E t) = 1 := by
  classical
  unfold eventMass
  rw [sum_filter_add_sum_filter_not,full_mass]

theorem all_mass (s : Finset Nat.Primes) :
    eventMass weight s (fun t => s ⊆ t) = ∏ i ∈ s, weight i := by
  classical
  unfold eventMass
  calc
    _ = ∑ t ∈ ({s} : Finset _), pattern weight t (s \ t) := by
      apply sum_congr _ (fun _ _ => rfl)
      ext t
      simp only [mem_filter,mem_powerset,mem_singleton]
      exact ⟨fun h => Subset.antisymm h.1 h.2,fun h => h ▸ ⟨Subset.rfl,Subset.rfl⟩⟩
    _ = _ := by simp [pattern]

theorem empty_mass (s : Finset Nat.Primes) :
    eventMass weight s (fun t => t = ∅) = ∏ i ∈ s, (1-weight i) := by
  classical
  unfold eventMass
  calc
    _ = ∑ t ∈ ({∅} : Finset (Finset Nat.Primes)), pattern weight t (s \ t) := by
      apply sum_congr _ (fun _ _ => rfl)
      ext t
      simp_all
    _ = _ := by simp [pattern]

#print axioms hits_le_deficit
#print axioms deficit_lower
#print axioms pattern_mean
#print axioms event_mean
#print axioms event_lower

end
end Erdos478.GapSieve
