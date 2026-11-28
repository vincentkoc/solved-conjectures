import CunninghamPairedRoughStops

/-! Primitive-root primes and sharp stopping thresholds for pairs of opposite
Cunningham progressions. -/

namespace CunninghamChain.PairedRough
open Finset PairedGaps ArtinPrimitiveRootsConjecture

theorem all_local_tests_iff (h : ℕ) :
    (∀ k > 0, ∀ l > 0, localTest h k l) ↔ GapAdmissible h := by
  constructor
  · intro all k q hp
    obtain ⟨x,hx⟩ := (localTest_iff_all (k:=k+1) (l:=k+1) (by omega) (by omega)).mp
      (all (k+1) (by omega) (k+1) (by omega)) q hp
    refine ⟨x+1,fun i hi => ⟨hx.1 i (by omega),?_⟩⟩
    rw [show x+1+h-2=x+h-1 by ring]
    exact hx.2 i (by omega)
  · intro adm k hk l hl
    apply (localTest_iff_all hk hl).mpr
    intro q hp
    obtain ⟨v,hv⟩ := adm (max k l) q hp
    refine ⟨v-1,⟨fun i hi => ?_,fun j hj => ?_⟩⟩
    · simpa using (hv i (hi.trans_le (le_max_left ..))).1
    · rw [show v-1+h-1=v+h-2 by ring]
      exact (hv j (hj.trans_le (le_max_right ..))).2

/-- For unrestricted almost-prime starts this all-length characterization
uses no analytic input. -/
theorem all_paired_rough_stops_iff (h : ℕ) :
    (∀ k > 0, ∀ l > 0, supply (fun _ => True) h k l (324*(k+l)+33)) ↔
      Even h ∧ ∀ q ∈ S 2, h ≡ 2 [MOD q] := by
  rw [← gap_admissible_iff,← all_local_tests_iff]
  exact forall_congr' fun k => forall_congr' fun hk => forall_congr' fun l =>
    forall_congr' fun hl => paired_rough_stops_iff hk hl

theorem all_prime_paired_rough_stops_iff (hBV : PrimeSeedSieve.BombieriVinogradov) (h : ℕ) :
    (∀ k > 0, ∀ l > 0, supply Nat.Prime h k l (1152*(k+l)+117)) ↔
      Even h ∧ ∀ q ∈ S 2, h ≡ 2 [MOD q] := by
  rw [← gap_admissible_iff,← all_local_tests_iff]
  exact forall_congr' fun k => forall_congr' fun hk => forall_congr' fun l =>
    forall_congr' fun hl => paired_prime_rough_stops_iff hBV hk hl

#print axioms all_prime_paired_rough_stops_iff

/-- Uniqueness of the bi-twin gap for arbitrarily long, arbitrarily rough
almost-prime pairs is equivalent to the infinitude part of Artin at two. -/
theorem unique_rough_gap_iff :
    (∀ h, (∀ k > 0, ∀ l > 0, supply (fun _ => True) h k l (324*(k+l)+33)) ↔ h=2) ↔
      (S 2).Infinite := by
  rw [← unique_admissible_gap_iff]
  simp_rw [all_paired_rough_stops_iff, gap_admissible_iff]

#print axioms all_paired_rough_stops_iff
#print axioms unique_rough_gap_iff

private lemma primitive_data {q : ℕ} (hq : q ∈ S 2) :
    2 < q ∧ orderOf (2:ZMod q)=q-1 := by
  have hp := hq.1.two_le
  have ord : orderOf (2:ZMod q)=q-1 := by simpa using hq.2
  refine ⟨?_,ord⟩
  by_contra! h
  obtain rfl : q=2 := by omega
  rw [show (2:ZMod 2)=0 by decide,orderOf_zero] at ord
  omega

private lemma full_period_forces_gap {h q : ℕ} (hq : q ∈ S 2) {x : ZMod q}
    (ok : avoids h (q-1) (q-1) q x) : (h:ZMod q)=2 := by
  have ⟨big,ord⟩ := primitive_data hq
  let : Fact q.Prime := ⟨hq.1⟩
  let : NeZero (q-1) := ⟨by omega⟩
  have trans (u : ZMod q) (hn : u≠0) : ∃ i < q-1, (2:ZMod q)^i*u=1 := by
    have gen : IsPrimitiveRoot (2:ZMod q) (q-1) := ord ▸ IsPrimitiveRoot.orderOf _
    obtain ⟨i,hi,hit⟩ := gen.eq_pow_of_pow_eq_one (ξ:=u⁻¹) (ZMod.pow_card_sub_one_eq_one (inv_ne_zero hn))
    exact ⟨i,hi,by rw [hit,inv_mul_cancel₀ hn]⟩
  have one : x+1=0 := by
    by_contra ne
    obtain ⟨i,hi,hit⟩ := trans _ ne
    exact ok.1 i hi hit
  have zero : -(x+h-1)=0 := by
    by_contra ne
    obtain ⟨i,hi,hit⟩ := trans _ ne
    exact ok.2 i hi (by linear_combination -hit)
  linear_combination -zero-one

private lemma threshold_at_prime {h q : ℕ} (hq : q ∈ S 2) (shift : (h:ZMod q)= -2) :
    avoids h (q-2) (q-2) q 1 ∧ ¬∃ x : ZMod q, avoids h (q-1) (q-1) q x := by
  have ⟨big,ord⟩ := primitive_data hq
  let : Fact q.Prime := ⟨hq.1⟩
  let : NeZero (q-1) := ⟨by omega⟩
  have before (i : ℕ) (hi : i < q-2) : (2:ZMod q)^i*2 ≠ 1 := by
    intro eq
    have dv := orderOf_dvd_of_pow_eq_one (show (2:ZMod q)^(i+1)=1 by rwa [pow_succ])
    rw [ord] at dv
    have := Nat.le_of_dvd (by omega : 0 < i+1) dv
    omega
  constructor
  · constructor
    · exact fun i hi => by simpa only [one_add_one_eq_two] using before i hi
    · intro i hi eq
      rw [shift] at eq
      apply before i hi
      linear_combination -eq
  · rintro ⟨x,ok⟩
    have eq := full_period_forces_gap hq ok
    have two : (2:ZMod q)≠0 := fun e => Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) big
      ((ZMod.natCast_eq_zero_iff 2 q).mp (by simpa using e))
    exact mul_ne_zero two two (by linear_combination shift-eq)

/-- For each base-two primitive-root prime q there are infinitely many even
gaps where both prefixes pass at length q-2 and q itself obstructs q-1. -/
theorem infinitely_many_sharp_gaps {q : ℕ} (hq : q ∈ S 2) :
    {h : ℕ | Even h ∧ localTest h (q-2) (q-2) ∧ ¬∃ x : ZMod q, avoids h (q-1) (q-1) q x}.Infinite := by
  classical
  have big := (primitive_data hq).1
  let P := (2*q).primesLE
  let W := ∏ s ∈ P, s
  have pr {s : ℕ} (hs : s∈P) := Nat.prime_of_mem_primesLE hs
  have wpos : 0<W := prod_pos (fun _ h => (pr h).pos)
  let a (s : ℕ) := if s=q then q-2 else 2
  let u := Nat.chineseRemainderOfFinset a id P (fun _ hs => (pr hs).ne_zero)
    (fun _ hs _ ht ne => (Nat.coprime_primes (pr hs) (pr ht)).mpr ne)
  apply Set.infinite_of_forall_exists_gt
  intro N
  let h := W*(N+1)+u.val
  have cls (s : ℕ) (hs : s∈P) : (h:ZMod s)=(a s:ZMod s) := by
    have ws := (ZMod.natCast_eq_zero_iff W s).mpr (dvd_prod_of_mem id hs)
    dsimp only [h]; push_cast
    rw [ws,zero_mul,zero_add,(ZMod.natCast_eq_natCast_iff ..).mpr (u.property s hs)]
  have shift : (h:ZMod q)= -2 := by
    rw [cls q (Nat.mem_primesLE.mpr ⟨by omega,hq.1⟩)]
    simp [a,Nat.cast_sub (by omega : 2≤q)]
  have even : Even h := by
    apply even_iff_two_dvd.mpr
    apply (ZMod.natCast_eq_zero_iff h 2).mp
    rw [cls 2 (Nat.mem_primesLE.mpr ⟨by omega,Nat.prime_two⟩)]
    simp only [a,if_neg (show 2≠q by omega)]
    decide
  refine ⟨h,⟨even,?_,(threshold_at_prime hq shift).2⟩,?_⟩
  · intro s hs
    have prime := Nat.prime_of_mem_primesLE hs
    let : Fact s.Prime := ⟨prime⟩
    by_cases eq : s=q
    · subst s
      exact ⟨1,(threshold_at_prime hq shift).1⟩
    have ss := Nat.le_of_mem_primesLE hs
    have val : (h:ZMod s)=2 := by
      rw [cls s (Nat.mem_primesLE.mpr ⟨by omega,prime⟩)]
      simp [a,eq]
    exact ⟨-1,by simp [avoids,val,show (-1:ZMod s)+2-1=0 by ring]⟩
  · have := Nat.le_mul_of_pos_left (N+1) wpos
    dsimp [h]
    omega

#print axioms infinitely_many_sharp_gaps

/-- Failure of a local test gives an actual common-divisor obstruction
for every seed, also for the original prime-prefix questions. -/
theorem unavoidable_divisor {h k l q : ℕ} (none : ¬∃ x : ZMod q, avoids h k l q x)
    (n : ℕ) (hn : 2≤n) :
    (∃ i < k, q ∣ firstKindTerm n i) ∨ (∃ j < l, q ∣ secondKindTerm (n+h) j) := by
  by_contra! no
  apply none
  refine ⟨n,(avoids_iff ..).mpr ?_⟩
  apply (sites_iff (k:=k) (l:=l) (fun b i => residue q (2^i) (base h b i) n≠0)).mpr
  have lift (b : Bool) (i : ℕ) (absent : ¬q ∣ (if b then firstKindTerm n i else secondKindTerm (n+h) i)) :
      residue q (2^i) (base h b i) n≠0 := by
    rw [←term_cast _ _ _ _ hn]
    exact fun e => absent ((term_chain hn _ b i) ▸ (ZMod.natCast_eq_zero_iff ..).mp e)
  exact ⟨fun i hi => lift true i (by simpa using no.1 i hi),
    fun j hj => lift false j (by simpa using no.2 j hj)⟩

theorem gap_eight : localTest 8 3 3 ∧ ¬∃ x : ZMod 5, avoids 8 4 4 5 x := by
  constructor
  · intro q hq
    have primes : q=2 ∨ q=3 ∨ q=5 := by
      have : (3+3 : ℕ).primesLE={2,3,5} := by decide
      simpa [this] using hq
    rcases primes with rfl|rfl|rfl <;> unfold avoids <;> decide +kernel
  · unfold avoids
    decide +kernel

#print axioms unavoidable_divisor
#print axioms gap_eight

/-- Finite gaps with arbitrarily late first failure exist exactly when two is
a primitive root at infinitely many primes. All starts here are unrestricted
and the bounded multiplicities and two forced composites are part of supply. -/
theorem unbounded_finite_thresholds_iff :
    (∀ B : ℕ, ∃ k>B, ∃ h : ℕ,
      supply (fun _ => True) h k k (324*(k+k)+33) ∧
      ¬supply (fun _ => True) h (k+1) (k+1) (324*(k+1+(k+1))+33)) ↔ (S 2).Infinite := by
  constructor
  · intro late finite
    obtain ⟨M,hM⟩ := finite.bddAbove
    obtain ⟨k,hk,h,yes,no⟩ := late (M+2)
    have pos : 0 < k := by omega
    have localOK := (paired_rough_stops_iff pos pos).mp yes
    have all := (localTest_iff_all pos pos).mp localOK
    obtain ⟨u,hu⟩ := all 2 Nat.prime_two
    have even : Even h := by
      have one := hu.1 0 pos
      have two := hu.2 0 pos
      have eq : (h:ZMod 2)=0 := (by decide :
        ∀ u v : ZMod 2, (2:ZMod 2)^0*(u+1) ≠ 1 → (2:ZMod 2)^0*(u+v-1) ≠ -1 → v=0) u h one two
      exact even_iff_two_dvd.mpr ((ZMod.natCast_eq_zero_iff h 2).mp eq)
    have adm : GapAdmissible h := (gap_admissible_iff h).mpr ⟨even,fun q hq => by
      obtain ⟨x,ok⟩ := all q hq.1
      have le := hM hq
      have full : avoids h (q-1) (q-1) q x := ⟨fun i hi => ok.1 i (by omega),fun i hi => ok.2 i (by omega)⟩
      exact (ZMod.natCast_eq_natCast_iff ..).mp (by simpa using full_period_forces_gap hq full)⟩
    exact no ((paired_rough_stops_iff (by omega) (by omega)).mpr
      ((all_local_tests_iff h).mpr adm (k+1) (by omega) (k+1) (by omega)))
  · intro inf B
    obtain ⟨q,hq,big⟩ := Set.infinite_iff_exists_gt.mp inf (B+3)
    obtain ⟨h,_,pass,fail⟩ := (infinitely_many_sharp_gaps hq).nonempty
    have pos : 0 < q-2 := by omega
    refine ⟨q-2,by omega,h,(paired_rough_stops_iff pos pos).mpr pass,fun hs => fail ?_⟩
    have all := (localTest_iff_all (by omega) (by omega)).mp
      ((paired_rough_stops_iff (by omega) (by omega)).mp hs) q hq.1
    simpa only [show q-2+1=q-1 by omega] using all

#print axioms unbounded_finite_thresholds_iff

#print axioms all_local_tests_iff

end CunninghamChain.PairedRough
