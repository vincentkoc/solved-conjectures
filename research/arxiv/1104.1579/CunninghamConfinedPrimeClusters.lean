import Mathlib
import CunninghamPrimeReturnTimes
import CunninghamPeriodicReturnCover

/-! Return times of centered Cunningham orbits in prescribed residue classes. -/

namespace CunninghamChain.ConfinedClusters

/-- In centered coordinates the two Cunningham recurrences both multiply by two.
Cancelling the center gives the exact modulus of a residue return. -/
theorem center_return_iff {w : ℕ} (hw : 0 < w) (x j : ℕ) :
    2 ^ j * x ≡ x [MOD w] ↔ 2 ^ j ≡ 1 [MOD w / w.gcd x] := by
  constructor
  · intro h
    exact Nat.ModEq.cancel_right_div_gcd hw (by simpa using h)
  · intro h
    have h' := (h.mul_right' (w.gcd x)).mul_right (x / w.gcd x)
    simpa only [Nat.div_mul_cancel (Nat.gcd_dvd_left w x), Nat.one_mul, Nat.mul_assoc,
      Nat.mul_div_cancel' (Nat.gcd_dvd_right w x)] using h'

/-- A positive return to the initial residue exists exactly when cancelling
the center removes the entire two-part of the modulus. -/
theorem positive_center_return_iff {w : ℕ} (hw : 0 < w) (x : ℕ) :
    (∃ j > 0, 2 ^ j * x ≡ x [MOD w]) ↔ Odd (w / w.gcd x) := by
  constructor
  · rintro ⟨j, hj, h⟩
    apply Nat.coprime_two_left.mp
    apply Nat.prime_two.coprime_iff_not_dvd.mpr
    intro hd
    have hbad : 2 ∣ 1 := ((center_return_iff hw x j).mp h).dvd_iff hd |>.mp
      (dvd_pow_self 2 hj.ne')
    exact (by decide : ¬2 ∣ 1) hbad
  · intro ho
    have hpos : 0 < w / w.gcd x := Nat.div_pos (Nat.gcd_le_left x hw) (Nat.gcd_pos_of_pos_left x hw)
    exact ⟨_, Nat.totient_pos.mpr hpos, (center_return_iff hw x _).mpr
      (Nat.ModEq.pow_totient ho.coprime_two_left)⟩

open PrimeReturns Finset

private theorem orbit_congr_iff (first : Bool) {w x y : ℕ} (hx : 0 < x) (hy : 0 < y)
    (i j : ℕ) :
    orbitValue first x i ≡ orbitValue first y j [MOD w] ↔ 2^i*x ≡ 2^j*y [MOD w] := by
  have hxi : 1 ≤ 2^i*x := Nat.mul_pos (by positivity) hx
  have hyj : 1 ≤ 2^j*y := Nat.mul_pos (by positivity) hy
  simp only [← ZMod.natCast_eq_natCast_iff]
  cases first <;> simp [orbitValue, Nat.cast_sub hxi, Nat.cast_sub hyj]

private theorem orbit_lower (first : Bool) (x i : ℕ) : x ≤ orbitValue first x i + 1 := by
  have := Nat.le_mul_of_pos_left x (by positivity : 0 < 2^i)
  cases first <;> simp [orbitValue] <;> omega

private theorem orbit_admissible (first : Bool) {w B : ℕ} (hB : 0 < B)
    (I : Finset ℕ) (s : ℕ → ℕ) (hunit : ∀ i ∈ I, (orbitValue first B (s i)).Coprime w)
    (q : ℕ) (hq : q.Prime) : ∃ t : ℕ, ∀ i ∈ I, ¬q ∣ orbitValue first (w*t+B) (s i) := by
  by_cases hd : q ∣ w
  · refine ⟨0, fun i hi h => ?_⟩
    simp only [mul_zero, zero_add] at h
    exact Nat.not_coprime_of_dvd_of_dvd hq.one_lt h hd (hunit i hi)
  · let : Fact q.Prime := ⟨hq⟩
    have hw := (ZMod.natCast_eq_zero_iff w q).not.mpr hd
    obtain ⟨t, ht⟩ := ZMod.natCast_zmod_surjective (-(B : ZMod q) / (w : ZMod q))
    have hz : ((w*t+B : ℕ) : ZMod q) = 0 := by push_cast; rw [ht]; field_simp; ring
    refine ⟨t, fun i _ hh => ?_⟩
    have h := (ZMod.natCast_eq_zero_iff ..).mpr hh
    have hp : 1 ≤ 2^(s i)*(w*t+B) := Nat.mul_pos (by positivity) (by omega)
    cases first <;> simp only [orbitValue, Bool.false_eq_true, if_false, if_true, Nat.cast_add,
      Nat.cast_sub hp, Nat.cast_one, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at h hz <;>
      simp [hz] at h

/-- Select a fixed pattern of at least m+1 actual prime sites on an admissible
grid. The pattern is measured from its first selected prime. The centers in
the original progression can be taken arbitrarily large. -/
private theorem recurrent_grid (h : MaynardAffineClusters) (first : Bool) {w B L : ℕ}
    (hw : 0 < w) (hB : 0 < B) (hL : 0 < L)
    (hunit : ∀ i : ℕ, (orbitValue first B (L*i)).Coprime w) (m : ℕ) :
    ∃ a : ℕ, ∃ V : Finset ℕ, 0 ∈ V ∧ m < V.card ∧ (∀ j ∈ V, L ∣ j) ∧
      ∀ Z : ℕ, ∃ x > Z, x ≡ B [MOD w] ∧ ∀ j ∈ V, (orbitValue first x (L*a+j)).Prime := by
  classical
  obtain ⟨K, hK⟩ := h (m+1)
  let I := range K
  let coeff (i : ℕ) := 2^(L*i)*w
  let c (i : ℕ) := orbitValue first B (L*i)
  have eqn (t i : ℕ) : coeff i*t+c i = orbitValue first (w*t+B) (L*i) :=
    (affine_orbit first hB w t (L*i)).symm
  have enough := hK I coeff c (by simp [I]) (fun i _ => Nat.mul_pos (by positivity) hw)
    (fun i _ j _ hn => affine_nondegenerate first hB hw (by exact mt (Nat.eq_of_mul_eq_mul_left hL) hn))
    (fun q hq => by simpa only [eqn] using orbit_admissible first hB I (fun i => L*i) (fun i _ => hunit i) q hq)
  choose t ht count using enough
  let pat (z : ℕ) : ↥I.powerset :=
    ⟨I.filter fun i => (coeff i*t z+c i).Prime, mem_powerset.mpr (filter_subset ..)⟩
  obtain ⟨U, hu⟩ := Finite.exists_infinite_fiber pat
  have freq : (pat ⁻¹' {U}).Infinite := Set.infinite_coe_iff.mp hu
  have identifies {z : ℕ} (hz : z ∈ pat ⁻¹' {U}) :
      (I.filter fun i => (coeff i*t z+c i).Prime) = U.val :=
    congrArg Subtype.val (show pat z = U from hz)
  obtain ⟨z₀, hz₀⟩ := freq.nonempty
  have hsize : m < U.val.card := identifies hz₀ ▸ count z₀
  have hne := card_pos.mp (by omega : 0 < U.val.card)
  let a := U.val.min' hne
  let shift (i : ℕ) := L*(i-a)
  have ha (i : ℕ) (hi : i ∈ U.val) : a ≤ i := min'_le _ _ hi
  have hinj : Set.InjOn shift (U.val : Set ℕ) := by
    intro i hi j hj he
    have := Nat.eq_of_mul_eq_mul_left hL he
    have := ha i hi
    have := ha j hj
    omega
  refine ⟨a, U.val.image shift, mem_image.mpr ⟨a, min'_mem _ hne, by simp [shift]⟩,
    (Finset.card_image_iff.mpr hinj).symm ▸ hsize, ?_, ?_⟩
  · rintro _ hj
    obtain ⟨i, _, rfl⟩ := mem_image.mp hj
    exact dvd_mul_right ..
  · intro Z
    obtain ⟨z, hz, hgt⟩ := Set.infinite_iff_exists_gt.mp freq Z
    have := Nat.le_mul_of_pos_left (t z) hw
    have := ht z
    refine ⟨w*t z+B, by omega, Nat.ModEq.modulus_mul_add, ?_⟩
    intro j hj
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hj
    have idx : L*a+shift i = L*i := by
      dsimp only [shift]
      rw [← Nat.mul_add, Nat.add_sub_of_le (ha i hi)]
    rw [idx, ← eqn]
    rw [← identifies hz] at hi
    exact (mem_filter.mp hi).2

private theorem class_of_center (first : Bool) {w x B j : ℕ} (hx : 0 < x) (hB : 0 < B)
    (h : 2^j*x ≡ B [MOD w]) :
    orbitValue first x j ≡ orbitValue first B 0 [MOD w] :=
  (orbit_congr_iff first hx hB j 0).mpr (by simpa using h)

private theorem positive_seed_center (first : Bool) {p : ℕ} (hp : 3 ≤ p) :
    ∃ x ≥ 2, orbitValue first x 0 = p := by
  cases first
  · exact ⟨p-1, by omega, by simp [orbitValue]; omega⟩
  · exact ⟨p+1, by omega, by simp [orbitValue]⟩

private theorem repeated_return {w B L : ℕ} (h : 2^L*B ≡ B [MOD w]) (k : ℕ) :
    2^(L*k)*B ≡ B [MOD w] := by
  induction k with
  | zero => simp [Nat.ModEq]
  | succ k ih =>
    rw [Nat.mul_succ, pow_add, Nat.mul_assoc]
    exact (h.mul_left _).trans ih

/-- A single return of a seed to its initial class forces the two-part condition
for that class, independently of primality or of any affine-cluster hypothesis. -/
theorem odd_quotient_of_seed_return (first : Bool) {w B p j : ℕ}
    (hw : 0 < w) (hB : 0 < B) (hp : 3 ≤ p) (hj : 0 < j)
    (hclass : p ≡ orbitValue first B 0 [MOD w])
    (hreturn : SquarefreeSeeds.term first p j ≡ p [MOD w]) : Odd (w / w.gcd B) := by
  obtain ⟨x, hx, rfl⟩ := positive_seed_center first hp
  change (if first then firstKindTerm else secondKindTerm) _ _ ≡ _ [MOD w] at hreturn
  rw [orbit_restart first hx, zero_add] at hreturn
  have h₀ : x ≡ B [MOD w] := by
    simpa using (orbit_congr_iff first (by omega) hB 0 0).mp hclass
  have h₁ := (orbit_congr_iff first (by omega : 0 < x) hB j 0).mp (hreturn.trans hclass)
  exact (positive_center_return_iff hw B).mp ⟨j, hj, (h₀.symm.mul_left _).trans (by simpa using h₁)⟩

/-- In a reduced seed class, the two-part condition characterizes arbitrarily
large fixed patterns of prime returns to that same class for infinitely many
prime seeds. The sufficiency direction uses Maynard's affine-cluster input. -/
theorem prime_clusters_in_class_iff (h : MaynardAffineClusters) (first : Bool) {w B : ℕ}
    (hw : 0 < w) (hB : 0 < B) (hunit : (orbitValue first B 0).Coprime w) :
    Odd (w / w.gcd B) ↔ ∀ m : ℕ, ∃ V : Finset ℕ, 0 ∈ V ∧ m < V.card ∧
      {p : ℕ | p.Prime ∧ p ≡ orbitValue first B 0 [MOD w] ∧
        ∀ j ∈ V, (SquarefreeSeeds.term first p j).Prime ∧
          SquarefreeSeeds.term first p j ≡ p [MOD w]}.Infinite := by
  constructor
  · intro ho m
    obtain ⟨L, hL, hbase⟩ := (positive_center_return_iff hw B).mpr ho
    have clas {x i : ℕ} (hx : 0 < x) (hc : x ≡ B [MOD w]) (hi : L ∣ i) :
        orbitValue first x i ≡ orbitValue first B 0 [MOD w] := by
      obtain ⟨k, rfl⟩ := hi
      exact class_of_center first hx hB ((hc.mul_left _).trans (repeated_return hbase k))
    obtain ⟨a, V, h₀, hm, hv, hits⟩ := recurrent_grid h first hw hB hL
      (fun i => (clas hB (Nat.ModEq.refl _) (dvd_mul_right L i)).gcd_eq.trans hunit) m
    refine ⟨V, h₀, hm, Set.infinite_of_forall_exists_gt ?_⟩
    intro Z
    obtain ⟨x, hx, hc, hh⟩ := hits (Z+3)
    have hp := orbit_lower first x (L*a)
    have ha := clas (by omega : 0 < x) hc (dvd_mul_right L a)
    refine ⟨orbitValue first x (L*a), ⟨by simpa using hh 0 h₀, ha, ?_⟩, by omega⟩
    intro j hj
    simp only [SquarefreeSeeds.term, orbit_restart first (by omega : 2 ≤ x)]
    exact ⟨hh j hj, (clas (by omega) hc (dvd_add (dvd_mul_right L a) (hv j hj))).trans ha.symm⟩
  · intro all
    obtain ⟨V, _, hmany, hp⟩ := all 1
    obtain ⟨i, hi, j, hj, hne⟩ := Finset.one_lt_card.mp hmany
    have pos : ∃ k ∈ V, 0 < k := by
      by_cases h : i = 0
      · exact ⟨j, hj, by omega⟩
      · exact ⟨i, hi, by omega⟩
    obtain ⟨k, hk, hpos⟩ := pos
    obtain ⟨p, ⟨_, hclass, hprime⟩, hlarge⟩ := Set.infinite_iff_exists_gt.mp hp 3
    exact odd_quotient_of_seed_return first hw hB (by omega) hpos hclass (hprime k hk).2

/-- Under the affine-cluster theorem, permanently confined orbits contain
arbitrarily large finite patterns of actual prime returns. Each pattern
occurs for infinitely many prime seeds and is independent of the seed. -/
theorem prime_clusters_with_confined_returns (h : MaynardAffineClusters) (M : ℕ) (hM : 0 < M) :
    ∃ D W : ℕ, 0 < D ∧ M ∣ D ∧ 0 < W ∧ ∀ (first : Bool) (m : ℕ),
      ∃ V : Finset ℕ, 0 ∈ V ∧ m < V.card ∧ (∀ j ∈ V, D ∣ j) ∧
        {p : ℕ | W < p ∧ p.Prime ∧ (∀ j ∈ V, (SquarefreeSeeds.term first p j).Prime) ∧
          ∀ j : ℕ, ((SquarefreeSeeds.term first p j).Coprime W ↔ D ∣ j) ∧
            ((SquarefreeSeeds.term first p j).Prime → M ∣ j)}.Infinite := by
  obtain ⟨D, W, hD, hMD, hW, classes⟩ := ReturnCover.periodic_seed_classes M hM
  refine ⟨D, W, hD, hMD, hW, ?_⟩
  intro first m
  obtain ⟨A, _, hA⟩ := classes first
  obtain ⟨B, hB, hb⟩ := positive_seed_center first (show 3 ≤ A+3*W by omega)
  have base : orbitValue first B 0 ≡ A [MOD W] := by rw [hb]; simp [Nat.ModEq]
  have mask {x : ℕ} (hx : 2 ≤ x) (hc : x ≡ B [MOD W]) (i : ℕ) :
      (orbitValue first x i).Coprime W ↔ D ∣ i := by
    have hx' : 0 < orbitValue first x 0 := by have := orbit_lower first x 0; omega
    have h₀ := (orbit_congr_iff first (by omega : 0 < x) (by omega : 0 < B) 0 0).mpr
      (by simpa using hc)
    simpa only [SquarefreeSeeds.term, orbit_restart first hx, zero_add] using hA _ hx' (h₀.trans base) i
  obtain ⟨a, V, h₀, hm, hv, hits⟩ := recurrent_grid h first hW (by omega : 0 < B) hD
    (fun i => (mask hB (Nat.ModEq.refl _) _).mpr (dvd_mul_right D i)) m
  refine ⟨V, h₀, hm, hv, Set.infinite_of_forall_exists_gt ?_⟩
  intro Z
  obtain ⟨x, hx, hc, hh⟩ := hits (Z+W+3)
  have hp := orbit_lower first x (D*a)
  have hseed : (orbitValue first x (D*a)).Prime := by simpa using hh 0 h₀
  refine ⟨orbitValue first x (D*a), ⟨by omega, hseed, ?_, ?_⟩, by omega⟩
  · intro j hj
    simpa only [SquarefreeSeeds.term, orbit_restart first (by omega : 2 ≤ x)] using hh j hj
  · intro j
    simp only [SquarefreeSeeds.term, orbit_restart first (by omega : 2 ≤ x)]
    have exactMask := (mask (by omega : 2 ≤ x) hc (D*a+j)).trans (Nat.dvd_add_right (dvd_mul_right D a))
    refine ⟨exactMask, fun hprime => hMD.trans (exactMask.mp ?_)⟩
    have hlow := orbit_lower first x (D*a+j)
    exact hprime.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hW (by omega))

#print axioms prime_clusters_with_confined_returns

#print axioms odd_quotient_of_seed_return
#print axioms prime_clusters_in_class_iff

#print axioms center_return_iff
#print axioms positive_center_return_iff

end CunninghamChain.ConfinedClusters
