import CunninghamJonesPoweredDegrees
import FormalConjecturesForMathlib.Data.Set.Density

/-! Simultaneous irreducibility across all powers of a fixed Jones coefficient. -/

namespace CunninghamChain
open Set Filter
open scoped Topology

/-- Degrees at which at least one positive power gives a reducible sum. -/
def jonesExceptionalDegrees (m : ℕ) : Set ℕ :=
  {j | ∃ h : ℕ, 0 < h ∧ ¬Irreducible ((jonesSumPolynomial (m^h) j).map (Int.castRingHom ℚ))}

private theorem count_in_interval {E : Set ℕ} {D q : ℕ}
    (hE : ∀ j ∈ E, D ≤ j → q ∣ j) (a N : ℕ) :
    (E ∩ Ico a (a+N)).ncard ≤ D+N/q+2 := by
  let T := Icc (a/q) ((a+N)/q)
  have sub : E ∩ Ico a (a+N) ⊆ Iio D ∪ (fun t : ℕ => q*t) '' T := by
    rintro j ⟨hj,hlo,hhi⟩
    by_cases h : j<D
    · exact Or.inl h
    · have hd := hE j hj (by omega)
      refine Or.inr ⟨j/q,⟨Nat.div_le_div_right hlo,Nat.div_le_div_right hhi.le⟩,?_⟩
      exact Nat.mul_div_cancel' hd
  have hc := ncard_le_ncard sub ((finite_Iio D).union ((finite_Icc ..).image _))
  have hi := ncard_image_le (f:=fun t : ℕ => q*t) (s:=T) (finite_Icc ..)
  have hcard := hc.trans (ncard_union_le ..)
  rw [Nat.ncard_Iio] at hcard
  have htc : T.ncard=(a+N)/q+1-a/q := by
    rw [show T=(Finset.Icc (a/q) ((a+N)/q) : Finset ℕ) by simp [T],Set.ncard_coe_finset,Nat.card_Icc]
  rw [htc] at hi
  have hs : (a+N)/q+1-a/q ≤ N/q+2 := by
    apply Nat.sub_le_of_le_add
    have := Nat.add_div_le_div_add_div_add_one a N q
    omega
  exact hcard.trans ((Nat.add_le_add_left (hi.trans hs) D).trans_eq (by omega))

/-- For every tolerance, all sufficiently long intervals contain a smaller
fraction of exceptional degrees, uniformly over their starting points. -/
theorem jones_powered_exceptional_windows {m : ℕ} (hm : 2 ≤ m) {ε : ℝ} (hε : 0<ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ a : ℕ,
      (((jonesExceptionalDegrees m ∩ Ico a (a+N)).ncard : ℝ) / N) < ε := by
  obtain ⟨k,hk⟩ := exists_nat_gt (2/ε)
  obtain ⟨D,hD⟩ := jones_powered_exceptional_degrees hm k
  let q := m^k
  have hkq : k<q := Nat.lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_left hm k)
  have hεq : 1 ≤ (ε/2)*(q:ℝ) := by
    have hreal : (k:ℝ) < q := by exact_mod_cast hkq
    have he := (div_lt_iff₀ hε).mp (hk.trans hreal)
    linarith
  obtain ⟨N₀,h₀⟩ := exists_nat_gt (2*((D:ℝ)+2)/ε)
  refine ⟨N₀+1,?_⟩
  intro N hn a
  have hn' : (N₀:ℝ) ≤ N := by exact_mod_cast (show N₀ ≤ N by omega)
  have hN : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hsmall := (div_lt_iff₀ hε).mp (h₀.trans_le hn')
  have hE (j : ℕ) (hj : j ∈ jonesExceptionalDegrees m) (hDj : D ≤ j) : q ∣ j := by
    obtain ⟨h,hh,hred⟩ := hj
    exact hD j hDj h hh hred
  have hc := count_in_interval hE a N
  have hc' : ((jonesExceptionalDegrees m ∩ Ico a (a+N)).ncard : ℝ) ≤
      (D:ℝ) + (N/q : ℕ) + 2 := by exact_mod_cast hc
  have hfloor : ((N/q : ℕ):ℝ)*q ≤ N := by exact_mod_cast Nat.div_mul_le_self N q
  have hb : ((N/q : ℕ):ℝ) ≤ (ε/2)*N := calc
    _ ≤ (N/q : ℕ)*((ε/2)*(q:ℝ)) := le_mul_of_one_le_right (Nat.cast_nonneg _) hεq
    _ = (ε/2)*(((N/q : ℕ):ℝ)*q) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hfloor (by positivity)
  apply (div_lt_iff₀ hN).mpr
  linarith

/-- A single set of natural density one works for every positive exponent of
the chosen base. -/
theorem jones_all_powers_density_one {m : ℕ} (hm : 2 ≤ m) :
    {j : ℕ | ∀ h : ℕ, 0<h →
      Irreducible ((jonesSumPolynomial (m^h) j).map (Int.castRingHom ℚ))}.HasDensity 1 := by
  let E := jonesExceptionalDegrees m
  have hE : E.HasDensity 0 := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨N₀,h⟩ := jones_powered_exceptional_windows hm hε
    refine eventually_atTop.mpr ⟨N₀,fun N hn => ?_⟩
    rw [Real.dist_eq,sub_zero,abs_of_nonneg (show 0 ≤ E.partialDensity Set.univ N by positivity)]
    have hz : Ico 0 N = Iio N := by ext x; simp
    simpa only [Set.partialDensity,Set.inter_univ,Set.univ_inter,Nat.ncard_Iio,
      Nat.zero_add,hz,E] using h N hn 0
  have hsum : ∀ᶠ N : ℕ in atTop,
      Eᶜ.partialDensity Set.univ N = 1-E.partialDensity Set.univ N := by
    refine eventually_atTop.mpr ⟨1,fun N hN => ?_⟩
    have he := ncard_inter_add_ncard_sdiff_eq_ncard (Iio N) E
    rw [Set.sdiff_eq,inter_comm (Iio N) E,inter_comm (Iio N) Eᶜ,Nat.ncard_Iio] at he
    simp only [Set.partialDensity,Set.inter_univ,Set.univ_inter,Nat.ncard_Iio]
    have : (N:ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    field_simp
    have hc : ((E ∩ Iio N).ncard : ℝ) + (Eᶜ ∩ Iio N).ncard = N := by exact_mod_cast he
    linarith
  have good : {j : ℕ | ∀ h : ℕ, 0<h →
      Irreducible ((jonesSumPolynomial (m^h) j).map (Int.castRingHom ℚ))} = Eᶜ := by
    ext j
    simp [E,jonesExceptionalDegrees]
  rw [good]
  have ht : Tendsto (fun N => 1-E.partialDensity univ N) atTop (𝓝 (1-(0:ℝ))) :=
    tendsto_const_nhds.sub hE
  change Tendsto (fun N => Eᶜ.partialDensity univ N) atTop (𝓝 1)
  rw [sub_zero] at ht
  exact ht.congr' (hsum.mono fun _ he => he.symm)

#print axioms jones_powered_exceptional_windows
#print axioms jones_all_powers_density_one

end CunninghamChain
