import ThetaMissingPrimePowers

/-! Chebyshev packing for distinct prime bases of omitted powers. -/
namespace Arxiv.«2501.03234».ThetaPrimePowerPacking
open Finset Filter ThetaMissingPrimePowers
noncomputable section

private lemma packing {D : ℝ} (hD : 0<D) {B : ℕ} (hB : 2≤B)
    (H : ∀ n : ℕ,B≤n → (Nat.primeCounting n:ℝ)≤D*n/Real.log n) (f : ℕ → ℕ)
    (s : Finset ℕ) (Y : ℕ) (hY : B≤Y) (hs : ∀ p∈s,p.Prime ∧ p≤f p ∧ Y≤f p) :
    ∑ p∈s,1/(f p:ℝ)^2≤4*D/((Y:ℝ)*Real.log Y) := by
  classical
  induction s using Finset.strongInductionOn generalizing Y with | _ s ih
  have hy : (1:ℝ)<Y := by exact_mod_cast (show 2≤Y by omega)
  have hl := Real.log_pos hy
  rcases s.eq_empty_or_nonempty with he|hne
  · subst s; simp; positivity
  let v := s.image f
  let M := v.min' (hne.image f)
  have hm (p) (hp : p∈s) : M≤f p := min'_le _ _ (mem_image_of_mem _ hp)
  obtain ⟨p₀,h₀,he⟩ := mem_image.mp (min'_mem v (hne.image f))
  change f p₀=M at he
  have hYM : Y≤M := he ▸ (hs p₀ h₀).2.2
  have hM : (1:ℝ)<M := hy.trans_le (by exact_mod_cast hYM)
  have hMpos : 0<(M:ℝ) := by linarith
  have hL := Real.log_pos hM
  have hlog : Real.log M≤Real.log (2*M:ℕ) :=
    Real.log_le_log hMpos (by exact_mod_cast (show M≤2*M by omega))
  let l := s.filter (fun p => f p≤2*M)
  let u := s.filter (fun p => ¬f p≤2*M)
  have hstrict : u ⊂ s := Finset.ssubset_iff_subset_ne.mpr ⟨filter_subset ..,by
    intro hh; have hpu : p₀∈u := hh ▸ h₀
    have := (mem_filter.mp hpu).2; omega⟩
  have hu := ih u hstrict (2*M) (by omega) (by
    intro p hp; obtain ⟨h₁,h₂⟩ := mem_filter.mp hp
    exact ⟨(hs p h₁).1,(hs p h₁).2.1,(lt_of_not_ge h₂).le⟩)
  have hcard : l.card≤Nat.primeCounting (2*M) := by
    rw [←Nat.primesLE_card_eq_primeCounting]
    apply card_le_card; intro p hp; obtain ⟨h₁,h₂⟩ := mem_filter.mp hp
    exact Nat.mem_primesLE.mpr ⟨(hs p h₁).2.1.trans h₂,(hs p h₁).1⟩
  have hc := (show (l.card:ℝ)≤Nat.primeCounting (2*M) by exact_mod_cast hcard).trans (H _ (by omega))
  have hlow : ∑ p∈l,1/(f p:ℝ)^2≤(l.card:ℝ)/(M:ℝ)^2 := calc
    _ ≤ ∑ _∈l,1/(M:ℝ)^2 := sum_le_sum (fun p hp => one_div_le_one_div_of_le (sq_pos_of_pos hMpos)
      (pow_le_pow_left₀ hMpos.le (by exact_mod_cast hm p (mem_filter.mp hp).1) 2))
    _ = _ := by simp [div_eq_mul_inv]
  have hlt : ∑ p∈l,1/(f p:ℝ)^2≤2*D/((M:ℝ)*Real.log M) := by
    apply hlow.trans
    have hc' := hc.trans (div_le_div_of_nonneg_left (by positivity) hL hlog)
    rw [le_div_iff₀ hL,Nat.cast_mul,Nat.cast_ofNat] at hc'
    rw [div_le_div_iff₀ (sq_pos_of_pos hMpos) (mul_pos hMpos hL)]
    nlinarith only [mul_le_mul_of_nonneg_left hc' hMpos.le]
  have hut : ∑ p∈u,1/(f p:ℝ)^2≤2*D/((M:ℝ)*Real.log M) := by
    apply hu.trans; push_cast at hlog ⊢
    rw [div_le_div_iff₀ (mul_pos (by positivity) (hL.trans_le hlog)) (mul_pos hMpos hL)]
    nlinarith only [mul_le_mul_of_nonneg_left hlog (mul_nonneg (show 0≤4*D by positivity) hMpos.le)]
  have Hsum := sum_filter_add_sum_filter_not s (fun p => f p≤2*M) (fun p => 1/(f p:ℝ)^2)
  change (∑ p∈l,_) + (∑ p∈u,_) = _ at Hsum
  rw [←Hsum]
  apply (add_le_add hlt hut).trans
  calc
    _ = 4*D/((M:ℝ)*Real.log M) := by ring
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (mul_pos (by linarith) hl)
      (mul_le_mul (by exact_mod_cast hYM) (Real.log_le_log (by linarith) (by exact_mod_cast hYM)) hl.le hMpos.le)

/-- The first omitted power of each prime has total reciprocal-square mass
of order at most 1/(Y log Y), uniformly over all finite prime sets. -/
theorem omitted_powers : ∃ C : ℝ, 0<C ∧ ∀ᶠ Y : ℕ in atTop, ∀ s : Finset ℕ, (∀ p∈s,p.Prime) →
    ∑ p∈s,1/(firstMissingPower Y p:ℝ)^2≤C/((Y:ℝ)*Real.log Y) := by
  let D := Real.log 4+1
  have hD : 0<D := by dsimp [D]; positivity
  have hu := (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually (Chebyshev.eventually_primeCounting_le zero_lt_one)
  simp only [Nat.floor_natCast] at hu
  obtain ⟨B,hB⟩ := eventually_atTop.mp hu
  refine ⟨4*D,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (max B 2)] with Y hY
  intro s hs
  exact packing hD (le_max_right B 2) (fun n hn => hB n ((le_max_left ..).trans hn))
    _ s Y hY (fun p hp => ⟨hs p hp,missing_prime_le,(missing_large (hs p hp)).le⟩)

/-- All conductors missing from the least common multiple have this logarithmic gain. -/
theorem omitted_conductors : ∃ C : ℝ, 0<C ∧ ∀ᶠ Y : ℕ in atTop, ∀ s : Finset ℕ,
    (∀ q∈s,0<q ∧ ¬q∣Nat.lcmUpto Y) → ∑ q∈s,1/((q:ℝ)*q.totient)≤C/((Y:ℝ)*Real.log Y) := by
  obtain ⟨C,hC,H⟩ := omitted_powers
  refine ⟨12*C,by positivity,?_⟩
  filter_upwards [H] with Y hY
  intro s hs
  apply (missing_mass Y s hs).trans
  have H := hY (s.biUnion Nat.primeFactors) (fun p hp => by
    obtain ⟨q,_,hd⟩ := mem_biUnion.mp hp; exact Nat.prime_of_mem_primeFactors hd)
  exact (mul_le_mul_of_nonneg_left H (by norm_num : (0:ℝ)≤12)).trans_eq (by ring)

end
end Arxiv.«2501.03234».ThetaPrimePowerPacking
#print axioms Arxiv.«2501.03234».ThetaPrimePowerPacking.omitted_powers
#print axioms Arxiv.«2501.03234».ThetaPrimePowerPacking.omitted_conductors
