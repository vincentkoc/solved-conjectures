import Erdos722CyclotomicSpectrum
import Erdos722DerivedAffine

/-!
# The spectrum at prime-power orders for prime-power block sizes

When both powers use the same prime, the point replication condition
forces the block exponent to divide the order exponent. The affine
construction handles every such order. Distinct characteristics use
the cyclotomic construction.
-/

namespace Erdos722.Cyclotomy
open Filter

private theorem exponent_dvd {p a e : ℕ} (hp : p.Prime) (h1 : p^a-1 ∣ p^e-1) : a ∣ e := by
  have h := Nat.gcd_eq_left_iff_dvd.mpr h1
  rw [Nat.pow_sub_one_gcd_pow_sub_one] at h
  apply Nat.gcd_eq_left_iff_dvd.mp
  apply Nat.pow_right_injective hp.two_le
  change p^(a.gcd e)=p^a
  have := Nat.one_le_pow (a.gcd e) p hp.pos
  have := Nat.one_le_pow a p hp.pos
  omega

theorem same_characteristic_iff (p a e : ℕ) [hp : Fact p.Prime] (ha : 0<a) (he : 0<e) :
    (∃ H : Finset (Finset (Fin (p^e))), H.IsBlockDesign 2 (p^a)) ↔ a ∣ e := by
  constructor
  · rintro ⟨H,hH⟩
    have h1 : p^a-1 ∣ p^e-1 := by
      simpa using Quartet.design_divisibility hH (i := 1) (Nat.one_le_pow _ _ hp.out.pos) (by decide)
    exact exponent_dvd hp.out h1
  · rintro ⟨d,hd⟩
    have hpos : 0<d := by by_contra! hz; simp [show d=0 by omega] at hd; omega
    rw [hd,pow_mul]
    exact affine_power_design p a d ha hpos

/-- For prime-power block size and order, the bound is required only
when their characteristics differ. -/
theorem prime_powers_iff {k q : ℕ} (hk : IsPrimePow k) (hq : IsPrimePow q)
    (hbig : k.Coprime q → cutoff k < q) :
    (∃ H : Finset (Finset (Fin q)), H.IsBlockDesign 2 k) ↔
      ∀ i<2, (k-i).choose (2-i) ∣ (q-i).choose (2-i) := by
  obtain ⟨p,a,hp,ha,rfl⟩ := (isPrimePow_nat_iff _).mp hk
  obtain ⟨s,e,hs,he,rfl⟩ := (isPrimePow_nat_iff _).mp hq
  have hk2 : 2≤p^a := (hp.two_le.trans (Nat.le_self_pow ha.ne' _))
  by_cases h : p=s
  · subst s
    have : Fact p.Prime := ⟨hp⟩
    have hq1 := Nat.one_le_pow e p hp.pos
    constructor
    · rintro ⟨H,hH⟩ i hi
      exact Quartet.design_divisibility hH (by omega) (by omega)
    · intro hab
      have h1 : p^a-1 ∣ p^e-1 := by simpa using hab 1 (by decide)
      exact (same_characteristic_iff p a e ha he).mpr (exponent_dvd hp h1)
  · have hcop := Nat.coprime_pow_primes a e hp hs h
    exact coprime_prime_power_iff ((isPrimePow_nat_iff _).mpr ⟨s,e,hs,he,rfl⟩) hk2 hcop (hbig hcop)

theorem prime_power_order_spectrum (k : ℕ) (hk : IsPrimePow k) :
    ∀ᶠ q : ℕ in atTop, IsPrimePow q →
      ((∃ H : Finset (Finset (Fin q)), H.IsBlockDesign 2 k) ↔
        ∀ i<2, (k-i).choose (2-i) ∣ (q-i).choose (2-i)) := by
  filter_upwards [eventually_gt_atTop (cutoff k)] with q hq h
  exact prime_powers_iff hk h (fun _ => hq)

#print axioms same_characteristic_iff
#print axioms prime_powers_iff
#print axioms prime_power_order_spectrum

end Erdos722.Cyclotomy
