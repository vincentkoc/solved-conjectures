import Erdos722CyclotomicDevelopment
import Erdos722HananiFour
import Mathlib.Algebra.IsPrimePow
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.NumberTheory.PrimesCongruentOne

/-!
# Wilson's cyclotomic existence theorem for pair designs

For each block size, sufficiently large prime powers congruent to one
modulo `k*(k-1)` support a Steiner pair design. At prime-power orders
coprime to the block size this gives exactly the pinned divisibility test.
-/

namespace Erdos722.Cyclotomy
open Finset Filter

def cutoff (k : ℕ) :=
  let C := 4*(k.choose 2)
  k*(4*C^2*C^k)*C^k

theorem field_design (F : Type*) [Field F] [Fintype F] (k : ℕ) (hk : 2≤k)
    (hbig : cutoff k < Fintype.card F) (hdiv : k*(k-1) ∣ Fintype.card F-1) :
    ∃ H : Finset (Finset (Fin (Fintype.card F))), H.IsBlockDesign 2 k := by
  obtain ⟨a,ha⟩ := hdiv
  have hq := Fintype.one_lt_card (α := F)
  have hm := Nat.choose_pos hk
  have ha' : 0<a := by by_contra! h; simp [show a=0 by omega] at ha; omega
  have he : Fintype.card F = k.choose 2*(2*a)+1 := by rw [← mul_assoc,twice_choose]; omega
  obtain ⟨H,hi,hn,hc⟩ := exists_even_subgroup F _ _ hm ha' he
  obtain ⟨f,hf,hr⟩ := rainbow_starter k H hi (hi ▸ hm) (by simpa [hi,cutoff] using hbig)
  exact (develop_starter H hi hn hc f hf hr).some.design

theorem prime_power_design {q k : ℕ} (hq : IsPrimePow q) (hk : 2≤k)
    (hbig : cutoff k < q) (hdiv : k*(k-1) ∣ q-1) :
    ∃ H : Finset (Finset (Fin q)), H.IsBlockDesign 2 k := by
  obtain ⟨p,d,hp,hd,rfl⟩ := (isPrimePow_nat_iff _).mp hq
  have : Fact p.Prime := ⟨hp⟩
  let F := GaloisField p d
  let : Fintype F := Fintype.ofFinite _
  have hc : Fintype.card F = p^d := (Nat.card_eq_fintype_card).symm.trans (GaloisField.card p d hd.ne')
  rw [← hc]
  exact field_design F k hk (hc ▸ hbig) (hc ▸ hdiv)

private theorem modulus_of_binom {q k : ℕ} (hq : 1≤q) (hcop : k.Coprime q)
    (h : ∀ i<2, (k-i).choose (2-i) ∣ (q-i).choose (2-i)) : k*(k-1) ∣ q-1 := by
  have h1 : k-1 ∣ q-1 := by simpa using h 1 (by decide)
  have h0 : k.choose 2 ∣ q.choose 2 := by simpa using h 0 (by decide)
  have hp : (q-1).Coprime q := (Nat.coprime_self_sub_left hq).mpr (by simp)
  have hcop' : (k*(k-1)).Coprime q := hcop.mul_left (hp.of_dvd_left h1)
  apply hcop'.dvd_of_dvd_mul_left
  simpa only [twice_choose] using Nat.mul_dvd_mul_right h0 2

theorem coprime_prime_power_iff {q k : ℕ} (hq : IsPrimePow q) (hk : 2≤k)
    (hcop : k.Coprime q) (hbig : cutoff k < q) :
    (∃ H : Finset (Finset (Fin q)), H.IsBlockDesign 2 k) ↔
      ∀ i<2, (k-i).choose (2-i) ∣ (q-i).choose (2-i) := by
  have hq' : 1≤q := by omega
  constructor
  · rintro ⟨H,hH⟩ i hi
    exact Quartet.design_divisibility hH (by omega) (by omega)
  · exact fun h => prime_power_design hq hk hbig (modulus_of_binom hq' hcop h)

/-- At all sufficiently large prime orders, the original divisibility
hypotheses for rank two are necessary and sufficient for every block size. -/
theorem prime_order_spectrum (k : ℕ) (hk : 2<k) :
    ∀ᶠ p : ℕ in atTop, p.Prime →
      ((∃ H : Finset (Finset (Fin p)), H.IsBlockDesign 2 k) ↔
        ∀ i<2, (k-i).choose (2-i) ∣ (p-i).choose (2-i)) := by
  filter_upwards [eventually_gt_atTop (max (cutoff k) k)] with p h hp
  have hkp := (le_max_right ..).trans_lt h
  have hcop := (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega : 0<k) hkp)).symm
  exact coprime_prime_power_iff hp.isPrimePow hk.le hcop ((le_max_left ..).trans_lt h)

theorem frequently_prime_design (k : ℕ) (hk : 2≤k) :
    ∃ᶠ p : ℕ in atTop, p.Prime ∧ ∃ H : Finset (Finset (Fin p)), H.IsBlockDesign 2 k := by
  rw [frequently_atTop]
  intro N
  have hn : 0<k*(k-1) := Nat.mul_pos (by omega) (by omega)
  obtain ⟨p,hp,hlt,hm⟩ := Nat.exists_prime_gt_modEq_one (max N (cutoff k)) hn.ne'
  refine ⟨p,((le_max_left ..).trans_lt hlt).le,hp,prime_power_design hp.isPrimePow hk
    ((le_max_right ..).trans_lt hlt) ?_⟩
  exact (Nat.modEq_iff_dvd' hp.one_le).mp hm.symm

#print axioms field_design
#print axioms prime_power_design
#print axioms coprime_prime_power_iff
#print axioms prime_order_spectrum
#print axioms frequently_prime_design

end Erdos722.Cyclotomy
