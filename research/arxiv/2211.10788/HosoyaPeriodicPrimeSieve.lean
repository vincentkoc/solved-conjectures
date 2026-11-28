import HosoyaDivisorWindowCounts

/-! The Fibonacci return modulus bounds prime values in every translated window. -/

namespace Arxiv.«2211.10788».DivisorWindows
open Finset

/-- The coprimality profile for a full Fibonacci return repeats with its index D. -/
theorem gcd_profile_periodic (D : ℕ) :
    Function.Periodic (fun n => (lucasFibonacciSum n).gcd (Nat.fib D)) D := by
  intro n
  apply Nat.dvd_antisymm
  · exact Nat.dvd_gcd ((lucasFibonacciSum_dvd_shift_iff (s:=n) (Nat.gcd_dvd_right _ _)).mp
      (Nat.gcd_dvd_left _ _)) (Nat.gcd_dvd_right _ _)
  · exact Nat.dvd_gcd ((lucasFibonacciSum_dvd_shift_iff (s:=n) (Nat.gcd_dvd_right _ _)).mpr
      (Nat.gcd_dvd_left _ _)) (Nat.gcd_dvd_right _ _)

/-- The count of candidates that survive all primes dividing F_D in one full period. -/
def survivors (D : ℕ) : ℕ := Nat.count (fun n => (lucasFibonacciSum n).Coprime (Nat.fib D)) D

/-- At most the coprime residues can be prime once the upper value exceeds F_D. -/
theorem period_prime_bound {D a : ℕ} (hD : 0<D) (large : Nat.fib D<lucasFibonacciSum a) :
    ((Ico a (a+D)).filter fun i => (lucasFibonacciSum i).Prime).card ≤ survivors D := by
  let f (i : ℕ) := (lucasFibonacciSum i).Coprime (Nat.fib D)
  have per : Function.Periodic f D := fun i => congrArg (· = 1) (gcd_profile_periodic D i)
  rw [survivors,←Nat.filter_Ico_card_eq_of_periodic a D f per]
  apply card_le_card
  intro i hi
  obtain ⟨hi,hp⟩ := mem_filter.mp hi
  refine mem_filter.mpr ⟨hi,?_⟩
  have mono : Monotone lucasFibonacciSum := fun _ _ h => Nat.add_le_add
    (Nat.mul_le_mul_left 2 (Nat.fib_mono h)) (Nat.fib_mono (by omega))
  apply hp.coprime_iff_not_dvd.mpr
  intro dvd
  have := Nat.le_of_dvd (Nat.fib_pos.mpr hD) dvd
  have := large.trans_le (mono (mem_Ico.mp hi).1)
  omega

private def rows : List (ℕ × ℕ × ℕ) :=
  [(2,3,1),(3,4,3),(5,5,2),(7,8,4),(19,18,12),(23,24,5),(31,30,23),
   (71,70,45),(83,84,48),(181,90,36),(631,630,95)]

private def certified (v : ℕ × ℕ × ℕ) : Prop :=
  0<v.2.1 ∧ v.2.1 ∣ 2520 ∧ v.1.Prime ∧ v.1≤631 ∧ v.1 ∣ Nat.fastFib v.2.1 ∧
    v.1 ∣ 2*Nat.fastFib v.2.2+Nat.fastFib (v.2.2+2)

private instance (v : ℕ × ℕ × ℕ) : Decidable (certified v) := by unfold certified; infer_instance

set_option maxRecDepth 12000 in
private lemma good {v : ℕ × ℕ × ℕ} (h : v ∈ rows) : certified v := by
  have cert : rows.all (fun x => decide (certified x))=true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp cert v h)

/-- Residues avoiding the eleven specified prime divisors. -/
def avoidsSieve2520 (n : ℕ) : Bool := rows.all fun v => n%v.2.1 != v.2.2

private lemma prime_passes_sieve {n : ℕ} (big : 12≤n) (hp : (lucasFibonacciSum n).Prime) :
    avoidsSieve2520 (n%2520) = true := by
  apply List.all_eq_true.mpr
  intro v hv
  obtain ⟨p,R,t⟩ := v
  obtain ⟨hR,hd,hp',lim,ret,hit⟩ := good hv
  change (n%2520%R != t)=true
  simp only [Nat.mod_mod_of_dvd _ hd,bne_iff_ne]
  intro he
  simp only [Nat.fastFib_eq] at ret hit
  change p ∣ Nat.fib R at ret
  change p ∣ lucasFibonacciSum t at hit
  have ret' : p ∣ Nat.fib (R*(n/R)) := ret.trans (Nat.fib_dvd _ _ (dvd_mul_right ..))
  have dv := (lucasFibonacciSum_dvd_shift_iff (s:=t) ret').mpr hit
  have eq := Nat.mod_add_div n R
  rw [he] at eq
  rw [eq] at dv
  have same := (Nat.prime_dvd_prime_iff_eq hp' hp).mp dv
  have mono : Monotone lucasFibonacciSum := fun _ _ h => Nat.add_le_add
    (Nat.mul_le_mul_left 2 (Nat.fib_mono h)) (Nat.fib_mono (by omega))
  have bigger : 631<lucasFibonacciSum n :=
    (by decide : 631<lucasFibonacciSum 12).trans_le (mono big)
  change p≤631 at lim
  omega

private def tally : ℕ → ℕ
  | 0 => 0
  | j+1 => tally j + if avoidsSieve2520 j then 1 else 0

private lemma tally_eq (N : ℕ) : Nat.count (fun n => avoidsSieve2520 n=true) N=tally N := by
  induction N with
  | zero => rfl
  | succ N ih => rw [Nat.count_succ,tally,ih]

set_option maxRecDepth 12000 in
/-- Exactly 613 of 2520 residues survive the eleven certified divisor primes. -/
theorem sieve_residues_2520 : Nat.count (fun n => avoidsSieve2520 n=true) 2520=613 := by
  rw [tally_eq]
  decide +kernel

/-- Every 2520 consecutive indices starting at or beyond 6 give at most
613 prime upper values. This is an unconditional bound on actual prime indices. -/
theorem prime_count_2520 {a : ℕ} (ha : 6≤a) :
    ((Ico a (a+2520)).filter fun i => (lucasFibonacciSum i).Prime).card ≤ 613 := by
  let f (i : ℕ) := avoidsSieve2520 (i%2520)=true
  have per : Function.Periodic f 2520 := fun n => by simp [f,Nat.add_mod_right]
  have h : Nat.count f 2520=613 := by
    rw [←sieve_residues_2520,Nat.count_eq_card_filter_range,Nat.count_eq_card_filter_range]
    apply congrArg Finset.card
    apply filter_congr
    intro i hi
    simp [f,Nat.mod_eq_of_lt (mem_range.mp hi)]
  rw [←h,←Nat.filter_Ico_card_eq_of_periodic a 2520 f per]
  apply card_le_card
  intro i hi
  obtain ⟨hi,prime⟩ := mem_filter.mp hi
  refine mem_filter.mpr ⟨hi,?_⟩
  by_cases late : 12 ≤ i
  · exact prime_passes_sieve late prime
  · have small : ∀ z : Fin 12, 6 ≤ z.val → (lucasFibonacciSum z.val).Prime →
        avoidsSieve2520 (z.val%2520)=true := by decide +kernel
    exact small ⟨i,by omega⟩ (ha.trans (mem_Ico.mp hi).1) prime

#print axioms gcd_profile_periodic
#print axioms period_prime_bound
#print axioms sieve_residues_2520
#print axioms prime_count_2520

end Arxiv.«2211.10788».DivisorWindows
