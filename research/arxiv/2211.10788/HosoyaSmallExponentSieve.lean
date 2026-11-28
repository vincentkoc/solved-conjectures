import HosoyaExponentCertificates

/-! Split-prime certificates for the odd prime exponents below 101. -/

namespace Arxiv.«2211.10788».HosoyaAuxiliaryPrime

-- Each row gives (q, T, r, k, plus, minus) as in SplitRow.Valid.
private def exponentRows : ℕ → List SplitRow
  | 5 => [⟨211, 7, 86, 42, [1], [], by norm_num⟩]
  | 7 => [⟨211, 7, 86, 30, [1], [], by norm_num⟩]
  | 11 => [⟨19801, 22, 6315, 1800, [1], [], by norm_num⟩]
  | 13 => [⟨79, 13, 13, 6, [1], [], by norm_num⟩]
  | 17 => [⟨3571, 17, 189, 210, [1], [], by norm_num⟩]
  | 19 => [⟨229, 19, 34, 12, [1], [], by norm_num⟩]
  | 23 => [⟨139, 23, 17, 6, [1], [], by norm_num⟩]
  | 29 => [⟨26449, 76, 3090, 912, [1], [], by norm_num⟩]
  | 31 => [⟨1427, 28, 100, 46, [1], [], by norm_num⟩]
  | 37 => [⟨146521, 37, 39098, 3960, [1], [], by norm_num⟩]
  | 41 => [⟨12301, 25, 415, 300, [1], [], by norm_num⟩]
  | 43 => [⟨20641, 40, 3164, 480, [1, 2819, 9343], [], by norm_num⟩,
      ⟨1549, 129, 365, 36, [1, 25, 62, 164, 1464], [], by norm_num⟩]
  | 47 => [⟨95881, 85, 14606, 2040, [1], [], by norm_num⟩]
  | 53 => [⟨107, 12, 15, 2, [1], [], by norm_num⟩]
  | 59 => [⟨709, 59, 162, 12, [1, 27, 604], [], by norm_num⟩,
      ⟨8969, 59, 2919, 152, [1, 4087, 4885], [], by norm_num⟩]
  | 61 => [⟨123953, 146, 53816, 2032, [1], [], by norm_num⟩]
  | 67 => [⟨269, 134, 77, 4, [1, 16, 136, 180], [16], by norm_num⟩,
      ⟨1609, 268, 352, 24, [1, 320, 357, 994, 1384], [], by norm_num⟩]
  | 71 => [⟨952111, 149, 64452, 13410, [1, 43975, 257844, 525416, 893328], [], by norm_num⟩,
      ⟨2564521, 215, 723670, 36120, [1, 19187, 263099, 622986, 744300, 1148811, 1532987], [], by norm_num⟩]
  | 73 => [⟨374929, 428, 126684, 5136, [1], [], by norm_num⟩]
  | 79 => [⟨317, 106, 149, 4, [1, 165, 244], [], by norm_num⟩,
      ⟨1668481, 158, 366134, 21120, [1, 460222, 495811], [], by norm_num⟩]
  | 83 => [⟨167, 56, 41, 2, [1], [], by norm_num⟩]
  | 89 => [⟨39161, 55, 14200, 440, [1, 17894, 25879], [], by norm_num⟩,
      ⟨3739, 89, 596, 42, [1, 788, 1637, 1783, 2399], [], by norm_num⟩]
  | 97 => [⟨3299, 97, 152, 34, [1], [], by norm_num⟩]
  | _ => []

private def ValidCover (p : ℕ) := (∀ s ∈ exponentRows p, s.Valid p) ∧
  ∀ i : Fin p, (∀ s ∈ exponentRows p, s.Allows i.val) → i.val=0

private instance (p : ℕ) : Decidable (ValidCover p) := inferInstanceAs (Decidable (_ ∧ _))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem certificates : ∀ j : Fin 101, j.val.Prime → 5 ≤ j.val → ValidCover j.val := by
  decide +kernel

/-- Every prime exponent from 5 through 97 is excluded at every positive multiple of six. -/
theorem fib_small_prime_power_excluded {p n : ℕ} (hp : p.Prime) (h₅ : 5 ≤ p) (hu : p < 101)
    (hn : 0 < n) (hd : 6 ∣ n) (y : ℤ) : y^p+1 ≠ 11*(Nat.fib n:ℤ)^2 := by
  obtain ⟨valid,cover⟩ := certificates ⟨p,hu⟩ hp h₅
  exact fib_power_excluded_of_rows (hp.odd_of_ne_two (by omega)) (by omega)
    (exponentRows p) valid cover hn hd y

#print axioms fib_small_prime_power_excluded

end Arxiv.«2211.10788».HosoyaAuxiliaryPrime
