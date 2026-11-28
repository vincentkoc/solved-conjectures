import HosoyaPrimeFibreCriterion

/-! A quadratic obstruction to critical fibres and contrasting prime-parameter progressions. -/

namespace Arxiv.«2211.10788».LocalPower

/-- The Pell identity excludes every critical reduced class when the indicated
signed constant is a nonsquare modulo p. -/
theorem uniform_rate_of_nonsquare (p r d : ℕ) [Fact p.Prime] (hd : 0<d)
    (nonsquare : ¬IsSquare ((-220 : ZMod p)*(-1)^(r+d))) : UniformFibreRate p r d := by
  apply (prime_fibre_criterion p r d hd).mpr
  let E := fibreReturn p d
  let a := (Nat.fib (d*E)).factorization p
  obtain ⟨_,even,_,ha,_,_⟩ := fibreReturn_spec p d hd
  rintro ⟨i,_,unit,root⟩
  obtain ⟨k,hk⟩ := Nat.coprime_two_left.mp ((unit.of_dvd_right even.two_dvd).symm)
  let n := r+d*i
  have div : p∣(coordinate n).natAbs :=
    (dvd_pow_self p (show a≠0 by dsimp [a,E]; omega)).trans root
  have zero : (coordinate n:ZMod p)=0 := (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mpr
    ((Int.natAbs_dvd_natAbs).mp (by simpa only [Int.natAbs_natCast] using div))
  have sign : (-1:ℤ)^n=(-1:ℤ)^(r+d) := by
    rw [show n=r+d+2*(d*k) by dsimp [n]; rw [hk]; ring,pow_add,(even_two.mul_right _).neg_one_pow,mul_one]
  have pell : coordinate n ^ 2 = 5*(lucasFibonacciSum n : ℤ)^2+44*(-1:ℤ)^n :=
    PrimeObstruction.upper_signed_pell n
  rw [sign] at pell
  have eq := congrArg (fun t : ℤ => (t:ZMod p)) pell
  push_cast at eq
  rw [zero] at eq
  apply nonsquare
  refine ⟨5*(lucasFibonacciSum n:ZMod p),?_⟩
  linear_combination 5*eq

#print axioms uniform_rate_of_nonsquare

private def fastCoordinate (n : ℕ) : ℤ :=
  2*((2*Nat.fastFib (n+1)+Nat.fastFib (n+1+2):ℕ):ℤ)
    - ((2*Nat.fastFib n+Nat.fastFib (n+2):ℕ):ℤ)

private lemma coordinate_fast (n : ℕ) : coordinate n=fastCoordinate n := by
  simp only [fastCoordinate,Nat.fastFib_eq]
  rfl

/-- Moving the offset by one changes the rate at seven. -/
theorem fibre_rate_seven :
    UniformFibreRate 7 0 1 ∧ ¬UniformFibreRate 7 1 1 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  refine ⟨uniform_rate_of_nonsquare 7 0 1 (by decide) (by decide +kernel),?_⟩
  have hf : 7^2∣Nat.fib (1*56) ∧ ¬7^3∣Nat.fib (1*56) := by rw [←Nat.fastFib_eq]; decide +kernel
  apply fun u => (uniform_rate_iff_no_critical_phase (E:=56) (a:=2) (by decide) (by decide)
    (by decide) (by decide) hf.1 hf.2).mp u ?_
  exact ⟨15,by decide,by decide,by rw [coordinate_fast]; decide +kernel⟩

#print axioms fibre_rate_seven

/-- Both 17 and 23 have sharp square-root concentration on the original progression. -/
theorem no_full_rate_seventeen_twenty_three :
    ¬UniformFibreRate 17 0 1 ∧ ¬UniformFibreRate 23 0 1 := by
  let : Fact (Nat.Prime 17) := ⟨by decide⟩
  let : Fact (Nat.Prime 23) := ⟨by decide⟩
  constructor
  · have hf : 17^2∣Nat.fib (1*306) ∧ ¬17^3∣Nat.fib (1*306) := by rw [←Nat.fastFib_eq]; decide +kernel
    intro u
    apply (uniform_rate_iff_no_critical_phase (E:=306) (a:=2) (by decide) (by decide)
      (by decide) (by decide) hf.1 hf.2).mp u
    exact ⟨185,by decide,by decide,by rw [coordinate_fast]; decide +kernel⟩
  · have hf : 23^2∣Nat.fib (1*552) ∧ ¬23^3∣Nat.fib (1*552) := by rw [←Nat.fastFib_eq]; decide +kernel
    intro u
    apply (uniform_rate_iff_no_critical_phase (E:=552) (a:=2) (by decide) (by decide)
      (by decide) (by decide) hf.1 hf.2).mp u
    exact ⟨473,by decide,by decide,by rw [coordinate_fast]; decide +kernel⟩

#print axioms no_full_rate_seventeen_twenty_three

/-- At thirteen the progression step alone changes the answer. -/
theorem fibre_rate_thirteen :
    ¬UniformFibreRate 13 0 1 ∧ UniformFibreRate 13 0 13 := by
  let : Fact (Nat.Prime 13) := ⟨by decide⟩
  constructor
  · have hf : 13^2∣Nat.fib (1*182) ∧ ¬13^3∣Nat.fib (1*182) := by rw [←Nat.fastFib_eq]; decide +kernel
    intro u
    apply (uniform_rate_iff_no_critical_phase (E:=182) (a:=2) (by decide) (by decide)
      (by decide) (by decide) hf.1 hf.2).mp u
    exact ⟨23,by decide,by decide,by rw [coordinate_fast]; decide +kernel⟩
  · have hf : 13^3∣Nat.fib (13*182) ∧ ¬13^4∣Nat.fib (13*182) := by rw [←Nat.fastFib_eq]; decide +kernel
    apply (uniform_rate_iff_no_critical_phase (E:=182) (a:=3) (by decide) (by decide)
      (by decide) (by decide) hf.1 hf.2).mpr
    rintro ⟨i,lt,unit,hit⟩
    have table : ∀ i : Fin 182, (i:ℕ).Coprime 182 → ¬ 13^3∣(fastCoordinate (13*i)).natAbs := by
      decide +kernel
    exact table ⟨i,lt⟩ unit (by simpa only [zero_add,coordinate_fast] using hit)

#print axioms fibre_rate_thirteen

end Arxiv.«2211.10788».LocalPower
