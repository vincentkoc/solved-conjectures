import research.arxiv.«2211.10788».LucasFibonacciOddCubes

/-! Representations by the norm of the quadratic order of discriminant −11. -/

namespace Arxiv.«2211.10788»

local instance : Fact (Nat.Prime 11) := ⟨by decide⟩

namespace ElevenRing

open QuadraticAlgebra

private theorem norm_associated {a b : ElevenRing} (h : Associated a b) : a.norm = b.norm := by
  obtain ⟨u, rfl⟩ := h
  have hu := Int.isUnit_iff.mp (u.isUnit.map (QuadraticAlgebra.norm : ElevenRing →* ℤ))
  have hn := norm_nonneg' (u : ElevenRing)
  rw [map_mul]
  rcases hu with h | h
  · simp [h]
  · omega

private theorem star_divides {a b : ElevenRing} (h : a ∣ b) : star a ∣ star b :=
  (starRingEnd ElevenRing).map_dvd h

private theorem norm_divides {a b : ElevenRing} (h : a ∣ b) : a.norm ∣ b.norm :=
  QuadraticAlgebra.norm.map_dvd h

private theorem coprime_parts {a b z : ElevenRing} (hz : IsCoprime z (star z))
    (ha : a ∣ z) (hb : b ∣ z) : IsCoprime a (star b) :=
  hz.mono ha (star_divides hb)

private theorem associated_of_norm {a b z : ElevenRing} (hz : IsCoprime z (star z))
    (ha : a ∣ z) (hb : b ∣ z) (h : a.norm = b.norm) : Associated a b := by
  have he := congrArg (algebraMap ℤ ElevenRing) h
  rw [algebraMap_norm_eq_mul_star, algebraMap_norm_eq_mul_star] at he
  exact associated_of_dvd_dvd
    ((coprime_parts hz ha hb).dvd_of_dvd_mul_right (he ▸ dvd_mul_right a (star a)))
    ((coprime_parts hz hb ha).dvd_of_dvd_mul_right (he.symm ▸ dvd_mul_right b (star b)))

/-- Every positive rational divisor of the norm of an element coprime to its
conjugate is the norm of a divisor of that element. -/
theorem exists_factor_norm {z : ElevenRing} (hz : IsCoprime z (star z))
    {d : ℕ} (hd : (d : ℤ) ∣ z.norm) : ∃ s : ElevenRing, s ∣ z ∧ s.norm = d := by
  classical
  have hdiv := (algebraMap ℤ ElevenRing).map_dvd hd
  change (d : ElevenRing) ∣ algebraMap ℤ ElevenRing z.norm at hdiv
  rw [algebraMap_norm_eq_mul_star] at hdiv
  obtain ⟨s,t,hs,ht,he⟩ := exists_dvd_and_dvd_of_dvd_mul hdiv
  have he' : (d : ElevenRing) = s*t := he
  have hstar : star s * star t = s*t := by
    have := congrArg star he'
    simpa [mul_comm] using this.symm.trans (by simpa using he')
  have htz : star t ∣ z := by simpa using star_divides ht
  have st : s ∣ star t := (coprime_parts hz hs hs).dvd_of_dvd_mul_left
    (hstar.symm ▸ dvd_mul_right s t)
  have ts : star t ∣ s := (by simpa using coprime_parts hz htz htz : IsCoprime (star t) t)
    |>.dvd_of_dvd_mul_right (hstar ▸ dvd_mul_left (star t) (star s))
  have hnorm := norm_associated (associated_of_dvd_dvd st ts)
  rw [QuadraticAlgebra.norm_star] at hnorm
  have hsq := congrArg QuadraticAlgebra.norm he'
  rw [QuadraticAlgebra.norm_natCast, map_mul, ←hnorm] at hsq
  exact ⟨s,hs,by nlinarith [norm_nonneg' s, (by positivity : (0 : ℤ) ≤ d)]⟩

private def Corresponds (z w : ElevenRing) (d : ℤ) :=
  ∃ s u : ElevenRing, z = s*u ∧ s.norm = d ∧ Associated (s*star u) w

private theorem corresponds_of_norm {z w : ElevenRing} (hz : IsCoprime z (star z))
    (hp : z ≠ 0) (h : w.norm = z.norm) :
    ∃ d : ℕ, (d : ℤ) ∣ z.norm ∧ Corresponds z w d := by
  classical
  have hw : w ∣ z * star z := by
    rw [← algebraMap_norm_eq_mul_star, ← h, algebraMap_norm_eq_mul_star]
    exact dvd_mul_right ..
  obtain ⟨s,t,hs,ht,hst⟩ := exists_dvd_and_dvd_of_dvd_mul hw
  obtain ⟨u,hu⟩ := hs
  have hs0 : s ≠ 0 := by intro hs; simp [hs] at hu; exact hp hu
  have hnorm : t.norm = u.norm := by
    rw [hst,hu,map_mul,map_mul] at h
    exact mul_left_cancel₀ (norm_pos' hs0).ne' h
  have hz' : IsCoprime (star z) (star (star z)) := by simpa using hz.symm
  have huc : star u ∣ star z := star_divides (hu ▸ dvd_mul_left ..)
  have htu := associated_of_norm hz' ht huc (by simpa using hnorm)
  have hs' : (s.norm.natAbs : ℤ) = s.norm := by rw [Int.natCast_natAbs, abs_of_nonneg (norm_nonneg' _)]
  refine ⟨s.norm.natAbs, by rw [hs']; exact norm_divides (hu ▸ dvd_mul_right ..), s, u, hu, hs'.symm, ?_⟩
  rw [hst]
  exact htu.symm.mul_left s

private theorem corresponds_unique_value {z w₁ w₂ : ElevenRing} {d : ℤ}
    (hz : IsCoprime z (star z)) (hp : z ≠ 0)
    (h₁ : Corresponds z w₁ d) (h₂ : Corresponds z w₂ d) : Associated w₁ w₂ := by
  obtain ⟨s,u,hu,hs,hw₁⟩ := h₁
  obtain ⟨t,v,hv,ht,hw₂⟩ := h₂
  have hst := associated_of_norm hz (hu ▸ dvd_mul_right ..) (hv ▸ dvd_mul_right ..) (hs.trans ht.symm)
  have hs0 : s ≠ 0 := by intro h; simp [h] at hu; exact hp hu
  have he := congrArg QuadraticAlgebra.norm (hu.symm.trans hv)
  rw [map_mul,map_mul,← hs.trans ht.symm] at he
  have huv := associated_of_norm hz (hu ▸ dvd_mul_left ..) (hv ▸ dvd_mul_left ..)
    (mul_left_cancel₀ (norm_pos' hs0).ne' he)
  exact hw₁.symm.trans ((hst.mul_mul (huv.map (starRingEnd ElevenRing))).trans hw₂)

private theorem corresponds_unique_divisor {z w : ElevenRing} {d e : ℤ} (hz : IsCoprime z (star z))
    (hd : Corresponds z w d) (he : Corresponds z w e) : d = e := by
  obtain ⟨s,u,hu,hs,hw₁⟩ := hd
  obtain ⟨t,v,hv,ht,hw₂⟩ := he
  have h := hw₁.trans hw₂.symm
  have st : s ∣ t := (coprime_parts hz (hu ▸ dvd_mul_right ..) (hv ▸ dvd_mul_left ..)).dvd_of_dvd_mul_right
    ((dvd_mul_right s (star u)).trans h.dvd)
  have ts : t ∣ s := (coprime_parts hz (hv ▸ dvd_mul_right ..) (hu ▸ dvd_mul_left ..)).dvd_of_dvd_mul_right
    ((dvd_mul_right t (star v)).trans h.dvd')
  exact hs.symm.trans ((norm_associated (associated_of_dvd_dvd st ts)).trans ht)

private theorem associated_iff_sign (a b : ElevenRing) :
    Associated a b ↔ b = a ∨ b = -a := by
  constructor
  · rintro ⟨u,rfl⟩
    have hi := unit_im_zero u
    have hn : (u : ElevenRing).norm = 1 := by
      have hu := Int.isUnit_iff.mp (u.isUnit.map (QuadraticAlgebra.norm : ElevenRing →* ℤ))
      have hp := norm_nonneg' (u : ElevenRing)
      omega
    rw [norm_def, hi] at hn
    have hu : (u : ElevenRing).re = 1 ∨ (u : ElevenRing).re = -1 := by
      have : ((u : ElevenRing).re - 1) * ((u : ElevenRing).re + 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h|h <;> omega
    rcases hu with h|h
    · left
      rw [show (u : ElevenRing) = 1 from QuadraticAlgebra.ext h hi, mul_one]
    · right
      rw [show (u : ElevenRing) = -1 by ext <;> simp [h,hi], mul_neg, mul_one]
  · rintro (rfl|rfl)
    · rfl
    · exact ⟨-1,by simp⟩

private theorem corresponds_of_associated {z a b : ElevenRing} {d : ℤ}
    (h : Corresponds z a d) (hab : Associated a b) : Corresponds z b d := by
  obtain ⟨s,u,he,hn,hw⟩ := h
  exact ⟨s,u,he,hn,hw.trans hab⟩

/-- For an element coprime to its conjugate, choosing one of the two unit signs
above each positive divisor parametrizes every representation of its norm. -/
theorem card_norm_representations {z : ElevenRing} {n : ℕ} (hn : 0 < n)
    (hz : IsCoprime z (star z)) (h : z.norm = n) :
    Nat.card {w : ElevenRing // w.norm = n} = 2 * n.divisors.card := by
  classical
  let S := {w : ElevenRing // w.norm = n}
  have h0 : z ≠ 0 := by rintro rfl; simp at h; omega
  have each (d : n.divisors) : ∃ w : S, Corresponds z w d.val := by
    have hd := Nat.dvd_of_mem_divisors d.property
    obtain ⟨s,hs,hs'⟩ := exists_factor_norm hz (d := d.val) (by rw [h]; exact_mod_cast hd)
    obtain ⟨u,hu⟩ := hs
    refine ⟨⟨s * star u, ?_⟩,s,u,hu,hs',Associated.refl _⟩
    rw [map_mul, QuadraticAlgebra.norm_star, ← map_mul,← hu,h]
  let rep := fun d : n.divisors => (each d).choose
  have spec (d : n.divisors) : Corresponds z (rep d) d.val := (each d).choose_spec
  let signed (d : n.divisors) (b : Bool) : S :=
    if b then rep d else ⟨-(rep d).val, by simpa using (rep d).property⟩
  have assoc (d : n.divisors) (b : Bool) : Associated (rep d).val (signed d b).val := by
    rw [associated_iff_sign]
    cases b <;> simp [signed]
  have inj : Function.Injective (fun q : (↥n.divisors) × Bool => signed q.1 q.2) := by
    rintro ⟨d,b⟩ ⟨e,c⟩ hh
    change signed d b = signed e c at hh
    have h' := corresponds_of_associated (spec d) (assoc d b)
    rw [hh] at h'
    have de := corresponds_unique_divisor hz h' (corresponds_of_associated (spec e) (assoc e c))
    have : d = e := Subtype.ext (by exact_mod_cast de)
    subst e
    have distinct : (rep d).val ≠ -(rep d).val := by
      intro hneg
      have hr := congrArg QuadraticAlgebra.re hneg
      have hi := congrArg QuadraticAlgebra.im hneg
      simp only [re_neg, im_neg] at hr hi
      have hw : (rep d).val = 0 := QuadraticAlgebra.ext (by change _ = 0; omega) (by change _ = 0; omega)
      have hval := (rep d).property
      rw [hw,QuadraticAlgebra.norm_zero] at hval
      omega
    cases b <;> cases c
    · rfl
    · exact (distinct (congrArg Subtype.val hh).symm).elim
    · exact (distinct (congrArg Subtype.val hh)).elim
    · rfl
  have surj : Function.Surjective (fun q : (↥n.divisors) × Bool => signed q.1 q.2) := by
    intro w
    obtain ⟨d,hd,hw⟩ := corresponds_of_norm hz h0 (w.property.trans h.symm)
    let e : n.divisors := ⟨d,Nat.mem_divisors.mpr ⟨by rw [h] at hd; exact_mod_cast hd,hn.ne'⟩⟩
    have ha := (associated_iff_sign _ _).mp (corresponds_unique_value hz h0 (spec e) hw)
    rcases ha with ha|ha
    · exact ⟨⟨e,true⟩,Subtype.ext ha.symm⟩
    · exact ⟨⟨e,false⟩,Subtype.ext ha.symm⟩
  have he := Nat.card_congr (Equiv.ofBijective _ ⟨inj,surj⟩)
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := ↥n.divisors), Fintype.card_coe, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at he
  exact he.symm.trans (Nat.mul_comm ..)

private theorem coprime_conjugate {z : ElevenRing} (hc : IsCoprime z.re z.im)
    (h11 : ¬(11 : ℤ) ∣ z.norm) : IsCoprime z (star z) := by
  have htr : IsCoprime (2*z.re+z.im) z.norm := by
    apply isCoprime_of_prime_dvd
    · rintro ⟨_,he⟩; exact h11 (he ▸ dvd_zero _)
    intro p hp htrace hn
    have hf := four_norm z
    obtain ⟨r,hr⟩ := htrace
    obtain ⟨s,hs⟩ := hn
    rw [hr,hs] at hf
    have hy' : p ∣ 11*z.im^2 := ⟨4*s-p*r^2, by linear_combination -hf⟩
    have hy : p ∣ z.im := by
      rcases hp.dvd_or_dvd hy' with h | h
      · have eq := hp.associated_of_dvd (by decide : Prime (11 : ℤ)) h
        exact False.elim (h11 (eq.dvd'.trans ⟨s,hs⟩))
      · exact hp.dvd_of_dvd_pow h
    apply hp.not_isUnit (hc.isUnit_of_dvd' _ hy)
    apply hp.dvd_of_dvd_pow (n := 2)
    obtain ⟨k,hk⟩ := hy
    refine ⟨s-k*(z.re+3*z.im), ?_⟩
    rw [norm_def,hk] at hs
    rw [hk]
    linear_combination hs
  have hsum : algebraMap ℤ ElevenRing (2*z.re+z.im) = z+star z := by ext <;> simp; ring
  obtain ⟨a,b,he⟩ := htr.map (algebraMap ℤ ElevenRing)
  rw [hsum,algebraMap_norm_eq_mul_star] at he
  exact ⟨a+b*star z,a,by linear_combination he⟩

private theorem prime_norm_primitive {z : ElevenRing} {p : ℕ} (hp : p.Prime) (hn : z.norm = p) :
    IsCoprime z.re z.im := by
  apply isCoprime_of_prime_dvd
  · rintro ⟨hx,hy⟩
    rw [norm_def,hx,hy] at hn
    have := hp.pos
    simp at hn
    omega
  intro q hq hx hy
  obtain ⟨x,hx⟩ := hx
  obtain ⟨y,hy⟩ := hy
  apply hq.not_isUnit
  apply (Nat.prime_iff_prime_int.mp hp).squarefree
  refine ⟨x*x + x*y + 3*y*y,?_⟩
  rw [←hn,norm_def,hx,hy]
  ring

private theorem split_prime_norm {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2)
    (hsq : IsSquare (-11 : ZMod p)) : ∃ z : ElevenRing, z.norm = p := by
  have := hp.two_le
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨r,hr⟩ := hsq
  let x : ℤ := r.val
  have hx : (x : ZMod p) = r := by simp [x]
  have hx0 : (p : ℤ) ∣ x^2+11 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp (by
    push_cast
    rw [hx,pow_two,← hr]
    ring)
  let v : ElevenRing := ⟨x-1,2⟩
  have hv : v.norm = x^2+11 := by dsimp [v,norm_def]; ring
  have hprod : (p : ElevenRing) ∣ v*star v := by
    rw [← algebraMap_norm_eq_mul_star,hv]
    exact (algebraMap ℤ ElevenRing).map_dvd hx0
  have imag {w : ElevenRing} (h : (p : ElevenRing) ∣ w) : (p : ℤ) ∣ w.im := by
    obtain ⟨c,rfl⟩ := h
    exact ⟨c.im,by simp⟩
  have hnot : ¬Prime (p : ElevenRing) := by
    intro hi
    have htwo : (p : ℤ) ∣ 2 := by
      rcases hi.dvd_or_dvd hprod with h|h
      · exact imag h
      · simpa [v] using imag h
    have : p ∣ 2 := by exact_mod_cast htwo
    have := Nat.le_of_dvd (by decide : 0 < 2) this
    omega
  have hpu : ¬IsUnit (p : ElevenRing) := by
    intro hu
    have h := Int.isUnit_iff.mp (hu.map (QuadraticAlgebra.norm : ElevenRing →* ℤ))
    rw [QuadraticAlgebra.norm_natCast] at h
    rcases h with h|h <;> nlinarith [show (2 : ℤ) ≤ p by exact_mod_cast hp.two_le]
  obtain hi|⟨a,b,ha,hb,hab⟩ := irreducible_or_factor hpu
  · exact False.elim (hnot hi.prime)
  have hprod := congrArg QuadraticAlgebra.norm hab
  rw [QuadraticAlgebra.norm_natCast,map_mul] at hprod
  have hpos : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have ha' : 1 < a.norm := by
    have hn := norm_nonneg' a
    have h1 : a.norm ≠ 1 := fun h => ha (isUnit_iff_norm_isUnit.mpr (by rw [h]; exact isUnit_one))
    by_contra! h
    have := show a.norm = 0 by omega
    rw [this,zero_mul] at hprod
    nlinarith
  have hb' : 1 < b.norm := by
    have hn := norm_nonneg' b
    have h1 : b.norm ≠ 1 := fun h => hb (isUnit_iff_norm_isUnit.mpr (by rw [h]; exact isUnit_one))
    by_contra! h
    have := show b.norm = 0 by omega
    rw [this,mul_zero] at hprod
    nlinarith
  have habs : (a.norm.natAbs : ℤ) = a.norm := by simp [abs_of_nonneg (norm_nonneg' _)]
  have hd : a.norm.natAbs ∣ p^2 := by
    exact_mod_cast (show (a.norm.natAbs : ℤ) ∣ (p : ℤ)^2 by rw [habs]; exact ⟨_,hprod⟩)
  obtain ⟨k,hk,he⟩ := (Nat.dvd_prime_pow hp).mp hd
  have he' := congrArg (fun i : ℕ => (i : ℤ)) he
  push_cast at he'
  rw [abs_of_nonneg (norm_nonneg' _)] at he'
  refine ⟨a,?_⟩
  interval_cases k
  · rw [pow_zero] at he'
    omega
  · simpa only [pow_one] using he'
  · nlinarith [mul_pos (by omega : 0<a.norm) (by omega : 0<b.norm-1)]

private theorem neg_eleven_square {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2)
    (hn : (p : ZMod 11) ≠ 0) (hq : IsSquare (p : ZMod 11)) : IsSquare (-11 : ZMod p) := by
  let : Fact p.Prime := ⟨hp⟩
  have hne : p ≠ 11 := by rintro rfl; exact hn (by decide)
  have hp11 : ¬p ∣ 11 := by
    intro hd
    exact ((Nat.dvd_prime (by decide : Nat.Prime 11)).mp hd).elim hp.ne_one hne
  have hneg : ((-11 : ℤ) : ZMod p) ≠ 0 := by
    have h := (ZMod.natCast_eq_zero_iff (11 : ℕ) p).not.mpr hp11
    simpa using h
  have h₁ := (legendreSym.eq_one_iff' 11 hn).mpr hq
  suffices h : legendreSym p (-11) = 1 by simpa using (legendreSym.eq_one_iff p hneg).mp h
  rw [legendreSym.at_neg h2]
  obtain h|h : p%4 = 1 ∨ p%4 = 3 := by
    have := hp.mod_two_eq_one_iff_ne_two.mpr h2
    omega
  · rw [ZMod.χ₄_nat_one_mod_four h,one_mul]
    exact (legendreSym.quadratic_reciprocity_one_mod_four h (by decide : 11 ≠ 2)).symm.trans h₁
  · rw [ZMod.χ₄_nat_three_mod_four h,neg_one_mul]
    exact (legendreSym.quadratic_reciprocity_three_mod_four h (by decide : 11%4=3)).symm.trans h₁

end ElevenRing

/-- Number of ordered integral representations by the principal form of discriminant −11. -/
noncomputable def elevenFormCount (n : ℕ) :=
  Nat.card {p : ℤ × ℤ // p.1^2 + p.1*p.2 + 3*p.2^2 = n}

private theorem eleven_count_coords (n : ℕ) :
    elevenFormCount n = Nat.card {z : ElevenRing // z.norm = n} := by
  apply Nat.card_congr
  exact {
    toFun := fun ⟨⟨x,y⟩,he⟩ => ⟨⟨x,y⟩,by rw [QuadraticAlgebra.norm_def]; dsimp; linear_combination he⟩
    invFun := fun ⟨z,he⟩ => ⟨(z.re,z.im), by rw [QuadraticAlgebra.norm_def] at he; dsimp; linear_combination he⟩
    left_inv := fun ⟨⟨_,_⟩,_⟩ => rfl
    right_inv := fun ⟨_,_⟩ => rfl }

/-- A primitively represented positive integer coprime to 11 has exactly twice
as many ordered representations as positive divisors. -/
theorem primitive_eleven_form_count {n : ℕ} (hn : 0<n) (h11 : ¬11∣n)
    {x y : ℤ} (hc : IsCoprime x y) (he : x^2+x*y+3*y^2 = n) :
    elevenFormCount n = 2*n.divisors.card := by
  let z : ElevenRing := ⟨x,y⟩
  have h : z.norm = n := by rw [QuadraticAlgebra.norm_def]; dsimp [z]; linear_combination he
  have hn' : ¬(11 : ℤ) ∣ z.norm := by rw [h]; exact_mod_cast h11
  rw [eleven_count_coords]
  exact ElevenRing.card_norm_representations hn (ElevenRing.coprime_conjugate hc hn') h

private theorem two_divisors {n : ℕ} (hn : 0<n) : n.divisors.card = 2 ↔ n.Prime := by
  constructor
  · intro h
    have h1 : n ≠ 1 := by rintro rfl; simp at h
    have hs : ({1,n} : Finset ℕ) ⊆ n.divisors := by
      intro d hd
      simp only [Finset.mem_insert,Finset.mem_singleton] at hd
      rcases hd with rfl|rfl <;> simp [Nat.mem_divisors,hn.ne']
    have he := Finset.eq_of_subset_of_card_le hs (by simp [h, Ne.symm h1])
    apply Nat.prime_def.mpr
    refine ⟨by omega,fun d hd => ?_⟩
    have hm := Nat.mem_divisors.mpr ⟨hd,hn.ne'⟩
    rw [←he] at hm
    simpa using hm
  · intro hp
    simp [hp.divisors, Ne.symm hp.ne_one]

/-- A positive integer which is a nonzero square modulo 11 is prime exactly when
it has a primitive representation and its principal form has four representations in all. -/
theorem prime_iff_four_eleven_representations {n : ℕ} (hn : 0<n)
    (h₀ : (n : ZMod 11) ≠ 0) (hsq : IsSquare (n : ZMod 11)) :
    n.Prime ↔ (∃ x y : ℤ, IsCoprime x y ∧ x^2+x*y+3*y^2 = n) ∧ elevenFormCount n = 4 := by
  have h11 := (ZMod.natCast_eq_zero_iff n 11).not.mp h₀
  constructor
  · intro hp
    have h2 : n ≠ 2 := by rintro rfl; exact (by decide : ¬IsSquare (2 : ZMod 11)) hsq
    obtain ⟨z,hz⟩ := ElevenRing.split_prime_norm hp h2 (ElevenRing.neg_eleven_square hp h2 h₀ hsq)
    have hc := ElevenRing.prime_norm_primitive hp hz
    have he : z.re^2+z.re*z.im+3*z.im^2 = n := by
      rw [QuadraticAlgebra.norm_def] at hz
      linear_combination hz
    refine ⟨⟨_,_,hc,he⟩,?_⟩
    rw [primitive_eleven_form_count hn h11 hc he,(two_divisors hn).mpr hp]
  · rintro ⟨⟨x,y,hc,he⟩,hr⟩
    rw [primitive_eleven_form_count hn h11 hc he] at hr
    exact (two_divisors hn).mp (by omega)

private theorem upper_eleven_residue (n : ℕ) : (lucasFibonacciSum n : ZMod 11) = 4^n := by
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more n h₀ h₁ =>
    rw [lucas_fibonacci_sum_recurrence,Nat.cast_add,h₁,h₀,pow_succ,pow_succ]
    linear_combination -(4 : ZMod 11)^n * (by decide : (4 : ZMod 11)*4 = 4+1)

/-- An exact prime-value test for the pinned upper sequence at every index. -/
theorem lucasFibonacciSum_prime_iff_four_representations (n : ℕ) :
    (lucasFibonacciSum n).Prime ↔
      (∃ x y : ℤ, IsCoprime x y ∧ x^2+x*y+3*y^2 = lucasFibonacciSum n) ∧
      elevenFormCount (lucasFibonacciSum n) = 4 := by
  have h₀ : (lucasFibonacciSum n : ZMod 11) ≠ 0 := by rw [upper_eleven_residue]; exact pow_ne_zero _ (by decide)
  have hn : 0 < lucasFibonacciSum n := Nat.pos_of_ne_zero (fun h => h₀ (by simp [h]))
  apply prime_iff_four_eleven_representations hn h₀
  rw [upper_eleven_residue]
  exact ⟨2^n,by rw [←mul_pow]; norm_num⟩

private theorem four_mul_eleven_form_count (n : ℕ) : elevenFormCount (4*n) = elevenFormCount n := by
  classical
  rw [eleven_count_coords,eleven_count_coords]
  let := ElevenRing.instEuclideanDomain
  have hn2 : QuadraticAlgebra.norm (2 : ElevenRing) = 4 := rfl
  let F (w : {z : ElevenRing // z.norm = n}) : {z : ElevenRing // z.norm = 4*n} :=
    ⟨2*w.val,by rw [map_mul,w.property,hn2]⟩
  have inj : Function.Injective F := by
    intro a b h
    apply Subtype.ext
    exact mul_left_cancel₀ (by decide : (2 : ElevenRing) ≠ 0) (congrArg Subtype.val h)
  have surj : Function.Surjective F := by
    rintro ⟨z,he⟩
    have hm := congrArg (Int.castRingHom (ZMod 2)) he
    rw [QuadraticAlgebra.norm_def] at hm
    have hz : (z.re : ZMod 2)*(z.re : ZMod 2) + (z.re : ZMod 2)*z.im + z.im*z.im = 0 := by
      simpa [Int.cast_ofNat, show (3 : ZMod 2) = 1 by decide, show (4 : ZMod 2) = 0 by decide,
        sub_neg_eq_add] using hm
    have hb := (by decide : ∀ x y : ZMod 2, x*x+x*y+y*y = 0 → x=0 ∧ y=0) _ _ hz
    obtain ⟨x,hx⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp hb.1
    obtain ⟨y,hy⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp hb.2
    let w : ElevenRing := ⟨x,y⟩
    have hzw : z=2*w := by
      apply QuadraticAlgebra.ext <;> simp [w,hx,hy,show (2 : ElevenRing).re=2 from rfl,
        show (2 : ElevenRing).im=0 from rfl]
    have hw : w.norm = n := by
      rw [hzw,map_mul] at he
      rw [hn2] at he
      omega
    exact ⟨⟨w,hw⟩,Subtype.ext hzw.symm⟩
  exact (Nat.card_congr (Equiv.ofBijective F ⟨inj,surj⟩)).symm

private theorem odd_form_count {n : ℕ} (hn : 0<n) (h11 : ¬11∣n) {a b : ℤ}
    (hc : IsCoprime a b) (he : 3*a^2+2*a*b+4*b^2 = n) :
    elevenFormCount n = 2*(if 2∣n then n/4 else n).divisors.card := by
  have p2 : Prime (2 : ℤ) := by decide
  by_cases ha : (2 : ℤ) ∣ a
  · obtain ⟨s,hs⟩ := ha
    have q : b^2+b*s+3*s^2 = (n : ℤ)/4 := by
      rw [hs] at he
      have h : 4*(b^2+b*s+3*s^2)=(n : ℤ) := by linear_combination he
      omega
    have hm : 4*(n/4)=n := by
      rw [hs] at he
      have h : 4*(b^2+b*s+3*s^2)=(n : ℤ) := by linear_combination he
      omega
    have hqn : b^2+b*s+3*s^2 = ((n/4 : ℕ) : ℤ) := by exact_mod_cast q
    have hp := hc.symm.of_isCoprime_of_dvd_right (hs ▸ dvd_mul_left ..)
    rw [if_pos (show 2∣n by omega), ← hm, four_mul_eleven_form_count]
    rw [Nat.mul_div_cancel_left _ (by decide : 0<4)]
    apply primitive_eleven_form_count (by omega) _ hp hqn
    intro h
    exact h11 (hm ▸ dvd_mul_of_dvd_right h 4)
  · have hp := (p2.irreducible.coprime_iff_not_dvd.mpr ha).mul_left hc.symm
    have he' : (2*b)^2+(2*b)*a+3*a^2 = n := by linear_combination he
    have hodd : ¬2∣n := by
      rintro ⟨t,ht⟩
      have ha' : (a : ZMod 2) ≠ 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd a 2).not.mpr ha
      have hz := congrArg (Int.castRingHom (ZMod 2)) he
      rw [ht] at hz
      have : (a : ZMod 2)^2 = 0 := by
        simpa [show (2 : ZMod 2)=0 by decide, show (3 : ZMod 2)=1 by decide,
          show (4 : ZMod 2)=0 by decide] using hz
      exact (pow_ne_zero 2 ha') this
    rw [if_neg hodd]
    exact primitive_eleven_form_count hn h11 hp he'

/-- At odd indices on either diagonal, every representation is accounted for by the
divisors of the odd part. An even value at such an index is four times an odd integer. -/
theorem odd_hosoya_representation_counts (n : ℕ) :
    ∀ v ∈ ({lucasFibonacciSum (2*n+1),lowerNeighborAtAddTwo (2*n+1)} : Finset ℕ),
      elevenFormCount v = 2*(if 2∣v then v/4 else v).divisors.card := by
  have low (m : ℕ) : (lowerNeighborAtAddTwo m : ZMod 11) = 2*8^m := by
    induction m using Nat.twoStepInduction with
    | zero => decide
    | one => decide
    | more m h₀ h₁ =>
      have hh : lowerNeighborAtAddTwo (m+2) = lowerNeighborAtAddTwo (m+1) + lowerNeighborAtAddTwo m := by
        simp only [lowerNeighborAtAddTwo,Nat.fib_add_two]
        omega
      rw [hh,Nat.cast_add,h₁,h₀,pow_succ (8 : ZMod 11) (m+1),pow_succ]
      linear_combination -(2*(8 : ZMod 11)^m) * (by decide : (8 : ZMod 11)*8=8+1)
  obtain ⟨⟨a,b,hc,hu⟩,⟨c,d,hd,hv⟩⟩ := odd_hosoya_form_witnesses n
  intro v hm
  rcases (by simpa using hm : v = lucasFibonacciSum (2*n+1) ∨ v = lowerNeighborAtAddTwo (2*n+1)) with rfl|rfl
  · have h11 : (lucasFibonacciSum (2*n+1) : ZMod 11) ≠ 0 := by rw [upper_eleven_residue]; exact pow_ne_zero _ (by decide)
    exact odd_form_count (Nat.pos_of_ne_zero (fun h => h11 (by simp [h])))
      ((ZMod.natCast_eq_zero_iff _ 11).not.mp h11) hc hu
  · have h11 : (lowerNeighborAtAddTwo (2*n+1) : ZMod 11) ≠ 0 := by
      rw [low]
      exact mul_ne_zero (by decide) (pow_ne_zero _ (by decide))
    exact odd_form_count (Nat.pos_of_ne_zero (fun h => h11 (by simp [h])))
      ((ZMod.natCast_eq_zero_iff _ 11).not.mp h11) hd hv

/-- The four representations at upper index thirteen are all imprimitive.
This composite term shows why the primitive witness in the prime test is necessary. -/
theorem four_representations_at_composite_upper_value :
    lucasFibonacciSum 13 = 1076 ∧ elevenFormCount 1076 = 4 ∧
      ¬∃ x y : ℤ, IsCoprime x y ∧ x^2+x*y+3*y^2 = 1076 := by
  have hu : lucasFibonacciSum 13 = 1076 := by decide
  have hc := odd_hosoya_representation_counts 6 (lucasFibonacciSum 13) (by simp)
  change elevenFormCount (lucasFibonacciSum 13) = _ at hc
  rw [hu] at hc
  have hp : Nat.Prime 269 := by norm_num
  have hr : elevenFormCount 1076 = 4 := by
    convert hc using 1
    change 4 = 2 * (269 : ℕ).divisors.card
    simp [hp.divisors]
  refine ⟨hu,hr,?_⟩
  intro h
  have hiff := lucasFibonacciSum_prime_iff_four_representations 13
  rw [hu] at hiff
  exact (by norm_num : ¬Nat.Prime 1076) (hiff.mpr ⟨h,hr⟩)

#print axioms four_representations_at_composite_upper_value
#print axioms odd_hosoya_representation_counts
#print axioms ElevenRing.exists_factor_norm
#print axioms ElevenRing.card_norm_representations
#print axioms primitive_eleven_form_count
#print axioms prime_iff_four_eleven_representations
#print axioms lucasFibonacciSum_prime_iff_four_representations

end Arxiv.«2211.10788»
