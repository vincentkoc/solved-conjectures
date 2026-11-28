import HosoyaPrimePowerIndexClasses
import HosoyaPrimeIndexTestMass

/-! Uniform prime-index mass bounds along powers of any one prescribed prime. -/

namespace Arxiv.«2211.10788».LocalPower
open CongruenceClosure ProgressionClosure AlmostPrimeClosure Finset Filter Topology CunninghamChain.PrimeMass

private def cls {m : ℕ} (u : (ZMod m)ˣ) : Set ℕ := {n | (n:ZMod m)=u}

private theorem prime_cover {p d : ℕ} (hp : p.Prime) (hd : 0<d) :
    ∃ a : ℕ, ∀ (r b : ℕ) (y : ℤ), ∃ u v : (ZMod (p^b))ˣ,
      ∀ n∈primeIndexHits r d (p^(2*(a+b+1))) y,
        n∈cls u ∨ n∈cls v ∨ n≤ max 2 p := by
  classical
  obtain ⟨a,classes⟩ := two_index_classes hp hd
  refine ⟨a,?_⟩
  intro r b y
  let P := fun n : ℕ => n.Prime ∧ max 2 p<n ∧ Hit d r (p^(2*(a+b+1))) y n
  have odd (n) (h : P n) : n%2=1 := by
    apply (Nat.Prime.eq_two_or_odd h.1).resolve_left
    have := h.2.1
    omega
  have unit (n) (h : P n) : IsUnit (n:ZMod (p^b)) := by
    apply (ZMod.isUnit_iff_coprime n (p^b)).mpr
    exact ((Nat.coprime_primes h.1 hp).mpr (by have := h.2.1; omega)).pow_right b
  by_cases any : ∃ n, P n
  · obtain ⟨i,j,pi,pj,hits⟩ := classes r b y P
      (fun n m pn pm => (odd n pn).trans (odd m pm).symm) (fun _ h => h.2.2) any
    obtain ⟨u,hu⟩ := unit i pi
    obtain ⟨v,hv⟩ := unit j pj
    refine ⟨u,v,fun n hn => ?_⟩
    by_cases small : n≤ max 2 p
    · exact Or.inr (Or.inr small)
    · rcases hits n ⟨hn.1,by omega,hn.2⟩ with eq|eq
      · exact Or.inl (((ZMod.natCast_eq_natCast_iff ..).mpr eq).trans hu.symm)
      · exact Or.inr (Or.inl (((ZMod.natCast_eq_natCast_iff ..).mpr eq).trans hv.symm))
  · refine ⟨1,1,fun n hn => Or.inr (Or.inr (by
      by_contra! big
      exact any ⟨n,hn.1,big,hn.2⟩))⟩

/-- At a fixed prime and step, two reduced parameter classes suffice.
The mass bound is simultaneous over offsets and target residues. -/
theorem prime_power_hit_mass {p d : ℕ} (hp : p.Prime) (hd : 0<d) :
    ∃ a : ℕ, ∀ (b : ℕ) {ε : ℝ}, 0<ε →
      ∀ᶠ s : ℝ in 𝓝[>] 1, ∀ (r : ℕ) (y : ℤ),
        (s-1)*mass (primeIndexHits r d (p^(2*(a+b+1))) y) s < 2/((p^b).totient:ℝ)+ε := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨a,cov⟩ := prime_cover hp hd
  refine ⟨a,?_⟩
  intro b ε ep
  let M := p^b
  let G := Set.Iic (max 2 p)
  have top (u : (ZMod M)ˣ) : ∀ᶠ s : ℝ in 𝓝[>] 1,
      (s-1)*mass (cls u) s < (M.totient:ℝ)⁻¹+ε/3 :=
    (mass_progression (u:ZMod M) u.isUnit).eventually_lt_const (by linarith)
  have all : ∀ᶠ s : ℝ in 𝓝[>] 1, ∀ u : (ZMod M)ˣ,
      (s-1)*mass (cls u) s < (M.totient:ℝ)⁻¹+ε/3 := Filter.eventually_all.mpr top
  have tail := (finite_mass_tendsto (Set.finite_Iic (max 2 p))).eventually_lt_const
    (show (0:ℝ)<ε/3 by positivity)
  filter_upwards [all,tail,self_mem_nhdsWithin] with s bounds tiny hs
  change 1<s at hs
  intro r y
  obtain ⟨u,v,hcover⟩ := cov r b y
  let P := primeIndexHits r d (p^(2*(a+b+1))) y
  have cmp := mass_le_cover {()} (fun _ => cls u) P (cls v) G (by
    intro n hn _
    rcases hcover n hn with h|h|h
    · exact Or.inl ⟨(),mem_singleton_self _,h⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)) hs
  simp only [sum_singleton] at cmp
  have bound := mul_le_mul_of_nonneg_left cmp (sub_nonneg.mpr hs.le)
  change (s-1)*mass G s<ε/3 at tiny
  change (s-1)*mass P s < 2/(M.totient:ℝ)+ε
  rw [div_eq_mul_inv]
  linarith only [bound,bounds u,bounds v,tiny]

/-- Monotonicity only needs set inclusion on primes, since the mass vanishes elsewhere. -/
theorem prime_mass_mono {A B : Set ℕ} (incl : ∀ n, n.Prime → n∈A → n∈B) {s : ℝ} (hs : 1<s) :
    mass A s≤ mass B s := by
  classical
  apply (summable_weight A hs).tsum_le_tsum _ (summable_weight B hs)
  intro n
  apply div_le_div_of_nonneg_right _ (by positivity)
  by_cases h : n.Prime ∧ n∈A
  · simp [weight,h,incl n h.1 h.2]
  · rw [weight,if_neg h]
    exact weight_nonneg ..

/-- The prime-power exponent and the neighborhood of 1 work for every
larger exponent, all offsets and all integer candidates at once. -/
theorem uniform_single_prime_tests {p d : ℕ} (hp : p.Prime) (hd : 0<d) {ε : ℝ} (ep : 0<ε) :
    ∃ H : ℕ, ∀ᶠ s : ℝ in 𝓝[>] 1, ∀ h≥H, ∀ (r : ℕ) (y : ℤ),
      (s-1)*mass (primeIndexHits r d (p^h) y) s<ε := by
  obtain ⟨a,upper⟩ := prime_power_hit_mass hp hd
  obtain ⟨b : ℕ,grow⟩ := exists_nat_gt (4/ε)
  have pos : 0<((p^(b+1)).totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr (pow_pos hp.pos _)
  have lb : b≤(p^(b+1)).totient := by
    rw [Nat.totient_prime_pow_succ hp]
    exact (show b<2^b from Nat.lt_two_pow_self).le.trans ((Nat.pow_le_pow_left hp.two_le b).trans
      (Nat.le_mul_of_pos_right _ (by have := hp.one_lt; omega)))
  have below : 2/((p^(b+1)).totient:ℝ)<ε/2 := by
    apply (div_lt_iff₀ pos).mpr
    have gr : 4/ε < ((p^(b+1)).totient:ℝ) := grow.trans_le (by exact_mod_cast lb)
    have big := (div_lt_iff₀ ep).mp gr
    linarith
  refine ⟨2*(a+(b+1)+1),?_⟩
  filter_upwards [upper (b+1) (show 0<ε/2 by positivity),self_mem_nhdsWithin] with s low hs
  change 1<s at hs
  intro h hh r y
  have cmp := prime_mass_mono (A:=primeIndexHits r d (p^h) y) (B:=primeIndexHits r d (p^(2*(a+(b+1)+1))) y)
    (fun n _ hit => ⟨hit.1,hit.2.of_dvd (by exact_mod_cast pow_dvd_pow p hh)⟩) hs
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left cmp (sub_nonneg.mpr hs.le))
    ((low r y).trans (by linarith))

#print axioms uniform_single_prime_tests

#print axioms prime_power_hit_mass

end Arxiv.«2211.10788».LocalPower
