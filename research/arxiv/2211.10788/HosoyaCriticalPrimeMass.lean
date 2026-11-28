import HosoyaPrimePowerUniformMass
import HosoyaThirteenCriticalClass

/-! A matching square-root lower bound at thirteen on the original prime-index sequence. -/

namespace Arxiv.«2211.10788».LocalPower
open CongruenceClosure ProgressionClosure AlmostPrimeClosure Filter Topology CunninghamChain.PrimeMass

/-- At levels 13^(2b+4) some target takes a prime class of modulus 364·13^b.
Thus a bound uniform over targets cannot replace the square-root exponent
by any larger exponent in the decay rate. -/
theorem critical_thirteen_mass (b : ℕ) :
    ∃ y : ℤ, ∀ᶠ s : ℝ in 𝓝[>] 1, (1:ℝ)/(728*13^b) ≤
      (s-1)*mass (primeIndexHits 0 1 (13^(2*(b+2))) y) s := by
  classical
  let L := 364*13^b
  have lp : 0<L := Nat.mul_pos (by decide) (pow_pos (by decide) _)
  let : NeZero L := ⟨lp.ne'⟩
  obtain ⟨a,bound,cop,constant⟩ := critical_thirteen b
  let y : ℤ := lucasFibonacciSum a
  let A := {n : ℕ | (n:ZMod L)=a}
  have lim := mass_progression (a:ZMod L) ((ZMod.isUnit_iff_coprime ..).mpr cop)
  have tp : 0<(L.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr lp
  have rl : (L.totient:ℝ)≤364*(13:ℝ)^b := by exact_mod_cast Nat.totient_le L
  have lb : (1:ℝ)/(728*13^b)<(L.totient:ℝ)⁻¹ := by
    rw [←one_div]
    exact one_div_lt_one_div_of_lt tp (by nlinarith [show 0<(13:ℝ)^b by positivity])
  refine ⟨y,?_⟩
  filter_upwards [lim.eventually_const_lt lb,self_mem_nhdsWithin] with s lower hs
  change 1<s at hs
  have inc (n : ℕ) (pr : n.Prime) (hit : n∈A) :
      n∈primeIndexHits 0 1 (13^(2*(b+2))) y := by
    have mod := (ZMod.natCast_eq_natCast_iff n a L).mp hit
    change n%L=a%L at mod
    have res : n%L=a := mod.trans (Nat.mod_eq_of_lt bound)
    have eq : a+L*(n/L)=n := by rw [←res]; exact Nat.mod_add_div ..
    have v := constant (n/L)
    rw [show a+364*13^b*(n/L)=n from eq] at v
    refine ⟨pr,?_⟩
    simpa [Hit,y] using v
  exact lower.le.trans (mul_le_mul_of_nonneg_left (prime_mass_mono inc hs) (sub_nonneg.mpr hs.le))

#print axioms critical_thirteen_mass

end Arxiv.«2211.10788».LocalPower
