import HosoyaCriticalCompanionLifts
import HosoyaPrimePowerUniformMass
import HosoyaReducedClassMass

/-! Finite companion tests for the size of prime-parameter fibres of the upper sequence. -/

namespace Arxiv.«2211.10788».LocalPower

open ProgressionClosure AlmostPrimeClosure PrimeObstruction Finset Filter Topology CunninghamChain.PrimeMass

/-- An even return whose modulus contains the testing prime. -/
def fibreReturn (p d : ℕ) [Fact p.Prime] : ℕ :=
  Nat.lcm (Nat.lcm 2 p) (fibonacciStepRank (p^2) d)

/-- Search the reduced parameter residues of a single return. -/
def CriticalPhase (p r d E a : ℕ) : Prop :=
  ∃ i<E, i.Coprime E ∧ p^a ∣ (coordinate (r+d*i)).natAbs

theorem fibreReturn_spec (p d : ℕ) [Fact p.Prime] (hd : 0<d) :
    let E := fibreReturn p d
    let a := (Nat.fib (d*E)).factorization p
    0<E ∧ Even E ∧ p∣E ∧ 2≤a ∧ p^a∣Nat.fib (d*E) ∧ ¬p^(a+1)∣Nat.fib (d*E) := by
  have hp : p.Prime := Fact.out
  let e := fibonacciStepRank (p^2) d
  let E := fibreReturn p d
  have epos : 0<e := (Nat.find_spec (p:=fun t => 0<t ∧ p^2∣Nat.fib (d*t)) _).1
  have pos : 0<E := Nat.lcm_pos (Nat.lcm_pos (by decide) hp.pos) epos
  have nd : Nat.fib (d*E) ≠ 0 := (Nat.fib_pos.mpr (Nat.mul_pos hd pos)).ne'
  have base := (fibonacciStepRank_dvd_iff (p^2) d E).mp (Nat.dvd_lcm_right ..)
  exact ⟨pos,even_iff_two_dvd.mpr ((Nat.dvd_lcm_left 2 p).trans (Nat.dvd_lcm_left ..)),
    (Nat.dvd_lcm_right 2 p).trans (Nat.dvd_lcm_left ..),
    (hp.pow_dvd_iff_le_factorization nd).mp base,Nat.ordProj_dvd ..,
    Nat.pow_succ_factorization_not_dvd nd hp⟩

#print axioms fibreReturn_spec

private lemma regular_of_reduced {p r d E a i : ℕ} (pos : 0<E) (hf : p^a∣Nat.fib (d*E))
    (h : ¬CriticalPhase p r d E a) (cop : i.Coprime E) :
    ¬p^a ∣ (coordinate (r+d*i)).natAbs := by
  intro bad
  have cm : (i%E).Coprime E := by
    change (i%E).gcd E=1
    rw [←Nat.gcd_rec E i,Nat.gcd_comm]
    exact cop
  have shift : r+d*i=r+d*(i%E)+d*E*(i/E) := by
    conv_lhs => rw [←Nat.mod_add_div i E]
    ring
  have fib := hf.trans (Nat.fib_dvd (d*E) (d*E*(i/E)) (dvd_mul_right ..))
  rw [shift] at bad
  exact h ⟨i%E,Nat.mod_lt _ pos,cm,(companion_return_dvd fib _).mp bad⟩

private lemma regular_phase {p r d E a i : ℕ} (hp : p.Prime) (even : Even E)
    (ha : 2≤a) (hf : p^a∣Nat.fib (d*E)) (sharp : ¬p^(a+1)∣Nat.fib (d*E))
    (regular : ¬p^a∣(coordinate (r+d*i)).natAbs) (b t u : ℕ) {y : ℤ}
    (ht : Hit d r (p^(2*a+b)) y (i+2*E*t)) (hu : Hit d r (p^(2*a+b)) y (i+2*E*u)) :
    t ≡ u [MOD p^b] := by
  let s := r+d*i
  let v := (coordinate s).natAbs.factorization p
  have small : v<a := lt_of_not_ge fun h =>
    regular ((hp.pow_dvd_iff_le_factorization (Int.natAbs_ne_zero.mpr (coordinate_pos _).ne')).mpr h)
  have eq (k : ℕ) : r+d*(i+2*E*k)=s+2*(d*E)*k := by dsimp [s]; ring
  unfold Hit at ht hu
  rw [eq] at ht hu
  have cmp := ht.trans hu.symm
  push_cast at cmp
  apply (midpoint_class_congruence hp (even.mul_left d) ha hf sharp
    (regular_companion_order hp hf regular) b t u).mp
  exact cmp.of_dvd (pow_dvd_pow (p:ℤ) (show a+v+b≤2*a+b by omega))

/-- At a critical residue a reduced class of primes has a common value
at twice the lifting exponent. The integer target may depend on the level. -/
theorem critical_fibre_mass {p r d E a : ℕ} [Fact p.Prime] (pos : 0<E) (even : Even E)
    (ep : p∣E) (ha : 2≤a) (hf : p^a∣Nat.fib (d*E)) (sharp : ¬p^(a+1)∣Nat.fib (d*E))
    (crit : CriticalPhase p r d E a) (b : ℕ) :
    ∃ y : ℤ, ∀ᶠ x : ℝ in 𝓝[>] 1, (1:ℝ)/(4*E*p^b) ≤
      (x-1)*mass (primeIndexHits r d (p^(2*(a+b))) y) x := by
  classical
  have hp : p.Prime := Fact.out
  have hpp : 0<p := hp.pos
  let M := 2*E*p^b
  have mp : 0<M := by dsimp [M]; positivity
  let : NeZero M := ⟨mp.ne'⟩
  obtain ⟨i,lt,unit,root⟩ := crit
  obtain ⟨c,bound,cop,flat⟩ := flat_value_class even ep unit (by omega) ha hf sharp root b
  let y : ℤ := lucasFibonacciSum (r+d*c)
  let A := {n : ℕ | (n:ZMod M)=c}
  have lim := mass_progression (c:ZMod M) ((ZMod.isUnit_iff_coprime ..).mpr cop)
  have tp : 0<(M.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr mp
  have rl : (M.totient:ℝ)≤2*E*(p:ℝ)^b := by exact_mod_cast Nat.totient_le M
  have lb : (1:ℝ)/(4*E*p^b)<(M.totient:ℝ)⁻¹ := by
    rw [←one_div]
    apply one_div_lt_one_div_of_lt tp
    exact rl.trans_lt (by nlinarith [show 0<(E:ℝ)*(p:ℝ)^b by positivity])
  refine ⟨y,?_⟩
  filter_upwards [lim.eventually_const_lt lb,self_mem_nhdsWithin] with x lower hx
  change 1<x at hx
  have inc (n : ℕ) (pr : n.Prime) (member : n∈A) : n∈primeIndexHits r d (p^(2*(a+b))) y := by
    have eq := (ZMod.natCast_eq_natCast_iff n c M).mp member
    change n%M = c%M at eq
    have res := eq.trans (Nat.mod_eq_of_lt bound)
    have idx : c+M*(n/M)=n := by rw [←res]; exact Nat.mod_add_div ..
    exact ⟨pr,idx ▸ (flat (n/M) : Hit d r _ y (c+M*(n/M)))⟩
  exact lower.le.trans (mul_le_mul_of_nonneg_left (prime_mass_mono inc hx) (sub_nonneg.mpr hx.le))

#print axioms critical_fibre_mass

private lemma regular_cover {p r d E a : ℕ} [Fact p.Prime] (pos : 0<E) (even : Even E)
    (ha : 2≤a) (hf : p^a∣Nat.fib (d*E)) (sharp : ¬p^(a+1)∣Nat.fib (d*E))
    (regular : ¬CriticalPhase p r d E a) (b : ℕ) (y : ℤ) :
    let M := 2*E*p^b
    ∃ S : Finset (ZMod M)ˣ, S.card≤2*E ∧ ∀ n∈primeIndexHits r d (p^(2*a+b)) y,
      n∈represented S ∨ n≤M := by
  classical
  have hp : p.Prime := Fact.out
  let P := 2*E
  let M := P*p^b
  have pp : 0<P := by dsimp [P]; omega
  have mp : 0<M := Nat.mul_pos pp (pow_pos hp.pos b)
  let U (i : Fin P) (t : ℕ) := M < (i:ℕ)+P*t ∧ i+P*t∈primeIndexHits r d (p^(2*a+b)) y
  have cls (i : Fin P) : ∃ v : (ZMod M)ˣ, ∀ t, U i t → ((i+P*t:ℕ):ZMod M)=v := by
    by_cases any : ∃ t, U i t
    · obtain ⟨t,big,pr,hit⟩ := any
      have co : (i+P*t).Coprime M := pr.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt mp big)
      have ic : (i:ℕ).Coprime P := (Nat.coprime_add_mul_left_left ..).mp (co.of_dvd_right (dvd_mul_right ..))
      have small := regular_of_reduced pos hf regular (ic.of_dvd_right (dvd_mul_left E 2))
      refine ⟨ZMod.unitOfCoprime (i+P*t) co,fun u hu => ?_⟩
      rw [ZMod.coe_unitOfCoprime]
      apply (ZMod.natCast_eq_natCast_iff ..).mpr
      exact ((regular_phase hp even ha hf sharp small b u t hu.2.2 hit).mul_left' P).add_left i
    · exact ⟨1,fun t h => (any ⟨t,h⟩).elim⟩
  choose v hv using cls
  refine ⟨univ.image v,(card_image_le.trans (by simp [P])),fun n hn => ?_⟩
  by_cases big : M<n
  · let i : Fin P := ⟨n%P,Nat.mod_lt _ pp⟩
    have eq : i+P*(n/P)=n := Nat.mod_add_div ..
    have hu : U i (n/P) := by unfold U; rw [eq]; exact ⟨big,hn⟩
    exact Or.inl ⟨v i,mem_image_of_mem _ (mem_univ i),eq ▸ hv i (n/P) hu⟩
  · exact Or.inr (le_of_not_gt big)

private lemma totient_return {p P : ℕ} (hp : p.Prime) (div : p∣P) (b : ℕ) :
    (P*p^b).totient=P.totient*p^b := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [pow_succ,←Nat.mul_assoc,Nat.mul_comm (P*p^b) p,
      Nat.totient_mul_of_prime_of_dvd hp (div.trans (dvd_mul_right P _)),ih]
    ring

/-- With no critical residue, the mass of every target decays by a full
factor of p per level. The neighborhood of 1 works for all targets. -/
theorem regular_fibre_mass {p r d E a : ℕ} [Fact p.Prime] (pos : 0<E) (even : Even E)
    (ep : p∣E) (ha : 2≤a) (hf : p^a∣Nat.fib (d*E)) (sharp : ¬p^(a+1)∣Nat.fib (d*E))
    (regular : ¬CriticalPhase p r d E a) (b : ℕ) {ε : ℝ} (epos : 0<ε) :
    ∀ᶠ x : ℝ in 𝓝[>] 1, ∀ y : ℤ, (x-1)*mass (primeIndexHits r d (p^(2*a+b)) y) x <
      (2*E:ℕ)/(((2*E).totient:ℝ)*(p:ℝ)^b)+ε := by
  classical
  let P := 2*E
  let M := P*p^b
  have hp : p.Prime := Fact.out
  have pp : 0<P := by dsimp [P]; omega
  have mp := Nat.mul_pos pp (pow_pos hp.pos b)
  let : NeZero M := ⟨mp.ne'⟩
  have tot : (M.totient:ℝ)=((2*E).totient:ℝ)*(p:ℝ)^b := by
    exact_mod_cast totient_return hp (ep.trans (dvd_mul_left E 2)) b
  have upp (S : Finset (ZMod M)ˣ) : ∀ᶠ x : ℝ in 𝓝[>] 1,
      (x-1)*mass (represented S) x < (S.card:ℝ)/M.totient+ε/2 :=
    (mass_represented S).eventually_lt_const (by linarith)
  have all := Filter.eventually_all.mpr upp
  have tail := (finite_mass_tendsto (Set.finite_Iic M)).eventually_lt_const
    (show (0:ℝ)<ε/2 by positivity)
  filter_upwards [all,tail,self_mem_nhdsWithin] with x bounds tiny hx
  change 1<x at hx
  intro y
  obtain ⟨S,size,cover⟩ := regular_cover pos even ha hf sharp regular b y
  have mu := mass_le_cover (∅ : Finset Unit) (fun _ => (∅ : Set ℕ))
    (primeIndexHits r d (p^(2*a+b)) y) (represented S) (Set.Iic M)
    (fun n hn _ => Or.inr (cover n hn)) hx
  simp only [sum_empty,zero_add] at mu
  have cmp := mul_le_mul_of_nonneg_left mu (sub_nonneg.mpr hx.le)
  rw [mul_add] at cmp
  change (x-1)*mass (Set.Iic M) x < ε/2 at tiny
  have count : (S.card:ℝ)/(M.totient:ℝ) ≤ (2*E:ℕ)/(M.totient:ℝ) :=
    div_le_div_of_nonneg_right (by exact_mod_cast size) (by positivity)
  rw [←tot]
  linarith only [cmp,bounds S,tiny,count]

#print axioms regular_fibre_mass

/-- A bound with a full power of p per level and constants independent of the integer target. -/
def UniformFibreRate (p r d : ℕ) : Prop :=
  ∃ (H : ℕ) (C : ℝ), 0<C ∧ ∀ (b : ℕ) {ε : ℝ}, 0<ε →
    ∀ᶠ x : ℝ in 𝓝[>] 1, ∀ y : ℤ, (x-1)*mass (primeIndexHits r d (p^(H+b)) y) x <
      C/(p:ℝ)^b+ε

/-- The finite test is necessary as well as sufficient for the full rate.
Any sharp even return containing p may be used. -/
theorem uniform_rate_iff_no_critical_phase {p r d E a : ℕ} [Fact p.Prime]
    (pos : 0<E) (even : Even E) (ep : p∣E) (ha : 2≤a) (hf : p^a∣Nat.fib (d*E))
    (sharp : ¬p^(a+1)∣Nat.fib (d*E)) :
    UniformFibreRate p r d ↔ ¬CriticalPhase p r d E a := by
  constructor
  · rintro ⟨H,C,cp,upper⟩ crit
    have hp : p.Prime := Fact.out
    have pone : 1<(p:ℝ) := by exact_mod_cast hp.one_lt
    have pp : 0<(p:ℝ) := by linarith
    have er : 0<(E:ℝ) := by exact_mod_cast pos
    obtain ⟨k,hk⟩ := pow_unbounded_of_one_lt (4*E*C) pone
    let b := H+k
    let j := k+2*a
    have depth : H+(b+j)=2*(a+b) := by dsimp [b,j]; omega
    have grow : 4*E*C < (p:ℝ)^j :=
      hk.trans_le (pow_le_pow_right₀ pone.le (Nat.le_add_right k _))
    let L : ℝ := 1/(4*E*p^b)
    let U : ℝ := C/(p:ℝ)^(b+j)
    have gap : U<L := by
      unfold U L
      rw [div_lt_div_iff₀ (by positivity) (by positivity),one_mul,pow_add (p:ℝ) b j]
      calc C*(4*E*p^b) = (4*E*C)*(p:ℝ)^b := by ring
           _ < (p:ℝ)^j*p^b := mul_lt_mul_of_pos_right grow (pow_pos pp _)
           _ = _ := mul_comm ..
    obtain ⟨y,lower⟩ := critical_fibre_mass pos even ep ha hf sharp crit b
    have bounds := upper (b+j) (ε:=(L-U)/2) (by linarith only [gap])
    rw [depth] at bounds
    obtain ⟨x,hx,lo⟩ := (bounds.and lower).exists
    have hi := hx y
    change _ < U+(L-U)/2 at hi
    change L≤_ at lo
    linarith only [hi,lo,gap]
  · intro regular
    have totpos : 0<((2*E).totient:ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr (Nat.mul_pos (by decide : 0<2) pos)
    refine ⟨2*a,((2*E:ℕ):ℝ)/(2*E).totient,by positivity,fun b ε eps => ?_⟩
    simpa only [div_div] using regular_fibre_mass pos even ep ha hf sharp regular b eps

#print axioms uniform_rate_iff_no_critical_phase

/-- A single bounded phase test works for every prime and positive affine step,
including progressions whose step shares a factor with the testing prime. -/
theorem prime_fibre_criterion (p r d : ℕ) [Fact p.Prime] (hd : 0<d) :
    let E := fibreReturn p d
    UniformFibreRate p r d ↔ ¬CriticalPhase p r d E ((Nat.fib (d*E)).factorization p) := by
  obtain ⟨pos,even,ep,ha,hf,sharp⟩ := fibreReturn_spec p d hd
  exact uniform_rate_iff_no_critical_phase pos even ep ha hf sharp

#print axioms prime_fibre_criterion

end Arxiv.«2211.10788».LocalPower
