import HosoyaJointParameterRecovery

/-! Prime mass of simultaneous value targets on distinct affine Hosoya sequences. -/

namespace Arxiv.«2211.10788».LocalPower.CompanionAffine

open ProgressionClosure AlmostPrimeClosure PrimeObstruction Finset Filter Topology CunninghamChain.PrimeMass

def jointHits (r d s f m : ℕ) (y z : ℤ) : Set ℕ :=
  primeIndexHits r d m y ∩ primeIndexHits s f m z

private abbrev V (n : ℕ) : ℤ := lucasFibonacciSum n

private lemma joint_cover {p r d s f H P : ℕ} (hp : p.Prime) (pp : 0<P)
    (inv : ∀ i b t u,
      V (r+d*(i+P*t)) ≡ V (r+d*(i+P*u)) [ZMOD (p:ℤ)^(H+b)] →
      V (s+f*(i+P*t)) ≡ V (s+f*(i+P*u)) [ZMOD (p:ℤ)^(H+b)] →
      t ≡ u [MOD p^b]) (b : ℕ) (y z : ℤ) :
    let M := P*p^b
    ∃ S : Finset (ZMod M)ˣ, S.card≤P ∧ ∀ n∈jointHits r d s f (p^(H+b)) y z,
      n∈represented S ∨ n≤M := by
  classical
  let M := P*p^b
  have mp : 0<M := Nat.mul_pos pp (pow_pos hp.pos b)
  let U (i : Fin P) (t : ℕ) := M < (i:ℕ)+P*t ∧ i+P*t∈jointHits r d s f (p^(H+b)) y z
  have cls (i : Fin P) : ∃ v : (ZMod M)ˣ, ∀ t, U i t → ((i+P*t:ℕ):ZMod M)=v := by
    by_cases any : ∃ t, U i t
    · obtain ⟨t,big,ht⟩ := any
      have co : (i+P*t).Coprime M := ht.1.1.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt mp big)
      refine ⟨ZMod.unitOfCoprime (i+P*t) co,fun u hu => ?_⟩
      rw [ZMod.coe_unitOfCoprime]
      apply (ZMod.natCast_eq_natCast_iff ..).mpr
      have cmp {a e : ℕ} {y : ℤ} (m : Hit e a (p^(H+b)) y (i+P*u)) (n : Hit e a (p^(H+b)) y (i+P*t)) :
          V (a+e*(i+P*u)) ≡ V (a+e*(i+P*t)) [ZMOD (p:ℤ)^(H+b)] := by
        simpa only [Hit,Nat.cast_pow] using m.trans n.symm
      exact ((inv i b u t (cmp hu.2.1.2 ht.1.2) (cmp hu.2.2.2 ht.2.2)).mul_left' P).add_left i
    · exact ⟨1,fun t h => (any ⟨t,h⟩).elim⟩
  choose v hv using cls
  refine ⟨univ.image v,(card_image_le.trans (by simp)),fun n hn => ?_⟩
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

/-- For every testing prime, two distinct positive-step index maps have
a uniform full-rate bound on the mass of prime parameters hitting both values. -/
theorem joint_prime_mass {p r d s f : ℕ} [Fact p.Prime] (hd : 0<d) (hf : 0<f)
    (distinct : (r,d)≠(s,f)) :
    ∃ (H : ℕ) (C : ℝ), 0<C ∧ ∀ (b : ℕ) {ε : ℝ}, 0<ε →
      ∀ᶠ x : ℝ in 𝓝[>] 1, ∀ y z : ℤ,
        (x-1)*mass (jointHits r d s f (p^(H+b)) y z) x < C/(p:ℝ)^b+ε := by
  classical
  have hp : p.Prime := Fact.out
  obtain ⟨P,pp,ep,H,inv⟩ := joint_phase_recovery p r d s f hd hf distinct
  have tp := Nat.totient_pos.mpr pp
  refine ⟨H,(P:ℝ)/P.totient,by positivity,fun b {ε} epos => ?_⟩
  let M := P*p^b
  have mp : 0<M := Nat.mul_pos pp (pow_pos hp.pos b)
  let : NeZero M := ⟨mp.ne'⟩
  have tot : (M.totient:ℝ)=((P.totient:ℝ)*(p:ℝ)^b) := by
    exact_mod_cast totient_return hp ep b
  have upp (S : Finset (ZMod M)ˣ) : ∀ᶠ x : ℝ in 𝓝[>] 1,
      (x-1)*mass (represented S) x < (S.card:ℝ)/M.totient+ε/2 :=
    (mass_represented S).eventually_lt_const (by linarith)
  have all := Filter.eventually_all.mpr upp
  have tail := (finite_mass_tendsto (Set.finite_Iic M)).eventually_lt_const
    (show (0:ℝ)<ε/2 by positivity)
  filter_upwards [all,tail,self_mem_nhdsWithin] with x bounds tiny hx
  change 1<x at hx
  intro y z
  obtain ⟨S,size,cover⟩ := joint_cover hp pp inv b y z
  have mu := mass_le_cover (∅ : Finset Unit) (fun _ => (∅ : Set ℕ))
    (jointHits r d s f (p^(H+b)) y z) (represented S) (Set.Iic M)
    (fun n hn _ => Or.inr (cover n hn)) hx
  simp only [sum_empty,zero_add] at mu
  have cmp := mul_le_mul_of_nonneg_left mu (sub_nonneg.mpr hx.le)
  rw [mul_add] at cmp
  change (x-1)*mass (Set.Iic M) x < ε/2 at tiny
  have count : (S.card:ℝ)/(M.totient:ℝ) ≤ (P:ℝ)/(M.totient:ℝ) :=
    div_le_div_of_nonneg_right (by exact_mod_cast size) (by positivity)
  rw [div_div,←tot]
  linarith only [cmp,bounds S,tiny,count]

#print axioms joint_prime_mass

end Arxiv.«2211.10788».LocalPower.CompanionAffine
