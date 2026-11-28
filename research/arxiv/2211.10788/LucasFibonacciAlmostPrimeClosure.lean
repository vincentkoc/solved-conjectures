import HosoyaAlmostPrimeParameters
import HosoyaBoundedParameterRecovery

/-! Congruence limits at index parameters with prescribed total
prime-factor count, even with finitely many testing primes removed. -/

namespace Arxiv.«2211.10788».AlmostPrimeClosure
open CongruenceClosure ProgressionClosure
open scoped ArithmeticFunction.Omega

/-- Cofinal modular hits at exactly k prime factors. Testing moduli
may discard all primes dividing a fixed positive integer E. -/
def CofinalHits (k r d E : ℕ) (y : ℤ) : Prop :=
  ∀ M : ℕ, 0<M → M.Coprime E → ∀ B : ℕ, ∃ t : ℕ, B<t ∧ Nat.IsAlmostPrime k t ∧ Hit d r M y t

/-- Ordinary modular hits include those supplied by a fixed parameter. -/
def ModularHits (k r d E : ℕ) (y : ℤ) : Prop :=
  ∀ M : ℕ, 0<M → M.Coprime E → ∃ t : ℕ, Nat.IsAlmostPrime k t ∧ Hit d r M y t

/-- One allowed testing modulus confines every large successful parameter
to the classes of exact signed witnesses modulo any prescribed H. -/
theorem confining_modulus {k r d E H : ℕ} (hd : 0<d) (he : 0<E) (hh : 0<H) (y : ℤ) :
    ∃ M : ℕ, 0<M ∧ M.Coprime E ∧ ∀ t : ℕ, y.natAbs+r+2<t → Nat.IsAlmostPrime k t →
      Hit d r M y t → ∃ w : ℤ, (t:ℤ) ≡ w [ZMOD H] ∧ w≠0 ∧ Ω w.natAbs<k ∧ signed (r+d*w)=y := by
  let B := y.natAbs+r+2
  let D := indexModulus k B*H
  have Dpos : 0<D := Nat.mul_pos (indexModulus_pos ..) hh
  obtain ⟨e,_,cop⟩ := exists_coprime_detector (d*D) y he
  have dp := Nat.mul_pos hd Dpos
  have Mpos : 0 < detector (d*D) y e :=
    Nat.mul_pos (Nat.zero_lt_of_lt (layer_size dp y _)) (Nat.zero_lt_of_lt (layer_size dp y _))
  refine ⟨_,Mpos,cop,?_⟩
  intro t big factors hit
  obtain ⟨w,cl,val,size⟩ := recover_parameter hd Dpos r t e y hit
  have ap : (t:ℤ) ≡ w [ZMOD indexModulus k B] := cl.of_dvd
    (by exact_mod_cast (dvd_mul_right (indexModulus k B) H))
  obtain ⟨nz,budget⟩ := fewer_factors_of_class size factors big ap
  exact ⟨w,cl.of_dvd (by exact_mod_cast (dvd_mul_left H (indexModulus k B))),nz,budget,val⟩

/-- Only nonzero signed parameters with fewer than k factors survive
arbitrarily far along the k-almost-prime parameters. -/
theorem cofinal_hits_iff {k r d E : ℕ} (hd : 0<d) (he : 0<E) (y : ℤ) :
    CofinalHits k r d E y ↔ ∃ w : ℤ, w≠0 ∧ Ω w.natAbs<k ∧ signed (r+d*w)=y := by
  constructor
  · intro all
    obtain ⟨M,mp,cop,confine⟩ := confining_modulus (k:=k) (r:=r) hd he (by decide : 0<1) y
    obtain ⟨t,big,factors,hit⟩ := all M mp cop (y.natAbs+r+2)
    obtain ⟨w,_,nz,budget,val⟩ := confine t big factors hit
    exact ⟨w,nz,budget,val⟩
  · rintro ⟨w,nz,budget,val⟩ M mpos _ B
    let : NeZero M := ⟨mpos.ne'⟩
    obtain ⟨T,Tpos,period⟩ := signed_forward_period M ((r:ℤ)+d*w)
    obtain ⟨t,large,weight,ap⟩ := large_almost_prime_congruent nz budget Tpos (max B w.natAbs)
    have wt : w≤(t:ℤ) := by omega
    refine ⟨t,by omega,weight,?_⟩
    have hit := period ((r:ℤ)+d*t) (by gcongr) ((ap.mul_left (d:ℤ)).add_left (r:ℤ))
    rw [val,show (r:ℤ)+d*t=((r+d*t:ℕ):ℤ) by push_cast; rfl,signed_nat] at hit
    exact (ZMod.intCast_eq_intCast_iff ..).mp (by simpa only [Int.cast_natCast] using hit)

/-- A modular hit at every allowed modulus is either an exact hit or a
cofinal one. This also covers the zero-factor parameter 1. -/
theorem modular_hits_iff {k r d E : ℕ} (he : 0<E) (y : ℤ) :
    ModularHits k r d E y ↔
      (∃ t : ℕ, Nat.IsAlmostPrime k t ∧ (lucasFibonacciSum (r+d*t):ℤ)=y) ∨ CofinalHits k r d E y := by
  classical
  constructor
  · intro all
    by_cases exactHit : ∃ t : ℕ, Nat.IsAlmostPrime k t ∧ (lucasFibonacciSum (r+d*t):ℤ)=y
    · exact Or.inl exactHit
    right
    intro M mp cop B
    let V := lucasFibonacciSum (r+d*B)
    let K := E*(V+y.natAbs+1)+1
    have kp : 0<K := by dsimp [K]; omega
    have limit : V+y.natAbs<K := by
      have := Nat.le_mul_of_pos_left (V+y.natAbs+1) he
      dsimp [K]; omega
    have co : K.Coprime E := by simp [K]
    obtain ⟨t,weight,hit⟩ := all (M*K) (Nat.mul_pos mp kp) (Nat.coprime_mul_iff_left.mpr ⟨cop,co⟩)
    have split (D : ℕ) (dv : D∣M*K) : Hit d r D y t :=
      (show (lucasFibonacciSum (r+d*t):ℤ) ≡ y [ZMOD (M*K:ℕ)] from hit).of_dvd (by exact_mod_cast dv)
    refine ⟨t,?_,weight,split M (dvd_mul_right ..)⟩
    by_contra! small
    have ix := Nat.add_le_add_left (Nat.mul_le_mul_left d small) r
    have ub : lucasFibonacciSum (r+d*t)≤V :=
      Nat.add_le_add (Nat.mul_le_mul_left 2 (Nat.fib_mono ix)) (Nat.fib_mono (Nat.add_le_add_right ix 2))
    have zk := (split K (dvd_mul_left ..)).dvd
    have diff : (y-(lucasFibonacciSum (r+d*t):ℤ)).natAbs<K :=
      (Int.natAbs_sub_le ..).trans_lt (by simp only [Int.natAbs_natCast]; omega)
    have z : y-(lucasFibonacciSum (r+d*t):ℤ)=0 :=
      Int.eq_zero_of_dvd_of_natAbs_lt_natAbs zk (by simpa using diff)
    exact exactHit ⟨t,weight,by omega⟩
  · rintro (⟨t,weight,val⟩|cofinal) M mp unit
    · exact ⟨t,weight,val ▸ Int.ModEq.refl _⟩
    · obtain ⟨t,_,weight,hit⟩ := cofinal M mp unit 0
      exact ⟨t,weight,hit⟩

#print axioms confining_modulus
#print axioms cofinal_hits_iff
#print axioms modular_hits_iff

end Arxiv.«2211.10788».AlmostPrimeClosure
