import CunninghamPairedLocalTest

/-! A finite test for paired almost-prime Cunningham prefixes with a
specified composite after each prefix. -/

namespace CunninghamChain.PairedRough
open Finset PrimeSeedSieve

def rough (L B n : ℕ) : Prop := Nat.IsAtMostAlmostPrime L n ∧ ∀ q, q.Prime → q∣n → B<q

/-- Seed n starts the plus chain and n+h starts the minus chain. Q and R
are fixed divisors of the two composite successors. -/
def stopped (h k l L B Q R n : ℕ) : Prop :=
  (∀ i < k, rough L B (firstKindTerm n i)) ∧
  (∀ j < l, rough L B (secondKindTerm (n+h) j)) ∧
  Q ∣ firstKindTerm n k ∧ ¬(firstKindTerm n k).Prime ∧
  R ∣ secondKindTerm (n+h) l ∧ ¬(secondKindTerm (n+h) l).Prime

def supply (Seed : ℕ → Prop) (h k l L : ℕ) : Prop :=
  ∃ Q R, Q.Prime ∧ R.Prime ∧ Q<R ∧ ∀ B : ℕ,
    {n : ℕ | 2≤n ∧ Seed n ∧ stopped h k l L B Q R n}.Infinite

private theorem local_of_supply {Seed : ℕ → Prop} {h k l L : ℕ}
    (hs : supply Seed h k l L) : localTest h k l := by
  obtain ⟨Q,R,_,_,_,s⟩ := hs
  intro q hq
  have prime := Nat.prime_of_mem_primesLE hq
  obtain ⟨n,mem⟩ := (s q).nonempty
  obtain ⟨hn,_,plus,minus,_⟩ := mem
  refine ⟨n,(avoids_iff ..).mpr ?_⟩
  apply (sites_iff (k:=k) (l:=l) (fun b i => residue q (2^i) (base h b i) n≠0)).mpr
  have no (b : Bool) (i : ℕ) (free : rough L q (if b then firstKindTerm n i else secondKindTerm (n+h) i)) :
      residue q (2^i) (base h b i) n≠0 := by
    intro zero
    rw [← term_cast _ _ _ _ hn] at zero
    have div := (ZMod.natCast_eq_zero_iff ..).mp zero
    rw [term_chain hn] at div
    exact (lt_irrefl q) (free.2 q prime div)
  exact ⟨fun i hi => no true i (by simpa using plus i hi),
    fun j hj => no false j (by simpa using minus j hj)⟩

private theorem supply_of_sieve {h k l L : ℕ} {Seed : ℕ → Prop} (hk : 0 < k) (hl : 0 < l)
    (ok : localTest h k l)
    (sieve : ∀ x : (q : ℕ) → ZMod q, (∀ q, q.Prime → avoids h k l q (x q)) →
      ∀ B N : ℕ, ∃ n>N, 2≤n ∧ Seed n ∧ (∀ q ∈ B.primesLE, (n:ZMod q)=x q) ∧
        ∀ z, rough L B (term (slopes k l z) (constants h k l z) n)) : supply Seed h k l L := by
  obtain ⟨Q,R,hQ,hR,hQR,x,avoid,hitQ,hitR⟩ := stop_classes hk hl ok
  refine ⟨Q,R,hQ,hR,hQR,fun B => Set.infinite_of_forall_exists_gt (fun N => ?_)⟩
  let cut := B+R
  obtain ⟨n,hn,pos,hseed,cls,good⟩ := sieve x avoid cut (N+R+2)
  have each (b : Bool) (i : ℕ) (hz : rough L cut (term (2^i) (base h b i) n)) :
      rough L B (if b then firstKindTerm n i else secondKindTerm (n+h) i) := by
    rw [term_chain pos] at hz
    exact ⟨hz.1,fun q hp div => (Nat.le_add_right B R).trans_lt (hz.2 q hp div)⟩
  obtain ⟨plus,minus⟩ := (sites_iff (k:=k) (l:=l) (fun b i => rough L cut (term (2^i) (base h b i) n))).mp good
  have stop (b : Bool) (i q : ℕ) (hp : q.Prime) (le : q≤R)
      (hit : residue q (2^i) (base h b i) (x q)=0) :
      let y := if b then firstKindTerm n i else secondKindTerm (n+h) i
      q∣y ∧ ¬y.Prime := by
    rw [← term_chain pos h b i]
    have same := cls q (Nat.mem_primesLE.mpr ⟨le.trans (Nat.le_add_left R B),hp⟩)
    have div : q ∣ term (2^i) (base h b i) n := (ZMod.natCast_eq_zero_iff ..).mp (by
      rw [term_cast _ _ _ _ pos,same]; exact hit)
    have large : q<term (2^i) (base h b i) n := by
      have := Nat.le_mul_of_pos_left (n-2) (pow_pos (by decide : 0 < 2) i)
      dsimp [term]
      omega
    exact ⟨div,fun prime => large.ne ((Nat.prime_dvd_prime_iff_eq hp prime).mp div)⟩
  obtain ⟨dQ,nQ⟩ := stop true k Q hQ hQR.le hitQ
  obtain ⟨dR,nR⟩ := stop false l R hR le_rfl hitR
  exact ⟨n,⟨pos,hseed,(fun i hi => each true i (plus i hi)),(fun j hj => each false j (minus j hj)),
    dQ,nQ,dR,nR⟩,by omega⟩

/-- Unconditionally, testing only the primes through k+l decides whether the
two bounded-almost-prime prefixes can stop at their specified composites. -/
theorem paired_rough_stops_iff {h k l : ℕ} (hk : 0 < k) (hl : 0 < l) :
    supply (fun _ => True) h k l (324*(k+l)+33) ↔ localTest h k l := by
  refine ⟨local_of_supply,fun ok => supply_of_sieve hk hl ok ?_⟩
  intro x safe B N
  have H := integer_realization (slopes k l) (constants h k l) (fun _ => pow_pos (by decide) _) x
    (fun q hp => (avoids_iff ..).mp (safe q hp)) B
  obtain ⟨n,⟨hn,cls,good⟩,big⟩ := Set.infinite_iff_exists_gt.mp H N
  exact ⟨n,big,hn,trivial,cls,good⟩

/-- Bombieri–Vinogradov gives the same local criterion with a genuinely
prime first seed. The second seed and the other prefix terms are almost-primes. -/
theorem paired_prime_rough_stops_iff (hBV : BombieriVinogradov) {h k l : ℕ} (hk : 0 < k) (hl : 0 < l) :
    supply Nat.Prime h k l (1152*(k+l)+117) ↔ localTest h k l := by
  refine ⟨local_of_supply,fun ok => supply_of_sieve hk hl ok ?_⟩
  intro x safe B N
  have H := prime_realization hBV (slopes k l) (constants h k l) (fun _ => pow_pos (by decide) _)
    (fun z => base_pos h _ _) x (fun q hp => ⟨avoids_unit hp hk (safe q hp),(avoids_iff ..).mp (safe q hp)⟩) B
  obtain ⟨n,⟨prime,cls,good⟩,big⟩ := Set.infinite_iff_exists_gt.mp H N
  exact ⟨n,big,prime.two_le,prime,cls,good⟩

#print axioms paired_rough_stops_iff
#print axioms paired_prime_rough_stops_iff

end CunninghamChain.PairedRough
