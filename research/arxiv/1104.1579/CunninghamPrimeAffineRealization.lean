import CunninghamPrimeSieveCount

/-! Realizing prescribed local classes at a prime seed while sifting a family
of affine forms. Giving the value at two permits negative intercepts. -/

namespace CunninghamChain.PairedRough

open Finset BrunBlocks PrimeSeedSieve

def term (a c n : ℕ) := a*(n-2)+c

def residue (q a c : ℕ) (x : ZMod q) := (a:ZMod q)*(x-2)+c

lemma term_cast (q a c n : ℕ) (hn : 2≤n) :
    (term a c n : ZMod q) = residue q a c n := by
  simp [term,residue,Nat.cast_sub hn]

private noncomputable def roots {k : ℕ} (a c : Fin k → ℕ) (q : ℕ) : Finset (ZMod q) := by
  classical
  exact if h : q.Prime then
    letI : Fact q.Prime := ⟨h⟩
    (univ.image fun i => (2:ZMod q)-(c i : ZMod q)/(a i : ZMod q)).erase 0
  else ∅

private lemma roots_spec {k q : ℕ} (a c : Fin k → ℕ) (hq : q.Prime)
    (ha : ∀ i, 0<a i ∧ a i<q) :
    (roots a c q).card ≤ k ∧ (∀ x ∈ roots a c q, IsUnit x) ∧
      ∀ (n : ℕ) (i : Fin k), n.Prime → q<n → q ∣ term (a i) (c i) n →
        (n:ZMod q) ∈ roots a c q := by
  classical
  let : Fact q.Prime := ⟨hq⟩
  simp only [roots,dif_pos hq]
  refine ⟨(card_le_card (erase_subset ..)).trans (card_image_le.trans_eq (by simp)),?_,?_⟩
  · exact fun x hx => isUnit_iff_ne_zero.mpr (mem_erase.mp hx).1
  · intro n i hn hqn hd
    have nz : (n:ZMod q)≠0 := fun e => hqn.ne ((Nat.prime_dvd_prime_iff_eq hq hn).mp
      ((ZMod.natCast_eq_zero_iff ..).mp e))
    have unit : (a i:ZMod q)≠0 := fun e => (Nat.not_dvd_of_pos_of_lt (ha i).1 (ha i).2)
      ((ZMod.natCast_eq_zero_iff ..).mp e)
    refine mem_erase.mpr ⟨nz,mem_image.mpr ⟨i,mem_univ _,?_⟩⟩
    have h := (ZMod.natCast_eq_zero_iff ..).mpr hd
    rw [term_cast _ _ _ _ hn.two_le] at h
    unfold residue at h
    field_simp [unit]
    linear_combination -h

/-- Every fixed set of admissible small-prime choices can be imposed on
infinitely many prime parameters. All the affine values avoid those primes
and have a factor-count bound depending only on the number of forms. -/
theorem prime_realization {k : ℕ} (hBV : BombieriVinogradov) (a c : Fin k → ℕ)
    (ha : ∀ i, 0<a i) (hc : ∀ i, 0<c i) (x : (q : ℕ) → ZMod q)
    (hx : ∀ q, q.Prime → IsUnit (x q) ∧ ∀ i, residue q (a i) (c i) (x q) ≠ 0)
    (B : ℕ) : {n : ℕ | n.Prime ∧
      (∀ q ∈ B.primesLE, (n:ZMod q)=x q) ∧ ∀ i,
        Nat.IsAtMostAlmostPrime (1152*k+117) (term (a i) (c i) n) ∧
        ∀ q, q.Prime → q ∣ term (a i) (c i) n → B<q}.Infinite := by
  classical
  let S := ∑ i, (a i+c i)
  let H := B+2*k+S+2
  have bound (i : Fin k) : a i+c i≤H :=
    (single_le_sum (fun j _ => Nat.zero_le (a j+c j)) (mem_univ i)).trans (by dsimp [H,S]; omega)
  have big : 1<H := by dsimp [H]; omega
  have wide : 2*k≤H := by dsimp [H]; omega
  have cut : B≤H := by dsimp [H]; omega
  have spec (q : ℕ) (hp : q.Prime) (hq : H<q) := roots_spec a c hp
    (fun i => ⟨ha i,by have := bound i; omega⟩)
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨Z,n,hXZ,hZn,hnx,hn,cls,free⟩ := rough_prime_sample hBV k H big wide x
    (fun q hq => (hx q (Nat.prime_of_mem_primesLE hq)).1) (roots a c)
    (fun q hp hq => (spec q hp hq).1) (fun q hp hq => (spec q hp hq).2.1) (N+H)
  have hZ : H<Z := by omega
  refine ⟨n,⟨hn,fun q hq => cls q (Nat.mem_primesLE.mpr
    ⟨(Nat.mem_primesLE.mp hq).1.trans cut,Nat.prime_of_mem_primesLE hq⟩),?_⟩,by omega⟩
  intro i
  have rough (q : ℕ) (hp : q.Prime) (hd : q ∣ term (a i) (c i) n) : Z<q := by
    by_contra! hq
    by_cases small : q≤H
    · have zero := (ZMod.natCast_eq_zero_iff ..).mpr hd
      rw [term_cast _ _ _ _ hn.two_le,cls q (Nat.mem_primesLE.mpr ⟨small,hp⟩)] at zero
      exact (hx q hp).2 i zero
    · exact free q hp (by omega) hq ((spec q hp (by omega)).2.2 n i hn (by omega) hd)
  refine ⟨rough_factor_count (Z:=Z) (lt_trans big hZ) (by dsimp [term]; have := hc i; omega) ?_ rough,
    fun q hp hd => cut.trans_lt (hZ.trans (rough q hp hd))⟩
  have est : term (a i) (c i) n ≤ (a i+c i)*n := by
    dsimp [term]
    rw [Nat.add_mul]
    exact Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.sub_le ..)) (Nat.le_mul_of_pos_right _ hn.pos)
  calc
    _ ≤ (a i+c i)*n := est
    _ ≤ Z*Z^(4*(8*(36*k)+29)) := Nat.mul_le_mul ((bound i).trans hZ.le) hnx
    _ = _ := by rw [←pow_succ']; congr 1; omega

#print axioms prime_realization

/-- For unrestricted parameters, Brun's elementary lower sieve suffices to
impose the same prescribed classes and a smaller multiplicity bound. -/
theorem integer_realization {k : ℕ} (a c : Fin k → ℕ) (ha : ∀ i, 0<a i)
    (x : (q : ℕ) → ZMod q)
    (hx : ∀ q, q.Prime → ∀ i, residue q (a i) (c i) (x q) ≠ 0) (B : ℕ) :
    {n : ℕ | 2≤n ∧ (∀ q ∈ B.primesLE, (n:ZMod q)=x q) ∧ ∀ i,
      Nat.IsAtMostAlmostPrime (324*k+33) (term (a i) (c i) n) ∧
      ∀ q, q.Prime → q ∣ term (a i) (c i) n → B<q}.Infinite := by
  classical
  let P := B.primesLE
  let W := ∏ q ∈ P, q
  have pr {q : ℕ} (hq : q∈P) := Nat.prime_of_mem_primesLE hq
  have wpos : 0<W := prod_pos (fun _ hq => (pr hq).pos)
  let g (q : ℕ) := (x q-2).val
  let b := Nat.chineseRemainderOfFinset g id P (fun _ hq => (pr hq).ne_zero)
    (fun _ hp _ hq h => (Nat.coprime_primes (pr hp) (pr hq)).mpr h)
  let n (t : ℕ) := W*t+b.val+2
  have cls (t q : ℕ) (hq : q∈P) : (n t:ZMod q)=x q := by
    let : NeZero q := ⟨(pr hq).ne_zero⟩
    have w0 := (ZMod.natCast_eq_zero_iff W q).mpr (dvd_prod_of_mem id hq)
    have base := (ZMod.natCast_eq_natCast_iff ..).mpr (b.property q hq)
    dsimp only [n]
    push_cast
    rw [w0,zero_mul,zero_add,base]
    simp [g]
  let A (i) := a i*W
  let C (i) := a i*b.val+c i
  have eq (t i) : A i*t+C i=term (a i) (c i) (n t) := by simp [A,C,term,n]; ring
  have adm (q : ℕ) (hq : q.Prime) : ∃ t : ℕ, ∀ i, ¬q ∣ A i*t+C i := by
    let : Fact q.Prime := ⟨hq⟩
    suffices ∃ t : ℕ, (n t:ZMod q)=x q by
      obtain ⟨t,ht⟩ := this
      refine ⟨t,fun i div => hx q hq i ?_⟩
      have h := (ZMod.natCast_eq_zero_iff ..).mpr (eq t i ▸ div : q∣term (a i) (c i) (n t))
      rwa [term_cast _ _ _ _ (by dsimp [n]; omega),ht] at h
    by_cases small : q∈P
    · exact ⟨0,cls 0 q small⟩
    have unit : (W:ZMod q)≠0 := by
      intro hz
      obtain ⟨l,hl,hql⟩ := (hq.prime.dvd_finsetProd_iff id).mp ((ZMod.natCast_eq_zero_iff ..).mp hz)
      exact small (((Nat.prime_dvd_prime_iff_eq hq (pr hl)).mp hql).symm ▸ hl)
    obtain ⟨t,ht⟩ := ZMod.natCast_zmod_surjective ((x q-(b.val:ZMod q)-2)/(W:ZMod q))
    refine ⟨t,?_⟩
    dsimp only [n]
    push_cast
    rw [ht]
    field_simp [unit]
    ring
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨t,ht,hn⟩ := Set.infinite_iff_exists_gt.mp
    (almostPrime_linear_forms k A C (fun i => Nat.mul_pos (ha i) wpos) adm B) N
  refine ⟨n t,⟨by dsimp [n]; omega,cls t,fun i => ?_⟩,?_⟩
  · simpa only [eq] using ht i
  · have := Nat.le_mul_of_pos_left t wpos
    dsimp [n]
    omega

#print axioms integer_realization

#print axioms term_cast

end CunninghamChain.PairedRough
