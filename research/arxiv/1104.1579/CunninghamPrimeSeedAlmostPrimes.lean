import CunninghamPrimeSieveCount

/-! Prime-started, rough almost-prime Cunningham prefixes of either kind. -/

namespace CunninghamChain.PrimeSeedSieve

open Finset BrunBlocks

private lemma term_mod (b : Bool) (q p i : ℕ) (hp : 2 ≤ p) :
    (chain b p i : ZMod q) = (2:ZMod q)^i*((p:ZMod q)-2) + (chain b 2 i : ZMod q) := by
  have h := chain_shift b (p-2) 2 (by decide) i
  rw [Nat.sub_add_cancel hp] at h
  rw [h,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_sub hp]
  norm_num

private noncomputable def forbidden (b : Bool) (k q : ℕ) : Finset (ZMod q) := by
  classical
  exact if h : q.Prime then
    letI : Fact q.Prime := ⟨h⟩
    ((range k).image fun i => (2:ZMod q) - (chain b 2 i : ZMod q)/(2:ZMod q)^i).erase 0
  else ∅

private lemma forbidden_spec (b : Bool) (k q : ℕ) (hq : q.Prime) (h2 : 2 < q) :
    (forbidden b k q).card ≤ k ∧ (∀ a ∈ forbidden b k q, IsUnit a) ∧
    ∀ p i : ℕ, p.Prime → q < p → i < k → q ∣ chain b p i → (p:ZMod q) ∈ forbidden b k q := by
  classical
  let : Fact q.Prime := ⟨hq⟩
  have htwo : (2:ZMod q) ≠ 0 := by
    have := (ZMod.natCast_eq_zero_iff 2 q).1
    exact fun hz => (Nat.not_dvd_of_pos_of_lt (by decide) h2) (this (by simpa using hz))
  simp only [forbidden,dif_pos hq]
  constructor
  · exact (card_le_card (erase_subset ..)).trans (card_image_le.trans_eq (card_range _))
  constructor
  · intro a ha
    exact isUnit_iff_ne_zero.mpr (mem_erase.mp ha).1
  · intro p i hp hqp hi hd
    have hpu : (p:ZMod q) ≠ 0 := fun hz => hqp.ne ((Nat.prime_dvd_prime_iff_eq hq hp).mp
      ((ZMod.natCast_eq_zero_iff _ _).mp hz))
    refine mem_erase.mpr ⟨hpu,mem_image.mpr ⟨i,mem_range.mpr hi,?_⟩⟩
    have hz := (ZMod.natCast_eq_zero_iff _ _).mpr hd
    rw [term_mod b q p i hp.two_le] at hz
    field_simp [pow_ne_zero i htwo]
    linear_combination -hz

/-- Under the Bombieri–Vinogradov distribution statement, both recurrences have
infinitely many prime seeds whose first k terms avoid every prescribed small prime
and have bounded Ω. A fixed prime divides the strictly larger composite successor. -/
theorem prime_seeds_rough_prefixes_exact_composite (hBV : BombieriVinogradov) (k : ℕ) (hk : 0 < k)
    (b : Bool) : ∃ q : ℕ, q.Prime ∧ ∀ B : ℕ,
      {p : ℕ | p.Prime ∧
        (∀ i < k, let y := (if b then firstKindTerm else secondKindTerm) p i
          Nat.IsAtMostAlmostPrime (1152*k+117) y ∧ ∀ l : ℕ, l.Prime → l ∣ y → B < l) ∧
        q ∣ (if b then firstKindTerm else secondKindTerm) p k ∧
        ¬((if b then firstKindTerm else secondKindTerm) p k).Prime}.Infinite := by
  classical
  obtain ⟨v,hv,hq⟩ := prime_at_length b hk
  let q := chain b v k
  have hq' : q.Prime := hq
  have hv0 : v < q := by
    have h := chain_grows b hv hk
    cases b <;> simpa [q,chain,firstKindTerm,secondKindTerm] using h
  refine ⟨q,hq',fun cutoff => ?_⟩
  let H := q+2*k+cutoff+2
  have hH : 1 < H := by dsimp [H]; omega
  have hqH : q ≤ H := by dsimp [H]; omega
  have hkH : 2*k ≤ H := by dsimp [H]; omega
  let a (l : ℕ) : ZMod l := if l=q then v else fixedResidue b l
  have ha (l : ℕ) (hl : l ∈ H.primesLE) : IsUnit (a l) := by
    let : Fact l.Prime := ⟨Nat.prime_of_mem_primesLE hl⟩
    by_cases he : l=q
    · subst l
      simp only [a,if_pos rfl]
      exact isUnit_iff_ne_zero.mpr (fun hz => (Nat.not_dvd_of_pos_of_lt (by omega) hv0)
        ((ZMod.natCast_eq_zero_iff _ _).mp hz))
    · cases b <;> simp [a,he,fixedResidue]
  let U := forbidden b k
  have hspec {l : ℕ} (hl : l.Prime) (hh : H < l) := forbidden_spec b k l hl (by dsimp [H] at hh; omega)
  apply Set.infinite_of_forall_exists_gt
  intro bound
  let X := bound+H+2^k+chain b 2 k
  obtain ⟨Z,p,hXZ,hZp,hpx,hp,hclass,hfree⟩ := rough_prime_sample hBV k H hH hkH a ha U
    (fun _ h h' => (hspec h h').1) (fun _ h h' => (hspec h h').2.1) X
  have hsum : bound+H ≤ X := Nat.le_trans (Nat.le_add_right (bound+H) (2^k)) (Nat.le_add_right _ _)
  have hHZ := (Nat.le_add_left H bound).trans_lt (hsum.trans_lt hXZ)
  have hbound := (Nat.le_add_right bound H).trans_lt (hsum.trans_lt (hXZ.trans hZp))
  have hterm (i : ℕ) : (chain b p i : ZMod q) = (chain b v i : ZMod q) := by
    have he := hclass q (Nat.mem_primesLE.mpr ⟨hqH,hq'⟩)
    simp only [a,if_pos rfl] at he
    rw [term_mod b q p i hp.two_le,term_mod b q v i hv,he]
  have hstop : q ∣ chain b p k := (ZMod.natCast_eq_zero_iff _ _).mp (by
    rw [hterm k]; change (q : ZMod q) = 0; simp)
  have hgt : q < chain b p k := by
    have h := chain_grows b hp.two_le hk
    have h0 : chain b p 0 = p := by cases b <;> rfl
    rw [h0] at h
    omega
  refine ⟨p,⟨hp,?_,hstop,fun h => hgt.ne ((Nat.prime_dvd_prime_iff_eq hq' h).mp hstop)⟩,hbound⟩
  intro i hi
  let y := chain b p i
  have hy : 2 ≤ y := chain_ge_two b hp.two_le i
  have rough (l : ℕ) (hl : l.Prime) (hd : l ∣ y) : Z < l := by
    by_contra! hz
    by_cases hsmall : l ≤ H
    · have hzero := (ZMod.natCast_eq_zero_iff y l).mpr hd
      by_cases he : l=q
      · subst l
        change (chain b p i : ZMod q) = 0 at hzero
        rw [hterm] at hzero
        exact (Nat.not_dvd_of_pos_of_lt (by have := chain_ge_two b hv i; omega) (chain_grows b hv hi))
          ((ZMod.natCast_eq_zero_iff _ _).mp hzero)
      · have hf := hclass l (Nat.mem_primesLE.mpr ⟨hsmall,hl⟩)
        rw [show a l = fixedResidue b l from if_neg he] at hf
        change (chain b p i : ZMod l) = 0 at hzero
        rw [chain_fixed b l p hp.two_le hf] at hzero
        let : Fact l.Prime := ⟨hl⟩
        cases b <;> simp [fixedResidue] at hzero
    · have hh := lt_of_not_ge hsmall
      exact hfree l hl hh hz ((hspec hl hh).2.2 p i hp (hz.trans_lt hZp) hi hd)
  have hval : y ≤ Z^(1152*k+117) := by
    have hscale := chain_shift b (p-2) 2 (by decide) i
    rw [Nat.sub_add_cancel hp.two_le] at hscale
    have hle := Nat.mul_le_mul (Nat.pow_le_pow_right (by decide : 0 < 2) hi.le) (Nat.sub_le p 2)
    have ht := (chain_grows b (p := 2) (by decide) hi).le
    have hcoef : 2^k+chain b 2 k ≤ Z := by dsimp [X] at hXZ; omega
    have hp0 := hp.pos
    calc
      y ≤ (2^k+chain b 2 k)*p := by dsimp [y]; rw [hscale]; nlinarith only [hle,ht,Nat.le_mul_of_pos_right (chain b 2 k) hp0]
      _ ≤ Z*Z^(4*(8*(36*k)+29)) := Nat.mul_le_mul hcoef hpx
      _ = _ := by rw [← pow_succ']; congr 1; omega
  exact ⟨rough_factor_count (Z:=Z) (y:=y) (hH.trans hHZ) (by omega) hval rough,
    fun l hl hd => by have := rough l hl hd; dsimp [H] at hHZ; omega⟩

#print axioms prime_seeds_rough_prefixes_exact_composite

end CunninghamChain.PrimeSeedSieve
