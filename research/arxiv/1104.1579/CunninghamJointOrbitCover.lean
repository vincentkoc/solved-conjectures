import CunninghamThinPrimePeriods
import CunninghamSquarefreePrimeSeeds

/-! One reduced class confines both Cunningham orbits, with separate
sets of prime periods and small total reciprocal cost on the seed primes. -/

namespace CunninghamChain.PrimePeriodSupply
open Finset SquarefreeSeeds

namespace PeriodSupply
variable {T : ℝ} (S : PeriodSupply T)

def selected (b : Bool) := if b then S.plus else S.minus
def periodProduct (b : Bool) := (S.selected b).prod id
def seedModulus := (S.plus∪S.minus).prod S.q

lemma selected_mem {b : Bool} {l : ℕ} (hl : l∈S.selected b) : l∈S.plus∪S.minus := by
  cases b
  · exact mem_union_right _ hl
  · exact mem_union_left _ hl

lemma modulus_pos : 0<S.seedModulus := prod_pos fun l hl => (S.spec l hl).2.1.pos
lemma periodProduct_pos (b : Bool) : 0<S.periodProduct b :=
  prod_pos fun l hl => (S.spec l (S.selected_mem hl)).1.pos

private lemma term_lower (b : Bool) {p : ℕ} (_pos : 0<p) (j : ℕ) : p≤term b p j := by
  induction j with
  | zero => cases b <;> rfl
  | succ j ih =>
    cases b <;> simp only [term,Bool.false_eq_true,if_false,if_true,firstKindTerm,secondKindTerm] at ih ⊢ <;> omega

/-- On this single reduced class a return at site i+1 forces i coprime
to the designated product of prime periods, for each choice of sign. -/
theorem simultaneous_class :
    ∃ A : ℕ, A.Coprime S.seedModulus ∧ ∀ p : ℕ, S.seedModulus<p → p ≡ A [MOD S.seedModulus] →
      ∀ b : Bool, ∀ i : ℕ, (term b p (i+1)).Prime → i.Coprime (S.periodProduct b) := by
  classical
  let U := S.plus∪S.minus
  let sign (l : ℕ) := decide (l∈S.plus)
  let r l := root (sign l) (S.q l) 1
  have spec {l : ℕ} (hl : l∈U) := S.spec l hl
  have distinct {k l : ℕ} (hk : k∈U) (hl : l∈U) (h : S.q k=S.q l) : k=l := by
    rw [←(spec hk).2.2.2,←(spec hl).2.2.2,h]
  obtain ⟨A,hA⟩ := Nat.chineseRemainderOfFinset r S.q U (fun l hl => (spec hl).2.1.ne_zero)
    (fun k hk l hl ne => (Nat.coprime_primes (spec hk).2.1 (spec hl).2.1).mpr (fun eq => ne (distinct hk hl eq)))
  have odd {l : ℕ} (hl : l∈U) : Nat.Coprime 2 (S.q l) :=
    (Nat.coprime_primes Nat.prime_two (spec hl).2.1).mpr (spec hl).2.2.1.ne
  have unit (l : ℕ) (hl : l∈U) : (r l).Coprime (S.q l) := by
    let : Fact (S.q l).Prime := ⟨(spec hl).2.1⟩
    apply Nat.Coprime.symm
    apply (spec hl).2.1.coprime_iff_not_dvd.mpr
    intro dv
    have eq := (ZMod.natCast_eq_zero_iff ..).mpr dv
    have van := root_spec (sign l) (odd hl) 1
    change (r l : ZMod (S.q l))=0 at eq
    change value (sign l) 1 (r l : ZMod (S.q l))=0 at van
    rw [eq] at van
    cases hbit : sign l <;> norm_num [value,fixed,hbit] at van
  refine ⟨A,Nat.Coprime.prod_right fun l hl => (hA l hl).gcd_eq.trans (unit l hl),?_⟩
  intro p large ap b i prime
  rw [periodProduct,Nat.coprime_prod_right_iff]
  intro l hl
  have hu : l∈U := S.selected_mem hl
  let : Fact (S.q l).Prime := ⟨(spec hu).2.1⟩
  have bit : sign l=b := by
    cases b
    · exact decide_eq_false (fun h => disjoint_left.mp S.disjoint h hl)
    · exact decide_eq_true hl
  apply Nat.Coprime.symm
  apply (spec hu).1.coprime_iff_not_dvd.mpr
  rintro ⟨t,ht⟩
  have pow1 : (2:ZMod (S.q l))^i=1 := by
    have powOrder := pow_orderOf_eq_one (2:ZMod (S.q l))
    rw [(spec hu).2.2.2] at powOrder
    rw [ht,pow_mul,powOrder,one_pow]
  have same : root b (S.q l) (i+1)=r l := by simp [root,r,bit,pow_succ,pow1]
  have dw : S.q l ∣ S.seedModulus := dvd_prod_of_mem S.q hu
  have pos : 0<p := S.modulus_pos.trans large
  have dv := (root_iff b pos (odd hu) (i+1)).mpr (same ▸ (ap.of_dvd dw).trans (hA l hu))
  have qlt : S.q l < term b p (i+1) := (Nat.le_of_dvd S.modulus_pos dw).trans_lt (large.trans_le (term_lower b pos _))
  exact qlt.ne ((Nat.prime_dvd_prime_iff_eq (spec hu).2.1 prime).mp dv)

#print axioms simultaneous_class

end PeriodSupply
end CunninghamChain.PrimePeriodSupply
