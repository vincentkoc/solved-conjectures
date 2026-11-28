import HosoyaExactGcdFrequency
import HosoyaRoughCofactorResidues

/-! Positive mass from cofactor residues avoiding all small primes. -/

namespace Arxiv.«2211.10788».IndexDivisors
open Finset Filter Topology

def repeats (D : ℕ) (S : Finset ℕ) (n : ℕ) : Prop := n%D∈S
instance (D : ℕ) (S : Finset ℕ) (n : ℕ) : Decidable (repeats D S n) := by unfold repeats; infer_instance

private lemma repeats_period (D : ℕ) (S : Finset ℕ) : Function.Periodic (repeats D S) D := by
  intro n
  simp [repeats]

private lemma repeats_mean {D : ℕ} (S : Finset ℕ) (bounded : ∀ r∈S, r<D) :
    periodMean (repeats D S) D = (S.card:ℝ)/D := by
  unfold periodMean
  rw [Nat.count_eq_card_filter_range]
  have eq : (range D).filter (repeats D S)=S := by
    ext r
    constructor
    · intro h
      obtain ⟨lt,hit⟩ := mem_filter.mp h
      simpa [repeats,Nat.mod_eq_of_lt (mem_range.mp lt)] using hit
    · intro h
      exact mem_filter.mpr ⟨mem_range.mpr (bounded _ h),by simpa [repeats,Nat.mod_eq_of_lt (bounded _ h)]⟩
  rw [eq]

private lemma residue_lower_density {P : ℕ → Prop} [DecidablePred P] {D K : ℕ} (dpos : 0 < D)
    (hk : 64 ≤ K) (S : Finset ℕ) (bounded : ∀ r∈S, r<D) {δ : ℝ}
    (lim : Tendsto (sampleFreq P) atTop (𝓝 δ))
    (cnt : ∀ X, sample (repeats D S) X ≤ sample P X+(largeCommon K X).card) :
    (S.card:ℝ)/D-4/K ≤ δ := by
  let C := (D:ℝ)+1+8*K^2
  have err (X : ℕ) (hx : 0 < X) : (S.card:ℝ)/D-4/K-C/X ≤ sampleFreq P X := by
    have xp : 0 < (X:ℝ) := by exact_mod_cast hx
    have periodic := (abs_le.mp (periodic_freq_error dpos (repeats_period D S) hx)).1
    rw [repeats_mean S bounded] at periodic
    have tail := large_common_frequency_bound hk hx
    have le : sampleFreq (repeats D S) X ≤ sampleFreq P X+((largeCommon K X).card:ℝ)/X := by
      unfold sampleFreq
      rw [←add_div]
      apply div_le_div_of_nonneg_right _ xp.le
      exact_mod_cast cnt X
    have split : C/X=D/X+(1+8*(K:ℝ)^2)/X := by dsimp [C]; ring
    rw [split]
    linarith
  have l := (tendsto_const_nhds (x:=(S.card:ℝ)/D-4/K)).sub (tendsto_const_div_atTop_nhds_zero_nat C)
  apply le_of_tendsto_of_tendsto (by simpa only [sub_zero] using l) lim
  filter_upwards [eventually_gt_atTop 0] with X hx using err X hx

private lemma local_gcd {A n t : ℕ} (ret : A ∣ Nat.fib A) (small : t < A) (cl : n ≡ t [MOD A]) :
    (t.gcd A).gcd (lucasFibonacciSum n)=residueGcd A t := by
  rw [←cl.gcd_eq,Nat.gcd_comm n A,Nat.gcd_assoc,←residueGcd_mod ret,Nat.mod_eq_of_modEq cl small]

/-- Inside a realizing class modulo A, count all cofactor residues avoiding primes up
to K². Any of these indices missed by the exact fiber has a large common prime. -/
theorem exact_fiber_rough_lower {A m a d t : ℕ} (pos : 0 < A) (ret : A ∣ Nat.fib A)
    (ma : m ∣ A) (small : t<A) (cl : t ≡ a [MOD m]) (val : residueGcd A t=d)
    {δ : ℝ} (lim : Tendsto (sampleFreq (gcdFiber m a d)) atTop (𝓝 δ)) {K : ℕ} (hk : 64 ≤ K) :
    let P := roughProduct (A/(t.gcd A)) (K^2)
    (P.totient:ℝ)/(A*P)-4/K ≤ δ := by
  let g := t.gcd A
  let L := A/g
  let h := t/g
  let P := roughProduct L (K^2)
  let gp : 0 < g := Nat.gcd_pos_of_pos_right _ pos
  have gL : g*L=A := Nat.mul_div_cancel' (Nat.gcd_dvd_right ..)
  have gh : g*h=t := Nat.mul_div_cancel' (Nat.gcd_dvd_left ..)
  have lp : 0 < L := Nat.div_pos (Nat.le_of_dvd pos (Nat.gcd_dvd_right ..)) gp
  have pp : 0 < P := roughProduct_pos ..
  have co : L.Coprime P := coprime_roughProduct ..
  have unit : h.Coprime L := Nat.coprime_div_gcd_div_gcd gp
  let S := roughResidues g h L P co
  have bound (r : ℕ) (hr : r∈S) : r<A*P := gL ▸ roughResidues_lt gp lp pp co hr
  have cnt (X : ℕ) : sample (repeats (A*P) S) X ≤ sample (gcdFiber m a d) X+(largeCommon K X).card := by
    have sub : (Icc 1 X).filter (repeats (A*P) S) ⊆ (Icc 1 X).filter (gcdFiber m a d) ∪ largeCommon K X := by
      intro n hn
      obtain ⟨bounds,hit⟩ := mem_filter.mp hn
      change n%(A*P)∈S at hit
      rw [←gL] at hit
      obtain ⟨q,split,qcl,cp⟩ := cofactor_of_rough_residue co hit
      have ncl : n ≡ t [MOD A] := by simpa only [gL,gh,←split] using qcl.mul_left' g
      have trunc := (local_gcd ret small ncl).trans val
      by_cases good : q.Coprime (lucasFibonacciSum n)
      · have eq := Nat.Coprime.gcd_mul_right_cancel g good
        rw [←split] at eq
        exact mem_union_left _ (mem_filter.mpr ⟨bounds,(ncl.of_dvd ma).trans cl,eq.trans trunc⟩)
      obtain ⟨p,ppr,pdv⟩ := Nat.exists_prime_and_dvd good
      obtain ⟨pq,pu⟩ := Nat.dvd_gcd_iff.mp pdv
      have pn : p ∣ n := split ▸ dvd_mul_of_dvd_right pq g
      have qL : q.Coprime L := qcl.gcd_eq.trans unit
      have big : K^2 ≤ p := by
        by_contra! lo
        rcases small_prime_dvd_rough (L:=L) ppr lo.le with pL|pP
        · exact ppr.not_dvd_one (qL ▸ Nat.dvd_gcd pq pL)
        · exact ppr.not_dvd_one (cp ▸ Nat.dvd_gcd pq pP)
      refine mem_union_right _ (mem_filter.mpr ⟨bounds,p,?_,big,pu⟩)
      exact ppr.mem_primeFactors pn (by have := (mem_Icc.mp bounds).1; omega)
    exact (card_le_card sub).trans (card_union_le ..)
  have low := residue_lower_density (Nat.mul_pos pos pp) hk S bound lim cnt
  simpa only [S,roughResidues_card gp co,Nat.cast_mul] using low

#print axioms exact_fiber_rough_lower

end Arxiv.«2211.10788».IndexDivisors
