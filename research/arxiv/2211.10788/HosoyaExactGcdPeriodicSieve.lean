import LucasFibonacciExactGcdSpectrum

/-! Finite periodic approximations to an exact index–value gcd on an index progression. -/

namespace Arxiv.«2211.10788».IndexDivisors
open Finset

def gcdFiber (m a d n : ℕ) : Prop := n ≡ a [MOD m] ∧ n.gcd (lucasFibonacciSum n)=d
instance (m a d n : ℕ) : Decidable (gcdFiber m a d n) := by unfold gcdFiber; infer_instance

def finiteFiber (A m a d n : ℕ) : Prop := n%A ≡ a [MOD m] ∧ residueGcd A (n%A)=d
instance (A m a d n : ℕ) : Decidable (finiteFiber A m a d n) := by unfold finiteFiber; infer_instance

lemma finiteFiber_periodic (A m a d : ℕ) : Function.Periodic (finiteFiber A m a d) A := by
  intro n
  simp only [finiteFiber,Nat.add_mod_right]

lemma finiteFiber_iff {A m a d n : ℕ} (ret : A ∣ Nat.fib A) (mD : m ∣ A) :
    finiteFiber A m a d n ↔ n ≡ a [MOD m] ∧ A.gcd (n.gcd (lucasFibonacciSum n))=d := by
  have cl := (Nat.mod_modEq n A).of_dvd mD
  rw [finiteFiber,residueGcd_mod ret]
  exact and_congr_left fun _ => ⟨fun h => cl.symm.trans h,fun h => cl.trans h⟩

/-- A finite test that covers dp for each small prime p can only overcount exact
gcd d at an index sharing a large prime factor with its upper value. -/
theorem finiteFiber_error {A m d : ℕ} (ret : A ∣ Nat.fib A) (mD : m ∣ A) (dD : d ∣ A)
    (hd : 0 < d) (a K X : ℕ) (cover : ∀ p < K^2, p.Prime → d*p ∣ A) :
    sample (gcdFiber m a d) X ≤ sample (finiteFiber A m a d) X ∧
      sample (finiteFiber A m a d) X ≤ sample (gcdFiber m a d) X + (largeCommon K X).card := by
  constructor
  · apply card_le_card
    intro n hn
    obtain ⟨bounds,cl,val⟩ := mem_filter.mp hn
    exact mem_filter.mpr ⟨bounds,(finiteFiber_iff ret mD).mpr ⟨cl,by rw [val,Nat.gcd_eq_right dD]⟩⟩
  have sub : (Icc 1 X).filter (finiteFiber A m a d) ⊆
      (Icc 1 X).filter (gcdFiber m a d) ∪ largeCommon K X := by
    intro n hn
    obtain ⟨bounds,hit⟩ := mem_filter.mp hn
    obtain ⟨cl,trunc⟩ := (finiteFiber_iff ret mD).mp hit
    let c := n.gcd (lucasFibonacciSum n)
    change A.gcd c=d at trunc
    by_cases eq : c=d
    · exact mem_union_left _ (mem_filter.mpr ⟨bounds,cl,eq⟩)
    have divides : d ∣ c := trunc ▸ Nat.gcd_dvd_right ..
    obtain ⟨v,hv⟩ := divides
    have ne : v≠1 := by rintro rfl; simp_all
    obtain ⟨p,hp,pv⟩ := Nat.exists_prime_and_dvd ne
    have dc : d*p ∣ c := hv ▸ Nat.mul_dvd_mul_left d pv
    have pc := (dvd_mul_left p d).trans dc
    have big : K^2 ≤ p := by
      by_contra! small
      have div := Nat.dvd_gcd (cover p small hp) dc
      rw [trunc] at div
      have le := Nat.le_of_dvd hd div
      nlinarith [Nat.mul_lt_mul_of_pos_left hp.one_lt hd]
    refine mem_union_right _ (mem_filter.mpr ⟨bounds,p,?_,big,pc.trans (Nat.gcd_dvd_right ..)⟩)
    exact hp.mem_primeFactors (pc.trans (Nat.gcd_dvd_left ..)) (by have := (mem_Icc.mp bounds).1; omega)
  exact (card_le_card sub).trans (card_union_le ..)

/-- An even factorial covering m and every dp with p at most K². -/
def densityReturn (m d K : ℕ) := (2*(max m (d*(K^2+1))+2)).factorial

lemma densityReturn_spec {m d : ℕ} (hm : 0 < m) (hd : 0 < d) (K : ℕ) :
    0 < densityReturn m d K ∧ densityReturn m d K ∣ Nat.fib (densityReturn m d K) ∧
      m ∣ densityReturn m d K ∧ d ∣ densityReturn m d K ∧
        ∀ p < K^2, p.Prime → d*p ∣ densityReturn m d K := by
  let H := max m (d*(K^2+1))
  have mH : m≤H := le_max_left ..
  have mulH : d*(K^2+1)≤H := le_max_right ..
  have dH := (Nat.le_mul_of_pos_right d (show 0<K^2+1 by omega)).trans mulH
  refine ⟨Nat.factorial_pos _,even_factorial_dvd_fib _,Nat.dvd_factorial hm (by change m≤2*(H+2); omega),
    Nat.dvd_factorial hd (by change d≤2*(H+2); omega),?_⟩
  intro p lo hp
  apply Nat.dvd_factorial (Nat.mul_pos hd hp.pos)
  have bd := Nat.mul_le_mul_left d (show p≤K^2+1 by omega)
  change d*p ≤ 2*(H+2)
  omega

#print axioms finiteFiber_error
#print axioms densityReturn_spec

end Arxiv.«2211.10788».IndexDivisors
