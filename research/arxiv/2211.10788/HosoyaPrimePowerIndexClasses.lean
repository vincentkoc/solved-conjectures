import HosoyaPrimePowerCollisions
import LucasFibonacciProgressionClosure

/-! Two possible index classes at a fixed parity for any prime-power test. -/

namespace Arxiv.«2211.10788».LocalPower
open CongruenceClosure ProgressionClosure

private abbrev uc (n : ℕ) : ℤ := lucasFibonacciSum n

private theorem value_eq {p r d h n m : ℕ} {y : ℤ}
    (hn : Hit d r (p^h) y n) (hm : Hit d r (p^h) y m) :
    uc (r+d*n) ≡ uc (r+d*m) [ZMOD (p:ℤ)^h] := by
  unfold Hit at hn hm
  simpa only [Nat.cast_pow] using hn.trans hm.symm

private theorem pair_roots {p r d h n m : ℕ} {y : ℤ} (hp : p.Prime)
    (par : n ≡ m [MOD 2]) (hn : Hit d r (p^(2*h)) y n) (hm : Hit d r (p^(2*h)) y m) :
    coordinate (r+d*n) ≡ coordinate (r+d*m) [ZMOD (p:ℤ)^h] ∨
    coordinate (r+d*n) ≡ -coordinate (r+d*m) [ZMOD (p:ℤ)^h] := by
  have arg : r+d*n ≡ r+d*m [MOD 2] := (par.mul_left d).add_left r
  have sign : (-1:ℤ)^(r+d*n)=(-1:ℤ)^(r+d*m) := by
    apply neg_one_pow_congr
    simpa only [Nat.even_iff] using (congrArg (·=0) arg) |>.to_iff
  have pell (i : ℕ) : coordinate i^2=5*uc i^2+44*(-1:ℤ)^i := PrimeObstruction.upper_signed_pell i
  apply square_split hp
  rw [pell,pell,sign]
  exact (((value_eq hn hm).pow 2).mul_left 5).add_right _

/-- A set at a fixed parity has at most two residue classes of hits
modulo p^b. The input set may impose additional index restrictions. -/
theorem two_index_classes {p d : ℕ} (hp : p.Prime) (hd : 0<d) :
    ∃ a : ℕ, ∀ (r b : ℕ) (y : ℤ) (P : ℕ → Prop),
      (∀ n m, P n → P m → n ≡ m [MOD 2]) →
      (∀ n, P n → Hit d r (p^(2*(a+b+1))) y n) →
      (∃ n, P n) →
      ∃ u v, P u ∧ P v ∧ ∀ n, P n → n ≡ u [MOD p^b] ∨ n ≡ v [MOD p^b] := by
  obtain ⟨a,rank⟩ := rank_offset hp hd
  refine ⟨a,?_⟩
  intro r b y P parity hits nonempty
  obtain ⟨u,pu⟩ := nonempty
  let h := a+b+1
  have same {n m : ℕ} (pn : P n) (pm : P m)
      (co : coordinate (r+d*n) ≡ coordinate (r+d*m) [ZMOD (p:ℤ)^h]) : n ≡ m [MOD p^b] := by
    apply state_recovery hp rank _ co
    exact (value_eq (hits n pn) (hits m pm)).of_dvd (pow_dvd_pow _ (by omega))
  have roots (n) (pn : P n) := pair_roots hp (parity n u pn pu) (hits n pn) (hits u pu)
  by_cases neg : ∃ v, P v ∧ coordinate (r+d*v) ≡ -coordinate (r+d*u) [ZMOD (p:ℤ)^h]
  · obtain ⟨v,pv,cv⟩ := neg
    refine ⟨u,v,pu,pv,fun n pn => ?_⟩
    rcases roots n pn with eq|op
    · exact Or.inl (same pn pu eq)
    · exact Or.inr (same pn pv (op.trans cv.symm))
  · refine ⟨u,u,pu,pu,fun n pn => Or.inl (same pn pu ?_)⟩
    exact (roots n pn).resolve_right (fun eq => neg ⟨n,pn,eq⟩)

#print axioms two_index_classes

end Arxiv.«2211.10788».LocalPower
