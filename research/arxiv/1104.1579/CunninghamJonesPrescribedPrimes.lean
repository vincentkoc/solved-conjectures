import CunninghamJonesWeightedResidues
import Mathlib.NumberTheory.LSeries.PrimesInAP

/-! Simultaneous prime residue conditions for Jones coefficients. -/

namespace CunninghamChain.JonesSplitParity
open Finset

private theorem prime_in_joint_classes (S : Finset ℕ) (r a : ℕ → ℕ) (D b B : ℕ)
    (hD : 0 < D) (hb : b.Coprime D) (hr : ∀ i ∈ S, 0 < r i)
    (hpair : Set.Pairwise S (fun i j => (r i).Coprime (r j)))
    (ha : ∀ i ∈ S, (a i).Coprime (r i)) (hsep : ∀ i ∈ S, D.Coprime (r i)) :
    ∃ p > B, p.Prime ∧ p ≡ b [MOD D] ∧ ∀ i ∈ S, p ≡ a i [MOD r i] := by
  classical
  let R := ∏ i ∈ S,r i
  have hR : 0 < R := prod_pos hr
  obtain ⟨c,hc⟩ := Nat.chineseRemainderOfFinset a r S (fun i hi => (hr i hi).ne') hpair
  obtain ⟨d,hd,hc'⟩ := Nat.chineseRemainder (Nat.Coprime.prod_right hsep) b c
  have hdD : d.Coprime D := hd.gcd_eq.trans hb
  have hdR : d.Coprime R := by
    apply Nat.Coprime.prod_right
    intro i hi
    exact ((hc'.of_dvd (dvd_prod_of_mem r hi)).trans (hc i hi)).gcd_eq.trans (ha i hi)
  obtain ⟨p,hp,hpr,h⟩ := Nat.forall_exists_prime_gt_and_modEq B (Nat.mul_pos hD hR).ne'
    (Nat.Coprime.mul_right hdD hdR)
  refine ⟨p,hp,hpr,(h.of_dvd (dvd_mul_right D R)).trans hd,?_⟩
  intro i hi
  exact (((h.of_dvd (dvd_mul_left R D)).trans hc').of_dvd (dvd_prod_of_mem r hi)).trans (hc i hi)

/-- A prime list with prescribed global residues and successive weighted fourth roots. -/
structure PrescribedPrefix (q residue weight : ℕ → ℕ) (s D B : ℕ) : Prop where
  prime : ∀ i < s, (q i).Prime
  large : ∀ i < s, max 2 B < q i
  increasing : StrictMonoOn q (Set.Iio s)
  residues : ∀ i < s, q i ≡ residue i [MOD D]
  nextSquare : ∀ i, i+1 < s → ((q (i+1) : ZMod (q i))^(weight (i+1)))^2 = -1
  laterResidues : ∀ i j, i+1 < j → j < s → (q j : ZMod (q i))=1

/-- Assemble the global residues and the pairwise conditions by CRT and Dirichlet. -/
theorem exists_prescribed_prefix (D B : ℕ) (residue weight : ℕ → ℕ)
    (hD : 0 < D) (hw : ∀ i, 0 < weight i) (hunit : ∀ i, (residue i).Coprime D)
    (hdiv : ∀ i, 4*weight (i+1) ∣ D)
    (hone : ∀ i, residue i ≡ 1 [MOD 4*weight (i+1)]) (s : ℕ) :
    ∃ q : ℕ → ℕ, PrescribedPrefix q residue weight s D B := by
  classical
  induction s with
  | zero => exact ⟨fun _ => 0, by constructor <;> simp; intro i hi; exact False.elim hi⟩
  | succ s ih =>
    obtain ⟨q,h⟩ := ih
    have root (i : ℕ) (hi : i<s) : ∃ c : ℕ, c.Coprime (q i) ∧
        ((c:ZMod (q i))^(weight (i+1)))^2 = -1 := by
      have hr := ((h.residues i hi).of_dvd (hdiv i)).trans (hone i)
      exact exists_weighted_fourth_root (h.prime i hi) (by have := h.large i hi; omega)
        (hw _) hr.symm.dvd'
    choose c hcop hc using root
    let a (i : ℕ) := if hi : i<s then (if i+1=s then c i hi else 1) else 1
    have hlocal (i : ℕ) (hi : i<s) : (a i).Coprime (q i) := by
      simp only [a,dif_pos hi]
      split_ifs
      · exact hcop i hi
      · simp
    have hsep (i : ℕ) (hi : i<s) : D.Coprime (q i) :=
      Nat.Coprime.symm ((h.residues i hi).gcd_eq.trans (hunit i))
    have hpair : Set.Pairwise (range s : Finset ℕ) (fun i j => (q i).Coprime (q j)) := by
      intro i hi j hj hne
      exact (Nat.coprime_primes (h.prime i (mem_range.mp hi)) (h.prime j (mem_range.mp hj))).mpr
        (h.increasing.injOn.ne (mem_range.mp hi) (mem_range.mp hj) hne)
    obtain ⟨p,hp,hpr,hdy,hsmall⟩ := prime_in_joint_classes (range s) q a D (residue s)
      (max (max 2 B) ((range s).sup q)) hD
      (hunit s) (fun i hi => (h.prime i (mem_range.mp hi)).pos)
      hpair (fun i hi => hlocal i (mem_range.mp hi)) (fun i hi => hsep i (mem_range.mp hi))
    let q' (i : ℕ) := if i=s then p else q i
    have old (i : ℕ) (hi : i<s) : q' i=q i := if_neg hi.ne
    have last : q' s=p := if_pos rfl
    have above (i : ℕ) (hi : i<s) : q i<p := lt_of_le_of_lt (le_sup (f:=q) (mem_range.mpr hi)) ((le_max_right ..).trans_lt hp)
    refine ⟨q',⟨?_,?_,?_,?_,?_,?_⟩⟩
    · intro i hi
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hlt|rfl
      · rw [old i hlt]; exact h.prime i hlt
      · rwa [last]
    · intro i hi
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hlt|rfl
      · rw [old i hlt]; exact h.large i hlt
      · rw [last]; exact (le_max_left ..).trans_lt hp
    · intro i hi j hj hij
      change j<s+1 at hj
      rw [old i (by omega)]
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hlt|rfl
      · rw [old j hlt]; exact h.increasing (by change i<s; omega) hlt hij
      · rw [last]; exact above i hij
    · intro i hi
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hlt|rfl
      · rw [old i hlt]; exact h.residues i hlt
      · rwa [last]
    · intro i hi
      have hil : i<s := by omega
      rw [old i hil]
      by_cases hl : i+1=s
      · rw [hl,last,(ZMod.natCast_eq_natCast_iff ..).mpr (hsmall i (mem_range.mpr hil))]
        simpa [a,hil,hl] using hc i hil
      · rw [old (i+1) (by omega)]
        exact h.nextSquare i (by omega)
    · intro i j hij hj
      have hil : i<s := by omega
      rw [old i hil]
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hlt|rfl
      · rw [old j hlt]; exact h.laterResidues i j hij hlt
      · rw [last,(ZMod.natCast_eq_natCast_iff ..).mpr (hsmall i (mem_range.mpr hil))]
        simp [a,hil,show i+1≠j by omega]

#print axioms exists_prescribed_prefix

end CunninghamChain.JonesSplitParity
