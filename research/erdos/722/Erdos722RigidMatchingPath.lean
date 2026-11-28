import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic

/-! # A marked path with trivial symmetry on the base vertices -/

namespace Erdos722.FourPoint
open Equiv

/-- The star and the first path edge have label one. Subsequent consecutive
edges have label two, and the remaining nonstar edges have label three. -/
def pathTag (i j : ℕ) : ℕ :=
  if i=0 ∨ j=0 ∨ i=j ∨ i+j=3 then 1 else if i+1=j ∨ j+1=i then 2 else 3

theorem pathTag_symm (i j : ℕ) : pathTag i j=pathTag j i := by
  unfold pathTag; split_ifs <;> omega

theorem pathTag_one (i j : ℕ) : pathTag i j=1 ↔ i=0 ∨ j=0 ∨ i=j ∨ i+j=3 := by
  unfold pathTag; split_ifs <;> omega

theorem pathTag_two (i j : ℕ) : pathTag i j=2 ↔ 2 ≤ i ∧ 2 ≤ j ∧ (i+1=j ∨ j+1=i) := by
  unfold pathTag; split_ifs <;> omega

/-- The universal one-star fixes vertex zero. Vertex one is the only other
vertex off the two-path. Its one-edge fixes vertex two, and each remaining
vertex is the next vertex of the path. -/
theorem pathTag_rigid (m : ℕ) (p : Perm (Fin (m+4)))
    (h : ∀ i j, pathTag (p i).val (p j).val=pathTag i.val j.val) : p=1 := by
  let z : Fin (m+4) := ⟨0,by omega⟩
  let a : Fin (m+4) := ⟨1,by omega⟩
  let b : Fin (m+4) := ⟨2,by omega⟩
  let c : Fin (m+4) := ⟨3,by omega⟩
  have hz (j : Fin (m+4)) : pathTag (p z).val j.val=1 := by
    simpa only [Equiv.apply_symm_apply] using
      (h z (p.symm j)).trans ((pathTag_one ..).mpr (Or.inl rfl))
  have zfix : p z=z := by
    have h₁ := (pathTag_one ..).mp (hz a)
    have h₃ := (pathTag_one ..).mp (hz c)
    apply Fin.ext; dsimp only [a,c,z] at *; omega
  have n2 (j : Fin (m+4)) : pathTag (p a).val j.val≠2 := by
    intro eq
    have h' := h a (p.symm j)
    rw [Equiv.apply_symm_apply,eq] at h'
    have := ((pathTag_two ..).mp h'.symm).1
    change 2≤1 at this; omega
  have afix : p a=a := by
    have hn : p a≠z := zfix ▸ p.injective.ne (show a≠z by intro eq; have he := congrArg Fin.val eq; exact (by decide : (1:ℕ)≠0) he)
    have nz : (p a).val≠0 := fun he => hn (Fin.ext he)
    apply Fin.ext
    change (p a).val=1
    by_contra ht
    by_cases hb : (p a).val=2
    · apply n2 c
      apply (pathTag_two ..).mpr
      dsimp only [c]; omega
    · let j : Fin (m+4) := ⟨(p a).val-1,by have := (p a).isLt; omega⟩
      apply n2 j
      apply (pathTag_two ..).mpr
      dsimp only [j]; omega
  have pval {i j : Fin (m+4)} (hi : p i=i) (ne : i≠j) : (p j).val≠i.val := by
    intro eq
    exact ne (p.injective (hi.trans (Fin.ext eq).symm))
  have bfix : p b=b := by
    have h' := (pathTag_one ..).mp ((h a b).trans ((pathTag_one ..).mpr (Or.inr (Or.inr (Or.inr rfl)))))
    rw [afix] at h'
    have hz' := pval zfix (j:=b) (by intro eq; have := congrArg Fin.val eq; change 0=2 at this; omega)
    have ha' := pval afix (j:=b) (by intro eq; have := congrArg Fin.val eq; change 1=2 at this; omega)
    apply Fin.ext; dsimp only [z,a,b] at *; omega
  have all (n : ℕ) (hn : n<m+4) : (p ⟨n,hn⟩).val=n := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases small : n<3
      · obtain rfl|rfl|rfl : n=0 ∨ n=1 ∨ n=2 := by omega
        · exact congrArg Fin.val zfix
        · exact congrArg Fin.val afix
        · exact congrArg Fin.val bfix
      let u : Fin (m+4) := ⟨n-1,by omega⟩
      let v : Fin (m+4) := ⟨n-2,by omega⟩
      let i : Fin (m+4) := ⟨n,hn⟩
      have uf : p u=u := Fin.ext (ih (n-1) (by omega) u.isLt)
      have vf : p v=v := Fin.ext (ih (n-2) (by omega) v.isLt)
      have adj := (pathTag_two ..).mp ((h u i).trans ((pathTag_two ..).mpr (by change 2 ≤ n-1 ∧ 2 ≤ n ∧ (n-1+1=n ∨ n+1=n-1); omega)))
      rw [uf] at adj
      have ne := pval vf (j:=i) (by intro eq; have := congrArg Fin.val eq; dsimp only [v,i] at this; omega)
      change (p i).val=n
      change 2 ≤ n-1 ∧ 2 ≤ (p i).val ∧ (n-1+1=(p i).val ∨ (p i).val+1=n-1) at adj
      change (p i).val≠n-2 at ne
      omega
  exact Equiv.ext fun i => Fin.ext (all i.val i.isLt)

#print axioms pathTag
#print axioms pathTag_symm
#print axioms pathTag_one
#print axioms pathTag_two
#print axioms pathTag_rigid
end Erdos722.FourPoint
