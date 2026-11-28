import Erdos722AffineIngredients

/-!
# Enlarging intervals for a prescribed collection of residues

An interval with a fixed margin can be multiplied by one more than any
usable width divisible by the block size. Round the full group height so
that its one-point completion has residue zero. The last group then has
the residue of the target.
-/

namespace Erdos722.PairDesign

def FullFor (P : ℕ → Prop) (k J l h : ℕ) := 8*J ≤ l ∧
  ∀ u, l ≤ u+4*J → u ≤ h+4*J → P (u%k) → Local k u

private theorem rounded {k : ℕ} (hk : 0<k) (a : ℕ) :
    ∃ δ, 1≤δ ∧ δ≤k ∧ k ∣ a+δ+1 := by
  let b := k*((a+1)/k+1)
  have hb : a+1 < b ∧ b ≤ a+1+k := by
    have := Nat.mod_add_div (a+1) k
    have := Nat.mod_lt (a+1) hk
    dsimp [b]
    rw [Nat.mul_add,Nat.mul_one]
    omega
  refine ⟨b-(a+1),by omega,by omega,?_⟩
  rw [show a+(b-(a+1))+1=b by omega]
  exact dvd_mul_right ..

theorem dilate_for {P : ℕ → Prop} (h₀ : P 0) {k J s N l h : ℕ} (hk : 2≤k) (hs : 0<s) (hds : k ∣ s)
    (H : Adjacent k s) (hN : ∀ t ≥ N, ArrayAt (s+1) t)
    (hnj : N≤J) (hsj : (s+1)*(k+2)≤J) (F : FullFor P k J l h) :
    FullFor P k J ((s+1)*l) ((s+1)*h) := by
  obtain ⟨hl,F⟩ := F
  refine ⟨hl.trans (by simpa using Nat.mul_le_mul_right l (by omega : 1≤ s+1)),?_⟩
  intro u hu hu' ha
  let a := u/(s+1)
  let e := u%(s+1)
  have he : e ≤ s := Nat.le_of_lt_succ (Nat.mod_lt _ (by omega))
  have hrep : e+(s+1)*a=u := Nat.mod_add_div _ _
  have hl' : l ≤ a+3*J := by
    by_contra! Hlt
    have hm := Nat.mul_le_mul_left (s+1) (show a+3*J+1≤l by omega)
    have hp := Nat.mul_le_mul_right J (by omega : 1≤ s)
    nlinarith only [hm,hu,hrep,he,hp]
  have hh' : a ≤ h+2*J := by
    by_contra! Hlt
    have hm := Nat.mul_le_mul_left (s+1) (show h+2*J+1≤a by omega)
    have hp := Nat.mul_le_mul_right J (by omega : 1≤ s)
    nlinarith only [hm,hu',hrep,hp,Nat.zero_le e,Nat.zero_le s]
  obtain ⟨δ,hd,hdk,hb⟩ := rounded (by omega : 0<k) a
  have hprod : s*δ≤J := (Nat.mul_le_mul (by omega : s≤ s+1) (by omega : δ≤k+2)).trans hsj
  have hlo : e≤ s*δ := he.trans (by simpa using Nat.mul_le_mul_left s hd)
  have hJ : 0<J := lt_of_lt_of_le (by positivity) hsj
  let t := a+δ
  let q := a+e-s*δ
  have hqd : q+s*δ=a+e := by dsimp [q]; omega
  have hlow : 0<q := by omega
  have hqu : q ≤ t := by dsimp [t]; omega
  have htN : N ≤ t := by dsimp [t]; omega
  have heq : s*t+q=u := by dsimp [t]; nlinarith only [hqd,hrep]
  have hqmod : q%k=u%k := by
    rw [← heq,Nat.add_mod,Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_left hds _),Nat.zero_add,Nat.mod_mod]
  have htmod : (t+1)%k=0 := Nat.mod_eq_zero_of_dvd hb
  have hdJ : δ≤J := by
    have := Nat.mul_le_mul_right δ hs
    omega
  have ht : Local k (t+1) := F _ (by dsimp [t]; omega) (by dsimp [t]; omega) (htmod ▸ h₀)
  have hq : Local k (q-1+1) := by
    rw [Nat.sub_add_cancel hlow]
    exact F _ (by omega) (by omega) (hqmod ▸ ha)
  have hg := grow hk (hN t htN) H (by omega : q-1 ≤ t) le_rfl ht hq
  rwa [show s*t+(q-1)+1=u by omega] at hg

#print axioms dilate_for
end Erdos722.PairDesign
