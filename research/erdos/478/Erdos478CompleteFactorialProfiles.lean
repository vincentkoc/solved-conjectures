import Erdos478OccupiedFactorialCosets
import Mathlib.FieldTheory.Finite.Basic

/-! # Full relative coset patterns at three consecutive positive factorial indices -/

namespace Erdos478.CyclotomicProfiles
open Finset
open scoped Classical
noncomputable section

private theorem strict_support {d h N s : ℕ} (pos : 1≤d) (large : d^3+3≤h)
    (size : N+2=d*h) (bound : N^2≤s*(N+(h-1)*(h-2))) : d^2≤s := by
  by_contra! short
  let E : ℤ := N+((h:ℤ)-1)*(h-2)
  have energy : (N:ℤ)^2≤s*E := by
    have h₁ : 1≤h := by omega
    have h₂ : 2≤h := by omega
    zify [h₁,h₂] at bound
    exact bound
  have sz : (N:ℤ)=(d:ℤ)*h-2 := by
    have eq : (N:ℤ)+2=d*h := by exact_mod_cast size
    omega
  have hh : (2:ℤ)≤h := by exact_mod_cast (by omega : 2≤h)
  have he : 0≤E := add_nonneg (by positivity) (mul_nonneg (by omega) (by omega))
  have small : (s:ℤ)+1≤(d:ℤ)^2 := by exact_mod_cast (show s+1≤d^2 by omega)
  have le := mul_le_mul_of_nonneg_right small he
  have a : 0≤(h:ℤ)-((d:ℤ)^3+3) := by exact sub_nonneg.mpr (by exact_mod_cast large)
  have b : 0≤(d:ℤ)-1 := by exact sub_nonneg.mpr (by exact_mod_cast pos)
  have extra : 0≤((h:ℤ)-(d^3+3))*h+3*(d:ℤ)*(d-1)*h :=
    add_nonneg (mul_nonneg a (by positivity)) (mul_nonneg (mul_nonneg (by positivity) b) (by positivity))
  dsimp [E] at le energy
  rw [sz] at le energy
  nlinarith only [extra,energy,le]

variable {p : ℕ} [hp : Fact p.Prime]

/-- For a subgroup of index d and order at least d³+3, each pair of prescribed
successive ratios of coset labels occurs at actual positive consecutive factorial indices. -/
theorem all_relative_patterns (H : Subgroup (ZMod p)ˣ) (large : H.index^3+3≤Nat.card H)
    (u v : (ZMod p)ˣ ⧸ H) :
    ∃ i : ℕ, 1 ≤ i ∧ i + 2 < p ∧
      factorialLabel H (i+1)/factorialLabel H i=u ∧
      factorialLabel H (i+2)/factorialLabel H (i+1)=v := by
  let J := Ico 2 (p-1)
  let V := J.image fun j : ℕ => (j:ZMod p)
  have prod := H.card_mul_index
  rw [Nat.card_eq_fintype_card (α:=(ZMod p)ˣ),ZMod.card_units] at prod
  have dpos : 1≤H.index := Nat.card_pos (α:=(ZMod p)ˣ ⧸ H)
  have hp5 : 5≤p := by
    have one := Nat.pow_le_pow_left dpos 3
    have h := Nat.mul_le_mul_left (Nat.card H) dpos
    omega
  have reg (x) (hx : x∈V) : Regular x := by
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hx
    obtain ⟨lo,hi⟩ := mem_Ico.mp hj
    have nz (i : ℕ) (ip : 0 < i) (lim : i < p) : (i:ZMod p)≠0 := by
      rw [Ne,ZMod.natCast_eq_zero_iff]; exact Nat.not_dvd_of_pos_of_lt ip lim
    exact ⟨nz _ (by omega) (by omega),by simpa only [Nat.cast_succ] using nz (j+1) (by omega) (by omega)⟩
  have card : V.card=p-3 := by
    rw [show V=J.image (fun j : ℕ => (j:ZMod p)) from rfl,card_image_of_injOn,show J=Ico 2 (p-1) from rfl,Nat.card_Ico]
    · omega
    · intro i hi j hj eq
      obtain ⟨_,il⟩ := mem_Ico.mp hi
      obtain ⟨_,jl⟩ := mem_Ico.mp hj
      have e := (ZMod.natCast_eq_natCast_iff' ..).mp eq
      rwa [Nat.mod_eq_of_lt (by omega : i<p),Nat.mod_eq_of_lt (by omega : j<p)] at e
  have support := profile_occupation H V reg
  have sz : V.card+2=H.index*Nat.card H := by rw [card,mul_comm,prod]; omega
  have full := strict_support dpos large sz support
  have all : V.image (labelPair H)=univ := by
    apply eq_of_subset_of_card_le (subset_univ _)
    rwa [card_univ,Fintype.card_prod,← Nat.card_eq_fintype_card,
      show Nat.card ((ZMod p)ˣ ⧸ H)=H.index from rfl,← sq]
  obtain ⟨x,hx,hpat⟩ := mem_image.mp (all ▸ mem_univ (u,v))
  obtain ⟨j,hj,rfl⟩ := mem_image.mp hx
  obtain ⟨jl,ju⟩ := mem_Ico.mp hj
  let i := j-1
  have ident : i+1=j := by dsimp [i]; omega
  have lim : i+2<p := by omega
  refine ⟨i,by dsimp [i]; omega,lim,?_,?_⟩
  · rw [next_label H (by omega),ident]
    exact congrArg Prod.fst hpat
  · rw [next_label H (i:=i+1) lim,Nat.cast_succ,ident]
    exact congrArg Prod.snd hpat

#print axioms all_relative_patterns
end
end Erdos478.CyclotomicProfiles
