import Erdos722RankOrbitDefect

/-! # Effective symmetry and class count for the whole next binary rank -/

namespace Erdos722.QuadSwitch
open Finset Equiv
noncomputable section

theorem next_rank_nonempty (d : ℕ) (hd : 7≤d) : (nextRankClasses d).Nonempty := by
  classical
  let H := binaryBase d
  obtain ⟨_,enough,room⟩ := binary_motion_budget d hd H.prop
  have more : 2^d < H.val.card := by
    change 2*((2^d)^3/1024)≤H.val.card at enough
    change d*2^d+2^d+1≤(2^d)^3/1024 at room
    omega
  have some : ∃ s : H.val → Bool, ¬Coboundary s := by
    by_contra! all
    have sub : (univ : Finset (H.val → Bool))⊆gaugeAssignments H.val := fun s _ => gauge_mem (all s)
    have bound := (card_le_card sub).trans (gauge_card_le (H:=H.val))
    have bad : 2^H.val.card≤2^(2^d) := by simpa using bound
    exact (Nat.pow_lt_pow_right (by decide : 1<2) more).not_ge bad
  obtain ⟨s,ng⟩ := some
  exact ⟨_,(next_class_mem _).mpr ⟨s,ng,rfl⟩⟩

/-- Let N count unrestricted classes of *all* rank-(2n−d−1) Steiner quadruple
systems on 2n points. The extra one is the unique affine orbit in the switch cube. -/
theorem global_rank_count (d : ℕ) (hd : 7≤d) :
    let n := 2^d
    let b := blockNumber n
    let E := n^3/1024
    let N := (nextRankClasses d).card
    let g := liftOrder d
    2^(d+1)*2^b≤(N+1)*g ∧ ((N+1)*g-2^(d+1)*2^b)*2^E≤2^b := by
  have h := binary_class_estimate d hd
  dsimp only at h ⊢
  rwa [whole_rank_class_count] at h

/-- The exceptional fraction under uniform sampling of unrestricted rank
classes is at most 1/(n·2^E), with E=floor(n³/1024). -/
theorem global_rank_symmetry (d : ℕ) (hd : 7≤d) :
    (exceptionalRankClasses d).card * 2^d * 2^((2^d)^3/1024) ≤ (nextRankClasses d).card := by
  let n := 2^d
  let q := 2^(blockNumber n)
  let t := 2^(n^3/1024)
  let N := (nextRankClasses d).card
  let B := (exceptionalRankClasses d).card
  let g := liftOrder d
  have gp : 0<g := by change 0<liftOrder d; rw [← binary_lift_card]; exact Nat.card_pos
  obtain ⟨floor,margin⟩ := global_rank_count d hd
  change 2^(d+1)*q≤(N+1)*g at floor
  change ((N+1)*g-2^(d+1)*q)*t≤q at margin
  have c : 2^(d+1)=2*n := pow_succ' 2 d
  rw [c] at floor margin
  have defect := exceptional_orbit_defect d
  change B*g+2*(2^(d+1)*q)≤2*(N+1)*g at defect
  rw [c,mul_assoc 2 (N+1) g] at defect
  let err := (N+1)*g-2*n*q
  have split : err+2*n*q=(N+1)*g := Nat.sub_add_cancel floor
  have half : B*g≤2*err := by omega
  have weighted : B*g*t≤2*q := calc
    _ ≤ (2*err)*t := Nat.mul_le_mul_right _ half
    _ = 2*(err*t) := Nat.mul_assoc ..
    _ ≤ _ := Nat.mul_le_mul_left 2 margin
  change B*n*t≤N
  by_cases empty : B=0
  · simp [empty]
  have nz : 0<B*g := Nat.mul_pos (Nat.pos_of_ne_zero empty) gp
  have strict : 2*n*q<(N+1)*g := by omega
  have le : B*n*t*g<(N+1)*g := calc
    _ = B*g*t*n := by ring
    _ ≤ 2*q*n := Nat.mul_le_mul_right _ weighted
    _ = 2*n*q := by ring
    _ < _ := strict
  exact Nat.le_of_lt_succ (Nat.lt_of_mul_lt_mul_right le)

#print axioms next_rank_nonempty
#print axioms global_rank_count
#print axioms global_rank_symmetry
end
end Erdos722.QuadSwitch
