import Erdos722QuadruplePointMotion

/-! # Cubic block motion of nonidentity Steiner quadruple system automorphisms -/

namespace Erdos722.QuadSwitch
open Finset Equiv Function
variable {n : ℕ} {H : Finset (Finset (Fin n))}

def movedBlocks (H : Finset (Finset (Fin n))) (σ : Perm (Fin n)) :=
  H.filter fun B => σ.finsetCongr B≠B

theorem block_motion_card (σ : Perm (Fin n)) (hp : σ.finsetCongr.finsetCongr H=H) :
    (blockPerm σ hp).support.card=(movedBlocks H σ).card := by
  classical
  have eq : (blockPerm σ hp).support=H.attach.filter (fun i => σ.finsetCongr i.val≠i.val) := by
    ext i
    simp only [Perm.mem_support,mem_filter,mem_attach,true_and]
    exact not_congr Subtype.ext_iff
  rw [eq,filter_attach (fun B => σ.finsetCongr B≠B) H,card_map,card_attach]
  rfl

/-- A fixed block containing a moved point x also contains its image. Subtract
the pair degree from the point degree to bound moving incidences at x. -/
theorem through_moved_point (hH : H.IsBlockDesign 3 4) (σ : Perm (Fin n)) {x : Fin n} (hx : σ x≠x) :
    (n-2)*(n-4)≤6*((movedBlocks H σ).filter (x∈·)).card := by
  classical
  let D := H.filter (x∈·)
  let F := D.filter fun B => σ.finsetCongr B=B
  let S := D.filter fun B => σ.finsetCongr B≠B
  have spl : F.card+S.card=D.card := card_filter_add_card_filter_not ..
  have fixLe : F ⊆ H.filter ({σ x,x}⊆·) := by
    intro B hB
    obtain ⟨hm,he⟩ := mem_filter.mp hB
    obtain ⟨hb,hxb⟩ := mem_filter.mp hm
    exact mem_filter.mpr ⟨hb,insert_subset (he ▸ mem_map.mpr ⟨x,hxb,rfl⟩) (singleton_subset_iff.mpr hxb)⟩
  have le := Nat.mul_le_mul_left 2 (card_le_card fixLe)
  rw [pair_degree hH hx] at le
  have count := IntegralDesign.flag_count hH {x} (by simp)
  have deg : 3*D.card=(n-1).choose 2 := by simpa [D] using count
  have ar := Nat.choose_succ_right_eq (n-1) 1
  simp only [Nat.choose_one_right,Nat.reduceAdd] at ar
  have step : n-1-1=n-2 := by omega
  rw [step,← deg] at ar
  have eq : (movedBlocks H σ).filter (x∈·)=S := by
    ext B
    simp only [movedBlocks,S,D,mem_filter]
    tauto
  rw [eq]
  by_cases small : n<4
  · simp [show n-4=0 by omega]
  have n1 : n-1=(n-4)+3 := by omega
  have n2 : n-2=(n-4)+2 := by omega
  rw [n1,n2] at ar
  rw [n2] at le ⊢
  nlinarith

/-- A nonidentity base automorphism moves at least n(n−2)(n−4)/48 blocks. -/
theorem quadruple_block_motion (hH : H.IsBlockDesign 3 4) (σ : Perm (Fin n))
    (hp : σ.finsetCongr.finsetCongr H=H) (ne : σ≠Equiv.refl _) :
    n*(n-2)*(n-4)≤48*(blockPerm σ hp).support.card := by
  classical
  let M := movedBlocks H σ
  let S := σ.support
  have localCount (x : Fin n) (hx : x∈S) := through_moved_point hH σ (Perm.mem_support.mp hx)
  have atBlock (B : Finset (Fin n)) (hb : B∈M) : (S.filter (·∈B)).card≤4 := by
    rw [← hH.1 B (mem_filter.mp hb).1]
    exact card_le_card fun x hx => (mem_filter.mp hx).2
  have flags : (∑ x∈S,(M.filter (x∈·)).card)=(∑ B∈M,(S.filter (·∈B)).card) := by
    simp only [card_filter]
    exact sum_comm
  have hi := sum_le_sum localCount
  change (∑ _∈S,(n-2)*(n-4))≤(∑ x∈S,6*(M.filter (x∈·)).card) at hi
  rw [← mul_sum S _ 6,flags] at hi
  have lim := sum_le_sum atBlock
  simp only [sum_const,nsmul_eq_mul] at hi lim
  have pts := point_motion hH σ hp ne
  change n≤2*S.card at pts
  rw [block_motion_card]
  change _≤48*M.card
  calc
    n*(n-2)*(n-4) ≤ (2*S.card)*((n-2)*(n-4)) := by
      rw [mul_assoc]; exact Nat.mul_le_mul_right _ pts
    _ = 2*(S.card*((n-2)*(n-4))) := by ring
    _ ≤ 2*(6*(M.card*4)) := Nat.mul_le_mul_left 2 (hi.trans (Nat.mul_le_mul_left 6 lim))
    _ = _ := by ring

#print axioms movedBlocks
#print axioms block_motion_card
#print axioms through_moved_point
#print axioms quadruple_block_motion
end Erdos722.QuadSwitch
