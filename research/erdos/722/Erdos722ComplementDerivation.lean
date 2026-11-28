import Erdos722AlltopSignedExtension

/-! # Derivation and uniqueness of complementary extensions

A self-complementary extension is determined by its blocks through a named
point. At codimension one and even block size, every signed design on twice
as many points is automatically self-complementary.
-/

namespace Erdos722.ComplementExtension
open Finset IntegralDesign
variable {α : Type*} [DecidableEq α]

def Symmetric (V : Finset α) (k : ℕ) (w : Finset α → ℤ) :=
  ∀ B∈V.powersetCard k, w (V\B)=w B

theorem extend_symmetric {o : α} {V : Finset α} (ho : o∉V) (k : ℕ) (w : Finset α → ℤ) :
    Symmetric (insert o V) k (extend o V w) := by
  intro B hB
  have sub := (mem_powersetCard.mp hB).1
  by_cases h : o∈B
  · have e : V\(insert o V\B)=B.erase o := by ext x; simp; grind
    have no : o∉insert o V\B := by simp [h]
    simp only [extend,if_neg no,if_pos h,e]
  · have e : (insert o V\B).erase o=V\B := by ext x; simp; grind
    have yes : o∈insert o V\B := by simp [h]
    simp only [extend,if_pos yes,if_neg h,e]

theorem derive_signed {o : α} {V : Finset α} (ho : o∉V) {r k : ℕ} {l : ℤ} {z : Finset α → ℤ}
    (hz : Represents (insert o V) (r+1) (k+1) (fun _ => l) z) :
    Represents V r k (fun _ => l) (fun B => z (insert o B)) := by
  intro A hA
  obtain ⟨sub,hc⟩ := mem_powersetCard.mp hA
  have no : o∉A := fun h => ho (sub h)
  have h := hz (insert o A) (mem_powersetCard.mpr ⟨insert_subset_insert _ sub,by rw [card_insert_of_notMem no,hc]⟩)
  rwa [incidence_insert ho,incidence_outside (fun hh => ho (hh (mem_insert_self ..))),zero_add,erase_insert no] at h

/-- Equality on the punctured k-layer and complement symmetry fix every
weight on the extended layer. -/
theorem unique_on_layer {o : α} {V : Finset α} (ho : o∉V) {k : ℕ} (hv : V.card=2*k+1)
    {z w : Finset α → ℤ} (hz : Symmetric (insert o V) (k+1) z)
    (derived : ∀ A∈V.powersetCard k, z (insert o A)=w A) :
    ∀ B∈(insert o V).powersetCard (k+1), z B=extend o V w B := by
  intro B hB
  obtain ⟨sub,hc⟩ := mem_powersetCard.mp hB
  by_cases h : o∈B
  · have er : B.erase o⊆V := by
      intro x hx
      exact (mem_insert.mp (sub (mem_erase.mp hx).2)).resolve_left (mem_erase.mp hx).1
    have he := derived _ (mem_powersetCard.mpr ⟨er,by rw [card_erase_of_mem h,hc]; omega⟩)
    rwa [insert_erase h,show extend o V w B=w (B.erase o) from if_pos h] at *
  · have bv := (subset_insert_iff_of_notMem h).mp sub
    have c : V\B∈V.powersetCard k :=
      mem_powersetCard.mpr ⟨sdiff_subset,by rw [card_sdiff_of_subset bv,hv,hc]; omega⟩
    have eq : insert o V\B=insert o (V\B) := by ext x; simp; grind
    rw [extend,if_neg h,← hz B hB,eq]
    exact derived _ c

private theorem diagonal {V A : Finset α} {k : ℕ} (hA : A∈V.powersetCard k) (w : Finset α → ℤ) :
    incidence V k w A=w A := by
  unfold incidence
  rw [sum_eq_single A]
  · intro B hB hne
    have sub := (mem_filter.mp hB).2
    have hc := (mem_powersetCard.mp (mem_filter.mp hB).1).2
    exact (hne (eq_of_subset_of_card_le sub (by rw [hc,(mem_powersetCard.mp hA).2])).symm).elim
  · exact fun hn => (hn (mem_filter.mpr ⟨hA,Subset.rfl⟩)).elim

/-- For even k>0, every signed (k-1)-design on 2k points with block
size k assigns the same weight to complementary sets. -/
theorem automatic_symmetry {V : Finset α} {k : ℕ} (hk : 0<k) (even : Even k)
    (hv : V.card=2*k) {l : ℤ} {w : Finset α → ℤ}
    (hw : Represents V (k-1) k (fun _ => l) w) : Symmetric V k w := by
  intro A ha
  obtain ⟨sub,hc⟩ := mem_powersetCard.mp ha
  let f := center V (k-1) k l w
  have dual := next_row_duality (k:=k) (r:=k-1) (by omega) (center_zero (by omega) hw) (A:=A) (by omega)
  change avoiding V k f A=(-1:ℤ)^A.card*incidence V k f A at dual
  rw [← complement_incidence (j:=k) (k:=k) (by omega) sub,diagonal ha,diagonal ha,hc,even.neg_one_pow,one_mul] at dual
  have pos : 0<(V.card-(k-1)).choose (k-(k-1)) := Nat.choose_pos (by omega)
  have nz : (((V.card-(k-1)).choose (k-(k-1)):ℕ):ℤ)≠0 := by exact_mod_cast pos.ne'
  exact mul_left_cancel₀ nz (sub_left_inj.mp dual)

#print axioms Symmetric
#print axioms extend_symmetric
#print axioms derive_signed
#print axioms unique_on_layer
#print axioms automatic_symmetry
end Erdos722.ComplementExtension
