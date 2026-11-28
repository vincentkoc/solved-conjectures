import Erdos722ComplementDerivation

/-! # A bijection on integer-weighted design spaces

Weights live on the layer of actual blocks. This fixes the value of the
inverse exactly, including when the index is zero or negative.
-/

namespace Erdos722.ComplementExtension
open Finset IntegralDesign
variable {α : Type*} [DecidableEq α]

abbrev Layer (V : Finset α) (k : ℕ) := (V.powersetCard k) → ℤ

def readWeight {V : Finset α} {k : ℕ} (w : Layer V k) (B : Finset α) : ℤ :=
  if h : B∈V.powersetCard k then w ⟨B,h⟩ else 0

theorem read_mem {V : Finset α} {k : ℕ} (w : Layer V k) {B : Finset α} (h : B∈V.powersetCard k) :
    readWeight w B=w ⟨B,h⟩ := dif_pos h

abbrev Designs (V : Finset α) (r k : ℕ) (l : ℤ) :=
  {w : Layer V k // Represents V r k (fun _ => l) (readWeight w)}

abbrev Complementary (V : Finset α) (r k : ℕ) (l : ℤ) :=
  {z : Designs V r k l // Symmetric V k (readWeight z.val)}

private theorem restrict_design {V : Finset α} {r k : ℕ} {l : ℤ} {w : Finset α → ℤ}
    (hw : Represents V r k (fun _ => l) w) :
    Represents V r k (fun _ => l) (readWeight (V:=V) (k:=k) (fun B => w B.val)) := by
  intro A hA
  exact (incidence_congr (fun _ h => read_mem _ h) A).trans (hw A hA)

private theorem insert_block {V : Finset α} {o : α} (ho : o∉V) {k : ℕ} {B : Finset α}
    (h : B∈V.powersetCard k) : insert o B∈(insert o V).powersetCard (k+1) := by
  obtain ⟨sub,hc⟩ := mem_powersetCard.mp h
  exact mem_powersetCard.mpr ⟨insert_subset_insert _ sub,by rw [card_insert_of_notMem (fun hh => ho (sub hh)),hc]⟩

/-- Alltop extension and derivation are inverse maps for arbitrary signed
index and even strength, with self-complementarity on the extended space. -/
def alltopEquiv {o : α} {V : Finset α} (ho : o∉V) {r k : ℕ} (hv : V.card=2*k+1) (hrk : r≤k)
    (even : Even r) (l : ℤ) : Designs V r k l ≃ Complementary (insert o V) (r+1) (k+1) l where
  toFun w := by
    let f := extend o V (readWeight w.val)
    let z : Designs (insert o V) (r+1) (k+1) l :=
      ⟨fun B => f B.val,restrict_design (extend_signed ho hv hrk even w.prop)⟩
    refine ⟨z,fun B hB => ?_⟩
    obtain ⟨sub,hc⟩ := mem_powersetCard.mp hB
    have hcomp : insert o V\B∈(insert o V).powersetCard (k+1) := mem_powersetCard.mpr
      ⟨sdiff_subset,by rw [card_sdiff_of_subset sub,card_insert_of_notMem ho,hv,hc]; omega⟩
    rw [read_mem _ hcomp,read_mem _ hB]
    exact extend_symmetric ho _ _ _ hB
  invFun z := ⟨fun B => readWeight z.val.val (insert o B.val),restrict_design (derive_signed ho z.val.prop)⟩
  left_inv w := by
    apply Subtype.ext
    funext B
    change readWeight (V:=insert o V) (k:=k+1) (fun C => extend o V (readWeight w.val) C.val) (insert o B.val)=_
    rw [read_mem _ (insert_block ho B.prop)]
    change extend o V (readWeight w.val) (insert o B.val)=_
    have no : o∉B.val := fun h => ho ((mem_powersetCard.mp B.prop).1 h)
    simp only [extend,mem_insert_self,if_true,erase_insert no,read_mem _ B.prop]
  right_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    funext B
    let w : Layer V k := fun A => readWeight z.val.val (insert o A.val)
    have he := unique_on_layer ho hv z.prop (w:=readWeight w) (fun A ha => (read_mem w ha).symm) B.val B.prop
    change extend o V (readWeight w) B.val=z.val.val B
    exact he.symm.trans (read_mem _ B.prop)

/-- Mendelsohn's unique extension at maximal strength. The complement
condition on the codomain follows from its design rows. -/
def mendelsohnEquiv {o : α} {V : Finset α} (ho : o∉V) {k : ℕ} (hv : V.card=2*k+1)
    (odd : Odd k) (l : ℤ) : Designs V (k-1) k l ≃ Designs (insert o V) k (k+1) l := by
  have hk : 0<k := odd.pos
  have he : Even (k-1) := by obtain ⟨x,hx⟩ := odd; exact ⟨x,by omega⟩
  have up := alltopEquiv ho hv (r:=k-1) (by omega) he l
  rw [show k-1+1=k by omega] at up
  apply up.trans
  refine Equiv.subtypeUnivEquiv fun z => ?_
  apply automatic_symmetry (k:=k+1) (by omega) (odd.add_odd odd_one)
  · rw [card_insert_of_notMem ho,hv]
    omega
  · simpa only [Nat.add_sub_cancel] using z.prop

#print axioms Layer
#print axioms readWeight
#print axioms read_mem
#print axioms Designs
#print axioms Complementary
#print axioms alltopEquiv
#print axioms mendelsohnEquiv
end Erdos722.ComplementExtension
