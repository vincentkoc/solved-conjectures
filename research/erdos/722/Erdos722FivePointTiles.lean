import Erdos722PointedTiles
import Mathlib.Data.Nat.Bitwise

/-!
# Five-point fillings of pointed rectangles

Each bit identifies one local block. Intersecting three incidence rows
gives its unique index on an eligible triple, and zero on every other
triple. The three nontrivial tables come from the inversive plane over
the field of four elements, quadratic interpolation and the alternating
group on five letters.
-/

namespace Erdos722.PointedProduct.Five
open Finset

abbrev Points (s t : Shape) := Grid (Fin (s.width 4)) (Fin (t.width 4))

private instance {s t : Shape} (T : Finset (Points s t)) : Decidable (localEvent s t T) :=
  inferInstanceAs (Decidable ((s.accepts (leftTrace T).card) ∧ (t.accepts (rightTrace T).card)))

private def block {s t : Shape} (rows : Points s t → ℕ) {m : ℕ} (i : Fin m) :
    Finset (Points s t) := univ.filter fun x => (rows x).testBit i

private def mask {X : Type*} (rows : X → ℕ) (x y z : X) :=
  rows x &&& rows y &&& rows z

private theorem in_block {s t : Shape} (rows : Points s t → ℕ) {m : ℕ} (i : Fin m) (x y z) :
    {x,y,z}⊆block rows i ↔ (mask rows x y z).testBit i=true := by
  simp [block,mask,Nat.testBit_and,and_assoc,insert_subset_iff,singleton_subset_iff]

private def valid {s t : Shape} (rows : Points s t → ℕ) (m : ℕ) (x y z : Points s t) : Prop :=
  let v := mask rows x y z
  if localEvent s t {x,y,z} then v=2^v.log2 ∧ v.log2<m else v=0

private instance {s t : Shape} (rows : Points s t → ℕ) (m : ℕ) (x y z) :
    Decidable (valid rows m x y z) := by unfold valid; split <;> infer_instance

private def from_rows {s t : Shape} (rows : Points s t → ℕ) (m : ℕ)
    (hsize : ∀ i : Fin m, (block rows i).card=5)
    (cover : ∀ x y z, x≠y → x≠z → y≠z → valid rows m x y z) : Tile 4 s t where
  blocks := univ.image (block rows (m:=m))
  size := by
    intro B hB
    obtain ⟨i,_,rfl⟩ := mem_image.mp hB
    exact hsize i
  inside := by
    intro B hB T hTB ht
    obtain ⟨i,_,rfl⟩ := mem_image.mp hB
    obtain ⟨x,y,z,hxy,hxz,hyz,rfl⟩ := card_eq_three.mp ht
    have hc := cover x y z hxy hxz hyz
    by_contra h
    simp only [valid,if_neg h] at hc
    have hi := (in_block rows i x y z).mp hTB
    simp [hc] at hi
  cover := by
    intro T ht he
    obtain ⟨x,y,z,hxy,hxz,hyz,rfl⟩ := card_eq_three.mp ht
    have hc := cover x y z hxy hxz hyz
    simp only [valid,if_pos he] at hc
    let i : Fin m := ⟨(mask rows x y z).log2,hc.2⟩
    refine ⟨block rows i,⟨mem_image_of_mem _ (mem_univ _),(in_block rows i x y z).mpr ?_⟩,?_⟩
    · conv_lhs => rw [hc.1]
      simp [i]
    · rintro B ⟨hB,hTB⟩
      obtain ⟨j,_,rfl⟩ := mem_image.mp hB
      have hj := (in_block rows j x y z).mp hTB
      rw [hc.1,Nat.testBit_two_pow] at hj
      have hij : i=j := Fin.ext (of_decide_eq_true hj)
      rw [hij]

private def pos {a b : ℕ} : Grid (Fin a) (Fin b) → ℕ
  | none => 0
  | some (x,y) => 1+x.val*b+y.val

/- The infinity row comes first. Finite rows are in lexicographic order.
Line × line uses the 60 circles of the inversive plane of order four left
after removing the four rows and four columns through infinity. Circle ×
line uses the 60 nonconstant words obtained from degree-two
interpolation on the projective line over F₄, divided by a fixed irreducible
quadratic. Circle × circle uses the graphs of the 60 even permutations. -/
private def lineLine : Array ℕ := #[
  0xfff, 0x7fff007, 0x3ff800f038, 0x1fc0780f01c0,
  0xe3c780f00e00, 0x1f244889111248, 0xe3489092212481, 0x70c485122421812,
  0xb60248941822124, 0x531904a12844510, 0xa86908c22188844, 0x652452414881221,
  0x98946222414208a, 0xc2a31120c2288a0, 0xc458a2109284302, 0x1d432144441440c,
  0x2b88920c1448051]

private def circleLine : Array ℕ := #[
  0x0, 0x7fff, 0x3fff8000, 0x1fffc0000000,
  0xfffe00000000000, 0x1e003c0078007, 0x1e003c00380078, 0x1e001c003c00780,
  0xe001e003c007800, 0x222224444488888, 0x444448888811111, 0x888881111122222,
  0x111112222244444, 0x3049050890c2140, 0x48308a0460240a1, 0x850240620510c12,
  0x28430910a0920c, 0x902429208624210, 0x2490904a10090c2, 0x430900852090924,
  0x84246104942409]

private def circleCircle : Array ℕ := #[
  0x0, 0xfff, 0xfff000, 0xfff000000,
  0xfff000000000, 0xfff000000000000, 0x7007007007000, 0x38038038000007,
  0x1c01c0000038038, 0xe000001c01c01c0, 0xe00e00e00e00, 0x248248248248000,
  0x481481481000248, 0x812812000481481, 0x124000812812812, 0x124124124124,
  0x5108a05108a0000, 0x844302844000510, 0x22140c000302844, 0x8a00022140c221,
  0x5108a05108a, 0x8a05108a0510000, 0x3028443020008a0, 0x40c221000844302,
  0x5100040c22140c, 0x8a05108a051]

private def rows : (s t : Shape) → Points s t → ℕ
  | .point,.point,_ => 0
  | .point,.line,_ | .line,.point,_ => 1
  | .point,.circle,x | .circle,.point,x => if x.isSome then 1 else 0
  | .line,.line,x => lineLine[pos x]!
  | .circle,.line,x => circleLine[pos x]!
  | .line,.circle,x => circleLine[pos (x.map Prod.swap)]!
  | .circle,.circle,x => circleCircle[pos x]!

private def count : Shape → Shape → ℕ
  | .point,.point => 0
  | .point,_ | _,.point => 1
  | _,_ => 60

set_option maxRecDepth 32000 in
private theorem five_sizes (s t : Shape) : ∀ r : Fin (count s t), (block (rows s t) r).card=5 := by
  cases s <;> cases t <;> decide +kernel

set_option synthInstance.maxSize 1024 in
set_option maxRecDepth 32000 in
set_option maxHeartbeats 10000000 in
private theorem five_cover (s t : Shape) :
    ∀ x y z, x≠y → x≠z → y≠z → valid (rows s t) (count s t) x y z := by
  cases s <;> cases t <;> decide +kernel

/-- All nine pairs of face shapes have a five-point triple filling. -/
def tiles (s t : Shape) : Tile 4 s t :=
  from_rows (rows s t) (count s t) (five_sizes s t) (five_cover s t)

#print axioms tiles
end Erdos722.PointedProduct.Five
