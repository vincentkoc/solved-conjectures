import CunninghamOppositeRootReduction

/-! All noncyclotomic roots shared by opposite-sign Jones chains from one linear seed. -/

namespace CunninghamChain.SharedFactors
open Polynomial LinearRoots

/-- The sign belongs to the earlier iterate. The last equality in each row gives its shared factor. -/
def CollisionRow (k : Bool) (a b : ℤ) (m n : ℕ) (z : ℂ) : Prop :=
  (m=1 ∧ n=2 ∧ a-2*b = -4*sign k ∧ 2*z+1=0) ∨
  (m=1 ∧ n=3 ∧ k=true ∧ a=2 ∧ b=1 ∧ 2*z^2+z+1=0) ∨
  (m=2 ∧ n=3 ∧ k=false ∧ a=2 ∧ b=0 ∧ 2*z^2+2*z+1=0) ∨
  (m=2 ∧ n=4 ∧ k=true ∧ a=2 ∧ b=2 ∧ 2*z^2+1=0)

private lemma row_of_roots {a b : ℤ} (ha : 0 < a) {k : Bool} {m n : ℕ}
    (hm : 0 < m) (hn : m<n) {z : ℂ} (hu : OffUnity z)
    (hmz : aeval z (term k a b m) = 0) (hnz : aeval z (term (!k) a b n) = 0) :
    CollisionRow k a b m n z := by
  obtain ⟨s,rfl⟩ := Nat.exists_eq_add_of_le hn.le
  obtain ⟨g,i,j,rfl,rfl,⟨u,v,hP⟩,hz,rows⟩ := reduced_collision ha.ne' hm (by omega) hu hmz hnz
  have E (t : ℤ) := congrArg (fun P : ℤ[X] => P.eval t) hP
  have h0 := E 0
  have h1 := E 1
  have hm1 := E (-1)
  have h2 := E 2
  rcases rows with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ <;>
    cases k <;>
    norm_num [CollisionRow,sign,polynomialTerm,cofactor,geom,Finset.sum_range_succ,Polynomial.map_add]
      at h0 h1 hm1 h2 hz ⊢ <;>
    first | exact ⟨by omega,by linear_combination hz⟩
          | exact ⟨by omega,by omega,by linear_combination hz⟩
          | omega

lemma CollisionRow.roots {a b : ℤ} {k : Bool} {m n : ℕ} {z : ℂ}
    (row : CollisionRow k a b m n z) :
    aeval z (term k a b m)=0 ∧ aeval z (term (!k) a b n)=0 := by
  have h2 : aeval z (2 : ℚ[X]) = 2 := map_ofNat _ _
  rcases row with ⟨rfl,rfl,hab,hz⟩ | ⟨rfl,rfl,rfl,rfl,rfl,hz⟩ |
    ⟨rfl,rfl,rfl,rfl,rfl,hz⟩ | ⟨rfl,rfl,rfl,rfl,rfl,hz⟩
  · have h : z = -(1/2:ℂ) := by linear_combination hz / 2
    subst z
    cases k <;> norm_num [sign] at hab <;>
      have he := congrArg (Int.castRingHom ℂ) hab <;>
      norm_num [term,polynomialTerm] at he ⊢ <;> constructor <;> first | linear_combination he / 4 | linear_combination -he / 8
  · norm_num [term,polynomialTerm,h2]
    constructor
    · linear_combination hz
    · linear_combination (z^2-1)*hz
  · norm_num [term,polynomialTerm,h2]
    constructor
    · linear_combination (z-1)*hz
    · linear_combination (z^2-z+1)*hz
  · norm_num [term,polynomialTerm,h2]
    constructor
    · linear_combination (z+1)*hz
    · linear_combination (z^3+z^2-z-1)*hz

/-- For every integral linear seed of positive slope and every off-unity root, the four
rows are necessary and sufficient across all positive indices of the two chains. -/
theorem common_root_iff_row {a b : ℤ} (ha : 0 < a) {k : Bool} {m n : ℕ}
    (hm : 0 < m) (hn : m<n) {z : ℂ} (hu : OffUnity z) :
    (aeval z (term k a b m)=0 ∧ aeval z (term (!k) a b n)=0) ↔
    CollisionRow k a b m n z :=
  ⟨fun ⟨h₁,h₂⟩ => row_of_roots ha hm hn hu h₁ h₂,CollisionRow.roots⟩

#print axioms CollisionRow.roots
#print axioms common_root_iff_row

end CunninghamChain.SharedFactors
