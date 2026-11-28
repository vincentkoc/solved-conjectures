import Green51BCHDirections
/-! # Binary Moore determinants of triples through a fixed vector -/
open Green50Downsets Green51BCH
open scoped Pointwise
namespace Green51BCHCompression
local notation "F" => ZMod 2
variable {K : Type*} [Field K] [CharP K 2]

/-- The binary Moore determinant in three input vectors. -/
def moore (t b c : K) : K :=
  t^4*(b^2*c+b*c^2) + t^2*(b^4*c+b*c^4) + t*(b^4*c^2+b^2*c^4)

theorem moore_prod (t b c : K) : moore t b c=t*b*c*(t+b)*(t+c)*(b+c)*(t+b+c) := by
  unfold moore
  ring_nf
  reduce_mod_char!

theorem moore_right (t b c d : K) : moore t b (c+d)=moore t b c+moore t b d := by
  unfold moore
  ring_nf
  reduce_mod_char!

omit [CharP K 2] in
theorem moore_swap (t b c : K) : moore t b c=moore t c b := by unfold moore; ring
theorem moore_alternating (t b : K) : moore t b b=0 := by rw [moore_prod,CharTwo.add_self_eq_zero b];ring
theorem moore_left (t b c d : K) : moore t (b+c) d=moore t b d+moore t c d := by
  rw [moore_swap,moore_right,moore_swap t d b,moore_swap t d c]

variable [Algebra F K]

omit [CharP K 2] in
private theorem independent_sum {J : Cube 4 →ₗ[F] K} (inj : Function.Injective J) {s : Cube 4} (hs : s≠0) : J s≠0 :=
  fun eq => hs (inj (eq.trans J.map_zero.symm))

private abbrev e (i : Fin 4) : Cube 4 := Pi.single i 1

private theorem separated (J : Cube 4 →ₗ[F] K) (inj : Function.Injective J) (b c : Cube 4)
    (ok : e 0≠0 ∧ b≠0 ∧ c≠0 ∧ e 0+b≠0 ∧ e 0+c≠0 ∧ b+c≠0 ∧ e 0+b+c≠0) :
    moore (J (e 0)) (J b) (J c) ≠ 0 := by
  rcases ok with ⟨h0,hb,hc,h1,h2,h3,h4⟩
  rw [moore_prod]
  simp only [←map_add]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
    (independent_sum inj h0) (independent_sum inj hb)) (independent_sum inj hc))
    (independent_sum inj h1)) (independent_sum inj h2)) (independent_sum inj h3)) (independent_sum inj h4)

set_option maxHeartbeats 900000 in
/-- On a four-dimensional input through a fixed nonzero direction, the other two
arguments of the Moore determinant span at least three output dimensions. -/
theorem moore_rank {H : Type*} [AddCommGroup H] [Module F H] [Finite K]
    (L : K →ₗ[F] H) (J : Cube 4 →ₗ[F] K) (inj : Function.Injective J)
    (zero : ∀ b c, L (moore (J (Pi.single 0 1)) (J b) (J c))=0) :
    3 ≤ Module.finrank F L.ker := by
  let t := J (e 0)
  let b := J (e 1)
  let c := J (e 2)
  let d := J (e 3)
  let A : L.ker := ⟨moore t b c,zero _ _⟩
  let B : L.ker := ⟨moore t b d,zero _ _⟩
  let C : L.ker := ⟨moore t c d,zero _ _⟩
  have nzA : A.val≠0 := separated J inj _ _ (by decide +kernel)
  have nzB : B.val≠0 := separated J inj _ _ (by decide +kernel)
  have nzC : C.val≠0 := separated J inj _ _ (by decide +kernel)
  have nzAB : A.val+B.val≠0 := by
    change moore t b c+moore t b d≠0
    rw [←moore_right]
    change moore t b (J (e 2)+J (e 3))≠0
    rw [←map_add]
    exact separated J inj _ _ (by decide +kernel)
  have nzAC : A.val+C.val≠0 := by
    change moore t b c+moore t c d≠0
    rw [moore_swap t c d,←moore_left]
    change moore t (J (e 1)+J (e 3)) c≠0
    rw [←map_add]
    exact separated J inj _ _ (by decide +kernel)
  have nzBC : B.val+C.val≠0 := by
    change moore t b d+moore t c d≠0
    rw [←moore_left]
    change moore t (J (e 1)+J (e 2)) d≠0
    rw [←map_add]
    exact separated J inj _ _ (by decide +kernel)
  have nzABC : A.val+B.val+C.val≠0 := by
    have yes := separated J inj (e 1+e 2) (e 1+e 3) (by decide +kernel)
    rw [map_add,map_add] at yes
    change moore t (b+c) (b+d)≠0 at yes
    rw [moore_left,moore_right,moore_right,moore_alternating,zero_add,moore_swap t c b] at yes
    change moore t b c + moore t b d + moore t c d ≠ 0
    rw [add_comm (moore t b c) (moore t b d),add_assoc]
    exact yes
  let f : Cube 3 →ₗ[F] L.ker := Fintype.linearCombination F ![A,B,C]
  have val (w : Cube 3) : (f w).val=w 0 • A.val+w 1 • B.val+w 2 • C.val := by
    simp [f,Fintype.linearCombination_apply,Fin.sum_univ_three,add_assoc]
  have inj' : Function.Injective f := by
    apply (injective_iff_map_eq_zero f).mpr
    intro w eq
    have eq' : w 0 • A.val+w 1 • B.val+w 2 • C.val=0 :=
      (val w).symm.trans (congrArg Subtype.val eq)
    have bit (x : F) : x=0 ∨ x=1 := (show ∀ y:F, y=0 ∨ y=1 from by decide) x
    rcases bit (w 0) with h0|h0 <;> rcases bit (w 1) with h1|h1 <;> rcases bit (w 2) with h2|h2 <;>
      simp [h0,h1,h2,nzA,nzB,nzC,nzAB,nzAC,nzBC,nzABC] at eq'
    funext i; fin_cases i <;> assumption
  have rank := f.finrank_le_finrank_of_injective inj'
  simpa [Cube] using rank


end Green51BCHCompression
#print axioms Green51BCHCompression.moore_prod
#print axioms Green51BCHCompression.moore_right
#print axioms Green51BCHCompression.moore_swap
#print axioms Green51BCHCompression.moore_alternating
#print axioms Green51BCHCompression.moore_left
#print axioms Green51BCHCompression.moore_rank
