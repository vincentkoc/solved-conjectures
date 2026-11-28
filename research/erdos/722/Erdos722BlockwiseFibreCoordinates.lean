import Erdos722TwistedFourFibreRule

/-! # Independent fibre coordinates on the blocks of a Steiner quadruple system -/

namespace Erdos722.FourPoint
open QuadCompletion Finset
open scoped Classical
noncomputable section
variable {I : Type*} [DecidableEq I] [Fintype I]

/-- Each incident fibre can take its own coordinates on each base quadruple. -/
abbrev BlockCoordinates (Q : Rule I) := Q.blocks → I → Equiv.Perm Fibre

def baseQuad (Q : Rule I) (i j k : I) : Finset I := insert (Q.complete i j k) {i,j,k}

omit [Fintype I] in
private theorem baseQuad_swap₁ (Q : Rule I) (i j k : I) :
    baseQuad Q i j k=baseQuad Q j i k := by
  unfold baseQuad
  rw [Q.swap₁ i j k,insert_comm i j]

omit [Fintype I] in
private theorem baseQuad_swap₂ (Q : Rule I) (i j k : I) :
    baseQuad Q i j k=baseQuad Q i k j := by
  simp only [baseQuad,Q.swap₂ i j k]
  ext x
  simp only [mem_insert,mem_singleton]
  tauto

omit [Fintype I] in
private theorem baseQuad_cancel (Q : Rule I) (i j k : I) :
    baseQuad Q i j (Q.complete i j k)=baseQuad Q i j k := by
  unfold baseQuad
  rw [Q.cancel]
  ext x
  simp only [mem_insert,mem_singleton]
  tauto

def blockChart (Q : Rule I) (D : BlockCoordinates Q) (S : Finset I) : I → Equiv.Perm Fibre :=
  if h : S∈Q.blocks then D ⟨S,h⟩ else fun _ => Equiv.refl Fibre

private theorem repeated_chart (Q : Rule I) (D : BlockCoordinates Q) (i j : I) :
    blockChart Q D (baseQuad Q i i j)=fun _ => Equiv.refl Fibre := by
  apply dif_neg
  intro h
  have size := ((Q.mem_blocks _).mp h).1
  unfold baseQuad at size
  rw [Q.repeated] at size
  by_cases eq : i=j
  · subst j; simp at size
  · simp [eq,insert_comm j i] at size

private def chartPoints (e : I → Equiv.Perm Fibre) : Equiv.Perm (I × Fibre) where
  toFun a := (a.1,e a.1 a.2)
  invFun a := (a.1,(e a.1).symm a.2)
  left_inv a := Prod.ext rfl ((e a.1).symm_apply_apply a.2)
  right_inv a := Prod.ext rfl ((e a.1).apply_symm_apply a.2)

private def inChart (R : Rule (I × Fibre)) (e : I → Equiv.Perm Fibre) : Rule (I × Fibre) where
  complete a b c := (chartPoints e).symm (R.complete (chartPoints e a) (chartPoints e b) (chartPoints e c))
  swap₁ _ _ _ := congrArg _ (R.swap₁ ..)
  swap₂ _ _ _ := congrArg _ (R.swap₂ ..)
  repeated a b := by rw [R.repeated,Equiv.symm_apply_apply]
  cancel a b c := by rw [Equiv.apply_symm_apply,R.cancel,Equiv.symm_apply_apply]

/-- Conjugate the completion in the coordinates of its projected quadruple.
After any three-point completion, the projected quadruple stays the same. -/
def blockwiseRule (Q : Rule I) (M : Matching I) (R : Rule (I × Fibre))
    (h : Compatible Q M R) (D : BlockCoordinates Q) : Rule (I × Fibre) where
  complete a b c := (inChart R (blockChart Q D (baseQuad Q a.1 b.1 c.1))).complete a b c
  swap₁ a b c := by rw [baseQuad_swap₁ Q a.1 b.1 c.1]; apply Rule.swap₁
  swap₂ a b c := by rw [baseQuad_swap₂ Q a.1 b.1 c.1]; apply Rule.swap₂
  repeated a b := Rule.repeated _ a b
  cancel a b c := by
    let e := blockChart Q D (baseQuad Q a.1 b.1 c.1)
    have proj : ((inChart R e).complete a b c).1=Q.complete a.1 b.1 c.1 :=
      h.project (chartPoints e a) (chartPoints e b) (chartPoints e c)
    change (inChart R (blockChart Q D (baseQuad Q a.1 b.1 ((inChart R e).complete a b c).1))).complete
      a b ((inChart R e).complete a b c)=c
    rw [proj,baseQuad_cancel]
    exact (inChart R e).cancel a b c

theorem blockwise_compatible (Q : Rule I) (M : Matching I) (R : Rule (I × Fibre))
    (h : Compatible Q M R) (D : BlockCoordinates Q) : Compatible Q M (blockwiseRule Q M R h D) where
  project a b c := by
    let e := blockChart Q D (baseQuad Q a.1 b.1 c.1)
    exact h.project (chartPoints e a) (chartPoints e b) (chartPoints e c)
  pair i j x y z := by
    change (inChart R (blockChart Q D (baseQuad Q i i j))).complete (i,x) (i,y) (j,z)=_
    rw [repeated_chart]
    exact (h.pair i j x y z)

/-- A transversal meets its prescribed offset after applying the four local coordinates. -/
theorem blockwise_transversal (Q : Rule I) (M : Matching I) (u : BlockOffsets Q)
    (D : BlockCoordinates Q) {i j k : I} (ij : i≠j) (ik : i≠k) (jk : j≠k) (x y z : Fibre) :
    let B : Q.blocks := ⟨_,completed_block Q ij ik jk⟩
    let R := blockwiseRule Q M (twistedRule Q M u) (twisted_compatible Q M u) D
    D B (Q.complete i j k) (R.complete (i,x) (j,y) (k,z)).2=D B i x+D B j y+D B k z+u B := by
  dsimp only
  change D _ _ ((blockChart Q D (baseQuad Q i j k) (Q.complete i j k)).symm
    (twistedFourth Q M u i j k (blockChart Q D (baseQuad Q i j k) i x)
      (blockChart Q D (baseQuad Q i j k) j y) (blockChart Q D (baseQuad Q i j k) k z)))=_
  have chart : blockChart Q D (baseQuad Q i j k)=D ⟨_,completed_block Q ij ik jk⟩ :=
    dif_pos (completed_block Q ij ik jk)
  rw [chart,Equiv.apply_symm_apply]
  simp only [twistedFourth,fourth,if_neg ij,if_neg ik,if_neg jk,offset_on_block Q u ij ik jk]

#print axioms BlockCoordinates
#print axioms baseQuad
#print axioms blockChart
#print axioms blockwiseRule
#print axioms blockwise_compatible
#print axioms blockwise_transversal
end
end Erdos722.FourPoint
