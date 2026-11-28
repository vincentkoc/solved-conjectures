import Green51SeventhOrbit

/-! # A 73-bit trace certificate in the field of order 512

For a root of `X⁹ + X + 1`, the trace sequence has period 73. The recurrence
determines the sequence from its first nine entries. Testing the five displayed
field elements covers all 73 seventh-power scales.
-/
namespace Green51NinePencils
local notation "F" => ZMod 2
variable {K : Type*} [Field K] [CharP K 2] [Algebra F K] [Fintype K]

private def bit (n : ℕ) : F := if Nat.testBit 0x1feaa66221e0a060201 (n%73) then 1 else 0
private theorem bit_step : ∀ j : Fin 73, bit (j.val+9)=bit (j.val+1)+bit j.val := by decide +kernel
private theorem bit_hits : ∀ j : Fin 73,
  bit j.val ≠ 0 ∨ bit (j.val+6)+bit (j.val+7) ≠ 0 ∨
  bit (j.val+2)+bit (j.val+3)+bit (j.val+4)+bit (j.val+6) ≠ 0 ∨
  bit (j.val+1)+bit (j.val+4)+bit (j.val+5)+bit (j.val+6)+bit (j.val+8) ≠ 0 ∨
  bit (j.val+1)+bit (j.val+3)+bit (j.val+8) ≠ 0 := by decide +kernel

omit [CharP K 2] [Fintype K] in
private theorem word (Q : K →ₗ[F] F) (one : Q 1=1) (sq : ∀ z,Q (z^2)=Q z) (g : K) (rel : g^9=g+1) :
    ∀ n : ℕ, Q (g^n) = bit n := by
  let w (n : ℕ) := Q (g^n)
  have step (n : ℕ) : w (n+9) = w (n+1)+w n := by
    simp only [w,pow_add,rel,mul_add,pow_one,mul_one,map_add]
  have dbl (n : ℕ) : w (n*2)=w n := by simp only [w,pow_mul,sq]
  have e1 := dbl 1; have e2 := dbl 2; have e3 := dbl 3; have e4 := dbl 4
  have e5 := dbl 5; have e6 := dbl 6; have e7 := dbl 7; have e8 := dbl 8
  norm_num only [Nat.reduceMul] at e1 e2 e3 e4 e5 e6 e7 e8
  change w (1+9) = _ at e5
  change w (3+9) = _ at e6
  change w (5+9) = _ at e7
  change w (7+9) = _ at e8
  rw [step] at e5 e6 e7 e8
  norm_num only [Nat.reduceAdd] at e5 e6 e7 e8
  have z4 : w 4=0 := by simpa [e3] using e6
  have z7 : w 7=0 := by simpa [add_comm] using e8
  have z2 : w 2=0 := e2.symm.trans z4
  have z1 : w 1=0 := e1.symm.trans z2
  have z5 : w 5=0 := by simpa [z1,z2] using e5.symm
  have z6 : w 6=0 := by simpa [z5,z7] using e7
  have z3 : w 3=0 := e3.symm.trans z6
  have z8 : w 8=0 := e4.trans z4
  have z0 : w 0=1 := by simpa [w] using one
  have init : ∀ i : Fin 9, w i.val=bit i.val := by
    intro i; fin_cases i <;> first | exact z0 | exact z1 | exact z2 | exact z3 | exact z4 | exact z5 | exact z6 | exact z7 | exact z8
  intro n
  change w n=bit n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases small : n<9
    · exact init ⟨n,small⟩
    · let k:=n-9
      have eq : n=k+9 := by dsimp [k];omega
      have first := ih (k+1) (by omega)
      have last := ih k (by omega)
      rw [eq,step,first,last]
      have periodic := bit_step ⟨k%73,Nat.mod_lt _ (by decide)⟩
      simpa [bit,Nat.add_mod,Nat.mod_mod] using periodic.symm

def v1 (g:K) : K := (g^6+g^7)
def v2 (g:K) : K := (g^2+g^3+g^4+g^6)
def v3 (g:K) : K := (g+g^4+g^5+g^6+g^8)
def v4 (g:K) : K := (g+g^3+g^8)
def beta (g:K) : K := (g^3+g^4+g^5+g^7)
omit [CharP K 2] [Fintype K] in
/-- Every seventh-power translate of the five specified vectors has nonzero trace somewhere. -/
theorem blocks_trace (Q : K →ₗ[F] F) (one : Q 1=1) (sq : ∀ z,Q (z^2)=Q z)
    (g : K) (rel : g^9=g+1) (i : Fin 73) (U : Submodule F K)
    (has : (1:K)∈U ∧ v1 g∈U ∧ v2 g∈U ∧ v3 g∈U ∧ v4 g∈U) :
    ¬∀ x∈U,Q (g^i.val*x)=0 := by
  intro all
  obtain ⟨h0,h1,h2,h3,h4⟩ := has
  have e0:=all _ h0;have e1:=all _ h1;have e2:=all _ h2;have e3:=all _ h3;have e4:=all _ h4
  simp only [v1,v2,v3,v4,mul_add,map_add,mul_one,←pow_add,←pow_succ,word Q one sq g rel] at e0 e1 e2 e3 e4
  rcases bit_hits i with h|h|h|h|h
  all_goals contradiction

omit [CharP K 2] [Fintype K] in
/-- Two entries of the same trace word distinguish the second coefficient from both zero and one. -/
theorem beta_traces (Q : K →ₗ[F] F) (one : Q 1=1) (sq : ∀ z, Q (z^2)=Q z)
    (g : K) (rel : g^9=g+1) : Q (beta g)=0 ∧ Q (g^2*beta g)=1 := by
  constructor <;> simp only [beta,mul_add,map_add,←pow_add,word Q one sq g rel] <;> decide

end Green51NinePencils
#print axioms Green51NinePencils.blocks_trace
#print axioms Green51NinePencils.beta_traces
