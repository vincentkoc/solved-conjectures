import Mathlib

/-! Stretching exponent configurations while preserving all equal pairs of sums. -/

namespace CunninghamChain.GapLift

private def shiftAt (a b N x : ℕ) := b*x/N-a*x/N

private lemma sum_floor_error {N x y z w : ℕ} (eq : x+y=z+w) (j : ℕ) :
    j*x/N+j*y/N ≤ j*z/N+j*w/N+1 ∧ j*z/N+j*w/N ≤ j*x/N+j*y/N+1 := by
  have jl : (j*x+j*y)/N=(j*z+j*w)/N := by rw [←Nat.mul_add,eq,Nat.mul_add]
  have lo₁ : j*x/N+j*y/N ≤ (j*x+j*y)/N := Nat.div_add_div_le_add_div
  have lo₂ : j*z/N+j*w/N ≤ (j*z+j*w)/N := Nat.div_add_div_le_add_div
  have hi₁ := Nat.add_div_le_div_add_div_add_one (j*x) (j*y) N
  have hi₂ := Nat.add_div_le_div_add_div_add_one (j*z) (j*w) N
  omega

private lemma shifts_add {a b N x y z w : ℕ} (ab : a ≤ b) (eq : x+y=z+w)
    (cx : a*x/N ≡ b*x/N [MOD 3]) (cy : a*y/N ≡ b*y/N [MOD 3])
    (cz : a*z/N ≡ b*z/N [MOD 3]) (cw : a*w/N ≡ b*w/N [MOD 3]) :
    shiftAt a b N x+shiftAt a b N y=shiftAt a b N z+shiftAt a b N w := by
  have ha := sum_floor_error (N:=N) eq a
  have hb := sum_floor_error (N:=N) eq b
  have mono (u : ℕ) : a*u/N ≤ b*u/N := Nat.div_le_div_right (Nat.mul_le_mul_right u ab)
  have hx := mono x
  have hy := mono y
  have hz := mono z
  have hw := mono w
  have congr := ((cx.add cy).add (cz.symm.add cw.symm))
  change _%3=_%3 at congr
  dsimp only [shiftAt]
  omega

private lemma near_end_floor {N u j : ℕ} (hu : 0<u) (hj : 0<j) (tiny : j*u < N) :
    j*(N-u)/N=j-1 := by
  have ju : 0<j*u := Nat.mul_pos hj hu
  have uN : u≤N := (Nat.le_mul_of_pos_left u hj).trans tiny.le
  have id : j*(N-u)=(N-j*u)+(j-1)*N := by
    have eq₁ := Nat.sub_add_cancel uN
    have eq₂ := Nat.sub_add_cancel tiny.le
    have eq₃ := Nat.sub_add_cancel (show 1≤j by omega)
    nlinarith only [congrArg (j*·) eq₁,eq₂,congrArg (·*N) eq₃]
  rw [id,Nat.add_mul_div_right _ _ (by omega),Nat.div_eq_of_lt (by omega),Nat.zero_add]

private lemma shift_le {a b N x : ℕ} (ab : a≤b) (pos : 0<N) (hx : x≤N) :
    shiftAt a b N x ≤ b-a := by
  have hb : b*x ≤ a*x+(b-a)*N := by
    calc b*x = a*x+(b-a)*x := by rw [←Nat.add_mul]; congr 1; omega
         _ ≤ _ := Nat.add_le_add_left (Nat.mul_le_mul_left _ hx) _
  have dv := Nat.div_le_div_right hb (c:=N)
  rw [Nat.add_mul_div_right _ _ pos] at dv
  dsimp [shiftAt]
  omega

/-- Positions recorded for the reflected product of a witness and the quadratic endpoint. -/
def marked {t : ℕ} (x : Fin t → ℕ) (N u : ℕ) : Prop :=
  (∃ i, u=x i) ∨ u=0 ∨ u=N ∨ u=N-1 ∨ u=N-2

/-- Past this bound, there is a positive displacement of the upper three endpoints
and a bounded displacement of each witness position preserving all additive relations
on the union of those slots and the four marked endpoints. -/
theorem stretch_with_endpoints {t N : ℕ} (x : Fin t → ℕ) (large : 6*(3^t+1)<N) :
    ∃ d : ℕ, 0<d ∧ ∃ v : ℕ → ℕ, v 0=0 ∧ v N=d ∧ v (N-1)=d ∧ v (N-2)=d ∧
      (∀ u≤N, v u≤d) ∧
      ∀ u₁ u₂ u₃ u₄, marked x N u₁ → marked x N u₂ → marked x N u₃ → marked x N u₄ →
        u₁+u₂=u₃+u₄ → v u₁+v u₂=v u₃+v u₄ := by
  classical
  let mult (j : Fin (3^t+1)) := 3*(j.val+1)
  let color (j : Fin (3^t+1)) (i : Fin t) : Fin 3 := ⟨(mult j*x i/N)%3,Nat.mod_lt _ (by decide)⟩
  obtain ⟨i,j,ne,e⟩ := Fintype.exists_ne_map_eq_of_card_lt color (by simp)
  wlog lt : i<j generalizing i j
  · exact this j i ne.symm e.symm (lt_of_le_of_ne (le_of_not_gt lt) ne.symm)
  let a := mult i
  let b := mult j
  have ij : i.val<j.val := lt
  have jl := j.isLt
  have ba : a<b := by dsimp [a,b,mult]; omega
  have ap : 0<a := by dsimp [a,mult]; omega
  have bp : 0<b := by omega
  have bound : b*2<N := by dsimp [b,mult]; omega
  have NP : 0<N := by omega
  have end₁ (k : ℕ) (hk : 0<k) (kle : k≤b) : k*(N-1)/N=k-1 :=
    near_end_floor (by decide) hk (by omega)
  have end₂ (k : ℕ) (hk : 0<k) (kle : k≤b) : k*(N-2)/N=k-1 :=
    near_end_floor (by decide) hk (by omega)
  have mark (u : ℕ) (hu : marked x N u) :
      a*u/N ≡ b*u/N [MOD 3] := by
    rcases hu with ⟨s,rfl⟩|rfl|rfl|rfl|rfl
    · exact congrArg Fin.val (congrFun e s)
    · simp [Nat.ModEq]
    · simp [a,b,mult,NP.ne',Nat.ModEq]
    · rw [end₁ a ap ba.le,end₁ b bp le_rfl]; dsimp [a,b,mult,Nat.ModEq]; omega
    · rw [end₂ a ap ba.le,end₂ b bp le_rfl]; dsimp [a,b,mult,Nat.ModEq]; omega
  refine ⟨b-a,by omega,shiftAt a b N,by simp [shiftAt],by simp [shiftAt,NP.ne'],?_,?_,
    fun _ h => shift_le ba.le NP h,?_⟩
  · simp only [shiftAt,end₁ a ap ba.le,end₁ b bp le_rfl]; omega
  · simp only [shiftAt,end₂ a ap ba.le,end₂ b bp le_rfl]; omega
  · intro x₁ x₂ x₃ x₄ h₁ h₂ h₃ h₄ eq
    exact shifts_add ba.le eq (mark _ h₁) (mark _ h₂) (mark _ h₃) (mark _ h₄)

#print axioms stretch_with_endpoints

end CunninghamChain.GapLift
