import CunninghamThreeColorStretch
import CunninghamSquareGapComparison
import CunninghamGapPatternFiniteness

/-! An explicit degree bound for the two-degree comparison of square balanced Jones chains. -/

namespace CunninghamChain.GapLift

private lemma pos_marked {t n : ℕ} (x : Fin t → ℕ) (i : Fin t ⊕ Fin 4) :
    marked x (n+2) (positions n x i) := by
  cases i with
  | inl j => exact Or.inl ⟨j,rfl⟩
  | inr j => fin_cases j <;> simp [positions,marked]

private lemma pos_le {t n : ℕ} (x : Fin t → ℕ) (hx : ∀ i, x i≤n+2) (i : Fin t ⊕ Fin 4) :
    positions n x i ≤ n+2 := by
  cases i with
  | inl j => exact hx j
  | inr j => fin_cases j <;> simp [positions]

/-- The support of an exceptional witness cannot be too small relative to the degree. -/
theorem square_exception_degree_bound {b : ℚ} (hb : 1<b) {t n : ℕ} (exc : exceptional b t n) :
    n+2 ≤ 6*(3^t+1) := by
  by_contra! large
  obtain ⟨x,a,hx,prod,bad⟩ := exc
  obtain ⟨d,dp,v,v0,vN,v₁,v₂,bd,add⟩ := stretch_with_endpoints x large
  let y (i : Fin t) := x i+v (x i)
  have move (i : Fin t ⊕ Fin 4) :
      positions (n+d) y i = positions n x i + v (positions n x i) := by
    cases i with
    | inl j => rfl
    | inr j =>
      have e₁ : v (n+1)=d := by simpa using v₁
      have e₂ : v n=d := by simpa using v₂
      fin_cases j <;> simp [positions,v0,vN,e₁,e₂] <;> omega
  have hy (i : Fin t) : y i ≤ n+d+2 := by
    have := bd _ (hx i)
    have := hx i
    dsimp [y]
    omega
  apply bad
  apply square_comparison hb (show n<n+d by omega) x y hx hy _ a prod
  intro i j k l eq
  have marks := pos_marked x (n:=n)
  have bounds := pos_le x hx
  have bounds' := pos_le y hy
  have ex : positions n x i+positions n x l=positions n x k+positions n x j := by
    have := bounds j
    have := bounds l
    omega
  have ev := add _ _ _ _ (marks i) (marks l) (marks k) (marks j) ex
  have jle := bounds' j
  have lle := bounds' l
  rw [move,move,move,move]
  rw [move] at jle lle
  omega

#print axioms square_exception_degree_bound

end CunninghamChain.GapLift
