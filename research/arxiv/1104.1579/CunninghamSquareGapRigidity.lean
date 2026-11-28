import CunninghamGapSupportPresentation

/-! Eventual reflected-product rigidity at every positive square balanced coefficient. -/

namespace CunninghamChain.GapLift
open Polynomial Finset CoefficientEnergy LinearRoots LargeGap

private lemma signed_of_dvd {F G : ℤ[X]} {N : ℕ} (df : F.natDegree=N) (dg : G.natDegree ≤ N)
    (f₀ : F.coeff 0=1) (prod : G*reflect N G=F*reflect N F)
    (dvd : F.map (Int.castRingHom ℚ) ∣ G.map (Int.castRingHom ℚ)) :
    ∃ z : ℤ, z^2=1 ∧ G=C z*F := by
  have fn : F≠0 := by intro e; simp [e] at f₀
  have fp := mul_ne_zero fn (mt (reflect_eq_zero_iff.mp) fn : reflect N F≠0)
  have gn : G≠0 := by intro e; rw [e,zero_mul] at prod; exact fp prod.symm
  let f := Int.castRingHom ℚ
  have inj : Function.Injective f := Int.cast_injective
  have fm : F.map f≠0 := by simpa using (Polynomial.map_injective f inj).ne fn
  have gm : G.map f≠0 := by simpa using (Polynomial.map_injective f inj).ne gn
  obtain ⟨H,eq⟩ := dvd
  have hn : H≠0 := by rintro rfl; rw [mul_zero] at eq; exact gm eq
  have gd := congrArg Polynomial.natDegree eq
  rw [natDegree_mul fm hn,natDegree_map_eq_of_injective inj,natDegree_map_eq_of_injective inj,df] at gd
  have hc := eq_C_of_natDegree_eq_zero (by omega : H.natDegree=0)
  rw [hc] at eq
  have co := congrArg (fun P : ℚ[X] => P.coeff 0) eq
  simp only [coeff_map,mul_coeff_zero,coeff_C_zero,f₀,map_one,one_mul,Int.coe_castRingHom] at co
  let z := G.coeff 0
  have he : G=C z*F := by
    apply Polynomial.map_injective f inj
    rw [Polynomial.map_mul,map_C,mul_comm]
    simpa only [f,z,Int.coe_castRingHom,co] using eq
  have mult : C (z^2)*(F*reflect N F)=C (1:ℤ)*(F*reflect N F) := by
    rw [he,reflect_C_mul] at prod
    simpa only [map_pow,pow_two,map_mul,C_1,one_mul,mul_assoc,mul_left_comm,mul_comm] using prod
  exact ⟨z,C_injective (mul_right_cancel₀ fp mult),he⟩

private lemma too_far_for_exception {b : ℕ} (hb : 2 ≤ b) (n : ℕ) (hn : 0 < n)
    (G : ℤ[X]) (dg : G.natDegree ≤ n+2)
    (prod : G*reflect (n+2) G=separated (gapEndpoint (b^2) false) (n+2)*
      reflect (n+2) (separated (gapEndpoint (b^2) false) (n+2)))
    (bad : ¬ ∃ z : ℤ, z^2=1 ∧ (G=C z*separated (gapEndpoint (b^2) false) (n+2) ∨
      reflect (n+2) G=C z*separated (gapEndpoint (b^2) false) (n+2))) :
    exceptional b G.support.card n := by
  let c := gapEndpoint (b^2) false
  let F := separated c (n+2)
  have cdeg : c.natDegree=2 := by
    simp only [c,gapEndpoint,sign,Bool.false_eq_true,if_false,neg_neg,map_one,one_mul]
    exact (quadratic_ends (by nlinarith : 2 ≤ b^2) false).2.2
  have c₀ : c.coeff 0=(b^2:ℕ) := by
    simpa only [c,gapEndpoint,sign,Bool.false_eq_true,if_false,neg_neg,map_one,one_mul] using
      (quadratic_ends (by nlinarith : 2 ≤ b^2) false).1
  have low : F.coeff 0=1 := by simp [F,separated,coeff_eq_zero_of_natDegree_lt (p:=c) (show c.natDegree < n+2 by omega)]
  have high : F.coeff (n+2)=(b^2:ℕ) := by simp [F,separated,c₀,coeff_one]
  have df : F.natDegree=n+2 := (separated_degree c (by omega)).antisymm
    (le_natDegree_of_ne_zero (by rw [high]; positivity))
  have rf := integral_endpoint (b^2) n
  change F.map (Int.castRingHom ℚ)=_ at rf
  push_cast at rf
  obtain ⟨x,a,hx,eq⟩ := assemble_support G (n+2) dg
  have hp (i : Fin G.support.card ⊕ Fin 4) : positions n x i ≤ n+2 := by
    cases i with
    | inl i => exact hx i
    | inr j => fin_cases j <;> simp [positions]
  have e₁ := (present_witness n x a).trans eq
  have e₂ := (present_endpoint n x (b^2:ℚ)).trans rf.symm
  have r₁ := congrArg (reflect (n+2)) e₁
  have r₂ := congrArg (reflect (n+2)) e₂
  rw [reflect_assemble _ _ _ hp,reflect_map] at r₁ r₂
  refine ⟨x,a,hx,?_,?_⟩
  · rw [e₁,e₂,r₁,r₂,←Polynomial.map_mul,←Polynomial.map_mul]
    exact congrArg (Polynomial.map (Int.castRingHom ℚ)) prod
  · rw [e₁,r₁,←rf]
    rintro (h|h)
    · obtain ⟨z,hz,he⟩ := signed_of_dvd df dg low prod h
      exact bad ⟨z,hz,Or.inl he⟩
    · have dg' := natDegree_reflect_le (p:=G) (N:=n+2) |>.trans (max_le le_rfl dg)
      obtain ⟨z,hz,he⟩ := signed_of_dvd df dg' low
        (by simpa [mul_comm (reflect (n+2) G) G] using prod) h
      exact bad ⟨z,hz,Or.inr he⟩

/-- A square coefficient gives only finitely many second-kind degrees with
an integral reflected-product witness differing from both signed orientations. -/
theorem eventual_square_rigidity {b : ℕ} (hb : 2 ≤ b) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ G : ℤ[X], G.natDegree ≤ n+2 →
      G*reflect (n+2) G=separated (gapEndpoint (b^2) false) (n+2)*
        reflect (n+2) (separated (gapEndpoint (b^2) false) (n+2)) →
      ∃ z : ℤ, z^2=1 ∧ (G=C z*separated (gapEndpoint (b^2) false) (n+2) ∨
        reflect (n+2) G=C z*separated (gapEndpoint (b^2) false) (n+2)) := by
  let c := gapEndpoint (b^2) false
  let W := (1 + energy c (c.natDegree+1)).toNat
  have rat : 1 < (b:ℚ) := by exact_mod_cast (by omega : 1 < b)
  have bound := (bounded_exceptional_finite rat W).eventually_cofinite_notMem
  rw [Nat.cofinite_eq_atTop] at bound
  filter_upwards [bound,Filter.eventually_gt_atTop c.natDegree] with n hn large
  intro G dg prod
  by_contra bad
  have exc := too_far_for_exception hb n (by omega) G dg prod bad
  have energyEq := congrArg (fun P : ℤ[X] => P.coeff (n+2)) prod
  simp only [coeff_mul_self_reflect] at energyEq
  change energy G (n+2+1)=energy (separated c (n+2)) (n+2+1) at energyEq
  rw [separated_energy c (by omega)] at energyEq
  have card := support_card_le_energy G dg
  rw [energyEq] at card
  exact hn ⟨G.support.card,by dsimp [W]; omega,exc⟩

#print axioms eventual_square_rigidity

#print axioms signed_of_dvd
#print axioms too_far_for_exception

end CunninghamChain.GapLift
