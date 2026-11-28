import CunninghamBalancedEnergy

/-! A nineteen-coefficient multiplier for the plus chain. Its energy has only
twenty-one possible quadratic expressions in the seed coefficient. -/

namespace CunninghamChain.LinearRoots.PlusMultiplier
open Polynomial Finset CoefficientEnergy

private def entries : List ℤ :=
  [2,8,21,42,72,112,160,217,279,343,405,460,503,527,527,498,433,330,186]

private def entry (j : ℕ) := entries[j]?.getD 0
private noncomputable def K := ofCoeffList entries

private lemma coeff_K (j : ℕ) : K.coeff j = entry j := coeff_ofCoeffList ..

private lemma entry_zero {j : ℕ} (hj : 19 ≤ j) : entry j=0 := by
  have b : entries.length ≤ j := hj
  simp [entry,List.getElem?_eq_none b]

private lemma shape : K.natDegree=18 ∧ K.leadingCoeff=186 := by
  have top : K.coeff 18=186 := by rw [coeff_K]; decide
  have bound : K.natDegree≤18 := natDegree_le_iff_coeff_eq_zero.mpr
    (fun j hj => (coeff_K j).trans (entry_zero hj))
  have d := le_antisymm bound (le_natDegree_of_ne_zero (p:=K) (by rw [top]; decide))
  exact ⟨d,show K.coeff K.natDegree=186 from d.symm ▸ top⟩

private def diff (i : ℕ) : ℤ :=
  (if 2 ≤ i then entry (i-2) else 0)-2*(if 1 ≤ i then entry (i-1) else 0)+entry i

private lemma coeff_diff (i : ℕ) : ((X-1)^2*K).coeff i=diff i := by
  have h : (X-1)^2*K = X^2*K-C (2:ℤ)*(X^1*K)+K := by
    rw [show C (2:ℤ)=(2:ℤ[X]) by norm_num]; ring
  rw [h,coeff_add,coeff_sub,coeff_C_mul,coeff_X_pow_mul',coeff_X_pow_mul',diff]
  simp only [coeff_K]

/-- Expand the square before splitting at the shift. Only the overlap sum depends on n. -/
private lemma energy_shift_sub (P Q : ℤ[X]) {D : ℕ} (hq : Q.natDegree<D) (n : ℕ) :
    energy (X^n*P-Q) (n+D)=energy Q D+
      ∑ j ∈ range D, ((P.coeff j)^2-2*P.coeff j*Q.coeff (n+j)) := by
  have cross : ∑ j ∈ range (n+D), (X^n*P).coeff j*Q.coeff j =
      ∑ j ∈ range D, P.coeff j*Q.coeff (n+j) := by
    rw [sum_range_add]
    have low : ∑ j ∈ range n, (X^n*P).coeff j*Q.coeff j=0 := by
      apply sum_eq_zero
      intro j hj
      simp [coeff_X_pow_mul',not_le.mpr (mem_range.mp hj)]
    rw [low,zero_add]
    apply sum_congr rfl
    intro j _
    rw [Nat.add_comm n j,coeff_X_pow_mul]
  have expand : energy (X^n*P-Q) (n+D)=energy (X^n*P) (n+D)+energy Q (n+D)-
      2*(∑ j ∈ range (n+D), (X^n*P).coeff j*Q.coeff j) := by
    simp only [energy,coeff_sub,←sum_add_distrib,mul_sum,←sum_sub_distrib]
    apply sum_congr rfl
    intro i _
    ring
  rw [expand,cross,energy_shift,energy_stable Q hq (by omega),sum_sub_distrib]
  simp only [energy,mul_assoc,mul_sum]
  ring

private def alpha : ℤ := 186^2-4*(∑ j ∈ range 20, diff j^2)
private def beta (t : ℕ) : ℤ := -8*(∑ j ∈ range 20, diff j*(entry j-entry (t+j)))
private def gamma (t : ℕ) : ℤ := -4*(∑ j ∈ range 20, (2*entry j^2-2*entry j*entry (t+j)))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private lemma certificate : 0<alpha ∧ ∀ t : Fin 21,
    0<alpha*28^2+beta t*28+gamma t ∧ 0≤2*28*alpha+beta t := by
  decide +kernel

private lemma gap_pos {a : ℤ} (ha : 28≤a) (n : ℕ) :
    0<alpha*a^2+beta (min n 20)*a+gamma (min n 20) := by
  obtain ⟨positive,rows⟩ := certificate
  obtain ⟨v,s⟩ := rows ⟨min n 20,by omega⟩
  change 0<alpha*28^2+beta (min n 20)*28+gamma (min n 20) at v
  change 0≤2*28*alpha+beta (min n 20) at s
  nlinarith [mul_nonneg (sq_nonneg (a-28)) positive.le,
    mul_nonneg (show 0≤a-28 by omega) s]

private lemma clip (n j : ℕ) : entry (n+j)=entry (min n 20+j) := by
  by_cases h : n≤20
  · rw [min_eq_left h]
  · rw [min_eq_right (by omega),entry_zero (by omega),entry_zero (by omega)]

private lemma margin (a : ℤ) (n : ℕ) :
    (186*a)^2-4*energy (X^n*(C a*((X-1)^2*K)+K)-K) (n+20)=
      alpha*a^2+beta (min n 20)*a+gamma (min n 20) := by
  rw [energy_shift_sub _ K (by have := shape.1; omega)]
  simp only [energy,coeff_add,coeff_C_mul,coeff_diff,coeff_K]
  let t := min n 20
  have pt (j : ℕ) :
      (a*diff j+entry j)^2-2*(a*diff j+entry j)*entry (n+j)=
      a^2*diff j^2+2*a*(diff j*(entry j-entry (t+j)))+
      (entry j^2-2*entry j*entry (t+j)) := by rw [clip n j]; dsimp [t]; ring
  simp only [pt,alpha,beta,gamma,sum_add_distrib,sum_sub_distrib,←mul_sum]
  dsimp [t]
  ring

/-- At every plus index and every coefficient a ≥ 28, this fixed multiplier
makes four times the tail energy smaller than the leading square. -/
theorem plus_factor_energy {a : ℕ} (ha : 28≤a) (n : ℕ) :
    let T := polynomialTerm true (C (a:ℤ)*X+C (-(a:ℤ))) n
    ∃ W : ℤ[X], W≠0 ∧ 4*energy (T*W) (T*W).natDegree < (T*W).leadingCoeff^2 := by
  let T := polynomialTerm true (C (a:ℤ)*X+C (-(a:ℤ))) n
  let W : ℤ[X] := (X-1)*K
  have hn : K≠0 := by intro e; have := shape.2; simp [e] at this
  have xne : (X-1:ℤ[X])≠0 := by simpa using X_sub_C_ne_zero (1:ℤ)
  have wn : W≠0 := mul_ne_zero xne hn
  have ap : (a:ℤ)≠0 := by omega
  have sd : (C (a:ℤ)*X+C (-(a:ℤ))).natDegree=1 := natDegree_linear ap
  have sh := polynomialTerm_shape true (C (a:ℤ)*X+C (-(a:ℤ))) (by omega) n
  have dt : T.natDegree=1+n := by simpa only [T,sd] using sh.1
  have lt' : T.leadingCoeff=a := sh.2.trans (leadingCoeff_linear ap)
  have tn := leadingCoeff_ne_zero.mp (lt' ▸ ap)
  have deg : (T*W).natDegree=n+20 := by
    rw [natDegree_mul tn wn,show W=(X-1)*K from rfl,natDegree_mul xne hn,
      show (X-1:ℤ[X]).natDegree=1 by simpa using natDegree_X_sub_C (1:ℤ),dt,shape.1]
    omega
  have lc : (T*W).leadingCoeff=(a:ℤ)*186 := by
    rw [leadingCoeff_mul,show W=(X-1)*K from rfl,leadingCoeff_mul,shape.2,lt',
      show (X-1:ℤ[X]).leadingCoeff=1 by simpa using (monic_X_sub_C (1:ℤ)).leadingCoeff]
    ring
  have expr : T*W = X^n*(C (a:ℤ)*((X-1)^2*K)+K)-K := by
    calc T*W = ((X-1)*T)*K := by dsimp [W]; ring
         _ = _ := by rw [show (X-1)*T=_ from balanced_telescoping true (a:ℤ) n]; simp [sign]; ring
  refine ⟨W,wn,?_⟩
  change 4*energy (T*W) (T*W).natDegree < (T*W).leadingCoeff^2
  rw [deg,lc,expr]
  have g := gap_pos (a:=(a:ℤ)) (by omega) n
  rw [←margin] at g
  nlinarith

#print axioms plus_factor_energy

end CunninghamChain.LinearRoots.PlusMultiplier
