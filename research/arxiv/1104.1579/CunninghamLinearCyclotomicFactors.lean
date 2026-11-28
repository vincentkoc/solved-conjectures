import CunninghamLinearReciprocalRoots

/-! The complete list of cyclotomic factors for the two signs and positive-leading linear seeds. -/

namespace CunninghamChain.LinearRoots
open Polynomial

private def required (s : ℤ) : ℕ → ℤ × ℤ
  | 0 => (0,0)
  | r+1 => let (a,b) := required s r; (1-b,a+s*(b-1))

private lemma required_root {z : ℂ} {s : ℤ} (hq : z^2-s*z+1=0) (r : ℕ) :
    z^r*((z-1)*((required s r).1*z+(required s r).2)+1)=1 := by
  induction r with
  | zero => simp [required]
  | succ r ih =>
    obtain ⟨u,v,hp⟩ : ∃ u v, required s r = (u,v) := ⟨_,_,rfl⟩
    rw [required,hp]
    rw [hp] at ih
    simp only [pow_succ,Int.cast_sub,Int.cast_one,Int.cast_add,Int.cast_mul] at *
    have hstep : z*((1-v)*z+(u+s*(v-1)))+1 = (u:ℂ)*z+v := by
      linear_combination (1-(v:ℂ))*hq
    calc z^r*z*((z-1)*((1-v)*z+(u+s*(v-1)))+1) =
        z^r*((z-1)*(z*((1-v)*z+(u+s*(v-1)))+1)+1) := by ring
      _ = 1 := by rw [hstep]; exact ih

private lemma linear_unique {d : ℕ} (hd : 0<d) (ht : 1<d.totient) {z : ℂ}
    (hz : IsPrimitiveRoot z d) {c e : ℤ} (he : (c:ℂ)*z+e=0) : c=0 ∧ e=0 := by
  let P : ℚ[X] := C (c:ℚ)*X+C (e:ℚ)
  have hdiv : cyclotomic d ℚ ∣ P := (primitive_dvd hd hz _).mpr (by simpa [P] using he)
  have hP : P=0 := by
    by_contra h
    have hle := (natDegree_le_of_dvd hdiv h).trans (natDegree_linear_le (a := (c:ℚ)) (b := (e:ℚ)))
    rw [natDegree_cyclotomic] at hle
    omega
  have h0 := congrArg (fun P : ℚ[X] => P.coeff 0) hP
  have h1 := congrArg (fun P : ℚ[X] => P.coeff 1) hP
  simp [P] at h0
  simp [P,h0] at h1
  exact ⟨h1,h0⟩

private lemma required_iff (k : Bool) (a b : ℤ) (n : ℕ) {d : ℕ} (hd : 2<d)
    (ht : 1<d.totient) {z : ℂ} (hz : IsPrimitiveRoot z d) {s : ℤ} (hq : z^2-s*z+1=0) :
    cyclotomic d ℚ ∣ term k a b n ↔
      a=sign k*(required s (n%d)).1 ∧ b=sign k*(required s (n%d)).2 := by
  rw [primitive_dvd (by omega) hz,root_equation k a b n z (hz.ne_one (by omega))]
  let u := (required s (n%d)).1
  let v := (required s (n%d)).2
  have hr := required_root hq (n%d)
  change z^(n%d)*((z-1)*(u*z+v)+1)=1 at hr
  rw [hz.eq_orderOf,pow_mod_orderOf] at hr
  have hsign : z^n*((z-1)*((sign k*u:ℤ)*z+(sign k*v:ℤ))+sign k) = sign k := by
    push_cast
    linear_combination (sign k:ℂ)*hr
  constructor
  · intro h
    have hzn : z^n*(z-1)≠0 := mul_ne_zero (pow_ne_zero _ (hz.ne_zero (by omega))) (sub_ne_zero.mpr (hz.ne_one (by omega)))
    have hx : z^n*(z-1)*(((a-sign k*u:ℤ):ℂ)*z+((b-sign k*v:ℤ):ℂ))=0 := by
      push_cast at *
      linear_combination h-hsign
    have hh := linear_unique (by omega) ht hz ((mul_eq_zero.mp hx).resolve_left hzn)
    exact ⟨sub_eq_zero.mp hh.1,sub_eq_zero.mp hh.2⟩
  · rintro ⟨rfl,rfl⟩
    exact hsign

private lemma geom (n d : ℕ) (hd : 1<d) :
    cyclotomic d ℚ ∣ term true 1 1 n ↔ d∣n+2 := by
  let z := Complex.exp (2 * Real.pi * Complex.I / d)
  have hz : IsPrimitiveRoot z d := Complex.isPrimitiveRoot_exp d (by omega)
  rw [primitive_dvd (by omega) hz,root_equation _ _ _ _ _ (hz.ne_one hd)]
  rw [show (sign true:ℂ)=1 by norm_num [sign],Int.cast_one,one_mul,
    show (z-1)*(z+1)+1=z^2 by ring,←pow_add]
  exact hz.pow_eq_one_iff_dvd _

private lemma three_spec {n : ℕ} {k : Bool} {a b : ℤ} :
    cyclotomic 3 ℚ ∣ term k a b n ↔
      a=sign k*(required (-1) (n%3)).1 ∧ b=sign k*(required (-1) (n%3)).2 := by
  have hz := Complex.isPrimitiveRoot_exp 3 (by decide)
  apply required_iff _ _ _ _ (by decide) (by decide) hz
  have h := (primitive_dvd (by decide) hz _).mp (dvd_refl (cyclotomic 3 ℚ))
  simpa [cyclotomic_three] using h

private lemma four_spec {n : ℕ} {k : Bool} {a b : ℤ} :
    cyclotomic 4 ℚ ∣ term k a b n ↔
      a=sign k*(required 0 (n%4)).1 ∧ b=sign k*(required 0 (n%4)).2 := by
  let z := Complex.exp (2 * Real.pi * Complex.I / 4)
  have hz : IsPrimitiveRoot z 4 := by simpa [z] using Complex.isPrimitiveRoot_exp 4 (by decide)
  apply required_iff _ _ _ _ (by decide) (by decide) hz
  have h2 : z^2-1≠0 := fun h => (by decide : ¬4∣2) (hz.dvd_of_pow_eq_one 2 (sub_eq_zero.mp h))
  have he : (z^2-1)*(z^2+1)=0 := by linear_combination hz.pow_eq_one
  simpa using (mul_eq_zero.mp he).resolve_left h2

private lemma six_spec {n : ℕ} {k : Bool} {a b : ℤ} :
    cyclotomic 6 ℚ ∣ term k a b n ↔
      a=sign k*(required 1 (n%6)).1 ∧ b=sign k*(required 1 (n%6)).2 := by
  have hz := Complex.isPrimitiveRoot_exp 6 (by decide)
  apply required_iff _ _ _ _ (by decide) (by decide) hz
  have h := (primitive_dvd (by decide) hz _).mp (dvd_refl (cyclotomic 6 ℚ))
  simpa [cyclotomic_six] using h

/-- The five first-kind seeds and exact indices supporting a cyclotomic factor of order above two. -/
theorem higher_cyclotomic_iff {k : Bool} {a b : ℤ} (ha : 0<a) (n d : ℕ) (hd : 2<d) :
    cyclotomic d ℚ ∣ term k a b n ↔ k=true ∧
      ((a=1 ∧ b=1 ∧ d∣n+2) ∨
       (a=1 ∧ b=0 ∧ d=4 ∧ n%4=1) ∨
       (a=1 ∧ b= -1 ∧ d=6 ∧ n%6=1) ∨
       (a=2 ∧ b= -1 ∧ d=6 ∧ n%6=2) ∨
       (a=2 ∧ b=0 ∧ d=6 ∧ n%6=3)) := by
  by_cases hg : k=true ∧ a=1 ∧ b=1
  · obtain ⟨rfl,rfl,rfl⟩ := hg
    simpa using geom n d (by omega)
  have no : ¬(k=true ∧ a=1 ∧ b=1) := hg
  by_cases h3 : d=3
  · subst d
    rw [three_spec]
    have hr := Nat.mod_lt n (by decide : 0<3)
    generalize n%3=r at *
    interval_cases r <;> cases k <;> norm_num [sign,required] at * <;> omega
  by_cases h4 : d=4
  · subst d
    rw [four_spec]
    have hr := Nat.mod_lt n (by decide : 0<4)
    generalize n%4=r at *
    interval_cases r <;> cases k <;> norm_num [sign,required] at * <;> omega
  by_cases h6 : d=6
  · subst d
    rw [six_spec]
    have hr := Nat.mod_lt n (by decide : 0<6)
    generalize n%6=r at *
    interval_cases r <;> cases k <;> norm_num [sign,required] at * <;> omega
  constructor
  · intro h
    rcases linear_cyclotomic_orders ha no (by omega) h with h|h|h|h|h <;> omega
  · rintro ⟨hk,h⟩
    rcases h with h|h|h|h|h <;> grind

/-- The factors X−1 and X+1 have exact tests at each index, including index zero. -/
theorem linear_cyclotomic_endpoints (k : Bool) (a b : ℤ) (n : ℕ) :
    (cyclotomic 1 ℚ ∣ term k a b n ↔ a+b+sign k*n=0) ∧
    (cyclotomic 2 ℚ ∣ term k a b n ↔ if Even n then b=a else b=a+sign k) := by
  have hone : aeval (1:ℂ) (term k a b n) = ((a+b+sign k*n:ℤ):ℂ) := by
    induction n with
    | zero => simp [term,polynomialTerm]
    | succ n ih => rw [term_step,ih]; push_cast; ring
  have pair (i : ℕ) : aeval (-1:ℂ) (term k a b (2*i)) = (b:ℂ)-a ∧
      aeval (-1:ℂ) (term k a b (2*i+1)) = a-b+sign k := by
    induction i with
    | zero =>
      cases k <;> simp [term,polynomialTerm,sign] <;> constructor <;> ring
    | succ i ih =>
      have e : 2*(i+1)=2*i+1+1 := by omega
      rw [e,term_step,ih.2,term_step,term_step,ih.2]
      constructor <;> ring
  constructor
  · rw [primitive_dvd (by decide) (IsPrimitiveRoot.one (M := ℂ)),hone]
    exact_mod_cast Iff.rfl
  · rw [primitive_dvd (by decide) (IsPrimitiveRoot.neg_one (R := ℂ) 0 (by decide))]
    rcases Nat.even_or_odd n with he | ho
    · rw [if_pos he]
      obtain ⟨i,hi⟩ := he
      rw [show n=2*i by omega,(pair i).1,sub_eq_zero]
      exact_mod_cast Iff.rfl
    · rw [if_neg (Nat.not_even_iff_odd.mpr ho)]
      obtain ⟨i,hi⟩ := ho
      rw [hi,(pair i).2]
      constructor
      · intro h
        exact_mod_cast (show (b:ℂ)=a+sign k by linear_combination -h)
      · intro h
        rw [h]
        push_cast
        ring

/-- After index zero, both signs avoid every cyclotomic factor exactly for a(X−1), a≥2. -/
theorem both_signs_cyclotomic_free_iff (a b : ℤ) (ha : 0<a) :
    (∀ k : Bool, ∀ n d : ℕ, 0<n → 0<d → ¬ cyclotomic d ℚ ∣ term k a b n) ↔
      2≤a ∧ b= -a := by
  constructor
  · intro h
    have sum : a+b=0 := by
      by_contra hs
      rcases lt_or_gt_of_ne hs with hn | hp
      · let n := (-(a+b)).toNat
        have hn' : (n:ℤ) = -(a+b) := Int.toNat_of_nonneg (by omega)
        exact h true n 1 (by omega) (by decide)
          ((linear_cyclotomic_endpoints true a b n).1.mpr (by simp [sign]; omega))
      · let n := (a+b).toNat
        have hn' : (n:ℤ) = a+b := Int.toNat_of_nonneg (by omega)
        exact h false n 1 (by omega) (by decide)
          ((linear_cyclotomic_endpoints false a b n).1.mpr (by simp [sign]; omega))
    have hne : a≠1 := by
      rintro rfl
      have hb : b= -1 := by omega
      subst b
      apply h true 1 6 (by decide) (by decide)
      exact (higher_cyclotomic_iff (k:=true) (a:=1) (b:= -1) (by decide) 1 6 (by decide)).mpr (by decide)
    omega
  · rintro ⟨ha2,rfl⟩ k n d hn hd h
    rcases (show d=1 ∨ d=2 ∨ 2<d by omega) with rfl | rfl | hlarge
    · have he := (linear_cyclotomic_endpoints k a (-a) n).1.mp h
      cases k <;> simp [sign] at he <;> omega
    · have he := (linear_cyclotomic_endpoints k a (-a) n).2.mp h
      split at he <;> cases k <;> simp_all [sign] <;> omega
    · rcases (higher_cyclotomic_iff ha n d hlarge).mp h with ⟨_,h'⟩
      rcases h' with h'|h'|h'|h'|h' <;> omega

#print axioms higher_cyclotomic_iff
#print axioms linear_cyclotomic_endpoints
#print axioms both_signs_cyclotomic_free_iff

end CunninghamChain.LinearRoots
