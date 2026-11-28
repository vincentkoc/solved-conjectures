import Mathlib

/-! A simple factor in a squarefree reduction and an integral factorization. -/

namespace CunninghamChain
open Polynomial
open scoped Polynomial

variable {p : ℕ} [Fact p.Prime]

private abbrev red (p : ℕ) := Int.castRingHom (ZMod p)

private lemma scalar_dvd_of_map_zero {F : ℤ[X]} (h : F.map (red p)=0) : C (p:ℤ) ∣ F := by
  apply (C_dvd_iff_dvd_coeff ..).mpr
  intro n
  have hc := congrArg (fun f : (ZMod p)[X] => f.coeff n) h
  simpa [red,ZMod.intCast_zmod_eq_zero_iff_dvd] using hc

private lemma lift_divisibility {H F : ℤ[X]} (hf : H.map (red p) ∣ F.map (red p)) :
    ∃ U V : ℤ[X], F=H*U+C (p:ℤ)*V := by
  obtain ⟨u,hu⟩ := hf
  obtain ⟨U,hU⟩ := Polynomial.map_surjective (f:=red p) ZMod.intCast_surjective u
  have hz : (F-H*U).map (red p)=0 := by rw [Polynomial.map_sub,Polynomial.map_mul,hU,hu,sub_self]
  obtain ⟨V,hV⟩ := scalar_dvd_of_map_zero hz
  exact ⟨U,V,by linear_combination hV⟩

/-- If AB=HD+pW and H is squarefree modulo p, a factor of H shared by A and B
modulo p must also divide W modulo p. -/
theorem common_factor_dvd_correction {A B H D W : ℤ[X]}
    (he : A*B=H*D+C (p:ℤ)*W) (hs : Squarefree (H.map (Int.castRingHom (ZMod p))))
    (hH : H.map (Int.castRingHom (ZMod p)) ≠ 0) {f : (ZMod p)[X]} (hf : Irreducible f)
    (hfH : f ∣ H.map (Int.castRingHom (ZMod p))) (hfA : f ∣ A.map (Int.castRingHom (ZMod p))) (hfB : f ∣ B.map (Int.castRingHom (ZMod p))) :
    f ∣ W.map (Int.castRingHom (ZMod p)) := by
  obtain ⟨g,hg⟩ := hfH
  have hfg : ¬ f ∣ g := by
    rintro ⟨l,hl⟩
    exact hf.not_isUnit (hs f ⟨l,by rw [hg,hl]; ring⟩)
  obtain ⟨L,hL⟩ := Polynomial.map_surjective (f:=red p) ZMod.intCast_surjective g
  have hdiv {U : ℤ[X]} (hu : f ∣ U.map (red p)) : H.map (red p) ∣ (L*U).map (red p) := by
    obtain ⟨v,hv⟩ := hu
    exact ⟨v,by rw [Polynomial.map_mul,hL,hg,hv]; ring⟩
  obtain ⟨u,v,ha⟩ := lift_divisibility (hdiv hfA)
  obtain ⟨s,t,hb⟩ := lift_divisibility (hdiv hfB)
  let P : ℤ[X] := C (p:ℤ)
  let K := H*u*s+P*(u*t+s*v)-L^2*D
  have h : P*(L^2*W-P*v*t)=H*K := by
    dsimp only [P,K]
    linear_combination -L^2*he + (L*B)*ha + (H*u+C (p:ℤ)*v)*hb
  have hP : P.map (red p) = 0 := by simp [P,red]
  have hK : K.map (red p)=0 := by
    have hm := congrArg (Polynomial.map (red p)) h
    simp only [Polynomial.map_mul,hP,zero_mul] at hm
    exact (mul_eq_zero.mp hm.symm).resolve_left hH
  obtain ⟨N,hN⟩ := scalar_dvd_of_map_zero hK
  have hP₀ : P≠0 := by
    dsimp [P]
    exact C_ne_zero.mpr (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  have hz : L^2*W-P*v*t=H*N := by
    apply mul_left_cancel₀ hP₀
    change K=P*N at hN
    rw [h,hN]
    ring
  have hh := congrArg (Polynomial.map (red p)) hz
  simp only [Polynomial.map_sub,Polynomial.map_pow,Polynomial.map_mul,hP,zero_mul,sub_zero,hL,hg] at hh
  have hd : f ∣ g^2*W.map (red p) := ⟨g*N.map (red p),by rw [hh]; ring⟩
  exact (hf.prime.dvd_mul.mp hd).resolve_left (fun h => hfg (hf.prime.dvd_of_dvd_pow h))

#print axioms common_factor_dvd_correction

end CunninghamChain
