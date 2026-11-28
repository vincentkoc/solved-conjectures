import HosoyaCoprimeLucasTower
import HosoyaTwoWindowLift
import LucasFibonacciProgressionClosure

/-! Explicit mutually coprime finite tests after excluding arbitrary primes. -/

namespace Arxiv.«2211.10788».ProgressionClosure
open CongruenceClosure

private lemma detector_pos {d : ℕ} (hd : 0<d) (y : ℤ) (e : ℕ) :
    0 < detector d y e :=
  Nat.mul_pos (Nat.zero_lt_of_lt (layer_size hd y _)) (Nat.zero_lt_of_lt (layer_size hd y _))

private lemma split_mod {x y : ℤ} {A B : ℕ} (hc : A.Coprime B) :
    x ≡ y [ZMOD (A*B:ℕ)] ↔ x ≡ y [ZMOD A] ∧ x ≡ y [ZMOD B] := by
  rw [Nat.cast_mul]
  exact (Int.modEq_and_modEq_iff_modEq_mul (m := (A:ℤ)) (n := (B:ℤ)) (by simpa using hc)).symm

private lemma hit_signed {d r M t : ℕ} {y : ℤ} :
    Hit d r M y t ↔ (signed ((r+d*t:ℕ):ℤ) : ZMod M)=y := by
  rw [signed_nat]
  exact (ZMod.intCast_eq_intCast_iff ..).symm

/-- Each detector separately recovers a true bilateral witness in the input index class. -/
theorem detector_lifts {d r t : ℕ} (hd : 0<d) {y : ℤ} (e : ℕ)
    (hit : Hit d r (detector d y e) y t) :
    ∃ w : ℤ, w ≡ r [ZMOD d] ∧ w.natAbs < radius d y (2*e) ∧ signed w=y := by
  let h := radius d y (2*e)
  have hc := odd_layers_coprime d y (show 2*e ≠ 2*e+1 by omega)
  obtain ⟨a,b⟩ := (split_mod hc).mp hit
  have z₁ := hit_signed.mp (show Hit d r (oddLucas h) y t from a)
  have z₂ := hit_signed.mp (show Hit d r (oddLucas (radius d y (2*e+1))) y t from b)
  rw [radius_succ] at z₂
  have hsize := layer_size hd y (2*e+1)
  rw [radius_succ] at hsize
  obtain ⟨w,q,hn,hw,hy⟩ := two_window_lift (radius_pos hd y (2*e)) (radius_even ..)
    (oddLucas_dvd h) (oddLucas_dvd (2*h)) (lucas_le_twice_odd h)
    (lucas_le_twice_odd (2*h)) (layer_size hd y _) hsize z₁ z₂
  obtain ⟨c,hc'⟩ := step_dvd_radius d y (2*e)
  rw [hc'] at hn
  refine ⟨w,Int.modEq_iff_dvd.mpr ⟨4*(c:ℤ)*q-t,?_⟩,hw,hy⟩
  push_cast at hn
  linarith

private lemma detector_period (d : ℕ) (y : ℤ) (e : ℕ) :
    Function.Periodic (fun z : ℤ => (signed z : ZMod (detector d y e))) (8*(radius d y (2*e):ℤ)) := by
  intro z
  let h := radius d y (2*e)
  apply (ZMod.intCast_eq_intCast_iff ..).mpr
  apply (split_mod (odd_layers_coprime d y (show 2*e ≠ 2*e+1 by omega))).mpr
  have he := radius_even d y (2*e)
  constructor
  · have p := (lucas_period he).int_mul 2 z
    change (signed (z+2*(4*h)) : ZMod (lucas h)) = signed z at p
    have eq := congrArg (ZMod.castHom (oddLucas_dvd h) (ZMod (oddLucas h))) p
    simp only [map_intCast] at eq
    apply (ZMod.intCast_eq_intCast_iff ..).mp
    simpa only [show 2*(4*(h:ℤ))=8*h by ring] using eq
  · rw [radius_succ]
    have p := lucas_period (even_two_mul h) z
    change (signed (z+4*((2*h:ℕ):ℤ)) : ZMod (lucas (2*h))) = signed z at p
    have eq := congrArg (ZMod.castHom (oddLucas_dvd (2*h)) (ZMod (oddLucas (2*h)))) p
    simp only [map_intCast] at eq
    apply (ZMod.intCast_eq_intCast_iff ..).mp
    simpa only [show 4*((2*h:ℕ):ℤ)=8*h by push_cast; ring] using eq

/-- The number of progression terms tested at level e, independent of the step and offset. -/
def span (y : ℤ) (e : ℕ) : ℕ := 32*2^(2*e)*((threshold y).log2+1)

private lemma reduce_test {d r t : ℕ} {y : ℤ} (e : ℕ) (hit : Hit d r (detector d y e) y t) :
    Hit d r (detector d y e) y (t%span y e) := by
  let P := span y e
  let x := r+d*(t%P)
  let q := t/P
  have ht : t%P+P*q=t := Nat.mod_add_div _ _
  have he : r+d*t = x+q*(8*radius d y (2*e)) := by
    calc _ = r+d*(t%P+P*q) := by rw [ht]
         _ = _ := by dsimp [x,P,span,radius,window]; ring
  have h := hit_signed.mp hit
  have p := (detector_period d y e).int_mul (q:ℤ) x
  change (signed ((x:ℤ)+(q:ℤ)*(8*(radius d y (2*e):ℤ))) : ZMod (detector d y e))=signed (x:ℤ) at p
  apply hit_signed.mpr
  apply p.symm.trans
  rw [he] at h
  simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using h

/-- Every member of the pairwise coprime family is itself a bounded test for the bilateral orbit. -/
theorem coprime_detector_test {d : ℕ} (hd : 0<d) (r : ℕ) (y : ℤ) (e : ℕ) :
    (∃ w : ℤ, w ≡ r [ZMOD d] ∧ signed w=y) ↔
      ∃ t < span y e, Hit d r (detector d y e) y t := by
  constructor
  · intro h
    obtain ⟨t,ht⟩ := (progression_local_global hd r y).mpr h _ (detector_pos hd y e)
    exact ⟨_,Nat.mod_lt _ (by unfold span; positivity),reduce_test e ht⟩
  · rintro ⟨t,_,ht⟩
    obtain ⟨w,hw,_,hy⟩ := detector_lifts hd e ht
    exact ⟨w,hw,hy⟩

/-- Discarding every modulus touched by any prime factor of B preserves the exact index-class closure. -/
theorem coprime_progression_closure {d B : ℕ} (hd : 0<d) (hB : 0<B) (r : ℕ) (y : ℤ) :
    (∀ M > 0, M.Coprime B → ∃ t, Hit d r M y t) ↔
      ∃ w : ℤ, w ≡ r [ZMOD d] ∧ signed w=y := by
  constructor
  · intro all
    obtain ⟨e,_,hc⟩ := exists_coprime_detector d y hB
    obtain ⟨t,ht⟩ := all _ (detector_pos hd y e) hc
    obtain ⟨w,hw,_,hy⟩ := detector_lifts hd e ht
    exact ⟨w,hw,hy⟩
  · intro h M hM _
    exact (progression_local_global hd r y).mpr h M hM

#print axioms detector_lifts
#print axioms coprime_detector_test
#print axioms coprime_progression_closure

end Arxiv.«2211.10788».ProgressionClosure
