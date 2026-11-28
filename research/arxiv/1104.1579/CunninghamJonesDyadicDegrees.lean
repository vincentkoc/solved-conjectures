import CunninghamJonesLocalFactors
import CunninghamJonesDegreeResidues
import research.arxiv.«1104.1579».CunninghamJonesFactorOrders

/-! Local factor degrees for Jones polynomials. -/

namespace CunninghamChain
open Polynomial
open scoped Polynomial
open Finset

private abbrev ρ (p : ℕ) := Int.castRingHom (ZMod p)

private lemma no_common_at {p : ℕ} [Fact p.Prime] {A B : ℤ[X]} {x : ℤ}
    (he : ¬(p:ℤ)^2 ∣ (A*B).eval x) {f : (ZMod p)[X]} (hf : Irreducible f)
    (ha : f ∣ A.map (ρ p)) (hb : f ∣ B.map (ρ p)) :
    ¬f ∣ X-C (x:ZMod p) := by
  intro hd
  have hass := hf.associated_of_dvd (irreducible_X_sub_C (x:ZMod p)) hd
  have root {U : ℤ[X]} (hU : f ∣ U.map (ρ p)) : (p:ℤ) ∣ U.eval x := by
    have h := (dvd_iff_isRoot.mp (hass.symm.dvd.trans hU) : (U.map (ρ p)).IsRoot (x:ZMod p))
    change (U.map (ρ p)).eval ((ρ p) x)=0 at h
    rw [eval_map_apply] at h
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp h
  exact he (by simpa [pow_two] using mul_dvd_mul (root ha) (root hb))

private lemma geom_eq (m j : ℕ) :
    (X-1)*jonesSumPolynomial m j = X*(X^j-1)+C (m:ℤ)*(X-1) := by
  have h := jones_geometric_map (RingHom.id ℤ) m j
  simp only [Polynomial.map_id, RingHom.id_apply] at h
  linear_combination h

private lemma shifted_power {p m a d : ℕ} [Fact p.Prime] (hp : p ∣ m) :
    (X-1)*(jonesSumPolynomial m (p^a*d)).map (ρ p) = X*(X^d-1)^(p^a) := by
  have e := congrArg (Polynomial.map (ρ p)) (geom_eq m (p^a*d))
  have hm₀ := (ZMod.natCast_eq_zero_iff m p).mpr hp
  simp only [Polynomial.map_mul,Polynomial.map_sub,map_X,Polynomial.map_one,Polynomial.map_add,
    map_C,Int.coe_castRingHom,Int.cast_natCast,Polynomial.map_pow,ρ,hm₀,C_0,zero_mul,add_zero] at e
  rw [e]
  congr 1
  rw [sub_pow_char_pow,Nat.mul_comm (p^a),pow_mul,one_pow]

private lemma unity_reduction {d p : ℕ} [Fact p.Prime] (hd : ¬p ∣ d) :
    Squarefree (X^d-1 : (ZMod p)[X]) ∧ (X^d-1 : (ZMod p)[X]) ≠ 0 := by
  have hd₀ : (d:ZMod p) ≠ 0 := fun e => hd ((ZMod.natCast_eq_zero_iff d p).mp e)
  have hd' : d ≠ 0 := by rintro rfl; exact hd (dvd_zero p)
  exact ⟨(X_pow_sub_one_separable_iff.mpr hd₀).squarefree,
    (monic_X_pow_sub_C (1:ZMod p) hd').ne_zero⟩

private lemma shared_factor_at_one {p u : ℕ} [Fact p.Prime] {A B H D : ℤ[X]}
    {f : (ZMod p)[X]} (hf : Irreducible f) (hA : f ∣ A.map (ρ p)) (hB : f ∣ B.map (ρ p))
    (hfH : f ∣ H.map (ρ p)) (hsq : Squarefree (H.map (ρ p))) (h₀ : H.map (ρ p) ≠ 0)
    (hu : (u:ZMod p) ≠ 0) (he : ((X-1)*A)*B=H*D+C (p:ℤ)*(C (u:ℤ)*(X-1))) :
    f ∣ X-C (1:ZMod p) := by
  have hw := common_factor_dvd_correction he hsq h₀ hf hfH
    (show f ∣ ((X-1)*A).map (ρ p) by rw [Polynomial.map_mul]; exact dvd_mul_of_dvd_right hA _) hB
  have hw' : f ∣ C (u:ZMod p)*(X-1) := by simpa [ρ] using hw
  rcases hf.prime.dvd_mul.mp hw' with hC|h₁
  · exact (hf.not_isUnit (isUnit_of_dvd_unit hC (isUnit_C.mpr (isUnit_iff_ne_zero.mpr hu)))).elim
  · simpa using h₁

/-- When neither evaluation at zero and one is divisible by p², the two factors
reduce to coprime polynomials at a prime dividing the constant. -/
theorem jones_factor_reductions_coprime {p m a d : ℕ} [Fact p.Prime]
    (hp : p ∣ m) (hm : ¬p^2 ∣ m) (hd : ¬p ∣ d) (hs : ¬p^2 ∣ m+p^a*d)
    {A B : ℤ[X]} (ha : A.Monic) (he : A*B=jonesSumPolynomial m (p^a*d)) :
    IsCoprime (A.map (Int.castRingHom (ZMod p))) (B.map (Int.castRingHom (ZMod p))) := by
  obtain ⟨u,hu⟩ := hp
  have hu₀ : (u:ZMod p) ≠ 0 := by
    intro hz
    have hd' := (ZMod.natCast_eq_zero_iff u p).mp hz
    apply hm
    rw [hu,pow_two]
    exact Nat.mul_dvd_mul_left p hd'
  let H : ℤ[X] := X^d-1
  let h : (ZMod p)[X] := X^d-1
  have hmap : H.map (ρ p) = h := by simp [H,h]
  obtain ⟨hsq,h₀⟩ := unity_reduction hd
  have hgeom := geom_eq m (p^a*d)
  rw [←he] at hgeom
  obtain ⟨D,hD⟩ : H ∣ (X:ℤ[X])^(p^a*d)-1 := by
    dsimp [H]
    rw [Nat.mul_comm, pow_mul]
    exact sub_one_dvd_pow_sub_one ..
  let W : ℤ[X] := C (u:ℤ)*(X-1)
  have key : ((X-1)*A)*B=H*(X*D)+C (p:ℤ)*W := by
    rw [mul_assoc,hgeom,hD,hu]
    simp only [Nat.cast_mul,map_mul,W]
    ring
  have hmod := shifted_power (a:=a) (d:=d) (hu ▸ dvd_mul_right p u : p ∣ m)
  rw [←he,Polynomial.map_mul] at hmod
  change (X-1)*(A.map (ρ p)*B.map (ρ p))=X*h^(p^a) at hmod
  have val (x : ℤ) (hₓ : x=0 ∨ x=1) :
      (A*B).eval x=if x=0 then (m:ℤ) else (m:ℤ)+(p^a*d:ℕ) := by
    rcases hₓ with rfl|rfl <;> simp [he,jonesSumPolynomial,eval_finsetSum]
  apply isCoprime_of_irreducible_dvd (fun hz => (ha.map _).ne_zero hz.1)
  intro f hf hA hB
  have ho : ¬f ∣ X-C (0:ZMod p) := by
    simpa only [Int.cast_zero] using no_common_at (x:=0) (by
      rw [val 0 (Or.inl rfl),if_pos rfl]
      exact_mod_cast hm) hf hA hB
  have hl : ¬f ∣ X-C (1:ZMod p) := by
    simpa only [Int.cast_one] using no_common_at (x:=1) (by
      rw [val 1 (Or.inr rfl),if_neg (by decide)]
      exact_mod_cast hs) hf hA hB
  have hnX : ¬f ∣ X := by simpa using ho
  have hd' : f ∣ X*h^(p^a) := hmod ▸ dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hA _) _
  have hfH := hf.prime.dvd_of_dvd_pow ((hf.prime.dvd_mul.mp hd').resolve_left hnX)
  exact hl (shared_factor_at_one hf hA hB (hmap ▸ hfH) (hmap ▸ hsq) (hmap ▸ h₀) hu₀ key)

/-- The two factor degrees are multiples of pᵃ or occupy adjacent residues
on opposite sides of multiples of pᵃ. -/
theorem jones_factor_degree_residues {p m a d : ℕ} [Fact p.Prime]
    (hp : p ∣ m) (hm : ¬p^2 ∣ m) (hd : ¬p ∣ d) (hs : ¬p^2 ∣ m+p^a*d)
    {A B : ℤ[X]} (ha : A.Monic) (hb : B.Monic) (he : A*B=jonesSumPolynomial m (p^a*d)) :
    (p^a ∣ A.natDegree ∧ p^a ∣ B.natDegree) ∨
    (p^a ∣ A.natDegree-1 ∧ p^a ∣ B.natDegree+1) ∨
    (p^a ∣ A.natDegree+1 ∧ p^a ∣ B.natDegree-1) := by
  have hc := jones_factor_reductions_coprime hp hm hd hs ha he
  have eqn := shifted_power (a:=a) (d:=d) hp
  rw [←he,Polynomial.map_mul] at eqn
  simpa only [ha.natDegree_map,hb.natDegree_map] using
    factor_degrees_of_shifted_power (ha.map _).ne_zero (hb.map _).ne_zero hc eqn

/-- Every monic factor has degree divisible by the full power of two in the degree. -/
theorem jones_dyadic_factor_degree {m a d : ℕ} (hm : m % 4=2) (hd : Odd d)
    {A : ℤ[X]} (ha : A.Monic) (hdiv : A ∣ jonesSumPolynomial m (2^a*d)) :
    2^a ∣ A.natDegree := by
  have hd₀ := hd.pos
  have hj : 0 < 2^a*d := by positivity
  have oddN (h : 0 < a) : Odd (2^a*d+1) := by
    obtain ⟨b,hb⟩ := Nat.exists_eq_succ_of_ne_zero h.ne'
    rw [hb,pow_succ]
    exact ⟨2^b*d,by ring⟩
  rcases a with _|a
  · simp
  have hA := jones_factor_even_degree (by omega : 2 ≤ m) ha hdiv (oddN (by omega))
  rcases a with _|a
  · simpa using even_iff_two_dvd.mp hA
  have h₄ : 4 ∣ 2^(a+1+1)*d := ⟨2^a*d,by ring⟩
  obtain ⟨B,he⟩ := hdiv
  have hb := ha.of_mul_monic_left (he ▸ (jonesSumPolynomial_shape m _).2 hj)
  have hB := jones_factor_even_degree (by omega : 2 ≤ m) hb (he ▸ dvd_mul_left ..) (oddN (by omega))
  have cases := jones_factor_degree_residues (p:=2) (a:=a+1+1) (d:=d) (m:=m)
    (by omega) (by norm_num; omega) (by obtain ⟨v,hv⟩ := hd; omega)
    (by norm_num; omega) ha hb he.symm
  have ht : 2 ∣ 2^(a+1+1) := dvd_pow_self _ (by omega)
  rcases cases with h|h|h
  · exact h.1
  · have := ht.trans h.2
    have := even_iff_two_dvd.mp hB
    omega
  · have := ht.trans h.1
    have := even_iff_two_dvd.mp hA
    omega

/-- When a prime divides m−1 exactly once and j+1 has prime part pᵇ,
one of the two factor degrees is divisible by pᵇ. -/
theorem jones_predecessor_factor_degree {p m j b d : ℕ} [Fact p.Prime]
    (hm : 1 ≤ m) (hp : p ∣ m-1) (hv : ¬p^2 ∣ m-1) (hd : ¬p ∣ d)
    (hs : ¬p^2 ∣ m+j) (hj : j+1=p^b*d)
    {A B : ℤ[X]} (ha : A.Monic) (hb : B.Monic) (he : A*B=jonesSumPolynomial m j) :
    p^b ∣ A.natDegree ∨ p^b ∣ B.natDegree := by
  obtain ⟨u,hu⟩ := hp
  have hu₀ : (u:ZMod p) ≠ 0 := by
    intro hz
    apply hv
    rw [hu,pow_two]
    exact Nat.mul_dvd_mul_left _ ((ZMod.natCast_eq_zero_iff u p).mp hz)
  have hmu : (m:ℤ)-1=(p:ℤ)*u := by exact_mod_cast (show (m:ℤ)-1=((p*u:ℕ):ℤ) by omega)
  let H : ℤ[X] := X^d-1
  let h : (ZMod p)[X] := X^d-1
  have hmap : H.map (ρ p) = h := by simp [H,h]
  obtain ⟨hsq,h₀⟩ := unity_reduction hd
  obtain ⟨D,hD⟩ : H ∣ (X:ℤ[X])^(j+1)-1 := by
    dsimp [H]
    rw [hj,Nat.mul_comm,pow_mul]
    exact sub_one_dvd_pow_sub_one ..
  let W : ℤ[X] := C (u:ℤ)*(X-1)
  have hgeom := jones_geometric_map (RingHom.id ℤ) m j
  simp only [Polynomial.map_id,RingHom.id_apply] at hgeom
  rw [←he] at hgeom
  have hpC : C (m:ℤ)-1 = C (p:ℤ)*C (u:ℤ) := by simpa using congrArg (C : ℤ → ℤ[X]) hmu
  have key : ((X-1)*A)*B=H*D+C (p:ℤ)*W := by
    dsimp only [W]
    linear_combination hgeom + hD + (X-1)*hpC
  have hM : (m:ZMod p)=1 := by
    have v := congrArg (ρ p) hmu
    simpa [ρ,sub_eq_zero] using v
  have hpow : (X-1)*(A.map (ρ p)*B.map (ρ p))=h^(p^b) := by
    have e := congrArg (Polynomial.map (ρ p)) hgeom
    simp only [ρ,Polynomial.map_mul,Polynomial.map_sub,Polynomial.map_add,Polynomial.map_pow,
      map_C,map_X,Polynomial.map_one,Int.coe_castRingHom,Int.cast_natCast,hM,C_1,sub_self,
      zero_mul,add_zero] at e
    rw [e,hj,Nat.mul_comm (p^b),pow_mul]
    dsimp [h]
    rw [sub_pow_char_pow,one_pow]
  have hc : IsCoprime (A.map (ρ p)) (B.map (ρ p)) := by
    apply isCoprime_of_irreducible_dvd (fun hz => (ha.map _).ne_zero hz.1)
    intro f hf hA hB
    have hl : ¬f ∣ X-C (1:ZMod p) := by
      simpa only [Int.cast_one] using no_common_at (x:=1) (by
        have e : (A*B).eval 1=((m+j:ℕ):ℤ) := by simp [he,jonesSumPolynomial,eval_finsetSum]
        rw [e]
        exact_mod_cast hs) hf hA hB
    have hd' : f ∣ h^(p^b) := hpow ▸ dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hA _) _
    have hfH := hf.prime.dvd_of_dvd_pow hd'
    exact hl (shared_factor_at_one hf hA hB (hmap ▸ hfH) (hmap ▸ hsq) (hmap ▸ h₀) hu₀ key)
  simpa only [ha.natDegree_map,hb.natDegree_map] using
    factor_degree_of_linear_times_product (ha.map _).ne_zero (hb.map _).ne_zero hc hpow

#print axioms jones_predecessor_factor_degree

#print axioms jones_factor_degree_residues
#print axioms jones_dyadic_factor_degree

#print axioms jones_factor_reductions_coprime

end CunninghamChain
