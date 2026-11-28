import Erdos478EvenGapReflection
import Erdos478DisjointGapFamilies

/-! Simultaneous collisions at all even gap lengths through a specified cutoff. -/

namespace Erdos478.EffectiveResolvent
open Polynomial Finset GapFamilies

private def evenLength {n : ℕ} (i : Fin n) := 2*(i.val+1)
private def lengths (n : ℕ) := univ.map (⟨evenLength,fun a b he => Fin.ext (by dsimp [evenLength] at he; omega)⟩ : Fin n ↪ ℕ)

private noncomputable def gapPoly (R : Type*) [CommRing R] {n : ℕ} (i : Fin n) : R[X] :=
  descPochhammer R (evenLength i)-1

private theorem family_prod (R : Type*) [CommRing R] (n : ℕ) :
    family R (lengths n) = ∏ i : Fin n, gapPoly R i := by
  simp only [family,lengths,Finset.prod_map,gapPoly]
  rfl

private theorem map_gap {A R : Type*} [CommRing A] [CommRing R] (φ : A →+* R) {n : ℕ} (i : Fin n) :
    (gapPoly A i).map φ = gapPoly R i := by simp [gapPoly,Polynomial.map_sub,descPochhammer_map]

private theorem degree_gap (R : Type*) [CommRing R] [IsDomain R] {n : ℕ} (i : Fin n) :
    (gapPoly R i).IsMonicOfDegree (evenLength i) := by
  have hm : (descPochhammer R (evenLength i)).IsMonicOfDegree (evenLength i) :=
    ⟨descPochhammer_natDegree R _,monic_descPochhammer R _⟩
  have hi : 0<evenLength i := by unfold evenLength; omega
  simpa [gapPoly,sub_eq_add_neg] using hm.add_right (q := -(1:R[X])) (by simpa using hi)

private theorem family_simple (n : ℕ) : (family ℂ (lengths n)).Separable := by
  have hs := separable_gap_family (lengths n) (by
    intro k hk
    obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hk
    change 0<2*(i.val+1)
    omega)
  have h := hs.map (f := algebraMap ℚ ℂ)
  simpa [family,Polynomial.map_prod,Polynomial.map_sub,descPochhammer_map] using h

private theorem degree_family (R : Type*) [CommRing R] [IsDomain R] (n : ℕ) :
    (family R (lengths n)).IsMonicOfDegree (∑ i : Fin n, evenLength i) := by
  rw [family_prod]
  constructor
  · rw [natDegree_prod_of_monic _ _ (fun i _ => (degree_gap R i).monic)]
    exact sum_congr rfl (fun i _ => (degree_gap R i).natDegree_eq)
  · exact monic_prod_of_monic _ _ (fun i _ => (degree_gap R i).monic)

private theorem map_family' {A R : Type*} [CommRing A] [CommRing R] (φ : A →+* R) (n : ℕ) :
    (family A (lengths n)).map φ = family R (lengths n) := by
  simp [family_prod,Polynomial.map_prod,map_gap]

private theorem small_root (n : ℕ) (i : Fin n) {z : ℂ} (hz : (gapPoly ℂ i).IsRoot z) :
    ‖z‖ ≤ (2*n+1 : ℕ) := by
  apply (gap_root_norm (n := evenLength i) (by dsimp [evenLength]; omega) hz).trans
  exact_mod_cast (by dsimp [evenLength]; omega : evenLength i + 1 ≤ 2*n+1)

private theorem two_roots_card {p : ℕ} [Fact p.Prime] (h₂ : (2 : ZMod p) ≠ 0)
    {n : ℕ} (i : Fin n) (hs : (gapPoly (ZMod p) i).Separable) {z : ZMod p} (hz : (gapPoly (ZMod p) i).IsRoot z) :
    2 ≤ (gapPoly (ZMod p) i).roots.card := by
  let y := (((evenLength i:ℕ):ZMod p)-1-z)
  obtain ⟨hne,hy⟩ := two_even_roots h₂ (i.val+1) hs hz
  have hne' : z≠y := hne
  have hy' : (gapPoly (ZMod p) i).IsRoot y := hy
  have hn := (degree_gap (ZMod p) i).monic.ne_zero
  have hc : ({z,y} : Finset (ZMod p)) ⊆ (gapPoly (ZMod p) i).roots.toFinset := by
    intro x hx
    simp only [mem_insert,mem_singleton] at hx
    rcases hx with rfl|rfl
    · exact Multiset.mem_toFinset.mpr ((mem_roots hn).mpr hz)
    · exact Multiset.mem_toFinset.mpr ((mem_roots hn).mpr hy')
  simpa [hne'] using (card_le_card hc).trans (gapPoly (ZMod p) i).roots.toFinset_card_le

private theorem count_even_roots {p n : ℕ} [Fact p.Prime] (h₂ : (2 : ZMod p) ≠ 0)
    (hs : (family (ZMod p) (lengths n)).Separable)
    (hr : ∀ i : Fin n, ∃ z : ZMod p, (gapPoly (ZMod p) i).IsRoot z) :
    ((Ico 1 p).image (fun j => j.factorial % p)).card + 2*n ≤ p-1 := by
  classical
  let G := family (ZMod p) (lengths n)
  have hh : ((Ico 1 p).image (fun j => j.factorial % p)).card + G.roots.toFinset.card ≤ p-1 := by
    apply FallingGap.card_add_gap_endpoints
    intro x hx
    have he := isRoot_of_mem_roots (Multiset.mem_toFinset.mp hx)
    change (family (ZMod p) (lengths n)).eval x = 0 at he
    rw [family_prod,eval_prod,Finset.prod_eq_zero_iff] at he
    obtain ⟨i,_,hz⟩ := he
    exact ⟨evenLength i,by dsimp [evenLength]; omega,hz⟩
  have hn := (degree_family (ZMod p) n).monic.ne_zero
  rw [family_prod] at hs hn
  change _ + (family (ZMod p) (lengths n)).roots.toFinset.card ≤ _ at hh
  rw [family_prod,Multiset.toFinset_card_of_nodup (nodup_roots hs),roots_prod _ _ hn,Multiset.card_bind] at hh
  apply le_trans (Nat.add_le_add_left _ _ ) hh
  calc 2*n = ∑ _i : Fin n, 2 := by simp [mul_comm]
    _ ≤ _ := by
      apply sum_le_sum
      intro i _
      obtain ⟨z,hz⟩ := hr i
      exact two_roots_card h₂ i (hs.of_dvd (Finset.dvd_prod_of_mem _ (mem_univ i))) hz

def evenWordDegree (n : ℕ) := ∏ i : Fin n, evenLength i
def evenBoundWith (method : RootPrimeBound) (n : ℕ) :=
  let D := evenWordDegree n
  let U := 2*n+1
  let V := wordBound n D U
  method.bound D V (2*(2*U)^((n*(2*n))^2)*(2*V)^(D^2))

def evenWitnessBound := evenBoundWith elementarySchur

/-- One bounded prime witnesses two disjoint upper endpoints for each
of the lengths 2,4,...,2n. -/
theorem simultaneous_even_with (method : RootPrimeBound) (n : ℕ) (hn : 0<n) :
    ∃ p ≤ evenBoundWith method n, p.Prime ∧ 2*n<p ∧
      (∏ i : Fin n, (descPochhammer (ZMod p) (2*(i.val+1))-1)).Separable ∧
      (∀ i : Fin n, ∃ z w : ZMod p, z ≠ w ∧
        (descPochhammer (ZMod p) (2*(i.val+1))-1).IsRoot z ∧
        (descPochhammer (ZMod p) (2*(i.val+1))-1).IsRoot w) ∧
      ((Ico 1 p).image (fun j => j.factorial % p)).card+2*n ≤ p-1 := by
  classical
  let G := family ℤ (lengths n)
  let U := 2*n+1
  let N := ∑ i : Fin n, evenLength i
  have he (i : Fin n) : 0<evenLength i := by dsimp [evenLength]; omega
  have hN : 0<N := Finset.sum_pos (fun i _ => he i) ⟨⟨0,hn⟩,mem_univ _⟩
  have boundN : N ≤ n*(2*n) := calc
    _ ≤ ∑ _i : Fin n, 2*n := sum_le_sum fun i _ => by dsimp [evenLength]; omega
    _ = _ := by simp
  have degree := degree_family ℤ n
  have hsep : (G.map (Int.castRingHom ℂ)).Separable := (map_family' (Int.castRingHom ℂ) n).symm ▸ family_simple n
  obtain ⟨g,hg⟩ := enumerate_roots _ (degree.monic.map _) (IsAlgClosed.splits _) hsep
    ((degree.monic.natDegree_map _).trans degree.natDegree_eq)
  have hgU (j) : ‖g j‖ ≤ U := by
    have hroot : (G.map (Int.castRingHom ℂ)).IsRoot (g j) := by
      rw [hg]; simp only [IsRoot.def,eval_prod,eval_sub,eval_X,eval_C]
      exact prod_eq_zero (mem_univ j) (sub_self _)
    change ((family ℤ (lengths n)).map _).eval (g j) = 0 at hroot
    rw [map_family',family_prod,eval_prod,Finset.prod_eq_zero_iff] at hroot
    obtain ⟨i,_,hi⟩ := hroot
    exact small_root n i hi
  have ⟨hb₁,hb₂⟩ := bad_bound G g hg U (by dsimp [U];omega) hgU
  let B := 2*(bad G).natAbs
  have good (p) [Fact (Nat.Prime p)] (hp : ¬p ∣ B) : (family (ZMod p) (lengths n)).Separable := by
    rw [← map_family' (Int.castRingHom (ZMod p))]
    exact separable_at_good_prime G (by rw [show G.natDegree=N from degree.natDegree_eq]; omega) p
      (fun e => hp (dvd_mul_of_dvd_right e _))
  have hc (i : Fin n) := enumerate_roots (gapPoly ℂ i) (degree_gap ℂ i).monic (IsAlgClosed.splits _)
    ((family_prod ℂ n ▸ family_simple n).of_dvd (Finset.dvd_prod_of_mem _ (mem_univ i))) (degree_gap ℂ i).natDegree_eq
  choose a ha using hc
  have hu (i : Fin n) j : ‖a i j‖ ≤ U := by
    apply small_root n i
    rw [ha]; simp only [IsRoot.def,eval_prod,eval_sub,eval_X,eval_C]
    exact prod_eq_zero (mem_univ j) (sub_self _)
  have hprod (i : Fin n) := (map_gap (Int.castRingHom ℂ) i).trans (ha i)
  obtain ⟨p,hp,hprime,havoid,hr⟩ := joint_prime_with method hn evenLength he (gapPoly ℤ) a hprod U B
    (by dsimp [U];omega) (by dsimp [B];omega) hu (by
      intro p _ h i
      rw [map_gap]
      exact (family_prod (ZMod p) n ▸ good p h).of_dvd (Finset.dvd_prod_of_mem _ (mem_univ i)))
  let : Fact p.Prime := ⟨hprime⟩
  simp only [map_gap] at hr
  have h₂ : (2 : ZMod p) ≠ 0 := by
    intro e
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using e)
    exact havoid (dvd_mul_of_dvd_left hd _)
  have hh := count_even_roots h₂ (good p havoid) hr
  have cardword : Fintype.card (Word (@evenLength n)) = evenWordDegree n := by
    simpa only [Fintype.card_fin,evenWordDegree] using (Fintype.card_pi (α := fun i : Fin n => Fin (evenLength i)))
  rw [cardword] at hp
  have sf := good p havoid
  rw [family_prod] at sf
  have two (i : Fin n) : ∃ z w : ZMod p, z ≠ w ∧ (gapPoly (ZMod p) i).IsRoot z ∧ (gapPoly (ZMod p) i).IsRoot w := by
    have si := sf.of_dvd (Finset.dvd_prod_of_mem _ (mem_univ i))
    obtain ⟨z,hz⟩ := hr i
    obtain ⟨hne,hy⟩ := two_even_roots h₂ (i.val+1) si hz
    exact ⟨z,_,hne,hz,hy⟩
  refine ⟨p,hp.trans ?_,hprime,by omega,sf,two,hh⟩
  apply method.mono
  dsimp only [B,U] at *
  simp only [Fintype.card_fin] at hb₂
  gcongr
  exact hb₂.trans (by gcongr; omega)

theorem simultaneous_even_prime (n : ℕ) (hn : 0<n) :
    ∃ p ≤ evenWitnessBound n, p.Prime ∧ 2*n<p ∧
      (∏ i : Fin n, (descPochhammer (ZMod p) (2*(i.val+1))-1)).Separable ∧
      (∀ i : Fin n, ∃ z w : ZMod p, z ≠ w ∧
        (descPochhammer (ZMod p) (2*(i.val+1))-1).IsRoot z ∧
        (descPochhammer (ZMod p) (2*(i.val+1))-1).IsRoot w) ∧
      ((Ico 1 p).image (fun j => j.factorial % p)).card+2*n ≤ p-1 :=
  simultaneous_even_with elementarySchur n hn

#print axioms simultaneous_even_with
#print axioms simultaneous_even_prime

end Erdos478.EffectiveResolvent
