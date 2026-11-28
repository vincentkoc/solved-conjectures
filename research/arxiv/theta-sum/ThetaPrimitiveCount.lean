import ThetaConductorMoment

/-! Counting characters of deficient conductor by the primes removed from the level. -/
namespace Arxiv.«2501.03234».ThetaPrimitiveCount
open Finset DirichletCharacter
noncomputable section
def defect (q : ℕ) : ℝ := ∑ p∈q.primeFactors,1/((p:ℝ)-1)
def deficient (q : ℕ) : Finset (DirichletCharacter ℂ q) := by classical exact univ.filter (fun χ => ¬χ.IsPrimitive)

private def lifts (q p : ℕ) : Finset (DirichletCharacter ℂ q) := by
  classical
  exact if h : q/p ∣ q then univ.image (changeLevel (R:=ℂ) h) else ∅

private theorem contained {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : ¬χ.IsPrimitive) :
    ∃ p∈q.primeFactors,χ∈lifts q p := by
  classical
  let : DecidableEq (DirichletCharacter ℂ q) := Classical.decEq _
  obtain ⟨k,hk⟩ := χ.conductor_dvd_level
  have hk1 : k≠1 := by rintro rfl; apply hχ; change χ.conductor=q; simpa using hk.symm
  obtain ⟨p,hp,hpk⟩ := Nat.exists_prime_and_dvd hk1
  obtain ⟨a,ha⟩ := hpk
  have he : q=(χ.conductor*a)*p := by exact hk.trans (by rw [ha]; ring)
  have hd : q/p=χ.conductor*a := (congrArg (·/p) he).trans (Nat.mul_div_cancel _ hp.pos)
  have hpq : p∣q := he ▸ dvd_mul_left p _
  have h₁ : χ.conductor∣q/p := hd ▸ dvd_mul_right _ _
  have h₂ : q/p∣q := Nat.div_dvd_of_dvd hpq
  refine ⟨p,Nat.mem_primeFactors.mpr ⟨hp,hpq,NeZero.ne q⟩,?_⟩
  rw [lifts,dif_pos h₂]
  refine mem_image.mpr ⟨changeLevel h₁ χ.primitiveCharacter,mem_univ _,?_⟩
  rw [←changeLevel_trans,changeLevel_primitiveCharacter]

theorem count {q : ℕ} [NeZero q] :
    ((deficient q).card:ℝ) ≤ q.totient * defect q := by
  classical
  let : DecidableEq (DirichletCharacter ℂ q) := Classical.decEq _
  have hsub : deficient q ⊆ q.primeFactors.biUnion (lifts q) := by
    intro χ hχ
    exact mem_biUnion.mpr (contained χ (mem_filter.mp hχ).2)
  have hc := (card_le_card hsub).trans card_biUnion_le
  calc _ ≤ ∑ p∈q.primeFactors,((lifts q p).card:ℝ) := by exact_mod_cast hc
       _ ≤ ∑ p∈q.primeFactors,(q.totient:ℝ)/((p:ℝ)-1) := by
             apply sum_le_sum
             intro p hp
             have hh := Nat.prime_of_mem_primeFactors hp
             have hd := Nat.dvd_of_mem_primeFactors hp
             let : NeZero (q/p) := ⟨(Nat.div_pos (Nat.le_of_dvd (NeZero.pos q) hd) hh.pos).ne'⟩
             have hdiv := Nat.div_mul_cancel hd
             have htot := Nat.totient_super_multiplicative (q/p) p
             rw [hdiv,Nat.totient_prime hh] at htot
             have hsmall : (lifts q p).card≤(q/p).totient := by
               rw [lifts,dif_pos (Nat.div_dvd_of_dvd hd)]
               apply card_image_le.trans
               rw [card_univ,←Nat.card_eq_fintype_card,card_eq_totient_of_hasEnoughRootsOfUnity ℂ]
             have h2 : (2:ℝ)≤p := by exact_mod_cast hh.two_le
             apply (show ((lifts q p).card:ℝ)≤(q/p).totient by exact_mod_cast hsmall).trans
             apply (le_div_iff₀ (by linarith)).mpr
             have H : ((q/p).totient:ℝ)*((p-1:ℕ):ℝ)≤q.totient := by exact_mod_cast htot
             rwa [Nat.cast_sub hh.one_le,Nat.cast_one] at H
       _ = _ := by simp only [defect,mul_sum,mul_one_div]

#print axioms count
end
end Arxiv.«2501.03234».ThetaPrimitiveCount
