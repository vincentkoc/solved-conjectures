import research.arxiv.«1104.1579».CunninghamPrimeDirichletMass

/-! # Prime Dirichlet mass for finite squarefree sieves -/

namespace CunninghamChain.SquarefreeDensity
open Finset Filter Topology PrimeMass

/-- Normalized logarithmic Dirichlet mass of prime seeds as the real exponent
approaches one from above. -/
def HasPrimeMass (S : Set ℕ) (c : ℝ) : Prop :=
  Tendsto (fun s : ℝ => (s-1)*mass S s) (𝓝[>] 1) (𝓝 c)

private theorem mass_residues {m : ℕ} [NeZero m] (A : Finset (ZMod m))
    (hu : ∀ a ∈ A, IsUnit a) :
    HasPrimeMass {n : ℕ | (n : ZMod m) ∈ A} ((A.card : ℝ)/(m.totient : ℝ)) := by
  classical
  let S (a : ZMod m) := {n : ℕ | (n : ZMod m) = a}
  have lim := tendsto_finsetSum A (fun a ha => mass_progression a (hu a ha))
  have he {s : ℝ} (hs : 1<s) :
      mass {n : ℕ | (n : ZMod m) ∈ A} s = ∑ a ∈ A, mass (S a) s := by
    unfold mass
    rw [←Summable.tsum_finsetSum (fun a (_ : a∈A) => summable_weight (S a) hs)]
    apply tsum_congr
    intro n
    rw [←sum_div]
    congr 1
    by_cases hp : n.Prime
    · simp only [weight,S,hp,true_and,Set.mem_ofPred_eq]
      by_cases hn : (n : ZMod m) ∈ A <;> simp [hn,eq_comm (a := (n : ZMod m))]
    · simp [weight,hp]
  unfold HasPrimeMass
  convert lim.congr' (f₂ := fun s : ℝ => (s-1)*mass {n : ℕ | (n : ZMod m) ∈ A} s) ?_ using 1
  · simp [div_eq_mul_inv]
  · filter_upwards [self_mem_nhdsWithin] with s hs
    rw [he hs,mul_sum]

/-- The prime mass of simultaneous reduced residue restrictions factors over
any finite collection of pairwise coprime positive moduli. -/
theorem finite_crt_mass {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (hpos : ∀ i, 0 < m i) (hcop : Pairwise fun i j => (m i).Coprime (m j))
    (A : ∀ i, Finset (ZMod (m i))) (hunit : ∀ i a, a ∈ A i → IsUnit a) :
    HasPrimeMass {n : ℕ | ∀ i, (n : ZMod (m i)) ∈ A i}
      (∏ i, ((A i).card : ℝ)/(m i).totient) := by
  classical
  let e := ZMod.prodEquivPi m hcop
  let B := (Fintype.piFinset A).map e.symm.toEquiv.toEmbedding
  have hB (x : ZMod (∏ i, m i)) : x ∈ B ↔ ∀ i, e x i ∈ A i := by
    change x ∈ (Fintype.piFinset A).map e.symm.toEquiv.toEmbedding ↔ _
    rw [mem_map_equiv,Fintype.mem_piFinset]
    rfl
  let : NeZero (∏ i, m i) := .of_pos (prod_pos (fun i _ => hpos i))
  have h := mass_residues B (fun x hx => by
    have hu : IsUnit (e.symm (e x)) :=
      (Pi.isUnit_iff.mpr fun i => hunit i _ ((hB x).mp hx i)).map e.symm.toMonoidHom
    simpa using hu)
  have hset : {n : ℕ | (n : ZMod (∏ i, m i)) ∈ B} =
      {n : ℕ | ∀ i, (n : ZMod (m i)) ∈ A i} := by
    ext n
    simp [hB,e]
  rw [hset] at h
  have htot (t : Finset ι) : (∏ i ∈ t, m i).totient = ∏ i ∈ t, (m i).totient := by
    induction t using Finset.induction_on with
    | empty => simp
    | insert a t ha ih =>
      rw [prod_insert ha,prod_insert ha,Nat.totient_mul,ih]
      exact Nat.Coprime.prod_right (fun i hi => hcop (fun h => ha (h ▸ hi)))
  simpa [B,htot,prod_div_distrib] using h

#print axioms finite_crt_mass

end CunninghamChain.SquarefreeDensity
