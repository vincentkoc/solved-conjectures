import CunninghamProgressionReturnMass

/-! Prime-free forward windows of arbitrary fixed logarithmic length for
both canonical Cunningham orbits from the same prime seed. -/

namespace CunninghamChain.OrbitIsolation
open Finset Filter Topology Real PrimeMass

private lemma ancestor_mass_vanishes {ε : ℝ} (he : 0<ε) :
    ∀ᶠ s : ℝ in 𝓝[>] 1, (s-1)*mass {p | HasPrimeAncestor p} s < ε := by
  classical
  obtain ⟨C,cp,est⟩ := unbounded_ancestor_count
  apply eventually_mass_lt_of_sum_le _ (by positivity : 0≤ε/2) (by linarith)
  have high := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (2*C/ε+1)
  filter_upwards [est,high,eventually_ge_atTop 2] with N count large n2
  have logp : 0<log (N:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1<N))
  let V := (range N).filter fun p => p.Prime ∧ HasPrimeAncestor p
  have sub : V⊆primesWithAncestor N := by
    intro p hp
    obtain ⟨bound,pr,anc⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨(mem_range.mp bound).le,pr⟩,anc⟩
  have weightBound : ∑ p∈range N,weight {p | HasPrimeAncestor p} p ≤ ((primesWithAncestor N).card:ℝ)*log N := by
    change (∑ p∈range N, (if p.Prime ∧ HasPrimeAncestor p then log (p:ℝ) else 0)) ≤ _
    rw [←sum_filter]
    calc _ ≤ ∑ _p∈V,log (N:ℝ) := by
              apply sum_le_sum
              intro p hp
              exact Real.log_le_log (by exact_mod_cast (mem_filter.mp hp).2.1.pos)
                (by exact_mod_cast (mem_range.mp (mem_filter.mp hp).1).le)
         _ ≤ _ := by
           simp only [sum_const,nsmul_eq_mul]
           exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_le_card sub) logp.le
  apply le_of_mul_le_mul_right (a:=log (N:ℝ)) _ logp
  apply (mul_le_mul_of_nonneg_right weightBound logp.le).trans
  rw [mul_assoc,←pow_two]
  apply count.trans
  change 2*C/ε+1≤log N at large
  have small := (div_le_iff₀ he).mp (show 2*C/ε≤log N by linarith)
  calc C*N ≤ (ε/2*log N)*N := mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
       _ = _ := by ring

/-- The same progression can also exclude every prime ancestor, at any
positive depth in either recurrence. -/
theorem joint_clean_progression_mass {c ε : ℝ} (hc : 0≤c) (he : 0<ε) :
    ∃ W A : ℕ, 0<W ∧ A<W ∧ A.Coprime W ∧ ∀ᶠ s : ℝ in 𝓝[>] 1,
      (1-ε)/(W.totient:ℝ) ≤
        (s-1)*mass (isolatedClass c W A ∩ {p | ¬HasPrimeAncestor p}) s := by
  classical
  obtain ⟨W,A,wp,ap,unit,low⟩ := joint_isolation_progression_mass hc (half_pos he)
  let G := isolatedClass c W A
  let P := G ∩ {p | ¬HasPrimeAncestor p}
  have tp : 0<(W.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr wp
  have anc := ancestor_mass_vanishes (div_pos (half_pos he) tp)
  refine ⟨W,A,wp,ap,unit,?_⟩
  filter_upwards [low,anc,self_mem_nhdsWithin] with s enough cost hs
  change 1<s at hs
  have cover := mass_le_cover (∅ : Finset Unit) (fun _ => P) G P {p | HasPrimeAncestor p} (by
    intro p hp _
    by_cases h : HasPrimeAncestor p
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl ⟨hp,h⟩)) hs
  simp only [sum_empty,zero_add] at cover
  have both := mul_le_mul_of_nonneg_left cover (sub_nonneg.mpr hs.le)
  change (1-ε/2)/(W.totient:ℝ)≤(s-1)*mass G s at enough
  change (1-ε)/(W.totient:ℝ)≤(s-1)*mass P s
  rw [mul_add] at both
  simp only [div_eq_mul_inv] at enough cost ⊢
  linarith only [enough,cost,both]

/-- Each positive logarithmic radius is attained at infinitely many common
prime seeds, with primality excluded at every positive site in both orbits. -/
theorem infinitely_many_joint_logarithmic_gaps {c : ℝ} (hc : 0≤c) :
    Set.Infinite {p : ℕ | p.Prime ∧ ¬HasPrimeAncestor p ∧ ∀ j : ℕ, 0<j → (j:ℝ)≤c*log p →
      ¬(firstKindTerm p j).Prime ∧ ¬(secondKindTerm p j).Prime} := by
  obtain ⟨W,A,wp,_,_,massLow⟩ := joint_clean_progression_mass hc (by norm_num : (0:ℝ)<1/2)
  let G := isolatedClass c W A ∩ {p | ¬HasPrimeAncestor p}
  have inf : G.Infinite := by
    intro finite
    have tp : (0:ℝ)<W.totient := by exact_mod_cast Nat.totient_pos.mpr wp
    have pos : (0:ℝ)<(1-1/2)/(W.totient:ℝ) := div_pos (by norm_num) tp
    have low := (finite_mass_tendsto finite).eventually_lt_const pos
    obtain ⟨s,h,l⟩ := (massLow.and low).exists
    exact (not_lt_of_ge h) l
  apply inf.mono
  intro p hp
  obtain ⟨⟨pr,_,gap⟩,noAncestor⟩ := hp
  refine ⟨pr,noAncestor,?_⟩
  rintro (_|i) pos size
  · omega
  · exact ⟨fun first => gap ⟨true,i,size,first⟩,fun second => gap ⟨false,i,size,second⟩⟩

#print axioms joint_clean_progression_mass
#print axioms infinitely_many_joint_logarithmic_gaps

end CunninghamChain.OrbitIsolation
