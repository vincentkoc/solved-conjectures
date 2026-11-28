import ThetaRecurringPrimePattern

/-! The fixed gaps with a common theta asymptotic are unbounded. -/
namespace Arxiv.«2501.03234».ThetaUnboundedPrimeGaps
open Finset Filter Real ThetaRecurringPrimePattern ThetaConsecutiveClusters ThetaMaynardClusters
noncomputable section
open scoped Topology

/-- A sufficiently long finite set of prime translates straddles a block
of composite integers created by a multiple of (G+2)!. -/
theorem large_gap {T : Finset ℕ} {n G : ℕ} (hs : (G+2).factorial+G+4≤T.card)
    (hp : ∀ j∈T,(n+j).Prime) :
    ∃ u∈T, ∃ v∈T, u+G<v ∧ ∀ j∈T,u<j → j<v → False := by
  classical
  let F := (G+2).factorial
  have hF : 0<F := Nat.factorial_pos _
  have hT : T.Nonempty := card_pos.mp (by omega)
  let a := T.min' hT
  let b := T.max' hT
  have ha : a∈T := min'_mem ..
  have hb : b∈T := max'_mem ..
  have hspan : T.card≤b+1-a := (card_le_card (show T⊆Icc a b from fun j hj =>
    mem_Icc.mpr ⟨min'_le T j hj,le_max' T j hj⟩)).trans_eq (Nat.card_Icc a b)
  let B := F*((n+a)/F+1)
  have hlow : n+a<B ∧ B≤n+a+F := by
    have h := Nat.mod_add_div (n+a) F
    have h' := Nat.mod_lt (n+a) hF
    dsimp only [B]
    rw [Nat.mul_add,Nat.mul_one]
    omega
  have hlen : F+G+4≤T.card := hs
  have hB : 0<B := by omega
  have hend : B+G+2<n+b := by omega
  have composite {i : ℕ} (hl : 2 ≤ i) (hh : i≤G+2) : ¬(B+i).Prime := by
    intro hpr
    have hf : i∣F := Nat.dvd_factorial (by omega) hh
    have hd : i∣B+i := dvd_add (hf.trans (dvd_mul_right ..)) (dvd_refl _)
    rcases (Nat.dvd_prime hpr).mp hd with h|h <;> omega
  let L := T.filter (fun j => n+j≤B+1)
  let R := T.filter (fun j => B+1<n+j)
  have hL : L.Nonempty := ⟨a,mem_filter.mpr ⟨ha,by omega⟩⟩
  have hR : R.Nonempty := ⟨b,mem_filter.mpr ⟨hb,by omega⟩⟩
  let u := L.max' hL
  let v := R.min' hR
  obtain ⟨hu,huB⟩ := mem_filter.mp (show u∈L from max'_mem ..)
  obtain ⟨hv,hvB⟩ := mem_filter.mp (show v∈R from min'_mem ..)
  change n+u≤B+1 at huB
  change B+1<n+v at hvB
  have hv' : B+G+2<n+v := by
    by_contra! h
    let j := n+v-B
    have hj : B+j=n+v := by dsimp [j];omega
    exact composite (i:=j) (by dsimp [j];omega) (by dsimp [j];omega) (by rw [hj]; exact hp v hv)
  refine ⟨u,hu,v,hv,by omega,?_⟩
  intro j hj huj hjv
  rcases le_or_gt (n+j) (B+1) with hl|hr
  · exact huj.not_ge (le_max' L j (mem_filter.mpr ⟨hj,hl⟩))
  · exact hjv.not_ge (min'_le R j (mem_filter.mpr ⟨hj,hr⟩))

/-- Unboundedly many fixed consecutive prime gaps recur in the one class
modulo eight with simultaneous asymptotic theta values at both endpoints. -/
theorem unbounded (H : ∀ m : ℕ, ∃ k : ℕ, ∃ A : ℝ, 0<A ∧ Sieve m k A) :
    ∀ G : ℕ, ∃ g : ℕ, G<g ∧ 8∣g ∧ Realized g := by
  intro G
  let m := (G+2).factorial+G+4
  obtain ⟨k,A,hA,hS⟩ := H m
  obtain ⟨T,hT,hm,n,hn,hpat,hlim⟩ := common_limit hA hS
  have hpr (j : ℕ) (hj : j∈T) : (n 0+j).Prime := by
    exact (mem_pattern.mp (show j∈pattern (diameter k) (n 0) by rw [(hpat 0).1];exact hj)).2
  obtain ⟨u,hu,v,hv,huv,adj⟩ := large_gap (n:=n 0) (G:=G) hm hpr
  exact ⟨v-u,by omega,gap_of_pair (mem_powerset.mp hT) hu hv (by omega) adj hn hpat hlim⟩

#print axioms unbounded
#print axioms large_gap
end
end Arxiv.«2501.03234».ThetaUnboundedPrimeGaps
