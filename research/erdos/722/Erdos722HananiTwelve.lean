import Erdos722StemInflation
import Erdos722HananiTemplates
import Erdos722QuadrupleProduct
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Hanani's twelvefold construction for Steiner quadruple systems

Three twelve-point columns and two shared points form a 38-point local
system. Its three common 14-point subdesigns furnish the two-stem gluing.
-/

namespace Erdos722.HananiTwelve
open Finset QuadCompletion StemInflation

private def pull {A B : Type*} (R : Rule B) (e : A ≃ B) : Rule A where
  complete a b c := e.symm (R.complete (e a) (e b) (e c))
  swap₁ a b c := congrArg e.symm (R.swap₁ _ _ _)
  swap₂ a b c := congrArg e.symm (R.swap₂ _ _ _)
  repeated a b := by simp [R.repeated]
  cancel a b c := by simp [R.cancel]

private def smallLabel : Fin 2 ⊕ Fin 12 ≃ Fin 14 :=
  (Equiv.sumComm _ _).trans finSumFinEquiv
private def largeLabel : Lift (Fin 3) (Fin 12) ≃ Fin 38 :=
  (Equiv.sumComm _ _).trans ((Equiv.sumCongr finProdFinEquiv (Equiv.refl _)).trans finSumFinEquiv)

private def coordinate (i : Fin 3) (x : Fin 14) : Fin 38 :=
  largeLabel (column i (smallLabel.symm x))

private theorem inflate {n : ℕ} (hn : 3 ≤ n) {H : Finset (Finset (Fin n))}
    (hH : H.IsBlockDesign 3 4) (F : Rule (Fin 14)) (G : Rule (Fin 38))
    (hcomp : ∀ i a b c, coordinate i (F.complete a b c) =
      G.complete (coordinate i a) (coordinate i b) (coordinate i c)) :
    ∃ D : Finset (Finset (Fin (12*n-10))), D.IsBlockDesign 3 4 := by
  classical
  let I := Fin (n-1)
  have hcard : Fintype.card (Option I) = n := by simp [I]; omega
  let e := (Fintype.equivFinOfCardEq hcard).symm
  let S := pull F smallLabel
  let L := pull G largeLabel
  have hcol (i : Fin 3) : ∀ D ∈ S.blocks, D.map (column i) ∈ L.blocks := by
    intro D hD
    apply S.map_block L (column i) _ hD
    intro a b c
    apply largeLabel.injective
    change coordinate i (F.complete (smallLabel a) (smallLabel b) (smallLabel c)) =
      largeLabel (largeLabel.symm _)
    simpa [coordinate] using hcomp i (smallLabel a) (smallLabel b) (smallLabel c)
  obtain ⟨D,hD⟩ := exists_pointed S.isBlockDesign L.isBlockDesign hcol
    (relabel hH e) (by rwa [hcard])
  have hnew : Fintype.card (Lift I (Fin 12)) = 12*n-10 := by simp [Lift,I]; omega
  exact ⟨_,relabel hD (Fintype.equivFinOfCardEq hnew)⟩

/-- Closure of the binary and ternary projective-line orders under
products and the pointed tripling construction. -/
inductive ProductTriplingOrder : ℕ → Prop where
  | binary (d : ℕ) : ProductTriplingOrder (2^d)
  | ternary (d : ℕ) : ProductTriplingOrder (3^d+1)
  | product {a b} : ProductTriplingOrder a → ProductTriplingOrder b → ProductTriplingOrder (a*b)
  | tripling {a} : ProductTriplingOrder a → ProductTriplingOrder (3*a-2)

private theorem old_moduli {n : ℕ} (h : ProductTriplingOrder n) :
    n=1 ∨ 2∣n ∧ (n=2 ∨ 4∣n ∨ n%3=1) := by
  induction h with
  | binary d =>
    rcases d with _|d
    · simp
    rcases d with _|d
    · decide
    have h4 : 4 ∣ 2^(d+2) := ⟨2^d,by ring⟩
    exact Or.inr ⟨dvd_trans (by decide : 2∣4) h4,Or.inr (Or.inl h4)⟩
  | ternary d =>
    rcases d with _|d
    · decide
    have ho : Odd (3^(d+1) : ℕ) := (by decide : Odd (3:ℕ)).pow
    obtain ⟨k,hk⟩ := ho
    exact Or.inr ⟨by omega,Or.inr (Or.inr (by rw [pow_succ]; omega))⟩
  | product ha hb ia ib =>
    have ia' := ia
    rcases ia with ha1|⟨ha₂,_⟩
    · simpa [ha1] using ib
    rcases ib with hb1|⟨hb₂,_⟩
    · simpa [hb1] using ia'
    have h4 := Nat.mul_dvd_mul ha₂ hb₂
    exact Or.inr ⟨dvd_trans (by decide : 2∣4) h4,Or.inr (Or.inl h4)⟩
  | @tripling a h ih =>
    rcases ih with h1|⟨h2,_⟩
    · simp [h1]
    by_cases hz : a = 0
    · simp [hz]
    exact Or.inr ⟨by omega,Or.inr (Or.inr (by omega))⟩

theorem new_order {n : ℕ} (hn : 2 ≤ n) : ¬ProductTriplingOrder (12*n-10) := by
  intro h
  rcases old_moduli h with h|⟨_,h|h|h⟩ <;> omega

private theorem recurse_spectrum (P : ℕ → Prop) (p2 : P 2) (p4 : P 4) (p14 : P 14) (p38 : P 38)
    (double : ∀ m, P m → P (2*m))
    (triple : ∀ m ≥ 4, P m → P (3*m-2))
    (eight : ∀ m ≥ 4, m%12=2 → P m → P (3*m-8))
    (four : ∀ m ≥ 4, m%12=10 → P m → P (3*m-4))
    (six : ∀ m ≥ 4, (m%6=2 ∨ m%6=4) → P m → P (4*m-6))
    (twelve : ∀ m ≥ 4, P m → P (12*m-10)) :
    ∀ n, n%6=2 ∨ n%6=4 → P n := by
  have classes : ∀ r : Fin 72, r.val%6=2 ∨ r.val%6=4 →
      r.val%12=4 ∨ r.val%12=8 ∨ r.val%18=4 ∨ r.val%18=10 ∨
      r.val%36=34 ∨ r.val%36=26 ∨ r.val%24=2 ∨ r.val%24=10 ∨ r.val=14 ∨ r.val=38 := by
    decide +kernel
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro ha
    by_cases h2 : n=2
    · simpa [h2] using p2
    by_cases h4 : n=4
    · simpa [h4] using p4
    by_cases h14 : n=14
    · simpa [h14] using p14
    by_cases h38 : n=38
    · simpa [h38] using p38
    let r : Fin 72 := ⟨n%72,Nat.mod_lt _ (by decide)⟩
    have eqm (d : ℕ) (hd : d ∣ 72) : r.val%d=n%d := Nat.mod_mod_of_dvd n hd
    have hc := classes r (by rwa [eqm 6 (by decide)])
    rw [eqm 12 (by decide),eqm 18 (by decide),eqm 36 (by decide),eqm 24 (by decide)] at hc
    change _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ n%72=14 ∨ n%72=38 at hc
    have step (v u : ℕ) (hs : P v → P u) (hv : v<n)
        (ha' : v%6=2 ∨ v%6=4) (he : u=n) : P n := he ▸ hs (ih v hv ha')
    rcases hc with h|h|h|h|h|h|h|h|h|h
    · apply step _ _ (double (6*(n/12)+2)) <;> omega
    · apply step _ _ (double (6*(n/12)+4)) <;> omega
    · apply step _ _ (triple (6*(n/18)+2) (by omega)) <;> omega
    · apply step _ _ (triple (6*(n/18)+4) (by omega)) <;> omega
    · apply step _ _ (eight (12*(n/36)+14) (by omega) (by omega)) <;> omega
    · apply step _ _ (four (12*(n/36)+10) (by omega) (by omega)) <;> omega
    · apply step _ _ (six (6*(n/24)+2) (by omega) (by omega)) <;> omega
    · apply step _ _ (six (6*(n/24)+4) (by omega) (by omega)) <;> omega
    · apply step _ _ (twelve (6*(n/72)+2) (by omega)) <;> omega
    · apply step _ _ (twelve (6*(n/72)+4) (by omega)) <;> omega

/-- A Steiner quadruple system on the canonical finite vertex type. -/
abbrev HasSQS (n : ℕ) := ∃ H : Finset (Finset (Fin n)), H.IsBlockDesign 3 4

/-- Hanani's construction with two shared points and twelve new points for
each ordinary base point. -/
theorem exists_twelvefold {n : ℕ} (hn : 3 ≤ n) {H : Finset (Finset (Fin n))}
    (hH : H.IsBlockDesign 3 4) : HasSQS (12*n-10) := by
  apply inflate hn hH HananiTemplate.fourteen HananiTemplate.thirtyEight
  have he : ∀ (i : Fin 3) (x : Fin 14), coordinate i x = HananiTemplate.embed i x := by
    decide +kernel
  simpa only [he] using HananiTemplate.embed_completion

/-- The resulting infinite family starts at orders 38, 86 and 182. -/
theorem exists_twelve_binary (d : ℕ) : HasSQS (12 * 2^(d+2)-10) := by
  obtain ⟨D,hD⟩ := Erdos722.exists_binary_quadruple_design (d+2)
  have hp : 0 < (2:ℕ)^d := pow_pos (by decide) d
  exact exists_twelvefold (by rw [pow_add]; omega) hD

/-- Hanani's spectrum reduces to the three indicated construction steps.
Doubling, tripling and the twelvefold step are discharged here. -/
theorem spectrum_of_three_constructions
    (eight : ∀ m ≥ 4, m%12=2 → HasSQS m → HasSQS (3*m-8))
    (four : ∀ m ≥ 4, m%12=10 → HasSQS m → HasSQS (3*m-4))
    (six : ∀ m ≥ 4, (m%6=2 ∨ m%6=4) → HasSQS m → HasSQS (4*m-6)) :
    ∀ n, n%6=2 ∨ n%6=4 → HasSQS n := by
  have base₂ : HasSQS 2 := Erdos722.exists_binary_quadruple_design 1
  apply recurse_spectrum HasSQS base₂ (Erdos722.exists_binary_quadruple_design 2)
    ⟨_,HananiTemplate.fourteen.isBlockDesign⟩ ⟨_,HananiTemplate.thirtyEight.isBlockDesign⟩
  · rintro m ⟨D,hD⟩
    obtain ⟨B,hB⟩ := base₂
    exact QuadrupleProduct.exists_product hB hD
  · rintro m hm ⟨D,hD⟩
    exact Tripling.exists_tripling (by omega) hD
  · exact eight
  · exact four
  · exact six
  · rintro m hm ⟨D,hD⟩
    exact exists_twelvefold (by omega) hD

/-- The binomial hypotheses in the pinned question force the residue
classes used in the spectrum recursion. -/
theorem residues_of_divisibility {n : ℕ} (hn : 4 ≤ n)
    (H : ∀ i < 3, (4-i).choose (3-i) ∣ (n-i).choose (3-i)) : n%6=2 ∨ n%6=4 := by
  have h2 : 2 ∣ n-2 := by simpa using H 2 (by decide)
  have h3 : 3 ∣ (n-1).choose 2 := by simpa using H 1 (by decide)
  rw [Nat.choose_two_right] at h3
  have he := (n-1).even_mul_pred_self.two_dvd
  have hm : (n-1)*(n-1-1)%3=0 := by omega
  by_contra h
  have h0 : n%6=0 := by omega
  rw [Nat.mul_mod,show (n-1)%3=2 by omega,show (n-1-1)%3=1 by omega] at hm
  contradiction

#print axioms exists_twelvefold
#print axioms exists_twelve_binary
#print axioms new_order
#print axioms spectrum_of_three_constructions
#print axioms residues_of_divisibility

end Erdos722.HananiTwelve
