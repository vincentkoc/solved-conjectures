import CunninghamBatemanHorn

/-! Local means for opposite-kind Cunningham prefixes at a variable gap. -/

namespace CunninghamChain.GapMean

open Finset
open BatemanHornConjecture

/-- The number of residues at which a translate of the second set meets the first. -/
def pairCount {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (A B : Finset G) (h : G) : ℕ := (A.filter fun x => x+h∈B).card

/-- Over a full period every ordered pair contributes at its unique difference. -/
theorem sum_pairCount {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] (A B : Finset G) :
    ∑ h : G, pairCount A B h = A.card * B.card := by
  classical
  simp only [pairCount,card_filter]
  rw [sum_comm]
  have shift (x : G) : (∑ h : G, if x+h∈B then 1 else 0) = B.card := by
    calc
      _ = ∑ y : G, if y∈B then 1 else 0 :=
        Equiv.sum_comp (Equiv.addLeft x) (fun y => if y∈B then (1:ℕ) else 0)
      _ = _ := by simp
  simp [shift]

/-- The affine form at a single site, written with the canonical leading coefficient. -/
noncomputable def form (s : ℤ) (i : ℕ) : Polynomial ℤ :=
  Polynomial.C ((2:ℤ)^i)*Polynomial.X + Polynomial.C (s*((2:ℤ)^i-1))

theorem chainForms_count (s : ℤ) (k : ℕ) : (chainForms s k).card = k := by
  have lc (i : ℕ) : (form s i).leadingCoeff=(2:ℤ)^i := Polynomial.leadingCoeff_linear (by positivity)
  have inj : Function.Injective (form s) := by
    intro i j eq
    have e := congrArg Polynomial.leadingCoeff eq
    rw [lc,lc] at e
    exact (pow_right_injective₀ (by norm_num : (0:ℤ)<2) (by norm_num)) e
  change ((range k).image (form s)).card=k
  simp [card_image_of_injective _ inj]

#print axioms chainForms_count

/-- Residues at which every form in a single prefix avoids zero. -/
noncomputable def accepted (s : ℤ) (k q : ℕ) [NeZero q] : Finset (ZMod q) := by
  classical
  exact univ.filter fun x => ∀ f∈chainForms s k, (f.map (Int.castRingHom (ZMod q))).eval x ≠ 0

theorem accepted_card (s : ℤ) (k q : ℕ) [NeZero q] :
    (accepted s k q).card + OmegaP (chainForms s k) q = q := by
  classical
  let A := accepted s k q
  have roots : {z : ZMod q | ∃ f∈chainForms s k, (f.map (Int.castRingHom (ZMod q))).eval z=0} =
      ↑(Aᶜ : Finset (ZMod q)) := by ext x; simp [A,accepted]
  rw [OmegaP,roots,Set.ncard_coe_finset]
  exact (Finset.card_add_card_compl A).trans (ZMod.card q)

/-- The local factor for k plus forms and l translated minus forms. -/
noncomputable def pairFactor (k l q : ℕ) [NeZero q] (h : ZMod q) : ℝ :=
  (1-1/(q:ℝ))^(-((k+l:ℕ):ℤ)) *
    ((pairCount (accepted 1 k q) (accepted (-1) l q) h:ℝ)/q)

noncomputable def singleFactor (k q : ℕ) : ℝ :=
  (1-1/(q:ℝ))^(-(k:ℤ)) * (1-(OmegaP (chainForms 1 k) q:ℝ)/q)

/-- Averaging across the gap separates the local factors at every prime,
including 2 and the primes at which the combined forms can occupy all residues. -/
theorem mean_pairFactor (k l q : ℕ) [Fact q.Prime] :
    (∑ h : ZMod q, pairFactor k l q h) / q = singleFactor k q * singleFactor l q := by
  classical
  have hp : q.Prime := Fact.out
  have pos : 1<(q:ℝ) := by exact_mod_cast hp.one_lt
  have nz : (1-1/(q:ℝ))≠0 := (sub_pos.mpr ((div_lt_one (by linarith)).mpr pos)).ne'
  have ca := accepted_card 1 k q
  have cb := accepted_card (-1) l q
  rw [←chainForms_omega_neg 1] at cb
  have sum := sum_pairCount (accepted 1 k q) (accepted (-1) l q)
  unfold pairFactor singleFactor
  rw [← Finset.mul_sum,← Finset.sum_div,←Nat.cast_sum,sum,Nat.cast_mul,
    Nat.cast_add,neg_add,zpow_add₀ nz]
  have ra : ((accepted 1 k q).card:ℝ)+(OmegaP (chainForms 1 k) q:ℝ)=q := by exact_mod_cast ca
  have rb : ((accepted (-1) l q).card:ℝ)+(OmegaP (chainForms 1 l) q:ℝ)=q := by exact_mod_cast cb
  field_simp
  rw [show ((accepted 1 k q).card:ℝ)=q-OmegaP (chainForms 1 k) q by linarith,
    show ((accepted (-1) l q).card:ℝ)=q-OmegaP (chainForms 1 l) q by linarith]

#print axioms sum_pairCount
#print axioms accepted_card
#print axioms mean_pairFactor

end CunninghamChain.GapMean
