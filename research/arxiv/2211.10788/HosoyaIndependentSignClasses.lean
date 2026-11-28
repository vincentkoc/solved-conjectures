import HosoyaQuadraticCharacterPairs

/-! Counting simultaneous negative signs of independent quadratic characters. -/

namespace Arxiv.«2211.10788».PrimeObstruction
open Finset

/-- Every product obtained by multiplying a by a sublist of L is a nonsquare
whose Jacobi period divides M. -/
def nonsquareProducts (M : ℕ) (a : ℤ) : List ℤ → Prop
  | [] => ¬IsSquare a ∧ 4*a.natAbs ∣ M
  | b::L => nonsquareProducts M a L ∧ nonsquareProducts M (a*b) L

/-- The nonempty subproducts are all nonsquares with Jacobi period dividing M. -/
def independentProducts (M : ℕ) : List ℤ → Prop
  | [] => True
  | a::L => nonsquareProducts M a L ∧ independentProducts M L

private def indicatorWeight {M : ℕ} (u : (ZMod M)ˣ) : List ℤ → ℤ
  | [] => 1
  | a::L => (1-unitSymbol a u)*indicatorWeight u L

private def moment {M : ℕ} [NeZero M] (a : ℤ) (L : List ℤ) : ℤ :=
  ∑ u : (ZMod M)ˣ, unitSymbol a u * indicatorWeight u L

private theorem moment_cons {M : ℕ} [NeZero M] (a b : ℤ) (L : List ℤ) :
    moment (M:=M) a (b::L) = moment (M:=M) a L - moment (M:=M) (a*b) L := by
  unfold moment
  rw [←sum_sub_distrib]
  apply sum_congr rfl
  intro u _
  rw [show unitSymbol (a*b) u=unitSymbol a u*unitSymbol b u from jacobiSym.mul_left ..]
  simp [indicatorWeight]; ring

private theorem zero_moment {M : ℕ} [NeZero M] (a : ℤ) (L : List ℤ)
    (h : nonsquareProducts M a L) : moment (M:=M) a L = 0 := by
  induction L generalizing a with
  | nil => simpa [moment,indicatorWeight] using sum_symbol_zero h.2 h.1
  | cons b L ih => rw [moment_cons,ih _ h.1,ih _ h.2,sub_zero]

private theorem full_moment {M : ℕ} [NeZero M] (L : List ℤ) (h : independentProducts M L) :
    moment (M:=M) 1 L = M.totient := by
  induction L with
  | nil => simp [moment,indicatorWeight,unitSymbol,ZMod.card_units_eq_totient]
  | cons b L ih => rw [moment_cons,one_mul,zero_moment _ _ h.1,sub_zero,ih h.2]

/-- Residues on which every symbol in the list takes the value minus one. -/
noncomputable def allNegativeClasses (M : ℕ) [NeZero M] (L : List ℤ) : Finset (ZMod M)ˣ :=
  open Classical in univ.filter fun u => ∀ a ∈ L, unitSymbol a u = -1

/-- Every joint minus pattern of k independent square classes occurs on 1/2^k of the units. -/
theorem card_all_negative {M : ℕ} [NeZero M] (L : List ℤ) (h : independentProducts M L)
    (hd : ∀ a∈L, 4*a.natAbs ∣ M) :
    2^L.length*(allNegativeClasses M L).card=M.totient := by
  classical
  have weight (u : (ZMod M)ˣ) (K : List ℤ) (hK : ∀ a∈K, 4*a.natAbs ∣ M) :
      indicatorWeight u K = if ∀ a∈K, unitSymbol a u = -1 then (2:ℤ)^K.length else 0 := by
    induction K with
    | nil => simp [indicatorWeight]
    | cons a K ih =>
      rw [indicatorWeight,ih (fun b hb => hK b (List.mem_cons_of_mem _ hb))]
      rcases symbol_sign (hK a (by simp)) u with hs|hs
      · simp [hs]
      · by_cases ht : ∀ b∈K, unitSymbol b u = -1 <;> simp [hs,ht,pow_succ,mul_comm]
  have e := full_moment L h
  simp only [moment,unitSymbol,jacobiSym.one_left,one_mul] at e
  simp_rw [weight _ L hd] at e
  rw [←Finset.sum_filter] at e
  have hh : (2:ℤ)^L.length*(allNegativeClasses M L).card = M.totient := by
    simpa [allNegativeClasses,mul_comm] using e
  exact_mod_cast hh

#print axioms card_all_negative

end Arxiv.«2211.10788».PrimeObstruction
