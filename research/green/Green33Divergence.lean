import Green33Multiplicity
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic

open Filter Finset
open scoped Pointwise Topology

namespace Green33Multiplicity

/-- The largest ordered sum fiber in the cyclic group. -/
def maxReps {q : ℕ+} (A : Finset (ZMod q)) : ℕ :=
  univ.sup (reps A)

/-- On any family of cyclic two-bases of limiting density √2, the largest
ordered representation count eventually exceeds each fixed bound. -/
theorem tendsto_maxReps_atTop {ι : Type*} {l : Filter ι} (q : ι → ℕ+)
    (A : (i : ι) → Finset (ZMod (q i)))
    (hq : Tendsto (fun i => (q i : ℕ)) l atTop)
    (hA : ∀ i, A i + A i = univ)
    (hd : Tendsto (fun i => ((A i).card : ℝ) / Real.sqrt (q i)) l (𝓝 (Real.sqrt 2))) :
    Tendsto (fun i => maxReps (A i)) l atTop := by
  let x (i : ι) : ℝ := (A i).card / Real.sqrt (q i)
  have hs := Real.tendsto_sqrt_atTop.comp ((tendsto_natCast_atTop_atTop (R := ℝ)).comp hq)
  have hx : Tendsto x l (𝓝 (Real.sqrt 2)) := hd
  have hlin : Tendsto (fun i => x i / Real.sqrt (q i)) l (𝓝 0) :=
    hx.div_atTop hs
  refine tendsto_atTop.2 fun m => ?_
  -- For a fixed cap the normalized right-hand side tends to 2m, whereas
  -- the finite bound requires it to be at least 2m + 2.
  have hlim : Tendsto
      (fun i => (m : ℝ) * x i ^ 2 + (m + 8) * (x i / Real.sqrt (q i))) l
      (𝓝 (2 * (m : ℝ))) := by
    convert ((tendsto_const_nhds (x := (m : ℝ))).mul (hx.pow 2)).add
      ((tendsto_const_nhds (x := (m : ℝ) + 8)).mul hlin) using 1
    congr 1
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  filter_upwards [hlim.eventually_lt_const (show 2 * (m : ℝ) < 2 * m + 2 by linarith)] with i hi
  by_contra! hsmall
  have hcap (s : ZMod (q i)) : reps (A i) s ≤ m + 4 :=
    (Finset.le_sup (f := reps (A i)) (mem_univ s)).trans (by change maxReps (A i) ≤ m + 4; omega)
  have hfin := multiplicity_bound (q i) (A i) (hA i) m hcap
  have hreal : (2 * (m : ℝ) + 2) * (q i : ℝ) + 6 ≤
      m * ((A i).card : ℝ) ^ 2 + (m + 8) * (A i).card := by exact_mod_cast hfin
  have hpos : 0 < (q i : ℝ) := by exact_mod_cast (q i).pos
  have hroot := Real.sqrt_pos.2 hpos
  dsimp only [x] at hi
  field_simp [ne_of_gt hroot] at hi
  rw [Real.sq_sqrt hpos.le] at hi
  linarith

#print axioms tendsto_maxReps_atTop

end Green33Multiplicity
