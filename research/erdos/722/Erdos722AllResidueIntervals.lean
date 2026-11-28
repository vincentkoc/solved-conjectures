import Erdos722AdmissibleResidues
import Erdos722UnrestrictedWidths

/-!
# Intervals covering all admissible group counts

Choose a design representing every admissible residue modulo one usable
width. Repeated choices of adjacent heights translate the representatives
through a full interval in all those classes.
-/

namespace Erdos722.PairDesign
open Finset Erdos722.Quartet

private theorem width_fan {k s : ℕ} (hk : 2≤k) (H : Adjacent k s) (hs : 0<s) (B n : ℕ) :
    ∃ C, s ∣ C ∧ ∀ i≤n, ∀ x≤B, Local k x → Local k (C+s*i+x) := by
  induction n with
  | zero => exact ⟨0,dvd_zero _,by simp_all⟩
  | succ n ih =>
    obtain ⟨C,hC,h⟩ := ih
    obtain ⟨t,ht,hA,D₀,D₁⟩ := unrestricted_heights hk s (C+s*n+B) hs
    refine ⟨s*t+C,dvd_add (dvd_mul_right ..) hC,?_⟩
    intro i hi x hx hL
    by_cases hin : i≤n
    · have hr : C+s*i+x≤t := le_trans (by gcongr) ht
      have hh := grow hk D₀ H hr (show 0≤1 by decide)
        (by simpa using hA.1) (by simpa using h i hin x hx hL)
      simpa only [Nat.add_zero,Nat.add_assoc] using hh
    · have he : i=n+1 := by omega
      subst i
      have hr : C+s*n+x≤t+1 := by omega
      have hh := grow hk D₁ H hr (show 0≤1 by decide)
        (by simpa using hA.2) (by simpa using h n le_rfl x hx hL)
      convert hh using 1
      ring

theorem all_seed_interval {k s : ℕ} (hk : 2≤k) (hs : 0<s) (hks : k∣s)
    (H : Adjacent k s) (W : ℕ) :
    ∃ L ≥ W, ∀ u, L≤u → u≤L+W → Allowed k u → Local k u := by
  classical
  have hseed (r : ℕ) : ∃ x, Allowed k r → x ≡ r [MOD s] ∧ Local k x := by
    by_cases hr : Allowed k r
    · obtain ⟨x,h⟩ := residue_seed hk hs hks r hr
      exact ⟨x,fun _ => h⟩
    · exact ⟨0,fun h => (hr h).elim⟩
  choose seed seeds using hseed
  let B := (range s).sup seed
  let P := s*(B+W+1)
  have hP : B+W+1≤P := Nat.le_mul_of_pos_left _ hs
  obtain ⟨C,hC,fan⟩ := width_fan hk H hs B (P+W)
  refine ⟨C+P,by omega,?_⟩
  intro u hlo hhi ha
  let r := u%s
  have hr : r∈range s := mem_range.mpr (Nat.mod_lt _ hs)
  have hm := Nat.mod_modEq u s
  obtain ⟨hz,hL⟩ := seeds r ((allowed_congr (hm.of_dvd hks)).mpr ha)
  have hle : seed r≤B := le_sup hr
  have hres : C+seed r ≡ u [MOD s] := by
    simpa using (hC.modEq_zero_nat.add_right (seed r)).trans (by simpa using hz.trans hm)
  have hsmall : C+seed r≤u := by omega
  obtain ⟨i,hi⟩ := (Nat.modEq_iff_dvd' hsmall).mp hres
  have hEq : C+s*i+seed r=u := by omega
  have hii : i≤P+W := by have := Nat.le_mul_of_pos_left i hs; omega
  exact hEq ▸ fan i hii (seed r) hle hL

#print axioms all_seed_interval
end Erdos722.PairDesign
