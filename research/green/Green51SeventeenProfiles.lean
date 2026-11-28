import Green51TwelveCodes

/-! # Weight distributions of length-seventeen relation codes -/

open Finset Green50Downsets Green50Sharp Green51WeightTransform Green51ShortenedProfiles
open Green51ElevenDimensions
open scoped Classical

namespace Green51SeventeenProfiles
local notation "F" => ZMod 2
private abbrev weights : Finset ℕ := {0,8,10,12,16}
/-- Count dual words whose weights lie in a prescribed set. -/
noncomputable def dualCount (C : Submodule F (Cube 17)) (S : Finset ℕ) :=
  ((dualWords C).filter fun z => (supp z).card ∈ S).card

private theorem inactive_of_sixteen (C : Submodule F (Cube 17))
    (four : ∀ c : C, 4 ∣ (supp c.val).card) (x : C) (size : (supp x.val).card = 16) :
    0 < dualCount C {1} := by
  classical
  let I : Cube 17 := fun _ => 1
  let w := I+x.val
  have comp : supp w = (supp x.val)ᶜ := by
    ext i
    rcases (show ∀ a:F,a=0 ∨ a=1 from by decide) (x.val i) with h|h <;>
      simp [w,I,supp,h,show (1:F)+1=0 by decide]
  have weight : (supp w).card = 1 := by rw [comp,card_compl,Fintype.card_fin,size]
  apply card_pos.mpr
  refine ⟨w,mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,?_⟩,by simp [weight]⟩⟩
  intro y
  have parity : dotProduct I y.val = 0 := by
    have term (i : Fin 17) : I i * y.val i = if i ∈ supp y.val then 1 else 0 := by
      rcases (show ∀ a:F,a=0 ∨ a=1 from by decide) (y.val i) with h|h <;> simp [I,supp,h]
    simp only [dotProduct,term,sum_boole,filter_mem_eq_inter,univ_inter]
    exact (ZMod.natCast_eq_zero_iff ..).mpr (dvd_trans (by decide : 2∣4) (four y))
  have orth : dotProduct x.val y.val = 0 := by
    apply (Green51ShortenedColumns.weight_mod_four x.val y.val (four y)).mp
    change (supp (x+y).val).card % 4 = (supp x.val).card % 4
    rw [Nat.mod_eq_zero_of_dvd (four _),Nat.mod_eq_zero_of_dvd (four _)]
  change dotProduct (I+x.val) y.val = 0
  rw [add_dotProduct,parity,orth,add_zero]

set_option maxHeartbeats 2200000 in
private theorem distribution (C : Submodule F (Cube 17))
    (size : Module.finrank F C = 5) (allowed : ∀ c : C, (supp c.val).card ∈ weights)
    (unique : Green51ShortenedProfiles.multiplicity C 16 ≤ 1)
    (coloop : Green51ShortenedProfiles.multiplicity C 10 = 0 → 0 < Green51ShortenedProfiles.multiplicity C 16 → 0 < dualCount C {1}) :
    (Green51ShortenedProfiles.multiplicity C 8,Green51ShortenedProfiles.multiplicity C 10,Green51ShortenedProfiles.multiplicity C 12,Green51ShortenedProfiles.multiplicity C 16,
      dualCount C {1},dualCount C {2},dualCount C {3},dualCount C {3,7,11,15}) ∈
      ({(22,8,0,1,0,1,7,960),(25,0,6,0,0,1,15,896),(30,0,0,1,1,0,0,896)} :
        Finset (ℕ×ℕ×ℕ×ℕ×ℕ×ℕ×ℕ×ℕ)) := by
  classical
  have nc : Fintype.card C = 32 := by rw [Module.card_eq_pow_finrank (K:=F),size,ZMod.card];rfl
  have mu0 : Green51ShortenedProfiles.multiplicity C 0 = 1 := by
    have eq : (univ.filter fun c : C => (supp c.val).card = 0) = {0} := by
      ext c
      simp only [mem_filter,mem_univ,true_and,card_eq_zero,mem_singleton]
      constructor
      · intro h;apply Subtype.ext;funext i;by_contra! e
        have hi : i ∈ supp c.val := mem_filter.mpr ⟨mem_univ _,e⟩
        rw [h] at hi; exact notMem_empty i hi
      · rintro rfl;simp [supp]
    rw [Green51ShortenedProfiles.multiplicity,eq,card_singleton]
  have sumCode (g : ℕ → ℤ) : (∑ c:C,g (supp c.val).card) =
      g 0+g 8*Green51ShortenedProfiles.multiplicity C 8+g 10*Green51ShortenedProfiles.multiplicity C 10+g 12*Green51ShortenedProfiles.multiplicity C 12+
      g 16*Green51ShortenedProfiles.multiplicity C 16 := by
    calc
      _ = ∑ c:C,∑ j∈weights,if (supp c.val).card=j then g j else 0 := by
        apply sum_congr rfl; intro c _; simp [allowed c]
      _ = ∑ j∈weights,g j*Green51ShortenedProfiles.multiplicity C j := by
        rw [sum_comm];apply sum_congr rfl;intro j _;simp [Green51ShortenedProfiles.multiplicity,sum_ite,mul_comm]
      _ = _ := by simp [weights,mu0,add_assoc]
  have ev (c : C) : Even (supp c.val).card := by
    have al := allowed c
    simp only [weights,mem_insert,mem_singleton] at al
    rw [even_iff_two_dvd];omega
  let row (S : Finset ℕ) (w : ℕ) : ℤ := ∑ j∈S,coefficient 17 w j
  have transform (S : Finset ℕ) := (dual_count C ev S).trans (sumCode (row S))
  have total := sumCode fun _ => 1
  simp only [sum_const,card_univ,nsmul_eq_mul,mul_one,one_mul,nc] at total
  have quarter : 0 < Green51ShortenedProfiles.multiplicity C 10 → 8 ≤ Green51ShortenedProfiles.multiplicity C 10 := by
    intro ten
    let q : C → F := fun c => pairParity c.val
    have same : (univ.filter fun c:C => q c = 1) = (univ.filter fun c:C => (supp c.val).card=10) := by
      apply filter_congr;intro x _
      have h := allowed x
      simp only [weights,mem_insert,mem_singleton] at h
      rcases h with h|h|h|h|h <;> rw [show q x = _ from pairParity_eq x.val,h] <;> decide
    have positive : 0 < (univ.filter fun c : C => q c = 1).card := by rw [same]; exact ten
    obtain ⟨x,hx⟩ := card_pos.mp positive
    have qa : q x = 1 := (mem_filter.mp hx).2
    have cap := quadratic_quarter q (by simp [q,pairParity_eq,supp]) ⟨x,qa⟩
      (fun x a b => pairParity_second x.val a.val b.val)
    rw [same,nc] at cap
    change 32 ≤ 4*Green51ShortenedProfiles.multiplicity C 10 at cap
    omega
  have first := transform {1}
  have second := transform {2}
  have third := transform {3}
  have all := transform {3,7,11,15}
  rw [nc] at first second third all
  change (32:ℤ)*dualCount C {1} = _ at first
  change (32:ℤ)*dualCount C {2} = _ at second
  change (32:ℤ)*dualCount C {3} = _ at third
  change (32:ℤ)*dualCount C {3,7,11,15} = _ at all
  rw [show row {1} 0 = (17:ℤ) by decide +kernel,
    show row {1} 8 = (1:ℤ) by decide +kernel,
    show row {1} 10 = (-3:ℤ) by decide +kernel,
    show row {1} 12 = (-7:ℤ) by decide +kernel,
    show row {1} 16 = (-15:ℤ) by decide +kernel] at first
  rw [show row {2} 0 = (136:ℤ) by decide +kernel,
    show row {2} 8 = (-8:ℤ) by decide +kernel,
    show row {2} 10 = (-4:ℤ) by decide +kernel,
    show row {2} 12 = (16:ℤ) by decide +kernel,
    show row {2} 16 = (104:ℤ) by decide +kernel] at second
  rw [show row {3} 0 = (680:ℤ) by decide +kernel,
    show row {3} 8 = (-8:ℤ) by decide +kernel,
    show row {3} 10 = (20:ℤ) by decide +kernel,
    show row {3} 12 = (0:ℤ) by decide +kernel,
    show row {3} 16 = (-440:ℤ) by decide +kernel] at third
  rw [show row {3,7,11,15} 0 = (32640:ℤ) by decide +kernel,
    show row {3,7,11,15} 8 = (-128:ℤ) by decide +kernel,
    show row {3,7,11,15} 10 = (128:ℤ) by decide +kernel,
    show row {3,7,11,15} 12 = (-128:ℤ) by decide +kernel,
    show row {3,7,11,15} 16 = (-128:ℤ) by decide +kernel] at all
  generalize ha : Green51ShortenedProfiles.multiplicity C 8 = a at *
  generalize ht : Green51ShortenedProfiles.multiplicity C 10 = t at *
  generalize hb : Green51ShortenedProfiles.multiplicity C 12 = b at *
  generalize hc : Green51ShortenedProfiles.multiplicity C 16 = c at *
  have boundT : t ≤ 12 := by omega
  have small : dualCount C {1} ≤ 1 := by omega
  simp only [mem_insert,mem_singleton,Prod.mk.injEq]
  interval_cases c <;> interval_cases t <;> omega
/-- The three possible weight and dual-weight profiles of every even binary
code of length seventeen, dimension at least five and minimum distance eight. -/
theorem profiles (C : Submodule F (Cube 17)) (size : 5 ≤ Module.finrank F C)
    (even : ∀ x : C, 2 ∣ (supp x.val).card)
    (dist : ∀ x : C, x ≠ 0 → 8 ≤ (supp x.val).card) :
    Module.finrank F C = 5 ∧
    (Green51ShortenedProfiles.multiplicity C 8,Green51ShortenedProfiles.multiplicity C 10,
      Green51ShortenedProfiles.multiplicity C 12,Green51ShortenedProfiles.multiplicity C 16,
      dualCount C {1},dualCount C {2},dualCount C {3},dualCount C {3,7,11,15}) ∈
      ({(22,8,0,1,0,1,7,960),(25,0,6,0,0,1,15,896),(30,0,0,1,1,0,0,896)} :
        Finset (ℕ×ℕ×ℕ×ℕ×ℕ×ℕ×ℕ×ℕ)) := by
  classical
  have nofourteen (u : C) : (supp u.val).card ≠ 14 := by
    intro w
    have nz : u ≠ 0 := fun z => by simp [z,supp] at w
    have rk := Green51TwelveResidual.residual_rank C u nz (by
      intro x nx ne sub
      have ny : x+u ≠ 0 := fun eq => ne (add_right_cancel (eq.trans (ZModModule.add_self u).symm))
      have dx := dist x nx
      have dy := dist (x+u) ny
      have hit := Green51AffineMatchings.weight_sum x.val u.val
      rw [inter_eq_left.mpr sub,w] at hit
      change 8 ≤ (supp (x.val+u.val)).card at dy
      omega)
    let T : Finset (Fin 17) := (supp u.val)ᶜ
    let R : C →ₗ[F] (T → F) := LinearMap.pi fun i:T => (LinearMap.proj i.val).comp C.subtype
    change Module.finrank F R.ker = 1 at rk
    have add := R.finrank_range_add_finrank_ker
    have up := Submodule.finrank_le R.range
    rw [show Module.finrank F (T → F) = 3 by simp [T,w]] at up
    omega
  have allowed (x : C) : (supp x.val).card ∈ weights := by
    by_cases z : x = 0
    · simp [z,supp,weights]
    have dx := dist x z
    have upper : (supp x.val).card ≤ 17 := (supp x.val).card_le_univ.trans_eq (by simp)
    have ev := even x
    have banned := nofourteen x
    simp only [weights,mem_insert,mem_singleton]
    omega
  have four (ten : Green51ShortenedProfiles.multiplicity C 10 = 0) (x : C) :
      4 ∣ (supp x.val).card := by
    have miss : (supp x.val).card ≠ 10 := by
      intro h
      have hc := card_pos.mpr (show (univ.filter fun c:C => (supp c.val).card = 10).Nonempty
        from ⟨x,mem_filter.mpr ⟨mem_univ _,h⟩⟩)
      change 0 < Green51ShortenedProfiles.multiplicity C 10 at hc
      omega
    have al := allowed x
    simp only [weights,mem_insert,mem_singleton] at al
    omega
  have dim : Module.finrank F C = 5 := by
    apply le_antisymm _ size
    by_cases ten : Green51ShortenedProfiles.multiplicity C 10 = 0
    · exact Green51ResidualPacking.seventeen C dist (four ten)
    · obtain ⟨u,hu⟩ := card_pos.mp (Nat.pos_of_ne_zero ten)
      have w : (supp u.val).card = 10 := (mem_filter.mp hu).2
      have pack := Green51TwelveResidual.ten_packing C dist u w
      by_contra! high
      have bad := Nat.pow_le_pow_right (by decide : 0 < 2) (show 5 ≤ Module.finrank F C-1 by omega)
      norm_num at pack bad
      omega
  refine ⟨dim,distribution C dim allowed ?_ ?_⟩
  · apply card_le_one.mpr
    intro x hx y hy
    have wx : (supp x.val).card = 16 := (mem_filter.mp hx).2
    have wy : (supp y.val).card = 16 := (mem_filter.mp hy).2
    have small := (supp x.val ∪ supp y.val).card_le_univ
    rw [Fintype.card_fin] at small
    have counts := card_union_add_card_inter (supp x.val) (supp y.val)
    have result := Green51AffineMatchings.weight_sum x.val y.val
    have sum : x+y = 0 := by
      by_contra nz
      have h := dist (x+y) nz
      change 8 ≤ (supp (x.val+y.val)).card at h
      omega
    exact add_right_cancel (sum.trans (ZModModule.add_self y).symm)
  · intro ten yes
    obtain ⟨x,hx⟩ := card_pos.mp yes
    exact inactive_of_sixteen C (four ten) x (mem_filter.mp hx).2

end Green51SeventeenProfiles
#print axioms Green51SeventeenProfiles.profiles
