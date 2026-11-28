import Erdos722QuartetSeeds

/-!
# Difference families for the finite five-point spectrum

The order 81 data are Hanani's four starters in the additive group of order
81, as reproduced by Clayton Smith in Lemma 28. The cyclic starters at 141
and 161 occur in the SageMath difference-family tables. At 281 the fourteen
blocks are the multiples by `3^(10j)` of `{0,1,184,24,209}` for `0 ≤ j < 14`.
-/

namespace Erdos722.Five.Starter
open Erdos722.Quartet

set_option maxRecDepth 30000
set_option maxHeartbeats 8000000

private def blocks61 : Fin 3 → Fin 5 → ZMod 61 :=
  ![![1,9,20,34,58],
    ![4,36,19,14,49],
    ![16,22,15,56,13]]

theorem order61 : Has (· = 5) 61 := by
  exact (show Fintype.card (ZMod 61) = 61 by simp) ▸
    Seeds.development blocks61 (by unfold Function.Injective; decide +kernel)
      (by unfold ExistsUnique; decide +kernel)

#print axioms order61

private def blocks81 : Fin 4 → Fin 5 → ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3 :=
  ![![(0,0,0,1),(2,0,0,1),(0,0,2,1),(1,2,0,2),(0,1,1,1)],
    ![(0,0,1,0),(1,1,0,2),(0,2,1,0),(1,2,0,1),(1,1,1,0)],
    ![(2,2,1,1),(1,2,2,2),(2,0,1,2),(0,1,2,1),(1,1,0,0)],
    ![(0,2,0,2),(1,1,0,1),(1,2,1,2),(1,2,1,0),(0,2,1,1)]]

theorem order81 : Has (· = 5) 81 := by
  exact (show Fintype.card (ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3) = 81 by simp) ▸
    Seeds.development blocks81 (by unfold Function.Injective; decide +kernel)
      (by unfold ExistsUnique; decide +kernel)

#print axioms order81

private def blocks141 : Fin 7 → Fin 5 → ZMod 141 :=
  ![![0,33,60,92,97],
    ![0,3,45,88,110],
    ![0,18,39,68,139],
    ![0,12,67,75,113],
    ![0,1,15,84,94],
    ![0,7,11,24,30],
    ![0,36,90,116,125]]

theorem order141 : Has (· = 5) 141 := by
  exact (show Fintype.card (ZMod 141) = 141 by simp) ▸
    Seeds.development blocks141 (by unfold Function.Injective; decide +kernel)
      (by unfold ExistsUnique; decide +kernel)

#print axioms order141

private def blocks161 : Fin 8 → Fin 5 → ZMod 161 :=
  ![![0,19,34,73,80],
    ![0,16,44,71,79],
    ![0,12,33,74,78],
    ![0,13,30,72,77],
    ![0,11,36,67,76],
    ![0,18,32,69,75],
    ![0,10,48,68,70],
    ![0,3,29,52,53]]

theorem order161 : Has (· = 5) 161 := by
  exact (show Fintype.card (ZMod 161) = 161 by simp) ▸
    Seeds.development blocks161 (by unfold Function.Injective; decide +kernel)
      (by unfold ExistsUnique; decide +kernel)

#print axioms order161

private def blocks281 : Fin 14 → Fin 5 → ZMod 281 :=
  ![![0,1,184,24,209],
    ![0,39,151,93,2],
    ![0,116,269,255,78],
    ![0,28,94,110,232],
    ![0,249,13,75,56],
    ![0,157,226,115,217],
    ![0,222,103,270,33],
    ![0,228,83,133,163],
    ![0,181,146,129,175],
    ![0,34,74,254,81],
    ![0,202,76,71,68],
    ![0,10,154,240,123],
    ![0,109,105,87,20],
    ![0,36,161,21,218]]

theorem order281 : Has (· = 5) 281 := by
  exact (show Fintype.card (ZMod 281) = 281 by simp) ▸
    Seeds.development blocks281 (by unfold Function.Injective; decide +kernel)
      (by unfold ExistsUnique; decide +kernel)

#print axioms order281

end Erdos722.Five.Starter
