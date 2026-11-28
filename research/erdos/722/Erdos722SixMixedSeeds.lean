import Erdos722SixLayerDesign
import Erdos722SixConsecutiveSeeds

/-!
# Six-point designs on 196 and 201 points

These are the designs of Abel, Bluskov, Greig and de Heer,
*Pair covering and other designs with block size 6*, Theorem 3.2.
The first two starters need translations alone. The remaining starters
supply three translation orbits each under the stated multiplier.
-/

namespace Erdos722.Six
open Erdos722.Quartet

private def base196 : Fin 10 → Fin 6 → Fin 4 × ZMod 49 :=
  ![![(0,0),(0,1),(1,0),(1,30),(2,0),(2,18)],
    ![(0,8),(0,19),(1,44),(1,31),(2,46),(2,48)],
    ![(0,0),(0,2),(0,12),(0,45),(1,3),(3,11)],
    ![(0,0),(0,3),(0,8),(1,5),(1,17),(3,39)],
    ![(0,0),(0,9),(0,36),(1,24),(1,44),(3,37)],
    ![(0,0),(0,15),(1,34),(1,41),(2,47),(3,18)],
    ![(0,0),(0,7),(0,31),(1,13),(2,35),(3,41)],
    ![(0,0),(0,14),(1,32),(2,10),(3,22),(3,44)],
    ![(0,0),(0,23),(1,21),(1,39),(3,19),(3,25)],
    ![(0,0),(1,33),(3,0),(3,5),(3,29),(3,47)]]

private def rows196 (h : Fin 26) (i : Fin 6) : Fin 4 × ZMod 49 :=
  let l := if h.val < 2 then h.val else 2+(h.val-2)/3
  let e := if h.val < 2 then 0 else (h.val-2)%3
  let x := base196 ⟨l,by dsimp [l]; split <;> omega⟩ i
  (if x.1.val=3 then 3 else ⟨(x.1.val+e)%3,by omega⟩,30^e*x.2)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 20000000 in
theorem local_thirty_nine : Local 39 := by
  change Has (· = 6) 196
  have h := layer_design rows196 (by unfold Function.Injective; decide +kernel)
    (by intro u v; fin_cases u <;> fin_cases v <;> unfold ExistsUnique <;> decide +kernel)
  simpa only [Fintype.card_fin,ZMod.card] using h

#print axioms local_thirty_nine

private def base201 : Fin 8 → Fin 6 → Fin 3 × ZMod 67 :=
  ![![(1,3),(1,20),(1,44),(2,36),(2,39),(2,59)],
    ![(0,0),(1,0),(1,30),(1,38),(1,66),(2,0)],
    ![(0,0),(0,1),(2,4),(2,9),(2,34),(2,62)],
    ![(1,0),(1,2),(1,15),(2,8),(2,27),(2,49)],
    ![(0,0),(0,3),(0,22),(1,54),(2,13),(2,40)],
    ![(0,0),(0,36),(0,40),(1,31),(1,34),(2,5)],
    ![(0,0),(0,50),(0,55),(1,6),(1,24),(2,26)],
    ![(0,0),(0,2),(1,3),(1,14),(1,35),(2,25)]]

private def rows201 (h : Fin 20) (i : Fin 6) : Fin 3 × ZMod 67 :=
  let l := if h.val < 2 then h.val else 2+(h.val-2)/3
  let e := if h.val < 2 then 0 else (h.val-2)%3
  let x := base201 ⟨l,by dsimp [l]; split <;> omega⟩ i
  (x.1,29^e*x.2)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 20000000 in
theorem local_forty : Local 40 := by
  change Has (· = 6) 201
  have h := layer_design rows201 (by unfold Function.Injective; decide +kernel)
    (by intro u v; fin_cases u <;> fin_cases v <;> unfold ExistsUnique <;> decide +kernel)
  simpa only [Fintype.card_fin,ZMod.card] using h

#print axioms local_forty

end Erdos722.Six
