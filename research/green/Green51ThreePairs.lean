import Green51SimplexModel
import Green51SimplexDirections
import Green51BitTranslations

/-! # Covering the binary ten-space by translates of the odd simplex sums -/

open Green51SimplexSection Green51SimplexDirections
namespace Green51ThreePairs

private def labels := units++extras
private def triples := labels.flatMap fun a =>
  (labels.filter (fun b => a<b)).flatMap fun b =>
    (labels.filter (fun c => b<c)).map fun c => (a ^^^ b) ^^^ c
private def odd := labels++triples

private def bits : List ℕ → ℕ
  | [] => 0
  | x::xs => 2^x ||| bits xs

private theorem test_bits (xs:List ℕ) (i:ℕ) : (bits xs).testBit i=true ↔ i∈xs := by
  induction xs with
  | nil => simp [bits]
  | cons x xs ih =>
    simp only [bits,Nat.testBit_or,Bool.or_eq_true,Nat.testBit_two_pow,decide_eq_true_eq,ih,List.mem_cons]
    exact or_congr eq_comm Iff.rfl

private def oddMask := 89774161837697011814977378921789811718150896940945571441384947350293681326855704765236827662360498735170317244665617330001230001835935446143627982726259089026503790388572982937680328166938283853768128760340371995759562904613872707498953871020252173642912490439826004651019532307518331601386091125557455454207
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem mask_value : bits odd=oddMask := by decide +kernel

def choices (u v w:ℕ) := [0,u,v,w,u ^^^ v,u ^^^ w,v ^^^ w,(u ^^^ v) ^^^ w]
private def ok (u v w:ℕ) :=
  decide (u<v ∧ v<w) && directions.contains (u ^^^ v) && directions.contains (u ^^^ w) &&
    directions.contains (v ^^^ w) && (u ^^^ v != w)
private def translated (d:ℕ) := if d<1024 then Green51BitTranslations.shift d oddMask 10 else 0
private def unionMask (cs:List ℕ) := cs.foldr (fun d m => translated d ||| m) 0
private def works (u v w:ℕ) := unionMask (choices u v w) == 2^1024-1

private theorem find_offset (cs:List ℕ) (t:Fin 1024) (hit:(unionMask cs).testBit t.val=true) :
    ∃d∈cs,oddMask.testBit (t.val ^^^ d)=true := by
  induction cs with
  | nil => simp [unionMask] at hit
  | cons x xs ih =>
    change (translated x ||| unionMask xs).testBit t.val=true at hit
    simp only [Nat.testBit_or,Bool.or_eq_true] at hit
    rcases hit with h|h
    · unfold translated at h
      split at h
      · rename_i small
        exact ⟨x,List.mem_cons_self,(Green51BitTranslations.shift_bit ⟨x,small⟩ t oddMask) ▸ h⟩
      · simp at h
    · obtain ⟨d,hd,tst⟩ := ih h
      exact ⟨d,List.mem_cons_of_mem _ hd,tst⟩

private def row (u:ℕ) := directions.all fun v => directions.all fun w => !ok u v w || works u v w
section
set_option maxRecDepth 20000
set_option maxHeartbeats 0
private theorem row103 : row 103=true := by decide +kernel
private theorem row124 : row 124=true := by decide +kernel
private theorem row151 : row 151=true := by decide +kernel
private theorem row186 : row 186=true := by decide +kernel
private theorem row221 : row 221=true := by decide +kernel
private theorem row235 : row 235=true := by decide +kernel
private theorem row271 : row 271=true := by decide +kernel
private theorem row313 : row 313=true := by decide +kernel
private theorem row350 : row 350=true := by decide +kernel
private theorem row371 : row 371=true := by decide +kernel
private theorem row430 : row 430=true := by decide +kernel
private theorem row437 : row 437=true := by decide +kernel
private theorem row457 : row 457=true := by decide +kernel
private theorem row466 : row 466=true := by decide +kernel
private theorem row484 : row 484=true := by decide +kernel
private theorem row511 : row 511=true := by decide +kernel
private theorem row622 : row 622=true := by decide +kernel
private theorem row629 : row 629=true := by decide +kernel
private theorem row670 : row 670=true := by decide +kernel
private theorem row691 : row 691=true := by decide +kernel
private theorem row724 : row 724=true := by decide +kernel
private theorem row738 : row 738=true := by decide +kernel
private theorem row797 : row 797=true := by decide +kernel
private theorem row811 : row 811=true := by decide +kernel
private theorem row844 : row 844=true := by decide +kernel
private theorem row865 : row 865=true := by decide +kernel
private theorem row906 : row 906=true := by decide +kernel
private theorem row913 : row 913=true := by decide +kernel
end
private theorem checked : directions.all row=true := by
  simp only [directions,List.all_cons,List.all_nil,row103,row124,row151,row186,row221,row235,row271,row313,row350,row371,row430,row437,row457,row466,row484,row511,row622,row629,row670,row691,row724,row738,row797,row811,row844,row865,row906,row913,Bool.and_self]

set_option exponentiation.threshold 1024 in
theorem translated_sum {u v w t:ℕ} (hu:u∈directions) (hv:v∈directions) (hw:w∈directions)
    (order:u<v ∧ v<w) (uv:u ^^^ v∈directions) (uw:u ^^^ w∈directions) (vw:v ^^^ w∈directions)
    (non:u ^^^ v≠w) (small:t<1024) :
    ∃d∈choices u v w, ∃a∈units++extras, ∃b∈units++extras, ∃c∈units++extras,
      ((a ^^^ b) ^^^ c) ^^^ d=t := by
  have all := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp checked u hu) v hv) w hw
  have yes : ok u v w=true := by simp [ok,uv,uw,vw,non,order]
  simp only [yes,Bool.not_true,Bool.false_or] at all
  have same : unionMask (choices u v w)=2^1024-1 := by simpa only [works,beq_iff_eq] using all
  have bit : (unionMask (choices u v w)).testBit t=true := by
    rw [same,Nat.testBit_two_pow_sub_one];exact decide_eq_true small
  obtain ⟨d,hd,test⟩ := find_offset _ ⟨t,small⟩ bit
  change oddMask.testBit (t ^^^ d)=true at test
  rw [←mask_value] at test
  have hi := (test_bits _ _).mp test
  have total : (t ^^^ d) ^^^ d=t := by simp
  refine ⟨d,hd,?_⟩
  rcases List.mem_append.mp hi with h|h
  · exact ⟨_,h,0,by decide,0,by decide,by simpa only [Nat.xor_zero] using total⟩
  · obtain ⟨a,ha,more⟩ := List.mem_flatMap.mp h
    obtain ⟨b,hb,rest⟩ := List.mem_flatMap.mp more
    obtain ⟨c,hc,eq⟩ := List.mem_map.mp rest
    exact ⟨a,ha,b,(List.mem_filter.mp hb).1,c,(List.mem_filter.mp hc).1,by rw [eq];exact total⟩

private def Covered (u v w t:ℕ) :=
  ∃d∈choices u v w, ∃a∈units++extras, ∃b∈units++extras, ∃c∈units++extras,
    ((a ^^^ b) ^^^ c) ^^^ d=t

private theorem perm12 (u v w t:ℕ) : Covered u v w t ↔ Covered v u w t := by
  have same (d:ℕ) : d∈choices u v w ↔ d∈choices v u w := by
    simp only [choices,List.mem_cons,List.not_mem_nil,or_false,Nat.xor_comm u v]
    tauto
  unfold Covered
  simp_rw [same]
private theorem perm23 (u v w t:ℕ) : Covered u v w t ↔ Covered u w v t := by
  have last : (u ^^^ v) ^^^ w=(u ^^^ w) ^^^ v := by
    rw [Nat.xor_assoc,Nat.xor_comm v w,←Nat.xor_assoc]
  have same (d:ℕ) : d∈choices u v w ↔ d∈choices u w v := by
    simp only [choices,List.mem_cons,List.not_mem_nil,or_false,last,Nat.xor_comm v w]
    tauto
  unfold Covered
  simp_rw [same]

theorem all_orders {u v w t:ℕ} (hu:u∈directions) (hv:v∈directions) (hw:w∈directions)
    (uv:u ^^^ v∈directions) (uw:u ^^^ w∈directions) (vw:v ^^^ w∈directions)
    (non:u ^^^ v≠w) (small:t<1024) :
    ∃d∈choices u v w, ∃a∈units++extras, ∃b∈units++extras, ∃c∈units++extras,
      ((a ^^^ b) ^^^ c) ^^^ d=t := by
  change Covered u v w t
  have nz : 0∉directions := by decide
  have distinct {x y:ℕ} (h:x ^^^ y∈directions) : x≠y := by rintro rfl; simp_all
  have rotate {a b c:ℕ} (h:a ^^^ b≠c) : a ^^^ c≠b := by
    intro eq; apply h;rw [←eq,←Nat.xor_assoc,Nat.xor_self,Nat.zero_xor]
  have ij:=distinct uv; have ik:=distinct uw; have jk:=distinct vw
  have base {a b c:ℕ} (aD:a∈directions) (bD:b∈directions) (cD:c∈directions)
      (ab:a ^^^ b∈directions) (ac:a ^^^ c∈directions) (bc:b ^^^ c∈directions)
      (ne:a ^^^ b≠c) (i:a<b) (j:b<c) : Covered a b c t :=
    translated_sum aD bD cD ⟨i,j⟩ ab ac bc ne small
  have vu : v ^^^ u∈directions := Nat.xor_comm u v ▸ uv
  have wu : w ^^^ u∈directions := Nat.xor_comm u w ▸ uw
  have wv : w ^^^ v∈directions := Nat.xor_comm v w ▸ vw
  have nvu : v ^^^ u≠w := Nat.xor_comm u v ▸ non
  by_cases a:u<v
  · by_cases b:v<w
    · exact base hu hv hw uv uw vw non a b
    by_cases c:u<w
    · exact (perm23 ..).mpr (base hu hw hv uw uv wv (rotate non) c (by omega))
    apply (perm23 ..).mpr;apply (perm12 ..).mpr
    exact base hw hu hv wu wv uv (Nat.xor_comm u w ▸ rotate non) (by omega) a
  · by_cases b:u<w
    · exact (perm12 ..).mpr (base hv hu hw vu vw uw nvu (by omega) b)
    by_cases c:v<w
    · apply (perm12 ..).mpr;apply (perm23 ..).mpr
      exact base hv hw hu vw vu wu (rotate nvu) c (by omega)
    apply (perm12 ..).mpr;apply (perm23 ..).mpr;apply (perm12 ..).mpr
    exact base hw hv hu wv wu vu (Nat.xor_comm v w ▸ rotate nvu) (by omega) (by omega)

end Green51ThreePairs
#print axioms Green51ThreePairs.translated_sum
#print axioms Green51ThreePairs.all_orders
