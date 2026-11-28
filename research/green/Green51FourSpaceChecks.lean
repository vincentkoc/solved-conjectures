import Green51FourSpaceCover
/-! # Three binary parity checks on eight positions -/
namespace Green51FourSpace.Certificate
open Lean
private def merge (xs:List Nat) : Nat := xs.foldr (· ||| ·) 0
private theorem merge_spec (xs : List Nat) (i:Nat) :
    (merge xs).testBit i=true ↔ ∃ x∈xs,x.testBit i=true := by
  induction xs with
  | nil => simp [merge]
  | cons x xs ih =>
    change (x ||| merge xs).testBit i=true ↔ _
    simp [Nat.testBit_or,ih]
private def square (p:Nat) : Nat := merge <|
  ((List.range 256).filter p.testBit).map (fun b => (p%2^256) <<< (256*b))
private theorem square_sound {p b c:Nat} (hc:c<256) (hit:(square p).testBit (256*b+c)=true) :
    p.testBit b=true ∧ p.testBit c=true := by
  obtain ⟨_,mem,on⟩ := (merge_spec _ _).mp hit
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp mem
  have hx := (List.mem_filter.mp hr).2
  rw [Nat.testBit_shiftLeft] at on
  simp only [Bool.and_eq_true,decide_eq_true_eq] at on
  have lt : 256*b+c-256*r<256 := by
    by_contra! le
    have e := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (Nat.mod_lt p (by positivity : 0<2^256))
      (Nat.pow_le_pow_right (by decide : 0<2) le))
    simp_all
  have eq:r=b := by omega
  subst r
  rw [show 256*b+c-256*b=c by omega,Nat.testBit_mod_two_pow] at on
  simp only [decide_eq_true hc,Bool.true_and] at on
  exact ⟨hx,on.2⟩

elab "squareZones%" : term => return toExpr (zones.map fun p => (p,square p))
private def squares : List (Nat × Nat) := squareZones%
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem squares_exact : zones.map (fun p => (p,square p))=squares := by decide +kernel

private def covers (a:Nat) : Bool :=
  merge ((squares.filter (fun p => p.1.testBit a)).map Prod.snd) == 2^65536-1
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem coverage_table : ∀ g:Fin 32, (List.range 8).all (fun j=>covers (8*g.val+j))=true := by
  intro g
  fin_cases g <;> decide +kernel

/-- Any three parity checks on eight binary coordinates annihilate a common
obstruction. The bits of each square encode the last two checks simultaneously. -/
theorem three_checks (a b c:Nat) (ha:a<256) (hb:b<256) (hc:c<256) :
    ∃ B ∈ shapes, ∀ u∈B,orthogonal u a=true ∧ orthogonal u b=true ∧ orthogonal u c=true := by
  have row := List.all_eq_true.mp (coverage_table ⟨a/8,by omega⟩) (a%8) (List.mem_range.mpr (by omega))
  have ix : 8*(a/8)+a%8=a := by omega
  change covers (8*(a/8)+a%8)=true at row
  rw [ix] at row
  have full := beq_iff_eq.mp row
  have deg : 256*b+c<65536 := by omega
  have hit : (merge ((squares.filter (fun p=>p.1.testBit a)).map Prod.snd)).testBit (256*b+c)=true := by
    rw [full,Nat.testBit_two_pow_sub_one];exact decide_eq_true deg
  obtain ⟨_,hy,on⟩ := (merge_spec _ _).mp hit
  obtain ⟨p,mem,rfl⟩ := List.mem_map.mp hy
  obtain ⟨hp,hpa⟩ := List.mem_filter.mp mem
  rw [←squares_exact] at hp
  obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hp
  have ⟨hpb,hpc⟩ := square_sound hc on
  rw [←zones_exact] at hz
  obtain ⟨B,inB,rfl⟩ := List.mem_map.mp hz
  refine ⟨B,inB,fun u hu => ⟨((zone_iff B a).mp hpa).2 _ hu,
    ((zone_iff B b).mp hpb).2 _ hu,((zone_iff B c).mp hpc).2 _ hu⟩⟩

end Green51FourSpace.Certificate

#print axioms Green51FourSpace.Certificate.three_checks
