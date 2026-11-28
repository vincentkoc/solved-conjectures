import Green51FourSpaceOffsets

/-! # Incompatible offsets in the candidate configurations -/
namespace Green51FourSpace.Certificate
private def tryOffsets (seen : List (Nat × Nat)) : List Nat → Bool
  | [] => true
  | u :: rest => (offsets[u]?.getD []).any (fun v =>
      seen.all (fun (x,y) => (offsetMasks[u ^^^ x]?.getD 0).testBit (v ^^^ y)) &&
        tryOffsets (extendPairs seen u v) rest)


/-- Every linear choice of compatible offsets survives each step of the finite search. -/
private theorem tryOffsets_sound (R : Set Nat) (f : Nat → Nat)
    (closed : ∀ u∈R, ∀ v∈R,u ^^^ v ∈ R)
    (add : ∀ u∈R, ∀ v∈R,f (u ^^^ v)=f u ^^^ f v)
    (small : ∀ u∈R,u<256) (bound : ∀ u∈R,f u<256) (valid : ∀ u∈R,allowed u (f u)=true)
    (seen : List (Nat × Nat)) (remaining : List Nat)
    (correct : ∀ p∈seen,p.1∈R ∧ p.2=f p.1) (active : ∀ u∈remaining,u∈R) :
    tryOffsets seen remaining = true := by
  induction remaining generalizing seen with
  | nil => rfl
  | cons u rest ih =>
    have hu := active u (List.mem_cons_self)
    apply List.any_eq_true.mpr
    refine ⟨f u,in_offsets (small u hu) (bound u hu) (valid u hu),Bool.and_eq_true_iff.mpr ⟨?_,?_⟩⟩
    · apply List.all_eq_true.mpr
      rintro ⟨x,y⟩ member
      obtain ⟨hx,hy⟩ : x∈R ∧ y=f x := correct _ member
      subst y
      change (offsetMasks[u ^^^ x]?.getD 0).testBit (f u ^^^ f x)=true
      rw [←add u hu x hx]
      exact in_offsetMask (small _ (closed _ hu _ hx)) (bound _ (closed _ hu _ hx)) (valid _ (closed _ hu _ hx))
    · apply ih
      · intro p hp
        rcases List.mem_append.mp hp with old|new
        · exact correct p old
        · obtain ⟨⟨x,y⟩,inSeen,rfl⟩ := List.mem_map.mp new
          obtain ⟨hx,hy⟩ : x∈R ∧ y=f x := correct _ inSeen
          subst y
          exact ⟨closed _ hu _ hx,(add _ hu _ hx).symm⟩
      · exact fun x hx => active x (List.mem_cons_of_mem _ hx)

set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem failed_blocks : ∀ g:Fin 77,(List.range 8).all (fun j=>
    match shapes[g.val*8+j]? with
    | none => true
    | some b => !(tryOffsets [(0,0)] b))=true := by
  intro g
  fin_cases g <;> decide +kernel

/-- No compatible offset assignment exists on any shape in the cover. -/
theorem shapes_fail {B:List Nat} (h:B∈shapes) : tryOffsets [(0,0)] B=false := by
  obtain ⟨i,hi,eq⟩ := List.getElem_of_mem h
  have len : shapes.length=609 := by decide +kernel
  have row := List.all_eq_true.mp (failed_blocks ⟨i/8,by omega⟩) (i%8) (List.mem_range.mpr (by omega))
  change (match shapes[i/8*8+i%8]? with | none => true | some b => !(tryOffsets [(0,0)] b))=true at row
  rw [show i/8*8+i%8=i by omega,List.getElem?_eq_getElem hi,eq] at row
  simpa using row

theorem no_shape (R:Set Nat) (f:Nat→Nat) (zero:0∈R) (fzero:f 0=0)
    (closed:∀ u∈R,∀ v∈R,u ^^^ v ∈ R)
    (add:∀ u∈R,∀ v∈R,f (u ^^^ v)=f u ^^^ f v)
    (small:∀ u∈R,u<256) (bound:∀ u∈R,f u<256) (valid:∀ u∈R,allowed u (f u)=true)
    {B:List Nat} (hb:B∈shapes) : ¬∀ u∈B,u∈R := by
  intro contains
  have yes := tryOffsets_sound R f closed add small bound valid [(0,0)] B (by simpa [fzero] using zero) contains
  exact Bool.noConfusion (yes.symm.trans (shapes_fail hb))
end Green51FourSpace.Certificate
#print axioms Green51FourSpace.Certificate.no_shape
