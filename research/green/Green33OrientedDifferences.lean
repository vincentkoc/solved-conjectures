import Green33TailEnergy
/-! Opposite mixed differences in sparse cyclic bases. -/
open Finset Green33Multiplicity
open scoped Pointwise
namespace Green33OrientedDifferences
variable {G:Type*} [AddCommGroup G] [DecidableEq G]

private def pairSum : Sym2 G→G := Sym2.lift ⟨(·+·),add_comm⟩

private def used (E B:Finset G) := B.sym2.filter fun p => pairSum p∈E+E

private theorem used_budget {E B T:Finset G} (incE:E⊆T) (incB:B⊆T) (sep:Disjoint E B) :
    (used E B).card+(T+T).card≤(T.card+1).choose 2 := by
  classical
  let U:=used E B
  have sub:U⊆T.sym2 := by
    rintro ⟨a,b⟩ h
    exact mk_mem_sym2_iff.mpr (And.imp (fun k => incB k) (fun k => incB k) (mk_mem_sym2_iff.mp (mem_filter.mp h).1))
  have cover:T+T ⊆ (T.sym2\U).image pairSum := by
    intro s hs
    obtain ⟨a,ha,b,hb,rfl⟩:=mem_add.mp hs
    by_cases u:Sym2.mk a b∈U
    · obtain ⟨c,hc,d,hd,eq⟩:=mem_add.mp (mem_filter.mp u).2
      apply mem_image.mpr
      refine ⟨Sym2.mk c d,mem_sdiff.mpr ⟨mk_mem_sym2_iff.mpr ⟨incE hc,incE hd⟩,?_⟩,eq⟩
      exact fun h => Finset.disjoint_left.mp sep hc (mk_mem_sym2_iff.mp (mem_filter.mp h).1).1
    · exact mem_image.mpr ⟨Sym2.mk a b,mem_sdiff.mpr ⟨mk_mem_sym2_iff.mpr ⟨ha,hb⟩,u⟩,rfl⟩
  have h:=(card_le_card cover).trans card_image_le
  have sz:=card_sdiff_add_card_eq_card sub
  rw [card_sym2] at sz
  change U.card+_≤_;omega

/-- Each unordered pair admits at most two orderings. -/
private theorem ordered_budget (E B:Finset G) :
    ((B×ˢB).filter fun p => p.1+p.2∈E+E).card≤2*(used E B).card := by
  classical
  let M:=(B×ˢB).filter fun p => p.1+p.2∈E+E
  let f (p:G×G):=Sym2.mk p.1 p.2
  apply card_le_mul_card_image_of_maps_to (s:=M) (f:=f) _ 2 _
  · rintro ⟨b,c⟩ h
    exact mem_filter.mpr ⟨mk_mem_sym2_iff.mpr (mem_product.mp (mem_filter.mp h).1),(mem_filter.mp h).2⟩
  · rintro ⟨a,b⟩ _
    apply (card_le_card (t:={(a,b),(b,a)}) ?_).trans card_le_two
    rintro ⟨x,y⟩ h
    rcases Sym2.eq_iff.mp (mem_filter.mp h).2 with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> simp

/-- A difference represented in both orientations gives a same-sum pair
from each disjoint block. The constant two accounts for ordering the B-pair. -/
theorem mixed_difference_budget (T E B:Finset G) (incE:E⊆T) (incB:B⊆T)
    (sep:Disjoint E B) (C:ℕ) (cap:∀ s,reps E s≤C) :
    ((E-B)∩(B-E)).card≤2*C*((T.card+1).choose 2-(T+T).card) := by
  classical
  let M:=(B×ˢB).filter fun p => p.1+p.2∈E+E
  let V (p:G×G):=((E×ˢE).filter fun u => u.1+u.2=p.1+p.2).image (fun u => u.1-p.1)
  have inc:(E-B)∩(B-E) ⊆ M.biUnion V := by
    intro s hs
    obtain ⟨d,hd,b,hb,eq⟩:=mem_sub.mp (mem_inter.mp hs).1
    obtain ⟨c,hc,e,he,eq'⟩:=mem_sub.mp (mem_inter.mp hs).2
    have same:d+e=b+c := calc
      d+e=(d-b)+(b+e) := by abel
      _=(c-e)+(b+e) := by rw [eq,eq']
      _=b+c := by abel
    refine mem_biUnion.mpr ⟨(b,c),mem_filter.mpr ⟨mem_product.mpr ⟨hb,hc⟩,same ▸ add_mem_add hd he⟩,?_⟩
    exact mem_image.mpr ⟨(d,e),mem_filter.mpr ⟨mem_product.mpr ⟨hd,he⟩,same⟩,eq⟩
  have each (p:G×G) : (V p).card≤C:=card_image_le.trans (cap (p.1+p.2))
  have h:=((card_le_card inc).trans card_biUnion_le).trans (sum_le_sum (fun p _ => each p))
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id] at h
  have ord:=ordered_budget E B
  have quota:=used_budget incE incB sep
  have u:(used E B).card≤(T.card+1).choose 2-(T+T).card := by omega
  exact h.trans (by calc
    M.card*C ≤ (2*(used E B).card)*C := Nat.mul_le_mul_right _ ord
    _ = (2*C)*(used E B).card := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ u)
#print axioms mixed_difference_budget

/-- In the cyclic group of order five the two orientations use exactly twice
the entire unordered-pair excess, already with a singleton first block. -/
theorem sharp_five :
    let E:Finset (ZMod 5):={0}
    let B:Finset (ZMod 5):={1,4}
    let T:=E∪B
    T+T=univ ∧ (∀ s,reps E s≤1) ∧
      ((E-B)∩(B-E)).card=2 ∧ (T.card+1).choose 2-(T+T).card=1 := by decide
#print axioms sharp_five

open Filter Green33TailEnergy
open scoped Topology
variable {ι:Type*} {l:Filter ι}

/-- In an arbitrary critical full cyclic basis, opposite mixed differences
between disjoint blocks occupy a vanishing fraction if either block has
bounded ordered sum counts. The modulus has no parity restriction. -/
theorem critical_orientations (n:ι→ℕ+) (T E B:∀ i,Finset (ZMod (n i)))
    (grow:Tendsto (fun i => (n i).val) l atTop) (full:∀ i,T i+T i=univ)
    (crit:Tendsto (fun i => ((T i).card:ℝ)/Real.sqrt (n i)) l (𝓝 (Real.sqrt 2)))
    (incE:∀ i,E i⊆T i) (incB:∀ i,B i⊆T i) (sep:∀ i,Disjoint (E i) (B i))
    (C:ℕ) (cap:∀ i s,reps (E i) s≤C) :
    Tendsto (fun i => (((E i-B i)∩(B i-E i)).card:ℝ)/(n i:ℝ)) l (𝓝 0) := by
  obtain ⟨lin,quad⟩:=card_limits n (fun i => (T i).card) grow crit
  have zero:=((quad.add lin).sub_const 2).const_mul (C:ℝ)
  simp only [add_zero,sub_self,mul_zero] at zero
  apply squeeze_zero' (Eventually.of_forall fun i => by positivity) _ zero
  apply Eventually.of_forall
  intro i
  have p:=mixed_difference_budget (T i) (E i) (B i) (incE i) (incB i) (sep i) C (cap i)
  rw [full,card_univ,ZMod.card] at p
  have h:(n i).val≤((T i).card+1).choose 2 := by
    have small:=used_budget (incE i) (incB i) (sep i)
    rw [full,card_univ,ZMod.card] at small
    omega
  have r:=Nat.cast_le (α:=ℝ).mpr p
  rw [Nat.cast_mul,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_sub h,Nat.cast_choose_two,Nat.cast_add_one] at r
  have pos:(0:ℝ)<(n i).val := by exact_mod_cast (n i).pos
  apply (div_le_iff₀ pos).mpr
  apply r.trans
  field_simp [pos.ne']
  ring_nf
  exact le_rfl
#print axioms critical_orientations

end Green33OrientedDifferences
