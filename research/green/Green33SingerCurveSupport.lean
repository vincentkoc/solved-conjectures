import Green33AffineCurves
import Green33SingerCurveChart
import Green33SingerCurveEscape
/-! Plane curves in affine Singer coordinates, including the points at infinity. -/
open Finset Polynomial Green33SingerBlockingLayers Green33SingerCurveChart Green33SingerCurveEscape
open scoped Polynomial Pointwise
namespace Green33SingerCurveSupport
open Green33AffineCurves
variable {F G : Type*} [Field F] [DecidableEq F] [Fintype F] [AddCommGroup G] [DecidableEq G] [Fintype G]
variable {D : Finset G}

/-- The affine zero set together with the entire line at infinity. -/
noncomputable def locus (A : Chart F G D) (f : F[X][X]) : Finset G := by
  classical
  exact (univ.filter (fun z => z∉Set.range A.point))∪(zeros f).map A.point

theorem curve_cover (A : Chart F G D) (f : F[X][X]) (ne : f≠0) {d : ℕ}
    (dx : ∀ i,(f.coeff i).natDegree≤d) (B : Finset G) :
    ∃ C : LineCover D (B∩locus A f) (d+f.natDegree), C.lines.card≤1+d+f.natDegree := by
  classical
  let V:=B∩locus A f
  let P:=residual f
  let R:=V∩P.map A.point
  let centers:=insert A.infinity ((verticals f).image A.vertical ∪ (obliques f).image A.oblique)
  have bounds:=line_counts f ne dx
  have size : centers.card≤1+d+f.natDegree := by
    have v:= (card_image_le (s:=verticals f) (f:=A.vertical)).trans bounds.1
    have w:= (card_image_le (s:=obliques f) (f:=A.oblique)).trans bounds.2
    have u:=card_union_le ((verticals f).image A.vertical) ((obliques f).image A.oblique)
    have i:=card_insert_le A.infinity ((verticals f).image A.vertical∪(obliques f).image A.oblique)
    dsimp only [centers];omega
  have filt (c:G) (test : F×F→Prop) [DecidablePred test]
      (h : ∀ p,c-A.point p∈D → test p) :
      occupancy D R c≤(P.filter test).card := by
    have sub : R.filter (fun z => c-z∈D)⊆(P.filter test).map A.point := by
      intro z hz
      obtain ⟨r,hit⟩:=mem_filter.mp hz
      obtain ⟨p,hp,rfl⟩:=mem_map.mp (mem_inter.mp r).2
      exact mem_map.mpr ⟨p,mem_filter.mpr ⟨hp,h _ hit⟩,rfl⟩
    have n:=card_le_card sub
    rwa [occ_flip,card_map] at n
  refine ⟨⟨R,inter_subset_left,centers,?_,?_⟩,size⟩
  · intro c
    rcases A.equation c with empty|⟨a,vertical⟩|⟨l,oblique⟩
    · have h:=filt c (fun _ => False) (fun p hp => empty p hp)
      simpa using (h.trans (by simp))
    · exact (filt c _ vertical).trans ((residual_vertical f a).trans (Nat.le_add_left _ _))
    · exact (filt c _ oblique).trans (residual_oblique f dx l)
  · intro z hz
    rcases mem_union.mp (mem_inter.mp hz).2 with outside|affine
    · exact Or.inr ⟨A.infinity,mem_insert_self ..,A.off z (mem_filter.mp outside).2⟩
    obtain ⟨p,hp,rfl⟩:=mem_map.mp affine
    by_cases r:p∈P
    · exact Or.inl (mem_inter.mpr ⟨hz,mem_map.mpr ⟨p,r,rfl⟩⟩)
    right
    by_cases v:p.1∈verticals f
    · exact ⟨A.vertical p.1,mem_insert_of_mem (mem_union_left _ (mem_image_of_mem _ v)),(A.onVertical _ _).mpr rfl⟩
    · have h : ¬∀ l∈obliques f,p.2≠l.1*p.1+l.2 := fun h => r (mem_filter.mpr ⟨hp,v,h⟩)
      push Not at h
      obtain ⟨l,hl,eq⟩:=h
      exact ⟨A.oblique l,mem_insert_of_mem (mem_union_right _ (mem_image_of_mem _ hl)),(A.onOblique _ _).mpr eq⟩

#print axioms curve_cover

open Filter
open scoped Topology

section Family
variable {F : ℕ→Type*} [∀ i,Field (F i)] [∀ i,DecidableEq (F i)] [∀ i,Fintype (F i)]
    {v : ℕ→ℕ+} (D B : ∀ i,Finset (ZMod (v i))) (q : ℕ→ℕ)
    (A : ∀ i,Chart (F i) (ZMod (v i)) (D i))
    (f : ∀ i,Polynomial (Polynomial (F i))) (dx dy : ℕ→ℕ)
    (ne : ∀ i,f i≠0) (hx : ∀ i m,((f i).coeff m).natDegree≤dx i) (hy : ∀ i,(f i).natDegree≤dy i)
    (pf : ∀ i,Green33PerfectDifferenceCenters.Perfect (D i)) (sizes : ∀ i,(D i).card=q i+1)
    (budget : ∀ i,(B i).card≤q i+1) (pos : ∀ i,0<q i) (grow : Tendsto q atTop atTop)
    (reflects : ∀ a : ∀ i,ZMod (v i),Tendsto (fun i =>
      ((Green33PerfectDifferenceCenters.doubled (D i) (a i)+Green33PerfectDifferenceCenters.doubled (D i) (a i)).card:ℝ)/(2*(v i).val)) atTop (𝓝 (7/8)))

include ne hx hy pf sizes budget pos grow reflects

/-- The degree may grow provided its product with the doubled deficit fraction tends to zero. -/
theorem curve_escape
    (low : Tendsto (fun i => ((1+dx i+dy i:ℕ):ℝ)/(q i)) atTop (𝓝 0))
    (loss : Tendsto (fun i => ((1+dx i+dy i:ℕ):ℝ)*((split (D i) (B i)+split (D i) (B i))ᶜ.card:ℝ)/(q i:ℝ)^2) atTop (𝓝 0)) :
    Tendsto (fun i => ((B i∩locus (A i) (f i)).card:ℝ)/(q i)) atTop (𝓝 0) := by
  choose C h using fun i => curve_cover (A i) (f i) (ne i) (hx i) (B i)
  exact cover_escape D B _ q (fun i => dx i+(f i).natDegree) (fun i => 1+dx i+dy i)
    pf pos sizes budget (fun _ => inter_subset_left) C (fun i => by have := hy i; omega)
    (fun i => (h i).trans (Nat.add_le_add_left (hy i) _)) (fun _ => by omega) grow low loss reflects

/-- A critical doubled almost-cover escapes the zero locus of each uniformly
bounded nonzero polynomial in every affine Singer chart, including its line at infinity. -/
theorem bounded_escape (b : ℕ) (bx : ∀ i,dx i≤b) (by' : ∀ i,dy i≤b)
    (dense : Tendsto (fun i => ((split (D i) (B i)+split (D i) (B i)).card:ℝ)/(2*(v i).val))
      atTop (𝓝 1)) :
    Tendsto (fun i => ((B i∩locus (A i) (f i)).card:ℝ)/(q i)) atTop (𝓝 0) := by
  let w : ℕ := 1+b+b
  have small:=(tendsto_const_nhds (x:=(w:ℝ))).div_atTop ((tendsto_natCast_atTop_atTop (R:=ℝ)).comp grow)
  have defic:=small_deficit D B q pf sizes pos grow dense
  have cost:=defic.const_mul (w:ℝ)
  rw [mul_zero] at cost
  apply curve_escape D B q A f (fun _ => b) (fun _ => b) ne (fun i m => (hx i m).trans (bx i))
    (fun i => (hy i).trans (by' i)) pf sizes budget pos grow reflects small
  apply cost.congr
  intro i
  rw [mul_div_assoc]

end Family

#print axioms curve_escape
#print axioms bounded_escape
end Green33SingerCurveSupport
