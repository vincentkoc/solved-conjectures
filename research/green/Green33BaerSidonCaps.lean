import Green33BaerSidonFibers
import Green33SidonProfile
import Green33BaerDifferenceProfile
open Finset Green33Multiplicity Green33SidonProfile Green33BaerSubline Green33BaerForms
open scoped Pointwise
namespace Green33BaerSidonCaps
variable {G:Type*} [AddCommGroup G] [DecidableEq G]
/-- The diagonal is counted once as an unordered pair. -/
private theorem unordered_of_six (A:Finset G) (s:G) (six:reps A s≤6)
    (unique:∀ a∈A,∀ b∈A,a+a=b+b → a=b) : unorderedReps A s≤3 := by
  classical
  let S:=A.sym2.filter fun p => Sym2.lift ⟨(·+·),add_comm⟩ p=s
  let D:=(A×ˢA).filter fun p => p.1+p.2=s
  let f (p:G×G):=Sym2.mk p.1 p.2
  have maps:(D:Set (G×G)).MapsTo f S := by
    rintro ⟨a,b⟩ h
    obtain ⟨ha,hb⟩:=mem_filter.mp h
    exact mem_filter.mpr ⟨mk_mem_sym2_iff.mpr (mem_product.mp ha),hb⟩
  have point (p:Sym2 G) (hp:p∈S) :
      2≤(D.filter fun t => f t=p).card+(if p.IsDiag then 1 else 0) := by
    obtain ⟨a,b⟩:=p
    obtain ⟨h,eq⟩:=mem_filter.mp hp
    obtain ⟨ha,hb⟩:=mk_mem_sym2_iff.mp h
    change a+b=s at eq
    have h₁:(a,b)∈D.filter (fun t => f t=Sym2.mk a b) :=
      mem_filter.mpr ⟨mem_filter.mpr ⟨mem_product.mpr ⟨ha,hb⟩,eq⟩,rfl⟩
    by_cases ab:a=b
    · subst b
      have pos:=card_pos.mpr ⟨_,h₁⟩
      simpa using pos
    · have h₂:(b,a)∈D.filter (fun t => f t=Sym2.mk a b) :=
        mem_filter.mpr ⟨mem_filter.mpr ⟨mem_product.mpr ⟨hb,ha⟩,(add_comm _ _).trans eq⟩,Sym2.eq_swap⟩
      have two:=one_lt_card.mpr ⟨_,h₁,_,h₂,fun eq => ab (congrArg Prod.fst eq)⟩
      exact two.trans_le (Nat.le_add_right _ _)
  have one:(S.filter Sym2.IsDiag).card≤1 := by
    apply card_le_one_iff.mpr
    rintro ⟨a,b⟩ ⟨c,d⟩ ha hc
    obtain ⟨sa,hb⟩:=mem_filter.mp ha
    obtain ⟨sc,hd⟩:=mem_filter.mp hc
    have ab:a=b:=by simpa using hb
    have cd:c=d:=by simpa using hd
    subst b;subst d
    have eq:=unique a (mk_mem_sym2_iff.mp (mem_filter.mp sa).1).1 c
      (mk_mem_sym2_iff.mp (mem_filter.mp sc).1).1 ((mem_filter.mp sa).2.trans (mem_filter.mp sc).2.symm)
    rw [eq]
  have h:=sum_le_sum point
  rw [sum_add_distrib,←card_eq_sum_card_fiberwise maps] at h
  have cnt:(∑ p∈S,if p.IsDiag then 1 else 0)=(S.filter Sym2.IsDiag).card := by simp
  simp only [sum_const,nsmul_eq_mul,cnt] at h
  change D.card≤6 at six
  change S.card≤3
  norm_cast at h
  omega

open Green33BaerSidonFibers Green33SingerAllCharacteristics Green33PrimeSingerIncidence
variable {F E K:Type*} [Field F] [Fintype F] [Field E] [Fintype E] [Field K] [Fintype K]
    [Algebra F E] [Algebra E K] [Algebra F K] [IsScalarTower F E K]

/-- The rational points in any cyclic Singer chart, after a cyclic automorphism. -/
noncomputable def base {D:Finset (ZMod (order E))} (frame:K≃ₗ[E](Fin 3→E))
    (S:SingerMap E K D) (e:ZMod (order E)≃+ZMod (order E)) :=
  layer (fun u => e (S.tag u)) (rationalForm F frame) 0

/-- In every square-span-six Baer frame, three unordered pairs (with the
diagonal counted once) and six ordered pairs suffice at every cyclic sum. -/
theorem cyclic_caps (square:Fintype.card E=(Fintype.card F)^2) (frame:K≃ₗ[E](Fin 3→E))
    (rank:Module.finrank F ((rationalForm F frame)*(rationalForm F frame))=6)
    {D:Finset (ZMod (order E))} (S:SingerMap E K D) (e:ZMod (order E)≃+ZMod (order E)) :
    let B:=base (F:=F) frame S e
    B.card=(Fintype.card F)^2+Fintype.card F+1 ∧
      ∀ s,reps B s≤6 ∧ unorderedReps B s≤3 := by
  classical
  let tag (u:Kˣ):=e (S.tag u)
  let B:=base (F:=F) frame S e
  have tw:Module.finrank F E=2 := (Nat.pow_right_inj Fintype.one_lt_card).mp
    ((Module.card_eq_pow_finrank (K:=F) (V:=E)).symm.trans square)
  have same (u v:Kˣ) : tag u=tag v ↔ ∃ r:E,(u:K)=r • (v:K) := e.injective.eq_iff.trans (S.same _ _)
  have map (a b:Kˣ) : tag (a*b)=tag a+tag b := by simp [tag,S.mul]
  have law (a b c d:Kˣ) (h:tag a+tag b=tag c+tag d) : tag (a*b)=tag (c*d) := by rwa [map,map]
  have lifts (x) (hx:x∈B) : ∃ u:Kˣ,(u:K)∈rationalForm F frame ∧ tag u=x := by
    simpa only [B,base,layer,mem_filter,mem_univ,true_and,zero_add,tag,eq_comm] using hx
  refine ⟨layer_card frame tag same 0,fun s => ?_⟩
  have six:=six_ordered frame tw rank tag same law B lifts s
  refine ⟨six,unordered_of_six _ _ six ?_⟩
  rintro x hx y hy eq
  obtain ⟨a,_,rfl⟩:=lifts _ hx
  obtain ⟨b,_,rfl⟩:=lifts _ hy
  exact diagonal_tag (by rw [frame.finrank_eq];simp) tag same _ _ (law _ _ _ _ eq)
#print axioms cyclic_caps


open Filter Green33BaerDifferenceProfile Green33ReflectedLayers Green33BaerCyclic
open scoped Topology
/-- A full cyclic chart of a square-span-six rational subplane, in base coordinates. -/
def IsRankSixBase (F E K:Type*) [Field F] [Field E] [Fintype E] [Field K]
    [Algebra F E] [Algebra E K] [Algebra F K] [IsScalarTower F E K]
    (B:Finset (ZMod (positiveOrder E))) : Prop :=
  ∃ (frame:K≃ₗ[E](Fin 3→E)) (D:Finset (ZMod (order E))) (S:SingerMap E K D)
    (e:ZMod (order E)≃+ZMod (order E)), B=base (F:=F) frame S e ∧
    Module.finrank F ((rationalForm F frame)*(rationalForm F frame))=6

/-- Almost-full retention of a square-span-six layer in a critical basis forces
the undoubled cyclic profile to have asymptotically zero mean squared error. -/
theorem baer_profile {ι:Type*} {l:Filter ι} (F E K:ι→Type*)
    [∀ i,Field (F i)] [∀ i,Fintype (F i)] [∀ i,Field (E i)] [∀ i,Fintype (E i)]
    [∀ i,Field (K i)] [∀ i,Fintype (K i)] [∀ i,Algebra (F i) (E i)] [∀ i,Algebra (E i) (K i)]
    [∀ i,Algebra (F i) (K i)] [∀ i,IsScalarTower (F i) (E i) (K i)]
    (square:∀ i,Fintype.card (E i)=(Fintype.card (F i))^2)
    (grow:Tendsto (fun i => Fintype.card (F i)) l atTop)
    (B:∀ i,Finset (ZMod (positiveOrder (E i)))) (T:∀ i,Finset (ZMod (modulus (E i))))
    (geometry:∀ i,IsRankSixBase (F i) (E i) (K i) (B i)) (z:∀ i,ZMod (modulus (E i)))
    (full:∀ i,T i+T i=univ)
    (critical:Tendsto (fun i => ((T i).card:ℝ)/Real.sqrt (modulus (E i))) l (𝓝 (Real.sqrt 2)))
    (missing:Tendsto (fun i => (((placed (doubleHom (positiveOrder (E i))) (z i) (B i))\(T i)).card:ℝ)/
      (Fintype.card (F i):ℝ)^2) l (𝓝 0)) :
    Tendsto (fun i => variance (B i)/(order (E i):ℝ)) l (𝓝 0) := by
  let t i:=Fintype.card (F i)
  let v i:=positiveOrder (E i)
  have caps i : (B i).card=(t i)^2+t i+1 ∧ ∀ s,reps (B i) s≤6 ∧ unorderedReps (B i) s≤3 := by
    obtain ⟨frame,D,S,e,h,rank⟩:=geometry i
    rw [h]
    exact cyclic_caps (square i) frame rank S e
  have ord i : (v i).val=(t i)^4+(t i)^2+1 := by
    change (Fintype.card (E i))^2+Fintype.card (E i)+1=_
    rw [square]
    dsimp only [t];ring
  have tp i : (0:ℝ)<t i:=by exact_mod_cast Fintype.card_pos (α:=F i)
  have tr:=((tendsto_natCast_atTop_atTop (R:=ℝ)).comp grow)
  have tiny:=(tendsto_const_nhds (x:=(1:ℝ))).div_atTop tr
  have one:=tendsto_const_nhds (f:=l) (x:=(1:ℝ))
  have scaled:Tendsto (fun i => ((v i).val:ℝ)/(t i:ℝ)^4) l (𝓝 1) := by
    have h:=(one.add (tiny.pow 2)).add (tiny.pow 4)
    norm_num at h
    apply h.congr
    intro i
    simp only [ord,Nat.cast_add,Nat.cast_pow,Nat.cast_one]
    change 1+((t i:ℝ)^2)⁻¹+((t i:ℝ)^4)⁻¹=_
    field_simp [(tp i).ne']
  have rt:Tendsto (fun i => Real.sqrt (v i)/(t i:ℝ)^2) l (𝓝 1) := by
    have h:=scaled.sqrt
    rw [Real.sqrt_one] at h
    apply h.congr
    intro i
    rw [Real.sqrt_div (by positivity)]
    congr 1
    rw [show (t i:ℝ)^4=((t i:ℝ)^2)^2 by ring,Real.sqrt_sq (sq_nonneg _)]
  have seed:Tendsto (fun i => ((B i).card:ℝ)/(t i:ℝ)^2) l (𝓝 1) := by
    have h:=(one.add tiny).add (tiny.pow 2)
    norm_num at h
    apply h.congr
    intro i
    simp only [(caps i).1,Nat.cast_add,Nat.cast_pow,Nat.cast_one]
    change 1+(t i:ℝ)⁻¹+((t i:ℝ)^2)⁻¹=_
    field_simp [(tp i).ne']
  refine critical_profile v (fun i => modulus (E i)) B T (fun i => doubleHom (v i))
    (fun i => (double_coordinates (v i) 0).1) z 6 2 (fun _ => le_rfl)
    (fun i s => ((caps i).2 s).1) full ?_ ?_ critical ?_
  · apply tendsto_atTop_mono _ grow
    intro i
    rw [ord]
    have hh:=Nat.le_self_pow (by decide : 2≠0) (t i)
    change t i≤_;omega
  · have h:=seed.div rt (by norm_num)
    rw [div_one] at h
    exact h.congr fun i => div_div_div_cancel_right₀ (pow_ne_zero 2 (tp i).ne') _ _
  · have h:=missing.div rt (by norm_num)
    rw [zero_div] at h
    exact h.congr fun i => div_div_div_cancel_right₀ (pow_ne_zero 2 (tp i).ne') _ _
#print axioms baer_profile

end Green33BaerSidonCaps
