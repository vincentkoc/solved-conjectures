import Green51CodimensionTwo

/-! # Linear four-colourings for missing directions of large odd girth -/

open Finset Green53ParityThreshold Green51NearThreshold
open scoped Classical Pointwise
namespace Green51OddDirections
variable {G : Type*} [AddCommGroup G] [Module F G]

/-- Two directions outside a shortest odd circuit can differ inside its span
only by zero or by the sum of two of its elements. The final cardinality
corresponds to using the total basis sum as one of the two elements. -/
private theorem outside_weight (k : ℕ) (D : Set G) (B : Finset G) (sz : B.card=2*k)
    (bs : (B:Set G)⊆D) (d : G) (hd : d∈D) (db : d∉B) (sd : ∑ b∈B,b=d)
    (z : G) (hz : z∈D) (zb : z∉B) (zd : z≠d)
    (short : ∀ T : Finset G, (T:Set G)⊆D → 2∣T.card → T.card<2*k → (∑ x∈T,x)∉D)
    (T : Finset G) (tb : T⊆B) (out : z+(∑ x∈T,x)∈D) :
    T.card=0 ∨ T.card=2 ∨ T.card=2*k-1 := by
  classical
  by_contra! bad
  have le := (card_le_card tb).trans_eq sz
  by_cases even : 2∣T.card
  · let V := B\T
    have dv : d∉V := fun h => db (mem_sdiff.mp h).1
    have zv : z∉insert d V := by simp [zd,V,zb]
    have sub : (↑(insert z (insert d V)):Set G)⊆D := by
      simpa only [coe_insert,Set.insert_subset_iff] using
        And.intro hz (And.intro hd (show (V:Set G)⊆D from fun _ h => bs (mem_sdiff.mp h).1))
    have card : (insert z (insert d V)).card=2*k-T.card+2 := by
      rw [card_insert_of_notMem zv,card_insert_of_notMem dv]
      simp [V,card_sdiff_of_subset tb,sz,Nat.add_assoc]
    have sum : d+(∑ b∈V,b)=∑ b∈T,b := by
      have eq := sum_sdiff tb (f:=id)
      change (∑ b∈V,b)+(∑ b∈T,b)=∑ b∈B,b at eq
      rw [←sd,←eq,add_right_comm,ZModModule.add_self,zero_add]
    apply short _ sub (by rw [card];omega) (by rw [card];omega)
    simpa only [sum_insert zv,sum_insert dv,sum] using out
  · have zt : z∉T := fun h => zb (tb h)
    have card := card_insert_of_notMem zt
    have sub : (↑(insert z T):Set G)⊆D := by
      simpa only [coe_insert,Set.insert_subset_iff] using
        And.intro hz (show (T:Set G)⊆D from fun _ h => bs (tb h))
    apply short _ sub (by omega) (by omega)
    simpa only [sum_insert zt] using out


/-- Four independent coordinates supply two disjoint pairs. Both translated
pair sums cannot be missing, since their difference has weight four. -/
private theorem absent_pair (k : ℕ) (hk : 2≤k) (D : Set G) (B : Finset G)
    (sz : B.card=2*k) (bs : (B:Set G)⊆D) (d : G) (hd : d∈D) (db : d∉B) (sd : ∑ b∈B,b=d)
    (z : G) (l : G →ₗ[F] F) (lz : l z≠0) (lb : ∀ b∈B,l b=0)
    (short : ∀ T : Finset G, (T:Set G)⊆D → 2∣T.card → T.card<2*k → (∑ x∈T,x)∉D) :
    ∃ I⊆B,I.card=2 ∧ z+(∑ b∈I,b)∉D := by
  classical
  obtain ⟨I,ib,ic⟩ := exists_subset_card_eq (by omega : 2≤B.card)
  obtain ⟨J,jd,jc⟩ := exists_subset_card_eq (show 2≤(B\I).card by rw [card_sdiff_of_subset ib]; omega)
  have jb : J⊆B := fun _ h => (mem_sdiff.mp (jd h)).1
  have dis : Disjoint I J := disjoint_left.mpr (fun _ hi hj => (mem_sdiff.mp (jd hj)).2 hi)
  by_contra! all
  have hi := all I ib ic
  have hj := all J jb jc
  let x := z+(∑ b∈I,b)
  have lx : l x=l z := by simp [x,map_sum,sum_eq_zero (fun b hb => lb b (ib hb))]
  have ld : l d=0 := by rw [←sd,map_sum]; exact sum_eq_zero lb
  have xb : x∉B := fun h => lz (lx.symm.trans (lb _ h))
  have xd : x≠d := fun h => lz (lx.symm.trans ((congrArg l h).trans ld))
  have out : x+(∑ b∈I∪J,b)∈D := by
    rw [sum_union dis]
    have eq : x+(∑ b∈I,b)=z := by dsimp [x]; rw [add_assoc,ZModModule.add_self,add_zero]
    rwa [←add_assoc,eq]
  have bad := outside_weight k D B sz bs d hd db sd x hi xb xd short (I∪J) (union_subset ib jb) out
  rw [card_union_of_disjoint dis,ic,jc] at bad
  omega

private theorem outside_colour (k : ℕ) (hk : 0<k) (B I T : Finset G) (tb : T⊆B)
    (sz : B.card=2*k) (ic : I.card=2) (different : T≠I)
    (weight : T.card=0 ∨ T.card=2 ∨ T.card=2*k-1)
    (z : G) (f : G →ₗ[F] F×F) (fz : f z≠0) (same : f (∑ b∈B,b)=f z)
    (nb : ∀ b∈B,f b≠0) (ordinary : ∀ b∈B,b∉I → f b=f z) :
    f (z+∑ b∈T,b)≠0 := by
  classical
  have cancel (a b : F×F) : a+(a+b)=b := by rw [←add_assoc,ZModModule.add_self,zero_add]
  rcases weight with empty|pair|large
  · simpa [card_eq_zero.mp empty] using fz
  · obtain ⟨x,y,xy,rfl⟩ := card_eq_two.mp pair
    have xb := tb (mem_insert_self x {y})
    have yb := tb (mem_insert_of_mem (mem_singleton_self y))
    have missing : x∉I ∨ y∉I := by
      by_contra! both
      apply different
      exact eq_of_subset_of_card_le (by simpa only [insert_subset_iff,singleton_subset_iff] using both) (by omega)
    rw [sum_pair xy,map_add,map_add]
    rcases missing with left|right
    · rw [ordinary x xb left,cancel]; exact nb y yb
    · rw [ordinary y yb right,add_comm (f x) _,cancel]; exact nb x xb
  · have one : (B\T).card=1 := by rw [card_sdiff_of_subset tb];omega
    obtain ⟨j,hj⟩ := card_eq_one.mp one
    have jb : j∈B := (mem_sdiff.mp (show j∈B\T by rw [hj];simp)).1
    have sum := sum_sdiff tb (f:=id)
    change (∑ b∈B\T,b)+(∑ b∈T,b)=∑ b∈B,b at sum
    rw [hj,sum_singleton] at sum
    have relation := congrArg f sum
    change f (j+∑ b∈T,b)=f (∑ b∈B,b) at relation
    rw [map_add,same] at relation
    rw [map_add,←relation,add_assoc,ZModModule.add_self,add_zero]
    exact nb j jb

/-- Colour two marked directions and the unmarked directions by the three
nonzero vectors. The whole even basis sum has the unmarked colour. -/
private theorem marked_projection {G : Type*} [AddCommGroup G] [Module F G]
    (B I : Finset G) (z : G) (zb : z∉B) (ib : I⊆B) (ic : I.card=2)
    (even : 2∣B.card) (ind : LinearIndepOn F id (↑(insert z B):Set G)) :
    ∃ f : G →ₗ[F] F×F, f z≠0 ∧ f (∑ b∈B,b)=f z ∧ (∀ b∈B,f b≠0) ∧
      ∀ b∈B,b∉I → f b=f z := by
  classical
  obtain ⟨i,j,ij,rfl⟩ := card_eq_two.mp ic
  have hi : i∈B := ib (mem_insert_self _ _)
  have hj : j∈B := ib (mem_insert_of_mem (mem_singleton_self _))
  have zi : z≠i := fun h => zb (h ▸ hi)
  have zj : z≠j := fun h => zb (h ▸ hj)
  let red : F×F := (1,0)
  let w (x : G) : F×F := if x=i then (0,1) else if x=j then (1,1) else red
  obtain ⟨f,hf⟩ := extend_values ind w
  have colour (x) (hx : x∈B) : f x=w x := hf x (mem_insert_of_mem hx)
  have fz : f z=red := by simpa [w,zi,zj] using hf z (mem_insert_self _ _)
  have rest (b : G) (hb : b∈B) (out : b∉({i,j}:Finset G)) : f b=red := by
    have n : b≠i ∧ b≠j := by simpa using out
    simp [colour b hb,w,n.1,n.2]
  refine ⟨f,?_,?_,?_,fun b hb h => (rest b hb h).trans fz.symm⟩
  · rw [fz]; decide
  · have even' : 2∣(B\{i,j}).card := by rw [card_sdiff_of_subset ib,ic]; omega
    have zeros : (∑ b∈B\{i,j}, f b)=0 := by
      rw [sum_eq_card_nsmul (fun b h => rest b (mem_sdiff.mp h).1 (mem_sdiff.mp h).2)]
      obtain ⟨a,ha⟩ := even'
      rw [ha,mul_comm 2 a,mul_nsmul,two_nsmul,ZModModule.add_self]
    rw [map_sum,←sum_sdiff ib (f:=f),zeros,zero_add,sum_pair ij,fz,colour i hi,colour j hj]
    simp [w,Ne.symm ij,red]
    rfl
  · intro b hb
    rw [colour b hb]
    dsimp only [w]; split_ifs <;> decide


/-- In rank at most one greater than a shortest odd circuit's rank, absence
of shorter odd relations gives a linear four-colouring for odd girth at least five. -/
theorem two_coordinate_projection [Module.Finite F G] (k : ℕ) (hk : 2≤k)
    (rank : Module.finrank F G≤2*k+1) (D : Set G)
    (short : ∀ T : Finset G, (T:Set G)⊆D → 2∣T.card → T.card<2*k → (∑ x∈T,x)∉D) :
    ∃ f : G →ₗ[F] F×F, ∀ x∈D,f x≠0 := by
  classical
  by_cases bip : ∃ l : G →ₗ[F] F, ∀ x∈D,l x=1
  · obtain ⟨l,ok⟩ := bip
    exact ⟨l.prod 0,fun x hx h => one_ne_zero ((ok x hx).symm.trans (congrArg Prod.fst h))⟩
  obtain ⟨C,sub,card,span,ind⟩ := Submodule.exists_finset_span_eq_linearIndepOn F D
  obtain ⟨l,hl⟩ := Module.exists_dual_forall_apply_eq_one ind
  change ∀ x∈C,l x=1 at hl
  have bad : ¬∀ x∈D,l x=1 := fun h => bip ⟨l,h⟩
  push Not at bad
  obtain ⟨d,hd,nd⟩ := bad
  have db : d∉C := fun h => nd (hl d h)
  have rep (x : G) (hx : x∈D) : ∃ T⊆C,∑ b∈T,b=x :=
    subset_sum C x (span.symm ▸ Submodule.subset_span hx)
  obtain ⟨B,bc,sd⟩ := rep d hd
  have even : 2∣B.card := by
    have bit (x : F) : x=0 ∨ x=1 := by fin_cases x <;> first | exact Or.inl rfl | exact Or.inr rfl
    have eq := congrArg l sd
    change l (∑ x∈B,x)=l d at eq
    rw [map_sum,(bit (l d)).resolve_right nd,sum_eq_card_nsmul (fun b hb => hl _ (bc hb))] at eq
    simpa only [nsmul_eq_mul,mul_one,ZMod.natCast_eq_zero_iff] using eq
  have upper := card.trans_le ((Submodule.finrank_le _).trans rank)
  have bs : (B:Set G)⊆D := fun _ h => sub (bc h)
  have bcsize := card_le_card bc
  have sz : B.card=2*k := by
    have lo : ¬B.card<2*k := fun h => short _ bs even h (sd ▸ hd)
    omega
  have db' : d∉B := fun h => db (bc h)
  have inside (T : Finset G) (tb : T⊆B) (out : (∑ t∈T,t)∈D) :=
    inside_frame k D B sz bs d hd db' sd short T tb out
  by_cases same : C=B
  · obtain ⟨f,on,atSum⟩ := frame_projection B (card_pos.mp (by omega)) (same ▸ ind)
    refine ⟨f,fun x hx => ?_⟩
    obtain ⟨T,tc,e⟩ := rep x hx
    rcases inside T (same ▸ tc) (e ▸ hx) with member|eq
    · exact on x (e ▸ member)
    · exact (e.symm.trans (eq.trans sd.symm)) ▸ atSum
  have one : (C\B).card=1 := by
    rw [card_sdiff_of_subset bc]
    have strict : B.card<C.card := by
      by_contra! h; exact same (eq_of_subset_of_card_le bc h).symm
    omega
  obtain ⟨z,single⟩ := card_eq_one.mp one
  have zdf := mem_sdiff.mp (show z∈C\B by rw [single]; simp)
  have cb : C=insert z B := by
    ext x
    by_cases hx : x∈B
    · simp [hx,bc hx]
    · have eq : x∈C\B ↔ x∈({z}:Finset G) := by rw [single]
      simpa [hx] using eq
  obtain ⟨sep,hs⟩ := extend_values ind (fun x : G => if x=z then (1:F) else 0)
  have sepz : sep z≠0 := by simp [hs z zdf.1]
  have sepb (b) (hb : b∈B) : sep b=0 := by
    have ne : b≠z := fun e => zdf.2 (e ▸ hb)
    simpa [ne] using hs b (bc hb)
  obtain ⟨I,ib,ic,absent⟩ := absent_pair k hk D B sz bs d hd db' sd z sep sepz sepb short
  obtain ⟨f,fz,fs,nb,rest⟩ := marked_projection B I z zdf.2 ib ic (sz ▸ even) (cb ▸ ind)
  refine ⟨f,fun x hx => ?_⟩
  obtain ⟨T,tc,e⟩ := rep x hx
  have restB {x : G} (xt : x∈T) (nx : x≠z) : x∈B := by
    have mem := tc xt; rw [cb] at mem
    exact (mem_insert.mp mem).resolve_left nx
  by_cases zt : z∈T
  · let U := T.erase z
    have ub : U⊆B := fun _ h => restB (mem_erase.mp h).2 (mem_erase.mp h).1
    have relation : z+(∑ b∈U,b)=x := by
      rw [←e]; exact add_sum_erase _ id zt
    have yy := relation ▸ hx
    have weight := outside_weight k D B sz bs d hd db' sd z (sub zdf.1) zdf.2
      (fun e => db (e ▸ zdf.1)) short U ub yy
    rw [←relation]
    exact outside_colour k (by omega) B I U ub sz ic (fun h => absent (h ▸ yy)) weight z f fz fs nb rest
  · have tb : T⊆B := fun y hy => restB hy (fun eq => zt (eq ▸ hy))
    rcases inside T tb (e ▸ hx) with member|eq
    · exact nb x (e ▸ member)
    · have xd := e.symm.trans eq
      exact (xd.trans sd.symm) ▸ fs.symm ▸ fz

end Green51OddDirections
#print axioms Green51OddDirections.two_coordinate_projection
