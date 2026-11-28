import Green50QuadraticBogolyubov

/-!
# Polar values in sums of dense subsets of quadratic graphs

Four prescribed input translates meet a set of density greater than three quarters.
Applying this to a parallelogram recovers its polar value in four graph summands.
-/
open Finset
open scoped Pointwise
namespace Green50DenseQuadraticGraphs
private theorem translate_pattern {U : Type*} [AddCommGroup U] [Fintype U] [DecidableEq U]
    (A F : Finset U) (h : F.card * Aᶜ.card < Fintype.card U) :
    ∃ x, ∀ a ∈ F, x+a ∈ A := by
  classical
  let bad (a : U) := Aᶜ.image (fun y => y-a)
  let excluded := F.biUnion bad
  have hcard (a : U) : (bad a).card = Aᶜ.card :=
    card_image_of_injective _ (fun _ _ e => sub_left_inj.mp e)
  have small : excluded.card < Fintype.card U := calc
    _ ≤ ∑ a ∈ F, (bad a).card := card_biUnion_le
    _ = F.card * Aᶜ.card := by simp [hcard]
    _ < _ := h
  obtain ⟨x,_,hx⟩ := exists_mem_notMem_of_card_lt_card (t := (univ : Finset U)) (by simpa using small)
  refine ⟨x,?_⟩
  intro a ha
  by_contra hnot
  exact hx (mem_biUnion.mpr ⟨a,ha,mem_image.mpr ⟨x+a,mem_compl.mpr hnot,add_sub_cancel_right _ _⟩⟩)

private theorem twice {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] (x:E) : x+x=0 := by
  rw [← two_smul (ZMod 2) x,show (2:ZMod 2)=0 by decide,zero_smul]

/-- Every polar value survives arbitrary deletion of fewer than one quarter of the graph. -/
theorem vertical_survives {U V : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    [Fintype U] [DecidableEq U] [AddCommGroup V] [Module (ZMod 2) V] [DecidableEq V]
    (D : Finset U) (f : U → V) (B : U →ₗ[ZMod 2] U →ₗ[ZMod 2] V)
    (hf : ∀ a x, f x + f (x+a) = B a x + (f 0 + f a)) (hd : 4*Dᶜ.card < Fintype.card U)
    (a b : U) : (0,B a b) ∈ (4:ℕ) • D.image (fun x => (x,f x)) := by
  classical
  let F : Finset U := {0,a,b,b+a}
  have hF : F.card ≤ 4 := by
    dsimp [F]
    grw [card_insert_le,card_insert_le,card_insert_le]; simp
  obtain ⟨x,hx⟩ := translate_pattern D F ((Nat.mul_le_mul_right _ hF).trans_lt hd)
  let T := D.image (fun x => (x,f x))
  have ht (j : U) (hj : j∈F) : (x+j,f (x+j)) ∈ T := mem_image_of_mem _ (hx j hj)
  have h0 : (x,f x) ∈ T := by simpa using ht 0 (by simp [F])
  have h1 := ht a (by simp [F])
  have h2 := ht b (by simp [F])
  have h3 := ht (b+a) (by simp [F])
  have hsum := Finset.add_mem_add (Finset.add_mem_add h0 h1) (Finset.add_mem_add h2 h3)
  have he : ((x,f x)+(x+a,f (x+a)))+((x+b,f (x+b))+(x+(b+a),f (x+(b+a)))) = (0,B a b) := by
    apply Prod.ext
    · change (x+(x+a))+((x+b)+(x+(b+a))) = 0
      calc
        _ = (x+x)+(x+x)+(a+a)+(b+b) := by abel
        _ = 0 := by simp [twice]
    · change (f x+f (x+a))+(f (x+b)+f (x+(b+a))) = B a b
      rw [←add_assoc x b a,hf,hf,map_add]
      calc
        _ = B a b + (B a x+B a x) + ((f 0+f a)+(f 0+f a)) := by abel
        _ = _ := by simp [twice]
  rw [he] at hsum
  simpa only [show (4:ℕ)=2+2 by decide,add_nsmul,two_nsmul] using hsum

private theorem dense_slice {U : Type*} [AddCommGroup U] [Module (ZMod 2) U] [Fintype U] [DecidableEq U]
    (D : Finset U) (H : Submodule (ZMod 2) U) [Fintype H] (hd : Fintype.card U < 2*D.card) :
    ∃ x : U, Fintype.card H < 2*(univ.filter (fun h:H => x+h.val ∈ D)).card := by
  classical
  by_contra! hn
  have card (t : H) : (univ.filter (fun x : U => x+t.val ∈ D)).card = D.card := by
    apply card_bij' (fun x _ => x+t.val) (fun y _ => y-t.val)
    · intro x hx; exact (mem_filter.mp hx).2
    · intro y hy; simpa using hy
    · intro x _; simp
    · intro y _; simp
  have hav : (∑ x : U, (univ.filter (fun h:H => x+h.val ∈ D)).card) = Fintype.card H * D.card := calc
    _ = ∑ t : H, ∑ x : U, (if x+t.val ∈ D then 1 else 0) := by
      simp only [Finset.card_filter]
      exact sum_comm
    _ = ∑ _t : H, D.card := by
      apply sum_congr rfl
      intro t _
      rw [←Finset.card_filter]
      exact card t
    _ = _ := by simp
  have hp : (∑ x : U, 2*(univ.filter (fun h:H => x+h.val ∈ D)).card) ≤ ∑ _x : U, Fintype.card H :=
    sum_le_sum fun x _ => hn x
  rw [←mul_sum,hav] at hp
  simp only [sum_const,card_univ,nsmul_eq_mul] at hp
  have := Nat.mul_lt_mul_of_pos_right hd (Fintype.card_pos (α:=H))
  nlinarith only [this,hp]

section Compression

open Green50QuadraticFibres Green50QuadraticFlats Green50QuadraticBogolyubov
local notation "F₂" => ZMod 2
variable {U V : Type*} [AddCommGroup U] [Module F₂ U] [Fintype U] [DecidableEq U]
    [AddCommGroup V] [Module F₂ V] [Fintype V] [DecidableEq V]

/-- A dense coset supplies the horizontal differences. Each polar value takes four
retained graph points and each horizontal difference takes two. -/
theorem dense_graph_flat (D : Finset U) (f : U → V) (B : U →ₗ[F₂] U →ₗ[F₂] V)
    (hf : ∀ a x, f x + f (x+a) = B a x + (f 0 + f a))
    (hd : 4*Dᶜ.card < Fintype.card U) (k : ℕ) :
    ∃ (S : Submodule F₂ (U × V)) (m : ℕ), m ≤ Module.finrank F₂ V ∧
      (∀ p ∈ S, p ∈ (4*k+2) • D.image (fun x => (x,f x))) ∧
      k*Module.finrank F₂ U + k*m ≤ k*Module.finrank F₂ S + 2*m := by
  classical
  let T := D.image (fun x => (x,f x))
  obtain ⟨H,W,hiso,hfree,hpaid⟩ := polar_compression f B hf k
  have hv : vertical B ⊆ (4:ℕ) • T := by
    rintro _ h
    obtain ⟨⟨a,b⟩,_,rfl⟩ := mem_image.mp h
    exact vertical_survives D f B hf hd a b
  have hW (w : W) : ((0:U),w.val) ∈ (4*k) • T := by
    have h := nsmul_subset_nsmul_left (n := k) hv (hfree w)
    simpa only [← mul_smul,Nat.mul_comm k 4] using h
  have hD : Fintype.card U < 2*D.card := by rw [card_compl] at hd; omega
  obtain ⟨o,hslice⟩ := dense_slice D H hD
  let g (x : U) := f (o+x)
  have hquad (a x : U) : g x + g (x+a) = B a x + (g 0+g a) := by
    dsimp [g]
    rw [←add_assoc, hf, map_add, add_zero, hf a o]
    abel
  let L := quotientSlope g B hquad H W hiso
  obtain ⟨S,hS,hdim⟩ := graph_lift H W L
  refine ⟨S,Module.finrank F₂ W,W.finrank_le,?_,?_⟩
  · rintro ⟨u,v⟩ hp
    obtain ⟨h,hu,he⟩ := hS _ hp
    change u = h.val at hu
    subst u
    change W.mkQ v = W.mkQ (g h.val + g 0) at he
    let A := univ.filter (fun y:H => o+y.val ∈ D)
    have hsmall : ({0,h}:Finset H).card * Aᶜ.card < Fintype.card H := by
      have hc : ({0,h}:Finset H).card ≤ 2 := by grw [card_insert_le]; simp
      refine (Nat.mul_le_mul_right Aᶜ.card hc).trans_lt ?_
      change Fintype.card H < 2*A.card at hslice
      rw [card_compl]
      have hcap := A.card_le_univ
      omega
    obtain ⟨y,hy⟩ := translate_pattern A {0,h} hsmall
    have hy0 : o+y.val ∈ D := (mem_filter.mp (show y ∈ A by simpa using hy 0 (by simp))).2
    have hyh : o+(y+h).val ∈ D := (mem_filter.mp (hy h (by simp))).2
    let z := g y.val + g (y+h).val
    have hz : (h.val,z) ∈ (2:ℕ) • T := by
      have hs := add_mem_add (mem_image_of_mem (fun x => (x,f x)) hy0)
        (mem_image_of_mem (fun x => (x,f x)) hyh)
      have heq : ((o+y.val),f (o+y.val)) + ((o+(y+h).val),f (o+(y+h).val)) = (h.val,z) := by
        apply Prod.ext
        · change o+y.val+(o+(y.val+h.val))=h.val
          calc
            _ = (o+o)+(y.val+y.val)+h.val := by abel
            _ = _ := by simp [twice]
        · rfl
      rw [heq] at hs
      simpa only [two_nsmul] using hs
    have hzq : W.mkQ z = W.mkQ (g h.val + g 0) := by
      change W.mkQ (g y.val + g (y.val+h.val)) = _
      have hzero : W.mkQ (B h.val y.val) = 0 := (Submodule.Quotient.mk_eq_zero W).mpr (hiso h y)
      rw [hquad,map_add,hzero,zero_add,add_comm (g 0)]
    let w : W := ⟨v-z,(Submodule.Quotient.eq W).mp (he.trans hzq.symm)⟩
    have hin := add_mem_add (hW w) hz
    have heq : ((0:U),w.val)+(h.val,z) = (h.val,v) := by
      apply Prod.ext
      · exact zero_add _
      · exact sub_add_cancel _ _
    rw [heq] at hin
    simpa only [add_nsmul] using hin
  · have hle := H.finrank_le
    have he : Module.finrank F₂ U = Module.finrank F₂ H + (Module.finrank F₂ U - Module.finrank F₂ H) :=
      (Nat.add_sub_of_le hle).symm
    have hs := congrArg (k * ·) hdim
    have hd' := congrArg (k * ·) he
    simp only [Nat.mul_add] at hs hd'
    omega

/-- Ten summands contain a linear subspace of at least the input dimension. -/
theorem tenfold_dense_flat (D : Finset U) (f : U → V) (B : U →ₗ[F₂] U →ₗ[F₂] V)
    (hf : ∀ a x, f x + f (x+a) = B a x + (f 0 + f a))
    (hd : 4*Dᶜ.card < Fintype.card U) :
    ∃ S : Submodule F₂ (U × V), (∀ p ∈ S, p ∈ (10:ℕ) • D.image (fun x => (x,f x))) ∧
      Module.finrank F₂ U ≤ Module.finrank F₂ S := by
  obtain ⟨S,m,_,hS,h⟩ := dense_graph_flat D f B hf hd 2
  exact ⟨S,hS,by omega⟩

/-- Six summands suffice with codimension at most twice the output dimension. -/
theorem sixfold_dense_flat (D : Finset U) (f : U → V) (B : U →ₗ[F₂] U →ₗ[F₂] V)
    (hf : ∀ a x, f x + f (x+a) = B a x + (f 0 + f a))
    (hd : 4*Dᶜ.card < Fintype.card U) :
    ∃ S : Submodule F₂ (U × V), (∀ p ∈ S, p ∈ (6:ℕ) • D.image (fun x => (x,f x))) ∧
      Module.finrank F₂ U ≤ Module.finrank F₂ S + Module.finrank F₂ V := by
  obtain ⟨S,m,hm,hS,h⟩ := dense_graph_flat D f B hf hd 1
  exact ⟨S,hS,by omega⟩

end Compression

section Embedded

open Green50Graphs
local notation "F₂" => ZMod 2

/-- If a set contains more than three quarters of a quadratic graph, its tenfold sum
contains a linear subspace of at least the dimension of the input space. -/
theorem tenfold_of_intersection {G : Type*} [AddCommGroup G] [Module F₂ G] [Fintype G] [DecidableEq G]
    (A : Finset G) (U V : Submodule F₂ G) (hc : IsCompl U V) (f : U → V)
    (B : U →ₗ[F₂] U →ₗ[F₂] V) (hf : ∀ a x, f x + f (x+a) = B a x + (f 0+f a))
    (hd : 3*(graph U V f).card < 4*(A ∩ graph U V f).card) :
    ∃ S : Submodule F₂ G, (S : Set G) ⊆ ↑((10:ℕ) • A) ∧ Module.finrank F₂ U ≤ Module.finrank F₂ S := by
  classical
  let e := U.prodEquivOfIsCompl V hc
  let j (x : U) : U × V := (x,f x)
  let emb (x : U) : G := e (j x)
  let D := univ.filter fun x : U => emb x ∈ A
  have inj : Function.Injective emb := fun _ _ h => congrArg Prod.fst (e.injective h)
  have eq : D.image emb = A ∩ graph U V f := by
    ext x
    constructor
    · rintro hx
      obtain ⟨u,hu,rfl⟩ := mem_image.mp hx
      exact mem_inter.mpr ⟨(mem_filter.mp hu).2,mem_image_of_mem _ (mem_univ u)⟩
    · intro hx
      obtain ⟨ha,hg⟩ := mem_inter.mp hx
      obtain ⟨u,_,hu⟩ := mem_image.mp hg
      exact mem_image.mpr ⟨u,mem_filter.mpr ⟨mem_univ _,(show emb u = x from hu).symm ▸ ha⟩,hu⟩
  have cardEq := congrArg Finset.card eq
  rw [card_image_of_injective _ inj] at cardEq
  rw [graph_card U V hc,Nat.card_eq_fintype_card,←cardEq] at hd
  have cap : D.card ≤ Fintype.card U := D.card_le_univ
  obtain ⟨S,hS,hsize⟩ := tenfold_dense_flat D f B hf (by rw [card_compl]; omega)
  have hsub : (D.image j).image e ⊆ A := by
    rw [image_image]
    change D.image emb ⊆ A
    rw [eq]
    exact inter_subset_left
  refine ⟨S.map e.toLinearMap,?_,?_⟩
  · rintro _ ⟨p,hp,rfl⟩
    have him := mem_image_of_mem e (hS p hp)
    rw [image_nsmul e] at him
    exact nsmul_subset_nsmul_left (n:=10) hsub him
  · rwa [← (S.equivMapOfInjective e.toLinearMap e.injective).finrank_eq]

/-- Green's literal tenfold conclusion with coefficient one for subsets retaining more
than three quarters of a quadratic graph. The set can also contain other points as long
as its cardinality stays at most the size of the graph. -/
theorem dense_quadratic_green50 {n : ℕ} (A : Finset (Fin n → F₂))
    (U V : Submodule F₂ (Fin n → F₂)) (hc : IsCompl U V) (f : U → V)
    (B : U →ₗ[F₂] U →ₗ[F₂] V) (hf : ∀ a x, f x + f (x+a) = B a x + (f 0+f a))
    (hd : 3*(graph U V f).card < 4*(A ∩ graph U V f).card)
    (hsize : A.card ≤ (graph U V f).card) :
    ∃ (W : Submodule F₂ (Fin n → F₂)) (v : Fin n → F₂),
      v +ᵥ (W : Set (Fin n → F₂)) ⊆ ↑((10:ℕ) • A) ∧
      (n:ℝ) - Real.logb 2 (1/(A.dens:ℝ)) ≤ Module.finrank F₂ W := by
  classical
  obtain ⟨W,hW,hw⟩ := tenfold_of_intersection A U V hc f B hf hd
  refine ⟨W,0,by simpa using hW,?_⟩
  have ha : 0 < A.card := by
    have : (A ∩ graph U V f).card ≤ A.card := card_le_card inter_subset_left
    omega
  have hdim := (U.prodEquivOfIsCompl V hc).finrank_eq
  rw [Module.finrank_prod,Module.finrank_fintype_fun_eq_card,Fintype.card_fin] at hdim
  have hcard : Fintype.card U * Fintype.card V = Fintype.card (Fin n → F₂) := by
    simpa using Fintype.card_congr (U.prodEquivOfIsCompl V hc).toEquiv
  rw [graph_card U V hc,Nat.card_eq_fintype_card] at hsize
  have cap := (Nat.mul_le_mul_right (Fintype.card V) hsize).trans_eq hcard
  rw [Module.card_eq_pow_finrank (K := ZMod 2) (V := V),ZMod.card] at cap
  have h₀ : (A.card:ℝ) * (2:ℝ)^Module.finrank F₂ V ≤ 2^n := by
    simpa [Fintype.card_pi] using
      (show (A.card:ℝ) * (2:ℝ)^Module.finrank F₂ V ≤ (Fintype.card (Fin n → F₂):ℝ) by exact_mod_cast cap)
  have hpos : (0:ℝ) < A.card := by exact_mod_cast ha
  have den : (A.dens:ℝ) = (A.card:ℝ)/2^n := by simp [Finset.dens,Fintype.card_pi]
  have hlog : (Module.finrank F₂ V:ℝ) ≤ Real.logb 2 (1/(A.dens:ℝ)) := by
    rw [den,one_div_div,Real.le_logb_iff_rpow_le (by norm_num) (div_pos (by positivity) hpos),
      Real.rpow_natCast,le_div_iff₀ hpos]
    linarith
  have hreal : (Module.finrank F₂ U:ℝ) + Module.finrank F₂ V = n := by exact_mod_cast hdim
  have hreal' : (Module.finrank F₂ U:ℝ) ≤ Module.finrank F₂ W := by exact_mod_cast hw
  linarith

end Embedded

#print axioms Green50DenseQuadraticGraphs.tenfold_of_intersection
#print axioms Green50DenseQuadraticGraphs.dense_quadratic_green50

#print axioms Green50DenseQuadraticGraphs.dense_graph_flat
#print axioms Green50DenseQuadraticGraphs.tenfold_dense_flat
#print axioms Green50DenseQuadraticGraphs.sixfold_dense_flat

#print axioms Green50DenseQuadraticGraphs.vertical_survives

end Green50DenseQuadraticGraphs
