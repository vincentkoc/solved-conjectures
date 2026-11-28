import Green33SquareTilings
import Green33PrimePowerBudget

/-! Exact uniformity on minimum common supports in cyclic groups of prime-square order. -/

open Finset Green33WeightedStability Green33SquareTilings Green33PrimePowerBudget
open scoped Pointwise

namespace Green33PrimeSquareSeeds

variable {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]

/-- Extend weights on a label set by zero to the whole group. -/
def extend {R : Type*} [Zero R] (A : Finset G) (f : A → R) (z : G) : R :=
  if h : z∈A then f ⟨z,h⟩ else 0

omit [AddCommGroup G] in
private theorem sum_extend {R : Type*} [AddCommMonoid R] (A : Finset G) (f : A → R) :
    ∑ z, extend A f z=∑ i, f i := by
  calc
    _ = ∑ z ∈ A, extend A f z := (sum_subset (subset_univ A) (fun x _ hx => by simp [extend,hx])).symm
    _ = ∑ i : A, extend A f i := (sum_attach A _).symm
    _ = _ := by simp [extend]

omit [AddCommGroup G] in
private theorem sum_mul_extend (A : Finset G) (f : A → ℝ) (g : G → ℝ) :
    ∑ z, extend A f z*g z=∑ i, f i*g i := by
  convert sum_extend A (fun i => f i*g i) using 1
  apply sum_congr rfl
  intro z _
  by_cases h : z∈A <;> simp [extend,h]

/-- The mass at an ambient group element, including zero outside the seed. -/
noncomputable def weight {A : Finset G} (P : PMF A) := extend A (fun i => (P i).toReal)

omit [AddCommGroup G] in
private theorem weight_total {A : Finset G} (P : PMF A) : ∑ z, weight P z=1 := by
  rw [weight,sum_extend]
  have e := congrArg ENNReal.toReal P.tsum_coe
  rwa [tsum_fintype, ENNReal.toReal_sum (fun i _ => P.apply_ne_top i),ENNReal.toReal_one] at e

private theorem conv_apply {A : Finset G} (P Q : PMF A) (z : G) :
    ∑ x, weight P x*weight Q (z-x)=((law P Q (fun i j : A => (i:G)+j)) z).toReal := by
  change ∑ x, extend A (fun i => (P i).toReal) x*weight Q (z-x)=_
  rw [sum_mul_extend]
  have e := observed_eq_mass P Q (fun i j : A => (i:G)+j) {z}
  simp only [mass,sum_singleton] at e
  rw [← e]
  apply sum_congr rfl
  intro i _
  by_cases h : z-(i:G)∈A
  · let j : A := ⟨z-i,h⟩
    rw [sum_eq_single j]
    · have eq : (i:G)+j=z := by dsimp [j]; abel
      simp [mem_singleton,eq,weight,extend,h,j]
    · intro a _ ne
      have neq : (i:G)+a≠z := fun ea => ne (Subtype.ext (by dsimp [j]; rw [← ea]; abel))
      simp [mem_singleton,neq]
    · simp
  · have off (a : A) : (i:G)+a≠z := fun ea => h (by rw [← ea]; simp)
    simp [mem_singleton,off,weight,extend,h]

variable (p : ℕ) [hp : Fact p.Prime]

/-- The quotient recording the low base-`p` digit. -/
def residue : ZMod (p^2) →+* ZMod p := ZMod.castHom (dvd_pow_self p (by decide : 2≠0)) _

/-- One complete residue class of the quotient. -/
def block (c : ZMod p) : Finset (ZMod (p^2)) := univ.filter fun x => residue p x=c

theorem block_card (c : ZMod p) : (block p c).card=p :=
  fiber_count _ _ _ (pow_two p) (residue p).toAddMonoidHom (ZMod.castHom_surjective (dvd_pow_self p (by decide : 2≠0))) c

private theorem only_class {A : Finset (ZMod (p^2))} (small : A.card<2*p) {c d : ZMod p}
    (hc : block p c⊆A) (hd : block p d⊆A) : c=d := by
  by_contra ne
  have dis : Disjoint (block p c) (block p d) := by
    exact disjoint_left.mpr fun z h h' => ne ((mem_filter.mp h).2.symm.trans (mem_filter.mp h').2)
  have le := card_le_card (union_subset hc hd)
  rw [card_union_of_disjoint dis,block_card,block_card] at le
  omega

/-- A normalized weight constant on quotient fibres and supported on fewer
than two full fibres must be uniform on a single fibre. -/
theorem block_of_period (A : Finset (ZMod (p^2))) (size : A.card<2*p)
    (f : ZMod (p^2) → ℝ) (total : ∑ x, f x=1) (outside : ∀ x∉A, f x=0)
    (period : ∀ z, f (z-(p:ZMod (p^2)))=f z) :
    ∃ c, block p c⊆A ∧ ∀ z, f z=if residue p z=c then (p:ℝ)⁻¹ else 0 := by
  classical
  have const {x y : ZMod (p^2)} (h : residue p x=residue p y) : f x=f y :=
    lift_equal _ f period h
  have inside {x : ZMod (p^2)} (hx : f x≠0) : block p (residue p x)⊆A := by
    intro y hy
    obtain ⟨_, eq⟩ := mem_filter.mp hy
    by_contra no
    exact hx ((const eq).symm.trans (outside y no))
  obtain ⟨x,hx⟩ : ∃ x, f x≠0 := by
    by_contra! n
    simp [n] at total
  have other {y} (ne : residue p y≠residue p x) : f y=0 := by
    by_contra hy
    exact ne (only_class p size (inside hy) (inside hx))
  have form (y) : f y=if residue p y=residue p x then f x else 0 := by
    split <;> rename_i h
    · exact const h
    · exact other h
  have mass : (p:ℝ)*f x=1 := by
    calc
      (p:ℝ)*f x = ∑ _z ∈ block p (residue p x), f x := by simp [block_card]
      _ = ∑ z, f z := by rw [block,sum_filter]; exact sum_congr rfl fun y _ => (form y).symm
      _ = 1 := total
  have val : f x=(p:ℝ)⁻¹ := by
    rw [← one_div,eq_div_iff (by exact_mod_cast hp.out.ne_zero)]
    linarith
  exact ⟨_,inside hx,fun y => (form y).trans (by rw [val])⟩


omit [DecidableEq G] in
private theorem conv_comm (f g : G → ℝ) (z : G) :
    ∑ x, f x*g (z-x)=∑ y, g y*f (z-y) := by
  apply Fintype.sum_equiv (Equiv.subLeft z)
  intro x
  simp [mul_comm]

/-- A fair draw from one class tests precisely the total masses of the other
input in the quotient. -/
theorem block_convolution (c : ZMod p) (f g : ZMod (p^2) → ℝ)
    (fair : ∀ x, f x=if residue p x=c then (p:ℝ)⁻¹ else 0) (z : ZMod (p^2)) :
    ∑ x, f x*g (z-x)=(p:ℝ)⁻¹*∑ y ∈ block p (residue p z-c), g y := by
  rw [conv_comm,mul_sum,block,sum_filter]
  apply sum_congr rfl
  intro y _
  rw [fair,map_sub]
  by_cases h : residue p y=residue p z-c
  · simp [h,mul_comm]
  · have ne : residue p z-residue p y≠c := fun e => h (by rw [← e]; abel)
    simp [ne,h]

/-- The first input is uniform on a full class, and the second projects to
the uniform law modulo the prime. -/
def BlockPair (f g : ZMod (p^2) → ℝ) : Prop :=
  ∃ c, (∀ x, f x=if residue p x=c then (p:ℝ)⁻¹ else 0) ∧
    ∀ y, ∑ x ∈ block p y, g x=(p:ℝ)⁻¹

private theorem quotient_uniform (c : ZMod p) (f g : ZMod (p^2) → ℝ)
    (fair : ∀ x, f x=if residue p x=c then (p:ℝ)⁻¹ else 0)
    (flat : ∀ z, ∑ x, f x*g (z-x)=((p:ℝ)^2)⁻¹) : BlockPair p f g := by
  refine ⟨c,fair,fun y => ?_⟩
  obtain ⟨z,hz⟩ := ZMod.castHom_surjective (dvd_pow_self p (by decide : 2≠0)) (y+c)
  change residue p z=y+c at hz
  have e := (block_convolution p c f g fair z).symm.trans (flat z)
  rw [hz,add_sub_cancel_right] at e
  have pos : (p:ℝ)≠0 := by exact_mod_cast hp.out.ne_zero
  rw [← inv_pow,pow_two ((p:ℝ)⁻¹)] at e
  exact mul_left_cancel₀ (inv_ne_zero pos) e

private theorem from_pair (f g : ZMod (p^2) → ℝ) (h : BlockPair p f g) (z : ZMod (p^2)) :
    ∑ x, f x*g (z-x)=((p:ℝ)^2)⁻¹ := by
  obtain ⟨c,fair,u⟩ := h
  rw [block_convolution p c f g fair,u,← inv_pow,pow_two]

private theorem periodic_alternative (A : Finset (ZMod (p^2))) (size : A.card<2*p)
    (P Q : PMF A) (a : A → ℚ) (rat : ∀ i, (a i : ℝ)=(P i).toReal)
    (flat : ∀ z, ∑ x, weight P x*weight Q (z-x)=((p:ℝ)^2)⁻¹) :
    BlockPair p (weight P) (weight Q) ∨ BlockPair p (weight Q) (weight P) := by
  have cast (x) : ((extend A a x : ℚ):ℝ)=weight P x := by
    by_cases h : x∈A <;> simp [extend,weight,h,rat]
  have old (z) : ∑ x, ((extend A a x : ℚ):ℝ)*weight Q (z-x)=((p:ℝ)^2)⁻¹ := by
    simp_rw [cast]; exact flat z
  have off (R : PMF A) (x) (hx : x∉A) : weight R x=0 := by simp [weight,extend,hx]
  rcases periodic_input 1 (extend A a) (weight Q) _ old with h|h
  · have h' (z) := congrArg (fun t : ℚ => (t:ℝ)) (h z)
    simp only [pow_one,cast] at h'
    obtain ⟨c,_,fair⟩ := block_of_period p A size _ (weight_total P) (off P) h'
    exact Or.inl (quotient_uniform p c _ _ fair flat)
  · simp only [pow_one] at h
    obtain ⟨c,_,fair⟩ := block_of_period p A size _ (weight_total Q) (off Q) h
    exact Or.inr (quotient_uniform p c _ _ fair fun z => (conv_comm _ _ z).trans (flat z))


/-- At the minimum common size, one of the two real laws is fair on a
complete residue class, and the other gives every residue class equal mass. -/
theorem flat_iff_block_pair (A : Finset (ZMod (p^2))) (size : A.card+1=2*p) (P Q : PMF A) :
    (∀ z, ((law P Q (fun i j : A => (i:ZMod (p^2))+(j:ZMod (p^2)))) z).toReal=((p:ℝ)^2)⁻¹) ↔
    BlockPair p (weight P) (weight Q) ∨ BlockPair p (weight Q) (weight P) := by
  have pos : (p:ℝ)≠0 := by exact_mod_cast hp.out.ne_zero
  have rat (R : PMF A) (S : Finset A)
      (fair : ∀ i, (p:ℝ)*(R i).toReal=if i∈S then 1 else 0) (i : A) :
      ((if i∈S then (p:ℚ)⁻¹ else 0 : ℚ):ℝ)=(R i).toReal := by
    have e := fair i
    by_cases h : i∈S
    · simp only [h,if_true] at e ⊢
      push_cast
      rw [← one_div,div_eq_iff pos]
      linarith
    · simp only [h,if_false,Rat.cast_zero] at e ⊢
      exact ((mul_eq_zero.mp e).resolve_left pos).symm
  constructor
  · intro flat
    have conv (z) := (conv_apply P Q z).trans (flat z)
    have small : A.card<2*p := by omega
    obtain ⟨S,h|h⟩ := (flat_iff_tiling_mixture p hp.out.pos (ZMod.card _)
      (by simpa only [Fintype.card_coe] using size) P Q (fun i : A => (i:ZMod (p^2)))).mp
      (by simpa only [ZMod.card,Nat.cast_pow] using flat)
    · exact periodic_alternative p A small P Q _ (rat P S h.fair) conv
    · exact (periodic_alternative p A small Q P _ (rat Q S h.fair)
        (fun z => (conv_comm _ _ z).trans (conv z))).symm
  · rintro (h|h) z
    · exact (conv_apply P Q z).symm.trans (from_pair p _ _ h z)
    · exact (conv_apply P Q z).symm.trans ((conv_comm _ _ z).trans (from_pair p _ _ h z))


/-- The prescribed labels support two independent laws with an exactly uniform sum. -/
def Feasible (A : Finset (ZMod (p^2))) : Prop :=
  ∃ P Q : PMF A, ∀ z : ZMod (p^2),
    ((law P Q (fun i j : A => (i:ZMod (p^2))+(j:ZMod (p^2)))) z).toReal=((p:ℝ)^2)⁻¹

private theorem seed_of_pair {A : Finset (ZMod (p^2))} (P Q : PMF A)
    (h : BlockPair p (weight P) (weight Q)) :
    ∃ c, block p c⊆A ∧ ∀ y, ∃ x∈A, residue p x=y := by
  obtain ⟨c,fair,hits⟩ := h
  have hp' : (p:ℝ)≠0 := by exact_mod_cast hp.out.ne_zero
  refine ⟨c,?_,?_⟩
  · intro x hx
    by_contra off
    have m := fair x
    simp [weight,extend,off,(mem_filter.mp hx).2] at m
    exact hp' m.symm
  · intro y
    by_contra! miss
    have zero : ∑ x ∈ block p y, weight Q x=0 := by
      exact sum_eq_zero fun x hx => by
        have off : x∉A := fun ha => miss x ha (mem_filter.mp hx).2
        simp [weight,extend,off]
    exact (inv_ne_zero hp') ((hits y).symm.trans zero)

private theorem fair_on (A U : Finset (ZMod (p^2))) (sub : U⊆A) (card : U.card=p) :
    ∃ P : PMF A, ∀ x, weight P x=if x∈U then (p:ℝ)⁻¹ else 0 := by
  let S := U.subtype (·∈A)
  have cs : S.card=p := by dsimp [S]; rw [card_subtype,filter_eq_self.mpr sub,card]
  have ns : S.Nonempty := card_pos.mp (by rw [cs]; exact hp.out.pos)
  refine ⟨PMF.uniformOfFinset S ns,fun x => ?_⟩
  by_cases ha : x∈A
  · let i : A := ⟨x,ha⟩
    have defn : weight (PMF.uniformOfFinset S ns) x=((PMF.uniformOfFinset S ns) i).toReal := by
      simp [i,weight,extend,ha]
    rw [defn]
    by_cases hu : x∈U
    · have hs : i∈S := mem_subtype.mpr hu
      simp [hu,PMF.uniformOfFinset_apply_of_mem _ hs,cs,ENNReal.toReal_inv]
    · have hs : i∉S := fun h => hu (mem_subtype.mp h)
      simp [hu,PMF.uniformOfFinset_apply_of_notMem _ hs]
  · have off : x∉U := fun h => ha (sub h)
    simp [weight,extend,ha,off]

/-- A minimum seed supports a uniform sum precisely when it contains a full
class and meets every class modulo the prime. -/
theorem feasible_iff (A : Finset (ZMod (p^2))) (size : A.card+1=2*p) :
    Feasible p A ↔ ∃ c, block p c⊆A ∧ ∀ y, ∃ x∈A, residue p x=y := by
  classical
  constructor
  · rintro ⟨P,Q,flat⟩
    rcases (flat_iff_block_pair p A size P Q).mp flat with h | h
    · exact seed_of_pair p P Q h
    · exact seed_of_pair p Q P h
  · rintro ⟨c,full,hits⟩
    choose s mem proj using hits
    have inj : Function.Injective s := fun x y h => (proj x).symm.trans ((congrArg (residue p) h).trans (proj y))
    let T := univ.image s
    have st : T⊆A := by intro x hx; obtain ⟨y,_,rfl⟩ := mem_image.mp hx; exact mem y
    have ct : T.card=p := by dsimp [T]; rw [card_image_of_injective _ inj,card_univ,ZMod.card]
    obtain ⟨P,pf⟩ := fair_on p A _ full (block_card p c)
    obtain ⟨Q,qf⟩ := fair_on p A T st ct
    refine ⟨P,Q,(flat_iff_block_pair p A size P Q).mpr (Or.inl ⟨c,?_,?_⟩)⟩
    · simpa [block] using pf
    · intro y
      rw [sum_eq_single (s y)]
      · rw [qf,if_pos (mem_image_of_mem _ (mem_univ y))]
      · intro z hz ne
        rw [qf,if_neg]
        intro ht
        obtain ⟨t,_,rfl⟩ := mem_image.mp ht
        have eq : t=y := (proj t).symm.trans (mem_filter.mp hz).2
        exact ne (congrArg s eq)
      · intro off
        exact False.elim (off (mem_filter.mpr ⟨mem_univ _,proj y⟩))


/-- Choose a point in each quotient class other than the distinguished class. -/
abbrev Choices (c : ZMod p) := (y : {y : ZMod p // y≠c}) → block p y

/-- The support made from one full class and the selected points. -/
def assemble (c : ZMod p) (s : Choices p c) : Finset (ZMod (p^2)) :=
  block p c ∪ univ.image (fun y => ((s y):ZMod (p^2)))

private theorem chosen {c : ZMod p} (s : Choices p c) (y) :
    residue p (s y)=y.1 := (mem_filter.mp (s y).property).2

private theorem other_card (c : ZMod p) : Fintype.card {y : ZMod p // y≠c}=p-1 := by
  rw [Fintype.card_subtype_compl,Fintype.card_subtype_eq,ZMod.card]

theorem assemble_size (c : ZMod p) (s : Choices p c) : (assemble p c s).card+1=2*p := by
  have dis : Disjoint (block p c) (univ.image fun y => ((s y):ZMod (p^2))) := by
    apply disjoint_left.mpr
    rintro z hz h
    obtain ⟨y,_,rfl⟩ := mem_image.mp h
    exact y.property ((chosen p s y).symm.trans (mem_filter.mp hz).2)
  have inj : Function.Injective (fun y => ((s y):ZMod (p^2))) := by
    intro y y' e
    exact Subtype.ext ((chosen p s y).symm.trans ((congrArg (residue p) e).trans (chosen p s y')))
  rw [assemble,card_union_of_disjoint dis,block_card,card_image_of_injective _ inj,card_univ,other_card]
  have := hp.out.pos
  omega

theorem assemble_feasible (c : ZMod p) (s : Choices p c) : Feasible p (assemble p c s) := by
  refine (feasible_iff p _ (assemble_size p c s)).mpr ⟨c,subset_union_left,fun y => ?_⟩
  by_cases h : y=c
  · subst y
    obtain ⟨z,hz⟩ := ZMod.castHom_surjective (dvd_pow_self p (by decide : 2≠0)) c
    exact ⟨z,mem_union_left _ (mem_filter.mpr ⟨mem_univ _,hz⟩),hz⟩
  · let t : {y : ZMod p // y≠c} := ⟨y,h⟩
    exact ⟨_,mem_union_right _ (mem_image_of_mem _ (mem_univ t)),chosen p s t⟩

/-- Parameterization with a distinguished class and one point in each other class. -/
theorem feasible_iff_assembled (A : Finset (ZMod (p^2))) :
    A.card+1=2*p ∧ Feasible p A ↔ ∃ c s, assemble p c s=A := by
  classical
  constructor
  · rintro ⟨size,h⟩
    obtain ⟨c,full,hit⟩ := (feasible_iff p A size).mp h
    choose pt inside proj using hit
    let s : Choices p c := fun y => ⟨pt y,mem_filter.mpr ⟨mem_univ _,proj _⟩⟩
    refine ⟨c,s,eq_of_subset_of_card_le ?_ ?_⟩
    · apply union_subset full
      intro z hz
      obtain ⟨y,_,rfl⟩ := mem_image.mp hz
      exact inside y
    · have := assemble_size p c s
      omega
  · rintro ⟨c,s,rfl⟩
    exact ⟨assemble_size p c s,assemble_feasible p c s⟩

private theorem assemble_inj : Function.Injective (fun t : (c : ZMod p) × Choices p c => assemble p t.1 t.2) := by
  rintro ⟨c,s⟩ ⟨d,t⟩ h
  change assemble p c s=assemble p d t at h
  have same : c=d := only_class p (A:=assemble p c s) (by have := assemble_size p c s; omega)
    subset_union_left (h ▸ subset_union_left)
  subst d
  have eq : s=t := by
    funext y
    apply Subtype.ext
    have mem : ((s y):ZMod (p^2))∈assemble p c t := h ▸ mem_union_right _ (mem_image_of_mem _ (mem_univ y))
    rcases mem_union.mp mem with a|a
    · exact False.elim (y.property ((chosen p s y).symm.trans (mem_filter.mp a).2))
    obtain ⟨u,_,e⟩ := mem_image.mp a
    have uy : u=y := Subtype.ext ((chosen p t u).symm.trans ((congrArg (residue p) e).trans (chosen p s y)))
    exact uy ▸ e.symm
  rw [eq]

/-- All minimum common seeds admitting exactly uniform sums. -/
noncomputable def feasibleSeeds : Finset (Finset (ZMod (p^2))) := by
  classical
  exact univ.filter fun A => A.card+1=2*p ∧ Feasible p A

/-- Exactly `p^p` distinct minimum supports work, counting actual subsets
of the prescribed cyclic group, including their different translates. -/
theorem feasibleSeeds_card : (feasibleSeeds p).card=p^p := by
  classical
  have eq : feasibleSeeds p=univ.image (fun t : (c : ZMod p) × Choices p c => assemble p t.1 t.2) := by
    ext A
    simp only [feasibleSeeds,mem_filter,mem_univ,true_and,feasible_iff_assembled,mem_image,Sigma.exists]
  rw [eq,card_image_of_injective _ (assemble_inj p),card_univ,Fintype.card_sigma]
  have choices (c : ZMod p) : Fintype.card (Choices p c)=p^(p-1) := by
    change Fintype.card ((y : {y : ZMod p // y≠c}) → block p y)=_
    rw [Fintype.card_pi]
    simp [block_card]
  simp only [choices,sum_const,card_univ,ZMod.card,nsmul_eq_mul]
  have hp' : p-1+1=p := Nat.sub_add_cancel hp.out.one_le
  exact (pow_succ' p (p-1)).symm.trans (congrArg (p^·) hp')

#print axioms block_card
#print axioms block_of_period
#print axioms block_convolution
#print axioms flat_iff_block_pair
#print axioms feasible_iff
#print axioms assemble_size
#print axioms assemble_feasible
#print axioms feasible_iff_assembled
#print axioms feasibleSeeds_card
end Green33PrimeSquareSeeds
