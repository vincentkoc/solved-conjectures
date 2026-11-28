import Green52WalshTiles
import Green52QuadraticFlats

/-! # Partitions into congruent colour classes in binary spaces

At every dyadic size the Hamming-ball obstruction occurs for a partition into nonempty
translates of the same tile. The resulting codimension bounds also quantify the cost of
requiring a quadratic transversal inside a general function graph.
-/
open Finset
open scoped Classical Pointwise
namespace Green53CongruentColours
local notation "K" => ZMod 2
variable {G : Type*} [AddCommGroup G] [Module K G]

private theorem twice (x : G) : x+x=0 := by
  rw [←two_smul K,show (2:K)=0 by decide,zero_smul]

/-- Every translate of a binary set has the same twofold sumset. -/
theorem translate_double (T : Set G) (v : G) : (v +ᵥ T) + (v +ᵥ T) = T+T := by
  ext z
  constructor
  · rintro ⟨_,⟨a,ha,rfl⟩,_,⟨b,hb,rfl⟩,rfl⟩
    exact ⟨a,ha,b,hb,by change a+b=v+a+(v+b); rw [add_add_add_comm,twice,zero_add]⟩
  · rintro ⟨a,ha,b,hb,rfl⟩
    refine ⟨v+a,⟨a,ha,rfl⟩,v+b,⟨b,hb,rfl⟩,?_⟩
    change v+a+(v+b)=a+b
    rw [add_add_add_comm,twice,zero_add]

variable [Fintype G] [DecidableEq G]

/-- The distinct vertical translates of a full graph form a partition.
Every class is nonempty and each double is exactly the double of the graph. -/
theorem graph_partition (U V : Submodule K G) (hc : IsCompl U V) (f : U → V) :
    ∃ P : Fin (Fintype.card V) → Set G, (⋃ i, P i)=Set.univ ∧
      Pairwise (fun i j => Disjoint (P i) (P j)) ∧
      ∀ i, (P i).Nonempty ∧ (∃ v : V, P i = (v:G) +ᵥ (Green50Graphs.graph U V f : Set G)) ∧
        P i + P i = (Green50Graphs.graph U V f : Set G) + (Green50Graphs.graph U V f : Set G) := by
  classical
  let e := Fintype.equivFin V
  let T : Set G := Green50Graphs.graph U V f
  let P (i : Fin (Fintype.card V)) := ((e.symm i : V):G) +ᵥ T
  have member (i) (x : G) : x ∈ P i ↔ ∃ u : U, (u:G)+(f u:G)+(e.symm i : G)=x := by
    constructor
    · rintro ⟨_,hy,rfl⟩
      obtain ⟨u,_,rfl⟩ := mem_image.mp hy
      exact ⟨u,add_comm _ _⟩
    · rintro ⟨u,rfl⟩
      exact ⟨(u:G)+(f u:G),mem_image_of_mem _ (mem_univ u),add_comm _ _⟩
  refine ⟨P,?_,?_,?_⟩
  · refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨⟨u,v⟩,h,_⟩ := Green52Complements.graph_tiles U V hc f x
    exact Set.mem_iUnion.mpr ⟨e v,(member _ _).mpr ⟨u,by simpa using h⟩⟩
  · intro i j hij
    refine Set.disjoint_left.mpr fun x hi hj => ?_
    obtain ⟨u,hu⟩ := (member i x).mp hi
    obtain ⟨v,hv⟩ := (member j x).mp hj
    have uniqueness := Green52Complements.graph_tiles U V hc f x
    have eq : (u,e.symm i) = (v,e.symm j) := uniqueness.unique hu hv
    exact hij (by simpa using congrArg (fun p : U × V => e p.2) eq)
  · intro i
    refine ⟨⟨_,(member i _).mpr ⟨0,rfl⟩⟩,⟨e.symm i,rfl⟩,translate_double _ _⟩

open Green52Complements

/-- A tiling by translates of one set, together with a lower bound on the
codimension of every affine subspace in the common twofold sumset. -/
def CongruentTiles (n k s : ℕ) : Prop :=
  ∃ (H : Submodule K (Cube n)) (T : Set (Cube n)), Nat.card H = k ∧ T + (H:Set (Cube n)) = Set.univ ∧
    ∃ P : Fin k → Set (Cube n), (⋃ i, P i) = Set.univ ∧ Pairwise (fun i j => Disjoint (P i) (P j)) ∧
      (∀ i, (P i).Nonempty ∧ (∃ v : H, P i = (v:Cube n) +ᵥ T) ∧ P i + P i = T+T) ∧
      ∀ W : AffineSubspace K (Cube n), (W : Set (Cube n)) ⊆ T+T →
        Module.finrank K W.direction + s ≤ n

/-- At every power-of-two word length n, the cube admits a partition into 2n
nonempty translates of one tile. Each twofold sum misses all flats of codimension
less than the integer square root of n. -/
theorem congruent_examples (m : ℕ) : CongruentTiles (2^m) (2^(m+1)) ((2^m).sqrt) := by
  classical
  obtain ⟨U,V,hcomp,_,cardV,f,bad⟩ := Green52WalshTiles.dyadic_bad_graph m
  let T : Set (Cube (2^m)) := Green50Graphs.graph U V f
  obtain ⟨P,hP,hdis,tiles⟩ := graph_partition U V hcomp f
  have cover : T + (V:Set (Cube (2^m))) = Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    have hx : x ∈ ⋃ i, P i := hP ▸ Set.mem_univ _
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
    obtain ⟨v,hv⟩ := (tiles i).2.1
    rw [hv] at hi
    obtain ⟨y,hy,rfl⟩ := hi
    exact ⟨y,hy,v.val,v.property,add_comm _ _⟩
  refine ⟨V,T,cardV,cover,?_⟩
  rw [←cardV,Nat.card_eq_fintype_card]
  exact ⟨P,hP,hdis,tiles,bad⟩

/-- An additive complement may be enlarged to any size up to the ambient order.
This gives lower bounds at sizes between the dyadic examples as well. -/
theorem cover_bound_at (c : ℕ → ℕ)
    (hc : ∀ (n k : ℕ) (A : Set (Cube n)) (S : Finset (Cube n)), S.card=k →
      A + (S:Set (Cube n)) = Set.univ → Flat n (c k) A) (m k : ℕ)
    (lo : 2^(m+1) ≤ k) (hi : k ≤ 2^(2^m)) : (2^m).sqrt ≤ c k := by
  classical
  obtain ⟨H,T,cardH,cover,_,_,_,_,bad⟩ := congruent_examples m
  let S := (H : Set (Cube (2^m))).toFinset
  have hcard : S.card=2^(m+1) := by simpa [S,Set.toFinset_card,Nat.card_eq_fintype_card] using cardH
  obtain ⟨F,hF,_,size⟩ := exists_subsuperset_card_eq (subset_univ S) (hcard ▸ lo)
    (by simpa [Cube] using hi : k ≤ (univ:Finset (Cube (2^m))).card)
  have mono : (H:Set (Cube (2^m))) ⊆ (F:Set (Cube (2^m))) := by simpa [S] using hF
  have full : T + (F : Set (Cube (2^m))) = Set.univ :=
    Set.eq_univ_of_univ_subset (cover ▸ Set.add_subset_add (Set.Subset.refl T) mono)
  obtain ⟨W,hw,dim⟩ := hc _ _ T F size full
  have small := bad W hw
  omega

private theorem four_times_le_pow (n : ℕ) (hn : 4 ≤ n) : 4*n ≤ 2^n := by
  induction n,hn using Nat.le_induction with
  | base => decide
  | succ n hn ih => rw [pow_succ]; omega

/-- On every complement size k ≥ 8 the required codimension is greater than
sqrt(k)/2 − 1, with an integral inequality avoiding rounding conventions. -/
theorem cover_bound_all (c : ℕ → ℕ)
    (hc : ∀ (n k : ℕ) (A : Set (Cube n)) (S : Finset (Cube n)), S.card=k →
      A + (S:Set (Cube n)) = Set.univ → Flat n (c k) A) {k : ℕ} (hk : 8 ≤ k) :
    k < 4*(c k+1)^2 := by
  let m := k.log2 - 1
  have lg : 3 ≤ k.log2 := (Nat.le_log2 (by omega : k≠0)).mpr hk
  have hm : m+1 = k.log2 := by dsimp [m]; omega
  have lo : 2^(m+1) ≤ k := hm ▸ Nat.log2_self_le (by omega)
  have hi : k < 4*2^m := by
    have h := Nat.lt_log2_self (n:=k)
    rw [←hm,pow_succ,pow_succ] at h
    omega
  have hn : 4 ≤ 2^m := Nat.pow_le_pow_right (by decide : 0<2) (by omega : 2 ≤ m)
  have csmall := cover_bound_at c hc m k lo (hi.le.trans (four_times_le_pow _ hn))
  have big := (Nat.lt_succ_sqrt' (2^m)).trans_le
    (Nat.pow_le_pow_left (Nat.add_le_add_right csmall 1) 2)
  omega

/-- The same square-root obstruction holds for the exact pinned Green 53 partition
predicate, witnessed even when all classes are translates with the same double. -/
theorem partition_bound_lower (c : ℕ → ℕ)
    (hc : ∀ (n k : ℕ) (P : Fin k → Set (Cube n)), (⋃ i, P i) = Set.univ →
      Pairwise (fun i j => Disjoint (P i) (P j)) → ∃ i, Flat n (c k) (P i)) (m : ℕ) :
    (2^m).sqrt ≤ c (2^(m+1)) := by
  obtain ⟨_,T,_,_,P,cover,dis,tiles,bad⟩ := congruent_examples m
  obtain ⟨i,W,hw,dim⟩ := hc _ _ P cover dis
  rw [(tiles i).2.2] at hw
  have small := bad W hw
  omega

/-- Any quadratic graph lying in any translate of a thin tile must pay for
its codimension obstruction in the square of its output dimension. -/
theorem quadratic_output_lower {n s : ℕ} {T : Set (Cube n)}
    (bound : ∀ W : AffineSubspace K (Cube n), (W : Set (Cube n)) ⊆ T+T →
      Module.finrank K W.direction+s ≤ n)
    (a : Cube n) (U V : Submodule K (Cube n)) (h : IsCompl U V) (f : U → V)
    (B : U →ₗ[K] U →ₗ[K] V) (hf : ∀ u x, f x+f (x+u)=B u x+(f 0+f u))
    (contained : (Green50Graphs.graph U V f : Set (Cube n)) ⊆ a +ᵥ T) : s ≤ (Module.finrank K V)^2 := by
  obtain ⟨W,hw,dim⟩ := Green52QuadraticFlats.quadratic_transversal_green52 _ U V h f B hf contained
  rw [translate_double] at hw
  have small := bound W hw
  have cost := min_le_right (Nat.card V-1) ((Module.finrank K V)^2)
  omega

/-- In this graph of output dimension m+1, every contained quadratic graph,
in any complementary coordinates and after any translation, needs output
dimension whose square is at least the integer square root of 2^m. -/
theorem quadratic_transversal_obstruction (m : ℕ) :
    ∃ (U V : Submodule K (Cube (2^m))), IsCompl U V ∧ Module.finrank K V = m+1 ∧
      ∃ f : U → V, ∀ (a : Cube (2^m)) (U' V' : Submodule K (Cube (2^m))), IsCompl U' V' →
        ∀ (g : U' → V') (B : U' →ₗ[K] U' →ₗ[K] V'),
          (∀ u x, g x+g (x+u)=B u x+(g 0+g u)) →
          (Green50Graphs.graph U' V' g : Set (Cube (2^m))) ⊆
            a +ᵥ (Green50Graphs.graph U V f : Set (Cube (2^m))) →
          (2^m).sqrt ≤ (Module.finrank K V')^2 := by
  obtain ⟨U,V,h,hd,_,f,bad⟩ := Green52WalshTiles.dyadic_bad_graph m
  exact ⟨U,V,h,hd,f,fun a U' V' h' g B hg ci => quadratic_output_lower bad a U' V' h' g B hg ci⟩

/-- The all-size companion for Green 53, with precisely the original colour-class quantifiers. -/
theorem partition_bound_all (c : ℕ → ℕ)
    (hc : ∀ (n k : ℕ) (P : Fin k → Set (Cube n)), (⋃ i, P i) = Set.univ →
      Pairwise (fun i j => Disjoint (P i) (P j)) → ∃ i, Flat n (c k) (P i)) {k : ℕ} (hk : 8 ≤ k) :
    k < 4*(c k+1)^2 :=
  cover_bound_all c (partition_implies_cover c hc) hk

private theorem exponential_beats_log (C D : ℝ) : ∃ t : ℕ, C*Real.log ((2:ℝ)^(2*t+1))+D < 2^t := by
  have h1 := tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1:ℝ)<2)
  have h0 := tendsto_pow_const_div_const_pow_of_one_lt 0 (by norm_num : (1:ℝ)<2)
  have h := ((h1.const_mul (2*C*Real.log 2)).add (h0.const_mul (C*Real.log 2+D)))
  simp only [mul_zero,zero_add,pow_one,pow_zero] at h
  obtain ⟨t,ht⟩ := (h.eventually_lt_const (by norm_num : (0:ℝ)<1)).exists
  change 2*C*Real.log 2 * ((t:ℝ)/2^t) + (C*Real.log 2+D)*(1/2^t)<1 at ht
  have pos : 0 < (2:ℝ)^t := by positivity
  have ht' := (div_lt_iff₀ pos).mp (show ((2*C*Real.log 2)*t + (C*Real.log 2+D))/(2:ℝ)^t < 1 by
    simpa only [add_div,mul_div_assoc,mul_one_div] using ht)
  refine ⟨t,?_⟩
  rw [Real.log_pow]
  push_cast
  linarith

/-- The logarithmic strengthening asked about in Green's discussion of problem 53
fails even with a positive number of colours and an arbitrary real additive constant. -/
theorem no_logarithmic_partition_bound :
    ¬ ∃ C D : ℝ, ∀ (n k : ℕ), 0<k → ∀ P : Fin k → Set (Cube n), (⋃ i, P i) = Set.univ →
      Pairwise (fun i j => Disjoint (P i) (P j)) →
      ∃ (i : Fin k) (W : AffineSubspace K (Cube n)), (W : Set (Cube n)) ⊆ P i + P i ∧
        (n:ℝ) ≤ Module.finrank K W.direction + C * Real.log (k:ℝ) + D := by
  rintro ⟨C,D,h⟩
  obtain ⟨t,ht⟩ := exponential_beats_log C D
  obtain ⟨_,T,_,_,P,cover,dis,tiles,bad⟩ := congruent_examples (2*t)
  obtain ⟨i,W,hw,hd⟩ := h _ _ (by positivity) P cover dis
  rw [(tiles i).2.2] at hw
  have small := bad W hw
  have sq : (2^(2*t)).sqrt = 2^t := by rw [Nat.mul_comm 2 t,pow_mul,Nat.sqrt_eq']
  rw [sq] at small
  have small' : (Module.finrank K W.direction : ℝ) + (2:ℝ)^t ≤ (2:ℝ)^(2*t) := by exact_mod_cast small
  push_cast at hd
  linarith

end Green53CongruentColours

#print axioms Green53CongruentColours.translate_double
#print axioms Green53CongruentColours.graph_partition
#print axioms Green53CongruentColours.congruent_examples
#print axioms Green53CongruentColours.cover_bound_at
#print axioms Green53CongruentColours.cover_bound_all
#print axioms Green53CongruentColours.partition_bound_lower
#print axioms Green53CongruentColours.partition_bound_all
#print axioms Green53CongruentColours.no_logarithmic_partition_bound
#print axioms Green53CongruentColours.quadratic_output_lower
#print axioms Green53CongruentColours.quadratic_transversal_obstruction
