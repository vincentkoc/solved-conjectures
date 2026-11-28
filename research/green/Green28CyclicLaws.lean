import Green28PrimeCyclic
import Green28FiniteSearch
import Green28FourAtomLaws

/-! Transfer of the original marginal and sum laws between integers and prime cycles. -/

open Finset
open scoped ENNReal

namespace Green28CyclicLaws

variable {G H : Type*}

/-- Uniformity on a finite nonempty support, in any ambient type. -/
def Uniform (P : PMF G) : Prop := ∃ (s : Finset G) (hs : s.Nonempty), P = PMF.uniformOfFinset s hs

/-- The law of the sum of independent variables. -/
noncomputable def sumLaw [Add G] (P Q : PMF G) : PMF G :=
  P.bind fun x => Q.bind fun y => PMF.pure (x+y)

/-- Positive answer for sums with at most `k` occupied sites. -/
def AtMost (G : Type*) [Add G] (k : ℕ) : Prop :=
  ∀ (P Q : PMF G) (s : Finset G) (hs : s.Nonempty), s.card ≤ k →
    sumLaw P Q = PMF.uniformOfFinset s hs → Uniform P ∧ Uniform Q

private theorem bind_eq {P : PMF G} {u v : G → PMF H}
    (h : ∀ x ∈ P.support, u x = v x) : P.bind u = P.bind v := by
  ext z
  rw [PMF.bind_apply, PMF.bind_apply]
  apply tsum_congr
  intro x
  by_cases hx : x ∈ P.support
  · rw [h x hx]
  · rw [(P.apply_eq_zero_iff x).mpr hx]; simp

private theorem mapped_sum [Add G] [Add H] {P Q : PMF G} {f g h : G → H}
    (eq : ∀ x ∈ P.support, ∀ y ∈ Q.support, f x + g y = h (x+y)) :
    sumLaw (P.map f) (Q.map g) = (sumLaw P Q).map h := by
  simp only [sumLaw, PMF.bind_map, PMF.map_bind, PMF.pure_map, Function.comp_def]
  apply bind_eq
  intro x hx
  apply bind_eq
  intro y hy
  exact congrArg PMF.pure (eq x hx y hy)

private theorem map_mass {P : PMF G} {f : G → H} (inj : Set.InjOn f P.support)
    {x : G} (hx : x ∈ P.support) : P.map f (f x) = P x := by
  classical
  rw [PMF.map_apply, tsum_eq_single x]
  · simp
  · intro y hy
    by_cases hys : y ∈ P.support
    · simp [show f x ≠ f y from fun eq => hy (inj hx hys eq).symm]
    · simp [(P.apply_eq_zero_iff _).mpr hys]

private theorem uniform_image [DecidableEq H] {P : PMF G} {f : G → H} {s : Finset G} (hs : s.Nonempty)
    (eq : P = PMF.uniformOfFinset s hs) (inj : Set.InjOn f P.support) :
    P.map f = PMF.uniformOfFinset (s.image f) (hs.image f) := by
  classical
  subst P
  have sinj : Set.InjOn f (s : Set G) := by simpa using inj
  apply PMF.ext
  intro z
  by_cases hz : z ∈ s.image f
  · obtain ⟨x,hx,rfl⟩ := mem_image.mp hz
    rw [map_mass inj (by simpa using hx),PMF.uniformOfFinset_apply_of_mem _ hx,
      PMF.uniformOfFinset_apply_of_mem _ hz,Finset.card_image_of_injOn sinj]
  · rw [(PMF.apply_eq_zero_iff _ _).mpr (by simpa using hz),PMF.uniformOfFinset_apply_of_notMem _ hz]

private theorem uniform_map {P : PMF G} {f : G → H}
    (inj : Set.InjOn f P.support) (u : Uniform P) :
    Uniform (P.map f) := by
  classical
  obtain ⟨s,hs,eq⟩ := u
  exact ⟨s.image f,hs.image _,uniform_image hs eq inj⟩

/-- Relabelling injectively on a law's support preserves and reflects uniformity. -/
theorem uniform_map_iff [Nonempty G] {P : PMF G} {f : G → H} (inj : Set.InjOn f P.support) :
    Uniform (P.map f) ↔ Uniform P := by
  refine ⟨fun u => ?_,uniform_map inj⟩
  let g := Function.invFunOn f P.support
  have back : (P.map f).map g = P := by
    rw [PMF.map_comp]
    trans P.map id
    · change P.bind _ = P.bind _
      apply bind_eq
      intro x hx
      exact congrArg PMF.pure (inj.leftInvOn_invFunOn hx)
    · exact PMF.map_id P
  rw [← back]
  exact uniform_map (by rw [PMF.support_map]; exact Function.invFunOn_injOn_image f _) u


/-- Three compatible injections, each restricted to its law's actual support. -/
structure Transport [Add G] (P Q : PMF G) (s : Finset G) (H : Type*) [Add H] where
  left : G → H
  right : G → H
  output : G → H
  left_inj : Set.InjOn left P.support
  right_inj : Set.InjOn right Q.support
  output_inj : Set.InjOn output (s : Set G)
  add : ∀ x ∈ P.support, ∀ y ∈ Q.support, left x+right y = output (x+y)

variable [Add G] [Add H]

/-- The entire output law is the pushforward along the output map. -/
theorem Transport.map_sum {P Q : PMF G} {s : Finset G} (t : Transport P Q s H) :
    sumLaw (P.map t.left) (Q.map t.right) = (sumLaw P Q).map t.output := mapped_sum t.add

/-- All three point probabilities agree at the relabelled sites. -/
theorem Transport.masses {P Q : PMF G} {s : Finset G} (t : Transport P Q s H)
    (supp : (sumLaw P Q).support = (s : Set G)) :
    (∀ x ∈ P.support, P.map t.left (t.left x) = P x) ∧
    (∀ y ∈ Q.support, Q.map t.right (t.right y) = Q y) ∧
    (∀ z ∈ s, sumLaw (P.map t.left) (Q.map t.right) (t.output z) = sumLaw P Q z) := by
  refine ⟨fun _ hx => map_mass t.left_inj hx,fun _ hy => map_mass t.right_inj hy,?_⟩
  intro z hz
  rw [t.map_sum]
  exact map_mass (supp ▸ t.output_inj) (by rw [supp]; exact hz)

/-- A bounded-outcome theorem on the target applies to these original laws. -/
private theorem Transport.descend [Nonempty G] {P Q : PMF G} {s : Finset G} (t : Transport P Q s H)
    (hs : s.Nonempty) (eq : sumLaw P Q = PMF.uniformOfFinset s hs)
    {k : ℕ} (size : s.card ≤ k) (target : AtMost H k) : Uniform P ∧ Uniform Q := by
  classical
  have supp : (sumLaw P Q).support = (s : Set G) := by rw [eq,PMF.support_uniformOfFinset]
  have pushed := t.map_sum.trans (uniform_image hs eq (supp ▸ t.output_inj))
  obtain ⟨a,b⟩ := target _ _ _ _ (by rwa [card_image_of_injOn t.output_inj]) pushed
  exact ⟨(uniform_map_iff t.left_inj).mp a,(uniform_map_iff t.right_inj).mp b⟩

private theorem small_representatives {p : ℕ} [Fact p.Prime] (s : Finset (ZMod p))
    (large : 5^s.card < p) : ∃ (F : ZMod p → ℤ) (q : ZMod p), q ≠ 0 ∧
      ∀ z ∈ insert 0 s, ((F z : ℤ) : ZMod p) = q*z ∧ 5*|F z| < (p : ℤ) := by
  classical
  let x (i : Fin s.card) := (s.equivFin.symm i : ZMod p)
  obtain ⟨r,_,q,hq,qp,cast⟩ := Green28PrimeCyclic.rectify large x
  let F (z : ZMod p) := if hz : z ∈ s then r (s.equivFin ⟨z,hz⟩) else 0
  refine ⟨F,q,fun eq => qp.not_ge (Nat.le_of_dvd hq ((ZMod.natCast_eq_zero_iff q p).mp eq)),?_⟩
  intro z hz
  by_cases h : z ∈ s
  · simpa [F,h,x] using cast (s.equivFin ⟨z,h⟩)
  · have he := (mem_insert.mp hz).resolve_right h
    subst z
    have pos : 0 < p := (Fact.out : p.Prime).pos
    simp [F,h,pos]

private theorem rectified_sites {p : ℕ} [Fact p.Prime] (s : Finset (ZMod p))
    (large : 5^s.card < p) : ∃ F : ZMod p → ℤ, Set.InjOn F (s : Set (ZMod p)) ∧
      ∀ i ∈ s, ∀ j ∈ s, ∀ u ∈ s, ∀ v ∈ s, i+j=u+v ↔ F i+F j=F u+F v := by
  classical
  obtain ⟨F,q,qnz,rep⟩ := small_representatives s large
  have h {i} (hi : i ∈ s) := rep i (mem_insert_of_mem hi)
  refine ⟨F,?_,?_⟩
  · intro a ha b hb eq
    apply mul_left_cancel₀ qnz
    rw [← (h ha).1, ← (h hb).1, eq]
  · exact fun _ hi _ hj _ hu _ hv => Green28PrimeCyclic.pair_iff qnz (h hi) (h hj) (h hu) (h hv)

/-- Rectify the sum support; a translate of each marginal support lies inside it.
All three maps act on the original laws. -/
theorem lift_measures {p : ℕ} [Fact p.Prime] {P Q : PMF (ZMod p)} {s : Finset (ZMod p)}
    (supp : (sumLaw P Q).support = (s : Set (ZMod p))) (large : 5^s.card < p) :
    Nonempty (Transport P Q s ℤ) := by
  classical
  obtain ⟨x,hx⟩ := P.support_nonempty
  obtain ⟨y,hy⟩ := Q.support_nonempty
  have pair {a b : ZMod p} (ha : a ∈ P.support) (hb : b ∈ Q.support) : a+b ∈ s := by
    change a+b ∈ (s : Set (ZMod p))
    rw [← supp]
    exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨a,ha,
      (PMF.mem_support_bind_iff _ _ _).mpr ⟨b,hb,(PMF.mem_support_pure_iff _ _).mpr rfl⟩⟩
  obtain ⟨F,inj,rel⟩ := rectified_sites s large
  refine ⟨⟨fun a => F (a+y)-F (x+y), fun b => F (x+b), F, ?_, ?_, inj, ?_⟩⟩
  · intro a ha b hb e
    exact add_right_cancel (inj (pair ha hy) (pair hb hy) (sub_left_inj.mp e))
  · intro a ha b hb e
    exact add_left_cancel (inj (pair hx ha) (pair hx hb) e)
  · intro a ha b hb
    have e := (rel _ (pair ha hy) _ (pair hx hb) _ (pair ha hb) _ (pair hx hy)).mp (by abel)
    omega

/-- On a bounded integer interval the quotient map preserves the original atoms. -/
private theorem cast_injective_on {p B : ℕ} (large : B < p) :
    Set.InjOn (fun z : ℤ => (z : ZMod p)) (Set.Icc 0 (B : ℤ)) := by
  intro a ha b hb eq
  have pa : a < (p:ℤ) := lt_of_le_of_lt ha.2 (by exact_mod_cast large)
  have pb : b < (p:ℤ) := lt_of_le_of_lt hb.2 (by exact_mod_cast large)
  simpa [Int.emod_eq_of_lt ha.1 pa,Int.emod_eq_of_lt hb.1 pb] using
    (ZMod.intCast_eq_intCast_iff' a b p).mp eq

/-- The integer problem for at most `k` sum outcomes is equivalent to testing
laws on any single prime cycle above the cutoff. -/
theorem atMost_iff_prime (k p : ℕ) [Fact p.Prime] (large : 5^(k+1) < p) :
    Green28FiniteSearch.AtMost k ↔ AtMost (ZMod p) k := by
  constructor
  · intro h P Q s hs size eq
    have supp : (sumLaw P Q).support = (s : Set _) := by rw [eq,PMF.support_uniformOfFinset]
    have bound : 5^s.card < p := (Nat.pow_le_pow_right (by decide : 0 < 5) (by omega : s.card ≤ k+1)).trans_lt large
    obtain ⟨t⟩ := lift_measures supp bound
    exact t.descend hs eq size h
  · intro h
    apply (Green28FiniteSearch.atMost_iff_onInterval k).mpr
    intro P Q s hs size hp hq sub eq
    let f (x : ℤ) : ZMod p := x
    let t : Transport P Q s (ZMod p) :=
      ⟨f,f,f,(cast_injective_on large).mono hp,(cast_injective_on large).mono hq,
        (cast_injective_on large).mono sub, fun x _ y _ => (Int.cast_add x y).symm⟩
    exact t.descend hs eq size h

private theorem mem_sum {P Q : PMF G} {z : G} :
    z ∈ (sumLaw P Q).support ↔ ∃ a ∈ P.support, ∃ b ∈ Q.support, a+b=z := by
  simp only [sumLaw, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff, eq_comm]

/-- Rectification using only the nonzero differences from one anchor in each
marginal. Equalities of occupied cross sums, in both directions, suffice. -/
theorem lift_by_marginals {p : ℕ} [Fact p.Prime] {P Q : PMF (ZMod p)} {s : Finset (ZMod p)}
    (supp : (sumLaw P Q).support = (s : Set (ZMod p)))
    (large : 5^(P.support.ncard + Q.support.ncard - 2) < p) :
    Nonempty (Transport P Q s ℤ) := by
  classical
  let A := P.support.toFinset
  let B := Q.support.toFinset
  obtain ⟨a₀,ha₀⟩ := P.support_nonempty
  obtain ⟨b₀,hb₀⟩ := Q.support_nonempty
  let D := ((A.erase a₀).image (·-a₀)) ∪ ((B.erase b₀).image (·-b₀))
  have ar : a₀ ∈ A := Set.mem_toFinset.mpr ha₀
  have br : b₀ ∈ B := Set.mem_toFinset.mpr hb₀
  have dc : D.card ≤ P.support.ncard + Q.support.ncard - 2 := by
    have h := Finset.card_union_le ((A.erase a₀).image (·-a₀)) ((B.erase b₀).image (·-b₀))
    have l : ((A.erase a₀).image (·-a₀)).card ≤ (A.erase a₀).card := card_image_le
    have r : ((B.erase b₀).image (·-b₀)).card ≤ (B.erase b₀).card := card_image_le
    rw [card_erase_of_mem ar] at l
    rw [card_erase_of_mem br] at r
    have ap := card_pos.mpr ⟨a₀,ar⟩
    have bp := card_pos.mpr ⟨b₀,br⟩
    rw [Set.ncard_eq_toFinset_card',Set.ncard_eq_toFinset_card']
    change D.card ≤ A.card+B.card-2
    change D.card ≤ _ at h
    omega
  obtain ⟨F,q,qnz,rep⟩ := small_representatives D ((Nat.pow_le_pow_right (by decide) dc).trans_lt large)
  have ad (a) (ha : a ∈ P.support) : a-a₀ ∈ insert 0 D := by
    by_cases e : a=a₀
    · simp [e]
    · apply mem_insert_of_mem
      exact mem_union_left _ (mem_image.mpr ⟨a,mem_erase.mpr ⟨e,Set.mem_toFinset.mpr ha⟩,rfl⟩)
  have bd (b) (hb : b ∈ Q.support) : b-b₀ ∈ insert 0 D := by
    by_cases e : b=b₀
    · simp [e]
    · apply mem_insert_of_mem
      exact mem_union_right _ (mem_image.mpr ⟨b,mem_erase.mpr ⟨e,Set.mem_toFinset.mpr hb⟩,rfl⟩)
  let f (a : ZMod p) := F (a-a₀)
  let g (b : ZMod p) := F (b-b₀)
  have pairs {a b c d : ZMod p} (ha : a ∈ P.support) (hb : b ∈ Q.support)
      (hc : c ∈ P.support) (hd : d ∈ Q.support) : a+b=c+d ↔ f a+g b=f c+g d := by
    have e := Green28PrimeCyclic.pair_iff qnz (rep _ (ad a ha)) (rep _ (bd b hb))
      (rep _ (ad c hc)) (rep _ (bd d hd))
    rw [sub_add_sub_comm,sub_add_sub_comm,sub_left_inj] at e
    exact e
  have out (z : ZMod p) (hz : z ∈ s) : ∃ t : ℤ, ∀ a ∈ P.support, ∀ b ∈ Q.support, a+b=z → f a+g b=t := by
    obtain ⟨c,hc,d,hd,e⟩ := mem_sum.mp (show z ∈ (sumLaw P Q).support by rw [supp]; exact hz)
    exact ⟨f c+g d,fun a ha b hb he => (pairs ha hb hc hd).mp (he.trans e.symm)⟩
  let h (z : ZMod p) := if hz : z ∈ s then (out z hz).choose else 0
  have add {a b} (ha : a ∈ P.support) (hb : b ∈ Q.support) : f a+g b=h (a+b) := by
    have hz : a+b ∈ (s:Set (ZMod p)) := supp ▸ mem_sum.mpr ⟨a,ha,b,hb,rfl⟩
    dsimp only [h]
    rw [dif_pos (show a+b ∈ s from hz)]
    exact (out _ hz).choose_spec a ha b hb rfl
  refine ⟨⟨f,g,h,?_,?_,?_,fun _ ha _ hb => add ha hb⟩⟩
  · intro a ha c hc eq
    exact add_right_cancel ((pairs ha hb₀ hc hb₀).mpr (by rw [eq]))
  · intro b hb d hd eq
    exact add_left_cancel ((pairs ha₀ hb ha₀ hd).mpr (by rw [eq]))
  · intro z hz w hw eq
    obtain ⟨a,ha,b,hb,rfl⟩ := mem_sum.mp (show z ∈ (sumLaw P Q).support by rw [supp]; exact hz)
    obtain ⟨c,hc,d,hd,rfl⟩ := mem_sum.mp (show w ∈ (sumLaw P Q).support by rw [supp]; exact hw)
    exact (pairs ha hb hc hd).mpr ((add ha hb).trans (eq.trans (add hc hd).symm))

/-- In particular, above the six-coordinate threshold no two four-atom cyclic
marginals can give a uniform sum unless both are uniform. -/
theorem four_atom_prime {p : ℕ} [Fact p.Prime] (large : 5^6 < p) {P Q : PMF (ZMod p)}
    (hp : P.support.ncard ≤ 4) (hq : Q.support.ncard ≤ 4) (uniform : Uniform (sumLaw P Q)) :
    Uniform P ∧ Uniform Q := by
  classical
  obtain ⟨s,hs,eq⟩ := uniform
  have supp : (sumLaw P Q).support = (s : Set _) := by rw [eq,PMF.support_uniformOfFinset]
  obtain ⟨t⟩ := lift_by_marginals supp ((Nat.pow_le_pow_right (by decide : 0<5)
    (by omega : P.support.ncard+Q.support.ncard-2 ≤ 6)).trans_lt large)
  have pushed := t.map_sum.trans (uniform_image hs eq (supp ▸ t.output_inj))
  have pe : (P.map t.left).support.ncard ≤ 4 := by rwa [PMF.support_map,t.left_inj.ncard_image]
  have qe : (Q.map t.right).support.ncard ≤ 4 := by rwa [PMF.support_map,t.right_inj.ncard_image]
  obtain ⟨u,v⟩ := Green28FourAtomLaws.uniform_of_at_most_four_atoms ⟨_,_,pushed⟩ pe qe
  exact ⟨(uniform_map_iff t.left_inj).mp u,(uniform_map_iff t.right_inj).mp v⟩

/-- One sufficiently large prime per outcome budget gives the literal pinned
Green 28 proposition. -/
theorem green_28_iff_prime_tests (p : ℕ → ℕ) (primes : ∀ k, (p k).Prime)
    (large : ∀ k, 5^(k+1) < p k) :
    (type_of% Green28.green_28) ↔ ∀ k, AtMost (ZMod (p k)) k := by
  constructor
  · intro h k
    let _ : Fact (p k).Prime := ⟨primes k⟩
    apply (atMost_iff_prime k (p k) (large k)).mp
    intro P Q s hs _ eq
    have u : Green28.IsUniformOnSupport (Green28.indepSum P Q) := ⟨s,hs,eq⟩
    have finite := Green28UniformSums.finite_of_uniform_sum u
    exact h P Q ⟨finite.1,finite.2,u⟩
  · intro h P Q ⟨_,_,s,hs,eq⟩
    let _ : Fact (p s.card).Prime := ⟨primes _⟩
    exact (atMost_iff_prime s.card _ (large _)).mpr (h _) P Q s hs le_rfl eq

#print axioms green_28_iff_prime_tests
#print axioms lift_by_marginals
#print axioms four_atom_prime
#print axioms Transport.masses
#print axioms lift_measures
#print axioms atMost_iff_prime

end Green28CyclicLaws
