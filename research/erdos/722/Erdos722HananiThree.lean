import Erdos722HananiMatchings
import Erdos722HananiTwelve

/-!
# Hanani's three-column recurrences for Steiner quadruple systems

The two-point stem gives order `3v−4`; a four-point block as stem gives
order `3v−8`. Both use the same cyclic sum intervals and residual matchings.
-/

namespace Erdos722.HananiThree
open Finset QuadCompletion ThreeColumn HananiSlots HananiTwelve
open scoped Multiset

section Source
variable {V : Type*} [DecidableEq V] {H : Finset (Finset V)} (hH : H.IsBlockDesign 3 4)

private def good (H : Finset (Finset V)) (m : Multiset V) : Prop :=
  m.toFinset ∈ H ∨ ∀ x, Even (m.count x)

private def four (a b c d : V) : Multiset V := a ::ₘ b ::ₘ c ::ₘ d ::ₘ 0

private noncomputable def fourth (a b c : V) := (QuadrupleProduct.unique_fourth hH a b c).exists.choose

private theorem good_fourth (a b c : V) : good H (four a b c (fourth hH a b c)) :=
  (QuadrupleProduct.unique_fourth hH a b c).exists.choose_spec

private theorem force {a b c w : V} (hw : good H (four a b c w)) : fourth hH a b c = w :=
  (QuadrupleProduct.unique_fourth hH a b c).unique (good_fourth hH a b c) hw

private noncomputable def sourceRule : Rule V where
  complete := fourth hH
  swap₁ a b c := by
    apply force hH
    have he : four a b c (fourth hH b a c) = four b a c (fourth hH b a c) := by
      simp only [four,← Multiset.singleton_add]
      ac_rfl
    rw [he]
    exact good_fourth hH b a c
  swap₂ a b c := by
    apply force hH
    have he : four a b c (fourth hH a c b) = four a c b (fourth hH a c b) := by
      simp only [four,← Multiset.singleton_add]
      ac_rfl
    rw [he]
    exact good_fourth hH a c b
  repeated a b := by
    apply force hH
    right
    intro x
    simp only [four,Nat.even_iff, Multiset.count_cons,Multiset.count_zero]
    split_ifs <;> decide
  cancel a b c := by
    apply force hH
    have he : four a b (fourth hH a b c) (c) = four a b c (fourth hH a b c) := by
      simp only [four,← Multiset.singleton_add]
      ac_rfl
    rw [he]
    exact good_fourth hH a b c

private theorem source_closed {B : Finset V} (hB : B ∈ H) {a b c : V} (ha : a ∈ B)
    (hb : b ∈ B) (hc : c ∈ B) : (sourceRule hH).complete a b c ∈ B := by
  let Q := sourceRule hH
  change Q.complete a b c ∈ B
  by_cases hab : a=b
  · subst b; rwa [Q.repeated]
  by_cases hac : a=c
  · subst c; rwa [Q.swap₂,Q.repeated]
  by_cases hbc : b=c
  · subst c; rwa [Q.swap₁,Q.swap₂,Q.repeated]
  have h₃ : ({a,b,c} : Finset V).card = 3 := card_eq_three.mpr ⟨a,b,c,hab,hac,hbc,rfl⟩
  have hs : ({a,b,c} : Finset V) ⊆ B := by simp [insert_subset_iff,ha,hb,hc]
  obtain ⟨w,_,hw⟩ := exists_eq_insert_iff.mpr ⟨hs, by rw [h₃,hH.1 _ hB]⟩
  have he : good H (four a b c w) := by
    left
    have hf : (four a b c w).toFinset = insert w {a,b,c} := by ext x; simp [four,or_comm,or_left_comm]
    rwa [hf,hw]
  change fourth hH a b c ∈ B
  rw [force hH he,← hw]
  exact mem_insert_self ..

end Source

private def transport {A B : Type*} (R : Rule B) (e : A ≃ B) : Rule A where
  complete a b c := e.symm (R.complete (e a) (e b) (e c))
  swap₁ a b c := congrArg e.symm (R.swap₁ _ _ _)
  swap₂ a b c := congrArg e.symm (R.swap₂ _ _ _)
  repeated a b := by simp [R.repeated]
  cancel a b c := by simp [R.cancel]

private theorem construct {h d r : ℕ} [NeZero (2*r)] (hr : 2*d+1 ≤ r) (he : h+6*d=2*r)
    (Q : Rule (Fin h ⊕ Labels r)) (hq : Scheme.StemClosed Q) : HasSQS (h+6*r) := by
  classical
  let G := (HananiMatchings.scheme hr he).rule Q hq
  let e : Point (Fin h) (Labels r) ≃ Fin (h+6*r) :=
    Fintype.equivOfCardEq (by simp [Point,Col,Labels]; omega)
  exact ⟨_,StemInflation.relabel G.isBlockDesign e⟩

private theorem closed_two {A : Type*} (Q : Rule (Fin 2 ⊕ A)) : Scheme.StemClosed Q := by
  intro s t u
  have hp : ∀ s t u : Fin 2, s=t ∨ s=u ∨ t=u := by decide +kernel
  rcases hp s t u with h|h|h
  · subst t; exact ⟨u,Q.repeated ..⟩
  · subst u; exact ⟨t,(Q.swap₂ ..).trans (Q.repeated ..)⟩
  · subst u; exact ⟨s,(Q.swap₁ ..).trans ((Q.swap₂ ..).trans (Q.repeated ..))⟩

/-- Two common points give the three-column construction at every order `6d+4`. -/
theorem three_minus_four (d : ℕ) (h : HasSQS (6*d+4)) : HasSQS (18*d+8) := by
  classical
  obtain ⟨H,hH⟩ := h
  let r := 3*d+1
  let : NeZero (2*r) := ⟨by dsimp [r]; omega⟩
  let e : Fin 2 ⊕ Labels r ≃ Fin (6*d+4) := Fintype.equivOfCardEq (by simp [Labels,r]; omega)
  let Q := transport (sourceRule hH) e
  have hout := construct (h := 2) (r := r) (d := d) (by dsimp [r]; omega) (by dsimp [r]; omega)
    Q (closed_two Q)
  convert hout using 1
  dsimp [r]
  omega

/-- A block can be chosen as the four-point stem at every order `6d+8`. -/
theorem three_minus_eight (d : ℕ) (h : HasSQS (6*d+8)) : HasSQS (18*d+16) := by
  classical
  obtain ⟨H,hH⟩ := h
  let r := 3*d+2
  let : NeZero (2*r) := ⟨by dsimp [r]; omega⟩
  let V := Fin (6*d+8)
  let tri : Fin 3 ↪ V := Fin.castLEEmb (by omega)
  obtain ⟨B,⟨hB,_⟩,_⟩ := hH.2 (univ.map tri) (by simp)
  have h₄ := hH.1 _ hB
  let es : Fin 4 ≃ ↥B := Fintype.equivOfCardEq (by simp [h₄])
  let ea : Labels r ≃ {x : V // x ∉ B} := Fintype.equivOfCardEq (by
    rw [Fintype.card_subtype_compl (fun x : V => x ∈ B)]
    simp [Labels,V,r,h₄]; omega)
  let e : Fin 4 ⊕ Labels r ≃ V := (Equiv.sumCongr es ea).trans (Equiv.sumCompl (fun x => x ∈ B))
  have hin (s : Fin 4) : e (.inl s) ∈ B := (es s).property
  let Q := transport (sourceRule hH) e
  have hq : Scheme.StemClosed Q := by
    intro a b c
    let w := (sourceRule hH).complete (e (.inl a)) (e (.inl b)) (e (.inl c))
    have hw : w ∈ B := source_closed hH hB (hin a) (hin b) (hin c)
    refine ⟨es.symm ⟨w,hw⟩,e.injective ?_⟩
    change e (e.symm w) = (es (es.symm ⟨w,hw⟩)).val
    simp
  have hout := construct (h := 4) (r := r) (d := d) (by dsimp [r]; omega) (by dsimp [r]; omega) Q hq
  convert hout using 1
  dsimp [r]
  omega

/-- The `4v−6` recurrence alone suffices for the full admissible quadruple spectrum. -/
theorem spectrum_of_fourfold
    (six : ∀ m ≥ 4, (m%6=2 ∨ m%6=4) → HasSQS m → HasSQS (4*m-6)) :
    ∀ n, n%6=2 ∨ n%6=4 → HasSQS n := by
  apply spectrum_of_three_constructions _ _ six
  · intro m hm hr h
    have he : m=6*((m-8)/6)+8 := by omega
    have hh := three_minus_eight ((m-8)/6) (he ▸ h)
    convert hh using 1
    omega
  · intro m hm hr h
    have he : m=6*((m-4)/6)+4 := by omega
    have hh := three_minus_four ((m-4)/6) (he ▸ h)
    convert hh using 1
    omega

/-- The pinned eventual statement at `r = 3`, `k = 4`, conditional on the
remaining fourfold construction. -/
theorem eventually_quadruples_of_fourfold
    (six : ∀ m ≥ 4, (m%6=2 ∨ m%6=4) → HasSQS m → HasSQS (4*m-6)) :
    ∀ᶠ n : ℕ in Filter.atTop, (∀ i < 3, (4-i).choose (3-i) ∣ (n-i).choose (3-i)) →
      ∃ H : Finset (Finset (Fin n)), H.IsBlockDesign 3 4 := by
  filter_upwards [Filter.eventually_ge_atTop 4] with n hn h
  exact spectrum_of_fourfold six n (residues_of_divisibility hn h)

/-- Orders obtained from the two infinite seed families by the three earlier
quadruple-system operations in the notebook, allowing arbitrary nesting. -/
inductive EarlierOrder : ℕ → Prop where
  | binary (d : ℕ) : EarlierOrder (2^d)
  | ternary (d : ℕ) : EarlierOrder (3^d+1)
  | product {a b} : EarlierOrder a → EarlierOrder b → EarlierOrder (a*b)
  | triple {a} : EarlierOrder a → EarlierOrder (3*a-2)
  | twelve {a} : EarlierOrder a → EarlierOrder (12*a-10)

private def allowed : Finset (ZMod 36) := {1,2,4,8,10,14,16,20,22,28,32}

private theorem earlier_residue {n : ℕ} (hn : EarlierOrder n) : 0 < n ∧ (n : ZMod 36) ∈ allowed := by
  have hm : ∀ a ∈ allowed, ∀ b ∈ allowed, a*b ∈ allowed := by decide +kernel
  have ht : ∀ a ∈ allowed, 3*a-2 ∈ allowed := by decide +kernel
  have hv : ∀ a ∈ allowed, 12*a-10 ∈ allowed := by decide +kernel
  induction hn with
  | binary d =>
    refine ⟨by positivity,?_⟩
    push_cast
    induction d with
    | zero => decide
    | succ d ih => rw [pow_succ]; exact hm _ ih _ (by decide)
  | ternary d =>
    refine ⟨by positivity,?_⟩
    push_cast
    induction d with
    | zero => decide
    | succ d ih =>
      rw [pow_succ]
      convert ht _ ih using 1
      ring
  | product _ _ ia ib =>
    exact ⟨Nat.mul_pos ia.1 ib.1,by rw [Nat.cast_mul]; exact hm _ ia.2 _ ib.2⟩
  | triple _ ih =>
    obtain ⟨hp,hm⟩ := ih
    exact ⟨by omega,by rw [Nat.cast_sub (by omega)]; push_cast; exact ht _ hm⟩
  | twelve _ ih =>
    obtain ⟨hp,hm⟩ := ih
    exact ⟨by omega,by rw [Nat.cast_sub (by omega)]; push_cast; exact hv _ hm⟩

private theorem harmonic_seed (d : ℕ) : ∃ k, 9^(d+1) = 12*k+9 := by
  induction d with
  | zero => exact ⟨0,rfl⟩
  | succ d ih =>
    obtain ⟨k,hk⟩ := ih
    exact ⟨9*k+6,by rw [pow_succ,hk]; omega⟩

/-- The harmonic seeds give the orders 26, 242, 2186, …, all excluded by
the residue invariant of the earlier product, tripling and twelvefold closure. -/
theorem harmonic_family (d : ℕ) : HasSQS (3*9^(d+1)-1) ∧ ¬EarlierOrder (3*9^(d+1)-1) := by
  obtain ⟨k,hk⟩ := harmonic_seed d
  have h := Harmonic.exists_ternary_quadruple_design (2*(d+1)) (by omega)
  rw [pow_mul,show (3:ℕ)^2=9 by decide,hk] at h
  have he : 12*k+9+1=6*(2*k+1)+4 := by omega
  rw [he] at h
  constructor
  · have hh := three_minus_four (2*k+1) h
    convert hh using 1
    omega
  · intro hn
    have hmem := (earlier_residue hn).2
    have hval : 3*9^(d+1)-1=36*k+26 := by omega
    rw [hval] at hmem
    push_cast at hmem
    rw [show (36 : ZMod 36) = 0 by decide,zero_mul,zero_add] at hmem
    exact (by decide : (26 : ZMod 36) ∉ allowed) hmem

#print axioms harmonic_family
#print axioms three_minus_four
#print axioms three_minus_eight
#print axioms spectrum_of_fourfold
#print axioms eventually_quadruples_of_fourfold

end Erdos722.HananiThree
