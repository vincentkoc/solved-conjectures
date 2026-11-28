import Green28CyclicLaws

/-! Asymmetric rectification of two marginal supports on a prime cycle. -/

open Finset Green28CyclicLaws

namespace Green28AsymmetricSupports

/-- A dilation puts the differences from an anchor into a short signed interval.
Each coordinate uses a box of width `(p-1)/L+1` in the pigeonhole argument. -/
theorem narrow {p L : ℕ} [Fact p.Prime] (hL : 0 < L) (D : Finset (ZMod p))
    (large : L^D.card < p) :
    ∃ q : ZMod p, q ≠ 0 ∧ ∀ d ∈ insert 0 D, ∃ z : ℤ,
      (z : ZMod p)=q*d ∧ |z| ≤ ((p-1)/L : ℕ) := by
  classical
  let h := (p-1)/L
  have pp : 0<p := (Fact.out : p.Prime).pos
  have cap : p ≤ L*(h+1) := by
    have := Nat.lt_mul_div_succ (p-1) hL
    dsimp [h]
    omega
  let box (z : ZMod p) : Fin L :=
    ⟨z.val/(h+1), (Nat.div_lt_iff_lt_mul (Nat.succ_pos h)).mpr ((ZMod.val_lt _).trans_le cap)⟩
  let tag (u : ZMod p) (d : D) := box (u*d.val)
  obtain ⟨u,v,ne,eq⟩ := Fintype.exists_ne_map_eq_of_card_lt tag (by simpa using large)
  refine ⟨u-v,sub_ne_zero.mpr ne,?_⟩
  intro d hd
  rcases mem_insert.mp hd with rfl|hd
  · exact ⟨0,by simp, by rw [abs_zero]; exact Nat.cast_nonneg _⟩
  · let a := (u*d).val
    let b := (v*d).val
    have same : a/(h+1)=b/(h+1) := congrArg Fin.val (congrFun eq ⟨d,hd⟩)
    refine ⟨(a:ℤ)-b,by simp [a,b,sub_mul],?_⟩
    have e := Nat.div_add_mod a (h+1)
    rw [same] at e
    have f := Nat.div_add_mod b (h+1)
    have am : a%(h+1) ≤ h := Nat.lt_succ_iff.mp (Nat.mod_lt a (Nat.succ_pos h))
    have bm : b%(h+1) ≤ h := Nat.lt_succ_iff.mp (Nat.mod_lt b (Nat.succ_pos h))
    have ab : a ≤ b+h := by
      calc a = (h+1)*(b/(h+1))+a%(h+1) := e.symm
           _ ≤ (h+1)*(b/(h+1))+h := Nat.add_le_add_left am _
           _ ≤ b+h := Nat.add_le_add_right ((Nat.le_add_right _ _).trans_eq f) _
    have ba : b ≤ a+h := by
      calc b = (h+1)*(b/(h+1))+b%(h+1) := f.symm
           _ ≤ (h+1)*(b/(h+1))+h := Nat.add_le_add_left bm _
           _ ≤ a+h := Nat.add_le_add_right ((Nat.le_add_right _ _).trans_eq e) _
    change |(a:ℤ)-b| ≤ (h:ℤ)
    rw [abs_le]
    omega

/-- A translate of the second dilated support avoids the first `w` residues.
Each site rules out at most `w` possible cuts. -/
theorem avoid {p w : ℕ} [Fact p.Prime] (B : Finset (ZMod p)) (q : ZMod p)
    (budget : w*B.card < p) : ∃ t : ZMod p, ∀ b ∈ B, w ≤ (q*b+t).val := by
  classical
  let bad := ((range w) ×ˢ B).image (fun u : ℕ × ZMod p => (u.1:ZMod p)-q*u.2)
  have card : bad.card < (univ : Finset (ZMod p)).card := by
    have bound : bad.card ≤ w*B.card := by simpa [bad] using
      (card_image_le (f := fun u : ℕ × ZMod p => (u.1:ZMod p)-q*u.2) (s := range w ×ˢ B))
    simpa using bound.trans_lt budget
  obtain ⟨t,_,outside⟩ := exists_mem_notMem_of_card_lt_card card
  refine ⟨t,fun b hb => ?_⟩
  by_contra! short
  apply outside
  apply mem_image.mpr
  exact ⟨((q*b+t).val,b),mem_product.mpr ⟨mem_range.mpr short,hb⟩,by simp⟩

/-- A prime cycle models the two original laws over the integers whenever
`(2 · |B|)^(|A|−1) < p`. Only the first support enters the exponent. -/
theorem lift {p : ℕ} [Fact p.Prime] (P Q : PMF (ZMod p)) (s : Finset (ZMod p))
    (large : (2*Q.support.ncard)^(P.support.ncard-1) < p) :
    Nonempty (Transport P Q s ℤ) := by
  classical
  let A := P.support.toFinset
  let B := Q.support.toFinset
  let n := B.card
  let L := 2*n
  let h := (p-1)/L
  have pp : 0 < p := (Fact.out : p.Prime).pos
  have np : 0 < n := card_pos.mpr (by obtain ⟨b,hb⟩ := Q.support_nonempty; exact ⟨b,Set.mem_toFinset.mpr hb⟩)
  have lp : 0 < L := by dsimp [L]; omega
  obtain ⟨a₀,ha₀⟩ := P.support_nonempty
  have a₀A : a₀ ∈ A := Set.mem_toFinset.mpr ha₀
  let D := (A.erase a₀).image (·-a₀)
  have cardD : D.card ≤ A.card-1 := (card_image_le).trans_eq (card_erase_of_mem a₀A)
  have size : L^D.card < p := by
    rw [Set.ncard_eq_toFinset_card',Set.ncard_eq_toFinset_card'] at large
    exact (Nat.pow_le_pow_right lp cardD).trans_lt large
  obtain ⟨q,qnz,rep⟩ := narrow lp D size
  have reps (a) (ha : a ∈ P.support) : ∃ z : ℤ, (z : ZMod p)=q*(a-a₀) ∧ |z| ≤ (h:ℤ) := by
    apply rep
    by_cases e : a=a₀
    · simp [e]
    · exact mem_insert_of_mem (mem_image.mpr ⟨a,mem_erase.mpr ⟨e,Set.mem_toFinset.mpr ha⟩,rfl⟩)
  have budget : (2*h)*B.card < p := by
    have div := Nat.div_mul_le_self (p-1) L
    change h*L ≤ p-1 at div
    have e : (2*h)*B.card=h*L := by dsimp [L,n]; ring
    omega
  obtain ⟨t,cut⟩ := avoid B q budget
  let r (a : ZMod p) : ℤ := if ha : a ∈ P.support then (reps a ha).choose else 0
  have bounds {a} (ha : a ∈ P.support) : ((r a : ℤ) : ZMod p)=q*(a-a₀) ∧ |r a| ≤ (h:ℤ) := by
    dsimp only [r]
    rw [dif_pos ha]
    exact (reps a ha).choose_spec
  let left (a : ZMod p) : ℤ := r a+h
  let right (b : ZMod p) : ℤ := ((q*b+t).val:ℤ)-2*h
  let output (z : ZMod p) : ℤ := (q*(z-a₀)+t-h).val
  have left_inj : Set.InjOn left P.support := by
    intro a ha b hb eq
    have e : r a=r b := add_right_cancel eq
    have cc := congrArg (fun z : ℤ => (z:ZMod p)) e
    rw [(bounds ha).1,(bounds hb).1] at cc
    exact sub_left_inj.mp (mul_left_cancel₀ qnz cc)
  have right_inj : Function.Injective right := by
    intro a b eq
    have e : (((q*a+t).val:ℕ):ℤ)=((q*b+t).val:ℕ) := sub_left_inj.mp eq
    have ev : (q*a+t).val=(q*b+t).val := by exact_mod_cast e
    exact mul_left_cancel₀ qnz (add_right_cancel (ZMod.val_injective p ev))
  have out_inj : Function.Injective output := by
    intro a b eq
    dsimp only [output] at eq
    have ev : (q*(a-a₀)+t-h).val=(q*(b-a₀)+t-h).val := by exact_mod_cast eq
    exact sub_left_inj.mp (mul_left_cancel₀ qnz (add_right_cancel (sub_left_inj.mp (ZMod.val_injective p ev))))
  refine ⟨⟨left,right,output,left_inj,right_inj.injOn,out_inj.injOn,?_⟩⟩
  intro a ha b hb
  let v := q*b+t
  have lower : 2*h ≤ v.val := cut b (Set.mem_toFinset.mpr hb)
  have upper := ZMod.val_lt v
  have rad := abs_le.mp (bounds ha).2
  have range : 0 ≤ left a + right b ∧ left a + right b < (p:ℤ) := by
    change 0 ≤ r a+h+((v.val:ℤ)-2*h) ∧ r a+h+((v.val:ℤ)-2*h) < (p:ℤ)
    omega
  have cast : ((left a+right b:ℤ):ZMod p)=q*(a+b-a₀)+t-h := by
    dsimp [left,right]
    push_cast
    rw [(bounds ha).1]
    simp only [ZMod.natCast_zmod_val]
    ring
  have val := congrArg (fun z : ZMod p => (z.val:ℤ)) cast
  rw [ZMod.val_intCast, Int.emod_eq_of_lt range.1 range.2] at val
  change left a+right b = ((q*(a+b-a₀)+t-h).val:ℤ)
  omega

/-- A test with a fixed left support budget and no bound on the integer right support. -/
def OneSided (m : ℕ) : Prop :=
  ∀ (P Q : PMF ℤ), P.support.ncard ≤ m → Green28.IsUniformOnSupport (Green28.indepSum P Q) →
    Green28.IsUniformOnSupport P ∧ Green28.IsUniformOnSupport Q

private theorem transport_test {G H : Type*} [Add G] [Add H] [Nonempty G]
    {P Q : PMF G} {s : Finset G} {hs : s.Nonempty} (t : Transport P Q s H)
    (eq : sumLaw P Q = PMF.uniformOfFinset s hs)
    (test : ∀ (X Y : PMF H), X.support.ncard=P.support.ncard → Y.support.ncard=Q.support.ncard →
      Uniform (sumLaw X Y) → Uniform X ∧ Uniform Y) : Uniform P ∧ Uniform Q := by
  have supp : (sumLaw P Q).support = (s:Set G) := by rw [eq,PMF.support_uniformOfFinset]
  have push : Uniform (sumLaw (P.map t.left) (Q.map t.right)) := by
    rw [t.map_sum,uniform_map_iff (supp ▸ t.output_inj)]
    exact ⟨s,hs,eq⟩
  obtain ⟨a,b⟩ := test _ _ (by rw [PMF.support_map,t.left_inj.ncard_image])
    (by rw [PMF.support_map,t.right_inj.ncard_image]) push
  exact ⟨(uniform_map_iff t.left_inj).mp a,(uniform_map_iff t.right_inj).mp b⟩

private theorem reduce_integer {p : ℕ} [Fact p.Prime] {P Q : PMF ℤ} {s : Finset ℤ}
    (supp : (Green28.indepSum P Q).support = (s : Set ℤ)) (large : 5^(s.card+1)<p) :
    Nonempty (Transport P Q s (ZMod p)) := by
  obtain ⟨r⟩ := Green28FiniteSearch.compress supp
  have inj : Set.InjOn (fun z : ℤ => (z : ZMod p)) (Set.Icc 0 ((5^(s.card+1):ℕ):ℤ)) := by
    intro a ha b hb eq
    have e {z : ℤ} (hz : z ∈ Set.Icc 0 ((5^(s.card+1):ℕ):ℤ)) : z % (p:ℤ) = z :=
      Int.emod_eq_of_lt hz.1 (lt_of_le_of_lt hz.2 (by exact_mod_cast large))
    simpa only [e ha,e hb] using (ZMod.intCast_eq_intCast_iff' a b p).mp eq
  refine ⟨⟨fun a => (r.left a:ZMod p),fun b => (r.right b:ZMod p),fun z => (r.output z:ZMod p),
    fun _ ha _ hb e => r.left_inj ha hb (inj (r.left_bound _ ha) (r.left_bound _ hb) e),
    fun _ ha _ hb e => r.right_inj ha hb (inj (r.right_bound _ ha) (r.right_bound _ hb) e),
    fun _ ha _ hb e => r.output_inj ha hb (inj (r.output_bound _ ha) (r.output_bound _ hb) e),?_⟩⟩
  intro a ha b hb
  rw [← r.add a ha b hb,Int.cast_add]

/-- Equivalence with prime tests whose allowed right support grows with the prime.
In particular `m=4` tests every finite opposite integer law via a cubic cutoff. -/
theorem oneSided_iff_primes (m : ℕ) : OneSided m ↔
    ∀ p : ℕ, p.Prime → ∀ (P Q : PMF (ZMod p)), P.support.ncard ≤ m →
      (2*Q.support.ncard)^(m-1)<p → Uniform (sumLaw P Q) → Uniform P ∧ Uniform Q := by
  constructor
  · intro integer p prime P Q size bound ⟨s,hs,eq⟩
    let _ : Fact p.Prime := ⟨prime⟩
    have pos : 0 < Q.support.ncard := (Set.ncard_pos (Set.toFinite _)).mpr Q.support_nonempty
    have exp : P.support.ncard-1 ≤ m-1 := by omega
    obtain ⟨t⟩ := lift P Q s ((Nat.pow_le_pow_right (by omega) exp).trans_lt bound)
    exact transport_test t eq (fun X Y hx _ uniform => integer X Y (hx.trans_le size) uniform)
  · intro cyclic P Q size ⟨s,hs,eq⟩
    have supp : (Green28.indepSum P Q).support = (s:Set ℤ) := by rw [eq,PMF.support_uniformOfFinset]
    obtain ⟨p,lower,prime⟩ := Nat.exists_infinite_primes (max (5^(s.card+1)) ((2*Q.support.ncard)^(m-1))+1)
    let _ : Fact p.Prime := ⟨prime⟩
    have bound := Nat.le_max_left (5^(s.card+1)) ((2*Q.support.ncard)^(m-1))
    have budget := Nat.le_max_right (5^(s.card+1)) ((2*Q.support.ncard)^(m-1))
    obtain ⟨t⟩ := reduce_integer (p := p) supp (by omega)
    apply transport_test t eq
    intro X Y hx hy uniform
    exact cyclic p prime X Y (hx.trans_le size) (by rw [hy]; omega) uniform

/-- Every prime above 512 suffices for four atoms on each side. -/
theorem four_atom_prime {p : ℕ} [Fact p.Prime] (large : 512 < p) {P Q : PMF (ZMod p)}
    (hp : P.support.ncard ≤ 4) (hq : Q.support.ncard ≤ 4) (u : Uniform (sumLaw P Q)) :
    Uniform P ∧ Uniform Q := by
  obtain ⟨s,hs,eq⟩ := u
  have pos : 0 < Q.support.ncard := (Set.ncard_pos (Set.toFinite _)).mpr Q.support_nonempty
  have budget : (2*Q.support.ncard)^(P.support.ncard-1) ≤ 8^3 :=
    (Nat.pow_le_pow_right (by omega) (by omega)).trans (Nat.pow_le_pow_left (by omega) 3)
  obtain ⟨t⟩ := lift P Q s (budget.trans_lt large)
  exact transport_test t eq (fun _ _ hx hy uniform =>
    Green28FourAtomLaws.uniform_of_at_most_four_atoms uniform (hx.trans_le hp) (hy.trans_le hq))

/-- Ratios of positive masses suffice, since masses off the support vanish. -/
def RationalRatios {G : Type*} (P : PMF G) : Prop :=
  ∀ x ∈ P.support, ∀ y ∈ P.support, ∃ r : ℚ, (r : ℝ)=(P x).toReal/(P y).toReal

private theorem rational_push {G : Type*} {P : PMF G} {f : G → ℤ}
    (mass : ∀ x ∈ P.support, P.map f (f x)=P x) (rat : RationalRatios P) :
    Green28UniformSums.RationalRatios (P.map f) := by
  intro x y hy
  by_cases hx : x ∈ (P.map f).support
  · rw [PMF.support_map] at hx hy
    obtain ⟨a,ha,rfl⟩ := hx
    obtain ⟨b,hb,rfl⟩ := hy
    rw [mass a ha,mass b hb]
    exact rat a ha b hb
  · exact ⟨0,by simp [(P.map f).apply_eq_zero_iff x |>.mpr hx]⟩

/-- Unconditional obstruction in the asymmetric range. Rational probability
ratios on either side force uniformity of both original cyclic laws. -/
theorem uniform_of_rational_ratios {p : ℕ} [Fact p.Prime] {P Q : PMF (ZMod p)}
    (large : (2*Q.support.ncard)^(P.support.ncard-1)<p) (u : Uniform (sumLaw P Q))
    (rat : RationalRatios P ∨ RationalRatios Q) : Uniform P ∧ Uniform Q := by
  obtain ⟨s,hs,eq⟩ := u
  have supp : (sumLaw P Q).support = (s:Set (ZMod p)) := by rw [eq,PMF.support_uniformOfFinset]
  obtain ⟨t⟩ := lift P Q s large
  have masses := t.masses supp
  have uniform : Green28.IsUniformOnSupport (Green28.indepSum (P.map t.left) (Q.map t.right)) := by
    change Uniform (sumLaw _ _)
    rw [t.map_sum,uniform_map_iff (supp ▸ t.output_inj)]
    exact ⟨s,hs,eq⟩
  obtain ⟨l,r⟩ := Green28UniformSums.uniform_of_rational_ratios uniform
    (rat.imp (rational_push masses.1) (rational_push masses.2.1))
  exact ⟨(uniform_map_iff t.left_inj).mp l,(uniform_map_iff t.right_inj).mp r⟩

#print axioms narrow
#print axioms avoid
#print axioms lift
#print axioms oneSided_iff_primes
#print axioms four_atom_prime
#print axioms uniform_of_rational_ratios

end Green28AsymmetricSupports
