import Green28CyclicLaws
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas

/-! A single involution for testing uniform independent sums. -/

namespace Green28DigitTranspose

/-- Pack two digits into the block beginning at the cube of the radix. -/
def pack (r i j : ℕ) : ℕ := r^3+i+r*j

/-- Transpose the two base-`r` digits in the first square of each cubic block.
All other integers are fixed. The radix is recovered from the input alone. -/
def transpose (z : ℤ) : ℤ :=
  let n := z.toNat
  let r := Nat.nthRoot 3 n
  let s := n-r^3
  if 0 ≤ z ∧ s < r^2 then (pack r (s/r) (s%r) : ℕ) else z

private theorem digits_lt {r i j : ℕ} (hi : i < r) (hj : j < r) : i+r*j < r^2 := by
  have h := Nat.mul_le_mul_left r (show j+1 ≤ r by omega)
  nlinarith

theorem transpose_pack {r i j : ℕ} (hi : i < r) (hj : j < r) :
    transpose (pack r i j) = pack r j i := by
  have hr : 0 < r := by omega
  have lim := digits_lt hi hj
  have root : Nat.nthRoot 3 (pack r i j)=r := Nat.nthRoot_eq_of_le_of_lt
    (by unfold pack; omega) (by unfold pack; nlinarith [sq_nonneg (r:ℤ)])
  have off : pack r i j-r^3=i+r*j := by unfold pack; omega
  simp only [transpose,Int.toNat_natCast,root,off,Int.natCast_nonneg,lim,and_self,if_true]
  rw [Nat.add_mul_div_left _ _ hr,Nat.div_eq_of_lt hi,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hi,zero_add]

/-- Applying the fixed integer relabelling twice recovers every integer. -/
theorem transpose_involutive : Function.Involutive transpose := by
  intro z
  let r := Nat.nthRoot 3 z.toNat
  let s := z.toNat-r^3
  by_cases inside : 0 ≤ z ∧ s < r^2
  · have hr : 0 < r := by
      by_contra! h
      have zero : r=0 := by omega
      simpa [zero] using inside.2
    have hi := Nat.mod_lt s hr
    have hj : s/r < r := (Nat.div_lt_iff_lt_mul hr).mpr (by simpa [pow_two] using inside.2)
    have root_le : r^3 ≤ z.toNat := Nat.pow_nthRoot_le_iff.mpr (Or.inl (by decide))
    have eq : (pack r (s%r) (s/r) : ℤ)=z := by
      have d := Nat.mod_add_div s r
      have e : pack r (s%r) (s/r) = z.toNat := by dsimp [pack,s] at *; omega
      rw [e,Int.toNat_of_nonneg inside.1]
    rw [←eq,transpose_pack hi hj,transpose_pack hj hi]
  · have fix : transpose z=z := if_neg inside
    rw [fix,fix]

open Green28 Green28CyclicLaws Finset
open scoped ENNReal

/-- Joint law of two independent samples, retaining both coordinates. -/
noncomputable def pairLaw (P Q : PMF ℤ) : PMF (ℤ×ℤ) :=
  P.bind fun x => Q.bind fun y => PMF.pure (x,y)

theorem pairLaw_apply (P Q : PMF ℤ) (x y : ℤ) : pairLaw P Q (x,y) = P x*Q y := by
  classical
  unfold pairLaw
  rw [PMF.bind_apply,tsum_eq_single x]
  · rw [PMF.bind_apply,tsum_eq_single y]
    · simp
    · intro j ne
      simp [PMF.pure_apply,Ne.symm ne]
  · intro i ne
    simp [PMF.bind_apply,PMF.pure_apply,Ne.symm ne]

private theorem pair_support (P Q : PMF ℤ) (v : ℤ×ℤ) :
    v ∈ (pairLaw P Q).support ↔ v.1 ∈ P.support ∧ v.2 ∈ Q.support := by
  rcases v with ⟨x,y⟩
  simp [PMF.mem_support_iff,pairLaw_apply]

private theorem pair_uniform {S T : Finset ℤ} (hs : S.Nonempty) (ht : T.Nonempty) :
    pairLaw (PMF.uniformOfFinset S hs) (PMF.uniformOfFinset T ht) =
      PMF.uniformOfFinset (S ×ˢ T) (hs.product ht) := by
  ext ⟨x,y⟩
  rw [pairLaw_apply]
  by_cases hx : x∈S <;> by_cases hy : y∈T <;>
    simp [PMF.uniformOfFinset_apply,hx,hy,Finset.card_product,ENNReal.mul_inv]

private theorem map_swap (P Q : PMF ℤ) : (pairLaw P Q).map Prod.swap=pairLaw Q P := by
  simp only [pairLaw,PMF.map_bind,PMF.pure_map,Prod.swap_prod_mk]
  exact PMF.bind_comm _ _ _

/-- The two coordinates of a sum of independent product laws are independent. -/
private theorem pair_sum (P Q R S : PMF ℤ) :
    sumLaw (pairLaw P Q) (pairLaw R S) = pairLaw (indepSum P R) (indepSum Q S) := by
  simp only [sumLaw,pairLaw,indepSum,Bind.bind,PMF.bind_bind,PMF.pure_bind,Prod.mk_add_mk]
  congr 1
  funext x
  exact PMF.bind_comm _ _ _

private theorem sum_swap (P Q : PMF ℤ) : indepSum Q P=indepSum P Q := by
  change (Q.bind fun y => P.bind fun x => PMF.pure (y+x)) = _
  rw [PMF.bind_comm]
  simp only [indepSum,Bind.bind,add_comm]

private def encode (r shift base : ℤ) (v : ℤ×ℤ) : ℤ :=
  base+(v.1+shift)+r*(v.2+shift)

private theorem encode_inj {r shift base : ℤ} (hr : 0 < r) {v w : ℤ×ℤ}
    (vā : 0 ≤ v.1+shift) (vlt : v.1+shift < r)
    (wā : 0 ≤ w.1+shift) (wlt : w.1+shift < r)
    (eq : encode r shift base v=encode r shift base w) : v=w := by
  have digits : v.1+shift+r*(v.2+shift)=w.1+shift+r*(w.2+shift) := by
    unfold encode at eq
    linarith
  have modEq := congrArg (fun z : ℤ => z%r) digits
  simp only [Int.add_mul_emod_self_left,Int.emod_eq_of_lt vā vlt,Int.emod_eq_of_lt wā wlt] at modEq
  have first : v.1=w.1 := by omega
  have second : v.2=w.2 := by
    have eq' : r*(v.2+shift)=r*(w.2+shift) := by omega
    exact add_right_cancel ((mul_left_cancel₀ hr.ne') eq')
  exact Prod.ext first second

private theorem transpose_encode {r : ℕ} {s : ℤ} (v : ℤ×ℤ)
    (bounds : 0≤v.1+s ∧ v.1+s < r ∧ 0≤v.2+s ∧ v.2+s < r) :
    transpose (encode r s ((r:ℤ)^3) v)=encode r s ((r:ℤ)^3) v.swap := by
  let i := (v.1+s).toNat
  let j := (v.2+s).toNat
  have ei : (i:ℤ)=v.1+s := Int.toNat_of_nonneg bounds.1
  have ej : (j:ℤ)=v.2+s := Int.toNat_of_nonneg bounds.2.2.1
  have hi : i < r := by omega
  have hj : j < r := by omega
  simpa only [pack,Nat.cast_add,Nat.cast_pow,Nat.cast_mul,ei,ej,encode,Prod.fst_swap,Prod.snd_swap]
    using transpose_pack hi hj

private theorem map_on_support {G H : Type*} (P : PMF G) (f g : G → H)
    (agree : ∀ x∈P.support, f x=g x) : P.map f=P.map g := by
  ext y
  rw [PMF.map_apply,PMF.map_apply]
  apply tsum_congr
  intro x
  by_cases hx : x∈P.support
  · rw [agree x hx]
  · simp [(P.apply_eq_zero_iff _).mpr hx]

private theorem encoded_sum {P Q : PMF (ℤ×ℤ)} (r s b : ℤ) :
    indepSum (P.map (encode r s b)) (Q.map (encode r s b)) =
      (sumLaw P Q).map (encode r (2*s) (2*b)) := by
  simp only [indepSum,sumLaw,Bind.bind,PMF.bind_map,PMF.map_bind,PMF.pure_map,Function.comp_def]
  congr 1
  funext x
  congr 1
  funext y
  apply congrArg PMF.pure
  simp only [encode,Prod.fst_add,Prod.snd_add]
  ring

private theorem ratios_of_flat_pair {P Q : PMF ℤ} (joint : Uniform (pairLaw P Q)) :
    Green28UniformSums.RationalRatios P := by
  obtain ⟨S,ne,e⟩ := joint
  obtain ⟨y,hy⟩ := Q.support_nonempty
  have on (x : ℤ) (hx : x∈P.support) : P x*Q y=(S.card:ℝ≥0∞)⁻¹ := by
    have m := (pair_support P Q (x,y)).mpr ⟨hx,hy⟩
    rw [e,PMF.support_uniformOfFinset] at m
    rw [←pairLaw_apply,e,PMF.uniformOfFinset_apply_of_mem ne m]
  intro x z hz
  by_cases hx : x∈P.support
  · have same := (ENNReal.mul_left_inj ((Q.mem_support_iff _).mp hy) (Q.apply_ne_top _)).mp
      ((on x hx).trans (on z hz).symm)
    have pos := ENNReal.toReal_pos ((P.mem_support_iff _).mp hz) (P.apply_ne_top _)
    exact ⟨1,by rw [same]; simp [pos.ne']⟩
  · exact ⟨0,by simp [(P.apply_eq_zero_iff _).mpr hx]⟩

private theorem mass_at_unique_image {α β : Type*} (p : PMF α) (f : α → β) (v : α)
    (unique : ∀ w∈p.support, f w=f v → w=v) : p.map f (f v)=p v := by
  classical
  rw [PMF.map_apply,tsum_eq_single v]
  · simp
  · intro w ne
    by_cases hw : w∈p.support
    · simp [show f v ≠ f w from fun e => ne (unique w hw e.symm)]
    · simp [(p.apply_eq_zero_iff w).mpr hw]

/-- The product law attains the common output mass at the rightmost pair.
Every other pair contributes at most that much to its own sum. -/
private theorem joint_peak {P Q : PMF ℤ} {S : Finset ℤ} (ne : S.Nonempty)
    (eq : indepSum P Q=PMF.uniformOfFinset S ne) :
    ∃ v∈(pairLaw P Q).support, pairLaw P Q v=(S.card:ℝ≥0∞)⁻¹ ∧
      ∀ w∈(pairLaw P Q).support, pairLaw P Q w≤(S.card:ℝ≥0∞)⁻¹ := by
  classical
  let J := pairLaw P Q
  let add := fun w : ℤ×ℤ => w.1+w.2
  have sum : J.map add=PMF.uniformOfFinset S ne := by
    simpa only [J,add,pairLaw,PMF.map_bind,PMF.pure_map,indepSum,Bind.bind] using eq
  have at_sum (w : ℤ×ℤ) (hw : w∈J.support) : J.map add (add w)=(S.card:ℝ≥0∞)⁻¹ := by
    have occ : add w∈(J.map add).support := (PMF.mem_support_map_iff _ _ _).mpr ⟨w,hw,rfl⟩
    rw [sum,PMF.support_uniformOfFinset] at occ
    exact sum ▸ PMF.uniformOfFinset_apply_of_mem ne occ
  obtain ⟨⟨a,ha,topA,_⟩,⟨b,hb,topB,_⟩⟩ := Green28UniformSums.endpoint_weights ⟨S,ne,eq⟩
  have corner := (pair_support P Q (a,b)).mpr ⟨ha,hb⟩
  have single : J.map add (add (a,b))=J (a,b) := by
    apply mass_at_unique_image
    rintro ⟨x,y⟩ hw he
    obtain ⟨hx,hy⟩ := (pair_support _ _ _).mp hw
    have lx := topA _ hx
    have ly := topB _ hy
    change x+y=a+b at he
    exact Prod.ext (by dsimp; omega) (by dsimp; omega)
  refine ⟨(a,b),corner,single.symm.trans (at_sum _ corner),?_⟩
  intro w hw
  rw [←at_sum _ hw,PMF.map_apply]
  simpa [J] using ENNReal.le_tsum (f := fun u => if add w=add u then J u else 0) w

/-- The synthesized marginal lives in one cubic block. Its independent sum
with the relabelled copy is uniform on exactly the square of the old number
of outcomes. Uniformity of the marginal recovers both original laws. -/
structure SquareLift (P Q : PMF ℤ) (k : ℕ) where
  law : PMF ℤ
  finite : law.support.Finite
  label : ℤ×ℤ → ℤ
  label_inj : Set.InjOn label (pairLaw P Q).support
  law_eq : law=(pairLaw P Q).map label
  radix : ℕ
  block : ∀ z∈law.support, (radix:ℤ)^3 ≤ z ∧ z < (radix:ℤ)^3+(radix:ℤ)^2
  outcomes : Finset ℤ
  inhabited : outcomes.Nonempty
  size : outcomes.card=k^2
  sum_eq : indepSum law (law.map transpose)=PMF.uniformOfFinset outcomes inhabited
  peak : ∃ z∈law.support, law z=(k:ℝ≥0∞)⁻¹ ∧ ∀ x, law x≤(k:ℝ≥0∞)⁻¹
  uniform_iff : IsUniformOnSupport law ↔ IsUniformOnSupport P ∧ IsUniformOnSupport Q

/-- Construct a single-law square witness for an arbitrary uniform independent
sum in the original pinned statement. -/
theorem exists_square_lift {P Q : PMF ℤ} {S : Finset ℤ} (ne : S.Nonempty)
    (eq : indepSum P Q=PMF.uniformOfFinset S ne) : Nonempty (SquareLift P Q S.card) := by
  classical
  obtain ⟨pf,qf⟩ := Green28UniformSums.finite_of_uniform_sum ⟨S,ne,eq⟩
  obtain ⟨N,bound⟩ := ((pf.union qf).image Int.natAbs).exists_le
  have box (z : ℤ) (hz : z ∈ P.support ∪ Q.support) : -(N:ℤ) ≤ z ∧ z ≤ N := by
    have lim := bound (z.natAbs) ⟨z,hz,rfl⟩
    omega
  let r := 4*N+1
  have rp : 0 < (r:ℤ) := by dsimp [r]; positivity
  let E := encode r N ((r:ℤ)^3)
  let H := encode r (2*(N:ℤ)) (2*(r:ℤ)^3)
  have digits (z : ℤ) (hz : z∈P.support ∪ Q.support) : 0≤z+N ∧ z+N < r := by
    obtain ⟨lo,hi⟩ := box z hz
    dsimp [r]; omega
  have inj : Set.InjOn E (pairLaw P Q).support := by
    intro v hv w hw he
    have h := digits v.1 (Or.inl ((pair_support _ _ _).mp hv).1)
    have k := digits w.1 (Or.inl ((pair_support _ _ _).mp hw).1)
    exact encode_inj rp h.1 h.2 k.1 k.2 he
  have switch : ((pairLaw P Q).map E).map transpose=(pairLaw Q P).map E := by
    rw [←map_swap P Q,PMF.map_comp,PMF.map_comp]
    apply map_on_support
    intro v hv
    obtain ⟨hx,hy⟩ := (pair_support _ _ _).mp hv
    have x := digits _ (Or.inl hx)
    have y := digits _ (Or.inr hy)
    exact transpose_encode v ⟨x.1,x.2,y⟩
  have boundS (z : ℤ) (hz : z∈S) : 0≤z+2*(N:ℤ) ∧ z+2*(N:ℤ) < r := by
    have occ : z∈(indepSum P Q).support := by rwa [eq,PMF.support_uniformOfFinset]
    obtain ⟨x,hx,y,hy,e⟩ := Green28FiniteSearch.mem_support_indepSum.mp occ
    have p := box _ (Or.inl hx)
    have q := box _ (Or.inr hy)
    dsimp [r]; omega
  let sq := S ×ˢ S
  have sqne : sq.Nonempty := ne.product ne
  have hout : Set.InjOn H (sq : Set (ℤ×ℤ)) := by
    intro v hv w hw he
    have h := boundS v.1 (Finset.mem_product.mp hv).1
    have k := boundS w.1 (Finset.mem_product.mp hw).1
    exact encode_inj rp h.1 h.2 k.1 k.2 he
  have finprod : (pairLaw P Q).support.Finite := (pf.prod qf).subset (fun v hv => (pair_support _ _ v).mp hv)
  refine ⟨⟨(pairLaw P Q).map E,?_,E,inj,rfl,r,?_,sq.image H,sqne.image _,?_,?_,?_,?_⟩⟩
  · rw [PMF.support_map]; exact finprod.image E
  · intro z hz
    obtain ⟨v,hv,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
    obtain ⟨hx,hy⟩ := (pair_support _ _ _).mp hv
    have x := digits _ (Or.inl hx)
    have y := digits _ (Or.inr hy)
    change _ ≤ encode _ _ _ v ∧ encode _ _ _ v < _
    unfold encode
    have ub : v.2+N+1 ≤ r := by omega
    have add := mul_le_mul_of_nonneg_left ub rp.le
    have non := mul_nonneg rp.le y.1
    constructor <;> nlinarith
  · rw [Finset.card_image_of_injOn hout,Finset.card_product,pow_two]
  · rw [switch,encoded_sum,pair_sum,sum_swap P Q,eq,pair_uniform ne ne]
    change (PMF.uniformOfFinset sq sqne).map H=PMF.uniformOfFinset (sq.image H) (sqne.image H)
    apply PMF.ext
    intro z
    by_cases hz : z∈sq.image H
    · obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hz
      rw [PMF.map_apply,tsum_eq_single v]
      · simp [PMF.uniformOfFinset_apply_of_mem sqne hv,PMF.uniformOfFinset_apply_of_mem (sqne.image _) (Finset.mem_image_of_mem _ hv),
          Finset.card_image_of_injOn hout]
      · intro w ne'
        by_cases hw : w∈sq
        · simp [show H v ≠ H w from fun he => ne' (hout hv hw he).symm]
        · simp [PMF.uniformOfFinset_apply_of_notMem sqne hw]
    · rw [PMF.uniformOfFinset_apply_of_notMem _ hz]
      apply (PMF.apply_eq_zero_iff _ _).mpr
      rwa [PMF.support_map,PMF.support_uniformOfFinset,←Finset.coe_image]
  · obtain ⟨v,hv,at_v,boundv⟩ := joint_peak ne eq
    let J := pairLaw P Q
    have at_image (w : ℤ×ℤ) (hw : w∈J.support) : J.map E (E w)=J w :=
      mass_at_unique_image J E w (fun u hu e => inj hu hw e)
    refine ⟨E v,(PMF.mem_support_map_iff _ _ _).mpr ⟨v,hv,rfl⟩,(at_image v hv).trans at_v,?_⟩
    intro x
    by_cases hx : x∈(J.map E).support
    · obtain ⟨w,hw,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
      exact (at_image w hw).le.trans (boundv w hw)
    · exact ((J.map E).apply_eq_zero_iff _ |>.mpr hx).le.trans bot_le
  · change Uniform _ ↔ _
    rw [uniform_map_iff inj]
    constructor
    · intro h
      exact Green28UniformSums.uniform_of_rational_ratios ⟨S,ne,eq⟩ (Or.inl (ratios_of_flat_pair h))
    · rintro ⟨⟨A,an,p⟩,⟨B,bn,q⟩⟩
      exact ⟨A ×ˢ B,an.product bn,p ▸ q ▸ pair_uniform an bn⟩

/-- The left side is the statement of the pinned Green 28 declaration.
On the right only one law varies, its partner is determined by a fixed
integer involution, and the output size is a square. -/
theorem green_28_iff_single_square :
    (∀ P Q : PMF ℤ, P.support.Finite ∧ Q.support.Finite ∧ IsUniformOnSupport (indepSum P Q) →
      IsUniformOnSupport P ∧ IsUniformOnSupport Q) ↔
    (∀ (R : PMF ℤ) (r k : ℕ) (V : Finset ℤ) (hv : V.Nonempty), R.support.Finite →
      (∀ z∈R.support, (r:ℤ)^3 ≤ z ∧ z < (r:ℤ)^3+(r:ℤ)^2) →
      (∃ z∈R.support, R z=(k:ℝ≥0∞)⁻¹ ∧ ∀ x, R x≤(k:ℝ≥0∞)⁻¹) →
      V.card = k^2 → indepSum R (R.map transpose) = PMF.uniformOfFinset V hv →
      IsUniformOnSupport R) := by
  constructor
  · intro conject R r k V hv fin _ _ _ u
    have mapped : (R.map transpose).support.Finite := by rw [PMF.support_map]; exact fin.image transpose
    exact (conject R (R.map transpose) ⟨fin,mapped,V,hv,u⟩).1
  · rintro test P Q ⟨_,_,S,ne,eq⟩
    obtain ⟨L⟩ := exists_square_lift ne eq
    exact L.uniform_iff.mp
      (test L.law L.radix S.card L.outcomes L.inhabited L.finite L.block L.peak L.size L.sum_eq)

#print axioms transpose_pack
#print axioms transpose_involutive
#print axioms pairLaw_apply
#print axioms exists_square_lift
#print axioms green_28_iff_single_square

end Green28DigitTranspose
