import Mathlib
import Green33TailEnergy
import Green33StrictReduction
import Green33GraphHistogram

/-! Reflection rigidity for the graph layer of a two-layer strict sum cover. -/

open Finset

namespace Green33GraphRows

/-- Compare a covering sum row with a difference row of the same total size.
The ordered sum row has two witnesses for every color. -/
theorem row_comparison {K : Type*} [Fintype K] (a b : K → ℕ) (h : ℕ)
    (ha : ∀ z, 2 ≤ a z) (hsa : ∑ z, a z = 2*Fintype.card K+h)
    (hsb : ∑ z, b z = 2*Fintype.card K+h) :
    (∑ z, a z^2)+h ≤ (∑ z, b z^2)+h^2 := by
  classical
  let e := fun z => a z-2
  have he (z : K) : a z=e z+2 := by dsimp [e]; have := ha z; omega
  have hes : ∑ z, e z = h := by
    simp_rw [he] at hsa
    simp only [sum_add_distrib,sum_const,card_univ,smul_eq_mul] at hsa
    omega
  have heu (z : K) : e z ≤ h := by
    rw [← hes]
    exact single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ z)
  have hess : ∑ z, e z^2 ≤ h^2 := by
    calc
      _ ≤ ∑ z, e z*h := sum_le_sum fun z _ => by rw [sq]; exact Nat.mul_le_mul_left _ (heu z)
      _ = _ := by rw [← sum_mul,hes,sq]
  have ha₂ : ∑ z, a z^2 = (∑ z, e z^2)+4*h+4*Fintype.card K := by
    calc
      _ = ∑ z, (e z^2+4*e z+4) := sum_congr rfl fun z _ => by rw [he]; ring
      _ = _ := by simp only [sum_add_distrib,← mul_sum,hes,sum_const,card_univ,smul_eq_mul]; ring
  have hlow (z : K) : 5*b z ≤ b z^2+6 := by
    generalize b z = n
    rcases n with _ | _ | _ | n
    · decide
    · decide
    · decide
    · nlinarith [Nat.zero_le (n*n)]
  have hb₂ := sum_le_sum (s := (univ : Finset K)) (fun z _ => hlow z)
  simp only [← mul_sum,hsb,sum_add_distrib,sum_const,card_univ,smul_eq_mul] at hb₂
  omega

/-- If every nonzero sum row covers strictly, the exceptional row carries
nearly the full zero-difference energy. p and q are the two group orders. -/
theorem exceptional_row_energy {H K : Type*} [Fintype H] [Fintype K] [Zero H]
    [DecidableEq H] [Zero K] (s d : H → K → ℕ) (h : ℕ)
    (hsize : Fintype.card H=2*Fintype.card K+h)
    (hsm : ∀ r, ∑ z, s r z=Fintype.card H) (hdm : ∀ r, ∑ z, d r z=Fintype.card H)
    (hcover : ∀ r, r ≠ 0 → ∀ z, 2 ≤ s r z)
    (hdiag : d 0 0=Fintype.card H)
    (he : ∑ r, ∑ z, s r z^2 = ∑ r, ∑ z, d r z^2) :
    (Fintype.card H)^2+(Fintype.card H-1)*h ≤
      (∑ z, s 0 z^2)+(Fintype.card H-1)*h^2 := by
  classical
  let I : Finset H := univ.erase 0
  have hI : I.card=Fintype.card H-1 := by simp [I]
  have hcmp := sum_le_sum (s := I) (fun r hr => row_comparison (s r) (d r) h
    (hcover r (ne_of_mem_erase (by exact hr))) ((hsm r).trans hsize) ((hdm r).trans hsize))
  simp only [sum_add_distrib,sum_const,smul_eq_mul,hI] at hcmp
  have hs := sum_erase_add (univ : Finset H) (fun r => ∑ z, s r z^2) (mem_univ 0)
  have hd := sum_erase_add (univ : Finset H) (fun r => ∑ z, d r z^2) (mem_univ 0)
  change (∑ r ∈ I, ∑ z, s r z^2)+_= _ at hs
  change (∑ r ∈ I, ∑ z, d r z^2)+_= _ at hd
  have h0 : (Fintype.card H)^2 ≤ ∑ z, d 0 z^2 := by
    rw [← hdiag]
    exact single_le_sum (f := fun z : K => d 0 z^2) (fun _ _ => Nat.zero_le _) (mem_univ (0:K))
  omega

/-- At excess three, at most three domain elements miss one reflection. -/
theorem almost_reflection_three {K : Type*} [Fintype K] [Nonempty K]
    (s : K → ℕ) {p : ℕ} (hp : 14 ≤ p) (hs : ∑ z, s z=p)
    (he : p^2 ≤ (∑ z, s z^2)+6*(p-1)) : ∃ z, p ≤ s z+3 := by
  classical
  obtain ⟨z,_,hz⟩ := exists_max_image univ s univ_nonempty
  refine ⟨z,?_⟩
  have hbound : ∑ x, s x^2 ≤ s z*p := by
    rw [← hs,mul_sum]
    exact sum_le_sum fun x hx => by rw [sq]; exact Nat.mul_le_mul_right _ (hz x hx)
  have hfour : 4 ≤ s z := by
    by_contra! h
    have := Nat.mul_le_mul_right p (by omega : s z ≤ 3)
    have := Nat.mul_le_mul_left p hp
    nlinarith [Nat.sub_add_cancel (show 1 ≤ p by omega)]
  let I : Finset K := univ.erase z
  have hsum := sum_erase_add (univ : Finset K) s (mem_univ z)
  change (∑ x ∈ I, s x)+s z= _ at hsum
  let t := ∑ x ∈ I, s x
  have ht : t+s z=p := hsum.trans hs
  have hrest : ∑ x ∈ I, s x^2 ≤ t^2 := by
    calc
      _ ≤ ∑ x ∈ I, s x*t := sum_le_sum fun x hx => by
        have hxt : s x ≤ t := single_le_sum (fun _ _ => Nat.zero_le _) hx
        rw [sq]; exact Nat.mul_le_mul_left _ hxt
      _ = _ := by rw [← sum_mul,sq]
  have hsq := sum_erase_add (univ : Finset K) (fun x => s x^2) (mem_univ z)
  change (∑ x ∈ I, s x^2)+_= _ at hsq
  by_contra! h
  have ht4 : 4 ≤ t := by omega
  have h₁ : s z-4+4=s z := by omega
  have h₂ : t-4+4=t := by omega
  have hmul : 4*p ≤ s z*t+16 := by
    rw [← ht,← h₁,← h₂]
    nlinarith [Nat.zero_le ((s z-4)*(t-4))]
  have h13 : p≤13 := by
    nlinarith only [he,hrest,hsq,hmul,congrArg (fun x : ℕ => x^2) ht,
      Nat.sub_add_cancel (show 1 ≤ p by omega)]
  omega

section Graph

variable {H K : Type*} [AddCommGroup H] [AddCommGroup K]
    [Fintype H] [Fintype K] [DecidableEq H] [DecidableEq K]

/-- Every nonzero row of the graph contains each color as a sum with distinct inputs. -/
def CoversRows (f : H → K) : Prop := ∀ r : H, r ≠ 0 → ∀ z : K,
  ∃ a b : H, a ≠ b ∧ a+b=r ∧ f a+f b=z

def sumRow (f : H → K) (r : H) (z : K) : ℕ :=
  (univ.filter fun a => f a+f (r-a)=z).card

private def diffRow (f : H → K) (r : H) (z : K) : ℕ :=
  (univ.filter fun a => f a-f (a-r)=z).card

private def graph (f : H → K) : Finset (H × K) :=
  univ.filter (fun x => x.2=f x.1)

private theorem graph_sums (f : H → K) (r : H) (z : K) :
    Green33Multiplicity.reps (graph f) (r,z) = sumRow f r z := by
  apply card_bij (fun x _ => x.1.1)
  · rintro ⟨⟨a,u⟩,b,v⟩ hx
    simp [graph,Prod.mk_add_mk] at hx
    simp only [mem_filter,mem_univ,true_and]
    obtain ⟨⟨rfl,rfl⟩,rfl,rfl⟩ := hx
    simp
  · rintro ⟨⟨a,u⟩,b,v⟩ hx ⟨⟨a',u'⟩,b',v'⟩ hy h
    change a=a' at h
    subst a'
    simp [graph,Prod.mk_add_mk] at hx hy
    obtain ⟨⟨rfl,rfl⟩,hr,_⟩ := hx
    obtain ⟨⟨rfl,rfl⟩,hr',_⟩ := hy
    simp [add_left_cancel (hr.trans hr'.symm)]
  · intro a ha
    have haz := (mem_filter.mp ha).2
    refine ⟨((a,f a),(r-a,f (r-a))),?_,rfl⟩
    simp [graph,Prod.mk_add_mk,haz]

private theorem graph_diffs (f : H → K) (r : H) (z : K) :
    Green33TailEnergy.diffReps (graph f) (r,z) = diffRow f r z := by
  apply card_bij (fun x _ => x.1.1)
  · rintro ⟨⟨a,u⟩,b,v⟩ hx
    simp [graph,Prod.mk_sub_mk] at hx
    simp only [mem_filter,mem_univ,true_and]
    obtain ⟨⟨rfl,rfl⟩,rfl,rfl⟩ := hx
    simp
  · rintro ⟨⟨a,u⟩,b,v⟩ hx ⟨⟨a',u'⟩,b',v'⟩ hy h
    change a=a' at h
    subst a'
    simp [graph,Prod.mk_sub_mk] at hx hy
    obtain ⟨⟨rfl,rfl⟩,hr,_⟩ := hx
    obtain ⟨⟨rfl,rfl⟩,hr',_⟩ := hy
    simp [sub_right_inj.mp (hr.trans hr'.symm)]
  · intro a ha
    have haz := (mem_filter.mp ha).2
    refine ⟨((a,f a),(a-r,f (a-r))),?_,rfl⟩
    simp [graph,Prod.mk_sub_mk,haz]

private theorem graph_energy (f : H → K) :
    ∑ r, ∑ z, sumRow f r z^2 = ∑ r, ∑ z, diffRow f r z^2 := by
  have e := Green33TailEnergy.centered_energy_eq (graph f) 0
  simp only [sub_zero] at e
  have ee : ∑ w, Green33Multiplicity.reps (graph f) w^2 =
    ∑ w, Green33TailEnergy.diffReps (graph f) w^2 := by exact_mod_cast e
  simpa only [Fintype.sum_prod_type,graph_sums,graph_diffs] using ee

omit [DecidableEq H] in
private theorem sum_row_total (f : H → K) (r : H) : ∑ z, sumRow f r z = Fintype.card H := by
  simpa [sumRow] using sum_card_fiberwise_eq_card_filter (univ : Finset H)
    (univ : Finset K) (fun a => f a+f (r-a))

/-- Exact lower bound for the zero-row energy of a graph covering all other rows. -/
theorem graph_reflection_energy {f : H → K} (hf : CoversRows f) (h : ℕ)
    (hs : Fintype.card H=2*Fintype.card K+h) :
    Fintype.card H^2+(Fintype.card H-1)*h ≤
      (∑ z, sumRow f 0 z^2)+(Fintype.card H-1)*h^2 := by
  apply exceptional_row_energy (sumRow f) (diffRow f) h hs (sum_row_total f)
  · intro r
    simpa [diffRow] using sum_card_fiberwise_eq_card_filter (univ : Finset H)
      (univ : Finset K) (fun a => f a-f (a-r))
  · intro r hr z
    obtain ⟨a,b,hab,rfl,rfl⟩ := hf r hr z
    have H : ({a,b} : Finset H) ⊆ univ.filter (fun x => f x+f (a+b-x)=f a+f b) := by
      intro x hx
      rcases mem_insert.mp hx with rfl | hx
      · simp
      · obtain rfl := mem_singleton.mp hx
        simp [add_comm]
    simpa [sumRow,hab] using card_le_card H
  · simp [diffRow]
  · exact graph_energy f

/-- For input order 2q+3 at least 14, all but at most three points of the graph
are paired under a single reflection whose first coordinate is zero. -/
theorem graph_reflection_three {f : H → K} (hf : CoversRows f)
    (hs : Fintype.card H=2*Fintype.card K+3) (hp : 14 ≤ Fintype.card H) :
    ∃ z, Fintype.card H ≤ (univ.filter fun a => f a+f (-a)=z).card+3 := by
  have he := graph_reflection_energy hf 3 hs
  have h := almost_reflection_three (sumRow f 0) hp (sum_row_total f 0) (by omega)
  simpa [sumRow] using h

end Graph

section Order238

private abbrev X := ZMod 17
private abbrev Y := ZMod 7

private def offset (t : Fin 8) : X := (t.val: X)+1

private def place : Option (Bool × Fin 8) → X
  | none => 0
  | some (false,t) => offset t
  | some (true,t) => -offset t

private noncomputable def places : Option (Bool × Fin 8) ≃ X :=
  Equiv.ofBijective place (by decide +kernel)

private theorem sum_around {V : Type*} [AddCommMonoid V] (g : X → V) (i : X) :
    ∑ a, g a = g i+∑ t : Fin 8, (g (i+offset t)+g (i-offset t)) := by
  let e := places.trans (Equiv.addLeft i)
  rw [← e.sum_comp g]
  rw [Fintype.sum_option,Fintype.sum_prod_type,Fintype.sum_bool,sum_add_distrib]
  simp [e,places,place,sub_eq_add_neg,add_comm]

private def pairColor (f : X → Y) (i : X) (t : Fin 8) : Y :=
  f (i+offset t)+f (i-offset t)

private theorem offsets_pair (a i : X) (h : a ≠ i) :
    ∃ t : Fin 8, a=i+offset t ∨ a=i-offset t := by
  obtain ⟨v,hv⟩ := places.surjective (a-i)
  rcases v with _ | ⟨b,t⟩
  · change 0=a-i at hv
    exact (h (sub_eq_zero.mp hv.symm)).elim
  · refine ⟨t,?_⟩
    cases b
    · left
      change offset t=a-i at hv
      rw [hv]; abel
    · right
      change -offset t=a-i at hv
      rw [sub_eq_add_neg,hv]; abel

private lemma fiber_sum {I J V : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    [AddCommMonoid V] (g : I → J) (u : J → V) :
    ∑ i, u (g i) = ∑ z, (univ.filter fun i => g i=z).card • u z := by
  calc
    _ = ∑ z, ∑ i ∈ univ.filter (fun i => g i=z), u (g i) := by
      simpa using (sum_fiberwise_eq_sum_filter (univ : Finset I) (univ : Finset J) g (fun i => u (g i))).symm
    _ = _ := sum_congr rfl fun z _ => by
      rw [← sum_const]; exact sum_congr rfl fun i hi => congrArg u (mem_filter.mp hi).2

/-- At input order 2q+1, strict coverage of all nonzero rows is impossible
when doubling is injective in both groups and q is at least three. -/
theorem no_saturated_graph {H K : Type*} [AddCommGroup H] [AddCommGroup K]
    [Fintype H] [Fintype K] [DecidableEq H] [DecidableEq K] [Nontrivial H]
    (f : H → K) (hp : Fintype.card H=2*Fintype.card K+1) (hq : 3≤Fintype.card K)
    (hH : Function.Injective (fun x : H => x+x)) (hK : Function.Injective (fun z : K => z+z)) :
    ¬ CoversRows f := by
  classical
  intro hf
  have double (i : H) (hi : i≠0) : i+i≠0 := fun h => hi (hH (by simpa using h))
  have spectrum (i : H) (hi : i≠0) (z : K) :
      sumRow f (i+i) z=2+if f i+f i=z then 1 else 0 := by
    let b := fun u : K => 2+if f i+f i=u then 1 else 0
    have hb (u : K) : b u ≤ sumRow f (i+i) u := by
      obtain ⟨a,d,had,hs,hc⟩ := hf (i+i) (double i hi) u
      have hai : a≠i := by rintro rfl; exact had (add_left_cancel hs).symm
      have hdi : d≠i := by rintro rfl; exact had (add_right_cancel hs)
      let R := univ.filter fun x => f x+f (i+i-x)=u
      have ha : a ∈ R := mem_filter.mpr ⟨mem_univ _,by rw [← hs]; simpa using hc⟩
      have hd : d ∈ R := mem_filter.mpr ⟨mem_univ _,by rw [← hs]; simpa [add_comm] using hc⟩
      change b u≤R.card
      by_cases he : f i+f i=u
      · have hii : i∈R := mem_filter.mpr ⟨mem_univ _,by simpa using he⟩
        have hsub : {i,a,d} ⊆ R := by
          intro x hx
          simp only [mem_insert,mem_singleton] at hx
          rcases hx with rfl|rfl|rfl <;> assumption
        simpa [b,he,hai.symm,hdi.symm,had] using card_le_card hsub
      · have hsub : {a,d} ⊆ R := by
          intro x hx
          simp only [mem_insert,mem_singleton] at hx
          rcases hx with rfl|rfl <;> assumption
        simpa [b,he,had] using card_le_card hsub
    have hsum : ∑ u, b u=∑ u, sumRow f (i+i) u := by
      rw [sum_row_total,hp]; simp [b,sum_add_distrib,Nat.mul_comm]
    exact ((sum_eq_sum_iff_of_le (fun u _ => hb u)).mp hsum z (mem_univ _)).symm
  have moment (i : H) (hi : i≠0) :
      (∑ a, f a)+(∑ a, f a)=(∑ z : K, (2:ℕ) • z)+(f i+f i) := by
    have he := (Equiv.subLeft (i+i)).sum_comp f
    change (∑ a, f (i+i-a))=∑ a, f a at he
    calc
      _ = ∑ a, (f a+f (i+i-a)) := by rw [sum_add_distrib,he]
      _ = ∑ z, sumRow f (i+i) z • z := fiber_sum (fun a => f a+f (i+i-a)) id
      _ = _ := by simp [spectrum i hi,add_smul,ite_smul,sum_add_distrib]
  obtain ⟨r,hr⟩ := exists_ne (0:H)
  have hconst {a : H} (ha : a≠0) : f a=f r :=
    hK (add_left_cancel ((moment a ha).symm.trans (moment r hr)))
  have hall : (univ : Finset K) ⊆ {f r+f r,f 0+f r} := by
    intro z _
    obtain ⟨a,b,_,hs,hz⟩ := hf r hr z
    by_cases ha : a=0
    · subst a; simp only [zero_add] at hs; subst b; simp [← hz]
    · by_cases hb : b=0
      · subst b; simp only [add_zero] at hs; subst a; simp [← hz,add_comm]
      · simp [← hz,hconst ha,hconst hb]
  have hh := card_le_card hall
  have hcard : ({f r+f r,f 0+f r} : Finset K).card≤2 :=
    (card_insert_le _ _).trans (by simp)
  simp only [card_univ] at hh
  omega

private lemma pair_spectrum {f : X → Y} (hf : CoversRows f) (i : X) (hi : i ≠ 0) :
    ∀ z : Y, ((univ : Finset (Fin 8)).filter fun t => pairColor f i t=z).card =
      1+(if (∑ a, f a)-f i=z then 1 else 0) := by
  let g := pairColor f i
  have hs : Function.Surjective g := by
    intro z
    have h2 : i+i ≠ 0 := by revert hi; revert i; decide +kernel
    obtain ⟨a,b,hab,hs,hz⟩ := hf (i+i) h2 z
    have hai : a≠i := by rintro rfl; exact hab (add_left_cancel hs).symm
    obtain ⟨t,ht|ht⟩ := offsets_pair a i hai
    · exact ⟨t,by change f _+f _=z; rwa [ht,show b=i-offset t by rw [ht] at hs; linear_combination hs] at hz⟩
    · have hbt : b=i+offset t := by rw [ht] at hs; linear_combination hs
      exact ⟨t,by simpa only [g,pairColor,ht,hbt,add_comm] using hz⟩
  let c := fun z : Y => (univ.filter fun t => g t=z).card
  have hpos (z : Y) : 1 ≤ c z := by
    obtain ⟨t,ht⟩ := hs z
    exact card_pos.mpr ⟨t,mem_filter.mpr ⟨mem_univ _,ht⟩⟩
  have hsum : ∑ z, c z=8 := by
    simpa [c] using sum_card_fiberwise_eq_card_filter (univ : Finset (Fin 8)) (univ : Finset Y) g
  have hex : ∃ u : Y, 1<c u := by
    by_contra! hn
    have he (z : Y) : c z=1 := le_antisymm (hn z) (hpos z)
    simp [he,ZMod.card] at hsum
  obtain ⟨u,hu⟩ := hex
  have hspec (z : Y) : c z=1+(if u=z then 1 else 0) := by
    let e := fun z : Y => c z-(1+if u=z then 1 else 0)
    have hplus (v : Y) : c v=e v+(1+if u=v then 1 else 0) := by
      by_cases hv : u=v <;> simp only [e,hv,if_true,if_false]
      · subst v; omega
      · have := hpos v; omega
    have htot : ∑ v, e v=0 := by
      simp_rw [hplus] at hsum
      simp [sum_add_distrib,ZMod.card] at hsum
      simp [hsum]
    have he := (sum_eq_zero_iff.mp htot) z (mem_univ _)
    rw [hplus,he,zero_add]
  have hfirst : (∑ t, g t)=u := by
    calc
      _ = ∑ z : Y, (c z) • z := fiber_sum g id
      _ = u := by
        simp_rw [hspec,add_smul,one_smul]
        have hy : ∑ z : Y, z=0 := by decide +kernel
        simp [sum_add_distrib,ite_smul,hy]
  have hfSum := sum_around f i
  change ∑ a, f a = f i+∑ t, g t at hfSum
  have hu' : (∑ a, f a)-f i=u := by rw [hfSum,hfirst]; abel
  intro z
  rw [hu']
  exact hspec z

private def bit (a b : Y) : ℕ := if a=b then 1 else 0

private def freq {I : Type*} [Fintype I] (f : I → Y) (z : Y) : ℕ :=
  (univ.filter fun a => f a=z).card

private theorem freq_sum {I : Type*} [Fintype I] (f : I → Y) (z : Y) :
    freq f z=∑ a, bit (f a) z := by simp only [freq,bit,Finset.card_filter]

private def convolution (c : Y → ℕ) (z : Y) := ∑ v, c v*c (z-v)

private theorem color_total (f : X → Y) (z : Y) :
    (∑ i, sumRow f (i+i) z) = convolution (freq f) z := by
  let e : X ≃ X := Equiv.ofBijective (fun i : X => i+i) (by decide +kernel)
  change (∑ i, sumRow f (e i) z) = _
  rw [e.sum_comp (fun r => sumRow f r z)]
  simp_rw [sumRow,Finset.card_filter]
  rw [sum_comm]
  have hrow (a : X) : (∑ r : X, if f a+f (r-a)=z then 1 else 0 : ℕ)=freq f (z-f a) := by
    rw [freq_sum]
    have h (r : X) : (f a+f (r-a)=z) ↔ f (r-a)=z-f a := by abel_nf; constructor <;> intro h <;> linear_combination h
    simp_rw [h]
    exact (Equiv.subRight a).sum_comp (fun v => bit (f v) (z-f a))
  simp_rw [hrow]
  simpa [convolution,freq,smul_eq_mul] using fiber_sum f (fun v => freq f (z-v))

private def predicted (f : X → Y) (i : X) (z : Y) : ℕ :=
  2+2*bit ((∑ a, f a)-f i) z+bit (f i+f i) z

private theorem ordered_spectrum {f : X → Y} (hf : CoversRows f) (i : X)
    (hi : i≠0) (z : Y) : sumRow f (i+i) z=predicted f i z := by
  change freq (fun a => f a+f (i+i-a)) z=_
  rw [freq_sum,sum_around _ i]
  have he (t : Fin 8) :
      bit (f (i+offset t)+f (i+i-(i+offset t))) z+
        bit (f (i-offset t)+f (i+i-(i-offset t))) z=2*bit (pairColor f i t) z := by
    rw [show i+i-(i+offset t)=i-offset t by abel,show i+i-(i-offset t)=i+offset t by abel]
    simp only [pairColor,add_comm (f (i-offset t)) (f (i+offset t)),two_mul]
  simp_rw [he]
  rw [← mul_sum,← freq_sum]
  have h := pair_spectrum hf i hi z
  change freq (pairColor f i) z=_ at h
  rw [h]
  simp only [predicted,bit,add_sub_cancel_right]
  omega

private theorem predicted_total (f : X → Y) (z : Y) :
    (∑ i, predicted f i z) = 34+2*freq f ((∑ a, f a)-z)+freq f (4*z) := by
  have e₁ (i : X) : bit ((∑ a, f a)-f i) z=bit (f i) ((∑ a, f a)-z) := by
    have h : (∑ a, f a)-f i=z ↔ f i=(∑ a, f a)-z := by constructor <;> intro h <;> linear_combination -h
    simp only [bit,h]
  have e₂ : ∀ u v : Y, u+u=v ↔ u=4*v := by decide +kernel
  have e₃ (i : X) : bit (f i+f i) z=bit (f i) (4*z) := by simp only [bit,e₂]
  simp only [predicted,sum_add_distrib,e₁,e₃,← mul_sum,← freq_sum,sum_const,card_univ,
    ZMod.card,smul_eq_mul]

/-- For order 238 the zero row is determined by the seven color frequencies,
the total color and the color at zero. -/
theorem histogram_identity {f : ZMod 17 → ZMod 7} (hf : CoversRows f) (z : ZMod 7) :
    let c := fun v => (univ.filter fun a => f a=v).card
    let S := ∑ a, f a
    (∑ v, c v*c (z-v)) + 2*(if S-f 0=z then 1 else 0) + (if f 0+f 0=z then 1 else 0) =
      32+2*c (S-z)+c (4*z)+sumRow f 0 z := by
  intro c S
  have hr := sum_erase_add (univ : Finset X) (fun i => sumRow f (i+i) z) (mem_univ 0)
  have hp := sum_erase_add (univ : Finset X) (fun i => predicted f i z) (mem_univ 0)
  have he := sum_congr (s₁ := univ.erase (0:X)) rfl (fun i hi => ordered_spectrum hf i (ne_of_mem_erase hi) z)
  rw [he,color_total] at hr
  rw [predicted_total] at hp
  simp only [zero_add,predicted] at hr hp
  change convolution (freq f) z+2*bit ((∑ a, f a)-f 0) z+bit (f 0+f 0) z=
    32+2*freq f ((∑ a, f a)-z)+freq f (4*z)+sumRow f 0 z
  let base := ∑ i ∈ univ.erase (0:X), predicted f i z
  change base+sumRow f 0 z=convolution (freq f) z at hr
  change base+(2+2*bit ((∑ a, f a)-f 0) z+bit (f 0+f 0) z)=
    34+2*freq f ((∑ a, f a)-z)+freq f (4*z) at hp
  rw [← hr]
  omega

private def rowBase (c : Y → ℕ) (z : Y) := 32+2*c (-z)+c (4*z)

private theorem centered_conditions {f : X → Y} (hf : CoversRows f) (hS : ∑ a, f a=0) :
    (∑ z, (rowBase (freq f) z-convolution (freq f) z)) ≤ 3 ∧
    ∃ z, rowBase (freq f) z+14 ≤ convolution (freq f) z+3 := by
  let err := fun z => 2*bit (-f 0) z+bit (f 0+f 0) z
  have he (z : Y) : convolution (freq f) z+err z = rowBase (freq f) z+sumRow f 0 z := by
    have h := histogram_identity hf z
    simpa only [hS,zero_sub,convolution,err,bit,rowBase,freq,Nat.add_assoc] using h
  have hs : ∑ z, err z=3 := by
    simp [err,sum_add_distrib,bit]
  constructor
  · rw [← hs]; apply sum_le_sum; intro z _; have := he z; omega
  · obtain ⟨z,hz⟩ := graph_reflection_three hf (by decide) (by decide)
    have hz' : 14 ≤ sumRow f 0 z := by
      simpa only [sumRow,zero_sub,ZMod.card] using (show 14 ≤ _ from by rw [ZMod.card] at hz; omega)
    have hE : err z ≤ 3 := by
      rw [← hs]
      exact single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ z)
    exact ⟨z,by have := he z; omega⟩

private theorem normalize_total {f : X → Y} (hf : CoversRows f) :
    ∃ g : X → Y, CoversRows g ∧ ∑ a, g a=0 := by
  let v := 5*(∑ a, f a)
  let g := fun a => f a-v
  refine ⟨g,?_,?_⟩
  · intro r hr z
    obtain ⟨a,b,hab,hs,hz⟩ := hf r hr (z+v+v)
    exact ⟨a,b,hab,hs,by dsimp [g]; linear_combination hz⟩
  · simp only [g,sum_sub_distrib,sum_const,card_univ,ZMod.card,nsmul_eq_mul,v]
    have h : (17: Y)*5=1 := by decide
    change (∑ a, f a)-(17:Y)*(5*(∑ a, f a))=0
    rw [← mul_assoc,h,one_mul,sub_self]

private theorem sum7 (g : Y → ℕ) : ∑ z, g z=g 0+g 1+g 2+g 3+g 4+g 5+g 6 := by
  rw [show (univ : Finset Y)={0,1,2,3,4,5,6} by decide +kernel]
  repeat rw [sum_insert (by decide)]
  rw [sum_singleton]; omega

private theorem certificate_sound (c : Y → ℕ) (hc : ∑ z, c z=17)
    (hsmall : (∑ z, (rowBase c z-convolution c z))≤3)
    (hlarge : ∃ z, rowBase c z+14 ≤ convolution c z+3) : False := by
  rw [sum7] at hc hsmall
  have h := Green33GraphHistogram.impossible (c 0) (c 1) (c 2) (c 3) (c 4) (c 5) (c 6) hc
  simp only [Green33GraphHistogram.excluded,decide_eq_true_eq] at h
  have p0 : convolution c 0=c 0*c 0 + 2*(c 1*c 6+c 2*c 5+c 3*c 4) := by
    rw [convolution,sum7]
    change c 0*c 0+c 1*c 6+c 2*c 5+c 3*c 4+c 4*c 3+c 5*c 2+c 6*c 1=_
    ring
  have p1 : convolution c 1=c 4*c 4 + 2*(c 0*c 1+c 2*c 6+c 3*c 5) := by
    rw [convolution,sum7]
    change c 0*c 1+c 1*c 0+c 2*c 6+c 3*c 5+c 4*c 4+c 5*c 3+c 6*c 2=_
    ring
  have p2 : convolution c 2=c 1*c 1 + 2*(c 0*c 2+c 3*c 6+c 4*c 5) := by
    rw [convolution,sum7]
    change c 0*c 2+c 1*c 1+c 2*c 0+c 3*c 6+c 4*c 5+c 5*c 4+c 6*c 3=_
    ring
  have p3 : convolution c 3=c 5*c 5 + 2*(c 0*c 3+c 1*c 2+c 4*c 6) := by
    rw [convolution,sum7]
    change c 0*c 3+c 1*c 2+c 2*c 1+c 3*c 0+c 4*c 6+c 5*c 5+c 6*c 4=_
    ring
  have p4 : convolution c 4=c 2*c 2 + 2*(c 0*c 4+c 1*c 3+c 5*c 6) := by
    rw [convolution,sum7]
    change c 0*c 4+c 1*c 3+c 2*c 2+c 3*c 1+c 4*c 0+c 5*c 6+c 6*c 5=_
    ring
  have p5 : convolution c 5=c 6*c 6 + 2*(c 0*c 5+c 1*c 4+c 2*c 3) := by
    rw [convolution,sum7]
    change c 0*c 5+c 1*c 4+c 2*c 3+c 3*c 2+c 4*c 1+c 5*c 0+c 6*c 6=_
    ring
  have p6 : convolution c 6=c 3*c 3 + 2*(c 0*c 6+c 1*c 5+c 2*c 4) := by
    rw [convolution,sum7]
    change c 0*c 6+c 1*c 5+c 2*c 4+c 3*c 3+c 4*c 2+c 5*c 1+c 6*c 0=_
    ring
  have hp (i : Y) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 := by revert i; decide +kernel
  rcases h with h | h
  · simp only [p0,p1,p2,p3,p4,p5,p6] at hsmall
    exact (Nat.not_lt_of_ge hsmall) h
  · obtain ⟨z,hz⟩ := hlarge
    obtain ⟨h0,h1,h2,h3,h4,h5,h6⟩ := h
    apply Nat.not_lt_of_ge hz
    rcases hp z with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · rw [p0]; exact h0
    · rw [p1]; exact h1
    · rw [p2]; exact h2
    · rw [p3]; exact h3
    · rw [p4]; exact h4
    · rw [p5]; exact h5
    · rw [p6]; exact h6

/-- No function from the seventeen-element field to the seven-element field
covers every color on every nonzero restricted sum row. -/
theorem no_graph_17_7 (f : ZMod 17 → ZMod 7) : ¬ CoversRows f := by
  intro hf
  obtain ⟨g,hg,hgS⟩ := normalize_total hf
  have hh := centered_conditions hg hgS
  apply certificate_sound (freq g) _ hh.1 hh.2
  simpa [freq,ZMod.card] using sum_card_fiberwise_eq_card_filter (univ : Finset X) (univ : Finset Y) g

/-- The graph at parity zero and a full vertical fiber at parity one. -/
def axisSet (f : ZMod 17 → ZMod 7) : Finset (ZMod 2 × ZMod 17 × ZMod 7) :=
  univ.filter fun x => (x.1=0 ∧ x.2.2=f x.2.1) ∨ (x.1=1 ∧ x.2.1=0)

theorem axis_card (f : ZMod 17 → ZMod 7) : (axisSet f).card=24 := by
  let label : X ⊕ Y → ZMod 2 × X × Y := Sum.elim (fun a => (0,a,f a)) (fun z => (1,0,z))
  have hi : Function.Injective label := by
    rintro (a|u) (b|v) h
    · exact congrArg Sum.inl (congrArg (fun w => w.2.1) h)
    · exact False.elim ((by decide : (0:ZMod 2) ≠ 1) (congrArg Prod.fst h))
    · exact False.elim ((by decide : (1:ZMod 2) ≠ 0) (congrArg Prod.fst h))
    · exact congrArg Sum.inr (congrArg (fun w => w.2.2) h)
  have he : axisSet f=univ.image label := by
    ext ⟨i,a,z⟩
    simp only [axisSet,mem_filter,mem_univ,true_and,mem_image]
    constructor
    · rintro (⟨rfl,h⟩|⟨rfl,h⟩)
      · exact ⟨Sum.inl a,by change (0,a,f a)=(0,a,z); rw [h]⟩
      · exact ⟨Sum.inr z,by change (1,0,z)=(1,a,z); rw [h]⟩
    · rintro ⟨v,hv⟩
      cases v with
      | inl t =>
        change (0,t,f t)=(i,a,z) at hv
        have h₁ : t=a := congrArg (fun w => w.2.1) hv
        have h₂ : f t=z := congrArg (fun w => w.2.2) hv
        exact Or.inl ⟨(congrArg Prod.fst hv).symm,h₂.symm.trans (congrArg f h₁)⟩
      | inr y =>
        change (1,0,y)=(i,a,z) at hv
        exact Or.inr ⟨(congrArg Prod.fst hv).symm,(congrArg (fun w => w.2.1) hv).symm⟩
  rw [he,card_image_of_injective _ hi,card_univ,Fintype.card_sum,ZMod.card,ZMod.card]

/-- The 24-label graph-plus-axis family supplies no strict two-basis of order 238. -/
theorem no_axis_238 (f : ZMod 17 → ZMod 7) :
    ¬ Green33StrictReduction.StrictCover (axisSet f) := by
  intro hs
  apply no_graph_17_7 f
  intro r hr z
  obtain ⟨⟨i,a,u⟩,ha,⟨j,b,v⟩,hb,hab,he⟩ := hs (0,r,z)
  have ei := congrArg Prod.fst he
  have er := congrArg (fun w => w.2.1) he
  have ez := congrArg (fun w => w.2.2) he
  change i+j=0 at ei
  change a+b=r at er
  change u+v=z at ez
  have ha' := (mem_filter.mp ha).2
  have hb' := (mem_filter.mp hb).2
  change (i=0 ∧ u=f a) ∨ (i=1 ∧ a=0) at ha'
  change (j=0 ∧ v=f b) ∨ (j=1 ∧ b=0) at hb'
  rcases ha' with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> rcases hb' with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact ⟨a,b,fun h => hab (by rw [h]),er,ez⟩
  · norm_num at ei
  · norm_num at ei
  · exact (hr (by simpa using er.symm)).elim

/-- CRT coordinates for the cyclic order in the finite exclusion. -/
def coords238 : ZMod 238 ≃+ (ZMod 2 × ZMod 17 × ZMod 7) :=
  (ZMod.chineseRemainder (m := 2) (n := 119) (by decide)).toAddEquiv.trans
    ((AddEquiv.refl (ZMod 2)).prodCongr (ZMod.chineseRemainder (m := 17) (n := 7) (by decide)).toAddEquiv)

theorem no_cyclic_axis_238 (f : ZMod 17 → ZMod 7) :
    ¬ Green33StrictReduction.StrictCover ((axisSet f).map coords238.symm.toEmbedding) := by
  intro hf
  apply no_axis_238 f
  intro x
  obtain ⟨a,ha,b,hb,hab,he⟩ := hf (coords238.symm x)
  obtain ⟨a',ha',rfl⟩ := mem_map.mp ha
  obtain ⟨b',hb',rfl⟩ := mem_map.mp hb
  exact ⟨a',ha',b',hb',fun h => hab (by rw [h]),
    coords238.symm.injective (by rw [map_add]; exact he)⟩

end Order238

#print axioms no_saturated_graph
#print axioms no_graph_17_7
#print axioms axis_card
#print axioms no_axis_238
#print axioms no_cyclic_axis_238
#print axioms histogram_identity
#print axioms graph_reflection_energy
#print axioms graph_reflection_three
#print axioms row_comparison
#print axioms exceptional_row_energy
#print axioms almost_reflection_three

end Green33GraphRows
