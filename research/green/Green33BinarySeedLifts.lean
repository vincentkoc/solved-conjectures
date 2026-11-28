import Green33ApproximateCovers
import Mathlib.Combinatorics.Additive.Energy

/-! Three occupied residue classes in a cyclic sum cover. -/

open Finset Filter Green33StrictReduction Green33ApproximateCovers
open scoped Pointwise Topology

namespace Green33BinarySeedLifts

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

private def count (B C : Finset G) (f : G × G → G) (x : G) : ℕ :=
  ((B ×ˢ C).filter fun t => f t = x).card

private abbrev plus (B C : Finset G) := count B C fun t => t.1 + t.2
private abbrev minus (B C : Finset G) := count B C fun t => t.1 - t.2

omit [AddCommGroup G] in
private lemma total (B C : Finset G) (f : G × G → G) :
    ∑ x, count B C f x = B.card * C.card := by
  simpa [count] using sum_card_fiberwise_eq_card_filter (B ×ˢ C) univ f

omit [AddCommGroup G] in
private lemma count_sq (P : Finset (G × G)) (f : G × G → G) :
    (∑ x, ((P.filter fun p => f p = x).card)^2) =
      ((P ×ˢ P).filter fun t => f t.1 = f t.2).card := by
  let Q := (P ×ˢ P).filter fun t => f t.1 = f t.2
  have hi (x : G) : Q.filter (fun t => f t.1 = x) =
      (P.filter fun p => f p = x) ×ˢ (P.filter fun p => f p = x) := by
    ext t; simp only [Q,mem_filter,mem_product]; grind
  simpa [hi,sq] using sum_card_fiberwise_eq_card_filter Q univ (fun t => f t.1)

private lemma mixed_energy (B C : Finset G) :
    ∑ x, minus B C x ^ 2 = ∑ x, plus B C x ^ 2 := by
  unfold minus plus count
  rw [count_sq,count_sq]
  let swap (t : (G × G) × (G × G)) := ((t.1.1,t.2.2),(t.2.1,t.1.2))
  apply card_bij' (fun t _ => swap t) (fun t _ => swap t)
  · rintro ⟨⟨a,b⟩,c,d⟩ h
    simp only [swap,mem_filter,mem_product] at *
    exact ⟨⟨⟨h.1.1.1,h.1.2.2⟩,h.1.2.1,h.1.1.2⟩,by abel_nf at *; grind [sub_eq_sub_iff_add_eq_add]⟩
  · rintro ⟨⟨a,b⟩,c,d⟩ h
    simp only [swap,mem_filter,mem_product] at *
    exact ⟨⟨⟨h.1.1.1,h.1.2.2⟩,h.1.2.1,h.1.1.2⟩,by grind [sub_eq_sub_iff_add_eq_add]⟩
  · intros; rfl
  · intros; rfl

private lemma squares_le {ι : Type*} [Fintype ι] (f : ι → ℕ) :
    ∑ x, f x ^ 2 ≤ (∑ x, f x)^2 := by
  rw [sq,sum_mul]
  apply sum_le_sum
  intro x _
  simpa only [sq] using Nat.mul_le_mul_left (f x)
    (single_le_sum (s := (univ : Finset ι)) (f := f) (fun _ _ => Nat.zero_le _) (mem_univ x))

omit [AddCommGroup G] [Fintype G] in
private lemma count_as_sum (B C : Finset G) (f : G → G → G) (g : G → G → G)
    (hf : ∀ a b x, f a b = x ↔ a = g x b) (x : G) :
    count B C (fun p => f p.1 p.2) x = ∑ b ∈ C, if g x b ∈ B then 1 else 0 := by
  let P := (B ×ˢ C).filter fun t => f t.1 t.2 = x
  have eq (b) (hb : b ∈ C) : (P.filter fun t => t.2 = b).card =
      if g x b ∈ B then 1 else 0 := by
    by_cases hg : g x b ∈ B
    · have hset : P.filter (fun t => t.2 = b) = {(g x b,b)} := by
        ext ⟨a,c⟩; simp [P,hf,Prod.ext_iff]; grind
      simp [hg,hset]
    · have hset : P.filter (fun t => t.2 = b) = ∅ := by
        ext ⟨a,c⟩; simp [P,hf]; grind
      simp [hg,hset]
  have hs : P.filter (fun t => t.2 ∈ C) = P :=
    filter_eq_self.mpr (fun t h => (mem_product.mp (mem_filter.mp h).1).2)
  have h := sum_card_fiberwise_eq_card_filter P C Prod.snd
  rw [hs] at h
  exact h.symm.trans (sum_congr rfl eq)

omit [Fintype G] in
private lemma reassociate (B C : Finset G) (z : G) :
    ∑ c ∈ C, plus B C (z+c) = ∑ c ∈ C, minus B C (z-c) := by
  have hp (x : G) := count_as_sum B C (·+·) (·-·) (fun _ _ _ => eq_sub_iff_add_eq.symm) x
  have hm (x : G) := count_as_sum B C (·-·) (·+·) (fun _ _ _ => sub_eq_iff_eq_add) x
  simp only [plus,minus,hp,hm]
  rw [sum_comm]
  simp only [add_sub_right_comm]

/-- A mixed sum cover with d surplus pairs covers one factor by reflections
in at most d(d+1)/2 centers, provided the surplus is positive. -/
theorem reflection_centers (B C : Finset G) (cover : B+C = univ) {d : ℕ}
    (surplus : B.card*C.card = Fintype.card G+d) (pos : 0 < d) :
    ∃ T : Finset G, 2*T.card ≤ d*(d+1) ∧ ∀ c ∈ C, ∃ t ∈ T, t-c ∈ C := by
  classical
  have hs (x : G) : 0 < plus B C x := by
    obtain ⟨a,ha,b,hb,he⟩ := mem_add.mp (show x ∈ B+C from cover ▸ mem_univ _)
    exact card_pos.mpr ⟨(a,b),by simp [ha,hb,he]⟩
  let E (x) := plus B C x-1
  have split (x) : plus B C x = E x+1 := by dsimp [E]; have := hs x; omega
  have mass : ∑ x, E x = d := by
    have h := total B C (fun t => t.1+t.2)
    change (∑ x, plus B C x) = _ at h
    simp only [split,sum_add_distrib,sum_const,card_univ,smul_eq_mul,mul_one] at h
    omega
  let F := univ.filter fun x => 1 < minus B C x
  have upper : 2*F.card ≤ d*(d+1) := by
    have point (x : G) : (if x ∈ F then 2 else 0)+minus B C x ≤ minus B C x^2 := by
      by_cases h : x ∈ F
      · have hx : 1 < minus B C x := (mem_filter.mp h).2
        simp only [if_pos h]; nlinarith [Nat.mul_self_le_mul_self (show 2 ≤ minus B C x by omega)]
      · simp only [if_neg h,zero_add]; exact Nat.le_self_pow (by decide) _
    have h := sum_le_sum (s := univ) (fun x _ => point x)
    have hd := total B C (fun t => t.1-t.2)
    change ∑ x, minus B C x = _ at hd
    have e := mixed_energy B C
    simp only [split,add_sq,one_pow,mul_one,sum_add_distrib,← mul_sum,sum_const,card_univ,
      smul_eq_mul,mass] at e
    have hc : (∑ x : G, if x ∈ F then 2 else 0) = F.card*2 := by
      simp
    rw [sum_add_distrib,hc,hd] at h
    have he := squares_le E
    rw [mass] at he
    nlinarith
  obtain ⟨s,hplus⟩ : ∃ s, 1 < plus B C s := by
    by_contra! h
    have he (x) : E x=0 := by dsimp [E]; have := h x; omega
    simp [he] at mass
    omega
  refine ⟨F.image (fun y => s-y),(Nat.mul_le_mul_left 2 card_image_le).trans upper,?_⟩
  intro c hc
  let z := s-c
  have large : C.card < ∑ a ∈ C, plus B C (z+a) := by
    have h := sum_lt_sum (s := C) (f := fun _ => 1) (g := fun a => plus B C (z+a))
      (fun a _ => hs _) ⟨c,hc,by simpa [z] using hplus⟩
    simpa using h
  rw [reassociate] at large
  obtain ⟨a,ha,hbig⟩ : ∃ a ∈ C, 1 < minus B C (z-a) := by
    by_contra! hn
    have h := sum_le_sum (s := C) hn
    simp at h
    omega
  exact ⟨s-(z-a),mem_image.mpr ⟨_,mem_filter.mpr ⟨mem_univ _,hbig⟩,rfl⟩,
    by convert ha using 1; dsimp [z]; abel⟩

/-- Loss of distinct sums compared with one slot per unordered pair. -/
def loss (C : Finset G) : ℕ := C.card.choose 2 - (strictSums C).card

omit [Fintype G] in
private lemma slots (C : Finset G) : loss C + (strictSums C).card = C.card.choose 2 := by
  unfold loss strictSums
  apply Nat.sub_add_cancel
  simpa using (card_image_le (f := pairSum) (s := C.powersetCard 2))

omit [Fintype G] in
private lemma reflected_loss (C T : Finset G) (hT : ∀ c ∈ C, ∃ t ∈ T, t-c ∈ C)
    {τ : ℕ} (hd : ∀ s : G, (C.filter fun c => c+c=s).card ≤ τ) :
    C.card ≤ (τ+2)*T.card+2*loss C := by
  classical
  let Q := (C.powersetCard 2).filter fun p => pairSum p ∈ T
  let R := (C.powersetCard 2).filter fun p => pairSum p ∉ T
  let D := C.filter fun c => c+c ∈ T
  have hD : D.card ≤ T.card*τ := by
    have h := sum_le_sum (s := T) fun t _ => hd t
    simpa [sum_card_fiberwise_eq_card_filter C T (fun c => c+c),D] using h
  have sub : C ⊆ D ∪ Q.biUnion id := by
    intro c hc
    obtain ⟨t,ht,hm⟩ := hT c hc
    by_cases eq : t-c=c
    · exact mem_union_left _ (mem_filter.mpr ⟨hc,by rwa [← (sub_eq_iff_eq_add.mp eq)]⟩)
    · apply mem_union_right
      apply mem_biUnion.mpr
      refine ⟨{c,t-c},mem_filter.mpr ⟨mem_powersetCard.mpr ⟨?_,by simp [Ne.symm eq]⟩,?_⟩,
        by simp⟩
      · exact insert_subset hc (singleton_subset_iff.mpr hm)
      · simpa [pairSum,Ne.symm eq] using ht
  have two (p) (hp : p ∈ Q) : p.card = 2 := (mem_powersetCard.mp (mem_filter.mp hp).1).2
  have u : (Q.biUnion id).card ≤ Q.card*2 := by
    have h := card_biUnion_le (s := Q) (t := id)
    simpa [sum_congr rfl two] using h
  have cap := (card_le_card sub).trans (card_union_le _ _)
  have imageSub : strictSums C ⊆ T ∪ R.image pairSum := by
    intro x hx
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hx
    by_cases h : pairSum p ∈ T
    · exact mem_union_left _ h
    · exact mem_union_right _ (mem_image.mpr ⟨_,mem_filter.mpr ⟨hp,h⟩,rfl⟩)
  have hs := (card_le_card imageSub).trans (card_union_le _ _)
  have hi : (R.image pairSum).card ≤ R.card := card_image_le
  have hr : Q.card+R.card = C.card.choose 2 := by
    simpa [Q,R] using card_filter_add_card_filter_not (s := C.powersetCard 2)
      (fun p => pairSum p ∈ T)
  have hslots := slots C
  nlinarith

/-- In a mixed cover with positive surplus, one factor either loses strict
self-sums or needs many reflection centers. -/
theorem mixed_loss (B C : Finset G) (h : B+C = univ) {d τ : ℕ}
    (hd : B.card*C.card = Fintype.card G+d) (hp : 0 < d)
    (ht : ∀ s : G, (C.filter fun c => c+c=s).card ≤ τ) :
    2*C.card ≤ (τ+2)*(d*(d+1)) + 4*loss C := by
  obtain ⟨T,hcard,hcover⟩ := reflection_centers B C h hd hp
  have h₁ := reflected_loss C T hcover ht
  have h₂ := Nat.mul_le_mul_left (τ+2) hcard
  nlinarith only [h₁,h₂]

private def pack (m : ℕ+) (i : Fin 4) (x : ZMod m) : ZMod (4*m.val) :=
  ((4*x.val+i.val : ℕ) : ZMod (4*m.val))

private lemma pack_val (m : ℕ+) (i : Fin 4) (x : ZMod m) :
    (pack m i x).val = 4*x.val+i.val := by
  apply ZMod.val_natCast_of_lt
  have := x.val_lt
  omega

private lemma pack_inj {m : ℕ+} {i j : Fin 4} {x y : ZMod m}
    (h : pack m i x = pack m j y) : i = j ∧ x = y := by
  have e := congrArg ZMod.val h
  simp only [pack_val] at e
  exact ⟨Fin.ext (by omega),ZMod.val_injective _ (by omega)⟩

private lemma pack_onto (m : ℕ+) (v : ZMod (4*m.val)) :
    ∃ i x, pack m i x=v := by
  refine ⟨⟨v.val%4,Nat.mod_lt _ (by decide)⟩,(v.val/4 : ℕ),?_⟩
  apply ZMod.val_injective
  rw [pack_val,ZMod.val_natCast_of_lt (by have := v.val_lt; omega)]
  change 4*(v.val/4)+v.val%4=v.val
  omega

private lemma pack_add {m : ℕ+} {i j r : Fin 4} {x y z : ZMod m}
    (he : pack m i x + pack m j y = pack m r z) :
    (i.val+j.val)%4 = r.val ∧ x+y+((i.val+j.val)/4 : ℕ)=z := by
  let a := pack m i x
  let b := pack m j y
  have he' : a+b=pack m r z := he
  have val : (a.val+b.val=4*z.val+r.val) ∨ (a.val+b.val=4*z.val+r.val+4*m.val) := by
    by_cases h : a.val+b.val < 4*m.val
    · left
      have v := ZMod.val_add_of_lt h
      rw [he',pack_val] at v
      omega
    · right
      have v := ZMod.val_add_val_of_le (Nat.le_of_not_gt h)
      calc
        a.val+b.val = (a+b).val+4*m.val := v
        _ = _ := by rw [he',pack_val]
  dsimp [a,b] at val
  simp only [pack_val] at val
  constructor
  · omega
  · have h : x.val+y.val+(i.val+j.val)/4=z.val ∨
        x.val+y.val+(i.val+j.val)/4=z.val+m.val := by omega
    rcases h with h | h
    · have hh := congrArg (fun v : ℕ => (v : ZMod m)) h
      simpa using hh
    · have hh := congrArg (fun v : ℕ => (v : ZMod m)) h
      simpa using hh

/-- Labels above one residue class modulo four, using s as the origin. -/
def layer (m : ℕ+) (A : Finset (ZMod (4*m.val))) (s : ZMod (4*m.val))
    (i : Fin 4) : Finset (ZMod m) := univ.filter fun x => s+pack m i x ∈ A

private lemma layer_size (m : ℕ+) (A : Finset (ZMod (4*m.val))) (s : ZMod (4*m.val)) :
    ∑ i, (layer m A s i).card = A.card := by
  rw [← card_sigma]
  apply card_bij (fun (t : (i : Fin 4) × ZMod m) _ => s+pack m t.1 t.2)
  · intro t ht
    exact (mem_filter.mp (mem_sigma.mp ht).2).2
  · rintro ⟨i,x⟩ _ ⟨j,y⟩ _ he
    obtain ⟨rfl,rfl⟩ := pack_inj (add_left_cancel he)
    rfl
  · intro v hv
    obtain ⟨i,x,he⟩ := pack_onto m (v-s)
    exact ⟨⟨i,x⟩,mem_sigma.mpr ⟨mem_univ _,mem_filter.mpr ⟨mem_univ _,by simpa [he]⟩⟩,
      by simp [he]⟩

private def Basis {P : Type*} [AddCommGroup P] (strict : Bool) (A : Finset P) :=
  ∀ z, ∃ a ∈ A, ∃ b ∈ A, (strict = true → a ≠ b) ∧ a+b=z

private lemma layer_witness {m : ℕ+} {A : Finset (ZMod (4*m.val))} {strict : Bool}
    (h : Basis strict A) (s : ZMod (4*m.val)) (r : Fin 4) (z : ZMod m) :
    ∃ (i : Fin 4) (x : ZMod m) (j : Fin 4) (y : ZMod m), x ∈ layer m A s i ∧ y ∈ layer m A s j ∧
      (strict = true → i = j → x ≠ y) ∧ (i.val+j.val)%4=r.val ∧
      x+y+((i.val+j.val)/4 : ℕ)=z := by
  obtain ⟨a,ha,b,hb,hab,he⟩ := h (s+s+pack m r z)
  obtain ⟨i,x,hx⟩ := pack_onto m (a-s)
  obtain ⟨j,y,hy⟩ := pack_onto m (b-s)
  have eq : pack m i x + pack m j y = pack m r z := by rw [hx,hy]; abel_nf at *; grind
  obtain ⟨hr,hz⟩ := pack_add eq
  refine ⟨i,x,j,y,mem_filter.mpr ⟨mem_univ _,by simpa [hx]⟩,
    mem_filter.mpr ⟨mem_univ _,by simpa [hy]⟩,?_,hr,hz⟩
  rintro hs rfl rfl
  exact hab hs (by rw [hx] at hy; simpa using congrArg (fun v => v+s) hy)

private def rowSums (strict : Bool) (C : Finset G) : Finset G :=
  if strict then strictSums C else C+C

omit [Fintype G] in
private lemma to_row {strict : Bool} {C : Finset G} {x y : G}
    (hx : x ∈ C) (hy : y ∈ C) (ne : strict = true → x ≠ y) : x+y ∈ rowSums strict C := by
  cases strict
  · exact mem_add.mpr ⟨x,hx,y,hy,rfl⟩
  · exact mem_strictSums.mpr ⟨x,hx,y,hy,ne rfl,rfl⟩

private lemma three_rows {m : ℕ+} {A : Finset (ZMod (4*m.val))} {strict : Bool}
    (basis : Basis strict A) (s : ZMod (4*m.val)) (empty : layer m A s 3 = ∅) :
    let F := layer m A s
    F 1 + F 0 = univ ∧ F 1 + F 2 = univ ∧
    rowSums strict (F 0) ∪ (rowSums strict (F 2)).image (fun x => x+1) = univ := by
  let F := layer m A s
  have occupied {i x} (mem : x ∈ layer m A s i) : i ≠ 3 := by
    rintro rfl; simp [empty] at mem
  have row₁ : ∀ i j : Fin 4, i ≠ 3 → j ≠ 3 → (i.val+j.val)%4=1 →
      (i=1 ∧ j=0) ∨ (i=0 ∧ j=1) := by decide
  have row₃ : ∀ i j : Fin 4, i ≠ 3 → j ≠ 3 → (i.val+j.val)%4=3 →
      (i=1 ∧ j=2) ∨ (i=2 ∧ j=1) := by decide
  have row₀ : ∀ i j : Fin 4, i ≠ 3 → j ≠ 3 → (i.val+j.val)%4=0 →
      (i=0 ∧ j=0) ∨ (i=2 ∧ j=2) := by decide
  refine ⟨eq_univ_of_forall (fun z => ?_),eq_univ_of_forall (fun z => ?_),
    eq_univ_of_forall (fun z => ?_)⟩
  · obtain ⟨i,x,j,y,hx,hy,_,hr,hz⟩ := layer_witness basis s 1 z
    rcases row₁ i j (occupied hx) (occupied hy) hr with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact mem_add.mpr ⟨x,hx,y,hy,by simpa using hz⟩
    · exact mem_add.mpr ⟨y,hy,x,hx,by simpa [add_comm x y] using hz⟩
  · obtain ⟨i,x,j,y,hx,hy,_,hr,hz⟩ := layer_witness basis s 3 z
    rcases row₃ i j (occupied hx) (occupied hy) hr with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact mem_add.mpr ⟨x,hx,y,hy,by simpa using hz⟩
    · exact mem_add.mpr ⟨y,hy,x,hx,by simpa [add_comm x y] using hz⟩
  · obtain ⟨i,x,j,y,hx,hy,ne,hr,hz⟩ := layer_witness basis s 0 z
    rcases row₀ i j (occupied hx) (occupied hy) hr with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · apply mem_union_left
      have he : x+y=z := by simpa using hz
      exact he ▸ to_row hx hy (fun h => ne h rfl)
    · apply mem_union_right
      exact mem_image.mpr ⟨x+y,to_row hx hy (fun h => ne h rfl),by simpa using hz⟩

private lemma row_bound {m : ℕ+} {X Y : Finset (ZMod m)}
    (h : X ∪ Y.image (fun x => x+1) = univ) :
    m.val ≤ X.card+Y.card := by
  have hc := card_union_le X (Y.image (fun x => x+1))
  rw [h,card_univ,ZMod.card] at hc
  exact hc.trans (Nat.add_le_add_left card_image_le _)

private lemma mixed_size {m : ℕ+} {B C : Finset (ZMod m)} (h : B+C=univ) :
    m.val ≤ B.card*C.card := by simpa [h] using (card_add_le : (B+C).card ≤ _)

private lemma three_squares (m a b c : ℕ) (hs : m ≤ b*a) (hc : m ≤ c^2) :
    9*m ≤ (a+b+c)^2 := by
  have hab : 4*m ≤ (a+b)^2 := by nlinarith [sq_nonneg ((a:ℤ)-b)]
  have hmix : 2*m ≤ (a+b)*c := by
    by_contra! hn
    have hlt := Nat.pow_lt_pow_left hn (by decide : 2≠0)
    have hle := Nat.mul_le_mul hab hc
    nlinarith only [hlt,hle]
  nlinarith only [hc,hab,hmix]

omit [Fintype G] in
private lemma strict_slots (C : Finset G) :
    2*(strictSums C).card ≤ C.card^2 := by
  have h := slots C
  rw [Nat.choose_two_right] at h
  have := Nat.mul_le_mul_left C.card (Nat.sub_le C.card 1)
  nlinarith [Nat.div_mul_le_self (C.card*(C.card-1)) 2]

private lemma strict_basis {P : Type*} [AddCommGroup P] {A : Finset P} (h : StrictCover A) :
    Basis true A := by
  intro z; obtain ⟨a,ha,b,hb,ne,he⟩ := h z; exact ⟨a,ha,b,hb,fun _ => ne,he⟩

/-- A strict cover missing one residue class modulo four has size at least
three times the square root of one quarter of the group order. -/
theorem strict_three_class {m : ℕ+} {A : Finset (ZMod (4*m.val))} (hA : StrictCover A)
    (s : ZMod (4*m.val)) (empty : layer m A s 3 = ∅) : 9*m.val ≤ A.card^2 := by
  let F := layer m A s
  obtain ⟨c₁,c₂,c₀⟩ := three_rows (strict_basis hA) s empty
  have h₁ := mixed_size c₁
  have h₂ := mixed_size c₂
  have h₀ := row_bound c₀
  change m.val ≤ (strictSums (F 0)).card+(strictSums (F 2)).card at h₀
  have hh := layer_size m A s
  simp only [Fin.sum_univ_four,empty,card_empty,add_zero] at hh
  change (F 0).card + (F 1).card + (F 2).card=A.card at hh
  change m.val ≤ (F 1).card*(F 0).card at h₁
  change m.val ≤ (F 1).card*(F 2).card at h₂
  have bound (a b c : ℕ) (order : a ≤ c) (hs : m.val ≤ b*a)
      (hsq : 2*m.val ≤ a^2+c^2) : 9*m.val ≤ (a+b+c)^2 := by
    exact three_squares _ _ _ _ hs (by nlinarith [Nat.pow_le_pow_left order 2])
  rw [← hh]
  by_cases le : (F 0).card ≤ (F 2).card
  · apply bound _ _ _ le h₁
    nlinarith [strict_slots (F 0),strict_slots (F 2)]
  · have hs := bound _ _ _ (Nat.le_of_not_ge le) h₂
      (show 2*m.val ≤ (F 2).card^2+(F 0).card^2 by nlinarith [strict_slots (F 0),strict_slots (F 2)])
    simpa [Nat.add_comm,Nat.add_assoc,Nat.add_left_comm] using hs

/-- Ordinary covers in the same class satisfy the limiting coefficient 3/2
with an additive allowance of one label for the diagonal sums. -/
theorem ordinary_three_class {m : ℕ+} {A : Finset (ZMod (4*m.val))} (hA : A+A=univ)
    (s : ZMod (4*m.val)) (empty : layer m A s 3 = ∅) : 9*m.val ≤ (A.card+1)^2 := by
  let F := layer m A s
  have hb : Basis false A := by
    intro z
    obtain ⟨a,ha,b,hb,he⟩ := mem_add.mp (show z ∈ A+A from hA ▸ mem_univ _)
    exact ⟨a,ha,b,hb,by simp,he⟩
  obtain ⟨c₁,c₂,c₀⟩ := three_rows hb s empty
  have h₁ := mixed_size c₁
  have h₂ := mixed_size c₂
  have h₀ := row_bound c₀
  change m.val ≤ (F 0+F 0).card+(F 2+F 2).card at h₀
  have cap (C : Finset (ZMod m)) : 2*(C+C).card ≤ (C.card+1)^2 := by
    have h := (diagonal_loss C).2
    nlinarith [strict_slots C]
  have hh := layer_size m A s
  simp only [Fin.sum_univ_four,empty,card_empty,add_zero] at hh
  change (F 0).card + (F 1).card + (F 2).card=A.card at hh
  change m.val ≤ (F 1).card*(F 0).card at h₁
  change m.val ≤ (F 1).card*(F 2).card at h₂
  have both : 2*m.val ≤ ((F 0).card+1)^2+((F 2).card+1)^2 := by
    nlinarith [cap (F 0),cap (F 2)]
  by_cases le : (F 0).card ≤ (F 2).card
  · have he := three_squares _ _ _ _ h₁ (show m.val ≤ ((F 2).card+1)^2 by
      nlinarith [Nat.pow_le_pow_left (Nat.add_le_add_right le 1) 2])
    simpa [← hh,Nat.add_assoc] using he
  · have he := three_squares _ _ _ _ h₂ (show m.val ≤ ((F 0).card+1)^2 by
      nlinarith [Nat.pow_le_pow_left (Nat.add_le_add_right (Nat.le_of_not_ge le) 1) 2])
    simpa [← hh,Nat.add_comm,Nat.add_assoc,Nat.add_left_comm] using he

private lemma slots_even (n : ℕ) : 2*n.choose 2 ≤ n*(n-1) := by
  rw [Nat.choose_two_right]
  omega

private lemma size_profile {a b c m t : ℕ} (square : t^2 < m)
    (cross₁ : m ≤ b*a) (cross₂ : m ≤ b*c) (even : m ≤ a.choose 2+c.choose 2)
    (hk : a+b+c < 3*(t+1)) : a=t+1 ∧ b=t ∧ c=t+1 := by
  have ordered (u v : ℕ) (le : u ≤ v) (cross : m ≤ b*u)
      (ce : m ≤ u.choose 2+v.choose 2) (budget : u+b+v < 3*(t+1)) :
      u=t+1 ∧ b=t ∧ v=t+1 := by
    have vbig : t+1 ≤ v := by
      by_contra! small
      have h₁ := Nat.mul_le_mul (show u ≤ t by omega) (show u-1 ≤ t by omega)
      have h₂ := Nat.mul_le_mul (show v ≤ t by omega) (show v-1 ≤ t by omega)
      nlinarith only [ce,slots_even u,slots_even v,h₁,h₂,square]
    have hsum : 2*t < u+b := by
      by_contra! hl
      have hh := Nat.pow_le_pow_left hl 2
      have am : 4*(b*u) ≤ (u+b)^2 := by nlinarith [sq_nonneg ((u:ℤ)-b)]
      nlinarith only [cross,hh,am,square]
    have hv : v=t+1 := by omega
    have hu : u=t+1 := by
      by_contra! ne
      have small : u ≤ t := by omega
      have hmul := Nat.mul_le_mul small (Nat.sub_le_sub_right small 1)
      rw [hv] at ce
      have sub := slots_even (t+1)
      simp only [Nat.add_sub_cancel] at sub
      have ht : t-1+1=t ∨ t=0 := by omega
      rcases ht with h | h
      · nlinarith only [ce,slots_even u,sub,hmul,square,congrArg (fun z => z*t) h]
      · subst t; simp at small; subst u; simp at ce; omega
    exact ⟨hu,by omega,hv⟩
  by_cases hc : a ≤ c
  · exact ordered a c hc cross₁ even hk
  · obtain ⟨h₁,h₂,h₃⟩ := ordered c a (by omega) cross₂ (by omega) (by omega)
    exact ⟨h₃,h₂,h₁⟩

/-- An actual residue class modulo four is disjoint from the basis. -/
def MissesClass (m : ℕ+) (A : Finset (ZMod (4*m.val))) : Prop :=
  ∃ r : Fin 4, ∀ a ∈ A, a.val % 4 ≠ r.val

private lemma empty_origin {m : ℕ+} {A : Finset (ZMod (4*m.val))} (h : MissesClass m A) :
    ∃ s, layer m A s 3 = ∅ := by
  obtain ⟨r,hr⟩ := h
  let s : ZMod (4*m.val) := ((r.val+1 : ℕ) : ZMod (4*m.val))
  refine ⟨s,eq_empty_iff_forall_notMem.mpr (fun x hx => ?_)⟩
  apply hr _ (mem_filter.mp hx).2
  have rep : s + pack m 3 x =
      ((r.val+1+(4*x.val+3) : ℕ) : ZMod (4*m.val)) := by
    simp [s,pack]
  rw [rep,ZMod.val_natCast,Nat.mod_mod_of_dvd _ (by simp : 4 ∣ 4*m.val)]
  omega

/-- The literal missing-residue hypothesis gives the finite ordinary and
strict bounds; no coprimality between four and m is required. -/
theorem missing_class_bounds {m : ℕ+} {A : Finset (ZMod (4*m.val))} (h : MissesClass m A) :
    (A+A=univ → 9*m.val ≤ (A.card+1)^2) ∧ (StrictCover A → 9*m.val ≤ A.card^2) := by
  obtain ⟨s,he⟩ := empty_origin h
  exact ⟨fun ha => ordinary_three_class ha s he,fun ha => strict_three_class ha s he⟩

private lemma layer_losses {m : ℕ+} {A : Finset (ZMod (4*m.val))} (ha : StrictCover A)
    (s : ZMod (4*m.val)) (empty : layer m A s 3 = ∅) {t d : ℕ}
    (order : m.val+d=t*(t+1)) (h₀ : (layer m A s 0).card=t+1)
    (h₂ : (layer m A s 2).card=t+1) :
    loss (layer m A s 0)+loss (layer m A s 2) ≤ d := by
  obtain ⟨_,_,row⟩ := three_rows (strict_basis ha) s empty
  have h := row_bound row
  change m.val ≤ (strictSums (layer m A s 0)).card+(strictSums (layer m A s 2)).card at h
  have s₀ := slots (layer m A s 0)
  have s₂ := slots (layer m A s 2)
  rw [h₀] at s₀
  rw [h₂] at s₂
  have b := slots_even (t+1)
  simp only [Nat.add_sub_cancel] at b
  nlinarith only [s₀,s₂,b,h,order]

private lemma triangle_bound {m : ℕ+} {A : Finset (ZMod (4*m.val))} (ha : StrictCover A)
    (s : ZMod (4*m.val)) (empty : layer m A s 3 = ∅) {t d τ : ℕ}
    (order : m.val+d=t*(t+1)) (pos : 0 < d)
    (h₀ : (layer m A s 0).card=t+1) (h₁ : (layer m A s 1).card=t)
    (h₂ : (layer m A s 2).card=t+1) (diag : ∀ (C : Finset (ZMod m)) (v : ZMod m),
      (C.filter fun c => c+c=v).card ≤ τ) :
    2*(t+1) ≤ (τ+2)*(d*(d+1))+2*d := by
  obtain ⟨row₁,row₃,_⟩ := three_rows (strict_basis ha) s empty
  have b₀ := mixed_loss _ _ row₁ (by simpa [h₀,h₁,ZMod.card] using order.symm) pos (diag _)
  have b₂ := mixed_loss _ _ row₃ (by simpa [h₂,h₁,ZMod.card] using order.symm) pos (diag _)
  rw [h₀] at b₀
  rw [h₂] at b₂
  have hd := layer_losses ha s empty order h₀ h₂
  omega

private lemma cyclic_diagonal (m : ℕ+) (C : Finset (ZMod m)) (v : ZMod m) :
    (C.filter fun c => c+c=v).card ≤ 2 := by
  let P := C.filter fun c => c+c=v
  have sub : P.image ZMod.val ⊆ {v.val/2,(v.val+m)/2} := by
    intro z hz
    obtain ⟨c,hc,rfl⟩ := mem_image.mp hz
    have eq : c+c=v := (mem_filter.mp hc).2
    simp only [mem_insert,mem_singleton]
    by_cases h : c.val+c.val < m
    · have hh := ZMod.val_add_of_lt h
      rw [eq] at hh
      omega
    · have hh := ZMod.val_add_val_of_le (Nat.le_of_not_gt h)
      rw [eq] at hh
      omega
  simpa [P,card_image_of_injective _ (ZMod.val_injective m)] using
    (card_le_card sub).trans card_le_two

/-- For sizes t+1,t,t+1,0, a positive mixed-row surplus must grow at least
on the square-root scale in t, uniformly over all cyclic cofactors. -/
theorem positive_surplus {m : ℕ+} {A : Finset (ZMod (4*m.val))} (ha : StrictCover A)
    (s : ZMod (4*m.val)) (empty : layer m A s 3 = ∅) {t d : ℕ}
    (order : m.val+d=t*(t+1)) (pos : 0 < d)
    (h₀ : (layer m A s 0).card=t+1) (h₁ : (layer m A s 1).card=t)
    (h₂ : (layer m A s 2).card=t+1) : t+1 ≤ 2*(d*(d+1))+d := by
  have h := triangle_bound ha s empty order pos h₀ h₁ h₂ (cyclic_diagonal m)
  omega

private lemma forced_profile {m : ℕ+} {t : ℕ} (square : t^2 < m.val)
    {A : Finset (ZMod (4*m.val))} (ha : StrictCover A) {s : ZMod (4*m.val)}
    (empty : layer m A s 3 = ∅) (hk : A.card < 3*(t+1)) :
    (layer m A s 0).card=t+1 ∧ (layer m A s 1).card=t ∧ (layer m A s 2).card=t+1 := by
  let F := layer m A s
  obtain ⟨row₁,row₃,row₀⟩ := three_rows (strict_basis ha) s empty
  have h := row_bound row₀
  change m.val ≤ (strictSums (F 0)).card+(strictSums (F 2)).card at h
  have hs := layer_size m A s
  simp only [Fin.sum_univ_four,empty,card_empty,add_zero] at hs
  change (F 0).card+(F 1).card+(F 2).card=A.card at hs
  have s₀ := slots (F 0)
  have s₂ := slots (F 2)
  exact size_profile (a := (F 0).card) (b := (F 1).card) (c := (F 2).card)
    square (mixed_size row₁) (mixed_size row₃) (by omega) (by omega)

/-- An entire band below t(t+1) is excluded at the 3t+2 label budget, for
every possible distribution on three residue classes. -/
theorem surplus_band {m : ℕ+} {t d : ℕ} (order : m.val+d=t*(t+1)) (pos : 0 < d)
    (small : 2*(d*(d+1))+d < t+1) (A : Finset (ZMod (4*m.val)))
    (ha : StrictCover A) (absent : MissesClass m A) : 3*(t+1) ≤ A.card := by
  by_contra! hk
  obtain ⟨s,empty⟩ := empty_origin absent
  have square : t^2 < m.val := by nlinarith
  obtain ⟨ha₀,ha₁,ha₂⟩ := forced_profile square ha empty hk
  have h := positive_surplus ha s empty order pos ha₀ ha₁ ha₂
  omega

/-- At the one-surplus orders, no strict cover occupying at most three
classes can use only 3t+2 labels, irrespective of its fiber profile. -/
theorem one_surplus_orders {m : ℕ+} {t : ℕ} (ht : 3 ≤ t) (order : m.val+1=t*(t+1))
    (A : Finset (ZMod (4*m.val))) (ha : StrictCover A) (absent : MissesClass m A) :
    3*(t+1) ≤ A.card := by
  by_contra! hk
  obtain ⟨s,empty⟩ := empty_origin absent
  let F := layer m A s
  obtain ⟨row₁,row₃,_⟩ := three_rows (strict_basis ha) s empty
  obtain ⟨ha₀,ha₁,ha₂⟩ := forced_profile (show t^2 < m.val by nlinarith) ha empty hk
  have hd := layer_losses ha s empty order ha₀ ha₂
  change (F 0).card=t+1 at ha₀
  change (F 1).card=t at ha₁
  change (F 2).card=t+1 at ha₂
  have odd : Odd m.val := by
    obtain ⟨z,hz⟩ := Nat.two_dvd_mul_add_one t
    exact Nat.odd_iff.mpr (by omega)
  have unit : IsUnit (2 : ZMod m) := (ZMod.isUnit_iff_coprime 2 m).mpr odd.coprime_two_left
  have diag (C : Finset (ZMod m)) (v : ZMod m) : (C.filter fun c => c+c=v).card ≤ 1 := by
    apply card_le_one.mpr
    intro x hx y hy
    exact unit.mul_left_cancel (by simpa [two_mul] using
      ((mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm))
  have b₀ := mixed_loss (F 1) (F 0) row₁
    (by simpa [ha₀,ha₁,ZMod.card] using order.symm) (by decide : 0 < 1) (diag _)
  have b₂ := mixed_loss (F 1) (F 2) row₃
    (by simpa [ha₂,ha₁,ZMod.card] using order.symm) (by decide : 0 < 1) (diag _)
  rw [ha₀] at b₀
  rw [ha₂] at b₂
  change loss (F 0)+loss (F 2) ≤ 1 at hd
  omega

/-- In the ordinary convention of Green 33, any family confined to three
classes modulo four has limiting normalized size at least 3/2. The missing
class may depend on the modulus. -/
theorem missing_class_limit {ι : Type*} {l : Filter ι} [l.NeBot] (m : ι → ℕ+)
    (A : (i : ι) → Finset (ZMod (4*(m i).val))) (hm : Tendsto (fun i => (m i).val) l atTop)
    (cover : ∀ i, A i+A i=univ) (miss : ∀ i, MissesClass (m i) (A i))
    {L : ℝ} (hL : Tendsto (fun i => ((A i).card : ℝ)/Real.sqrt (4*(m i : ℝ))) l (𝓝 L)) :
    3/2 ≤ L := by
  have ht := ((tendsto_natCast_atTop_atTop (R := ℝ)).comp hm).const_mul_atTop (by norm_num : (0:ℝ)<4)
  have hs := Real.tendsto_sqrt_atTop.comp ht
  have hz : Tendsto (fun i => (1:ℝ)/Real.sqrt (4*(m i : ℝ))) l (𝓝 0) :=
    tendsto_const_nhds.div_atTop hs
  have hp : Tendsto (fun i => (((A i).card : ℝ)+1)/Real.sqrt (4*(m i : ℝ))) l (𝓝 L) := by
    simpa [add_div] using hL.add hz
  have point (i) : (9:ℝ)/4 ≤ ((((A i).card : ℝ)+1)/Real.sqrt (4*(m i : ℝ)))^2 := by
    have h : (9:ℝ)*(m i : ℝ) ≤ (((A i).card : ℝ)+1)^2 := by
      exact_mod_cast (missing_class_bounds (miss i)).1 (cover i)
    have pos : 0 < (m i : ℝ) := by exact_mod_cast (m i).pos
    rw [div_pow,Real.sq_sqrt (by positivity)]
    apply (le_div_iff₀ (by positivity)).mpr
    linarith
  have bound := le_of_tendsto_of_tendsto' tendsto_const_nhds (hp.pow 2) point
  have le : 0 ≤ L := le_of_tendsto_of_tendsto' tendsto_const_nhds hL (fun i => by positivity)
  exact (sq_le_sq₀ (by norm_num) le).mp (by norm_num; linarith)

#print axioms surplus_band
#print axioms missing_class_limit
#print axioms missing_class_bounds
#print axioms positive_surplus
#print axioms one_surplus_orders
#print axioms ordinary_three_class
#print axioms strict_three_class
#print axioms reflection_centers
#print axioms mixed_loss

end Green33BinarySeedLifts
