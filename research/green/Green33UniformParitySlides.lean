import Green33UniformSlideProfile
import Green33ParitySlides

/-! Stability of the slide limit when either parity layer retains a large seed. -/
open Finset Filter Green33Multiplicity Green33TailEnergy Green33SingerBlockingLayers
open Green33BaerDifferenceProfile Green33ParitySlides
open scoped Pointwise Topology
namespace Green33UniformSlides
variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

omit [Fintype G] in
private theorem sum_loss (A D : Finset G) : ((A+A)\(D+D)).card ≤ (A\D).card*A.card := by
  have sub : (A+A)\(D+D) ⊆ (A\D)+A := by
    intro z hz
    obtain ⟨hit,away⟩:=mem_sdiff.mp hz
    obtain ⟨x,hx,y,hy,rfl⟩:=mem_add.mp hit
    by_cases h:x∈D
    · have miss:y∉D:=fun hy' => away (add_mem_add h hy')
      simpa only [add_comm y x] using add_mem_add (mem_sdiff.mpr ⟨hy,miss⟩) hx
    · exact add_mem_add (mem_sdiff.mpr ⟨hx,h⟩) hy
  exact (card_le_card sub).trans card_add_le

omit [Fintype G] in
private theorem interaction_loss (U V : Finset G) (h:G) :
    diffReps U h ≤ diffReps V h + 2*(U\V).card := by
  let P:=U\V
  have info (S : Finset G) : (S ∩ ({h}+S)).card=diffReps S h := by
    rw [singleton_add,card_inter_vadd];exact (card_sub_eq S S h).symm
  have sub : U∩({h}+U) ⊆ (V∩({h}+V))∪P∪({h}+P) := by
    intro z hz
    obtain ⟨hzU,hz'⟩:=mem_inter.mp hz
    obtain ⟨t,ht,w,hw,rfl⟩:=mem_add.mp hz'
    have th : t=h:=mem_singleton.mp ht
    subst t
    by_cases x:h+w∈V
    · by_cases y:w∈V
      · exact mem_union_left _ (mem_union_left _ (mem_inter.mpr ⟨x,add_mem_add (mem_singleton_self h) y⟩))
      · exact mem_union_right _ (add_mem_add (mem_singleton_self h) (mem_sdiff.mpr ⟨hw,y⟩))
    · exact mem_union_left _ (mem_union_right _ (mem_sdiff.mpr ⟨hzU,x⟩))
  have b:=(card_le_card sub).trans (card_union_le _ _)
  have c:=card_union_le (V∩({h}+V)) P
  rw [info U,card_singleton_add] at b
  rw [info V] at c
  dsimp only [P] at b c
  omega

omit [Fintype G] in
/-- A one-sided edit bound for the translate intersections of self-sum supports. -/
theorem support_edit (A D : Finset G) (h:G) :
    diffReps (A+A) h ≤ diffReps (D+D) h + 2*((A\D).card*A.card) :=
  (interaction_loss _ _ _).trans (Nat.add_le_add_left (Nat.mul_le_mul_left 2 (sum_loss A D)) _)
#print axioms support_edit

private theorem label_edits {ι : Type*} {l : Filter ι} (v:ι→ℕ+) (A D:∀ i,Finset (ZMod (v i)))
    (a:Tendsto (fun i => ((A i).card:ℝ)/Real.sqrt (v i).val) l (𝓝 1))
    (d:Tendsto (fun i => ((D i).card:ℝ)/Real.sqrt (v i).val) l (𝓝 1))
    (missing:Tendsto (fun i => (((D i)\(A i)).card:ℝ)/Real.sqrt (v i).val) l (𝓝 0)) :
    Tendsto (fun i => (((A i)\(D i)).card:ℝ)/Real.sqrt (v i).val) l (𝓝 0) := by
  have h:=(missing.add a).sub d
  norm_num only [zero_add,sub_self] at h
  apply h.congr
  intro i
  have ad:=card_sdiff_add_card_inter (A i) (D i)
  have da:=card_sdiff_add_card_inter (D i) (A i)
  rw [inter_comm] at da
  have eq : ((A i)\(D i)).card+(D i).card=((D i)\(A i)).card+(A i).card := by omega
  rw [←add_div,←sub_div]
  congr 1
  have h':((((A i)\(D i)).card+(D i).card:ℕ):ℝ)=(((D i)\(A i)).card+(A i).card:ℕ) := by exact_mod_cast eq
  push_cast at h'
  linarith only [h']

/-- A seed of square-root size with variance o(v) passes its uniform
translate intersections to any other layer differing in o(√v) labels. -/
theorem retained_quarters {ι : Type*} {l : Filter ι} (v:ι→ℕ+) (A D:∀ i,Finset (ZMod (v i)))
    (grow:Tendsto (fun i => (v i).val) l atTop)
    (a:Tendsto (fun i => ((A i).card:ℝ)/Real.sqrt (v i).val) l (𝓝 1))
    (d:Tendsto (fun i => ((D i).card:ℝ)/Real.sqrt (v i).val) l (𝓝 1))
    (profile:Tendsto (fun i => variance (D i)/(v i).val) l (𝓝 0))
    (missing:Tendsto (fun i => (((D i)\(A i)).card:ℝ)/Real.sqrt (v i).val) l (𝓝 0)) :
    ∀ ε:ℝ, 0<ε → ∀ᶠ i in l, ∀ h:ZMod (v i),h≠0 →
      |(diffReps (A i+A i) h:ℝ)/(v i).val-1/4| < ε := by
  let n (i:ι):ℝ:=(v i).val
  have hn (i):0<n i:=by dsimp [n];exact_mod_cast (v i).property
  let ed (X Y:∀ i, Finset (ZMod (v i))) (i:ι):ℝ :=
    2*((X i\Y i).card:ℝ)*(X i).card/n i
  have costs (X Y:∀ i, Finset (ZMod (v i)))
      (sz:Tendsto (fun i => ((X i).card:ℝ)/Real.sqrt (n i)) l (𝓝 1))
      (mis:Tendsto (fun i => ((X i\Y i).card:ℝ)/Real.sqrt (n i)) l (𝓝 0)) :
      Tendsto (ed X Y) l (𝓝 0) := by
    have s:=(mis.mul sz).const_mul 2
    simpa only [ed,div_mul_div_comm,Real.mul_self_sqrt (hn _).le,zero_mul,mul_zero,mul_div_assoc,mul_assoc] using s
  have lossA:=costs A D a (label_edits v A D a d missing)
  have lossD:=costs D A d missing
  intro ε ep
  have half : 0<ε/2 := by positivity
  filter_upwards [quarter_translates v D grow d profile (ε/2) half,
    lossA.eventually_lt_const half,lossD.eventually_lt_const half] with i qi ai di
  intro h hh
  let r (X:Finset (ZMod (v i))) : ℝ:=diffReps (X+X) h
  have cap (X Y:∀ i,Finset (ZMod (v i))) : r (X i)/n i ≤ r (Y i)/n i + ed X Y i := by
    rw [show ed X Y i=2*((X i\Y i).card:ℝ)*(X i).card/n i by rfl,←add_div,div_le_div_iff_of_pos_right (hn i)]
    have c := support_edit (X i) (Y i) h
    dsimp only [r]
    rw [mul_assoc]
    exact_mod_cast c
  have op:=abs_lt.mp (qi h hh)
  change -_ < r (D i)/n i-1/4 ∧ r (D i)/n i-1/4<_ at op
  change |r (A i)/n i-1/4|<ε
  exact abs_lt.mpr ⟨by linarith only [op.1,cap D A,di],by linarith only [op.2,cap A D,ai]⟩
#print axioms retained_quarters


/-- Every nontrivial relative slide has the same seven-eighths limit when
the even layer retains almost all of a seed with a vanishing difference variance. -/
theorem uniform_slides {v : ℕ→ℕ+} (A B D:∀ i,Finset (ZMod (v i)))
    (grow:Tendsto (fun i => (v i).val) atTop atTop)
    (full:∀ i,split (A i) (B i)+split (A i) (B i)=univ)
    (critical:Tendsto (fun i => ((split (A i) (B i)).card:ℝ)/Real.sqrt ((2*(v i).val:ℕ):ℝ))
      atTop (𝓝 (Real.sqrt 2)))
    (seed:Tendsto (fun i => ((D i).card:ℝ)/Real.sqrt (v i).val) atTop (𝓝 1))
    (profile:Tendsto (fun i => variance (D i)/(v i).val) atTop (𝓝 0))
    (missing:Tendsto (fun i => (((D i)\(A i)).card:ℝ)/Real.sqrt (v i).val) atTop (𝓝 0)) :
    ∀ ε:ℝ, 0<ε → ∀ᶠ i in atTop, ∀ h:ZMod (v i), h+h≠0 →
      |((slide (A i) (B i) h+slide (A i) (B i) h).card:ℝ)/(2*(v i).val)-7/8|<ε := by
  let n (i:ℕ):ℝ:=(v i).val
  let U i := A i+A i
  let W i := ({1}:Finset (ZMod (v i)))+(B i+B i)
  have hn (i):0<n i:=by dsimp [n];exact_mod_cast (v i).property
  obtain ⟨us,overlap,_⟩:=critical_support A B grow full critical
  have a:=(balance A B full critical).1
  have qu:=retained_quarters v A D grow a seed profile missing
  intro ε ep
  have half : 0<ε/2:=by positivity
  have slack:=((us.sub_const (1/2)).abs).add overlap
  norm_num only [sub_self,abs_zero,zero_add] at slack
  filter_upwards [qu (ε/2) half,slack.eventually_lt_const half] with i qi hi
  intro h hh
  have lowHigh:=slide_card (A i) (B i) h (full i)
  let S:=slide (A i) (B i) h
  let d:ℝ:=diffReps (U i) (h+h)
  have l:2*n i+d≤(S+S).card+((U i).card:ℝ) := by dsimp only [n,U,S,d];exact_mod_cast lowHigh.1
  have u:(S+S).card+((U i).card:ℝ) ≤ 2*n i+d+(U i∩W i).card := by
    dsimp only [n,U,W,S,d];exact_mod_cast lowHigh.2
  have l':=(div_le_div_iff_of_pos_right (hn i)).mpr l
  have u':=(div_le_div_iff_of_pos_right (hn i)).mpr u
  simp only [add_div,mul_div_cancel_right₀ _ (hn i).ne'] at l' u'
  have r := abs_lt.mp (qi (h+h) hh)
  change -_ < d/n i-1/4 ∧ d/n i-1/4<_ at r
  change |((U i).card:ℝ)/n i-1/2|+((U i∩W i).card:ℝ)/n i<_ at hi
  have p:=le_abs_self (((U i).card:ℝ)/n i-1/2)
  have m:=neg_abs_le (((U i).card:ℝ)/n i-1/2)
  have nn:=div_nonneg (Nat.cast_nonneg (α:=ℝ) (U i∩W i).card) (hn i).le
  change |((S+S).card:ℝ)/(2*n i)-7/8|<ε
  rw [mul_comm (2:ℝ),←div_div]
  exact abs_lt.mpr ⟨by linarith only [hi,r.1,l',p,nn,ep],by linarith only [hi,r.2,u',m,ep]⟩

private theorem retained_profile {v : ℕ→ℕ+} (A B D:∀ i,Finset (ZMod (v i)))
    (grow:Tendsto (fun i => (v i).val) atTop atTop)
    (full:∀ i,split (A i) (B i)+split (A i) (B i)=univ)
    (critical:Tendsto (fun i => ((split (A i) (B i)).card:ℝ)/Real.sqrt ((2*(v i).val:ℕ):ℝ))
      atTop (𝓝 (Real.sqrt 2)))
    (seed:Tendsto (fun i => ((D i).card:ℝ)/Real.sqrt (v i).val) atTop (𝓝 1))
    (C:ℕ) (cap:∀ i z,reps (D i) z≤C)
    (missing:Tendsto (fun i => (((D i)\(A i)).card:ℝ)/Real.sqrt (v i).val) atTop (𝓝 0)) :
    Tendsto (fun i => variance (D i)/(v i).val) atTop (𝓝 0) := by
  let n (i:ℕ):ℕ+ := ⟨2*(v i).val,Nat.mul_pos (by decide) (v i).pos⟩
  let f i := Green33ReflectedLayers.doubleHom (v i)
  apply critical_profile v n D (fun i => split (A i) (B i)) f
    (fun i => (Green33ReflectedLayers.double_coordinates (v i) 0).1) (fun _ => 0) C 2
    (fun _ => le_rfl) cap full grow seed critical
  apply squeeze_zero (fun i => by positivity) _ missing
  intro i
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  apply Nat.cast_le.mpr
  have sub : (placed (f i) 0 (D i))\split (A i) (B i) ⊆ ((D i)\(A i)).image (f i) := by
    intro z hz
    obtain ⟨hs,ht⟩:=mem_sdiff.mp hz
    obtain ⟨x,hx,eq⟩:=mem_image.mp hs
    change 0+f i x=z at eq
    rw [zero_add] at eq
    have ax:x∉A i:=fun h => ht (mem_union_left _ (eq ▸ mem_image_of_mem (f i) h))
    exact mem_image.mpr ⟨x,mem_sdiff.mpr ⟨hx,ax⟩,eq⟩
  exact (card_le_card sub).trans card_image_le

/-- A bounded ordered sum count on the retained seed suffices. No bound
on the sum counts of the extra points or the opposite layer is required. -/
theorem bounded_seed_slides {v : ℕ→ℕ+} (A B D:∀ i,Finset (ZMod (v i)))
    (grow:Tendsto (fun i => (v i).val) atTop atTop)
    (full:∀ i,split (A i) (B i)+split (A i) (B i)=univ)
    (critical:Tendsto (fun i => ((split (A i) (B i)).card:ℝ)/Real.sqrt ((2*(v i).val:ℕ):ℝ))
      atTop (𝓝 (Real.sqrt 2)))
    (seed:Tendsto (fun i => ((D i).card:ℝ)/Real.sqrt (v i).val) atTop (𝓝 1))
    (C:ℕ) (cap:∀ i z,reps (D i) z≤C)
    (missing:Tendsto (fun i => (((D i)\(A i)).card:ℝ)/Real.sqrt (v i).val) atTop (𝓝 0)) :
    ∀ ε:ℝ, 0<ε → ∀ᶠ i in atTop, ∀ h:ZMod (v i), h+h≠0 →
      |((slide (A i) (B i) h+slide (A i) (B i) h).card:ℝ)/(2*(v i).val)-7/8|<ε :=
  uniform_slides A B D grow full critical seed (retained_profile A B D grow full critical seed C cap missing) missing
#print axioms uniform_slides
#print axioms bounded_seed_slides


private theorem layers_as_images {v:ℕ+} (A B:Finset (ZMod v)) :
    split A B=(A.image (Green33ReflectedLayers.doubleHom v))∪
      ({1}+B.image (Green33ReflectedLayers.doubleHom v)) := by
  unfold split
  congr 1
  rw [singleton_add]
  ext x
  simp only [mem_image,mem_vadd_finset,vadd_eq_add]
  constructor
  · rintro ⟨b,hb,rfl⟩;exact ⟨_,⟨b,hb,rfl⟩,rfl⟩
  · rintro ⟨_,⟨b,hb,rfl⟩,rfl⟩;exact ⟨b,hb,rfl⟩

/-- Swapping the layers reverses the relative slide, up to translation
of the entire basis. The odd carry translates the old even layer by −1. -/
theorem swap_slide {v:ℕ+} (A B:Finset (ZMod v)) (h:ZMod v) :
    slide B ({-1}+A) (-h) =
      {(-1:ZMod (2*v.val))-Green33ReflectedLayers.doubleHom v h}+slide A B h := by
  let f:=Green33ReflectedLayers.doubleHom v
  have two:f 1=1+1 := by simpa [f] using (Green33ReflectedLayers.double_coordinates v 0).2.2
  simp only [slide,layers_as_images,image_add,image_singleton,map_neg]
  change _ ∪ ({1}+({-f h}+({-f 1}+_))) = _ + (_∪({1}+({f h}+_)))
  rw [add_union,union_comm (B.image f),two]
  simp only [←add_assoc,singleton_add_singleton]
  have e:(1:ZMod (2*v.val))+-f h+-(1+1) = -1-f h := by abel
  have o:(-1:ZMod (2*v.val))-f h+1+f h=0 := by abel
  rw [e,o,singleton_zero,zero_add]

private theorem translated_card {H:Type*} [AddCommGroup H] [DecidableEq H] (z:H) (S:Finset H) :
    (({z}+S)+({z}+S)).card=(S+S).card := by
  rw [show ({z}+S)+({z}+S)={z+z}+(S+S) by rw [←singleton_add_singleton];ac_rfl,card_singleton_add]

private theorem swap_data {v:ℕ+} (A B:Finset (ZMod v)) (full : split A B+split A B=univ) :
    let R:=split B ({-1}+A)
    R+R=univ ∧ R.card=(split A B).card := by
  intro R
  have sh : R={(-1:ZMod (2*v.val))}+split A B := by
    simpa [R,slide,singleton_zero] using swap_slide A B 0
  rw [sh,card_singleton_add]
  refine ⟨eq_univ_of_card _ ?_,rfl⟩
  rw [translated_card,full,card_univ]

/-- The opposite parity has the same retention obstruction. This form
keeps the original odd layer as the layer that is physically moved. -/
theorem bounded_odd_seed_slides {v : ℕ→ℕ+} (A B D:∀ i,Finset (ZMod (v i)))
    (grow:Tendsto (fun i => (v i).val) atTop atTop)
    (full:∀ i,split (A i) (B i)+split (A i) (B i)=univ)
    (critical:Tendsto (fun i => ((split (A i) (B i)).card:ℝ)/Real.sqrt ((2*(v i).val:ℕ):ℝ))
      atTop (𝓝 (Real.sqrt 2)))
    (seed:Tendsto (fun i => ((D i).card:ℝ)/Real.sqrt (v i).val) atTop (𝓝 1))
    (C:ℕ) (cap:∀ i z,reps (D i) z≤C)
    (missing:Tendsto (fun i => (((D i)\(B i)).card:ℝ)/Real.sqrt (v i).val) atTop (𝓝 0)) :
    ∀ ε:ℝ, 0<ε → ∀ᶠ i in atTop, ∀ h:ZMod (v i), h+h≠0 →
      |((slide (A i) (B i) h+slide (A i) (B i) h).card:ℝ)/(2*(v i).val)-7/8|<ε := by
  let A' i := ({-1}:Finset (ZMod (v i)))+A i
  have data i:=swap_data (A i) (B i) (full i)
  have sc:Tendsto (fun i => ((split (B i) (A' i)).card:ℝ)/Real.sqrt ((2*(v i).val:ℕ):ℝ))
      atTop (𝓝 (Real.sqrt 2)) := critical.congr fun i => by rw [show (split (B i) (A' i)).card=_ from (data i).2]
  have q:=bounded_seed_slides B A' D grow (fun i => (data i).1) sc seed C cap missing
  intro ε ep
  filter_upwards [q ε ep] with i hi
  intro h hh
  have neg : -h+-h≠0 := by simpa only [←neg_add,neg_ne_zero] using hh
  have small:=hi (-h) neg
  dsimp only [A'] at small
  rw [swap_slide,translated_card] at small
  exact small
#print axioms swap_slide
#print axioms bounded_odd_seed_slides


/-- Eventually the full slides are exactly the kernel of doubling. This
includes both the unchanged slide and the possible order-two shift. -/
theorem full_slide_axes {v : ℕ→ℕ+} (A B D:∀ i,Finset (ZMod (v i)))
    (grow:Tendsto (fun i => (v i).val) atTop atTop)
    (full:∀ i,split (A i) (B i)+split (A i) (B i)=univ)
    (critical:Tendsto (fun i => ((split (A i) (B i)).card:ℝ)/Real.sqrt ((2*(v i).val:ℕ):ℝ))
      atTop (𝓝 (Real.sqrt 2)))
    (seed:Tendsto (fun i => ((D i).card:ℝ)/Real.sqrt (v i).val) atTop (𝓝 1))
    (C:ℕ) (cap:∀ i z,reps (D i) z≤C)
    (retained :
      Tendsto (fun i => (((D i)\(A i)).card:ℝ)/Real.sqrt (v i).val) atTop (𝓝 0) ∨
      Tendsto (fun i => (((D i)\(B i)).card:ℝ)/Real.sqrt (v i).val) atTop (𝓝 0)) :
    ∀ᶠ i in atTop, ∀ h:ZMod (v i),slide (A i) (B i) h+slide (A i) (B i) h=univ ↔ h+h=0 := by
  have uniform : ∀ᶠ i in atTop, ∀ h:ZMod (v i),h+h≠0 →
      |((slide (A i) (B i) h+slide (A i) (B i) h).card:ℝ)/(2*(v i).val)-7/8|<1/8 := by
    rcases retained with e|o
    · exact bounded_seed_slides A B D grow full critical seed C cap e _ (by norm_num)
    · exact bounded_odd_seed_slides A B D grow full critical seed C cap o _ (by norm_num)
  filter_upwards [uniform] with i hi
  intro h
  constructor
  · intro hit
    by_contra hh
    have z:=hi h hh
    rw [hit,card_univ,ZMod.card,Nat.cast_mul,Nat.cast_ofNat,div_self (by positivity)] at z
    norm_num at z
  · intro fix
    have lower:=(slide_card (A i) (B i) h (full i)).1
    rw [fix,show diffReps (A i+A i) 0=(A i+A i).card by
      simp only [diffReps,sub_eq_zero,←diag_eq_filter,diag_card]] at lower
    apply eq_univ_of_card
    apply le_antisymm (card_le_univ _)
    rw [ZMod.card]
    omega
#print axioms full_slide_axes

end Green33UniformSlides
