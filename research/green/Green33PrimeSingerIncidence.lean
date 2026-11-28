import Green33PrimeAffineSlopes
import Green33SingerBlockingLayers

/-! Prime-plane incidence for cyclic cubic Singer lines, in additive labels. -/

open Finset Green33SingerBlockingLayers
open scoped Pointwise

namespace Green33PrimeSingerIncidence

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

private def fiber (D B : Finset G) (c : G) := B.filter fun b => c-b∈D

omit [Fintype G] in
private theorem fiber_card (D B : Finset G) (c : G) : (fiber D B c).card=occupancy D B c := by
  apply card_nbij' (c-·) (c-·)
  · intro b hb
    obtain ⟨hB,hD⟩ := mem_filter.mp hb
    exact mem_filter.mpr ⟨hD,by simpa using hB⟩
  · intro d hd
    obtain ⟨hD,hB⟩ := mem_filter.mp hd
    exact mem_filter.mpr ⟨hB,by simpa using hD⟩
  · intro b _;simp
  · intro d _;simp

private def secants (D B : Finset G) (b : G) :=
  univ.filter fun c => c-b∈D ∧ 2≤(fiber D B c).card

private theorem sparse_pencil (D B : Finset G) (nonempty : B.Nonempty) :
    ∃ b∈B, B.card*(secants D B b).card+2*(D+B).card≤2*(D.card*B.card) := by
  classical
  have sizes (c : G) : (fiber D B c).card = ∑ b ∈ B, if c-b∈D then 1 else 0 :=
    Finset.card_filter _ _
  have total : (∑ c, (fiber D B c).card)=D.card*B.card := by
    simp_rw [sizes]
    rw [sum_comm]
    have shift (b : G) : (∑ c : G, if c-b∈D then 1 else 0)=D.card := by
      calc _ = ∑ c : G, if c∈D then 1 else 0 := by
             simp only [sub_eq_add_neg]; exact Equiv.sum_comp (Equiv.addRight (-b)) (fun c : G => if c∈D then (1:ℕ) else 0)
           _ = _ := by simp
    simp [shift,Nat.mul_comm]
  have sumsec : (∑ b ∈ B, (secants D B b).card) =
      ∑ c, if 2≤(fiber D B c).card then (fiber D B c).card else 0 := by
    have stars (b : G) : (secants D B b).card=∑ c : G, if c-b∈D ∧ 2≤(fiber D B c).card then 1 else 0 := card_filter _ _
    simp_rw [stars]
    rw [sum_comm]
    apply sum_congr rfl
    intro c _
    by_cases many : 2≤(fiber D B c).card
    · simp only [many,and_true,if_true];exact (sizes c).symm
    · simp [many]
  have pt (c : G) : (if 2≤(fiber D B c).card then (fiber D B c).card else 0)+
      2*(if c∈D+B then 1 else 0)≤2*(fiber D B c).card := by
    have pos : 0<(fiber D B c).card ↔ c∈D+B := fiber_card D B c ▸ occupancy_pos D B c
    by_cases hit : c∈D+B
    · have hh := pos.mpr hit
      by_cases m : 2≤(fiber D B c).card <;> simp only [hit,m,if_true,if_false] <;> omega
    · have z : (fiber D B c).card=0 := by have := mt pos.mp hit;omega
      simp [z,hit]
  have h := sum_le_sum (s:=univ) (fun c _ => pt c)
  rw [sum_add_distrib,←sumsec,←mul_sum,←mul_sum,total] at h
  have card : (∑ c : G, if c∈D+B then (1:ℕ) else 0)=(D+B).card := by simp
  rw [card] at h
  obtain ⟨b,hb,low⟩ := exists_min_image B (fun b => (secants D B b).card) nonempty
  refine ⟨b,hb,?_⟩
  have min := sum_le_sum (s:=B) (fun z hz => low z hz)
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id] at min
  omega

private def pencil (D : Finset G) (P : G) := D.image (fun d => d+P)

omit [Fintype G] in
private theorem mem_pencil (D : Finset G) (P c : G) : c∈pencil D P ↔ c-P∈D := by
  constructor
  · intro h;obtain ⟨d,hd,rfl⟩ := mem_image.mp h;simpa using hd
  · intro h;exact mem_image.mpr ⟨c-P,h,sub_add_cancel _ _⟩

omit [Fintype G] in
private theorem pencil_card (D : Finset G) (P : G) : (pencil D P).card=D.card :=
  card_image_of_injective _ (fun _ _ h => add_right_cancel h)

private theorem tangent (D B : Finset G) {P : G} (hp : P∈B) (few : (secants D B P).card<D.card) :
    ∃ c∈pencil D P, ∀ z∈B.erase P, c-z∉D := by
  by_contra! none
  have sub : pencil D P ⊆ secants D B P := by
    intro c hc
    obtain ⟨z,hz,h⟩ := none c hc
    have thru := (mem_pencil D P c).mp hc
    exact mem_filter.mpr ⟨mem_univ _,thru,one_lt_card.mpr
      ⟨z,mem_filter.mpr ⟨(mem_erase.mp hz).2,h⟩,P,mem_filter.mpr ⟨hp,thru⟩,(mem_erase.mp hz).1⟩⟩
  have le := card_le_card sub
  rw [pencil_card] at le
  omega

/-- Multiplicative projective coordinates for an additively indexed Singer line. -/
structure SingerMap (F K : Type*) [Field F] [Field K] [Algebra F K] (D : Finset G) where
  form : K →ₗ[F] F
  onto : Function.Surjective form
  tag : Kˣ → G
  mul : ∀ u v, tag (u*v)=tag u+tag v
  surj : Function.Surjective tag
  same : ∀ u v, tag u=tag v ↔ ∃ k : F, (u:K)=k • (v:K)
  mem : ∀ u, tag u∈D ↔ form (u:K)=0

private structure Chart (F : Type*) [Field F] (D B : Finset G) (P : G) where
  row : G→F
  col : G→F
  line : (F×F) ↪ G
  origin : ∀ t, line t-P∈D ↔ t.2=0
  affine : ∀ z∈B.erase P, ∀ t, line t-z∈D ↔ row z+t.2*col z=t.1

private noncomputable def chart {F K : Type*} [Field F] [Field K] [Algebra F K]
    {D B : Finset G} (S : SingerMap F K D) {P γ α : G}
    (hγ : γ-P∈D) (hα : α-P∈D) (diff : α≠γ) (tan : ∀ z∈B.erase P, γ-z∉D) : Chart F D B P := by
  classical
  let rep (b : G) := (S.surj b).choose
  have tag (b : G) : S.tag (rep b)=b := (S.surj b).choose_spec
  let val (b : G) (u : K) := S.form (u*(rep (-b):Kˣ))
  have line (b : G) (u : Kˣ) : S.tag u-b∈D ↔ val b u=0 := by
    rw [sub_eq_add_neg,←tag (-b),←S.mul]
    exact S.mem _
  let U := rep γ
  let V := rep α
  have pU : val P U=0 := (line P U).mp (by simpa only [U,tag] using hγ)
  have pV : val P V=0 := (line P V).mp (by simpa only [V,tag] using hα)
  let y := (S.onto 1).choose
  have hy : S.form y=1 := (S.onto 1).choose_spec
  let W := y/(rep (-P):Kˣ)
  have pW : val P W=1 := by simpa [val,W,div_mul_cancel₀ _ (rep (-P)).ne_zero] using hy
  let raw (t : F×F) := (V:K) + t.2 • W - t.1 • (U:K)
  have eval_raw (z : G) (t : F×F) : val z (raw t)=val z V+t.2*val z W-t.1*val z U := by
    simp only [val,raw,sub_mul,add_mul,smul_mul_assoc,map_sub,map_add,map_smul,smul_eq_mul]
  have independent (a b : F) (e : a • (V:K) = b • (U:K)) : a=0 ∧ b=0 := by
    by_cases h : a=0
    · subst a;rw [zero_smul] at e;exact ⟨rfl,(smul_eq_zero.mp e.symm).resolve_right U.ne_zero⟩
    · exfalso
      apply diff
      rw [←tag α,←tag γ]
      apply (S.same V U).mpr
      refine ⟨a⁻¹*b,?_⟩
      have hh := congrArg (fun x : K => a⁻¹ • x) e
      simpa [←mul_smul,h] using hh
  have nz (t : F×F) : raw t≠0 := by
    intro e
    have h := eval_raw P t
    rw [e,pU,pV,pW] at h
    have ts : t.2=0 := by simpa [val] using h.symm
    have eq : (1:F) • (V:K) = t.1 • (U:K) := by simpa [raw,ts,sub_eq_zero] using e
    exact one_ne_zero (independent _ _ eq).1
  let label (t : F×F) := S.tag (Units.mk0 (raw t) (nz t))
  have inj : Function.Injective label := by
    intro t s eq
    obtain ⟨k,hk⟩ := (S.same _ _).mp eq
    change raw t=k • raw s at hk
    have atP := congrArg (val P) hk
    have scale (z : G) (k : F) (w : K) : val z (k • w)=k*val z w := by
      simp only [val,smul_mul_assoc,map_smul,smul_eq_mul]
    rw [scale,eval_raw,eval_raw,pV,pU,pW] at atP
    have slopes : t.2=k*s.2 := by simpa using atP
    have pair : (1-k) • (V:K) = (t.1-k*s.1) • (U:K) := by
      dsimp only [raw] at hk
      rw [slopes,mul_smul] at hk
      simp only [smul_sub,smul_add,←mul_smul] at hk
      simp only [sub_smul,one_smul]
      linear_combination hk
    have ⟨kv,uv⟩ := independent _ _ pair
    have kk : k=1 := by linear_combination -kv
    rw [kk,one_mul] at slopes uv
    exact Prod.ext (sub_eq_zero.mp uv) slopes
  let x (z : G) := val z V/val z U
  let y' (z : G) := val z W/val z U
  refine ⟨x,y',⟨label,inj⟩,?_,?_⟩
  · intro t
    change S.tag (Units.mk0 (raw t) (nz t))-P∈D ↔ _
    rw [line]
    change val P (raw t)=0 ↔ _
    simp [eval_raw,pU,pV,pW]
  · intro z hz t
    have den : val z U≠0 := by
      intro eq
      apply tan z hz
      simpa only [U,tag] using (line z U).mpr eq
    change S.tag (Units.mk0 (raw t) (nz t))-z∈D ↔ _
    rw [line]
    change val z (raw t)=0 ↔ val z V/val z U+t.2*(val z W/val z U)=t.1
    rw [eval_raw]
    field_simp [den]
    constructor <;> intro h <;> linear_combination h

private theorem from_chart {p d : ℕ} [Fact p.Prime] (D B : Finset G) (P : G) (C : Chart (ZMod p) D B P)
    (hp : P∈B) (size : B.card=p+1) (few : 2*(D+B)ᶜ.card<(d+1)*(d+2)) (small : 3*(d+1)<p)
    (sparse : (secants D B P).card+d<p) : ∃ c : G, p+1≤occupancy D B c+d := by
  let U := B.erase P
  let E := Green33PrimeAffineSlopes.missed U C.row C.col
  have holes : E.card≤(D+B)ᶜ.card := by
    have sub : E.map C.line ⊆ (D+B)ᶜ := by
      intro c hc
      obtain ⟨t,ht,rfl⟩ := mem_map.mp hc
      obtain ⟨nt,miss⟩ := (Green33PrimeAffineSlopes.mem_missed U C.row C.col t).mp ht
      apply mem_compl.mpr
      intro h
      obtain ⟨w,hw,z,hz,eq⟩ := mem_add.mp h
      have incident : C.line t-z∈D := by rw [←eq];simpa using hw
      by_cases iz : z=P
      · exact nt ((C.origin t).mp (iz ▸ incident))
      · have mem := mem_erase.mpr ⟨iz,hz⟩
        exact miss z mem ((C.affine z mem t).mp incident)
    simpa only [card_map] using card_le_card sub
  have rows : (U.image C.row).card≤(secants D B P).card := by
    let index : ZMod p ↪ G := ⟨fun a => C.line (a,0),fun _ _ e => congrArg Prod.fst (C.line.injective e)⟩
    have sub : (U.image C.row).map index ⊆ secants D B P := by
      intro c hc
      obtain ⟨t,ht,rfl⟩ := mem_map.mp hc
      obtain ⟨z,hz,rfl⟩ := mem_image.mp ht
      have atP := (C.origin (C.row z,0)).mpr rfl
      have atZ := (C.affine z hz (C.row z,0)).mpr (by simp)
      exact mem_filter.mpr ⟨mem_univ _,atP,one_lt_card.mpr ⟨z,mem_filter.mpr ⟨(mem_erase.mp hz).2,atZ⟩,
        P,mem_filter.mpr ⟨hp,atP⟩,(mem_erase.mp hz).1⟩⟩
    simpa only [card_map] using card_le_card sub
  have u_size : U.card=p := by simp [U,card_erase_of_mem hp,size]
  rcases Green33PrimeAffineSlopes.slope_stability U C.row C.col u_size (by change 2*E.card<_;omega) small with all|⟨a,line⟩
  · omega
  · refine ⟨C.line (a,0),?_⟩
    let V := U.filter fun z => C.row z=a
    have sub : insert P V ⊆ fiber D B (C.line (a,0)) := by
      intro z hz
      rcases mem_insert.mp hz with rfl|hv
      · exact mem_filter.mpr ⟨hp,(C.origin _).mpr rfl⟩
      · obtain ⟨hu,he⟩ := mem_filter.mp hv
        exact mem_filter.mpr ⟨(mem_erase.mp hu).2,(C.affine z hu (a,0)).mpr (by simpa using he)⟩
    have fresh : P∉V := fun h => (mem_erase.mp (mem_filter.mp h).1).1 rfl
    have h := card_le_card sub
    rw [card_insert_of_notMem fresh,fiber_card] at h
    change p≤V.card+d at line
    omega

/-- The prime-plane stability dichotomy in cyclic Singer coordinates.
Every counted hole is an actual missing mixed residue. -/
theorem large_line {K : Type*} [Field K] {p d : ℕ} [Fact p.Prime] [Algebra (ZMod p) K]
    (D B : Finset G) (S : SingerMap (ZMod p) K D)
    (order : Fintype.card G=p^2+p+1) (sizeD : D.card=p+1) (sizeB : B.card=p+1)
    (few : 2*(D+B)ᶜ.card<(d+1)*(d+2)) (small : 3*(d+1)<p)
    (extra : 2*(p+(D+B)ᶜ.card)<(p+1)*(p-d)) : ∃ c : G, p+1≤occupancy D B c+d := by
  have ne : B.Nonempty := card_pos.mp (by omega)
  obtain ⟨P,hP,lo⟩ := sparse_pencil D B ne
  have partition := card_add_card_compl (D+B)
  rw [sizeB,sizeD] at lo
  rw [order] at partition
  have mul : (p+1)*(secants D B P).card≤2*(p+(D+B)ᶜ.card) := by nlinarith only [lo,partition]
  have sparse : (secants D B P).card+d<p := by
    have lt := Nat.lt_of_mul_lt_mul_left (mul.trans_lt extra)
    omega
  obtain ⟨γ,hγ,tan⟩ := tangent D B hP (by omega)
  have enough : ((pencil D P).erase γ).Nonempty := by
    rw [←card_pos,card_erase_of_mem hγ,pencil_card,sizeD]
    omega
  obtain ⟨α,hα⟩ := enough
  have m := mem_erase.mp hα
  let C := chart S ((mem_pencil ..).mp hγ) ((mem_pencil ..).mp m.2) m.1 tan
  exact from_chart D B P C hP sizeB few small sparse

#print axioms large_line

end Green33PrimeSingerIncidence
