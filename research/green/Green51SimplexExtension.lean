import Green51SimplexGeometry
import Green51FourSpaceMasks

/-! # Necessary conditions on extra pair differences of the simplex configuration -/

open Finset Green50Downsets Green51SystematicChecks Green51SimplexSection
open Green51SimplexGeometry Green51SimplexDirections
open scoped Pointwise
namespace Green51SimplexExtension
local notation "F" => ZMod 2
local notation "V" => Cube 10

/-- An injective affine image of the binary three-space in the indicated set. -/
def HasFrame (S : Finset V) : Prop :=
  ∃ (p:V) (L:Cube 3 →ₗ[F] V), Function.Injective L ∧ ∀ i,p+L i∈S

theorem frame_map {S T : Finset V} (f : V →ₗ[F] V) (inj : Function.Injective f)
    (inside : ∀ z∈S,f z∈T) (frame : HasFrame S) : HasFrame T := by
  obtain ⟨p,L,i,all⟩ := frame
  exact ⟨f p,f.comp L,inj.comp i,fun x => by simpa using inside _ (all x)⟩

private abbrev D := model+model
private def SingleBad (u : ℕ) := point 10 u∈D ∨ HasFrame (insert (point 10 u) D)
private def PairBad (p : ℕ×ℕ) := HasFrame (insert (point 10 p.1) (insert (point 10 p.2) D))

private theorem single_step (f : V →ₗ[F] V) (g : ℕ→ℕ) (inj : Function.Injective f)
    (act : ∀ x, f (point 10 x)=point 10 (g x)) (perm : ∀ z∈D,f z∈D)
    (u : ℕ) (bad : SingleBad u) : SingleBad (g u) := by
  rcases bad with m|h
  · exact Or.inl (act u ▸ perm _ m)
  · refine Or.inr (frame_map f inj ?_ h)
    intro z hz
    rcases mem_insert.mp hz with rfl|zD
    · rw [act]; exact mem_insert_self _ _
    · exact mem_insert_of_mem (perm _ zD)

private theorem pair_step (f : V →ₗ[F] V) (g : ℕ→ℕ) (inj : Function.Injective f)
    (act : ∀ x, f (point 10 x)=point 10 (g x)) (perm : ∀ z∈D,f z∈D)
    (p : ℕ×ℕ) (bad : PairBad p) : PairBad (g p.1,g p.2) := by
  apply frame_map f inj _ bad
  intro z hz
  rcases mem_insert.mp hz with rfl|s
  · rw [act]; exact mem_insert_self _ _
  · apply mem_insert_of_mem
    rcases mem_insert.mp s with rfl|zD
    · rw [act]; exact mem_insert_self _ _
    · exact mem_insert_of_mem (perm _ zD)

private def threeMap (a b c : ℕ) : Cube 3 →ₗ[F] V := columnMap [a,b,c]

private def rawModel := units++extras
private def rawDouble := rawModel.flatMap (fun a => rawModel.map (fun b => a ^^^ b))

private theorem raw_mem {u : ℕ} (hu : u∈rawModel) : point 10 u∈model := by
  rcases List.mem_append.mp hu with h|h
  · exact mem_union_left _ ((mem_rows units).mpr ⟨_,h,rfl⟩)
  · exact mem_union_right _ ((mem_rows extras).mpr ⟨_,h,rfl⟩)

private theorem raw_mem_double {u : ℕ} (hu : u∈rawDouble) : point 10 u∈D := by
  obtain ⟨a,ha,m⟩ := List.mem_flatMap.mp hu
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp m
  rw [point_xor]
  exact mem_add.mpr ⟨_,raw_mem ha,_,raw_mem hb,rfl⟩

private theorem raw_frame (S : Finset V) (rs : List ℕ)
    (lift : ∀ r∈rs, point 10 r∈S) (p a b c : ℕ)
    (cover : (List.range 8).all (fun i => rs.contains (p ^^^ matrix [a,b,c] i))=true)
    (small : (List.range 8).all (fun i => decide (matrix [a,b,c] i<1024))=true)
    (uniq : (List.range 8).all (fun i => (List.range 8).all (fun j =>
      i==j || matrix [a,b,c] i != matrix [a,b,c] j))=true) : HasFrame S := by
  let E := @Green51FourSpace.encode 3
  have mem (v : Cube 3) : E v∈List.range 8 :=
    List.mem_range.mpr (Green51FourSpace.encode_lt v)
  have de (v : Cube 3) : point 3 (E v)=v := Green51FourSpace.decode_encode v
  have deMap (v : Cube 3) : threeMap a b c v=point 10 (matrix [a,b,c] (E v)) := by
    exact (congrArg (threeMap a b c) (de v).symm).trans (columns_eval [a,b,c] (E v))
  refine ⟨point 10 p,threeMap a b c,?_,?_⟩
  · intro v w eq
    rw [deMap,deMap] at eq
    have lim (t : Cube 3) : matrix [a,b,c] (E t)<1024 := by
      simpa using List.all_eq_true.mp small _ (mem t)
    have same : (⟨_,lim v⟩:Fin 1024)=⟨_,lim w⟩ := Green51FourSpace.decode_inj 10 eq
    have raw := congrArg Fin.val same
    change matrix [a,b,c] (E v)=matrix [a,b,c] (E w) at raw
    have ij : E v=E w := by
      simpa [raw] using List.all_eq_true.mp (List.all_eq_true.mp uniq _ (mem v)) _ (mem w)
    exact (de v).symm.trans ((congrArg (point 3) ij).trans (de w))
  · intro v
    rw [deMap,←point_xor]
    exact lift _ (by simpa using List.all_eq_true.mp cover _ (mem v))

private theorem raw_single (u p a b c : ℕ)
    (cover : (List.range 8).all (fun i => (u::rawDouble).contains (p ^^^ matrix [a,b,c] i))=true)
    (small : (List.range 8).all (fun i => decide (matrix [a,b,c] i<1024))=true)
    (uniq : (List.range 8).all (fun i => (List.range 8).all (fun j =>
      i==j || matrix [a,b,c] i != matrix [a,b,c] j))=true) : SingleBad u := by
  refine Or.inr (raw_frame _ _ ?_ p a b c cover small uniq)
  intro r hr
  rcases List.mem_cons.mp hr with rfl|h
  exacts [mem_insert_self _ _,mem_insert_of_mem (raw_mem_double h)]

private theorem seed_one : SingleBad 1 := Or.inl (raw_mem_double (by decide +kernel))
private theorem seed_seven : SingleBad 7 := raw_single 7 0 6 2 1 (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem seed_thirteen : SingleBad 13 := raw_single 13 0 5 1 13 (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem seed_twenty_seven : SingleBad 27 := raw_single 27 0 10 3 27 (by decide +kernel) (by decide +kernel) (by decide +kernel)
private theorem seed_ninety_one : SingleBad 91 := raw_single 91 10 956 27 81 (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem seed_pair : PairBad (103,124) := by
  refine raw_frame _ (103::124::rawDouble) ?_ 9 970 110 27 (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  intro r hr
  simp only [List.mem_cons] at hr
  rcases hr with rfl|rfl|h
  exacts [mem_insert_self _ _,mem_insert_of_mem (mem_insert_self _ _),
    mem_insert_of_mem (mem_insert_of_mem (raw_mem_double h))]

/-- Adding a new difference outside the twenty-eight listed possibilities
either repeats an old pair difference or forces an affine three-space. -/
theorem single_obstruction {u : ℕ} (pos : u≠0) (bound : u<1024) (outside : u∉directions) :
    point 10 u∈D ∨ HasFrame (insert (point 10 u) D) :=
  single_orbits SingleBad (by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl
    exacts [seed_one,seed_seven,seed_thirteen,seed_twenty_seven,seed_ninety_one])
    (single_step firstMap first first_injective (columns_eval _) (fun _ => first_double))
    (single_step secondMap second second_injective (columns_eval _) (fun _ => second_double))
    pos bound outside

/-- Two distinct surviving directions force an affine three-space whenever
their sum lies outside the twenty-eight possible directions. -/
theorem pair_obstruction {u w : ℕ} (hu : u∈directions) (hw : w∈directions) (ne : u≠w)
    (absent : u ^^^ w∉directions) : HasFrame (insert (point 10 u) (insert (point 10 w) D)) :=
  pair_orbits PairBad seed_pair
    (pair_step firstMap first first_injective (columns_eval _) (fun _ => first_double))
    (pair_step secondMap second second_injective (columns_eval _) (fun _ => second_double))
    hu hw ne absent

end Green51SimplexExtension
#print axioms Green51SimplexExtension.single_obstruction
#print axioms Green51SimplexExtension.pair_obstruction
