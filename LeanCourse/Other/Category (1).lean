set_option autoImplicit true

namespace CategoryTheory

structure LargeCategory where
  ob : Type (u + 1)
  hom : ob → ob → Type u
  identity {x : ob} : hom x x
  comp (f : hom y z) (g : hom x y) : hom x z
  id_law : comp identity f = f ∧ comp f identity = f
  assoc_law : comp (comp f g) h = comp f (comp g h)

structure SmallCategory where
  ob : Type u
  hom : ob → ob → Type u
  identity {x : ob} : hom x x
  comp (f : hom y z) (g : hom x y) : hom x z
  id_law : comp identity f = f ∧ comp f identity = f
  assoc_law : comp (comp f g) h = comp f (comp g h)

namespace SmallCategory

structure Functor (C D : SmallCategory.{u}) where
  map_ob : C.ob → D.ob
  map_mor : C.hom x y → D.hom (map_ob x) (map_ob y)
  pres_id : map_mor C.identity = @SmallCategory.identity D (map_ob x)
  pres_comp : map_mor (C.comp f g) = D.comp (map_mor f) (map_mor g)

def Functor.identity (C : SmallCategory) : Functor C C := {
  map_ob := id
  map_mor := id
  pres_id := by simp
  pres_comp := by simp
}

def Functor.comp (f : Functor D E) (g : Functor C D) : Functor C E := {
  map_ob := f.map_ob ∘ g.map_ob
  map_mor := f.map_mor ∘ g.map_mor
  pres_id := by simp [Functor.pres_id]
  pres_comp := by simp [Functor.pres_comp]
}

end SmallCategory

def SmallCat : LargeCategory.{u} := {
  ob := SmallCategory
  hom := SmallCategory.Functor
  identity := @SmallCategory.Functor.identity
  comp := SmallCategory.Functor.comp
  id_law := by intros; constructor <;> simp <;> constructor
  assoc_law := by intros; constructor
}

namespace LargeCategory

structure Functor (C D : LargeCategory.{u}) where
  map_ob : C.ob → D.ob
  map_mor : C.hom x y → D.hom (map_ob x) (map_ob y)
  pres_id : map_mor C.identity = @identity D (map_ob x)
  pres_comp : map_mor (C.comp f g) = D.comp (map_mor f) (map_mor g)

def idFunctor {C : LargeCategory} : Functor C C := {
  map_ob := id
  map_mor := id
  pres_id := by simp
  pres_comp := by simp
}

def Functor.comp (f : Functor D E) (g : Functor C D) : Functor C E := {
  map_ob := f.map_ob ∘ g.map_ob
  map_mor := f.map_mor ∘ g.map_mor
  pres_id := by simp [Functor.pres_id]
  pres_comp := by simp [Functor.pres_comp]
}

end LargeCategory

def Ty : LargeCategory.{u} := {
  ob := Type u
  hom := λ x y => x → y
  identity := id
  comp := Function.comp
  id_law := by simp [Function.comp_def]
  assoc_law := by simp [Function.comp_def]
}

structure Quiver where
  vertices : Type u
  edges : Type u
  source : edges → vertices
  target : edges → vertices

structure Quiver.Mor (G H : Quiver.{u}) where
  map_v : G.vertices → H.vertices
  map_e : G.edges → H.edges
  compat_law : map_v (G.source e) = H.source (map_e e) ∧ map_v (G.target e) = H.target (map_e e)

def Quiver.comp (f : Quiver.Mor H I) (g : Quiver.Mor G H) : Quiver.Mor G I := {
  map_v := f.map_v ∘ g.map_v
  map_e := f.map_e ∘ g.map_e
  compat_law := by intros; constructor <;> simp [Quiver.Mor.compat_law]
}

def Quiv : LargeCategory.{u} := {
  ob := Quiver.{u}
  hom := Quiver.Mor
  identity := {
    map_v := id
    map_e := id
    compat_law := by simp
  }
  comp := Quiver.comp
  id_law := by simp [Quiver.comp, Function.comp_def]
  assoc_law := by simp [Quiver.comp, Function.comp_def]
}

namespace Quiver

inductive Path (G : Quiver) : G.vertices → G.vertices → Type u where
  | nil : G.Path x x
  | con (e : G.edges) (p : G.Path x (G.source e)) : G.Path x (G.target e)

def Path.concate {G : Quiver} {x y z : G.vertices} (p : G.Path y z) (q : G.Path x y) : G.Path x z :=
  match p with
    | nil => q
    | con e p' => con e (p'.concate q)

theorem Path.concate_nil {G : Quiver} {x y : G.vertices} {p : G.Path x y} :
  p.concate nil = p ∧ nil.concate p = p
:= by
  constructor
  . cases p <;> try rfl
    simp [concate, concate_nil]
  . rfl

theorem Path.concate_assoc {G : Quiver} (x y z w : G.vertices) {p : G.Path z w} {q : G.Path y z} {r : G.Path x y} :
  (p.concate q).concate r = p.concate (q.concate r)
:= by
  cases p with
    | nil => simp [concate_nil]
    | con e p => simp [concate, concate_assoc]

def Path.map {G H} {x y : G.vertices} (p : G.Path x y) (F : Mor G H) : H.Path (F.map_v x) (F.map_v y) :=
  match p with
    | nil => nil
    | con e p => F.compat_law.right ▸ con (F.map_e e) (F.compat_law.left ▸ p.map F)

theorem Path.concate_map_dist {G H} {x y z : G.vertices} {F : Mor G H} {p : G.Path y z} {q : G.Path x y} :
  (p.concate q).map F = (p.map F).concate (q.map F)
:= by
  cases p with
    | nil => simp [concate]
    | con e p =>
      simp [concate, concate_map_dist, map]
      sorry
#print Path.concate_map_dist

def lift (G : Quiver) : SmallCategory := {
  ob := G.vertices
  hom := λ x y => G.Path x y
  identity := Path.nil
  comp := Path.concate
  id_law := by simp [Path.concate_nil]
  assoc_law := by simp [Path.concate_assoc]
}

def liftMor {G H} (F : Mor G H) : SmallCategory.Functor G.lift H.lift := {
  map_ob := F.map_v
  map_mor := λ p => p.map F
  pres_id := by simp [lift, Path.map]
  pres_comp := by simp [lift, Path.map, Path.concate_map_dist]
}
