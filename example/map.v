From Base Require Import Free.
From Base Require Import Prelude.

Module VersionWithoutSections.
  (*
    map :: (a -> b) -> [a] -> [b]
    map f xs = 
      case xs of
        []        -> []
        (x : xs') -> f x : map f xs'
  *)

  Fixpoint map' (Shape : Type) (Pos : Shape -> Type)
                {a b : Type} 
                (f  : Free Shape Pos (Free Shape Pos a -> Free Shape Pos b))
                (xs : List Shape Pos a)
                : Free Shape Pos (List Shape Pos b) :=
    match xs with
    | nil        => Nil Shape Pos
    | cons x xs' => Cons Shape Pos
        (f >>= fun(f' : Free Shape Pos a -> Free Shape Pos b) => f' x) 
        (xs' >>= fun(xs'0 : List Shape Pos a) => map' Shape Pos f xs'0)
    end.

  Definition map (Shape : Type) (Pos : Shape -> Type)
                 {a b : Type} 
                 (f  : Free Shape Pos (Free Shape Pos a -> Free Shape Pos b))
                 (xs : Free Shape Pos (List Shape Pos a))
                 : Free Shape Pos (List Shape Pos b) :=
    xs >>= fun(xs0 : List Shape Pos a) =>
      map' Shape Pos f xs0.

  (*
    data Rose a = Rose [a] a
  *)

  Inductive Rose (Shape : Type) (Pos : Shape -> Type)
                 (a : Type)
                 : Type :=
    rose_ : Free Shape Pos (List Shape Pos (Rose Shape Pos a))
            -> Free Shape Pos a
            -> Rose Shape Pos a.

  Arguments rose_ {Shape} {Pos} {a}.

  Definition Rose_ {Shape : Type} {Pos : Shape -> Type}
                   {a : Type}
                   (rs : Free Shape Pos (List Shape Pos (Rose Shape Pos a)))
                   (x : Free Shape Pos a)
                   : Free Shape Pos (Rose Shape Pos a) :=
    pure (rose_ rs x).

  (*
    mapRose :: (a -> b) -> Rose a -> Rose b
    mapRose f r =
      case r of
        (Rose rs x) -> Rose (map (mapRose f) (map f x)
        
    After η-conversion:
    
    mapRose :: (a -> b) -> Rose a -> Rose b
    mapRose f r =
      case r of
        (Rose rs x) -> Rose (map (\r' -> mapRose f r') rs) (f x)
  *)

  Fail Fixpoint mapRose' (Shape : Type) (Pos : Shape -> Type)
                    {a b : Type}
                    (f : Free Shape Pos (Free Shape Pos a -> Free Shape Pos b))
                    (r : Rose Shape Pos a)
                    : Free Shape Pos (Rose Shape Pos b) :=
    match r with
    | rose_ rs x => Rose_ 
        (map Shape Pos (pure (
            fun(r' : Free Shape Pos (Rose Shape Pos a)) => 
              r' >>= fun(r'0 : Rose Shape Pos a) =>
                mapRose' Shape Pos f r'0
        )) rs)
        (f >>= fun(f' : Free Shape Pos a -> Free Shape Pos b) => f' x)
    end.
End VersionWithoutSections.


Module VersionWithSections.
  (*
    map :: (a -> b) -> [a] -> [b]
    map f xs = 
      case xs of
        []        -> []
        (x : xs') -> f x : map f xs'
  *)

  Section SecMap.
    Variable Shape : Type.
    Variable Pos : Shape -> Type.
    Variable a : Type.
    Variable b : Type.
    Variable f  : Free Shape Pos (Free Shape Pos a -> Free Shape Pos b).

    Fixpoint map' (xs : List Shape Pos a)
                  : Free Shape Pos (List Shape Pos b) :=
      match xs with
      | nil        => Nil Shape Pos
      | cons x xs' => Cons Shape Pos
          (f >>= fun(f' : Free Shape Pos a -> Free Shape Pos b) => f' x) 
          (xs' >>= fun(xs'0 : List Shape Pos a) => map' xs'0)
      end.

    Definition map (xs : Free Shape Pos (List Shape Pos a))
                   : Free Shape Pos (List Shape Pos b) :=
      xs >>= fun(xs0 : List Shape Pos a) =>
        map' xs0.
  End SecMap.

  Arguments map Shape Pos {a} {b} f xs.

  (*
    data Rose a = Rose [a] a
  *)

  Inductive Rose (Shape : Type) (Pos : Shape -> Type)
                 (a : Type)
                 : Type :=
    rose_ : Free Shape Pos (List Shape Pos (Rose Shape Pos a))
            -> Free Shape Pos a
            -> Rose Shape Pos a.

  Arguments rose_ {Shape} {Pos} {a}.

  Definition Rose_ {Shape : Type} {Pos : Shape -> Type}
                   {a : Type}
                   (rs : Free Shape Pos (List Shape Pos (Rose Shape Pos a)))
                   (x : Free Shape Pos a)
                   : Free Shape Pos (Rose Shape Pos a) :=
    pure (rose_ rs x).

  (* Actually it is sufficient to just put [map] into a section,
     but for the sake of consistency we will do the same with [mapRose]. *)
  Section SecRoseMap.
    Variable Shape : Type.
    Variable Pos : Shape -> Type.
    Variable a : Type.
    Variable b : Type.
    Variable f  : Free Shape Pos (Free Shape Pos a -> Free Shape Pos b).

    (*
      mapRose :: (a -> b) -> Rose a -> Rose b
      mapRose f r =
        case r of
          (Rose rs x) -> Rose (map (mapRose f) (map f x)
          
      After η-conversion:
      
      mapRose :: (a -> b) -> Rose a -> Rose b
      mapRose f r =
        case r of
          (Rose rs x) -> Rose (map (\r' -> mapRose f r') rs) (f x)
    *)

    Fixpoint mapRose' (r : Rose Shape Pos a)
                      : Free Shape Pos (Rose Shape Pos b) :=
      match r with
      | rose_ rs x => Rose_ 
          (map Shape Pos (pure (
              fun(r' : Free Shape Pos (Rose Shape Pos a)) => 
                r' >>= fun(r'0 : Rose Shape Pos a) =>
                  mapRose' r'0
          )) rs)
          (f >>= fun(f' : Free Shape Pos a -> Free Shape Pos b) => f' x)
      end.

    Definition mapRose (r : Free Shape Pos (Rose Shape Pos a))
                       : Free Shape Pos (Rose Shape Pos b) :=
      r >>= fun(r0 : Rose Shape Pos a) =>
        mapRose' r0.
  End SecRoseMap.

  Arguments mapRose Shape Pos {a} {b} f r.
End VersionWithSections.

