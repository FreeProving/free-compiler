Inductive Ext (Shape : Type) (Pos : Shape -> Type) (A : Type) :=
  | ext : forall s, (Pos s -> A) -> Ext Shape Pos A.

Arguments ext {Shape} {Pos} {A} s pf.

Class Container (F : Type -> Type) :=
  {
    Shape   : Type;
    Pos     : Shape -> Type;
    to      : forall {A : Type}, Ext Shape Pos A -> F A;
    from    : forall {A : Type}, F A -> Ext Shape Pos A;
    to_from : forall {A : Type} (fx : F A), to (from fx) = fx;
    from_to : forall {A : Type} (e : Ext Shape Pos A), from (to e) = e
  }.

Section SecContainer.

  Variable F : Type -> Type.
  Variable C__F : Container F.

  (* fmap for containers *)
  Definition cmap {A B : Type} (f : A -> B) (e : Ext Shape Pos A)
    : Ext Shape Pos B :=
    match e with
    | ext s pf => ext s (fun x => f (pf x))
    end.

End SecContainer.

Arguments cmap {F} {C__F} {A} {B}.
