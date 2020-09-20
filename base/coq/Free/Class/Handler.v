From Base Require Import Free.Class.Normalform.
From Base Require Import Free.Monad.

(** A class representing handlers for whole effect stacks. *)
Class Handler (Shape : Type) (Pos : Shape -> Type) (A : Type) := {
  (* This function defines how a type is transformed by the handling process.
     Does not usually have to be implemented when defining an instance, as
     it can be inferred from the type of handle. *)
  handledType : Type;
  (* This function defines how the given effect stack is handled.
     Its return type is the return type of the normalization as
     transformed by the handler.
     For example, for a handler for the effect stack containing only the Maybe
     effect, a Free Shape Pos (Bool Shape Pos) is turned into an
     option (Bool Identity.Shape Identity.Pos). *)
  handle : Free Shape Pos A -> handledType
}.
