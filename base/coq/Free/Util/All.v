(* Utility function for constructing a property that is satisfied if and only
   if all of the properties in the given list are satisfied. *)
Fixpoint all (props : list Prop) : Prop
 := match props with
    | nil => True
    | cons prop props' => prop /\ all props'
    end.

Arguments all props /.
