(* This file is currently empty because the [trace] function is directly
   integrated into the compiler. Since the user may want to add an import
   for [Debug.Trace] nonetheless to compile a module with GHC, we have to
   provide this modules such that the generated Coq code does not refer
   to a missing module. In the future this module should export [trace]
   and [trace] should no longer be exported by [Free]. *)
