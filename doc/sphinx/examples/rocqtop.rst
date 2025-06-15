Rocqtop Examples
================

.. rocqtop:: reset all

   Print True. (* comment
   *) Print False.

.. rocqtop:: reset all

   From Ltac2 Require Import Ltac2.
   Ltac2 Type rec 'a backtracking_stream :=
     [ EmptyStream(exn) (* backtracking failure holding an exception *)
     | ConsStream('a, (exn -> 'a backtracking_stream)) ] (* backtracking success *).

.. rocqtop:: reset all

   From Ltac2 Require Import Ltac2.
   Ltac2 Type rec 'a backtracking_stream :=
     [ EmptyStream(exn) (* backtracking failure holding an exception *)
     | ConsStream('a, (exn -> 'a backtracking_stream)) ]. (* backtracking success *)

.. rocqtop:: reset all

   Check list (* comment
   *) nat. (* other comment *)

.. rocqtop:: reset all

   Check list (* comment
   *) nat (* other comment *).

.. rocqtop:: reset all

   Check (* comment *)
   nat. (* comment *)
   Check (* comment *) nat
   .
