(* ::Package:: *)

(*
This script imports the [-T] option output of
'directg' and 'waterclutter2' from 'nauty' into a graph list.
*)
sol=Import["input.txt","Table"];
sol=Drop[#,2]&/@sol;
Graph[DirectedEdge@@@Partition[#,2]]&/@sol
