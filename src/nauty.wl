(* ::Package:: *)

(*
This script imports the [-T] option output of
'directg' and 'waterclutter2' from 'nauty' into a graph list.
*)
(*str=Import["input.txt","Table"];*)
(*Import is extremely slow*)
str=ReadList["infile.txt", Number, RecordLists -> True];
str=Drop[#,2]&/@str;
glist=Graph[DirectedEdge@@@Partition[#,2]]&/@str
