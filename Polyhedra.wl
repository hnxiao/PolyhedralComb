(* ::Package:: *)

cddBegin::usage = "cddBegin[] initializes resources.";
cddBegin[] := (
	Clear[cddlib];
	Off[General::spell1];
	Off[General::spell];
    cddlib = Install["/Users/HXiao/GitHub/mcdd/src/WSTP/mcdd"];
  );


cddEnd::usage = "cddEnd[] closes and destroys resources.";
cddEnd[] := (
    Uninstall[cddlib];
    Clear[cddlib];
  );


VertexEnumeration::usage="VertexEnumeration[A,b] returns the vertex list of the polyhedron defined by linear inequality system Ax<=b.";
VertexEnumeration[A_?MatrixQ,b_?VectorQ]:=Module[{M,rown,coln,vl},
	M=MapThread[Insert,{-A,b,Table[1,{Length[b]}]}];
	{rown,coln}=Dimensions[M];
	vl=ToExpression/@AllVertices[rown, coln, ToString[Flatten@M]][[1,1]];
	Return[Drop[#,1]&/@vl]]; (*The last operation drops the indicator of vertices.*)

IdealQ::usage="IdealQ[A,b] returns True if the polyhedron defined by Ax<=b is integer and returns False otherwise.";
IdealQ[A_?MatrixQ,b_?VectorQ]:=Module[{},
	AllTrue[Union@Flatten@VertexEnumeration[A,b],IntegerQ]]

NonIdealQ::usage="NonIdealQ[A,b] returns True if the polyhedron defined by Ax<=b is not integer and returns False otherwise.";
NonIdealQ[A_?MatrixQ,b_?VectorQ]:=Module[{},
	AnyTrue[Union@Flatten@VertexEnumeration[A,b],Not@IntegerQ[#]&]]


cddBegin[];
Print["Connected to cddlib via WSTP."];
