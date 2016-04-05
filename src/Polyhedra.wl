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
VertexEnumeration[A_?MatrixQ,b_?VectorQ]:=Module[{mat,row,col,extremes,vertices},
	mat=MapThread[Insert,{-A,b,Table[1,{Length[b]}]}];
	{row,col}=Dimensions[mat];
	(*Enumerate extreme points and rays*)
	extremes=AllVertices[row, col, ToString[Flatten@mat]][[1,1]];
	(*Select extreme points and drop the indicator of each extreme point*)
	vertices=Drop[#,1]&/@ToExpression[Cases[extremes,{"1",__}]];
	vertices];

IdealQ::usage="IdealQ[A,b] returns True if the polyhedron defined by Ax<=b is integer and returns False otherwise.";
IdealQ[A_?MatrixQ,b_?VectorQ]:=Module[{},
	AllTrue[Union@Flatten@VertexEnumeration[A,b],IntegerQ]]

IntegerPolyhedronQ::usage="IntegerPolyhedronQ[A,b] returns True if the polyhedron defined by Ax<=b is integer and returns False otherwise.";
IntegerPolyhedronQ[A_?MatrixQ,b_?VectorQ]:=Module[{},
	AllTrue[Union@Flatten@VertexEnumeration[A,b],IntegerQ]]


cddBegin[];
Print["Connected to cddlib via WSTP."];
