(* ::Package:: *)

BeginPackage["Hypergraphss`",{"Graphs`"}]


HypergraphIncidenceMatrix::usage="HypergraphIncidenceMatrix[vl,el] returns the edge-vertex incidence matrix of the corresponding hypergraph.";
HypergraphCoveringSystem::usage="HypergraphCoveringSystem[vl,el] returns the corresponding covering system Ax<=b as a list {A,b}.";


Begin["`Private`"]


HypergraphIncidenceMatrix[vl_List,el_List]:=Module[{},
	Outer[Boole[MemberQ[#1,#2]]&,el,vl,1]];

HypergraphCoveringSystem[vl_List,el_List]:=Module[{mat,vec},
	mat=Join[HypergraphIncidenceMatrix[vl,el],IdentityMatrix[Length@vl]];
	vec=Join[ConstantArray[1,Length@el],ConstantArray[0,Length@vl]];
	{-mat,-vec}];


End[]


EndPackage[]
