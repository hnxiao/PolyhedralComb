(* ::Package:: *)

BeginPackage["PolyhedralComb`"]

EdmondsMatrix::usage"EdmondsMatrix[g] returns the LHS matrix of Edmonds odd set constraint Mx<=b";
EdmondsVector::usage"EdmondsVector[g] returns the RHS vector of Edmonds odd set constraint Mx<=b";
CycleVertexMatrix::usage="CycleVertexMatrix[g] returns the cycle vertex incidence matrix for both undirected and directed graphs";
CycleEdgeMatrix::usage="CycleEdgeMatrix[g] returns the cycle edge incidence matrix for undirected graphs only";
CycleArcMatrix::usage="CycleArcMatrix[g] returns the cycle arc incidence matrix for directed graphs only";
PreferenceTable::usage="PreferenceTable[g] returns a random prefrence table";
RothblumMatrix::usage="RothblumMatrix[g,pt] returns the Rothblum stable constraint matrix";
Begin["`Private`"]

EdmondsMatrix[g_]:=Module[{el,vl,subl},
	el=EdgeList[g];
	vl=VertexList[g];
	subl=Select[Subsets[vl,{3,Infinity,2}],!EmptyGraphQ[Subgraph[g,#]]&];
	SparseArray[{i_,j_}/;(Length@Intersection[subl[[i]],List@@el[[j]]]==2):>1,{Length@subl,Length@el}]];

EdmondsVector[g_]:=Module[{subl},
	subl=Select[Subsets[VertexList[g],{3,Infinity,2}],!EmptyGraphQ[Subgraph[g,#]]&];
	(Length/@subl-1)/2
];

CycleVertexMatrix[g_]:=Module[{},
	Outer[Boole[MemberQ[Flatten[List@@@#1],#2]]&,FindCycle[g,Infinity,All],VertexList@g,1]];

CycleEdgeMatrix[g_]:=Module[{},
	Outer[Boole[MemberQ[Sort/@#1,#2]]&,FindCycle[g,Infinity,All],EdgeList@g,1]];

CycleArcMatrix[g_]:=Module[{},
	Outer[Boole[MemberQ[#1,#2]]&,FindCycle[g,Infinity,All],EdgeList@g,1]];

PreferenceTable[g_]:=Module[{},
	Map[RandomSample[AdjacencyList[g,#]]&,VertexList@g]];

RothblumMatrix[g_,pt_]:=Module[{el},
	el=List@@@EdgeList@g;
	Outer[Boole[#1==#2\[Or]IntersectingQ[#1,#2]&&
		OrderedQ@{Position[pt[[Intersection[#1,#2][[1]]]],Complement[#2,Intersection[#1,#2]][[1]]],
				Position[pt[[Intersection[#1,#2][[1]]]],Complement[#1,Intersection[#1,#2]][[1]]]}]&,el,el,1]];

End[]

EndPackage[]
